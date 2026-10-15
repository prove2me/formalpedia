-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5049
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:34:40.815725+00:00
-- url     : https://prove2.me/submissions/79582218-857c-41c0-9757-2e63d9dc2232

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 907913669 ≤ n < 908093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 907914919 1250 907913669 907913681
    0xf0611070b130b0f0d0c05391b1003090213051003021522050d0201080705090a030809090702011116020a0e0703090302010c0509030d230a12060b030f041401 69
    0x80703c22400103144101140810103400c0b914100f10081003000e02c8a0400e079014404c0e80d03540b0f0b0208107a9101d0403945403418551504919103c40304002c40e50801c030071103041503650800940040c0117a4080c030300300d04101000c50b00e6000302d42000c00c072080301500003c1e0819000081003441030b071101c0003d0400310344074040000569002e065010210702e100a1041d80307030044281c00c00e030240c005400c4211150500d00c0e5070215080900150024015034004488481004191100307002c001c12445403562500c030001402180102229519448290100031149101618200442e0f062140519031030f0707520400c80d500e082d02c13101c80542448852012440c80400c40d071021410440240411000030b415401592030070784250b000304021021068150b880b40612106260554003c0202070107160080e460410307042c1d41784007070340801945040402da059100c004403e00040b4040b0b00265500070301d00a14010308040710116003507140450590900c1c400080c00900721a14806200c05180c40a40c401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 907916169 1250 907914919 907914929
    0x1b0904091e17040308070b060d0b01120611040812070f020a0f090f0e0d030e01060f1d0108010b0105180d0c03080c1209060405041d030703090f0611070b13 68
    0x10789240c0d245400304101c1c05001d24001d6880a8801a03601640c0d481d8070110303000d81c1c0e03004100b942003031982c0d240c0c0044210001e0241d43c0051804c03942c0404508001c038064000d02721a61055044407591900c4019199440026a010b45081c0010f1050300c2000c6402e000e96002610419100e01260030014005c40d1782c8480650001320324140806c0b4007045145a000352006100103102d80d1840000d90f10407200702c003200450540000d940009524842c4c1c0000840007548000499855283d4960643d01489a404081d00216901c11030a1700e421001c412801005880c0003081407190603400030b44030348188114000c1080700981c0b80013065480d25002605036030426052201c10b901c83c0741c55032040c1c0c400700c410000740c810a04001c3c401c0303120900711848810040c01e41030030140380c4002e10010304089512855814000c941d0711001d50070410103007c80740d01a580f61110f00b45400c03011607400c01c45401c1001080b0b24020080c1c280300000884008403202800820394860489400d9a8000119040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 907917419 1250 907916169 907916183
    0x19140714120903190c05060606030a15140f15041a0417010911033012040605011d07050a081812030f1305100506060d0f0c1202031b090409 61
    0xa00840d002e00002415051400c03007040301c80848881c00986211044007801041ea6000400040302814004081c580209014401040807041c1c041c0741e9443c584e5542052074414000340c400c0b00b842c0341603903d200c4503460a66410181c036503d1402d9801600c15806044464507088400d03400c5500782008850003886c2c0d820041110950001a030b17030203401000703025035490319801010040c038500441e0701e43c80719119100d071415100200720a032561032031141134038022140a101c01c42256090300b031441c1c811486504002499810f18103d0040d1480d425415111080424200401c140d0031404a901800751810644081d50318404541004030b081200482a4000e40020841c0141044040c500503d40707c0031640c0307665200201d01e4003500e40e451018000343c4c0703c11101c1f1403264480d4051604198082c1c0100c3c0303094158080232050310042201d51121540e03814070040b00ba98842055149041500010b600d1410407040c3c1049880b500c1c0c0d00b01c1c00d507403070010300c03003040303556036840031035000c0c0e00000e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 907918669 1250 907917419 907917421
    0x303040f080f0f0106050a060c020a03020d2105181e060f041a030c1b0a02060f0c010e0f030a0e030f06161103070503030403031a1302031914071412 65
    0x261080d00c0b20340e5111000c1c0c1e544264110283d0000381030050318295000a005100030382e02c1c090089a041701c035010305031f8101c00228408809030700e50000c160802401400038018121003c22030090f08000304a110003000740c184000e00491f020203500d848030640c02c440041c81c440205010b0303560401598007495000d14000b6060b12041000c901a208136601c1043d0501800d411288a1102d40f000700c0c3d81707512031013003001602051184032110203456448074048804034481503000ca41c1035807003800590041a0007150100c1945002d02801c0300c0021603d014140203000044032035520302801c00c401007444002d150300c115980b001c2007050071413480e0004603142420281001402006000f00c00d800048516402d1000d61800004444082d68004c00541c80c42d500c58a04900511500150010640090840041c1980c84014a1079120004200141d03282803080411010790503004802d84020f00b8000040c2c807180b14400300c00d07800403480c20700c0e100440c00c1c03200b0244140320352081c5810116002e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 907919919 1250 907918669 907918679
    0xc0601030308070306080105040809060a02030d0e0705040b012c0105070f0b0403030b0d17030606041e06080109090f170f0403050d020c010c0b060f0406050307080102090901090b1c020303040f 84
    0x10082d070f4000c2a054804000c80c94840b04190309a030300844028081060070070050516041a01c0200101c00491050f00d003400d110802c0b4405079050760f014402540d102c64020301c45890148a40200250300b420028110071240c6606049240910005000c00c0540c11450b40982d01417000c4030740140e4054040320f07601e8030610341030741c8441b01900c1c20303000245040041405030500c5030310380d01220b030490100c0b01e01c1464500f54101d01d80c40140007641110b814040002d140143ca00a65081e074503204d140d0a00609101004003c400141e101d10152810980d101010600300403041408a802a0f684e030310b50300400084254030301c41c400016034580000240002070040108004141c4640c541c00d035401c070744102004542180f004400036000440182c0454501d1908180000003a04058000f064665039440004c2c1004030a5002d40101e940000303680c030f00ca20300340d0f01060240604040810004510002091840c1e501039410600b0203c001e08601c01d5580401c180c0300182000200201140e80b95 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 907921169 1250 907919919 907919927
    0x30a1103070f1e0b07050a1203090b0703021206011b02060c010204031b06080609100e130b090d081b040501080c0f0f04140907020d210e0601150504060e090c0c06010303 74
    0x5044494100c405403e0301040003901041103800c0e26070020b0003003446803002d460b1701007a10000c10260003416918082c03800020030701b50300c1c07a100e03c103a034a005841d0704086610540e03041006020138100850060b46101021b8298901d0070020b070113071080c07900d5010702d030100c9009101c4c50300041c161850031140c0c00900ca039803146400c15140345079602d1103903031221804e111007048181c071881c81000c1083d20521424100114482e8484106c10a18030301e500c0c40d03182e40044520541d43c070442900030184080300ca40d080815141c2000c208216031420364800340c4e604020703004038050b0a04000fa4000451031003114041960007020700b0200540d60b0384034180c080340312a070203446000140c5240800070b400c00c2c036015444030302c14286c617005800100c3c40b1400403141c400f94000510210422180d4100140c0018465550040c0f0310703200410b00c0d5410f1252a0465065106220081001c200824001250320600710040340340d05036543c3c00300b0380304c00001c542c031ba0103030314106a01403054400020506901c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 907922419 1250 907921169 907921199
    0x50409020a03021c0e1908030604050406140f0601111203041e08190f030b03100f1104230907020309060717070b1504061a0c0a1b030204050f06030a1103070f 69
    0x5c0c00480f0784890244041c848407680001d4003501000003840027035070b981040d400035540684900d00005540d00f0310311448004050503174404404590010801942c0d503048081c01703145c4151076000700b01c03562a0450300c18a520008100400044907120105000e001403050808a02d0b444100c0548130341501d03070503c501e0503040e01d00c600002c0c2804502021305001c2c0c07281482c6800090094030201140c50b4081001e0005500382000541da0b07560900035070344c0320720003030030181404800858920a0001e0f041004202034009148103100304130920845039000004ca8408250603200c00d511102c0c0e605055901b2040301c03039002810117002407820100002101d4081c4201c03850108174016104800030b00080b030388240240c01501500e0b158403c402c0903c04040d00e1051042412540039903241c0e0344011320500540c01581004110030001d20071840c043c01042d6021281a6009040e4500200065a14018440050501c8042e01030700321031501c040c01940c019107844030105040d81d0ba204003492508034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 907923669 1250 907922419 907922441
    0x519110604090e01060e04050d08040219170708010c08040308280f110406121a0301060f0305060f06010e010c0f0605100305100209030a290a0218040606050409020a03021c 75
    0x102c0c2c24008516802105403450113590013800500c20090324480503a203641000d030082c0e030300c80c140e41d44030350011537102130140c0940307070040100349481d44e400b0300d05240c80c1c2c050f0440b00c101d0b4140240300314030740da2050716254000c0e0140341038003213900c460050081c2c8444068407030018000212a206015141d5045400c0c000c942002c2000390b2003040d002c0c210b40b40614010700c0c000440004401d1403802c0980c004280115008014842440513107001900f101e0040e0701c5508ac0903201a42007091101c00e02609030300042400940c000340c45c255000030100408d8000d250305101d0040381c44001e0240998000d442d41c0c1d4455010890340c1000d00010500d1401444202d41501c5110f81107402c00c0e210b4002d03264044006002004c1c100001c1c0e81c0c00c20400010709a04003404c04100c8a40301c1503400e42c5460f800340c00d500304010383d17410303030f02c4070860012241c0903145010302e00f4884100420b03070303020040b202101d060075070050f250703039840d40e0880c0a48100301400c001000400c900141d072000a50085001301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 907924919 1250 907923669 907923671
    0x8160e1306170601030507090b01120c03050106021002030105060a031107050604260f09120f060a0902010917070320030a052d03030613060803072d0519110604090e01 73
    0xb5200c18182c0790b84803024000103010f034000c201e041001d0711194100620f0003105040140c500d43c41881490200c6003444403e1000035200c0c0f004121840c3c052101c1c030383c4058181e42c10340c51517051201080303551041a552404150f07844801001a00d400d505030b5080603400703000c1e55114142820103074140da000399940d240c01480c0034202c5901144240c111000484003c061030b0500102d4010400c00c00b844070300e411481d000310400301c0c4000301c080c0700842c41001422390008085c8164000184841e074103400101d224801c202054400c01d20002d9103008482c0d0182100c9200c1e0044601140c080c4000a0b1681d0507200b110211401c001d004100f40c00340789800c40f803890035500009034400d030010144a001c15203030020000b01c0e05a01b809250703000c4503001c482c80802c481e41e6030780c2850f1030f643c0420740075114542601385142d5a008081400e088500706107075140000d002940f00e042c4c80304d540c50401545081c2000c680020085c402042a000050040201e91582e550380c40c620003070680110018055 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 907926169 1250 907924919 907924949
    0xb1c1e0c0e010c021c022206080106150c3201023001060503100324060501050f0906090a0b1207121109010324080c0f03010c08160e1306 60
    0x1a5110343e424244090b001010140c1c2a0071030920103450403610042660400250b01050b90700c0a04441c510b40d551540050029045240035402400c558040d0899011088012000004180d110401100e560f4210303e9800c02c00180b10380644010018290544464041c100001060217042d40a841c5043d410f10310500c80c0c00c05510707a10350910b0581007141c402c1c041d4000500080d8401c002440c4d000b4641e0500196083d01c940395135098070304055411103181058035801441040500030900240300a082103410604c01018821881c01450301050003008041041d140c84d03a0f8032081103005020a0b03000c140da030b142034186240711800454a12000c2340d41d120454202e8440344c0f1654003485644c640c85e071b0a03c02220011405056030880b194102c0c134243c04014450120b40714114000e2450074010058032100d0000e000380000b0301c400345440f903450709451924071600000610b90000800ca00350481003504c4000f03a80f030b081d200390001d4100d0952100c55012001c030354406000c0c0c03003800c0d4680c0c0034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 907927419 1250 907926169 907926197
    0x111903020c060c0d050711063709090b1302040608040b1b091c0210080105040c020303090a0201350f2401031503140d11070b1c1e0c 58
    0xc0c41c07240b00b011840c1907101c0301d01213a42e1407048000e80306540c440d9410304540d4058030700080254024400100c01584600d00d07804000144002c49400031a0035140b00ca03072a030485002506501c80d42c8240107203a03484400d124001d41d242c0340001a41c540303c4400310345542c0c0b20f0718010803040701102c044513030020710004200036041800394840b100600402c0ca41c03508030039030700b070000c0004100326003400720740c2e051407010050391099900030049030319a442285641c0b40200708000e5844103c01181950001c0040c040c81100214104580c1d030340a0070a6903c0c0c2945040e2411804100d59083c0004100019104082c1144407500c1d405030b030210744c00ea08251940e6055240880d040c6c5041c6080e21004810307804c4950081d0855000d030f620303100501882c5640c0c0d0b10b4041521114000c0c00c5640c0e000402c1400300580c11106c81c01030311361900004d1007502e0030a41d5003040c611604d81020200751480303100d41d011824641150020346640d010fa6281c41c03100301e134800c003c0d0020a03841008600c50040c1202 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 907928669 1250 907927419 907927429
    0x906070b0604110711040902010504030f12030b0f030703080a020708030a110d14220b0a0327020a03080c072103030c081e09010207050d020d0807050a09030b0601111903020c 76
    0x1032490380042403032205c90a520f04000092220105c102d040c0142404004040781c1e805040300680703401400700200c86c2c070b41101c0007401c8075006007117540f080115010586032174030002142d1060300d500420325682e4990942c02645448600d130300c8841c0c1c6101c00542a00421f90102103030420502e131030110740c1d0300d0305201025541206891002400c40e001031152000340c4040841c0d407200141d4290b0308c50315540c2c4504c0700d1925035110450802c08603441d00108062080000c1035a078142c400002e00003503044059000515418140c0b0000d001924081078007050340380140420720051440204002d5403100c002c0300d044412000744000d0303010a24003411098014040d10f08103104502016268900c40050b1018405955014000c0c2610399406c0c0000000070f4000c0000c401146080c0c2c00418990300071800003424210002d00c06003c00800348154105190005442e0f02a81d80c0400c0d100002e550720b00048540e0365500020140350301c9146c003942c0b811024100c2e00d2150030f000c2d500351025034a210085c0f01e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 907929919 1250 907928669 907928677
    0x1091401031d07080a0c0807030f080d2c10050108061303051e131202030a120c0f060203100905010305070308250602090418020112110906070b060411 66
    0x880010610801000541c8241d000621a4003122540c06540b002555100c2c41e011494100040a07401035102c2010b0003e8014071600070041003004280721401d6544408583c03500d00750040c6283c2c0041200d0491b020190486800080c4080003004000602c9501c141d000f0484402641d0b103004440640c118001d41e4065075041c1c0e848000106010380342d017080406042d04010098003007000a104480749a070900d82109203000030100300304c0c0c40d00e2403000e408080101c5540201101644644080e006843c04a0380b4207201c0c0c4c02440f62400e8022201080d03640c080e44040040401e00305010301c0081008580c0a1030043c0d035426481c0c07498940fa10449400c85200307000141541d48110310400000e50024010002d4651512010314082030050030700e6041c035000030086a0903500810260043e040c40c0c407920046c100d0968802412001070740011342401c40c41100b02d0b1180b40c581c2c500d02c100300292800c0390038800c00a01850740d03814032814214690001900c07c14495070400c8480c2000c1c40b203a4040c1c07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 907931169 1250 907929919 907929929
    0x309031218032001020d0e0106060813200405070f02060106021b151b0a051614120c030d080901050c130902130f0305010902010f08100905040609060c020a030e0109 72
    0x401501a000c0d1016511000f280c0b0b407440000c20394100c2c901d80e041c42070024045030001c8075000b083d1120f80103c1d460a4610581102041121280801c48000c2101a8400d12641c00c10918001c03104200540d424080c45d0007010360b003060034202400741c03182e80003410802c002c02d2542a42d0250740c07908000c90700c43c081c554500b401809100640c4405240200306044682d0398030761004d24001181408040a0000c40052980c2d0b4001e4010002803010920145202042041001942c10b00b0104215403203501241c01601540c05080810910682000300114007903000b82114200203460700300402d002e00c1190403030717151750034280490701c00480c00d800c1e600394406208000403518203000300c000c001d40004203000450387c007401001410109601010010f58060302c0045051041030001410407806000c0041c2082110420070141304040c0381c0403010f4034803c0300081440c0d1128105100a4021031101410300303072400c0e80e00c046031500004c03008401c51090b11142003503803010005448400f013074070031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 907932419 1250 907931169 907931201
    0xb01180b191e091517070b0307050903070e0c0403063902070b040b070303055a0613020310030209091009141b100f110d03090312 57
    0x280031000507580c400100c5800b440078501c8a0741c0e244000c200351584050408070603c101071040c4613030104449502c8500111000500e0124074100f0791100500c0020541c408000020484508698007402110000c0100a03404582414514a46032480e0311a2004035510b501e0205e0b440000080508440a916148541076460404403103c82002000703504008046001350302000c00c10603900e0380603001600380701c0b4020361941c44070301d000b0701120000307072180c06003e1071005d5010000f40c440c050a010b80e103048142c41000541754030181e0511030800c400f024440740c0716520500803085070703004501c41d0310100c0b60340002c040d403050b00c90202d100c2030300c040700014a020390600150030201510380d000080796044403500070380070641c14210703035513120704071201800403414041200040000340c40607448408075103240d161200004525142983c24a8244080303520560030150150a640b07101903925001d841c148021030b0401001421201c0003140810041e49064010341c1c11031140e8407000303240100c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 907933669 1250 907932419 907932469
    0x1401110106080303071b2a120f022701152c0d0218040f0c0b0f22051005091306080a11040e0114090606030105090601140109030b01180b 60
    0x20100c07400c860101084003000d600c01280c200248001c0ba40210500340703000000141c4010520b69540c254040d4840440601c3c00a4084049040111846e003250760444901201d100b48120607170b8062f5940c49080d000d0302110b03000040c0489210451418001c071980e0300c411070302c510003100040480381640d07020301d40f0032901c00c4011402d03c24600030f80c180c002010310342c01a400a682001c040b500300c034212401850030040f0401c005c44181d030310002d0860700d942c650805850550344841d5000781d03a0158244519429449195410050080064907010f01b010148002110300a01258018001507020b00c0312844010303070700e4030175108a00690701c20364082c2000c000980c450821800c410400e86a019568116442d20080244601a100480340c40381c44018907002c0c8416040c50380050110340aa41800c04110581d24085202419a5480096503251010040048410003c01d170001820032656500200c3c6805140c0911120301300b0f82c00c01444050389007418440460910810b01820032440c1d6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 907934919 1250 907933669 907933681
    0xf0f240804080f0f1c0c0809030d0203060f2e031a04050907170a02030c060a1b030c17040503060a14011a0903101e020403030e010c1a011401110106080303 68
    0x401088404403400006040080038131455400390300501c4d500c1e5003811200c4840519449502805c01c0301c400d10b0900795142d18011030403079102e1180030000c6503100d07400000a078040da6131100240000746c0c05807026180e00b07241200c150109503040412000300414800d520310281c441d000f062820001c0d0680030480c0c3c4000014440600300c0541482c072203008001c00801c24103100c0003041051100d50006028a04880c0141800e00f00142820381c0600d404110401e0326a0700700c2c501000007100c40c1d281c041e511100b410210b8840d800c082000308410100000350300400c0d640000760003a10011025a859600d4141c1003104030b91140c944c45682a90342401000341d015070100c0030380784010323001a00e4035045070440081d09240ea90860160050750341c007414401960009981013030300040c840214681030964030080d0242c14485005410007003910289810442410340c4c01c1032240d50146003503299611884081030300d01405100b40e0000e18012074010b070f082414050001110861405180346031520 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 907936169 1250 907934919 907934933
    0x200105070b071707091a0f16140d051305030d120c03020714010f05130c180f020a0c140106060813110904060f050606120a0c03060f0f240804 62
    0xb040d803000d221020300c684210080105056100b0007a69981e0f44a0f24200100100402000240e00c014810180b10312005680c810b822944000341400030707040c0169a914282d94402e0380640e0700c000c1c5000d0041c01d140140c4e0810060540305040300c820f407417603649030360516941b0014075280d88000380d102c145100c90410903500400c5281c16524025103084010b440350000031241c0140c0b10250b0395590cc4010200b0442d21a440c2c0000c8030f02d180c02218502c0ba03d9103501800a07000300800611103500d5070034070914640c442c18528284040664849641000141c04110403500686054001d04107440c2001010f1040c10251a500d8a44418a4480320781031140344a007000215940314264000d02100c0d990381c20540c0c4928418440812503150500b42d10b001d4440141c126405400144064100403080c82041907100002882c0020800540c601c110044c00a5a1011402c0039810002145520081c0f100c10b05840c3e58070041e407442680000d0910203034400c0c0505000056045011400007811 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 907937419 1250 907936169 907936171
    0x190b010914042a0605030a0f0c0203070602090a030b041a1609140a090905032710030b0a030c0909020429100504090c1e090302030c13090501090b04200105070b 70
    0x791484107000710782030f5820344803441d460b0041c401240010041104098160007a0784000300000c205100e83c125180d4041e541c0e000e0f00d50028089a0007066141454540e9401d041c01580c00c403601200d01d091904180ea12400105102c5000000940c001521035800d900042c101c01c80c9075568010042c03500c4105003000c1074101403103601421600c8000345824080c054182e081e07011381d01455494141c3c00314000141c0d001c10080c800d4486821a0301c04076541d0b081200031300d04450901040800410002030b0000d00d0540009202991130310001c50410310340c1d84000402803098804000c0b0f020041803841c2d04850303610524105110b00384441180b420181462852001c03182051800c050b198000502174406842400b00005e000d11001c5041102c044c4c0702034071040180c144081000d0035600825104c000d0702003034900035480303005000e0700046141d01070030b0031076004002081b80d14801e140c2003024a4007a9070903a00a0b0581d40c3d000641030392401103100f51031050f101d103840d00e4625a290345035554 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 907938669 1250 907937419 907937453
    0x50d0503070206030c0901110c060d020903010b130507030b012a020607060504060c1e0212090312030405010b01111515130c080604050c090906040905010e190b01091404 74
    0xc10710204006841c0c0c140694080c503c05c0ba010b58541101d100010300420421001c03408176030199003500b00b00d4503900300b1101c41102000015903210740150109000d8510f01c00c00c142c00410202410b0088035265212600440480d682404012000c000446204119003000b0000900851200088400c0c200000801b1440640080e081211507281c2500702d44c0c0c110703800e072078503501c84d251020341c036134081c032a80a10790354680d20060300050072030006c1d0754176030700821809211000611410903513010005120302c441c040c61010b0b030340d01d0145407a0380608030b00340e81c0c1404515044c00600b00c01034040341c000182c00301c20f10010540d90383c18501fa0011113480d140903030000035103805400840c4c0075000f00141c01c500b0307854022250500c10184001c4510003031010b080060240b00c00703075450707440248007900002c040718045a0b128090514500400d40b15542211038814412200c0031a084280e02680040c0140c0038101142e0361401c211098620390030010382201c0e8004e0004001840da0f20240800d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 907939919 1250 907938669 907938673
    0x180a0c182903072720030a0504080910020705040b0102031e0304030504050a060503091204053001151e06050d020c0f030d09050c0d03230903030a050703030507090f050d05 75
    0x2650707902031221129940103080002c140d107804410300c0700125005d030701c2d605000301c2c02514100ea0305011500c000d0101400d41d03403405482e0004202840b001c1f1050341c1d65050010990082d2845203840030b90341e01040c0c41998000c0341403801d40c0c2000d42c000b1080d1103480d00104081840110442c3c50405280e200502c00c809006050202148984a088074540034000d00e445407a542d08016034402e1805000c2c0c0c40000012904120510040d00d07403400c03102a880c0810300d50301c01e03040302250892412072051b11028480d03103018130908104043c9400c01007101d4500041801c0e52800590f0420140810700170b500205e4410040b10083c03100d29401423525103070000585001404500071103056610001400940759100c00041003403007000d10041c00184811511403401d02e0301c51340d01070200c021040c81220350140f1500c1c1d85803180704100807036000940040a503a542e17101314501034425040402c0030381c0000d01d48000154070501070034501c001c0e601c0120178501543d01c1c100800680e0b8103e044100c42e18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 907941169 1250 907939919 907939933
    0xd0506100f0f031104030303020901021011190c05010f06051002030703021e011b09091d0a02060310080a030c0326060616080301142d0108180a0c182903 67
    0x1681c071304c5000c3c001031440f0ba074003da556810790000a1500111809907001b092030f00e4a40f21348240070740122064001c80d4048100310310500c034416034111001201c0900b01e5401e0145a03191540c1c80d50041082e550f08590400c4d0300030b14480c0c120384e640078502005000da071200890705000a0140b520400c590840800440d1400284040781101e0b000c80e954030b030115032896824000102c950048118882c03058903100a032110070030b0515074420b0b00600190181d0000000700d00b08a01030305142018000d284101e4a880a4610b401418814051401d900240c0d202c00c50325080b02416a1307192200e58541c07072020301a1200010000f1541c8044c0b52824050410340120000801401c083c42c0206000081e43c0100f0f030384d034418010040002c0862814500b0350680081503c1c0300300c02c4006c080442840e242d031003659945200003124565034170103002c1c1e12622000004000032441c036001502d0b02c0f440ca1002503081c07500d6400a81d04405000049a410040c0314006149546002905440300400b19111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 907942419 1250 907941169 907941191
    0xa0306090317070e0d0204050a3206100f0e060c100e07060203030c0d0506040b04020f092407020105071a131103071412010e0f030d0506100f0f03 64
    0x480c0c40d404801c4021038030035a08a03548a40c0d0480c0c0d035502c11070a041c0078400454000001c1c1d1140c480090003803040e0b0b076034804601c16000d075034000038030982c4a0f4440d9511094424141403d08060101404c00c00c0700600002e0050900e5081405401015100c2c2814031607088030035140941000007180d0059800e1185680c20002000480d014484100c00054503045400c490350402c02d13507800910641d13008205010dc124200d01c102c0b503926062020000745610f4850000340640030007001c0b0355001c0c0c00880d1500301140800010503900c0320807900d0503001c0440f04140a0107c0c01c882039030046090074040617015500450082c50954494800d00318500c0300301112040c0b4500c16139581d4200c0d855122000b082003801c1c01e4090a03000c0c1200244042d510307210090050400b07802c402400b80d1400da4140c54180c10035008410300000480994841010040e40b00da07a94005a041622090130180456403906126480c005018805da803142600000d40106071f4015112014040c00c140e900d801e4501c3c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 907943669 1250 907942419 907942421
    0x50609030a0501151e060917070506030a020a120e120703200f0709050603061602011b0503090c180403030203070c0f06150902190e0a0512060106030c0215070e0a0306 73
    0xf050b0030301301c42618209403d042e102100a03071440181c4500d0503c03030070f0a20641e5040302c0e03020300700d42c059500e8080388000c1c0300300710341002490350103190400800b2050050100300744c1c001c3d100c0c552455444442c109403c44a03002514010f1a07101c2050704004074242140c442080200744a50182c101401d070742d0b4120f51200b0f044016041d0100e0075030444580c0d4a2216400d000e588006c1005003014001403e2000010341c030768001600c420701d6442034809400b4510b000303400c418461550040a028003c0300c03c13401030510380c030807140888079000705a400101c40c035240002c0883e082030b40c0d222540c40d0b0b9480c1c0c0c040d0003c0d80094451400d1159480c2d46e5400524588800900741d4801e01001c60022101a940303032200d00300da0401c01c1040d005208481c0300c0079003070b07110a4010050f032074903240c0d02c800800812000551500700b0354001040011189500000003001c1e4100e0780c05540800150011107002c985810f006180803958030600004124250303c0740d10a00a07100703005083c83c01040d80c030340d2108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 907944919 1250 907943669 907943681
    0x13020603100302030c101409011e020a1e030504050d1a0403020307120903080d091104020d090c06020c010903080d180f0309241202041205030c060c0f04050609030a0501 74
    0x1a0851014540900c00c50606200d05c0410140a40d9440a03035000d001d0301070210707081801010300043d0003081e0b07072001c0c1c0e1140362060345555415aa54807962a5140c00030340310104c03084213560362101d10361410039204003543c1664040d50144d8401c0d003032504102c2000f444241d4000141c41b50b010900e131040d12003d41680c0a800350384650002c5640c0c490514202405c00c0601110101344450100100007088124080b5000e400c007400e00018100d80c03a1070450401401190b0031a0440d2002c5042c0348071010903480071032503078014070100c1c6641c0c0d950a4106c8c0e552880b141100c0c005840b400b8100001501c507005030021061215000c40c4542450780c202d080304080d140c0640f40d2141c1c80940718203064000e124800030300410016031003a4204c1580c1562209580011282002000d01c240024294181d054801500c40c3d05a0b9104c00d4440c0d00708036540c1e8004825040484c040c2001080c142c4200c0011030751084103060300c1606051400302004032a030841d202880c0c040c0900541701001034000c0c8954 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 907946169 1250 907944919 907944931
    0x8072307140607051b010b0a050d2102100f0216150902040f06140a061b0f020303030a0903080a051512150c0a020f010b030c0d15050103121418060313020603 69
    0x25500c0388010316125840410005e410600c07179142c1174050103a5203c1c0ca0907501036810549107034042c0f01040c60711014058000410071107178941000d0380d08480d68040382ca070030443c2d0207241c140041c41d19401c07002c04a200c0d140d02c044140880300c159000040d546440600b0001120030001a10b500c10f030040b90039074403c800c01ca028541c0e601003c1c020b00340c01a001130b5020034182d4408069506058010300f5840f0042220554000714909401c104015104d000c520281c1c090243e07902c03400c0c000a01000f0380a46503049001c203029400103000703000300784103251007079034443c61000c2010b03810001c0c01100c08240040d00761a01617020503440e51424900c0c6540104072409200344c3e584090302008ac2030945c00b80702800036034180010315116540001f90b02102c40401c64010710380e900300340f92103002410910004000da82c2400c000005000602e510f0201d080c46903104d240e040d00d4100414007040c85a12001c41c050113070801c0040710f46c18260040c0d50b1203500c0750b184002e10300c0f150300090300781e410894403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 907947419 1250 907946169 907946177
    0x30d0f050402130b090a021b1c03140405062d041a0141090f070912030818030904140a150b03070c0203150103060c08072307140607 58
    0x103010442c01c02c00364a03480f500d6103c100300036015050001400038100035145603001c5030040780c0d0641400e403040103c0b104030701c0d42c0c0c115070b4079001c00c51400c0d810b00030754100c007800f0916204540b40e1140c0036280c020f1099038000003034000c039a940c2d41c0d031919104828078003040c0202d0301c400e1480080b9044e0146030090340a048000b006050111036005800ca0581000140718484001d01c0110309419001c035036000c0910042303070300e000035601800507101c9051030a90b511000c0001400101d86001010a008428994688a01588500c50513a0120302d010008001401140008505120020100e180d0a0100084c3c9180c40a0600003c003a154241d8070388402030815401c2c010000307024820722035000f002003000c8000c10b240c03d0207201c0e14080100110140320800d4a51400c56805201602000420410304645541c407824884001c00d080380003030000c98400ba01280d00680505503094108000c808030300941c0f00e444808001c241c101113011201c2e07100043c002d540b10320040c080f2510440803691 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 907948669 1250 907947419 907947421
    0x2010f05130b07021c0e190b12102d18020d0b0a0b0403080a0c0b0a06031104090b0a09080708190f030606050f03360c190512030d0f05 59
    0x1005581580040c02c40c00641d031000305c0c13280b1407200304114010b5030322139400c1c00c1c170a400c2c41d400071031040200c01e00c017035600c41c0110801083c1d11032404003800c0b0304101c11201c80e40319aa11030b154803402c2018054041d4440c158441c0604201d181146410007003501c0054001040c2e640b41140600044410071810070342d00441c03d510002c02034861140340c45421141031520300e02d044d103101854130aa02002e022118001014000940141c0080342c00300c0c0d00001114481c82e051240780001d10780f0f80012125464082c2c1004074034586030081c484555042140000d054481000c220001c1030072510032100340782c0c14059a0086162400644007816074018071040007103240c1001821200f124108078107251415005000c001ea0200075107818400000c4100d0b50b07901c1d224488010180b0300072801850500b0200301d00c2405180416401200411400310340002d00d41a00b0082d0241c14050b407420210381740c40003000140362020610300d10700d264209480c42c1c541400c480000380e6104517120b120150b2208 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 907949919 1250 907948669 907948673
    0x1b0203031201141c080301030f1b12031704150c020c0310050604060605070f1509050118020f0f03060f07050f03090601050307090c0f0e130204090501050411090a1502010f0513 77
    0x131048814100a500008403102c042c0d0307581070750b400103020141040b840304440e601008080c20030b1060041a04a030315008a5a482c0070010070060020201d0009540c50300b12180480d45011f01130203a41e1101000046040c0104041c00030301c442401542184511125206d4035102801407003180c04c203100000c030706480c258080c082515400e82c01041081001c1003003802040960400080f010383c048100325003c02c05480c114050940c0c0e00004c0c105500c0c1205013401c102164500122851080e259800703450020001c008820070300c0c811b92074244d048000002c18040121105030350000d240c0c14031a041c0300c160403121000d07800c100c400490aa003e4001480710b0b15040200e50001d041a600c2480740d12450500100844818840d41c402d00029900000499950009020010340500c500715204d0343c2e07900c5a100644020b1158074045c6140c02030340742a0b201e0640883c0c0300140c0141850300702516200c41080c5001c41804801c0455507a0050354040c17006030b001e41400703a50701c1032000301948114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 907951169 1250 907949919 907949929
    0xc050f0306190207020a05100c052815061212081f0302190803030a020a0915050f0d0209030105130204240b0d0204080303090f1207031b020303120114 66
    0x81004944207500c49000c100c1c601c00400b000502c24984200c0158807504184045000c403511074203c0c5510192240030000e18650040c04002d900780241d01302d440c880c60b0f9a00600303a031894007030480900554000220049548130b402e031a1003030700c014000680256118525048911054000c480311b91a81e080c40c0b0b84544c0c844402c030307000750b11101000c0e0060352060904401e00840c3c80000d020360143d0f1042c1e91480c240541d034100910241094035564944098184000e500000f4181c0c003140100c01d0100d0389201c00c410919509c41c040d250350780380c0000c0e00ca0f080865084154040c0d002c540810425059840030700485015920b01da00f4110106014810801903c46004500d407070148507050f03110110149010b90021950441181c03903654031260300c5640648910342010702984000002e10111800001e15807406c21558820380d0a651489085010203124003540500000c0242d20920303150b801c80e08050b011584001c0c1281d140040480441484500c2640300000c04180b2208030440c90501d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 907952419 1250 907951169 907951189
    0x306090c06020c06391c08060a06050319020a020109020411071104110c0118050d18261c1107030f080c0312010b030108011d0307061509090c05 63
    0x1c1d03400500030302581030011442c64080c404070300414104807030002103a0340700301803008030a4662900d1086040d50680b44290f5074a10040e6101030440403404060301c0510450342e59028480040c20002054900b07c000c8803146c001074544070564600c09400a0a0307049440100b1100900350000b0500c41c505004000c100e070031294003802c05881c03c2280030001244503c00e80c2036500e044400045110007443d900e2042c0c0140e1110304103030f40c646443c5a1101c90014802c00100307100e80201d48504000ea24102c0d00049004c441060050403d0b500340001c0c0c100000200e21081911803490118165106882c50304144c00046d1805004040c0c1244916500071060303034110081c0402409494555507925081c242c20042c068000308012492a40203041130044951100d0380f00c500190550310740c0000055903000b880384603103540c600b1075a8000c0c00b05e001540103401103007101440c03c243e032640f20354000d050300054440d142d80700f110002c22030403e540b007800361550140c00741e80900c508003024081d06040e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 907953669 1250 907952419 907952429
    0xc120302160609030203091206040204050a0207080a0311120106030c0207152102040e07080108060702060f010e0709080118050f0606030d110304120609110f1f05130306090c 76
    0x80100040303601d0400d0092080e080c02c0e4002d0700024488440d0900700d00b1801038081040c1d00c0f000c040948d001c00310001412074001d40c0203d404101e50303250482ca007800ca00c2206d1340144812018806015030300c2c0203600004840e400344990b6850b0106090944030617030401d8010b68082961403056030b80b0241d0400c185c002801340c4d0034150181c0141007a0140c1a0201c0c0303035801c039451a081401c60b0303c103803503601501d000740076068100510f03044c16030001d015032109008014031441490000340c0407510025406024410700c0c1e03c1e4002507401c044074080c103020020000c17000d11100d40b10016000c08244104031243e820700310804002d2a15203020750a00701c3e0f003464510507910100501484d560042003500302c040c005d04005440380110501c02c3c0c110b0049922203c01d8100c1d401c500d50034410310b03811050905114810030740d0881801000c1207110006410b026030010380000a00010100da030f52104141c0e10141011800c107000ca12103c074000b44560811941d050716521020100300d00c20a0200c0604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 907954919 1250 907953669 907953671
    0x6291e0a1b02060d110415020102040e0f0402060f03040f02131b1d0603091609020a0809060f0708090a0c031407080d0c02060d270c06020d120c0e100c1203 68
    0x854000543c00c0c01076490b4403403580d030b60760150803103400484210780c02031200019a030056018a14082e00035081071086a06000d2410000351403032010409291180c4e50003000c507403d0800ba070030030310002d800c02003040362010303600b000302d00241c0c1d100c41d0f01800c0c0a48002c004213020349440da4a0b50704080380740a1206214080004880343e80280c1c07904016194180c543d140c8965445080501d402446403e425100140d1840131038154616001401d9002450b1104115511046c110f10760364001203d410180b0300307202c00414181071041a0321078000055504450003641d01c0e0b200d611148159610880e1784849008208500032000e001d401d00415580001d05007540c40044080e06084130030200a01c14039002412414648403540040c2044802e03e400ca24209010019260032080f46441540c840300b601d400080e40d540300040e13414440811b907980c280d1302190029524060028944018103104d90940444d0040c0c84205140d41070080640e60070809d81c0d090b080c100c0c0c40c00039044a0301c00305 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 907956169 1250 907954919 907954967
    0x50909101b0207050d030903080a0e030c1c060b061902030d0c0507020904150906020c0f0f190311010e0102070b100918030c031101050106020c0906030106291e0a 71
    0x281d008a40103040b18130685000039446480c1c9011600000030b504010301070800800e0b06040c890780006a54600107041d012907405542540400946480300100503124035200300266000590540100c018640c02a01301c81c2003200b5501440e071006542e481c0d080050348003041c078031141c40325800b4100c503814243c00c1143c80c01c5120340102d40c40107001000030740500c060f101c0c0030f001100194401c401198010008545a8604000ea1511034801852540c081c1c415490004143d81c4d011540311716601c504c0344289520300040c1d40540c0c502c0c0140c1031010403035590307100400c204c40b400e000421003d4420010b5682509e01058a545413a07042e400c069001403904038a590700b008843d6040b41043d8041c1840422025245402c03100f090520384995819400d1000005525030009155408090103c605c2e22059480e0001d041c00c8810703512030700364541d07034141e5220051000c48048510404803108014500f40002c41d0324180e02d50264105038041c8000110004000d0340032120034100120740da006845 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 907957419 1250 907956169 907956221
    0xc13030804062319051602100e09090106060f031a040905060601120501060c14010b030d09151107030615080303190b0103050603120a020c0d0f17130308070c05090910 73
    0x4403200480005041c0b14001904070900322155210b11041980142a10102d81c9100303401811440100c168900074410003000c1032f40008103004000c26030340543d450120560803644102c0c050032030201d000ca58154103c00014240e26103000c0d81d03030428010f10041480f810140001048040180340c02003010740340000602801d54026080038010340c02502d0703080c0700008840720394010043e0307840c000c4d414402c8059209010340c00a5244085034100e003070550b1001d80c40d100950302100b14000090036504404800c0c400201c9540c40b41c0c2038490703042c690210480d1140000381c41e40e80700b9520690b640e4a8080c088051404902440011070003c0c40c050000e401d10501003980d50f0070a001c401c85080d0b0104040c2d580d14820403007601c5c099801451689602c10300d04260717240d603002c01001d039102018140210b8810f0240b40132200140103090043c51411300c0c41d00c8000c0c1c1c40d0010401204c401640c40400601a9103402e0140c0c000d18003040609200740c44d0304044421900d50103040c60012940d02c1080c10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 907958669 1250 907957419 907957447
    0x10c3507200a0e09010b0102060a090209270708010b1c02090a200d02190c0b1801060e151003060f05120f12031e040206030c130308040623 61
    0x82a80c854810841494103007400200801c00540040006942c55001c00c451001d05400075020345030282c090710125103500e02240309440c40180069041407a040100381100103100130004007801c4010580100540385042ca81480019808400e01ea9100d202520311071900d0035103041094402070301c0050048299000c54003044004100300805507541d03c501c03403502c0044002020700402d00b5070081d0383e131400b22220802901700318a9000690b9040c7c506200840c00f5015071030301660490f0999006580f90048541030407482e1b8595501e13552507040005402d4522145c13079006042d82c100d5440504002d0f8103000700d10b01c080c4c1c2d82c0010141808c00402c4103118401240096410540790a200b1030000d41446242404c01e036032422807489101c0840c44c4591914003e140500ba6034880503209001103054001007480030f44010b54042d404102140c03060441e680100704c800b0210010b045078654135100d442164100c0d038805030108508145a18240c54440b822084110300807180505120701c41e08004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 907959919 1250 907958669 907958693
    0x902031614040219080a24030b0606070201080615070204090305031608060a150e03100b03070b03160f020f0a0c060e030105010f090c12020c0c0414040b15010c3507 72
    0x20a115041c0041030340041290449187c00580540310004040c5115944a01600b144000e0324030036545404144140380c040300315900c181c3c05a5607042c25480e844200091042801705054051100b00600001070319a40180f6031b4050080d141c064491800d00e01607110411030f86640d1080000035810003e40d5940d954901c0e040e100c03c12244420b1110111065416400c00c150040c1d03d8400c08201c00e10403490354018021040b4150241d07400c40d03650704090841400b00380c0344103000305041d43c81d16503107030320542d90025803569074030441d490007241d03240c0301d030800010360819111044c64990074005140c0104900c0305072582030300204102e40c0340203521000400e20b4040d42010359140c0c0c540c029124410050306804070640a01150740b880440d8000d0340d03a8041405060080741425868005e841c0c00c0449144140d0300155080c41c590755114804540e000b881090b141800442d03911a00403c0c4031600c0c0aa000c00060001414086c000c200184140c0ca8001c004400a5040010b82c00143e4484540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 907961169 1250 907959919 907959967
    0x22060e06041a0f0f100905090c03010e0604030e06071707051e072913080c130c082a0c01060905060d0807030809011b020303041101030203010f03031209020316140402 73
    0xb500c4035468484a80300c1c00d01e140c1e1b12900c41c079030400040c0030ba402e0000c10100e41c032403c11402042501940c1240d00c0c6c554408640150224605019458850030640003c0082900c124050b103080074800401c000c1d190000c1ca0b09407200d41c4221000745a003541d2910004080b1895070003400d56030700c0d0071140f05424203100d10b0408501442804c10a40d001c01e072080d54892500c0c5494a1190f40d00c8100b4290340e11a40044984190740c0342808084074078980c82f540050400d990b031240820b507200002019282490000c03101c441100d543c01d001c4c4445200d01402d2a1501a4004101c103440c104004003540c40240034240f003000c070120054002807080048601099150415118540c0d601d0585d50040c0075031642c2400e10101c4480c601c2c0f49603404002144214410300c1460640c10a0000440403400240940c22480648450174008603000340c0100e207103a51180c2000c00c9111155002c00d050040250685030b007048401c5060140400c607994804d11038506982c01c505201000c0740140b41107100c2c40032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 907962419 1250 907961169 907961191
    0x4060b0f04060e0d0b04150f0b010f030218042f1206210303010f061e052506090c1a180907110d0e01020712080322060e06041a0f 57
    0x20583d041e031a07000760918002c1d0844614100ca14090400201010311074106401c03107031034036611541c2c03c4c0d43c9100e180ca140c00180c2d03401c2030781003900308150002d5002403050041e42030321810700012903032607002d000d82d00c549140c04106a2048115a1607000e200717070301030404102050140f001c0b40040b541c0700642c010007c46015640e10b02000c0601d51820724220289240c1c00000000700b60b0f504981e0708103081303460700c1e980c43c1c40704115140c4450007803c50084101c00240e01300901150741c44101040c10f0350140618002a110341196603681c11120a418122a42800c0300004c01194a1f801c1e03100c2d50220010300041d14000d2184203544158500e41c3c00144180408008a180d90b0300c21145011912520400ca43c034140c60503101030400400d44851078010300c107800010444e00c200384101c007a51640226101c0c1903844815013000940301001110031768540c03584942c80422440c0c01401c01010312500941160304080c00d044091303401d0743d11440440703a0700d4020300c00c120340c644c49a07a80c458100c030300b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 907963669 1250 907962419 907962437
    0x31704141b0a450903050a1d011e090b190f0839031806010f12170f071b05060306180402040b03010e07050a0e040305030c090d15050604060b0f0406 65
    0x3c51164030f9040580c01000c294941414a010550002d0007000304864644070028021281c0040e6250760b4003081200c0c0c0040c00a844e002c0c0541c2c03c040d440d404812140c20030866072510781007189041d402002c4004002e078000c034514010320b5002048000c04400380d00d0303c20300d20720301841c0c0b1483e01100c2500d0300c10081700480d0210002d03840004954440da41045880b641c0341000120300c2003640820321044514040c440c00011403664000d0700d4400ca4030380d40d2a0350001c00c4e4a0f01c424840048103001c0646115081007942d104489002c002c20009104008103941c07142c1d0440c0c0f10400542542106009403000c10920a02d40d4030410041c0741c007061058022141d603543e00c00b0030068004510900e40642c02c24280c2e0400043c04901402500d005440f01040940d83c0c030038100e02040151005000b041c020804242003080c120000c011402d801341041c1d001c50302581c1d92048020060070242249981c803030600030185010300504005040d001c807014104400c080b4800f600f48510b10407001801400c903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 907964919 1250 907963669 907963769
    0xb0f090d060203130b160215130f1203110304020f060a03092f090f1305160b090f041514040b12070305060c0304031704141b0a 56
    0x84a450035a81c000380654a9043c40c80102c0d9191540400417120200e00d000042d0004610203210202e005446e0b00a10b10f64120b60340045607840050101c0c1d000a010700e00c0240400c0500308081324040c4680a00100c031045407200504850007280c2c0020041000c009200159840300d4070b1145a02e0222030b0740d0381e1005c140c80203074010054500e0051403c101c0c00700a800032010b01004043c1c03002c1c2021000201401d80080003000305007250052440314000010a2810703c04c8001d504a551007801190105041000b080c0f0300034002d580400c442040000e5800c0d80c6007800040d0048030002541c0034001c60f0310481807180d480c1b415018600c1440c060200b6034100e50b540f90840f80b0800d1001e00510541582e401c60203888180324042640c0c10320404010868441c0650304071b078412601960f80c4498082c031181c01c408080f0010700160340440c5a000c10291130001480205040342d0300164881e003d80301d8009000071401607038000b41c5c160503c0d43e249100d40c4c0c4510345540c600406400000070031201c02c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 907966169 1250 907964919 907964929
    0x601091406040509010e120c070f0e0411220902010e030604030818030d090c0e0601050c0c0907030e0312090709090c0e0402010323060405060909031e090d1b0905010b0f09 75
    0x3c2d80040c00700c0c403841f2003200d80c11013682c00600461110100b0342c2e4400d616440c942e80182003610425409406c1c880005020075620652003d41c044014420002080c00c001c1c1c0b100300044410b800b403242551403c64100719a0440904000c4080690141c807032407a00d6103014203000001804c41245100d1950000c1d102c400030f0044582c03c0780c18081c20409000719007051a4020018000d0306655074420300070400560256041c0c07070b0110101c1005000000040c000c0c84071119002e0070060515840310f2a400700c2403003e10150452a0f214106240c031850f00c4800940781c004550300c84202d00b85046140c0b004070b2242c15400c401d54412543d400500d0300c032440120300600c2e0002c10803680f00d400240c070051940d800c210382801007004807010700940c0c80700010806178540907207a01355242d00400420b01404001518102408040301d403090804e058000441e8994108600403030302181102c0074100000700c0c9501c00006032980060803c000e60400090545500c1102025043d080001ca13000c0300717540c1e07a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 907967419 1250 907966169 907966181
    0x1060c060b041b17061c080703020c090108030a0305220609111906030507050a05090906010e03070603021b060106021f0f02040b270f062206050705060109140604050901 74
    0xf99100f001942058610300500d582024680d5024484400001c40c00d64584012003416140d0612a503040c402e0791580c544506900c10502203083d8003d80301144a1640e5119015008018400c06148d0300e5041d00c0c3c00400319503004020f1007903051030148603280241c0c100d042d1040309900180020340305605061131801c40030408103203a4400244000c22140b10062030280040b10f00d5501d00b07000e1b94a906805466500503c80ca00340021010b2102a54520b000c16809401c050181000e0000780304c1d03000820f00b00b00c0d40c5d421080121790005040e824030601200078600c03440040010f44855414040000e440d10050640b407503e2190503072005c1c02c074600780c1d800000b0b51403036808110754171680c0e40c0c3c1005041d08a280d890f0203044800c0d05083d0350225103080c01c07d0403480200102c074800920010000c132604003c503111a0300001c1e085006410403920b03e4040505002c1d211541c81d050586030840c906101600708401907400d025252803103103030040752382d43c11200807600882c850759901869401420 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 907968669 1250 907967419 907967441
    0x3090b0a0507122606010203030411010c050d03270f06090212070e060a09051501030e010f11041e0803181c0b061207080a020d0309050a061e0801060c060b04 69
    0x4000100c3d41c020b541c02c810810786a00803e000c0e01d4080003941030380d06130150b080f6040703805a081040090002031440d00e61600090050501d191801d5940d00c51038900146580b011021a9582d0703080240c88003020380500d40300640d8100d4030035000647e0b49030710340c08585010080c0203e48071311017001199100140107a10031070b2041101c05042e80d5101c0d840c05c1c82e03410744006010f60040c0f28049418216405500d00c501d01c14001d00181807501d40044000741030081c22800d26560714092601c06091502895081c2c40090802685a42c140104402e82c80c411a443c1910002403c504124103200403003075415005c4896000e8002040100101d0140720b82c5e00c0000301881c10f2040400c0422400c540010300804c42540c0900129003070705141d2343c2c6d503d09070140e400e032540305012540051410301601074403d4841d29000425903621b401180100c07106411030004603206920030201c2841029610a001c8290b10301403c40f5454164007902540700684042d003a180c0b00e9804020b50746031a045149003070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 907969919 1250 907968669 907968683
    0x71a161202031b1306080630100c05030109060603150e0c07021f030b01020106270f060f090c4d0102070b06030d02070512011401090e150403090b0a0507 67
    0x2c0113034a00b0030f000600030381d00814001030114941c0c0c00d0690550507001c00c0000500d00d0907261484010013808034041c1c5040380d10506200302d0b007a2504c1e000302c0500400d00e031a03071a100c2d4140280c0c0c1c015034660b900b1081c10946010400040307416809a200100c8581c402d200800c1d131034200c845642d500ca640e4019402031280080c02101100541031031720080243d560400001e41c00c0b00049080e59030701c0c880c40801c4200c0d07035180a00e50190384007180c216118000b001039180c100f10740040c00d689803940280344210240004018000c4240103e40030803004c0e207403107201c3e10601042c40120071491003101515120754815407841d880c0c0350f00a51948001300c91403031103c101505985020b5400502c040b941d101c1c103900843c4d0141000268140300041c02d401914102d401e10051040b0f4002c139005d41060f640d02d41040407450300725807020354013270100030b400403900c9034045904c246014070100401c003618010030f00708008641c1c07000100c0c0a0350580301401c0e81c0c1d0755142104465a018600d4040e1104c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 907971169 1250 907969919 907969927
    0x70801170f0d091d0f1504140f1602031215060d050a06090f020909070c031701120c0b0c061906050306311101030207020a0b071a161202031b 62
    0x854005080300b00311584c0100810b4030b40341d01001100c48507026522003010442460120f681600e1071038003503802544c003920008030761402d460307072040b2481c00303440003168441d5981c217016842c80c40c07801c2113013103800f640011842c20103c1524454050002844040076105800c282909075460304116840090201ea042c0a58240398070f424004003510b22075030444601d8031401c1d2b50080894029a190b0100040004800781c1d6a0081918040800d0400328200315140070402141c1818280481c081c2c04c0900021305e00e07112920388a6101c440c01d400520003280300b8001c8544074900025440e80c0701802d10001d90010007589460000740950b50029541805400204036610a04810706500c0d048401e1103561010030307d2001c1c80d10211000d0020345200040c0c14034078107550080d001410228400761001a03120b6441d0300e003103401c1d000010100c070390860103420f401c8404980032010340c000440344004088886121805030504085000c11550140c02100140c840024a070084240c1d0001094466031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 907972419 1250 907971169 907971193
    0x11030102071a1305030f0a0c02120304051003060e130311031605070e040503040905041b06120f0c091a040f0b0a020106080c0114071401110a080609070801170f 70
    0x86076107442c003010010380c0141c0000c101d0082c01004078156900040a5807500c0b25070111001203602510290080c414219402001a01c0390f1628044103901c01c2c0180d134481c0d0409c802c2010b900d00c0407005008050030141d060201c0151001205d8021520026140402d40036260513110304450302d80c9104c0c203010104118000e0f5480e07408544100e4401e81c240d036601921900c819450100c16100548079910921080c09020b03081d07805650007074010b60b40d4420301e0603a0070080c0411a002d410102c0020714004030714100c0d000a01a81c1004c1e0b02e600d01c00e109090854200426580881c4940c0860f0658000805010f04500303040364080c3c21f04141102c041521782c10808416441810444015841d02500080000021a0080300d000e4140d40d0312000b640d4040064030240c2101000343c1355000b0200004404030380911912000300101c0c41c0d0b107910743c40024405060141c00030030702c0b801040e188041009265100280e103054540e02448402c5c0c084425407014545200c030904503001d80b04004080070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 907973669 1250 907972419 907972433
    0x71509051510060e0618011407081305130b0f0d261306020105070f030921110c0109080303180a0f031808031903020c1005040c1502120301030f1103010207 68
    0x10f4600d29200d08080c03c42800c2804214891030468180e11901c0100c04806076104640c0b01c14a414000348460511055071210400c1d648901c0000e891881102020411401e24410308007070351110000412030054030302d0200317141055032011b0500c00c40d11030580c1010005961184c8082100c0b65142011464104060500c503134824809810b4052010700006441441400f5041c0704140e240e58444032200c1484068018000b00003080303c4404031b101c60f8a155240010710100c0c2da41d140d42c0c50440e140d10040e0058104004101402c2c100510384405010f042c0c40003045a4000340707200c0c5000890072810301d8a60030301483c40d100a040755039180010050552220f901c841071200c601781c0c2e56540340e45900d8203030f4034031941400541307284141600704c00c902d000364043c0040c841c03001c049e108122000b161482c2141c408640450301001c1c00fa00074050045902a0304900c00315600080c003010101c140341c130f0740a00051000820440b1000d4072042040303058081c10b280a01d02030000e64407000c0c1031916807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 907974919 1250 907973669 907973701
    0x42d0902011106100531052d060f03191110030b0906090703020c0d0507060b1815030118050a030e0603061318050703030906140715090515 61
    0x6400161001810301070040e000c5226800b0f4030b081240c02c0300741032510091101c6c9010040d0b41109a01068038140c2201d6840e0701000d0005000030380014076482c1002c900c85e40d0905d0040601c0e0140c0116204004080c00c0b00040d68006204a0b11640c0110420000a103011240f00d0001c80220b0041c600804010181c8000c407101501100c00c4a0340c4809550101c0c1128050901c0c01e03413150301000417800301e0800415654201e0500e00d000351400c0300b007484443c60030320004c0c0c145001400015002041c0401c0348203040c40d0580885660090140c22203002c40c580d60003400903014040161201000d65900b50b012060b2051111384410500289082540d10713082058416404101c0008440c52103103061400c41c0d2142c00028111021040110920b2004204400104006500b16140c003801319004002040041d803080c7c4d240d03074142d0f041100050006008110079030003140180038020009000e90381e000c16851648500184c4003003581071607445e012130303c00c4032007000c240d0700180442103510007510 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 907976169 1250 907974919 907974923
    0x4181b080d0305060a0f1523040b0c0705030d0c05210712050403050a03090e070f1b0f0c0b1902031e030a02160b09070e090304290f03060a0b070f02042d09 68
    0xc0c0076000b08d034400d10303008150140307800d204041b0421040c0000d40c011405004c02990b0701b0f0845e16581c2d00d9201180c901101d0204140114100010b8201004420000200d01015171010010001c186040d4562329026040004280d40070ac00c000320303940751060064074000c6403c10b04491244400b8180503103070f505a801303408903419003035002614032401014030024040c80e40c1d440e90400344554440320980220303804201c0301e826174040e04501049608041d0009401c1010865541d41d02c1d03207000401d01221401e411082d500148a0428a24441c5400c060700361000b2091070b80c3c07540c070860404020712810006600e207100358000c500074404105030f050310030703500041140c00a54031004483c8241030100c90781c0100f40d1040006005071014003035000f400c174079044080040325006003040289604005100c101c034081c0442001000e14100c0e44420060110f40800307460b0a0362501d4030707075500d2010640a07010355200e07020014920031031a0742c6011103082c15001c0088820b04c21039000070704152681 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 907977419 1250 907976169 907976177
    0xc070b0a0908011e020c0309090c031008420406060609050406120f2d0501150b07060e0708010c020703020915030d03091104181b080d0305060a0f15 65
    0x8049800c03841442904c15009140100680d104010310100010754401c01c00a000b6010a0104039a00e8030341c64a820b002c0d00561a00c242c03a4900206049200360240d400280140d1290703184070228869021108a403e486400001005a02103501c4038034401d080101d40c1c250003840c01f0007060119a5000d403040e20040e40e04c802005030748008101c2941e09501a481240c6d0100c04920001411035100401403441403600d0580034254006c00034500c0038140e0021a4800d104145404019080c410f40d04810500f114400b0b2031810700d04410f00c14024006d00034011503070340301e0b6824440360400280009043c0c04000b8018601002002500d0b0003075440704074010850180440c609560202941d044444090000c1094060982048015000080060b19134101003002c0c0c0005459500826450030301c1c2c600061505407013403030400300b00c2205500f0b08064207811101440402c502013501c58514246185c0414152110070000d0480c4002e83e0000d42c0c40300044100256085101b00300600940c1c2e9629 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 907978669 1250 907977419 907977437
    0x1223131202030906091e0303160c240509040b1f0e0607021f0e04020d0603021305040206090d0c12050f0f0c030a0605150310050612011b050f0c070b0a 66
    0x6410381c0d683c003070800320307541c0420b0034040e07101542446050803401041c0e004442e07845040342d002003821035201c0141c0e15204400b4140070310038040b20080d200c0060580941c4030400c05101c411124107080d0a684460030058001245582c6030381e1038001441c80c0f64018160b1080e8243c04524141045504000f840418032000c070040c2c3d82e10b007100c180e0742416000303002e02d064031624952001040080d44140d406220320055012020b40b118409807008218210001074078070b0450040040c0f16440610b10345201d810f100401c801600c6d100141c400194040e01c805521150600c1e010f80e0000c5140c00c2498501c8010001230b09110b03000034035013200c00c181425580800c400d003e905840c0c40720040d03c45c2d00755010608460020b542030307001d103a00100903030015981e0003440002908003124140415a025101c409208c03075468000d456940610a5000810000c0084e07254829401c5c803420500060003030100c0c24060300090002114100c0104400b0b0320f11032516910701c6519a00b00804c03040024407848 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 907979919 1250 907978669 907978703
    0x9010f06030213020a0225030b090d09090b0d02060f030105101e3005011802091c140607110606061c0902120307230d122313 55
    0x1100d4001900d401410003598203a1110348800a90300400301c0b8011071042c8071124014251441000c07240c0194031a000c0d41c9245181450410a80e02900c0e01445402c50a0034415403600042034200f01c0d0450400800c401e90180001a400c14030284065004000025081101024080114180d030004c85080c54a80c4600c10704880080e0818564404082140032444600c1e0140603096003041c000d060720398240004181200d4240840c00c40001d500b91998018070400c28041002d00305c10b02481070443c02c0c0307040342002400c2c2c04002804507000c003e10705c07040c2d02413001034070454000002040c215034083c01c00b044018010a2001c04002040c02003c001c06c1a5251220491310011385da02d90080300034101411070002000501e41c00c0364020000b8400c043c0080381400a040c2503409140070306c0c44081043c0c090702140c401c1240d844c62036081100640b4119030800e81e41e644030705c40e114001540490100880301e0060640c03081ca0007445080c07080040d5115900112140184540c081c103410070110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 907981169 1250 907979919 907979921
    0x903020901060215041103010605061209070605310b03010e0412020d0903060b13050a0c080a1512080702030304030b07034b111b03040f0b0d2309010f 66
    0xe80c11071185101d0130300401c1c0407a8403400924500c100040002404595450010700c00d98003811217600682a003070204502c2ca0401e2045200030641400c2680c1f80a0000d5400b02c030411181843c21210100c54540f0000c91580d152150003409002c0c901542d81e5844003040361681d08221002c9540f040340080c4203040d184045580c1d49481a10b80341c0d03840c080e0540d034610001e0034002d4231540c0c01c508041d90303000d140a540c0c01024003580c4219000580200c1458000b841290020804031200d400c0074081c22a0780444076a100448074000b8112001004a20b84500c10380301c1c2c042e001e076244c030006ca0003105009265141c2d900605c115141040781725004103840480c2124100c650000d0703600c07601a125403901c5a0068040c0d24580c6400d2002200904154411030b801e05400410191004c500c20702c0c01250703840d103900300c2c411001c010350504d4903151604040906900401c0850000810700403400d06094001c055000740754000304a083c005146100b03103d10080b18014810342c2080500c02010701c40d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 907982419 1250 907981169 907981183
    0xf030403030915050c06040305180d21050403080d05060901060c02030703020f06070b090f2b0c080c031204110616061a0316030302060f09030712030e0d09030209010602 74
    0x1040e221040385520f03008140d8948002c4050283c01d02070100a03100d02944144850383c4154440e440c1c268484004000090b0f050080231682d40c010602c0c01000b00205000490900c42e80030480310a6500c0741811008079450f0041ea4401803294a0115803000c580c0c0403038210b14824901a90000c0440e03a0f6510100c030800380080020750150819501480942400041d0b46180d41019103000d00e49942ca41c0c40f82108841103c920445800c2409110740207417050154031810b42e620918041a400c40000c2024a142e15598031030611020750700001c2044403440c00d60722a0385103c803d0b29112104083c902c0070380c0004580484618030700d12420301092800b40705640003015012810036218181c0d81d24000240703104200d4800d07841d000342d100800c6030340c00c00c2043d58500c1c0c10150700c5070721031561401a00d490b40180c503080044410004100c2c1030302c40081903d9101d07801800c4000848103002c410740040c102c114400c00c0600901c9013003204160030114040c2200d100751a07141850ba40e60300100d07101c40c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 907983669 1250 907982419 907982423
    0xa02040b07140120030108060702010905060a050907091a1f0914120102130e250c1502030c0a090b030c07020919020304240e0c0607060f02070807050f030403 69
    0xc05010760340220780c9111001594000080002554407240d840c00c00d40c4070120320034004a4040040144030700c1005200307803900010540002c0c050340055945040d150000140b6461541e41c1d0303080010409501080540c004020509007040405220741c1c64900484200c040d950081c2c03e0182000500040c1503007005a2800664408045504041c2c0c0010001040c0151a50003901080907441d06182880180070b1300b490a4260301c80d1501e46051510402c0c0010a1410318085011400c0c000e50f0349590041c200407020b141402080c0440c0c036001202c0f003421601c81030217901c0402000a07101d8080c009142028160300e98030041652890905594441207856401d010300071b00c003900044c1403c0400d01d80040302d0300038034450141c01d01d116000300e0300102c805441d00840601c002002c0c07401c0030b815060780c1500900030707c03508524021069440d14130302c20b01805003030005480340900803690f000c01c0d48050080703029959098035007424081500300d01400d072142d024a8100103500c902c0001280c040725 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 907984919 1250 907983669 907983689
    0x702100c03021c0f0e030f1603020a0605030c0406030b010507060c0306050f030a1a0402060d1104140f010c030e01030b0316060336060e1905010b0631080d12050a0204 73
    0xa0342c00c1501722100c001001081c0d800d88200301c1010180e0809100c20b40b8004800400c3c0f0f45014658010491031100c154440f8045c08070403c280301c18000c914044034280d0b815070402140145600c8012210341c4103007070000d07105501d044071108070301d64540c11000032907400300d45074921060660209511103406000c024070f580351045101005c900c2c00c800040d402400107001c10308140b11100360b03000740c410400c00d124682500190038410901c80c0e903262040140b0035103e41150021810002e0a070782903c5a002c0e040c0000308502440d140e101e504029040080079041c0c883d106000ba1711211740d88103074003507540400d0034065001c1030004098450708544000003e16404601d00728180c00e40d507001340c201070320100e40301d981454034040e08100090017020b1007088070303051400604001c3c0c04c66005141051052508008030565070030990700d415070212100c140c0000726180c1c040d8031804106203070f100d80c0803400781540e5401040c2e00100c1600e407500c0011401d00044c3e5580081004900c80d80c010f280d217079 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 907986169 1250 907984919 907984937
    0x1209050103021c0b010c020d12020d0c0812041e0311060c030405060f06010309061b090501080c0703320c060f13121101050c04030c14090c0f0702100c03021c 69
    0xa0300b40e6001131800800c1814a091011002d401281054140300020340384001c81000c3d0100301641003100c503084000701c0c40d2864082155581d8864a4400c65040c0004031601c80042014007480642c000700c40907510403007102180700380c07601070b100c1220b030300c810302c06c03409010b000400441c106412240306030380c008041d08081e03541d000d5200011002520a034101a6100a00d0b000601c1902c601d5000c8040c0306015500102a03110003440d424031900309504001010301440b01211031301044d282c80541c10b0a0032004805805a060f8801d080340c50071902000ca14803648484041030b800920501c880d00041d110aa50b42d41c0d40300e084811305071a04101050000f028401103106610415a43c44552401a050100c026a514203443c001c4e214464140300000e010802c00401e400d911000300b12603d0301c0f64880540100007216071200411580b8000b04c00100d058242129000321488035a0040c4901240f00c2c0c1400010720030b0700c0301a400c9000d0311401802980c5021408940007400c0000e540d001c4030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 907987419 1250 907986169 907986217
    0x103050703021522051908030a0c080708070b01030b090f07060f0201020d09030503180606030c040c0c05070306060e01090536030318010c05190507021c120905010302 73
    0x203050300318460f43d40c8502d82400300450800244a400c441c80d03142c0c0c0c407680c50036800c000c10010058906005850800c078503141c2040181808401d49802c40703d44d0070040d4000e9403d0406450381d1140e14402000d81d40001801d81c200481100e0050503039009048041c117594031000c3e100da81d006003000104956001d80c50030000e03036120300302d00407a900f6248000f5041650840c2e141d010748400f0942100411804810845110482ca0030b012800f45610700a000905000001c40e403641a10984036005580f101711421000340140540710580f6130020468102d03a66074244036009111901a504540c95107130000900380f2158090207010b803d54004a40c404040c031003104a08000b18550114941358a40039a541420103201443c40f03100c08222021030203081461050840e0421420441401028000c1809081001c244080301c0e00300b9042840d50703031107140000340f1078043d2600030316102c0c1c800782801000c200d803c000d6071360b003513083d0344880d911942c07074500560583c02107035180340c0304042000080302 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 907988669 1250 907987419 907987429
    0x4030602030c0f07051b03010b010c1b0b0c06150f0603070327080304020f090907030f031403180106060914040207060f020f1b030a12051512010e070905010305070302 73
    0x500901001202443c3c50f501d01c141412070740100100352001c1e000b000b641034242d444034811710b000c03800440007000b0034840754002030443e60700448042d010095489080085141a0010320082c00000500b242c41f42c141e062059034907601141e151000c080a4860100541400c059180030b41200408940c115510160114010b00506100c03d07144180c0c0070844a400032401440800a401100800d90f40d1401d40140701e83c4c06070323038582c807406004400208850307070001007244020340782d1122031040c01c20001d040450380c002100700540500e4200000340044510048a0082d1702c0c80500b000b03101c0c0310341e5000240c0e001080c0b84900b0209003200c0302c01d5801c81c98241d0041104034450a0006080d035410181241240c000b0080403072814070015603044201811004880490003d50017140713040003060000b024204180c05003241710340c030b68010800113482000c00b110b00641c09013500300302040c1248101d010385200c00740080c0900a086c4042040090381c041c07141030b00d4000005048240c55542409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 907989919 1250 907988669 907988671
    0x260102041413110a050a03050c0301030308190b090c0307171b0706020c06130c090204080c06031512060709050a031e0302070b030a060e01330207080a1a09030c030403060203 76
    0xb81001c3e628501402100d200d20007030122080595511394580940c00405000c4410190801080761018401080061342c03103020954440c18600151200f41190442c3e50060200010f9281c0d0050150b1300300540d10b07414a004c1c0d482080b20381e5404d9150860204010468072040d5100c107000e814060006c0f02144d0000010040c6074410341c001031410882100250801105a90080e0300101c010301d08030601080103035400240013052021890701c0c1c5091152a41c4000096103d40100c90100024040c41d8030f03c640d00d22080c0c030250462102042d0810200c0c0c48007000c49000000c501c240c0004101c1c0d0030000c107480c040d01c1d070041040c1516540b8101071403603075002d600124114800d87c0e0012800c0c440d450081e500903184e000c000706072030341469809001c4100580144940f048201310404100084035145002078031740303c080000250a40380c0417410702c078854216071041d116520720030741000340340702d0b450815010403a8440c196840344107101f074a0f07101d000c0010322a544140814070102d03403942d00039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 907991169 1250 907989919 907989949
    0x1003140a060608070302010e2b020a0806040b04060c0212040302090c221802282309090114092e06260c040308090f0405012601020414 59
    0x49003900129500c000c1a10283e4226900c00d4000035420811035811500d000c00700700007240c281b03175004040041d81000140c60034291140d105082c42c18030035901ca051010002d480c025056500a10703003400c11595802e8165011a222803818265030741140c40412609083d40044200070b20301031864007000302402001d0039001c9014001c000d00b1082c1041c07c402440d40c8401040e030307100064501210a4206480241500b444500400c5040d507500d41d240200d2001c0c8a411150440c2220b4120080740c0120040a1850180300c40392800a00c030020600648600002221415140e03078a42c050420034a020114130790b0416400d5005c500703a400050211100030034a80c0f2004c1c44481460000e50f4125003581c4000080360044109011852a0080039650082407610794605030038000c05400c00c074840d40c13202604540f80410740b460b45a0340c209880306415001442805035507100e07413402e411840c1c0e8400444624010141c50b0317440003418000e40301103600308074040205045150511200d020f0901c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 907992419 1250 907991169 907991173
    0x80603010b04050702150705090a15020109081b07142b120906020c0907051e120c0c1005070905090415140604150e0615120106050d1103100314 63
    0x3541081c1d0300c41e48a02c512a04a982c0244a103440740c0380c0303007040804060240001c1040800c00700341030342c030750403084006c0303503c5c45401140341780001c101240141000c100003800500001001c02c2c2c0149101403107001428220192481e03241d4844c0008401c0f410307811002d42205005d1513010850080c00b07000000380100b2240c3d50041c0200380d450360001703003945042c8408144801c9061114a41c10000d07255030b40f500351040130705420541809031041c007540010b1812801c100ba010b1880d541d1080c103072802595200600b0185060411024002c2d4208013800613a901c118248170403541d429020f264001c1c0803948400c02c009081005020307000400600075030719000b0600705030180341010301c14442c0c0c100340c420070000075040c00000c01054500c1501e92020f85103401d40244405003600070480c2d00003008841900b00325181742203649040c0100f0000c644a84809000001c2183e0410300400c5040411601082808141c3c0c1c1202c4043c041960101071412613203406000060a002d0440000703441441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 907993669 1250 907992419 907992431
    0x2909040807061b0f0e030c06031f14040507020a080306130228020705010c02031e0c06040b04080d03141602010b0d05010605100201061a0a1e1d040b01050a08060301 72
    0xc90000b43c07900d00c407000911004601d050040c003580154111420070052070006580d640e0000000c0e44c5152880c3c0540c45841c0000125911011030104180300300c1c403844860070202d41da00140c1d0120400480031501850810000600c60b03480031425904032940628000d0860301c1d05410b0003401c800d0760041c45805542007180c06015140403800c10b41c50056030036a08500d00500800900f080255170000b03043c003001458000040c3c1e40460000c00c404802e03902000d15060301440704d45080d1401d070500c0c3e0080300c0010f0105880b40403030010800e070740d0060100d400521101c103040301160204100000f81e00701210100c2d210607011203882a081c0c00318400403030301000000010780b401c04206022030ba0b03a951340d1070420180c00d003d81f0600f80c0500f40d000030400c25261003141101a14800c4c010700c0603c0c1d000500c0700c20b0500418540ba003120010702044075030345403900c02900b00c0e01515201c42e04c4621400300c140840c07405008001a059041e5940c0d810b203181e1340b1040e40c0240000c1e002c1c55042d52115 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 907994919 1250 907993669 907993673
    0x60f13080f04140a0b09060a030203040618080a11070b0703030c0e090a060302010e03121e070c06030b01020f010b15090d150902100318110d0b0a0605042909040807 72
    0x1c00a0005400058100100b00740000c0801c006428950722020341800240101000d030b503285000d90700000740c00d05025030381b603566280c01c0c4018030059a0280b90000c0c5402d486082c49180006841c00481c01d841e4801100c00c0c0310049030762000103100320301d06800200603c02c0000d1113030300b22504070561820802d2540d0040d07400a98221003c5841d036200d980d442e0420425582d000402680c050f038250040c1c442c2c08011081701802e1303c0b410441118003035000070720000e080c000c0d02c00c90300078036082450f1248207921400014040c0c075003a6181e600520409605099002040c031070b01c0000b038802402685509182c000c160700c60f03006800c0940d880402424200086901d5199107801c094841c0030000364503000307204226a000120320b040d0105441c0c03a14501c01803c40e50049010940c00081000810010000042e41d05d80c0311a00100141628000d1000e100203e402c00001c1c3c500843d810320007c0c10381d030001503003804016041b001c040501510308c082e9040456160303803c075000b008079514000c803079 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 907996169 1250 907994919 907994947
    0x30507090f02090405071115010b0d0b011202070b1b03190f1d030904060e1e0429070207090c02070905040201090803030709031a06010518011209030e12060f1308 71
    0x6c0303808101103000c3d25071800c0151400d004454001c1c0700c1e0101d02ca415410714086c40d015011300291180541d81c0c0c1c00c0c40c100745a008410000000404400039581c40c80745203040808544c0a49030a041c06181080191584580100384c81c4120300b0282400d43ca416aa0140f00203820000080e000241d50f8038000340102110441a44442408400440d9100618810f01040341c1d49980200c41e241101c4052107203030546100729080c02c4080030410030072511282484268440401d03402403c102e00c3c031454009948001c10051320524158007907410305035841144005480105100f54016000f140090010341c0e0183e104540150062600b287c0460b00c8400080c5036500560381000410b101500800401110241061302c802d62505008101d042c00350010b0300e11b008944420840a2a002c01809640d100750501601c941e413040041c407074012306040140441c0d401e448094001c14200302d8803940007200081e0b0f18041c0c4100011036001c1d940702c62559242c44240c01b0100d402c503400f00b0840c0303031400c03030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 907997419 1250 907996169 907996171
    0x40509150d0f1b0308032a07060509070b1b0d0f05070308090a060c1805060f032202130b12010e1f110301240923040b060409091b030507090f02090405 66
    0x86030f080d25980e0b0410350b01c078050300013002d8034115a0b0380400c7c01100d81400078100780d6000310b0f442040401c4946071040203504111a980000034552000700c0c0c018075030401d000c202407184c0400416610131381c8540310100c492031f14504040e00400c100308000380000e407140744040c0c0d0194103081565541440c556030072003685c0c0d07075486060019805c052540321481c3c0b200018401444110784080c03504418041444075804000e003800440190580001d035800030208450214650091003d0710180994003000d00070300501c010140135010302e55502c00c860070144148407004c40460004e00003400540c04000900344a140e260407066194804102024a424040c602034400807084a443c8030b180d40d18181c001e01c0fa000e0742030800051500400c4204c0c500c3c05040000e035005e8901ca0303561290400420068285000f6094000e2400200000c0f10f09040c2d06c401c03000e511505c4030395040c508910301406c03000498040541a5000b142c4104680300c11680b0045580685c20000350912440c10001000c64074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 907998669 1250 907997419 907997423
    0x20606010e0f0f06030f0103051e0607030c18090509070b0f03060906010c051c111f0203100f0803030f0c0f09010305060d1b0e010815011811030a02040509150d0f1b03 73
    0x20304c6c18014010080b041c0a00750f5200c501505000015101080107070352041c4c007070100700c181a910303201155850b108d40c0c41041402a00400366901695403c00240200000c8402e0041409014804038148c07a028040f07860100d030030040c03030342143c5403d41006050b0070092b080343d051203c1d0400c1180012801d0003042c2c41113068513100e020031440b0640103010441e044004444580141250f09145010550f03842c41100200c440180c0700d99a8030002c0f0354070701c0c075604100a0103d2058000880810000045100362441000c2400a41f00c0c0c40503020b01c0d001e121011220904140b04800c0305503c81d42c00355500c2280208a002c09000a07103030011000d240d61400081074521a03170511210f40603000d441c2c01015050018002100300c00300c5a044598113004010f05070f8800800400c280303500e074110350560317940142d4442e0341e400c051101d41c0003907002e0b108041c004c080c20300c00034041000c070740200d0f882d00b00b0180820040400641c2c03a0b91902d0034810084a1404980241304a035500007a1510041d41c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 907999919 1250 907998669 907998691
    0x1505030a060510031b18020c030d0b03030d0e07091d060a0903090b07051e0303060315040501061e03050709020a090902070c0b0406200f25050907050d0c020606010e0f0f0603 76
    0x50500382141841b10807021120203490041012004094001085a0511044040000d40390485100203400d41c821a203103850128100ba05c1407400000c040b400800301c801510081200c440c8400c2803a261079134030403451017103800c03610000c0c040110135008101c21500c40d14001d001c4544451407908a80c00200054410f40c0c40543d014061703a51011003940d8103030144005600314035080c0e0000741c0d10b01d06d40300313060000340028000c1000c2089c2504400080c0400c0b100125905080b150a00f2036120b140c4001c2d1070601c071f55503001444000b13500c2110030341c41c103030750f18402c1d40b508050070000a5445224115070b406401c40e400101c41a40f2409003000d0852030381c8401c14450850380b00c01d07030342840c1c408640e01504000e0345a0420100090f2010f08040c482002d00030000d80d1104052201c0103c2c0d100e15000208070701001003480d4410020314942140c40130801100c40c2600c000c980d40c2d5007c942d030f076010411051694130f041c50074044190901c0001000d80b03501c1a9260003007000f680085c0e40590140d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 908001169 1250 907999919 907999973
    0xe071e050c060708151c060e060f0c040609230315100918021c05070305150708060d060b061309200a080a05180a050706031505030a06051003 62
    0x14100c14002c0b560811140d2510300b1850804c2c0407281c035010351048000d03125034040485880d82c0e800a030924086150021801c10078841c941000c0c58880008031500045031b2040e0300012401048407050b181525900d81c1c898101c0d1303007001890201826001000f681c212440000c031100342e5420400384061401c0d1f505012014141803011040b10319854111481e980e090210098001c0d5000740301001680d011201583d0344540c10591403c00c90000030701a141e0301910b4400310520a0001300386940c0d107143d9100007141d580e80001111001c0d03040c0da03003561108030403c518010400941020b41c40c09001040c1d240ba062080307504980480b07071030344150409900c40d002c843e80ca20001c0b249107422442502028130700300400388002e05080005004441c00365446000c2481620003040848be580340d12004c039607140f00c0d01c2c14910703a92032161040d20300081c03c1c15150341c9170324200b103002c0e8100c581c040c004119001c0c00e5511840a080000e2690b094900054000400710398260900c009a40b0306640201d13032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 908002419 1250 908001169 908001187
    0x91e10050a08010c05090f120604050a110621040305130e06120607090b0315040204180f0c050703030515100518010c0b1f0b0d0f05130c0e071e05 64
    0x3008268410b8070583d240c20003240c600d81d004804c40d020030000f19821030f0101075180015004a42c069107250440c81644104070812400241c0314042c18003c1c05032303882c003000e003000f004000d11901140740f400402a9010144031a619200d003074200e40b0034204142040902113030780a2203079459102c0d05d0300d0b80030b05061200c1400c14520f890714018451002e000c507854140070140240d0f40500c1012546140000011584000c08206010a40c1d000300b080d940c03641d60700c4407045404160740301e04804900d08500300203c4039152050204041c115200d5a00f40040c1e078030700381d008101c01881d1025049100c60104025a268a0485e000000c01e4807101e49807002c1c2c510200f002510b41d40c81505225220400c50007045501c511968440409480350403400321010f4401c3c00d021003039001070180c1401140f4645407010a8100800a040c4100104015500d2160071003004001c4803001d0001010707084188506c4216000320b6074000328505050310020103228030400341004030232402000a0700401d2180c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 908003669 1250 908002419 908002429
    0xf03130513050405150a0b030a060506040e0105091e0c1503070908030406120e0a02040f020405121209010e01091e1502030a0f3b0108010b07080306091e1005 69
    0x1510081d10141000301e460300360b0b1a1659220940a22202d000000000420181c1d551b04046c0c1c4d0043c0103000d49040c03c807680340200c003400c404e0340c05910503400c1c01d034030f80480601449030603c2803850130014050450400c10401c8804140f0214060b58058442e5036681c45e25141b40707001c00c2c03403020400a942c03032400d01c0300101014003540200d1001d40003040108000e99000b02d540140d1501040002094005a008180342c000d400744000c3d041810120030181e0380c203080c3d02a01c22240e064503000c0f1400344942c0c4890b00c43d9400300802107503840c107007c00521544580d0207204185818100382d81030319112504d20122003102c403000c1011021740d50082c02005504c4180d03001011490004504141c48818017170165444800c0081c10427901e100f603180c03c500f11030007180000880384600030081994514040d50fa1070130707510550110380808000502091503808035450a0b400c213200038115104c003c104089a040613041800c8840c41c00070000c00500c4400980d4024803601480f00c41d56480d00e0140030b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 908004919 1250 908003669 908003689
    0x2b05010b030a050a0308060a03063b280812150904030807140d06062604031b050106030803131b120b100b16050705040b060f0c0f031305 60
    0xe4003a401035104000003840010f60788900b1030b0305003484400ea41c0e5400200e900310a0b43e510152005042c1050724031403204508100140c1014015440b4440c02020032000c5030790382c50b0b40d060006903c01001c0d1000403840c2e20350b441d07405d00300004c0102c0108a940358040c03903070401c6894807940400c01d800e002c0120401d00248a03c120283c940c03800c41c1c40d1039100a040e0348001800081417041e5181050702d200011b030105c494103080e200080000340c1d01e40310014103454243e19143d04003085580f0901d05800e4440c00b562103158941d4075031001d01c01508a0f44080150010116015900d80402100003003518014600c40d080b034244110366500f0b1401c080420948821000401c00b00c0e03003e042c054050441451120380d90007134201020b070f84078441040d24042c1540e029103000c6001080803054803028040c1101d016003c0c4084948054903001007004a4044409883d8003030030400813191700c0c400317100150441c1c01450054401900d034903010070781198807071000d008407007408560901151821303403210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 908006169 1250 908004919 908004941
    0x712050f0c0a050a0c05061815060a1815030f06050f0106080a0b120304030803040309090209130f090213150905090606010c1b0602011e0b0904060b2b0501 68
    0x51006080040141c9040e10800c0040030402c480003403c00000c034055141c0f01a403950080c112415807030b00c0031003108803401940c180c4145018035664080c190a00c800001c1c0030781c100420f02d000d100d00d044101d404e407000c0441028000ca481e071f600001c10b094010980b00003140100481e400d11400d0307281c130a00301c4500822100d03401107048010700250340c4c0f110545500803001134000680b005035100007030b03450b60482c007144064480000c0100800c000c1d40003642c040c1d40309440754120070703440d080c0e003034240e010340c88006400c03650b10350040308000302d142c00150010255013400503007c0d48a8020ed403030640180b030104c09681d00d030100150511a0420140000c140c3c1300410000c608044000c184c4444000e000a8100110000c01000b44040e09002101a0b1540c4007088002aa5242c0190180514041c03451014280e0700c441401480103004000d0440c000a003441c00507952030391601d00a00c8181529030304002d6244041d5044000e802d83c03034584d120f840140011140c924a0f009094402c52060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 908007419 1250 908006169 908006191
    0x5010305040c05011413120201020106050a080307060c140c210703051801030e060a0504230a1b05030d03090b0106050c0712020102030906070f0201020c030d02031e070506071205 78
    0x81202003402140402d007615005d203002c3c840d10503058200031882c05403000703400301413219060000710700350141c1c41c80f00824800c0c0c000340030f0301c1c0e41d880403c80340444900c40c0c090340e03800c02c10001c0c00084250384921040c01e01820642017042402d5100300e02900b02e6058402194802c4000f80041e03448030300051103220b42d40340040d04e0541980e8000388180582d803a88041d550780c0c228003440c1607000e0b402ca4080078814004551251402401100141c48103a17003d550650010114481681c80d02105401c003214000080594141d02c1c1e50303100101780400418210300b60340c0039003c1090b0741e05200000560501c1d0b580814504040c1c20102030003901a807044080c04801c1000c1e006c051400300b112021201c000090302c10b8103065000603401c501c200001c441d423000001a000d01003000007841001140d000780d0840300800d07460428550340d440d280c0d43e03160141e0b0081c0441c1e0400d4241c02d064402032070716a0b500509010b010b5482a15005040d90000302240300c000c50900e03414401d02c0796503804100c09031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 908008669 1250 908007419 908007421
    0x210605131b050f061c02280e012156090411060f0315040c0516030c0501050a1b030902010c0b1e0708160903020f0d0c03140c040605010305 61
    0x346070308a8883d40a0150380080340e0a03844c289050380b9480c002d00101020755075138200e081c800c1010198030a101400c126a400440c014621660b07400241d0101078442d0111040b0710403200030000781c04211040e000b921078800180d414107010410010340241228068682c0d43c111100e8002c3e90380340620aa0031402d802e0285501503000b4481000002c243c90325002a120b506195003000c0c58092095004140019040c000c640c80300c0003144039400e50b80708010000b401c032003040145d4804400102c00036200382b01c2d0f0b81c051501c00c0840101030b40300381030030310301e66001d03a03900d03800d40304100c51000b0074a0340d882ea003112041210008850f240820710f000c00500401c0c2e40041e040c00c000c100064a00c0e19620001684540e950562801440c10102d035141035140c681c0008180c1c00084070032160121a171046000080d02684442d03080d0fa90050460a50320108001d10034a80401c10054900240355140040071030100790300399030000511006405c50742d031004203000550b020b030f905c174a0405141c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 908009919 1250 908008669 908008679
    0x2010c0e031203310c060306080607080f09011425022113050310060312170c161208010303170106080609040c05060f03040b06090106020304210605131b 67
    0x1c116070b0b119410034201080d816406152141030381400449030135594410241506001521030a10304686c5159030034002c80e07480d40030064a69909507070281c0800d8510020031041d081000131580c0c00007050380005441a008080440003040c15a00440702c4091011280403c0700c0c810929140d203c1d0318001403000b000e0854004025090820195010010100c0d440314040c4620200e08000d000040442d0700a4050342940c500400c100e1104658840b00d4040b507802060140f0b511000982040000b01126a16007911201d2584080c900e600c42c0710880701142c00080c08400030b102d0b0005d0b0707540d4a030000d41c1141b80140100c52404a524003051380940100300b250340c010407856104405855075120358440c1d02d0300b8401842960002903101c90003003019445802d01e107000c9d41c0b103240288030b440d0254070cc500c24008081c1081c040e41006800400041c00320015030980105d40300c24800384000a80b640d62a081e0071283e060b1a078204004940c0d001509100749038241d10106c489400302c1c050f00078500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 908011169 1250 908009919 908009953
    0x2030304050a121e0f02011515052116080a090b040f0f060608150a02040b040b0a050d0204150810051c03050c0d0c0c06021212040f05070602010c0e03 66
    0xc0d80c1d0090082209082060030a031084800e0301050050000706a141e694415002d00300085105c00d40340150701c1c040740c2e124004010307041c1e042220515034060b001d24244600498013070f405000460b9924114040b0703460540303812800d461003001c0350072241040c02040c1c0401808950003400d01004681404c3c507250114281218842d00140d0022029281224515009a84441d1501e01801c294a490750014002c0c001207a00b50030300d5040c2108801a42c1c2d840d41d80c10882c019401281c201032014401031015900c0c9070000c1c0b0206000742002424400240e03050001d9038416041164200d9100060200c07580d04404015002141b100b805588603082c20302160407640741107915552205048828820706d40103008640540c95008142c80604c4104600940b0344035100c0f0f0f04456030224140000303003080c40032801c0103a18040e8880d0903d80b8040f100421150032024009803056591110408001501041a0b80c01070445030004141001400005011114130b0000503011b0741007440c8a03503203d000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 908012419 1250 908011169 908011183
    0x60408030115110d02070816120b0c0409020f040510031b1b0503070b04050c0d0c090207141609060506040e010902310503061005010e010c05160b09040b010203030405 73
    0x100ca0201804081030110071225460310101c51079860081031320b20903505134081180000d03650302c8000c03140c42101880040c002d40c4542d1185030b00c50254103031002d001428142005400c56015205141819101c3c0070034000caa10250180c942c284002500304030a051032000000ca202d107e04041255100100303030303008405065040102004146007034000075074501c20400c50b0080d04241143e8035801940340c185005401910f050351603100b2141206443d18280d2244c0c01c61651042031a24000e1401e200303080a500103002c210b074500f4140f041028442c10030090050440c2e07003090404407240c9000f000c0d50440d1aa178100c2ea0041c58200000c0c000a10010941c90464503291001a0741d10b10201c9081d0819482c0c044d402c1d4103111541c8258054100302034481c0690b001202501d000e501d440901449091503481128017161081805180d150b0040309030405280c002c0045e00c0c114000c2040300045ea8015070004040c0d0440403401d496030f810b191180c84032000c002e000541ca141440d4440981c0c41c80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 908013669 1250 908012419 908012429
    0x703031d030901080a0f0f09140d0c0b1005060703031e1a0616080318010b0306061f233c071a010e150f010f1d130903020d020604080301 60
    0x845180485c0362a803855200440d20b15052600700a00c16800b0b42c0030014110451051b9050301c0f4000480b00d80700c4001c645d01401274415210000241e20b103540750800c031800280a51300c000b24286001a454881100400c503180c40f0f0740d00060189180240014040d0100003800d40851409092159030810010f03402c6280e030040300e1054507500c1410034500c5025201c44000d20003103011083c0501c0da00c01049640e00310700100300920800528206244c0d98410845070395511038410740744080401107c011520b041c41182c9003102102c40b0b20b514402e10b0800d6583c07040c082000014a440d015000000c1002d001d40701d50500840da401269015000c0c1110544440004000021402c1c204180c096120300c1e15170100031003d000d507950f900900b902c0f40d0101c510920007200e20b1681c442c603249c80458007001c001c058403520080c20034540221810b42860111149440007184000500daa42801000b0072224419001c20400041e00c0d000b4104038910381030006640c0030300e0601000402d07003010b1300d054074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 908014919 1250 908013669 908013677
    0x60f012706050301020c0f06130c14010c120224010b040e180a0803190902031b060427060e0c031f09020d060806131109041110050703031d030901 64
    0x801082400018071195008035851341c40001c146c000700e503005c10b003907003940380c60380903100b007507a2350340903607122940917a4000d1500c440024148042060700d99082e030120810b1401250703550300e5556191181c6c1d80540d8810141e4031061240c2e01240410300001c01c4104a4900d02c0d10b6545000d00030200e43c0101d01918200c0c1110310006503103403101d0050f420220110408540008046003000c40640d81301f9180c811141c19400b0a00750801c07641e0040001d840d5024000b0288034011031403414114500055063380718008000c0003030501c01d5a80501100140e100110360403861400c1045e045403002d500c03041486204004020303c07460303240c080c4c07030340450048584148240e000c07004105010300d6402c0b03660003520204418407075400981c07015041c0c55912048414684810341d940040c400c009000411007002801000c1260034080c01280e04607100fa080504000e0304000029800000c02c81d00000207030000c07404c0018150f060003004400300c3e04504540c06010b0401c2d00355280c1c890341041d14140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 908016169 1250 908014919 908014979
    0xd020f0f01021624090b09010c0c09090501020301050306100e180106091a01090b0405031b0301020c0708030a020706031404030507050c0306131b0506070b040f050d03050603060f01 79
    0x180e40280910307800840562402007005889004c0b803658a0a01000100e0307084480d80106510b0740948210025200c082c100c490800341c20400440e040e2a134424220b8401c80000c0c00011301d242607001d5054201c1c49031001684940c108000d161401800802d510f4078940202000c224004051000a4201c040260020112103002d0340c001d0140074550302447e101841e01001404040380c20300c0920061030241d80d5100b0722a52000f00d213009008500402d42d05030450310b6040104821303004048a071550103800503041a00f800100303420598540d1010b1501d07040045e015801641c180074060180055060800420b441e42c14a0302c400000244003c050000000f0380300244a01085076481800700141103c03240e14003801c102d021388085e8903040b501665100c2c1c0c02a40c1d0f420b040c0b1020240c0d500600110308120441d180c40c510264094410b0721004203540805010940620500e234000104d81ca022071141800014185441d800070000010451b071180107005c0080341c0c64035450b100b07840300156109 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 908017419 1250 908016169 908016199
    0x270301180b1e0601112b0e012a05010e03030702010b120601262a03010c23210106080103111014030a06080703050d0806010801080d080411042301050d020f 68
    0x1034103e406107000000c0078130340100c51040074041c0c07800114801c142d5460b041f840030140195100c41c0322201136107810f562030580101442d0706109100d640c40c003480000c00c1c0880705440b00c0341154400e43e2030f070703005035107814100225003042c40401a070f01c07040b00014070744d40d8035040e031807004075a032205021980c07840d0320305980c401c00f0200300d160a043e5500d00011240300c0c52800c0480f00355482c24005000b54240054400b02c06c1c082c035000c0c1c00601c59551800468070060041861a610a0500400594444908150352802c45144c03501034405a02d0b44855035055003040702c49030b00324500c124403a9400c801d00301880c13079110400b60030074010304085503207941300e440400018119036000000d40d13209000001003030200005810000466540f181181900c1d450300440f84510240503140640c0d02c8600340c2203003d441411843d9115016904a040c3e00d1682c40019040e86c680070300c0f400b82d13040b0102419010100000e8110b0040100f114030703890742c048030b40c04100d07130000c0260700d1880b87e25a0814005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 908018669 1250 908017419 908017423
    0x20a0b030a06060206070504030c0b0706061a3f061c08071a060604060c0809100f0206010609060c06090804030b2e0506270301180b1e060111 62
    0x160911065450326481d0103015000101520301c103403070044c403480c0e01050003140120107c4d4192034104407910312082c00c010303800d8070741e40c014001207801e0759442e4000210701c25003003105c42c0c11080c424804e0350b45056010545c11000d12008603c81c0c242c811761442c0c60843c00007001c1850314000d510503544c2654403c00000c9500700ba0034510000d8a000891130020030210000038002c0030303c90b200808030304220045841c20503c00720b0315590040c00400090010a01400f06503045a04c00d8480c1858401c0d9400800c41b0854150010004284000d4900d090345406001560260800e450008502403070010020100101d002c40030b0211690b6480d20402c1c020304000b200d02440d00034100070310909016803201841c0102c04041c4841c0b004810070203080205801e90b9100f1940000d0085041c418003062110283d54204009003460f5142c0c01a80602c2e28280101c55140d02c46400000580025003010803c0c10f100030b10b030305030f135802400c2c0c0480c8407000345002540040003881d041138104d20381d030f00300380c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 908019919 1250 908018669 908018689
    0x609070f0b28020f0d1211040302101b0f140f010e071406070611120a090b0a020c01141f0503300f03040506040c080c01020a0311070b12010f0b0c1002030402 69
    0x45003500072500c82c0900b07185c0100341e90510300c03e08081041107d001d141840c03407602417404020341c0841200303400b0a41910540303816940d41040741e0101850001756550303410695035424203c40d80b401641c0c1d8610000030505c0402c100c0d01e170400003030020404d018416912400c043c01215400f0381d006240039040d460f5482500e045030b600c0030042183e80c04203441c41c4090382110041e07102c206003803000200000824016050010762040060326903456044894002e50014640c9072902e6680c0c840086581c2044070403540204441442243c104401d507819486580d99a0881030103a445004c1e602e02b003094040d00051100505d81c1c000e0345200c4081c1560400380304440848468000c04001e1009101001c1009405079202361541e61f40c10744c1d01c506031501d80f8003482d049400340c0c00160b43c10000c47e001da0010a0307018004c809660103d5100c0174111046c3d040f0847c1c185016020000610000b5503800d002d1019060303140f4500c0c100442003071103540e1800030302c03081d407201c0740c021000c5403c54581c11034103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 908021169 1250 908019919 908019943
    0x50f070b01091a030a0302030a030b04111c06080a0803010e071814040c140d050603030412050a020907110a03210f0c020105012903060609030609070f0b2802 69
    0x140000703503034881094000d010004481d9070b00d400f10008161652400040c500b20399603254003d98240b200e1080d041d4000c08009280c95081902d40080c1c40444c03441c43d0041c41d400000000e4601e0104420b4904c1003220040d400c000703410381c0a020395801103503140042d681114039240490710a550390300d00407500c00c0118003c2c460491005d00c2c020070480780341c40c079444107034800341d400700561312042000301e40c00c408400e0500194501007003460b000c4140c1c2e8001d194450000f40480313140c00d076903e5801c01000ea0619054410b5041404441c0841c6800b0f21070340d41210141c601100400c4044c54001e03110402d4100040c140300484403445d40000d1400045241c10f200500204000c0300b80e15200b801601e040c8813040700551034000041400301c0380b51641000b81040d000524102e2004c0e442e218640d51014222541c0300b9024442c0fa0741d1550304100c1c5502c035070220005010032501d0400c078105254400d130000e100266007801504a0002c02d540c0c405007224080c50340785003d01c080c039401e9003003034490010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 908022419 1250 908021169 908021183
    0xc10060308040305160e0105192c09010911060307021518210f0702060409050a0606140304020108072d1d0406030203060703051e041505070203070c06050f07 69
    0x1c1c051128040c0c011203005100740c80e00498480c424051811316405107100d00714120005000340c1c00e050040360f050b1644002450000b40e116610544950000e0324270480090040c0c5429403148102d2024030740000c0c4440c020310820109699104400c1012541203000c0c44c0c0c0440000c000311b00c00c0000d62440b081c4d00d83d4005441c145420b10080c0000c080d130b980d03075117823055141030040d140005495003100e840da089654203000d409201505e069111030011307030340a5400d00012500b145a4403800b07016483d2400c0000d01c4502c0e180000d4a40d820302d04560111032003d000700700240c1d0304045119801081c1d458181c0507070045011109041c1c02e10788030520412003503903082c01030b42c7c1c20100c440f84031500141c0b41a016440d0394104825121203000083d091f422080216842500a0f0002c6d50410340095491200104101c02012492003c440640d078110940382d503015041c480e403180c01d070000c0702c0e440614507100c800d454002c0403110b00c0c0b0552080000010304900c9400c0d008013502c014640c8419 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 908023669 1250 908022419 908022431
    0x90b060f070b04060506030a1a070e040e15061903020d02060409021204140a050a080c0307050d080406050606030c070f02060f210c070c06050901030f05070503040b011502030f0c10 79
    0x40c42c1d41c140104071030803a4010b1034100031034010315000074182c0d00d4940c444403030b12a81c078610407841d06020005d0000e200344040d20750035540c941c0c2d4500070f554130548850300916000d4151103041e0707540000900658050314402c40c280e00418000300f00d01d410750340c041c4d03040b144000c000e2021036150b05c142c0d03004100c01d0384040760110901020041040c02680038800404110b0030460b61301c0e0300d070461741000800c0f0760f0141d4091000510300301c0c01340070040e070704605803800c1c4442038032994280425003141500280200c2d0030402008664072880c1e401076010340b402c60961a21a52013030042c4541c190140070090b0345124002195140011200c0e40111481015129848115500340c2110300401183e5440e403050002206044828203a803035203034000c0b89403900540741c120292440d5010a05242c1010344802c4807641c01d000900503e070240d03800c1d682c1c02e43c1e00d10b800c0c28002100001a000903006040e02607600103030550000a031a8840d1790413080a0341c0d0801d150005103045170840b01050280d007408 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 908024919 1250 908023669 908023673
    0x10203040509040602090f0307061b170f03090609010204030f02121f09021e0619020304030c18050711030406181203020604150c1416053301080304090b060f07 70
    0x240150141500540741c80192554030700c02c02d0746500300e41c02b400c40041c3c0b2848000350340c9160221103403007042c020031149600c42204820304103541c0c440c024070500f40b00008184804210104092a401070010b0b0003142080d0075646c440f01482092803003c1c0c452090811152265002486501d080100d200760900e22060b828042d0000781c104498207902c1003980321461920740d412045c419540400003484c1d0307071500031039000e4603a8017002401e502c0111700c420300c0088005002c03154500b002e020307801c490000440400d4020f81c01d482d001440f29082007804040782c1c81d18000042524243c5006040001400e00d1500d220182c801595010030562002681000141340c1c010450781d026a0188889502d17000c50003460070700341ca049009040001c0e03c0c41c60743d01000b803031280180041c030b00c0012001802000940fa110f250184a884055002070601e400b0800001c50803030300444c3c0c0028046c0802e441d850003400ea82c5034051072180350341c10354564171982000d9442008954502e495800c0311a140d0b0058 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 908026169 1250 908024919 908024921
    0x41401060e371b020106050d0f08040915140f0a0308180406031203060b030906010e1b0c01050f010603060810020307051209010903032a11030910020312280b0102030405090406 77
    0x800124803c03610403c40b0124032441806030000b582d901410201400403190381c2c0b40f014002d41d0009a0b44030b0801d1201080b01c08050261900c00150741861601c110304024110b407240442c840070510401401d94460002d89507a4201c030200d03900040740f952076154060f5181c25941c84080c486174450b01d400408410000ca41d0100c01c441c0e985030b9010021151903500c580850312007030f5140e4074aa4041001080124450800258046802d1110540707180440e003403245c0c20b4100348442040c5944803400c11100f501d0194405004042928003130080510704003940d92501c84801c01ca600351382d000000076403000d00078030071604090781e004001035003403a2241142d4000d140071001100000e08000c0300003001e062900d00301003070124150503a010b8801c074450036241e412461451006a00003440001c513155140541300610000a8001d95039031882e41202090f0000028400716004d100003551008218406007010410b2500481c0024030040940c0140d1443c01507600c442d07402114401080200300c42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 908027419 1250 908026169 908026181
    0x210d050d05010b13121a150424060e0d170a0219020a121104020d1d0a030c0b100e07090602150919060603021206041401060e37 56
    0x40c180400c61641c036020211014819030070031160b1598065014404614030400700d984440c030407003a0f580000c66010b15150706610840e040e41e244a5082054045820140100c5440b0180c03070050340124206141d0032500c1d00c945005450800c24010358044c2940c4610020003100e41c5c110000b0341d0900440800081964031450502d03006000b6000d407161440014581a14040d5008140d00880b5050002d602d000c5000c28109454220b10750424a407070ba140c80c4010f12440042d01008203207000c1103071100000c189490042c010580c4802c5a41c40401d03445140e000582d54044500c450342d88030066848100e401542090781802c8158003449091030b000380418007120541c1c3c080e200d40030302161260f81e0b007500c115403901d8183c11844000d144d0741c0805440882080c82180c0014456031241c0203d80000080700d10341e281640f050b0244414010444440c00806000d01d001f4042c2504041c1c050104110240075011a00c03445803904160411040320f0403620300300941281035407010003007a01c0c00703418 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 908028669 1250 908027419 908027437
    0x41802040306090b160c02010f1101020d0911040b062a250608070f08010501080612060406020919080304150912030f031b020a0f050f030403030e0315090c210d05 71
    0x100710700c1c5d040301d40203000300440780d0380507140d110048680c944240c03a8503080f40500d5416550030041c9003408142c0d4400c03081d410f030003a41c98455800000c01400121103404114134481d030b0052102d8288404d002c0d1841c1e9908003555a155000380d4811a1103151040c2442441d00a91074200401e6002c4100c1c5030002c01c990482c2d0f240c0241d501ca010054907092601303440800099000001404a07502036204a6000b0001800c0c5800800750ba01035070f0304001e015501103030340540001d0080307018a00701d040000c0c1b01c03240300c000f400300c00e00c2c0c10a0107a6030b00c141c2c4210b02c018050300380054903050042c06c2280c01030014008001014040e8035005213030380700300038034040802d141c81c254401c040400500301904080781d800510340c100c076640710703c924151040c0c8103c40758407901e194524130002c24005040294443d0311904501c0031100c08140c01c1c262108010110600408204055407800081c1d0305038940003a81c418469084107512a45203002140348030519100358002400c5a503804001000201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 908029919 1250 908028669 908028691
    0x40b07170f060319030905100e060d0c18060c060c1b020607060905120a021b0d03080603070b0a02030c0c0d05030319060f0b042108041802040306090b 66
    0xa569128291000110850040418441039001030241254001915041040101107911444141003100c2410306000703000c40000740c1c030401c100114107000c42e04152a4015080503200c2c588140007041c10790007268400b200142d110004802c80c140104107a43c241e0707401001c070b01421a110200a00320f654400c81c11210145406890074900e0700c14030540f20078400d02d590700041c102c869000c102c0185c002c400b0a076221503440075a01c000450402c42c810801ea8540c000c240c485070707a0301c406410110000c00c0c4185140d01107200c014183c0c2c0d0780c2c4a201d90b603503060401c1d0080e907d848010910b403041980050100c0940051001c0c00150004007401e1015500c0e4215504a6000c50512034a00c07a50740b030050161f80244045042107030400d1b040501ca94101c01c1c00a24180d175410303001c104803180d52100841c41d500007403d00c00c0c411820030401901161108001c940d000a56886110307100300d1040c1112102512100401088260100c07030095801c80b0050000034280e08190b06441c900ba0380100e1f110b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 908031169 1250 908029919 908029921
    0x30f030c1101030908041202031f1409030301080d112103060f0d02130513050111120a050f0c090d0206040b0d05131515080f0a0510150306020705070f0806040b 70
    0x10b58032a01a0300d601030b50003c81c440c109403a2422441c02c0300300ca80d604990601500300d9444401c0250201c032510043c01c02c00106d89607030111140d42020b5000790000103650800c00050000440000780d00d0040102c0c1d14040c01d442e1003580d14a41003d8200c6050b107440b5000b896080030b5081454003441c064541120f00080c02d007003502c100103010f5a1004000c0d0000c014100100c102d16407a0300c0a580b044040c0c0c8640303246512940c825085585800283d119010007292001c46100c25400c0d171a07001006460820490810b1030312807406420051074802904d10020310120030341c45003148069450b80c0980302c15180ca443d850303841440d40050410412440c81d0100260034007609000500709140c00100626031a90b40305c2e41080a44414268420741300d02da06000590001d00b04996031700503000340082c020218442c13811a0910030012001d005c06420401414200b1202c80140e404895001d0f5005070342c2d600074a410350501442c1d50160022051007603000509180c0481e1061240f0700c40e0102c1806 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 908032419 1250 908031169 908031203
    0x60903020c150c1f0e060f0114010e010c020907022418010b10050c07210501050609060a0e1905160210110702060a11010c0e0108010e0105220204030f030c 68
    0x3140c080c0c07407042403196003e4260300e41340c1449100d1401560305014004541002c4c0680311a19103881601e004000b02803400041001581e886100b01c0740e02002d107068a85c1d0720640000030840499070303a0180c810310705100402d104030b00800440380303d5120f04061810000080600010380f0a0407248011206000c0360a0f01c1390352418130444404a20040c0500e031900304112080310741d82c002d2038500015100e1000f0220b140c070054541d07900e9214803c40c410b03200078501e181c05402c1d5640a050140541080f000344170059440001d201d060b152844a1700519554110900c1041071828a01600c0b5a14000078030000280102c41404214000c0c1c08807800c10521001000881e40c88000d240341c0340300140001001490204001e02c1035a4441c5400c8601003400203442d0308646080301c0e050301040c10360303501501c2c95804c0300c1c0c00f5004240040034a422585080c010850011150540040f4844401103101c450503d41d03040d42c0c0a107420510480141865147c00f85c1001803a02044d5610501c08610001d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 908033669 1250 908032419 908032459
    0x30615051b010c0c050618071217071101030e0718020d02130602060402120f0307060b1f08220f02090405120d021c0203040512090d060e06060a120c15050403060903020c 74
    0x681c500c2175030000d082c924074060f0040e01d0859030403c102c803403440029002c07030ad80c03130346070301411005000b0460101103180c0c2c08000350440342040381e41c0510750000034080019031182d00b05e40c0c0203414a000d000d80e4480b0b010b0b40410080c03144c0b40010402d1140b0120100c0c24a03030005010b4402e501c01d0302c58045001c031402c40e0964440400b805210035074010050b060016220b5003200d0704a140144c80c0481c01d05c8019071040e8003070401500034000038060780801010f0601031400d0740080e484840b00110200c2a5101c803103016008800203400781d0910000b00342080010030030220320030b05c0803e865850720b030107030907410207540b00c840d0b400a440483d1404d03036050b1301c1c0d51080328000c95000006000400f10035180d22440e400c6800355a501c2074200303898001081c000c2c0158140004540042c1515141c038104200c0d0044103600000d203501e00d41016080010213b840c480103403035a09028088041404904590f11b200d00c0d00010032290605611340101900000c0c1408051001c4481805603480242001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 908034919 1250 908033669 908033701
    0x150a0e0603010e01031127090d050f071b030203120304020307060816031d0a26071707050a0f0f0c0b0a0504060509063601030615051b010c0c0506 64
    0x101d0110a41c4004000191038080c210043d0040030b01f100d04407052010304802418880e20f440500c001c064820444c900500340100c0c07062100a082007400d100200b0181030040c015500c00905d8414102200b840000760901205d0095500504407038000d1040c540135000b640094800701e0091154003008a292400743c04060300c100408040741c1d43c0312003160b81c201c0c00340c841d0701c0c02020301094180c20040444000d108480c501c0d801955501d41c8401511041e8403940c44080ca2528a140103004040c0026090f0105080703601107811107903221542403d0903030820042d030070300420b07003180c0410460401c007951240c0241240a4140c0401203640c5111800d410300c5500c06180014804104c00d0200078000c1010300742020001d800c00d03081c0380c01c51440010f0688078803c401025516985c1ca01000607480b026541e4009003032806000a0b0b00c1c1074201d1002c0c84840180c44c0c00d00c0008211085140c014114030300b5081c10300c4000348403441c1003103070240804c1a83ca038151120f010340b5000070b4814020010070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 908036169 1250 908034919 908034929
    0x303120b0a0e150f03071e1703030705130503011a24093006160302090f0d1b0b0406030b0103020310030f171306031802030a080f09150a0e060301 64
    0x60b0300d980d1540da40c032811241c0d031180c066002100c00c64018168400b0090440500380208242d05500d1520102a0b03150182e68884d10115584035503030604000b01106481c1c10a40500b05540c42d141010000c80000841d03421240e059803030300030455481050b140c91011804401d03101c050380c420100840440e0014459403c40300210108a1050b2078200002402e8000201098110701004c903045900c1807201e50419a0081c2d611000600ca103056001d1060903000856080451900c43c4e81808111081c03040d03040d5074803800c0c000314580180b081100056154210044895035029201c80c0c0c2c13101c40ea042406840b0001e440c168441c03505500030b1080b04c3c01681401c0800030014035541e102c07149046600e0049a50704480c00468440381c1c501c5c0060301f20107441c60740d00d5013201c1c24100002c1c119416040500c503408540b0303541d01c02588000c0b654808003a00580380301d030f948003c00c6c0401228400c0429aa03000400b41c070355400381e038807034034090304804031166515410f51001c1420052140028056 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 908037419 1250 908036169 908036189
    0x70e06120619050919050601111f1d0a0b090c21120a090329040b09010e0d0503190203100e150a0303170708010b1b010e070303120b0a 59
    0xc54000c2c904503000600d010701201559190300e48890120305101d070103071800114210340c00b1400310f03042c0d10b038021650f00c00020b00e051001225100007007607881e10344140207212500d00302d00f80c519008680c0c01892501c00d0004d2905402000304464580d510362180e000d40700f50000101180762840041059248240020040070340c0d110000800075180e440c0b5016002c4600caa02c5108051070610000340c0408045600c8000780f5500d581801c0103540d040580d000c8031421200307502e001481841c2002a0019001140343c0c0709903441012050040c4044140c084c002d1190b01e05401c1c04940c130078015445030880382001540b105107445080c0a0b400241c4000900300b0507403070188107510900f20b07019804502c9494002c000d40141011880701c500c107802c142c000442d0842601d60308410340c3c00c860703004401c80c40c0c0312001c1d61405064003000e002d410310540311951007000001644509400030801034480310283e444040d5130385800761203c42c000808038081424030440740803074039080d00c10500312207107101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 908038669 1250 908037419 908037421
    0xf020c0a030204230c07060f050c072009190b03011505060a02071206020712020d1e050f03090c0306090a020901060806130617190218040f1a070e0612 66
    0x3003080007403c0ca00500071102184600c108500700c0d213a0031414000c01101c09104d9640c0450305108003541c6004041a101034240700034040f00c482000c04854885070002030100d0440a01d03c0400403210f0000e04050b17104c9411020f110003884401070380d18125402286c2009510429418103080c0d9104d03103d604882514020100564201403008014030785552043d03402a6441c0c1080d00c0b00e91100d1301c0150b030116408921441000350001c0384e50001840d0703000a02c00d4001114006000103101d00d0440c80340e01c2401c2d8030941181c0100149d41008600742a015103c0c031f0a1804155a20b015800d440d1003481074002203912801d0101c0e050184c0d80d005842c0014507801e190f401d603980c0710040c2803290801203843c00d01c0051181803050b4009002c01104e10244550011542880c10b03200424034040405a140d03201d0040c2d5400d4581e901c514420070030504181d4490404000010000d04058440312000000b00010000b0030003103031192a044d00ca455148212600b806040c3c064541c03100742c1c0c983e40700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 908039919 1250 908038669 908038673
    0x3010609060b07031110021909060e0d02040b011403040b04030f08010b030a0507050c2422061802091509010e040b13020303090604090218060901020a0f030e090c09010f020c0a03 78
    0x180d1517001240e915012100380316126001002240e01145201c1d200c05102036280001c0c0380d0001a01c001400b441c503210345100503620000740014200348001f0b1180303550701d51300e0007103900480034000c012114111041d264a0282071070060008101e0f0120002211040300d1400e10703000d0304603103043c1c60440c90380504680d01c81d1504002420094503120500c07200b0300002441020030040e0300807145d000c40036100250426483c00303100b6600501030200c003641c070300540e8088010a1030b24903800c43e0004c00100d144c040c803042c3c00b407880d60b0592010b0f42100c800010044480a121407079a115a41521100741c6c41ea0380d0070204d080380d601038500038544102e00b00800e4040c1128a000d01c1c01c18001000e0345d10b0550100c000490340e034082c0d4801c0c00d0700380d004925a852114035416114003501c041c3e03011403038400e00100003502c84400045c004c1c007040d4203a0840041c580300f010f801500c000003400c1c0044a00f0f10b0501c240047c0c0140310f4032400038402c5074102151038130110755458200340140c05454102e0071a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 908041169 1250 908039919 908039927
    0xe040308040309051c11010305090c0105031005041d0c0102062707050402030703060905010b0f09011808031204200a0b0d020708040e09070e090a0303091b03080903010609060b0703 79
    0x2800030350400c81041004035003665884d00c03400060305c030b1110302c441003e010300d00726680010714480c2ca03051614140c10070042c000c020480000b00c00302460401e81c0e039074500790124501c0c07200380c0007260044c0c90321040e000105004c0b070b00b81c80d2a5124004984803034050381c2c01240d81c3e10040b80e0300b040818012911280301412114100600c2d40c059044d0f5600c2ea446401040498008550441c0040d4440204201800c05881182d01420280f41e01500d0a0711078100c011480c819001030f06e04218007152a180080340802d4000c01078040c2c142906e0380c0d074031025076404440390103171015990326015881c202ca520100080c0d03001290b0018141000051070800d800c009a04402103540380b041d020403110001a0160340108003034050711b0ac0c030310110705001c0440c034075001098100c8400180702005000e202000014a4083c0380e60629000c2440c00031443c140111a950456010454134460f0300031080240f0340c0098100d800055000700460b40d6900b00d8a0180e0307816119086080340c02b002044042846 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 908042419 1250 908041169 908041171
    0x714030f0d05090309090f0a0b181807030c09140109050f010e092b020706111b040906020a0905130b06090409050c0a0807030204060f080c130b06040f0f050a0e040308 73
    0x400081d603003040c9040020400c2120701f2240d860490b440582009030030b1110b0f1060845d0882e003929000c02c400b540d0207458641103c05441d481160724460305114024a081103800080c6a202e0842551181c0e190300a602034950780640080c0441400c0c008980205c6070b11070103204102c21415003a4030f0b440c0c00b8298031801000b810303031711503405240e00b0386040740528040380c04801001c14003104074401c2c40320001c0c01c0505607085801008480c0f01803c0c020b400c0065100c42000d091201d610510107c000000d005150a841c020b16040c0081107090f401c40e0441d66000468031f007514014500b10501d000e1108690500ca0500e03400003040c081085542002da0211031468400d00896100d811000005a1080d20039800350707600358410350060003182010b004580080405000d102020350030046440c2d100e00715100594012490b000407012181c08a41184015900c080c0c1f0995445d0348901c000c0f40e4001d210300032a040303031310003c0c0300150ba81810114041180c03801c0140040310745071680d0840746410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 908043669 1250 908042419 908042431
    0x309040504060f0e0303061002030a050711190602030903010c0e0117041104091416150f090b1314030d2129040b0103050910021b0708030714030f0d05 66
    0x41d8800d19200034400030304c81c0244c81c01c0410300554072490b151041241c40b548c1c1300e20341801c54105110030030a20390408151b62105500c0380f00303070301c6507001c40b07000c06c00c00b1106204510000e0040c010010303505402000501045605130300902440804600544103081c550680d54001103800d4500e95520840700603180c1c00600c00c3d4003060940304c2c2c400005041c1c0708110b600307a80480e00351100701c42031242001109500c035003031007118400a15040f0742c1e01c20780c409584c00800b4000035400c0e1480080c8102d68010242c0070305094261550b00104469903580d04d40d000e0381420ba1100714181000d80350019018401d45c1d1981d0702c42c11200100d0b600000701c0203440c000301c0c800301e45480e00c2801c0d4602c0c00f071101114140c2006007810040c0280d04000a8620300030307149050500d400c0500a500c50041180070043c2d0700520301582d1007035140064400c2aa4a2282c1141805140c201250380c040100090445901640b01c4410a2607004070094a0748907603600c080d808007082020b400608615005154011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 908044919 1250 908043669 908043671
    0x904021902030a08012102010e010c143d0213030b0103150b061c0b1c050a0309211b03060c080619061b0620190e03030904050406 57
    0x80400d6500c6060300d98036000c2180540c001103074030024a944a142940104240d0f00d4140c1c0c50a0444200440e205840d0000780c10018402c9a410032039001d9081d0075034255020003406241560104919103800d0941c0503c1004064021510100220002004000403004501d1400034081c8141c0340000e46c041c416002c2c0340c900000b000808545c6802c030050007580204040d06089120a00380000c90314a070003420704c12407060120541c103500c84071166a44c0d1191550000e03001078641d00288001152042000300c10f5012000c0d00104040801e682241034070035180c503103289844240446a01a00d1421f20801c20185101d03040410400200008581d050380c581610107a141d0f110070054450702444400400c400409204140c101076000c1190b02940d20f0894401d5418138000403c5800c44c0403035813282c055001000d4044c03206561003101d0701459109000011a8004003211080e04410301c4040c108607411492100c180c002d42a07540c05d81d200801030f600e0b052041c800c100040201034420380f001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 908046169 1250 908044919 908044927
    0x1103180f130203070305130b1302120d1d0103020c121606050a0b03070501090b0403060e010b031f0f0c08060d0512040603060905012108070501020904020f0702040c080403080a02090402 81
    0x2a100c000c1e00282140c484a4007590301e00e0007810203030680d40c01070075403038000e0140075020307011504551106400455440482003107150074000103000c040d44000b0480280104011a1407a0750050301c60420b0380c005100045d401822080190200d005042d4605041d81260900041d042208802005a800a10f8a04181004584a060884008403240812030740e54844c006c20380e250411008006007000d10b0f2040c060b80c148000c00303a1601480c03100030151901e60311a0440c1303481c01e4014048908020f42151410035410510701c00400f5289482c64842e8544215070341c00043ca4007551010102544034800383e0746800090202d40388a50505862a005a80580000104840007403000309034a54020400a061081c1d1a0440d02c1c1a80209100520390610100d244001c0520028981e0001d50451700c940b020308006000e4800c1c500c084c3d902c5803000648088041014000d4514240207440810900402040a60725070505450281c0814541ea001503002101c035002000a01c02c00350002d420 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 908047419 1250 908046169 908046199
    0x305120f07060c0e0934020111030408130f03080f0c0a061d01060f05031002341203090510050a11040e160507031b03261006110318 58
    0x11903c0360600100020504440c40259203003101c042c0e50000c01c045001c4010650b0081104581d448804030a0f0880446135040360016000b980048220000c0500c0c2654900e0b062501020503809000901d030618001c010100d0420900c1c0340394001d4076441142c45241080710f4190885642019481d502e86108440c402030005086000d1402c0030041440303410312003106000d44600303444981c0c00c85021294103c0382007095607000141011440c0e07803400016581c445146051110b165a04048200040c08042d040d107150505802c00e0036503070007808445043e0038425011826a170403500b0203031150b80101c80c1c51101c060207a0000341c21990240001991030196652942c407600f103507100080700f0350800104075804407050102190103500381341146c0740074100c1e500a080d140803441464558207105084404160060000304400b8455102400001e000030502c221641c1c02250740c02100c140803000010b03400c1c041e1800c07031000030003c0003442c2803220280c0d148510400302059980c3c005644500c0b448 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 908048669 1250 908047419 908047421
    0x30f070c120609120c02010c11031614040b0d0f170913092307030834141b1311120906060d020d1b030501020a020d08100305120f0706 59
    0x1001d8407844000c1059034250400090109480d10324005000c1d080e501000141e80c0224031030841648103480c50030018814012038034050900401301001003250030041035071050507000d44140241100d00b4407084501400b403007861131556800400501248050400090344000c803400c1707a03c00500500c0c200701810300001c0d840c814940506110560f0740499101f400b6107031190010500f040e00ca44403800d4200001035594454600c40070741030500100b280364040e841e8145114030f4080280c41c58082e0071401c0501d4904821444080310604040b0010525428020985801012580b0301c00e110329203103481403103643d03e007034040803105030368480c4002c001091b4000030b04022281d408203d04076251080f9010324006c80078110902c12400c20780300d5801a52205068581c1a81c006006095284000040b01c3c0702e034044d41000b0507650020409042c85070f070024504491109583d0b541d500c544401c1004107895160740805040c80d0000e95401450b122031070014080f400c0c841c0d100e18039216040d29036070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 908049919 1250 908048669 908048699
    0x10f0e0603192c060c071b0503012a0f1e0509060a030504020907020703120f0c0f05101104080d080705120115030b0405070c02090615071202060c0c030f070c 69
    0x1c034a180442c0407418a038542c5851080a68404070f00600a900748128200c1c400c2c09500f00003400d20403018440e400e0100c102c01d56500030f2001034024060f04414041c0080c64200c5c1402e03407010001140040e50700d0318400c40382c03020346200680b5450100103480300407151600320b0368018814840208102d4000381c81d44002030400c08200c1c0e600050b03e041510421181c040060104001c55100745418008141c0040c4c3c890400d00040c00e02440380d0328440000e81c0d0781e40c5102005842400300c1d075116001c1c401c002c00c1c8442821038480341041150711220f05211680281d0248000d0780e0b0203641c01d07400640c010500c030b0f60049030794100107050170f54003c00141c0140098000503804110110050070710354060250310b241c0c4c0d800300c030113100c10325003400010b201841d0601c0c0a4031418103840418500c0d11001c0d00884000340b10407180b940e0f02030500f800078038810000f07210780052089100052030310f903910007a500c0400d0408080e5107010109540d600a03504400341c1601e00c50035607000041d6000d044181c40b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 908051169 1250 908049919 908049941
    0x3190b07050c06131110120b0a08010e0c0406120c091a06030901150b03041e030908010207030314090c010503150423090106060e060a080a020c0105090f0606010f0e060319 75
    0x98070250340c1031806040f245128450300780240c00c14642e000f81039410050105c80c442c0c0d040e60028110000b00009600c0d0545030340b004c10b2651810141140c20140400c14dc0d481802c203035000e010080c0e0b50355062000803c4c51002038071085405009200c15000b1b0b1304664480c503402003603504252009000211039074004d8030440103a079514070340101d11029510045006096102900741546800e03141d803001d400d14101c50fa0030715000316490070708040c0181718800107800c007200210b496582034500a00100280181c0c190002c0011002601038100014a80b0700000b060f901e090030350f2100700600001000542240e0b6200f03032100308400d50180307044070002000d031040c0703001c288070305190b0019400c5501d1500321104002109901554940700e00003240c2440941c1e06d0b220340a030361010404002401203030010070595080009015a108002403aa4041000c0405840d21a00d41400541e141c824604046010482d0b28080d0340107071070208003441d80700c0c0caa90540303041d804c4665845000c85480c9290 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 908052419 1250 908051169 908051191
    0x60203060a0509010f170c1e0a0f091406031b12190602030103061a0109050f01020703020d0506060307150804020103050403020a06050c1801091211150a05120603190b07050c06 77
    0x401c20450541b8103120114805c0700c0d015190b0181c3c004040750480103002c2c84940004500100e1250513198401180002d0003801d01030304526854007a03680103414101c81180c50b5480c00c0000c1900c40c9008140211058847c80c2c1c2d281c0003001241c240300c0c1482c051171104026000708184141100307420301c2e8100446210700401030b034039811407030240c08413114446140345610f0710424920b96a6040051700d8140c2e18121500c0420742c0071800101d2a100030794000a41040e50292541d041090000c8ca0038064207080742501c005507111004180f0005442988030002103180e0041400340d4002d520160300300703000340b040d5800d192035600e0b054280d44e406c0e2060316002c0400114010a00d141e400002d130003c109107416019549000140b0001401418010b406407643c1091210b50380e43c0c490001d009001c4017017034140c07144401d04000c2e0903508203210003405c0d0605000010703500c3ca000719914401d8090f003032642c115a06292242030180c80018108024008108441003118008000103032180341e615074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 908053669 1250 908052419 908052449
    0x30c062a060705210741130e07090302130b09090f0714060304140a0210020a030201051b0a0806040f150302030c01032904021309290d060203060a050901 67
    0x302d04462101a801030302d481c505408148441d0b0b60b0701600c070206c40c8240d1301000106e045481d40c01340d0001d2208070485125050900014196401c10001d00345880da01d0941030046552a00c1104049508480410008003035800c00d00c0140740804481e05400380038131002601101c404003140354038070182c49203621070380306440c4a155202c0400000002e08a4004281004003608011800c54000500002c0441000d000000803c20040000d1822660000d084082d181e01404001c2d44030702e400300b019001075003080002451996110303000300840408505c10351070018500d008990684010345019803050300c40315000204189130064140c0b11450450364401d061661040505e48201110b0040c1410f040ca0078000c0206d8080c501040c00c0302e00d40c02041700725031010300000d0080c0b247c4542024044002500480d0101096004082528a0040404540060801c40601140801500ca50040c441c580044c0004c0a80c3c01541d0400c20150140314001e85130000103040c44426080002da0b45078040e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 908054919 1250 908053669 908053687
    0x50103080c0f0c03100209041404120e1c030c02010e0604090e100c02030909040515011410090503070501050d0608060103080702090c070309140d121d030c062a060705 73
    0x800544081c498140c010b2400f001e444012940718030b10f41a050a00c580e002c520b00402d51140c0d040340d905000e402c846075a1901d841c1c40c0450018404030214000551030074000802410000700f000700d400e502c0303442e03a02c00394203e5030103c0d000c10100b035040b03040090128070345a060300c900300600007401c110703c804034501e2421048580341c401d40340c909003646802c0c0003510703c0054022040301d460480a50342c15606a40d9410b02d01d10f000050b01e609020703a114003000180c548082c040107481c0c44801c90380043c1511004c00100c0384410326001e600da0640040004129940c000d400500b80d4082d540c90106038183e0b9035081c01d0500d04240e009030707a94400018004110301d0410441a4040c40c5400020f06020f843c2d1070052951361103000d842140d0b00c031013504515035074414605606007584020140c013490004003000f02043e982241c643c081901044408110345030119a5080c4140c001c0c05050a0110140d103180400512500d03c8500142c401e8280c0314a0350140402d0b4882c407030310b484d50744d0360341c07aa0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 908056169 1250 908054919 908054923
    0x4080c1617030f03040807050a120f030b0f03070b030901180605061005040e0604020306120a03211a10030204080304031118010303080402040b0102030904181a070804060e10050103080c 81
    0x102030720380307040d07081044184414001c920680f0382081d0000c0210392910b62902c1c09a01d0a032200030003500c002c45125080c2203503540a620741126100a9038180103407405074051020381c422440e1300d541e16401c00c031420300c0105240c002560b40120007200110350060480810100e0002a00094034125150000c0000b81d003056152105006454545140307000c1c540040301c0d401c82e002a003c0c511542d0000045141d559030100007401218414081e04e041450514016040104030b100414043c110091200c1c2d5072500d501c03c017056a85a4120180541860310030040c9410440301c0c0e04003456030030f000204a503c41080640702035031040c0c2099203484e5200b0100914200030f42a06003000c0644401800042c0c0d01c43c40d03564201d9419030f40403c1014070b03400187c1c1107025000850340c0007482d00c010300e003a1845441c0c403002d540d8014002c00500d05594200030241c6141210609c010480d800b01144c0052800c0d070040300004203c1040d25166400110a6405e84000782d20503030791100041000c414017041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 908057419 1250 908056169 908056199
    0x170402280f050109050a09020a140c0307030806060306030c222301050307050609060715050a090b060303070b040b090708010515040c030e1b040b03030c011d0601060c080304080c16 79
    0x4d0030414030b0180f5042c0040c1c842e9429019051015030041111180d881c0102d544482c25424480c02603115081e04a425a403600501029070004491102080550911100b101d00038180500a080300301070b45001d00c50200740582010603103285403810450b061006108681c05600382e0182c803200d4803051981040d84681c1a040700d0701c02d4000c104100141d50f140801c64000201c00e8562603103075480e0742050b220001c03144d5038004400c2d0420041100b0101c40754440b020031845050143c20a4070354109055880c0034045005000040403804600403606841c600fa61004845003210300c09a1102c010900703407031080d148909441003c55040e03047d46800e009008203000300345010008003404807903a40d940c1040b1038410300715408480310918aa02e07650415114040040d0840ea62440c40c0c00c0c40c02d00800e200404d048081e00007101701070b481034002c1130070f50403956075544010030381c50941c440d440075500240007100d40e400104040c210460b414414000c211800c00c40150340689013800035104001c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 908058669 1250 908057419 908057429
    0x15030b01020f0d090e0a02090a030501020306041d0318031002180901060201090b06060d23040209010f0f0501080a0603020d03111204061b020a08100b1906170402280f 73
    0x90f03a42d410030f540301440408a9403c560b035501144c42c0e0541800092040542c1c1c41c2e084855000c000c81032200540045000c1d00046d1410060b40810904048800c2070700351010f030131600100b02c20244800f54030f0b00f2104804005081e9074005541d9038200c412070303000009540740e64142036a241c3c524500039092030700425140c0028466240d0b40d5842041c080d03001041d0620514021076607202882c02d50340400003045000d120440050307113013141e0031240700e400c039400c9100304940400401e10203850307952001101c5145000880090520005480c1e8450060542c0d41c000e6894100002684e1801d100905c82401780e10303100300041c50002110304200041154007421007042004000460b40140810200444401c1c03124200c115480041c00d14400ca500c02c1c4c0c180e02c524040e02840d003900341d1041e0802036085a01030390300720400404403048401d510810300840c1659060381c80100050040960062008005c40da5409041c42c00d02d21103050140e00c000044101a82400580b901c0241c80b00901 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 908059919 1250 908058669 908058673
    0x3060615050a12150b07140c0103020a0f080a022a28110420030a0c0c020f091b0406030903121103040807030203040909200a2d15030b01020f 62
    0x1404284094010b840d040c4036641c40fa0742d1404803940c03a804101e5034030702034010244490740c1c0d00c0c000c0c02c1448184a071200000720380d01a035280032107258028421103803171015940b0b50001c20311205005495000c801004904482c0d000c02c405035401040b80d800e5038488014452101582800108080c5490401510501d09140042c402c1103040b082c51915441594000c1c4004c090080701c40100b0003800c01c0307c4200b080f108080e407035443c0c2d5122800145200d483c40c00c130108541c40381c0c000300f100c054910342006904403444119903d6181020b101c11540214a054070182004800ca000c4440354410b41c00480081e680c2e000030300806034815025901c0001000f02444100c420945840d0b0900c8041c1c0024800000002c0d4401014028001d880007842014000c0203501704504041d103140140070fa44a00001200f1034201c071501d000405003064404c0c180d005d2400e4108883c10b2603001040d045070411000442000050210303541d0301c0d0321007040241c0e1340458001030a5002925058000d048c0100c00c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 908061169 1250 908059919 908059927
    0x31b0c090405030301091d060702010605032a0409050c09040503090f0a0b09010c1a0c031e070c110109030803190e190b040204090206030a1418070909030203040f0306061505 76
    0xc42c5002058906440b4103543c00117440d410418144a5080030b6091500d00d40520000c0101c215010750250302210f0041e42682d08940e0540b02c007850010301600c61030280030b18014070940c14205a84440c0d8828415002c46000c010203500013501c45004032802c6031258030003d60101d02e4100020500c401c0324064507a441d400e0304020300700da098000c524060b41040070309002101030211001c030b000198100e10005a003d414003503c421465441201e0f800c0409000b43d8112904074028012288509400d0791102c2c885081c50780c861502903020909a030412652034004000b08041400950040811070204c0344500c581c81001402c0d911600c0c00d039441a0400d900300410722349041c2842c0d210550000310702041d60384610009008140481d00690003603404020403000000039070003100c042030394854440719582d038011010001500131080d2846900221001c21182d80035400000c50648640181c03420326840f01c00d1031003c940e0b0f9605c1641c0064440504000f52140c10041e40c1c7c040400d440c010f494 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 908062419 1250 908061169 908061173
    0x503120703150612020a2607030b1021020d06121101090b040b0c03040e010b0901020f0d020d081504020304210e0a21060e0304051e01080408130305031b0c0904 70
    0x11131101c0c0c98403516240c001841400640c42811103a481e0f1008111114016a0aa80d1520f80440484018022900c0d01e01c00c04480e01c1e240c04031181c0030550755200b51003804104040c80c0c46c2c82400c800c4208031030b000e211601c10081c2d9801904050945c0c03264040c1d5401550601818400416066038140701c02c0d200c0c1070007035032490012034047c0c0b40d800c00c0d401d54640c90842e101c2d1640c4116031208907284091000421140001c000800725840241d080310003d10507610040c1c0c40d1031420112801590007818145165801110703060703446030140024002c0e10000501050580c0c1c23003158210303000c0704c01c50296808102c1c200003030080b0014a18080c03103981d0b200c4020511000e9203000b4140850007102181e030500c58669422002543d01c00018099040c1104201d556500b240c01180d2007a80031100305544000c6100600446000581daa81080c1c1c5507a145c21171907500c800c8054046000340c0c140400030031b000300000c0503080007c1d415000703190070f500320050400410405041c4100302c00742c14000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 908063669 1250 908062419 908062427
    0x12a050c0409170703020a0b010b0702180603061501031b020f100507080106050f07170d1a150307090e070203120f0403091814040c170307030c06110705031207031506 73
    0x808062410340d540d0340c40740281400c0e881d0480c60709004017844c40234030000c12810302e400c0103024100d10036281d00c0039049409500c10f030449070481c0d20a07050b03888103000806518030b956121880401c18100041c101003108800d1002e00345400740c1d00003582c03002c003000602103408c101c1c0071100d080c002401c00050a007100014041001880348004002e40031512400700168041107450791640000c8480c814010480683e40603082416940121860b0004085540041c0080f04800c640d000f414150f2038209080486034640000e8420b1042040d03804c000300303140500510040c061442074005541310703003442d40b04011104004100c0f940c1030302444188000aa00414240f080e200c10b010741c00c240000400d05040107042000080c82e03180c01d0501403000f03001c1030080702d1007510300300024480c0c402411000f0607aa4415510014002440d100d00380d0301048103a4807140103145161001442c154039034440c1c52454002c02122000020b000e400e2004850301482145100828201c02d00300c03084c40e20701c003d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 908064919 1250 908063669 908063693
    0x207080a020f01030f0e0c03070f140d0c0803042d0b0904380f0109180c0516051005061903030e040608030c07140109050f040b012a050c0409 62
    0x340203140d402c450354a6680650411400c6041c40c003001c00904451100c030315501d00100d400300303029004028012958910a905400550740480810348001d410041881901c2000c0d5009482140c0780010101391100180000d000070401c0c0b00d500d002e61601c02c0c0401c01584041440d070307010ba4400303101c2001075140c1002540c0da44c030001c4900040aa0300e041890080351500d0b20001c07c40001c1807081405076100040908a98405407070b82c81b03006401e00c00540b9070003051b000c3c544a40b58502c0c10686000e1064014109091032450031300d082c410300d05076000c28800444c40454080d08103e031102d120341000e200381d0742d004000b01d400e648541200342c159850503400c0e004c00f030100107412058043e070392229000203006200c1041102c1c3d83d59100b10300c1d20748400c400c2c01800c0c0c50364074018460300150300c80c1214a090b5500140310141c0703401c0040c200300007000b0580c00715045c0000c20051518561040c031140b9001c0c0d1409841312440581840c007a41082042c81c6a00d00c228a040c030000c0104500007545 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 908066169 1250 908064919 908064923
    0x601090e070303120921050706050c0a0e060a0507060f0506100207152706110d030903021e0114040506150405040b0103060e0708030301060306050a2103080a11040b040509070207080a 80
    0x81c65010a0420134044088014401784150034800e840b400d140d4440000d00232a40181c00802c00d648441812800d00e10801e081e44c0c00007800d0015a1240b2b05d032500050010b0502810843d203022520fa44000c240c400102d80140b43d03071340c0c51040029504128104140b00d903200e02c054442d1700d040500c3c60030b18004400000c4200300002191180c050300c1444050000c00c4030751450510255100401000d50400c01c064505d240034019880b80640e000c4d0095010b2150f040d0050850303052071800e00421000c00c01081c1c155507485804250f40c000d80d40030300500603070080015165518100d1031542d0440081d9002d14001c2d840c280030007010034281d0980742d044d241e00400100301f4500c1191254608049500104640d01002000282e0503070190703c29002c44006a5400c09403603501c9445011118004203071600c4602000704100000744901140766100703228100c009120800d0740100c800d16000f80d000711914400020301401782e071a0075181607a10588510060100500749058540c03590036030540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 908067419 1250 908066169 908066171
    0x1110d2604050601170c0d1b0e041e06020f031806060a0b030c070206090613033e01020102040911030a061707300303150806220809030f0601090e07030312 68
    0x9941194418010208454801024005081c0c0d2905083c8505640a80081c10501c0d11040001e254030f0300c809140c4c84ac3d07810072003020700c580c1e140300e8007401c03201c020f003040b03a44681c00c002c2c41429a08200c00341d405040254019100d171111803005510b010000f4002e64030800210304100002441c1004a07030740b00b01400141511140b052022510300d0060340c280da61310100c0841c51600102d402d00d07803071049a000385110340c0c58202c080e408002170705007410108050004a109000d48450520704030211182c10b100040c0b80554600100381200c1990f0b221a40c029000810310a01030158010100540f0301d20b03c246421940892074203940d00220311460f404c50f0400855503442a17a45114078004c403d200c000b04860342c4440c03500400504070341810800c40c481042c00880d0312900044c00601c147e607207003600d0f0354001074002c0e056010014040200da0b0f29030200011400d0391018800c100c005d0095100801e01c9504100480b001e1702d502c501d000a440d4000982080825481104046510ac00c000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 908068669 1250 908067419 908067449
    0x7143a0203151e0303120a060b03070e0f01090b0406120f05090a02090a060b131d04020f01110a020301060303021609180201120b09091f1a0f01110d2604050601 70
    0x440140d1151080c00f00b603600d40404142500209403030a402c600c10b52102e001000481d883d65407200860200340d40344000240c6035113101c416414456041540000141051a070003a5a003404402c0c95002da040000040d0070fa812000c0310301c4550149003644d8200745014003440c0f506501c01c0f6030b41c0c01c6003680a4403e010340004038040354030b207034848005810f0305c0b20a2590b812075a50301e070043c041070303201c0d03154002e002c0300c000d1035861911075466000f5a801010105891603120045074902c0e0009801c4000d802014200c81c01a0360900c9480010f5100fa00a01240b038240c09142c032540c1800e03800034200300e00b00180c14101d0100e0002ca00c42e850f9090070540040707054801c041000b032084140554101034400184003189400203410b0591051400351000c0355241c0c5c01000c02540c800940170b4002010441c080c100c0c070305d8454961810324134103140620a10303200702c0c10503241c911000e202101007001a240c0e04915500402901d00d44003424104498904050703079007664460b070520a5111500a5403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 908069919 1250 908068669 908068699
    0x9120b0703091a010b1308010911060d06270c050a2307050d03091b1d090a1a060f15030a0519142502030307143a020315 53
    0x80440c029034681c035010315503841e111755451070f40c880307200e03411140020071002507840f9050080c01c03c00c0d80d100b807030404240b04942c240840e84e002a43d1b036086c02d40d10344001080520206040000c6480380e0500b400404507009114400c0362480c40c40740003003140c01c0180c00d41d440e07005401804510341d6007105075482030341e40d103c0c00c40e640500d0500800c14021031498201c0c0030b6141d0488007000f07001d0b820035000309894000181182c0b43c184101134801c601102e070340602401c0449196481100c080c1500e01c81710a07540d81c5402001c42220784901e4801711010b01186091040007156140b20036918400040607020001e90306020080c0004169909e40c4001210640c0321480f070070300188041020f100503e2582d100d014009411101a0442072002900144900d00e8549444565060b50082e51460f152400c04807401e0301d802900607101d5108220100710b4078003134480340d4000d4180c60100490b1100e030700d504524201b03220010034601da0041c402c3c4203d41c1c42d612015820954100d80d918003c4500d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 908071169 1250 908069919 908069933
    0x1508070302010807120b0a090e07050a12060b0a030f08180d0c12020109091d011a090c180306010f03020319120c0501060f0f060f300e07030303020a09120b070309 71
    0x2849400343c03c0300d1f68080010781000d42e9080f03260001020307026201600e440d10709100026000e4440c2940d01c030280211070000c03810b1544418174030702000c0c0c404480c494407a00d40c404002142039045821a074001850412011031140011000303004541c599480341c0541c0398040661342034040c0f0031000d84158552030840e8050350503800201290704083c0091b2001c1e4840341a00000d4820385000355081400316020030400440114070444010a80f100c1e0b62228901005150050410360448500f09030402282d99010400d07107000b0300b031b59054240094154810300d4105005449000344020110710714034001035110702c1a40c007454a51514503041000c80c2010382c05080c040d0300c02080c01c1c0300000089a0303842045880023740320705071a110040c0500706412a04181d1506000d0b00008422000070043c00422241050004c9806004100c001308214028100320403948100d0102c2d60014007410500d0700044034400070329200643c0071800001c0e48503001200d400030921410180d40b900b4050403c800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 908072419 1250 908071169 908071181
    0x15021e0705150d0902180610050c120f070c0f1a090306010311010c06050901051803041d0a0b0402031003030e060408061308220303030f02030601021f1e150807030201080712 76
    0x50024004220091b08284039200c15071306030303020319038840d08040030034011400c40309030701541c50090098200186052000c0d4002c0b652044000e8000c00c189004150405440c5000e0708000c4074a40c0024034140d942c2903180b07040d20310b0414120301806050302954021482d0381c1103a4002500c0a098000d400040355981548400240800e02c0c01080c0006902c056111902c10301000e840145240c00d020025640c0740250301c074801600b000e215908a051402c030348001d41000b0040310101d04444604009001d98208941050682c07001107010810f055002c03078900407513041034404628040c14446446e072501c2c001001c04000025045080b41003056035001c89021703081c4076200c407140100030420a01540703023603c030680000b4140380701d07200b400d4024070840b40034141c160014103046202403e45402890b1200d24000e81076a5040703103d001141c0468446c04441c10b0780b40000e0400e003181c0104400e02040d4012006a9200750001c0c070050345c00440c2250130400b14144480340130603421110703000c0e0103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 908073669 1250 908072419 908072423
    0xd08090f06160501061a03060306040f0f0605010303050a08061005040e041e0305040911130302010f021c0504030519030f21020a171f18020415021e0705150d09 70
    0xc0711190442c2480b00640c003100a8860402110b9001c0d56410645c904030b01041d10825496001200400c000070021120000c00920413140c00c2446103007511084201c03002680190049940014003c1341c00e580079002d260302010840d5000c80c402c4041070018480d0040b070281000804410011905001010072504241c04120110850114180c54018107035040781c420310301114100403241e01402001c00c10354508840303000c115000c06145400448241d2200c161a90540c051010189002007110181c00b1090080e0303181c481e035a03859440c0c000c0c900745a03440d820440d21800324007080002d038440d40462000c841d514224880c8203d00c101e150a0102e04407906100b14400a883c40b40345410940703411944090b07840c46c010f41e689406000442003591158214000000b075000c1c0211a00c05a41424241c00040010706040c1c94000f100708180ba10102e0710090380c00003140d480c4800900e0498440144c2c408003621405260030042203941551406096150f4004200d04059010690010304469 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 908074919 1250 908073669 908073697
    0x170106230403020d0804052403060402070809040e0f0d080903030f042406030212030705060736090507110d0f1e23120a0f06180507020c0d08090f06 65
    0x44e4a8940741407142c1c064030401d80110303160f00a0745e041d1f000b11520601c0f00c00a94684500e941c3c2d410081000a41c07020341d080313804074000e210120543c1c13643e1241146426401005004000b08108041c2c60a1240300381c410400c4200d84c10000c2d194008000e8039041026046004c5050301c132444c1101098910119000c1880020341b03850b10b041515810800849000b42d4401e4884140c0682c03032500c0f40b03d041005400780e400800441d01ca240714107000100c1900c44403403c50300c0e2094008000544400350b40c0c0d40840b581c0e001040c4010109440740d982c01c5965401c090380d1442402803059198030420402c40d05104a2000503080306024030307000e490340300440707115000c03c0f668200080d02180086844816131000078400e000c44e226007000f1159804000005104d07a0740d104250300020f0700360381e80c40c040710989603600098860704000300c4101e181e528600206141c1b8250000a03c0c0401c0d00e2401c80c0f09014254020340400d030520221990900141d401c499840b4541010a038117100d0a4000d440035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 908076169 1250 908074919 908074939
    0x703140f0a1101090e041a060f060a0f091e090b01030e0a0305030604141602070906060504050904020d0b070f0e01020604081606061a04050a08010b090c071509030f17010623040302 79
    0x9914114041d10050070a142d068a2302c9010034040040018400e442d00b1034410401690340a020341504000c42e8001d1829940d601e854240e01c1101210050315480f1103c080c003030038030110149000d80c1d502c0b00001c0ca4100001044904129560440f02502a0601c100040458403603240d940100781c0100030010000c966051070320380e011910a1480d000300060082d040040f4a84001e401503801300c81c0c0c00c2c0d403800d00749410141001110329024000300d03805655030030540300207540010340c40e00c195410b8807182400d2047d0030004c1c124544011100d411900304204206c0041c480340140c030321008549030368a40e1b0110b80c2c81d00000400380c2d600915814041001c828101442440041c001d8404c1501d420307524580e40e850316426111302700d680b20341c80200d42c07000410040008010700000c5018134219920380d04044511421180c0c00d510075030000f640c0f1417007140090380120490b0f598a1800003550001d6140c110000c10101c1403840009628206001c00308041881c54140d40186400511740c00c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 908077419 1250 908076169 908076173
    0xb09010312050c0321070c030e150408060109091e0c0303030b1201141914070e0d06060e010e1317181503041a070903031202070f050703140f0a1101090e04 68
    0x800200400203400040a0100090151f0300c41d1407600c0d500c81d8144c40d4a100691501d042150040c15960b400e411070f072044c04001a050740800c40c0900904c4140000110002075003000700e0380c0a1a0b84c094103452000c02c00d076034000740100c1c0d111801c59405160010341c1d0617661000407003144500c3d002005942c208007200941d4901020031501680a6480c021400300b481038901098400c81511820309101e4030000950b0280100c000c02040300c401811442040f00c16690101155030a0300603045e036548600050100412100c07015401c03e46802c0d544200142999400d6100c0c2e40c0d1202146015038049084075030200a140001102c650003498034240310069020000d098000b101c0c02c2c0c4101d054081c08408180608223030310b008810f40d540321604c441c20342c2c80035140e4282c00c1986084082d400c000d014045018031b241e10521030300c81c002421400d072450034000000d003000c0004907056040000c0e280c42c0c007040011807901c515800350141c20454a524010b94010030681d04c08041280303403000f0442 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 908078669 1250 908077419 908077447
    0x70f0306170706110a0218040c08030d02030105040f02071101030e12040e09061630110702040e030301050a030b0c2206140f0418061e14040b09010312050c03 69
    0x250f07640755803101000403401641d80d5585101e1031020750004080c07100003a012040c07002c09607000e4021000000078642e034600c81071456003c0b10000540a602000610591400d8064902c03580300c3c0c807c00354109400c0780c464032400c000c01c400c0036041c50381d01e0f820345010b140e05003c04402c0c1d086502c81d094a4580d44c018014a0100403100300c2d14900031a000528042e8061000843c160755594944140e601071030228200034802907600980c0e03420889070016805150b000703a03c855610103240c16120801fa105000070b66a15248038215600144014001515000400760482c0d0f00450801c01329164080604502d00c142e900078603142c0f039146061451500512545422550140e80e00c4821106500d00c1082c0c501990340c140c101d4180822041210030510a0902c01061031083c0004200303a40d61028481c1c4000c040c004100c0c040c0511040011214214158851000c01d0b60184400721440c2c0010754110014000102001c05482c0c0300c0038500d20800a4410307000b81e01044954507035680000b40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 908079919 1250 908078669 908078683
    0x30a0b09160e030d02070e0a06150f080f0705090121050c040f0e0106050909040201110a05060712061409041707080306090c0702011d13061518030308070f030617 71
    0x880480e6031501d582e4010306000030345039240c2c1d64a50161440505184008440400c0546015000c540f90b00000c105441c205514202703007141078980440610302c1207000340948100402d0740010031380d03902c100440241c1104c200e90900e40240380090300e000c5902c182002a008000419090a10308010000f0b485c501c07000034000c0ea465020500b1100f40d45a1001226007002d00602000032000c2c0650102424074004503030b0054814103003e00c0400030010903032700d01000d01505071303950381c01a404e010640350000101185660203030010b0001d2402c103a2010706544941500794000e0314850005014007402c032803502c0703240703030720340315403079407003d440c1446006034000f56007883c800c0324407401143d400c4c4003d8088a44d41f40c0e0686929840d141ca1455210342c0b4411101c1d0b041d00405a20061201c0103118030605020300020801c002120051200003030802d4502c5085200c0d6074043d4100340f01007900b003c0400d0348600d01c0e15080500d09204da404038041d18541d404105002c1c01803600b45071481001c5103503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 908081169 1250 908079919 908079961
    0x80c21060a0b031003060218060d0b0f030c0303092e0f0f08240103021603090306140c0f180a060e03010b0402030c12091615020f0307110402030a0b09 66
    0x400d005032100814415440f0684154040c5103c51000f040001ca550300076206001c840050000311112213004514280d0000380680102ca5543c40d088945241c508040702d0854010381c014400c495242c80400d58074818034840c3c52040264800342d0700000030211032040c0c01c2001000050611f00e030304101a0114150741051000700742c2d0110034202140c800d0204500c25401d401880081540350a411800c084a040313146040540800803542d414030400794050201e840780d5510381701c80307185041800c11540502610f240c40030000c1c042c00130020703a0b031003a28916403d00c0b400d655101c0a1100c11525180c40442990b08966000c800141d500d4010292100d800c10681c02800584070751001c01c001c900c41110740e8164150300340001c600b99907020700740765844044d070000c0303809104103802a02100c100a43c014815850f02d00e10744034110384e043c8005c0904001f80b00040d82403040c0da0b95518400c2d1208503001d40103903400301c00030309901e4640e0400098400040e00380103c1d421700050100c03a40c80c5c0c00040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 908082419 1250 908081169 908081179
    0xe0a06062109050f06010f0302030601053f06010308190f0906050a0306031704030c08010b060703030e03070209040804091505030a020f0105070b01090c0e100906080c2106 75
    0x1a4240906040200a80d2101000d001d0303400c07021400303000304503080301568584101001c040d51040204685406010a441401611440c502c1014601603050300014000c81034502c168418084003060f81640705082034450300024070401030a150038240b150103481c06e200d40d00c0008180b00400c001445103e1900d00c0400c010b40c84078201783c03552048100000c00041d440b007002c11001c1d1255024181048e0145400f281442c0e40703484d1003039003a50710400c620000e038000404004001d4407904a1008000a000a1010400d42c0740050054001e112002c3c1c00c2c1611544e0416421700e0900c100e61003264002d104401600301820802d2035600a8060310440d207150840071412412018800c8080780d20003401025080c0342ca80c207005100b0114071209040c014140007000025458400642c0601501c600016969481c00b0380100360103000c541147c0110038100060070015840300302d0001340c4010303003451700007900c8001c2d0000182c0f040c500c060408408807024011080386800d501402203400300d030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 908083669 1250 908082419 908082431
    0x12010c1d0111070b0d0f020c0d020606031b0420070302010e06013303061505090a12021c030e1e0a0e0702031b010f06030302010207140c0123040305070e0a 68
    0x4015200c020006101e07900c20740c082d0f80304020120b941d100920b15800400004113031001650840030690308034003160012500601101885c850b81082000c5c5c3c401000c030010f100000b6402545407549404100441c002c0761150450403103a00c0e01c0e6032300c4940440e0030b1460f0b503131079105050090083c4000b9088035543d000301c1307000154152020142d058510f064081c4610182d15071142c0001103841c04180f9003d140d2168070029055900c1092032008050300e07190356a840c9a075001b000f03034083c5590000c1c076802603101c0544016894090302d801070452a1035117100c000307169040544111001c1081e041d449100051000101c140c03000c008402e00c102a640e03890a661500d019402102c8200c4048005074424072a042000c0d0010b4400e150041d0f807440002510f400d003e000301d040da0004c0c3c00a0740580c0d00000c07440e0402c4604c104040d5051072010142c09e0145d28280001d01c114a0804044005250b210108103141401006c42e002164084100c81005a4074001c9c42010343d002c6070301200d820b207452 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 908084919 1250 908083669 908083727
    0x30905062b0507021905070308041d09190209091006181808120c0c0d090501081509060d1401021207140315060a03020c16091d060703020912010c 64
    0x409614054840f80c2c001e000032100d94002040c069044e0306003030b1010720440800001054115000704064004040443c9150b4120204a10600e0028101c41295031003001aa4407207000203840101d80c540c12900c80000307881e000741031450702c800e030fa080c1301400d032901748002801148105825004115020180a40c818010071000c800410000203084400e04014060315003000e441c409a000d090005007504046006000c6441d000d0016551408586004424043c96030004a1140c0c02490388480900040007000890200d44000d40f0300c03402401e15844070341c1000000b2005001d042c00c018000c540710300840c8410307440b035034003940d9410200fa000020704101d09a42004c0742e02c18070303201c5001c5040c400c920040c026a40d0000c0c511800b0544d09100fa03042149051200d0007140301078291112004d820104d01c1000c540d1200c10751b5002c840c5040c18010b1941011925651002c400c1c240143c568501c8000f01d0390412642c0c0121056507e01a00c3c000f01980000c50100c0304d004612081d07030a82806 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 908086169 1250 908084919 908084921
    0xb0f0301020909060402070305070f0b0a0b030c2b021e1c0803070804080c190308010501111b031501060201090312020a05030a0c020316030503040212190609030905062b 74
    0x2d042e580360442000c00c001051030605400a2001d184217150052404200f070b01c9070054070aa042040355482c43c0d0409109002e00680152209698114042d1011406400028030000c0d0b140d2000c5804c0e450f0100484154859071036045000358002c1c040d1000952103540101351011b510604074440d403070001400f15041005da5012005550142c1c2c1c07103103103803542e10f810342d400e001c0200115500711040240303000f8001c0a10803041701c41800022400401020710f400303406072005070096810002401e980168644001410b00c0741c001c2d5919070103c2010580c0c0109050001380604005000403007400000d01607815444207200d940240d440d00350100b60107007824164400d030300d06840010400d0010030810005030b484000d19071a00d00440c1d28045194050a9900221000c15008180040200400e41c24606415022044044043d1440242c6008090a180103030b01002c0c19483d41c61035035008140c00b403240800642001060030b6101c132a5001c090203c0c00d40c00d14a403a500081d81d00c82c114000c41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 908087419 1250 908086169 908086177
    0x301030b07180b13030609053703030b03100903080106030c030204030f0b0640060303090b07080c0106090f0f050c18061605010b120c0906010f120e010b0f030102 71
    0x10404482c41d50a02e00f541e00c0d49190081004906004615038000002800ca4814841100c5c400d4010307100e955034945807190204000c075035500105034222941090780301c0d41c0d15400c100a9160400103003c1001d080401d291050444820024501d004144802c0c5034000780c07082d041303480f0365078140040c0d00745032421810303030041e4480204448004a00040001c41d00e080780c42d07200002400030444000c2c1010844070038841180302c0180b04507a05050f08a406810342070280038084544240034103843c0d030740c00400d000307090302c94640c448a002c00c803017040205040c21900c8441c01480280325558840c60020002c004070045018041d1800100c00344509042c002c881c443c0100c0c90040382014905c00c86100b44540c89150540d2000d01000200904203440d0380441c1c1030790288000040943c03412040c030400c003000c3c9100702511351000d441001c1650b00d0b2880c8940c1b1a10a18107141c4241603d04103071040c4c0000b1004454050070401228889881584001c03174401f0200c07031000304240344c0000c1c14200e02c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 908088669 1250 908087419 908087447
    0x5041d0f070b0f09030f120414010e0d060203070c0c0602071401020d02100b04020c070b040e0117030f09041b2c010c0206210a090b0105040203070c02040905210301030b07 75
    0x1c1c14412546020310f0f04002e800451405030a86800007404c40d10542402110200040c0c074401c0032405021000020600000010742800c01501c150482c100040c60426044001007609400000203007180d44660302c0f0700e4100e5030241d10f0603112a182d09019480350440c3c0910768000c200900ca00b2079640c400a50448614080c1e00030b0814005c0110225002e040135210b0a500603400b00424402c045080007103400611800d5480c580322400d00455240c10320303040c1c4c02080c1024408051000020021041f03d20641e14480040d6a5a0015011401405079007403a40d401404850003c045a40c110756402800c0c00481c60301c070384140923501001e10055007000c500e03002454444503480141408802000c84c08503000ca003014011803080e40010300541214105800c90b21044005c0400400404841c05404111420360841c5083ea100404288004101034880c81e03d8280034003d10506014488021351048003842100d8140103499466030304c280b02c01c5401d036084400040d1018815000b0002c000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 908089919 1250 908088669 908088689
    0x915060f09041106040602030c120c031c06030206030a020d0b01020601081e01021210031a010b0d0906140108010b09060a030c0302010507030e03100603050609011416030605041d0f07 80
    0xc60150180403040000400484a02118228401c29580e4850240004000607801144d442028413800c0d41003081c1d00700c1036048044203004042c90048040180e035150048612015031000c2034020020142146500c003940024000050020012032500200302c07040c4100ca0a01060100c4401265034170b0007417003240f52680006240890301d500d00e0701507403c4082c100c0e0015003042c26240c1401e106c2642a24501050801d400c8100200b109400d01100d1a07264440000c9256150028100c0c5510407060016055a80c43c6008810001c07294401c03206400b10401d01d01c0c4660f1183c02d0f40e0f009044a8283ca485101e81c41c0002d00c0c2450813007808070a80e544070f4003001c083c516541c011340b059000380c43e0440030300c01402e600389101d0b1405c100081541000c80c8011846918500b0050308141d000b03800c840a40c1d041c56505181c881c03100d4180e5401284002c403400d1250550703101140100000e4214a41c00345c1800d218109810500201005043d0250705450510704903050f49590b5000d076103d804484 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 908091169 1250 908089919 908089939
    0x118030306360b0105070206120103020102190b010b0a11070b0301090e07030c05011404241413260a08090913050d05130e0f0108010501060c0309140402091206091506 73
    0x500b15070002c10b00100103050907401c18103243d0003e405038200e0201050042000d134010410766a0405c008103032003c8035410314000540e20b0300c849103201070500481015580000e160f010340ca00c1540840861210681922101e5440b01c01070703030b400d9100b8851000314038100f00b40c00c0820300001c03074540d045a50150500c01c40500c0e01005480c0380710981032203001c0c010140070000e20300b90b403410024000c0e0840240744d21b00c880c0e440000341c40600c0800149001040610142c200c07240dc1a859100f550000903103940b0304190308420490b11101e901c0c1d2030040340980d10402c2e04000e400b9000c0c01180c241111807405658602d940004a29100440901103500a018955904d80600b004024025101c80e0620340903440c0c0c160b262204400340c40d800b00300400c000041201940a1180b9030241c000c504d06903800302440c0e00c0013014030b440e0780280440150110030400b840c1c0e9442c3c2c100e9400000280100300c41e10070200c46d503511500115414811401441c551055911140388100e1107180d00500c10508 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 908092419 1250 908091169 908091269
    0xc09180e0c1302040b03070905030d09050d02131e0e120f07030e0d0c080a11033d1119030b1f030f18021206270118030306 54
    0xb010701d40080a8a0941d401c10010500e6030380c00004600c12011600c42090191a1105051a0220102c41141000034482c0284030a1f51541c0e841e90314260101c03010320001420411080050404119164541c14980f0f52002c4000c020f4001044045005003a101d1502d030f500384105e80c0344108922491030702d1082010000103030280f010000d203242c003d08480c031a47e425035942482038000c2d802c4083c3c143e1080019404200d80340070b80c50090301041e800340640c00d10401c0804a008200202c0c46030400c1031402d40000c0d8810603ca00ca502508070070701780305401ea10559002c20381c1c44102905a12440000c0d01c4c3c20860081c0210030b400702004d4a04844014020050075250070403814101c00c0685030007002002c1c407098080c030042030b51080031400100a20b48100071036140c203040c0c0c10103581c01071820040003d003c207442030000d1180c441112440c2c0050b1160720f0040c10800b075801c0010364560105401d055142d4019010760709070f001d40d6042942c40001d6608084560a040c90540c001d60b600381c91 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 908093525 1106 908092419 908092429
    0x405090a0c0207060c11090c0703120b09130602070b0109050a0b04091703091510090c0305061003020904091e02180403020303041e060c09180e0c 64
    0x290890100a520b5103582d00c0b5000900a051041740180100c48641c1d89620100801440345844c0002e034100040e04080820740020303583d0148403024243c02d200720308080d078000300310001c0c0c1d54a01000081d450854102124100d409103c1070002a0321914101e020300300360356021480d440c0544000d0100d414103d47ca91007181401c161002141c03207044000c01c1c42180c0075400d541e9035203100d40e2030b10308400344074140481c102640030804ac814518210f0310a90b03180d40c009022400710510104c00b074882c00e50b0300a600c101c1207002a1200e5000b94010051120054004121241103480b0080384401d05480d5003e07800c420410b090031881c1500a2150704c90b880ca00b00400c0b030400d030701c0c002e43d6804018070050030706210603001c141840a028501c58015400101800b10011540005150140911a6102c40f5021003400d118034603032805003000b050318610080004115100c1004 = true := by decide +kernel

theorem cover : BRFrame.Cov 907913669 908093525 := by
  have h0 := BRFrame.cov_init 907913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 907913669 ≤ n) (h2 : n < 908093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
