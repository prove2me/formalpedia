-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2944
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:12:27.051723+00:00
-- url     : https://prove2.me/submissions/66ae25fe-f425-4c58-9aae-1dee8fd9bcc8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 529316546 ≤ n < 529496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 529317796 1250 529316546 529316603
    0x90c1516050309120303010b0912030c100501030b06060c07031e060e0f0610120f080f1215180105060d0608060403081f0e0f040507080106180f0b0604120501090807 72
    0x1380b5074028001000408803180840d031004409495000394100c450105514601401900803818042c3d01c140c407003c2c038426170100e81224003c11030021151075020602645104084078024203811003c0d0902c0818041e50584007502003125080d5604000780d2664401c480c421a118601074004c03008500031004200007058100c0080e5010f020820f00d46500a16600d81400c0001c140000c2110b82d40f081c480080140d410001c00704002c00d0b9580c0580406c0e102d0044202c070001e01741c01211840c20342c0e0b4201403032919002404010903420617400c1400300030b0190804512165460380b248404515010184052070043c0d1103071b2107000140c02c19000b44014144e0404110609684d600c030100641c07298904100d0304034444900c0038030f058039142045402d2a659801000343c641c00c0000001d0351000082e0081c2c84000210001c211900fa808000d03015200c0701003400790311043c01d10090006602c03400a031000c0c0c61141c1d00020710301880d540c0e00702160300041d0040d1594110f0050900c2c10301c1c4604070004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 529319046 1250 529317796 529317829
    0x210b06030303071b02030a02060c0109121b030c11040c050a0909020f0a05070c0305030301080d0e0301020909011a07051603030e010819020f12130302070608090c1516050309 76
    0x6085151403c0001c042d602c43c8007070000b00c0c050202c2c51006544040c01521041500500000c3c1e40b181812500c0e40a4424014100c030720103107018000592501c1141d887ca0110418110740b41c40b0141c5890481d4400d4002034107540d00e03950503074811140d58071481031080182c4079448281e103403146c03450094100c2509511140c0c5481c0100300b0b921081c042802125000c01090820035100e00c0141040325241030190002881840004000b250255001071641143e051a54450320f0030050503050600340d003e51a40036030401041c0005104005038a5503400c0d220b004011980d0824480792a014505085032462040e0259004070134014540d00041e01ea5019000303003803811040c100318240d8035890303906041e14441580d003ca98107506d5943d000031076079980403841c985901d42c03c0807104441c05403503c65085000d0700c50b140002500038003580e40c20348111200320141c070b4002d12703d5042c011480c00620222070f0000e020000300302512008031688203418000c0006580366109001404007150402d031000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 529320296 1250 529319046 529319053
    0xf13051005070323070c08010b130b0306011502150a0b0a120510020307050d0f020301090e0a0b13030c1b060809030f030a02210c1e030403080411010207210b0603 71
    0x2003000c41c0c0c0000002010b480301035001300341c0001c010740d03034001802000e80041c0303d66010000002c80860541001281d50800c441d0b007080c504112040c0030490b421b11003a80c2d05500002e00402181c5002005240b40700c243d030040c1c030118095008044a4150221070111000d0f6407501c03650304900705501d060b4054080c00004843c1801d064560a6861190440110100d07400000041280d03208406442c52204a210305202a4102400d400040d40090007962841843e0485421480300c0c002a00020143c2050714240540c480c20440102908001001c1d010701c01503002c800c0008004641a400022101c0032400404e4203151004114400203844070703c07258424850103550800e8801282e80190510702c0060b6120b0341c0c4450b010980300c0f40a246100300b403001e01040042d5080b84020104000241d10860700303d20141d1511500e404107a0b00030f000200840000340002d50440b8101000c824140100c4042581d5011407140110b0b0a01800181d808113410000030080080c11154002e08102e018 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 529321546 1250 529320296 529320307
    0x30207051207540e0c040e01050906100b0d0b01140c1e0d090e060a030515010315050103030504050405040c0f1202010905240d0e010c030b10030603170a0201020f13051005 75
    0x207003012610f18a03840408155188101c3e000c0034030400100b0009600500180030f50b0030003000340ba008160443d0700140314000c040c0090804107000b150365003540c080301211401c000000e007256004045008040c0e046c440c0e501c0c490022201504040c00c1c40c013075075000034860607441020b000d9044131030340610341e11031307000c02c04442c61550459100030541e0101d003492100c940d00c00700011540d14a85d030000d8a98007801500d14001204c10700c9a906a034041c0c41001c40c823918680001045400910002e0005007040c002400a842e00e03801540e0024094014140030ba91554124841c8204540c001c0515003100503200f01156000340c2c0c2c038402000210380c0b03181035480d2840c0507030386c480da07060034009280f0000a010030305d11041d42c41000d8206006000300006054005c016004088038034450f84200d075080e60760701c0410301c21b010b0f92007543e9001007030010900081d60054a02d07002040b513502955001d0200c00c040343c6102c406000241c88120400d1403003890203041c0101e0801202c511410403d08100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 529322796 1250 529321546 529321679
    0xf11010c0809040b1305090607080f040b06010c06020717030717250504080d02030703090e09100b0607021905040605010c0b0601050a031113090b060403030207051207 73
    0x640b100b181d0192030104030020f8000004950a0a8105207050203240c0360501c906200c000540501c6100991101031158403024103504041e00101d50044c0300c4400000003c266520030480c0143c0184210305c0982004084c1d80c0b00280f100440041401091005c01081006940410031704614084416503031024100100d44c0c14000b405281e86540303c10302011120350441c81b40040f500140700340c80c00d03100000d0400360000d40300d1740003540960004001300e00119104010380042c0d40648200d100402c00709021280050141c103803a40340360392041043c4000e0300962145005c165610000b02220a25603080c8070400c03084840640049040003012005d0f42c001401000202c0d401100900b800342d12802408070490140070b4940e0f90301d02500c00401c12140c1c0700c64080c1084180d031400745080c09003103045403d02095006520000d40160b1001d60108124241040122070881c0840306407240d0301d886010781d241c02140601e69403024a180c000000d15031445103c0305c0d0210710101c83ea22280466041c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 529324046 1250 529322796 529322813
    0x211208060316060c0f080408030d06090b0603070c02010e060d0c110d0306050105040b0c07090204030f050c010e0f04050a180503130f0b03010b1b01150f150f0810120f11010c 76
    0x170030117031070305c21403105100c040b900f0398000708240d500301d03555044a1100440070303115130711520030050f0500343c54000790316004003900d11074542e40c3c0c1d90310014a856001120000491121150850010041d05c17800a1003070052103148400c07034503030401e0121045299440c3c940042200400c052170800203100301eaa0080c2203d0031108003143e001d4669810300c0046081900d154401100b840c4009000810800107100003c90940101c00f0b842c00070700d0440041d55513101c0d180a07141d0001042d10b02c65210300e800d9100580002c94010f00041c00442404068241218050140c846c2e90001c80d202c44c4a03c2c0580e0440060104070340c000e1051407404641200c0d50006000b400400e110110f016004c040300600401007000d00d200003401520380b00500d024410045000b42c8208242c001c00219400203501e1010b00381e00c2c042d03031300d044e180080110b04480c03401c0060311b500c3c004000381e131002400e00d4144a0030903100d80150030740c2d0381c1c1100c62301c0d0505400000a084505000c50090104080b40422 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 529325296 1250 529324046 529324067
    0x306010e091614041a07030e040c12140f070f02010f090803010821160501020d090804051908030d0923030307081501020703060b0d0c03060207030f110721120806031606 74
    0x1700c03000d0301d513552840e00f035401001c001c48881c0c0081c98030035521003103944240c0301110109401400c200e0314000e410040020001282c00c14101000b440202d170300940302d031001025490040c8000a41c07001c1c50207030701041d10303a285000c1d2070108003c0700503c89100c040c820350500c2142c0107101c1e140e5407026012020140a000009032486605006540a00500390115440e0464003007041260250618004000b0741180c0111f50041201c0307030710085a084401c07112000d40d11484002c5040c24103100084d4013804800c1400c80310450700c0c0c08601c1c8001c0a00c81912041d60040f805980ca914245030010a03511008000540f0060382600f94041a6008107503035081e240c0003036012800c08020000310329515000c81c001002901c6500d07000050100c503602508004d44240d9402800034a54070007200c2c020b06000c1d10003040c1e00712000800064035000e00903089942e00e6050303181e109405031550a681c814008440011891755010028030713107810312500456540031862551001d080c240d0040c00110722 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 529326546 1250 529325296 529325339
    0x108070e09040c03051005040c0f0302060f070204090210020a050c0a0510111c0306090b040207080f0313020411070b010503031326030a0f02010b1e0103020306010e09161404 76
    0x7410701040620880241840140d9009022942c05805400781d242c01008100d41c26500903500b4000458a03100c50701d003040450703030000e14050500102c0c030004000c1d0f0f4441e43c030803640a0381d00c40791180140c9406515081c41c0c02580c01401100300c45040071828840e2034440310384070b0f0804940601c403a540e2610040f0420070280750448500002101d010300d014111881c0005401d803200b2100c28456040c0c0020040e20f1514006200d0700c4802c1e4103000582c0140000240b0402050281008401c0300320042c5900c90712a18034141030710703400d4011508071551040640704103040014228203110f500d11607207004250076030046240c00710840c01c05074424081d004001815040c0c0c071506642c02900003b10035048020030a40340e560200030806040104442c40c4140554207040c1c00c00090314140d40c0c00341c0450003a680c0e4400d5403c540b00118001c1d03000030922814484105000c2000743c940351211413003510b00840c0e00b070107250031620103010580e000d0800c0a18801c10003041c08200900e561440c074a03000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 529327796 1250 529326546 529326559
    0x441c2c030a091404270c15080705160c0e0103060c0f0e0d030215010b0c07081605011119141504050304090b1c03031b111513050f0604110108070e 64
    0x1c3c124006800381c150200c2051101031806003c82c2c0000750507048405480c80f610340c00c08144e07603611040c441d40d0044510540450801d10000d544039014034000c1c0400e0325080001c4803015010385d101e540003002e0341c1208205115450060080101c1449059801304a50600042948a500c8002c005014007040d06002e5005056a00109802000f590350004a03604140c41c540d0785803134058090350007510f41401c40d03200b2204000740000c4c01207100e01003441c031a40000c481c14100030040d20720703209501d840c180920a100508500411004502804501c01c2d000d0103c00310340540a50b203011041d80c501c0c60340d0492a03090000040d8000119070454100000c00b0550020307031800511103c143c4980701a00002002d41e20003019456400211160241d071003000030b007150100c1c12a04001c940901c002c3d29403020300d066040d690b00320081035000d030f181c04007681c003454265241810100c1d51a00d485860340038070240400c2188c2081c80b00c54010089c41e108059140410000340709194406900f409101d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 529329046 1250 529327796 529327829
    0xc05030f15030106052815090506071e0309050406050316330503060306160c0308060307080703260319051f03441c2c030a09 55
    0x1c400f0741001c001008010a0329100c4490b006584015254103140d40e4103800c00e80c800420302e004408a142e0387d500782980c400141c1c5003043d05108075580002c00070f40d03a02c0ea400b8054000301c040301d00e98229080c403d56441c50803e18080901069980e103070851131098101d01d035640c004900100050040755200b00c0d0601200361140d0b01e000075111030b0f914596000c51001201071209070450000c1d401507000307808488a42d50303102552200d0020360000203002450300c40c10b00b0003080c401c013107181e0081002405c1e1200148e5a00f510380c81d00c51a0b46c004c40b418014107150039100d80f008046900059040c4641c02d1452038000603981c407110100d6001107005580d00081034450044003400014914480e5410010300d859042c0107481003c1481481001d550020501140c510321007001c8511044c1c0c10452410b04007400c100c0c1446402105e080d0010030201101d8042200580c0164810389a40c0d003500c20300d0b83c40c0d035002401c44851040d2001c0c000e502c10000c00040c1035004403190104c0c4c51340c2c1030300e01019 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 529330296 1250 529329046 529329049
    0x908120d090f0501020a05040f05090103020121060b0c071e1401051602090a050117120d0c171005091b090405060609100306060e0306010f0605090d120c02040c05030f15 74
    0x1e03030070b580e0090305540c800b01e42c1504854122000708280c48401500b28007480e91403003040301808003400000c0c0020303500c00005221800103100300d00407415464000c80c109031140d44940b140d401044240000c0c0d84010000c001c0d10038440540c1801c45507030425418007a0401140c0c25030f450800d070010707041001c00100800d48001400c54800b02c80e07030051050f06142040c00d02280603107000c1c01003240316804501e80d0423040d400003800107090840502c0b264181480412000010250030f400003040c41030306081c50240c2558a800f840c8680c00c0c0000c0c200c2c1403810041031283c030803802084510400480b107644005030020300e09032000d400c401c46010a2965811000c14101d015101e1030030342100001d91042c0145416404c9041980c0e19a90b607800801481c404241da038440c00e110700125010880002c1c01100c1c49040100080702000d000401c0000e15503a60f00000601064904002185403040c00110f01c1c0c04d006d05492404c451400500314100400c1110401c013000c0e0010b401402c03540d5208445 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 529331546 1250 529330296 529330313
    0x90b07081b13090605011701050411041d0403020c030d0921021306030219050f040905011b0e0a2c07020f070620070b030408031e01080d0908120d09 65
    0x1403148506000d840300146515601860414025420f5860501c407010860354855010010a000a9403494450f030b482c03e03090000821000b40110365110040001203402c151030f00300ca4105078640804141146480e040c02418194802c50711446500f00c111007288e200d80c84604401a1040c4207000d24884004903130280e110300b0155402074005611040d5440184415403200301100d0003950016505035031a1050410005103018182e4001d503410340c050030320306242c1c0c0211152071040c80000b03159010030320300c0070003404030124110015203c0c192200349410541c80d602c00030034148500c542c08031000384140e00d0141001d80d610030000056800548480e208008100400020f01c0680e40701c9034840200402004c3c44208905050b0351030600b11200b030500140d03800413161644002401d58076955100745c050350010f400860500901c01d540b00e6144000c890300340c02801404001c0845404000018188441a41c07120209422800a01c641e00055500700c4401c7d100d400b00000380c0c00d1051a02590 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 529332796 1250 529331546 529331581
    0x280b160f0e0409230d300609060b0a02010e010515010804050c04022d0a0c0b040f020907030222060e10030f06060309140a080d052a1b01090b0708 64
    0xf9003130101c00003410000884224a0301c030780d5102d066545028068a003074484800b0700c0b080c03000002e4000081d20300c219100031625403240080b0404900c071955074000c10140c52040e04001003a400001c3d00104141d02442025400b0300000002d002c20710340505d0b002c900c140d0711800035050000910000f02040760a01c501b82010304014400c54070303055844103d03181c10340710111925030541c1d8003140c0760f200070516050b205a0541f9680d6071001c07201301ea60b111b04034072015000311241d6040030700c040d0050351100d0907644140c0c1d403594010703183c800d03218581b40010202d00d211350200b85281c8040c00840c2e07101140c901c2441c1c0546040c040c2c10b80d80601280245034801e040300034603145c1a00032800300d5054210700c460600684041c0200c0500001d03284c0c581a542c41d0060252008111481d00c580c50394104a5101e800719442600c0322001c001261040f5039034507041400900d0018000d039444640d43e1700c1151420700c9170000c000140d40396951381d006e100d018081d00309110b4094006681c814040c2160300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 529334046 1250 529332796 529332803
    0x4080d0b180a061e1a040b0c03070c2102060a0c020a0806010e09030c0d030c030209030114040b010b04060504031104020903120913050c090d020102280b160f0e0409 72
    0x444015030101c1c40c00e0012020b58514115905150000079030480007280e0030b0400010700e500e034504030310304901d6000c864080070390884500424880080c0c04140900644944011000a10b40e2401680340002e54071a10360401d8206202c0c001e511000450205402c1210590503211941d65410f03140050f14903c81c0c1d014001e6022051420214000001003540c07070494540401e8441203071642401c0d55100e014075580c40310503611003503110030494403d4105005584450030014600030312840480d0a50350141c84d9070604240c0c140500c001c0207078014030540108065400c141c1001d041240c020058411072001030f000d0b480c9640d40c800303699550390440e00a94401400c0742c811441130901c41c807640c2c12003c840361041820102400144010f40036079403152000f182c8461801e446042046008490100181e04600c101564009011030350b65900c5501122907885a6101042d8505012032940003005602d00105502075403c4864110102144d01c091604002c0481c42d41c64001c200100803955006c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 529335296 1250 529334046 529334059
    0x30b0a05040f0902030c01021c08040804050607061e11070206090406080a0c1404090201082a220b070c0b0f070c03140f0106050a06050a030f05011403160b0304080d0b 73
    0x26540c40c900d03406540410300c20341c1516006d0000d003005984500017110002d90898400d07011241080c403502c1d4243e4443d20454515003813a480e038020a5035074000e014110384a40d5110f00f0100c415005c0000a16070100c00c0f80305001c1c3d0801c1d120400001c0c013404100901403500032948160942e00e58200e03001030040300c4112803400c8400c1c107000c080841503101e01402041f40e070f81080450b04050045004941d01078442110b580c42e190703044521018803045040480b51411900440c0e114884010906c91103402840c0941c0542c4800401c1c0c40010fa510a0300e00d24820000f8100040f80060b980044a10100c0b131207032940c80940414900d4414494010000302034984084200a40c0c0c00b9a90002c504402c1156542c13001020542c0c201c8145010307840d44400ba454041100e24450740040c00008101c1c03401007850b02841ca00e030010345030280c204007900511612494224202003003d02900900b039080318a5081c076000f401d003610b100180c1302401038000040c0300100c0540c1500314045076440034100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 529336546 1250 529335296 529335311
    0x5220905010e03090109060e0d0b071806030b0307090e071401050705010f050a0f0b010c0215040e0c0c0f061909110319060f0c050904090212030c0a030806060415030b0a0504 76
    0x2d198890f480004500d0110f843e41c034022420710300c55440e9080321180504074401c180155200d620a08030010904020030030445594009104440f401e2402406180c6010a2039206041054200035960f0481090549061b00900b520303503000580708116040350342151104006a8012152441610000f512540c28066410131500f00d0740d200f00e119585280c000c024400702411402e003030b2800d8260442c00078030a584600c000d0300d45843e01640032290510300610305540c84003100a2880d0032180d0702c40300c00c000708040401c148107106d10508400340d07401401440c9060048a44440c42a0754029405941c1e0100e4204001440d03a10066007403004040b12441e4652401c084407940d000d40c8103ca01c0c6041400c0b110502100780036600300c50800d130b200c081c00c2c20341140902000300141c2c9410b030307031106200e66950034500d02400280b1206020300054444a0124140900000c5001c0c040d14050300d0304101c01c100e1640060b00080380e030056860b000c034498150700e0000303500850703d8200940c4a07241450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 529337796 1250 529336546 529336571
    0x5060708060a05120a0b0705220510030501050108010b3703060501020304081e0703080f0712021c0c23030c010b10051902070e0c09030f070522090501 66
    0x6405200d50411554619030b541c03648180011100ca221003050b10703501003130340c541c0000c207009245688401646403090500c48042d01c8820004102070b9907510b03500202c0c1c2c05008070f081c920310480c03502680f070806001652404000904440c41481010300c013050200e002c20000c1148a04103242887c548054050b640c0450142d01405c00442003080c003081c075000340010254004001d6800300c0e0f0014019240d8190540404c035486140d204070f1034054041c484000c00050700c1032014005040c1d401207041c0c0c503140c4510701001080405003200c01994001c002c19015550b040c070580446a85520f80b5142050091401ea50041ca003402106031501c10002280c03900000040501000e000c204000e02c83c1e081c98405110780d0156901011002407400c000c420304560b00c20844a8491202e8811036032079596840100c4d861090940b00c1c20110100028114081d01d000c1140c0341000c10510080d14180703260600140c071003404041c140207110f6000e2401c41d40d0031165400000740ca0b400c00c00911010782d4000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 529339046 1250 529337796 529337807
    0x901050d1412041d1e06060c07030605010f03230304050d05031207050d0c1d060c0f1002130501110a060b030114010e0f16020c010e0a0b07120201050108012a020703050607 75
    0x91002040c9809400188017a181c0202c8004201110606400e6511140d00b0702c9a1648903a40c030740d90034441c003400040050345038880da5000b010680d035220740d031a095182031022462640110320207046a00060511045c0200455003211400c56014024115510302141580140301c05040710121682c1008542500721008014001c408001000494480502503a85c0e6920180c00c0c10081000402d0314001e0400800805403200701000300c4100b00410000645000315030416403400c0d0b074001c40d642c03040c0c56200c0409005000c09080c500702848180c9515652507014080c040e00320343c3c43d41c60401c00703a1001e5120801682980e107984200d907844940103903d4a0040d038082000c0b030590b000244004000301c0031210210b0b4154094500f4241d400011640c14011981542d0710040c1c0c1c040c00030f04002c8041c01884140c1c8184409950300b00d507110041c2c00c490050f4401d928990500c496550180e00108480001c40d0003043d0a201040418604a00d00b0712960401891482840180001c41c2e4019 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 529340296 1250 529339046 529339079
    0xd0f0e090406050a0509010905120a020f0304080309040605040606320703020f0f06060d080f0412120f020105010620030405030307050609071d0c1c060603020a0e0901050d141204 78
    0xc0c00a1080380c07189100242214008800a040c41d000ac5800c401517041302e500070100c0c40c4030f40c0b040300ca0103a14603540350b0559100ea4000d010342d5000240207400c1d81000c1c040d5200814040f101005141d18008010b4800d03070b4040c1703000340c01520010b15a0301400001c91400b5600044411a036220310152801035030f2010400e100329074911904084013581e031000107034a8850540501484081d21842d52400743c950000000340071854024403000c11040611a501c80303d940c0100d5201e101070500c1c80d80544005070382c1260a00716414280180401500000c81070104000240f8180020344035084031401c6026582213036915000003c5e1800034064001240380c0110b4003041034811076a42c42c015900c0307801c00c4040d446900010003000904618114019000d00402031075a10380c15643d00707055004841050300540e02195001c150322440c103600c0b40f27054030b000c1c005881d01c0b1400c1d4107150026190a0300010024101d000310223601c1d0b4816003e00220034514400d00e00d00d6100c0c1d0304d07442d500c150701000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 529341546 1250 529340296 529340311
    0x3050d0f080c0309030406050c0106051005120907050f0f0a090207062a0813140d1e050306031009020109030602070f0b070305060a031b0302030331080d0f0e09040605 73
    0x1072400318a0490154003104c0c01020560000c500c1d2914143c4165440c1d04958052100b075580d52400241640315003450b080303c01d1042e41d0359035070b80944002d02011080042d140d015294420070040c481b03a20b812192104001e002c4810b81c51601061303000980700c018580041507030a0010449100f0403e080c0c000350380b41e0054146402d600805103440c68600203071644484005000d03180411601c941c0341011100040c00340410081045200421516040f402d40c0042c00142d00030040320050000614415081c0080b45040741ca54102000021355540c905940380031402c1d6038040907800c680c040c0380b015004607408a000c3d502d400090a01001201c98003a06035140101040051040c0d407192050f01c0c418640145100f0030181940c445043d956821007440f8450040c460002c8050380d42080070345100e5600290826800f944400301d604804100c4204d1280421310410502c0780b90804a00000031641925100a1000d40c251045407018024030019800914070b100740070601089030841403081e4407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 529342796 1250 529341546 529341557
    0xf090f071415160b0402040f020c1b04180206031f150f0503040206031503210d1d0d050c01020d02160201080f090d050702060d06060801080625050306030703050d0f 72
    0x20314a0207540244503207541c00304040c07602d01070f0400260f04015030a4020740003030f10003d41c0c9121407291404a904c90661080d00d075009060b0002103000c0095100105201aa4140141400301c0203030754446600d41030081c81114003000254004c91f203694030354211260070003102c18a0341d880034011641c4400001440004038081880002c02c1c1c0076508481c042c0c0da016150510790782d01c000840305042d514500d80c59250050b0407280341606101c020884042d40381d000f6581c5c1d80ea804103000c10842c1c544103200e43c1041d1000c1d4180b030314081c0201c0c0341e840020032418510358980c281a802d034021310075081c20114091000c0b03075185081704c0c41840e000c2100e2003030b01d4075107507619003440c3e2500c02c0004950310250b40e40920545200079200f0b401800702d40e44050302081c10904001c8514080d603440f90400400201400010821000b003089001e07000102c129840d45600d105490f5944184131008203007080c00070001c0456025201048204000e60304070051b40c01080d40350710001e0100c494045c41c8400140c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 529344046 1250 529342796 529342819
    0x160206091c0507080d0c03030b120618280206070c03080d2903100c0203120906160c080a08060d060903031505152a0a0303022701080f090f0714 63
    0x80000510900441207506d403081b55070f1003642c00701c0141c80c61008054120502c1004281d90407403c1026900850f0200d106004080d0480321091a00b0740221802d260381c0c1d01011500080403440781007456035501135560070781e038203142d0800c2d101c91314003035100606c0c070200010b40341a4400281d10002d060b400c1e821112005440340d1154408601c2c1008030a80c0c160403d03003c506201c0c035680e101600c079018500540b400c05081400c20003c661084603008166041801040100d0110407441610940d4a0424200100e02900d85000038060210242c0038407089001007041c1d5520200a504d0f510303800030301030200f480e00c0c3c1b4008015220000094070070204101d0702041c1460301402d0081200720701c1c040345080402d44015003562150f525180b0070581401a004030f07010030103001c0d140c502030007510b0160ba50900400003289501301d6145040d0b0100c1c12031040340b81c680c0c2c0110b03425005602d491007403c140c0c4032130a03041e042c0443ca0748620350350302c07030784400140f080781580a000b5a05401c690456191 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 529345296 1250 529344046 529344059
    0x30c1d0105010e01080106030c170406062d0509040213090609060506010504030506041203060b0c0714040209090a0f0f060602160506031e0a02040905010308120603070605160206091c0507 82
    0x2c50703c4080d1502250018005012403846a0b02c507106009651504504027020001041240d0805907400e9030324030303154242400b84403902800c0c050481c0303020404a404145c004c05c0c441c8289a5030003614070540c58403010500f955a031210028202e041d818040001d025140341c100028880360508960325801d0000007082e540c0100182c0382101d4203c0c025110581e699900c40c940c0c1d0050409000c01e241d81c5040118005482c4409080c480d0032450003441280c0c202680f482d01203580b0301c5094451801000039503419150004032940212008031301040d044200c02103440a07110069412004078901480040c401d41e0010350205c00c1d180000b95151813039103420500009100454994201d16868611540000000300e195a0b0007070380c1050060519803996050700075078100780e00039180d09070003080076419558103408481d0000f50490040c6141d5103031280180c2540a02019510718080c100703000425500ca040c202c0e000d1440041540213000e5404100460b000102c070010754040c41080c1010030403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 529346546 1250 529345296 529345307
    0xb151210150318050703030f08010b03010b07060506010e040f0b010915020a02150d0c080906090114070c080403060213031401060f030b06030f0601061d0102010b09060405040c030c1d010501 83
    0xc1c1c5030211950060108400380c103a01078030802c03159441c815104501c81e0301050081c80604d01451180d522481d9401d07400a00030030302c00b8107800804005004000410042e1442022512515070103a400b181d503a03910380050300c0300d001d0503c000760014141800d6000b4001168000082c020098030f40313071a1251110200c0d081003191407a20b00140e804503000e54050f07d001485140b0000c029514203140620301c0c01a042510700e034006c140c01045140c0280f18036018140002948071503410b000300617901c0701c96460054000081c10b0700c828410083e48517804e002050080720003a542001e410355961046031001d812030942e51005494440300c0c0c3c80e441c8104c440600400c0115121b40c003e400c2002d0643c2c49841000724041d01d80b070703814820092400c208000603c1514001c2045440700c1d42100c4481c4030500e05410300b0307a111411645080200c01d465a98020301a0f0004001d0301d0024140c1d03142c0c0340015480ca110740028200c80c14030300d00020704104a403100d2001c020880900c1c0c02599880340192107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 529347796 1250 529346546 529346549
    0xe0a0f052404030f020a0b190f0e220b0d0506011a0408030906030a0905101d21070201110304080c1804050c12030d0603151a0604060f030b151210 64
    0x2201e4002c00040010603600600340d12643d00003000e0001c441da8078400c0c1811075001d09244031140c03040c03828411215802c00491032401590741440b900c1e03692003c1c0014000084030040c050400052511b200480d0381c2640480300140d40980510000001810803503550f0000348646000000c1050f19142074084640941c7c0031201120011400c000a01003004120780000700324000c1c0580c0c074103154001c02e2007040144c602e80758040703001422038a00c170300500104640340301500d090f82c40780c1e00061501c035110007a0580251420389041d1660800c0c40100c1d00b030300c640d20f80c0b09030511003c9800b06005030089040e81d00d801084803052011f49142c1400b5050701011540900143c101d04a0003039a41800501819034034940d00c160307440c052107901104100e910540060301d042030240b9090344903140e24810503403020f905c1100f0340039100c6140c00064051003103008500810525070310350b54045009400c035508160000f400b203140c3c640c0d1000e0f00e0f0100d400c0340c004011100d09500100c0d208c180d1034040d0350f0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 529349046 1250 529347796 529347859
    0xf05031606030519050a090507090213060804050a120216091a0d1103030a03020a030b0a050d0219270b10020601290c030901021605100f0e0a0f05 64
    0x800c2854500150014800200442400a00401c822451a215225091040106080c001006401c07418414031703100498000a00705441040040c03415426450904d040310600d00c1c00114a0341c0d00d15200d810a02c0d04100280f080c03c960310300300001500841c1c01c402120300014880c0c0e840b5a185245400e030340d8641400c0d0451070885003611810304004540026213400740302000390101603a00842c0c0b0b180c2c010b0303d900700002e50101342c010700b290780741c0500010000c0c1191180c03611401c2200041c220707440c45000074441d441a007058100c0400740c10b26240102034003c0c071048485a9244880311500003d280810090324204854a40b4541440c5442c5104100e60080000717a0070301d14020b801e47d8820074400b02d81d004420f81409004c010100414032243c000c4042c1d51550903060001e881c10700401c0307140c444507025a005001a403100310603280156021b2402d03400950825200350303482075200c2c01803908240d0320b14002c200240d84284d9041200c1c5c098405003a60103101140400e40f1046102c2030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 529350296 1250 529349046 529349083
    0x50403080705090a0b0a11070806091504051e0a060606020d080a0911120705060d0b1c03020d140909040c0312020708062d01030605010305010b060c06270f010203010f0503 75
    0x2401000c0717201019028031000f500b060450a00b01340f629a00e0820603600c140d583e40d00030003c020005105210400b08030480d01c601e54828145940c803141c6600d41c8102d031024148010007401d0500e40304100c814415038108804112107a20742c24001e485e000c1190410010444810200f01003032200d10800da1220b40280c49000b00010b5101003220710980e402411030b99101d8528003185607a100b800424142225850005403c2221418800c00a02603c103151140d00c2c2c0a00d50004240c001c1610701902e034a6250110181241c041c801e40d15000d8985d080d5040300501042100b00a400ca60180c103032802040b002c0150072840344103e83e10151401081100d03004180482d0740001805c240c110144040a00585054044042000100c0017640213869443e200c10041061000130b00c02c105600b5001c0c0c60040c0f03051500019180c0c0c500010300b085201c80180c0c0542c001c58000700e001403034011440400d442007501440e40d918041c0d0002c1c000ca0480d40110400003d0341d1400242400d041240c003002d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 529351546 1250 529350296 529350299
    0x1805060610020708120d0b03010908040b07020a0f080a061401050f1c0b0f04120203071a190507030f060e071715031903031a06090d060204030f0303050403080705090a 73
    0x41c000c90703840107800c1d10290f01c9a4400071440c2039007072121074001075500c1c4801c0e4850184070f503200d040c3d0380000c0c1c84038080d0345091810004110000111020b0313913200c9402035038a5941b44040741c80c60040d80d10200c012860a200800d6900300450316120141c09200300b4007091a03004081d1900c00310030b11843d40e02141c0000c0c044040d06128400249034856250210f6510b03415441d85115000111a8900d00340b098004000c1040000f29042ca0900c0c800d10044d82000c800d66101009416074401d07120000300c0090020707050150341c1103d654001007900e8144040d00f084800a0050700c03c1000c1d00704424100070000c980d074040c9021552094126a071010000d06860544030042000544207068240c10700f1410f1009442c01c10103206008102c0f4001040c4071490704005084411441c8104040c504a1001301103503510f090035210b560f0011641301d10031480d240340002c0284990f0b440140301d161411100010f050301988110720803400380d03c40341c1c0990749102c803c840303d1045034075890348050403100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 529352796 1250 529351546 529351549
    0x203160b0d0e01090b09150901060323030c011a2d01081008070f170309011d030c21060610140a0e12010c1b030905041a090907050418050606 62
    0x122a6070101400300008241381903031254880e031760085034410003651040c0302c0c0780c3c5c4111104500e154031045040080000b2415a070b070304100c0b2032401d01e00b03902ca41825400c0401070a414070407100700a034004000c10424040103c2a041d03660301006841c46000003507941417551000c0305980c04040d210340f002210803140030005445402e0042c0184400980c400c4006c03c002c0d0040101c00c01030f0001c2d5440071a5075151600001106420064014a6410500c2000e41c242d80100d600c684c00c10384442854241950040480e00d00b2401c40740d031a034008020100c41c0030036668454282c40012010040e2406550b900c4180600e61122140d550005000500ba400303000804030054080c01f1190725250580d0310403407002a008031624605020641d6640c659440740a03040590414101d800500040c1034040e917460240c258411445503074001c1e5112450301200302880c104107c0703000d40052032240755081544500ba500c0f0342c90701500b40154900364500710089031040a00e48125440f0005010a035103010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 529354046 1250 529352796 529352801
    0x312150907120f0b0102190c03020919152106020c1603020a0803070302070605031306060303020f100606051b03220305120f16020f04112701080403050c2104030203160b0d 75
    0x141e00743c5503d1b2341c01c2e03004401a540d403241c46000d01d003915501c591704145100820304641b118a200855040364100800c224103a41c07501c81107642d04591004441c11310b504000001c0c2c03203001240b41d100e01604024903014600d04040c0320903680295a280c0b41c585e00c4440c059500c0c0b08006000d00503a011400801c940c610400045900400b034440c040c1c10f078078550342c4c0c034026212980c1084003d60000086002c0c0c03250704200d403a600c810b0911050080502d0590050098455506c0d006a91b240d034050000c41a02c0800449041003d0301c85048807003e40481c00101c85109800704440700e005034150740010030000c5050310900c2d10b01c100038528003003282040b000001095281242c00003e1440000520394441c45251008401e0080c403590758815818810b104105071203400140003102160940a42d0303002032100d52080c1d16082440e95196a400100e250480d106045000307100b050040d031100701ca052000d802100d200703404541034240181c0400005e164103000391724184c0c406120400b800c02654 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 529355296 1250 529354046 529354093
    0xc080f0606120106030209010b0a03050a0504080945100806070c02040b04060f0f061103070b090a050303070c0611031b0d0213080106060801170312150907120f0b0102 73
    0x80e0b00000300195070f075001c540300b980260b0009140600102c4c4012a4a0b018000d075a4400308000f03080180c0d140c16924020b250003031030b0909015440003003181400b03041080d8840c0c4802d06c0c5200e010742246500e04102131002c0028141010324201f10085a20b548411307901c01d0a0b5010b42001d4001559550000c50f008006450245c0e0302c40e44480c01041c07161194400c41024040c000e000d008142c2c01c0c034241c1c0c2000d0000750700c010100030400d444a80d0311507000c4155008030383c0c42581006c560300c60440392032034060700f24809030440c040003040c080201d40005810341d42a114031014040481c1185102900340400c48004a01240c07240d802c690100240b070040000741c904090050400a40408000e070b05041d5821450f042c0e036598400744041600501850b004144c2040900e1441c40d82003502522030007400c400c2c82841034044089800c8000751780164200850180404c2c189281c1a03800421222100116100052a146907000e0601560180204504040e0020f00300603282c05040240d120341c030b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 529356546 1250 529355296 529355329
    0x10b030406020415020706020c0a030308041106190305041e02130c02033f1306090602040b07050d1106060a1e030c0305060717060a050607020d06050a090c080f0606 72
    0x3000007140100c681103004c0c078014480d0b801050010f05000d4080d01c1d0058030100503201d02070b01c07201000040e6110001030741c81940a01441001004000070815500400c21202c1301031910410b404100c1ea41940414480c50148160110711380c100d00071444010907051006c1c1d00b0282051035244002e01c44d82084200741000e10459180040c51070440000840510707001c410200843e01c1c0d0a040c10130415002071540d0031426440c0f0609003d42d22031150f08810310000e14498540c00700d2000e103c1154165001014803002a654568292804648816001442d00080b94500000754031a610018500f84544009410050340d241050f22500e410442d07403101080d154503c0b45d0200014800908590080d88500004c0100d801c2210024040c0942030070103512088112040100303a41d0f03040c000c079049607070564443c0c0d60740b5002e0020a56508000390003502c9d15081c2010700c24490f6060340040d070018002c00000443e55101c1c081151030300000c40b085071290b80700c0340108100c1d2402030030400303d0282 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 529357796 1250 529356546 529356551
    0xa0b160912020f1e0307090506010e010f02030706021c140606090d02030c030a3009090e2d15101401020f010c020c01030501050402070b040305092b02010e090906010b030406 76
    0xc02000160741c04c00201005032189007000e06510241070821184010300034200c0d041c00380e40382040000300107140140a0314100f190241c40783e0500c6000b03200700c0c0e142d150000070642d5a10b181c00da8804212071402d1140f40c1d00303450011000801d11414217124024030004260324a40842c203000c1107800701c010942607030306003d0280400c5480c1d41c208209c06001d807140040345144034075019903040c4400c40c2d20048007090f086408041e00700382c0c04044242500d05181e8002044c42465080c0d07403800041d0300500121048036500f203038003100841c8000141c20890030031a45036040f40152150454802d840d0821481d0b014201841140c54103924048c40020601c1200c10124249440e03e0035121b81000368000b40e0031170219082596414054903015103001d1780c0561804580d81e0b211f003643c1d04018005401c07c40d002c80e4040395640e0344002103540e4510030b030311100001240b0031044080d00704d0b040100d003c03c401e1804030219003010b2504138840c2c0e140030042d020b60303842c08180071260340c80140100d5a03140e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 529359046 1250 529357796 529357819
    0x1090504021b01061e05010f1407060b030a0302071707050d110f090f06241c063c050907030b010e09070c05070e160309060f020c0a0b16091202 63
    0x80c2c248550030044c401c6001c2d8217030141c2e8440300b0b11001c1c815504000e0400889a06545800703820030000910030504102301580c4400904008006001d6000140d43c14012072100006040c4e000403414165401540d09100c004c070380007041d903540c1c00648640b54004250064000110f103150207416055440603002082c04200c1d130b8005951901c040320310709103803650300040c4000340c100300d80d1049480d02c0e03104d600241d80c40f12040084460040c2141080010408020440e2601e10b94200000800c2072100c01c10070421000d1f000c60012082c40030b0f0003400300c40c5d410000042c015141482c2d00f1504094507900058039403080072000b5201d11002141440303000402404103403501d011240c0301d220310b030f59041c1401401d40307000c50602d2020750003c201c3c14040400d10022110003880542c1c04802801c0001c0ca003000d91420401810b0321041d5056040d1000c54107146100010a1070701103584540328010135641ea011140503c902440c0c80d0380d00142c01e10909010800c000c00528240714001001c404c20305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 529360296 1250 529359046 529359097
    0xa060b03101409014d0a02070303030f0908042c010b0901080a0c020c011b020301020711030d03020a020d030203180f010605040e0102070b06061b0f0604020f0f0109050402 75
    0x4440461004604110030420091010402c1c400d0032800b1942218420715840040581c50007003c240620201d205c600945010446040180d490404001044a15241e40702401d02a4a5540303500c8180c011909040703281818460030301c035048065030320031022401e250600c148010100985040001c1c06000140049003034888409407900034050803d001340ea620741000010310760310004d001411503c0c1888a804030068020a0070f03c1100c10030703e8200751004881500c0383c0301401048020350103500c001450b0f0180518050441c0610b02c003502110b010107a1000100c6c02c81c8600e00f500001600010340c612080c9201c1d40003180c0190341c2010b140c044502c0c44010500b031814112404050740e65820040045c0d00b040d0083c1c07407500308000003c600303142d0b40f80c590003a005030007032005110b500300261242000c02a03403195481c410042003103888680c03201e41d050340e40c3c00c2e06940c140e1050702c9125404100707281ca03140c00729030182c0603501d004407145400b0a110103034100c0d0101c1e2070851859207500000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 529361546 1250 529360296 529360301
    0x40e07033503040609061a09010b0a03020909040506010e0702060708041b150c0303060501030b0303090d170a0306140d2006310504020306010c12051e0a12020301080a060b0310 77
    0x51402413030300146054480c58003404907102c501007074880806030030362402c2c5aa26055240c1c11640f1700b250483d521810108120001e200d020007c1e07a121029200380404d00c000001c2c920705941e007a0340c5040c0f0729101c8510a0b40d81d050101c44100000341c1860004000941104140c2e2081500c004140180c80d180d1441564031a12204500001540800c5010500d03905008801c0181402c0c202000a10351640c08682caa1240c400d40030b0040c41503500c03400c104149258606400b81201a041d07803100700044004020342030300d128090b446520000046503a00d04400c400c036140e64402d10340e0700504041c4154203900c0c16003284069000200b44040380180003486818030742ea0280d9100b0841c0c0e10b071500c13207001c8503414940140d07000768414400c0150590b040303404440055081b07442402400b4818100b15a14424180f03c034680038100d019103900c000384d50016100c80101070305c0303080440000c59091801c0f4082441404082d910295a031004900a9071220b601c0d50300203401d9416410000b00160305 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 529362796 1250 529361546 529361551
    0x207034101020d060905071205130204050103080a14091003050709030525081c0c0f02060f09120c030d05090604170607142a010f0f0506040e07033503 66
    0x2441c2d400066100003180d25100b0360020340039801d0204280d0410420040001c0c40c180003e80003c0d55030030100f07122009103000f100701a0382c0140b041c8000d41e141d2030406080d41008410302c01003080c01c00380745055460300003a030303503140c4c0c000d08100c8140340300d0b031011406030801500034814020242c4000c00868000d1100354003094203282c02040d01b034070003000d11500c2d184a5001140540000101c03021051841c0b210040d000034614103100710021071b04000f15002c0d40340f00c0c000e512541c002400200b96000300041d010440b411181030a00c071024002c810384595268020030b50607004111844802800f0f200074100030407011b0b020b10b08140c4c844000e00d41c42c0e8028500000a580401d0410213190b504c40d540c2549500503003102814003400080c0d000801c044980170038142840c45035401c00e070340c81c250700c421400d041d4001d062040302e400c58100c0005041c2550f003180194100b070100300d10408000b03402c00c1126440510714482d80c00040c2da0078101e158030714100b101c881c0180000550010007401550 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 529364046 1250 529362796 529362923
    0x6010e0147030907080307050d0e012601050906010e0d060f021b0705030601080d05030604050a092910080c04020a0e030f1c03060b0315220203010510020703 69
    0xc2d503e00f02200118682a9190b01c4044140d0007006480c0000e140030403403188030000303400c08480060214005840818103141c1c1418001c1c1801850421420054801307812190103503050115521440011a24020448080c540040d0700400b10000280307039500243d01008034850042c1044e080000c943c40440a04075141d0565104000c14000c038030303060008500601d02e1900500b80e401500f0700c0a05980001007170700f0300c1903a480380004d0590295810045079198402241d414100100341e11481808428804454030060b00c00044e0103006919440c00a4441c1c2800400e01203190342e0400003c0e40c400c03450603081082c880040d80180d102009600030214801d40500121800c0b8440e241d40b161003040c02604050400c001000941c4880007203a40102c1d00880071035944010f80d0105089503281030440c140345072006642c840011199020b14180c40c01140c02c0c18100c04180001c036591400e502020302030f40000c0c44100100721034a081403103110358500c864010350b0842c20401d91300c244040c1c1e800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 529365296 1250 529364046 529364189
    0x5010305060705070506070c0f140f010f0e07030b04060605090f01080111031509060301061a04030606151715041e0b120c040903171005010206010e01 66
    0x18010060140a00d59002926292550904540e03480300da941d61000703400541800b00c0c1200f0a020720074542c007a114403907000544e003c4040b0055403c15540c28040c1000e003115442d00c4040c9465404034010000300d400b48070024200e4906546801000300e0000e401101c140d5601c520002d6140c44190035540300d0480d106081c44151701d401d14450940e481c0c00c03031540313201c800ac00401620f4048082c2d000e2017810151090b80040c4d1301d40c404079004107050341200c03000d4000740680c030b55043c040000400581e0700c1108207003d02c03540c0d00f000c80703103c030042c0b1040c802040c200c6014810070415141000e07440f001482c84400c0070b80601c40840c0803036903492802da03031101c00f00c000c10103440d61500502c030090605a407100c2e07010032140481519041d44021683c030482d00e840d884800c0c1485014110090074000b40304810a090403114450402100c0c03103018058083d0f81c2c000a81540a11021412180c82680e1080001d00100d07007081c1c1103449104c0c0c8041910443e1082c14074084041d50f40c0a16200514034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 529366546 1250 529365296 529365299
    0x1e0b10120b041b0206100608060306010e07020a020a140f010503040c0b07080d02041503060e0405060a020a0e0a08030430110a0914040b01050a1a0a11100606080c0901050901110712060501 82
    0x34141b02d000c1e040141804444c0c002d011050710005a070b2411914180000d80064071a40d4040307003040329142d00070794440d00819020440713209a04101d485400101c805001200c442c000542d02d500007210050041840f80e181084003d00c510000e014480c41110145e15042c5168860022030300103400540c4041d0420b8080a0b0140d01485520003801c00702900c10401e140c00c1da00c0595850340101800446074000c60482c480324080d0600c00350300000101140f0003641c841c07150301e40c0e0b034000c1e100780074020500c5401080da25442980940308601100800c0a07000055195850440801801e01e500720041071800601041a84581e400c404464941c0c40103d00701401c0580c588071040e04101d2042583d040d0402c81c101c1c412424a903050642881c1c640c8030285c000003500d0b0130303c1526203000e032800b031521140e000d010150302c09000e40d4000e4403200420b0710344507244407140c05402606408108100901c201540c01160b50b08000e074519400c440c90300d07498445030300d40000700880803600c0b29240c200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 529367796 1250 529366546 529366561
    0x602010f0f0227040204050414061005070f0308040305040f0b030604110a02030406030b0a030f03110d03090201050714120a02010905100c2708011e0b10120b041b0206 73
    0x4820012807040e6056052948101d40c0b012a01a1202c481d0242588514240c4031921a0b806440c01844002d000f044580e80d048107065101b101162050b12a41c40b1500c803160541c007034826136042c035030050b017110803418603582c007555052030151064051003424440041c0060a0591031000ba001b80e03000c1545a040c0701043c0400e40e000044080c0c504002844031403042507001041e501111680e26000c03852840d40c00218400c0c1c5000d800290011100940300d400341604040c0f1400c58125120807110544009c11040f8110b461007607000740001e204100100c00302d070b8144640125260900c080d220211140d155442c03403540461144405030351034042200900c03101380210303070404414800c18004200d807014010301420740c0c00310075402c00000e81075203440701d50002c94040c0540081c2d4000c01501c40d06400c8585030b50141c3e159407108038100100342d500c40c1801345030321500070110b89800221400742100d0a0207405550866500540d0319040b44050a95512240380c01c3c0007a178018100c207080000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 529369046 1250 529367796 529367801
    0x307030c0e04060605030613240e0a050603030f03071803030e03160b040306110715050f1317091503040804090509190f0c09020304151803090504090503130602010f 72
    0x101e01c0d4401c0d483c02c03c040003d1a003000031294040821201c101982640115000080400751820300e0070003000b002e01e40c50b9242c0040300d0000d4404414210740e80c2e030342d0b20402000fa110708440d8141c0640041c4400000070b4600f4010b550401010700302100b03a03490700c41102c80714482c960b109800040300841840900c0c2403e001d080800004552901106410a000f6a01c244071701c0c40020b08483d9a1ba10030040d82a48105490085a00110b003002002c04100d50300c019101c02d6034202c981d074075420302040101b00041c0f2080b20081e0b000d010340c5440c01d2031810b0b8030241d402030301d0580c1e0030001800c0e0001c4031030071a20007035119600c10001240c07514100026401103d00c010210846a4440d040c40b41428468003222001c2c56800603d030840e800075440c1018000f0110b501c41c24409001109000401034405d030320704c10303800501d9020003400460300f44000c916000c845015011913500c14007848030b400c0030b810404102d4040c0f01100d24000c24207001e000f1090041e4410030040c0d5407100540018074050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 529370296 1250 529369046 529369067
    0x4030914010504050f060912060a0c02100605031504050c0a060c050c03010e070b13050411071103032b0b030a050a3e0109090f06091401030c03080a11030307030c 71
    0x2860b10340d00302410480850b8a030388510001500c10310001c41c0a0078180e440401d00b88c00c0c805030400f5542c0030301304942c444000d08481c038401000b41c040c00365030440304c580c82d104010490350010b00a01425080102c05004000302034429503a6004080c0b0003545501c078501075000626165851000c001402c3c01c0883c00d040c840328486200340d051090107001200001a400b013a100708100843d95026122b0700c031b06011140e50300240d0003508151461100e00350250152607500c0c02400b0b03000020980c80105601c074410881500c00d0202d281c1680814200d6005a00c010030a482c00b002841b003618500080c03400300144000c59981d846150254108100c00d0701112690013410f42110401c2c90707120407202e54442c0000303581407005124440380b4480c2e20842c4a0002815000c208000c590f90b1441010f000e0b24640c00740e003d1442c2000720301c180480c0340c81d90380c0d812240c01061080310b160469a4910150303122220240c00c019010745039080294040c0001c6001d9800d9032030010b100714030014041c1000950 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 529371546 1250 529370296 529370299
    0x1a030304080313140a03020121060e040b0a0c1407020103180b1b0315010309050c12010518070b04140d0b010b0703030e010207033009051509070807030609081204030914 74
    0x2031071342e0001903072298480041030702c1e07090a04040c40c02001010f078603400a050f090240b041d04140300050b905030f000c441c0c140103a0244051451903600c66289038250384440b151a0001040780700e442889100910151104520502d004111006040340c0b9800041c1c250b0003d9842d0300203134040c0324071801e544c1100c61100381503c0006055143c504880f00d00500e290f08a14103064075800c0084c10042c0c1403100c12a8524000c0c6402c01c501c00f40034202d0b00801084800040c1200c00048080b90f52100254540484420554080c07030300d820321014007c0d40c129400f40e180c00482c08a441c2000805209815002e000070006468603a030385408d0085c141e45000c0020700503a4070400ca170501007030303026580c100450280c2468904800c50f60030001c0600102d98a0000b0f807502c0c1441c0c5504110001c190f201305d00350350740008103250725842c0c0915200c5030648108151540040ba00b00b00080c3c030703600005180e60003240b00074244511100304541c0b000f01101c04800107412000306008480ca40c10409014000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 529372796 1250 529371546 529371569
    0xb0f0306010e12030d0b1f182715080a050309102109030516060614091e0c19030506180c090f120d110d18091a030304080313 55
    0xf40b114003e07499110300e400c0307031001d2911126800f12a89400f40220304d80d41c00001c0964101c4605180140010320000c180010032800c440e00041e14500000800d8118040c04a1b86c80e415003040d044100508106020302c0700031281c5000000d0644040c481c039240140104051943c44000004021003440340500040a1001e0403056500aa1845240110300d6981c0c07030f0001a42006800d0543c0d440c081c1310380418410302041000c0741085842c4d00078800b100e084c4641d1403512546042000907801007100d0355001e03062455008015501d91000300e85c1c001e40d40004a502d882d90507107060484400140350359001c25201da06201c51070916032401001c00d1604042d032031072424030381010103543c0714400603144250062551002c1c960344001012410318000c104942075000307143d40252481100c0001a4518051440c8041303089020b0014894000d0103003005024046c01c1000301e00040c0314200b000d800004d2001d500d12580d403020001040a01200300c01140c8401c00d61643e00c44c4400c86802058100c2c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 529374046 1250 529372796 529372819
    0x60f030522030c06061403070e2e050a03061409061006050c0c0402030114010807030e0316140a08030a0b010c050312180307120e120a030e03070b0f0306010e 69
    0x1019600080032500d250200e0400000300c1d07040440300c9a030a843c015084514250740052610900d00011048031030940035a40c60603a01c40d00e42c1004803003102d0482d00c040140360481800d031a1040540f9500c51441c0b445802070391240c0105d42c0e81e0f0b666800407140a513940542100c01902d070840c42c0c4e0f200080a005024618241d04400b03480005031107032009005000c500d034034040c0c4d03050015035850700010b0301c115100d694a083da80e5003110100c94940c046040c90b800300c0e030500d200c3d009a0001006500095141c01084940401404451079060b195403001300c401e41c40587e001d1150515043c00340c12030544a04110300040101ca0345414030b80e06014490303561100003503000c01600c0300c09048400300d00d4581c0c0d8510004a00c13070004a03241007940000030b20030701041107480740d000425180703990322183c4880c0c040a11461480311403020304075910810281c0c001a01c117000f00a00c43ea800340a0311200d954070002100107400c4406080606030000c0301700016540d021400300c15101d003c481a080c400b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 529375296 1250 529374046 529374061
    0x80d0210020a11011a04060e01140f0409021c0b0c0702012007121202010501060305040803060f06160609172506060e07031a0a08100b0406081204060f0305 68
    0x40d0352800010408580102d6007418182c0103200e051208850007001340640d803160022074840c40c0a07482c003d4402c078075156010403541003401f0340c00d051728440b041880441ca55403013000396240f41001c602ea401500c40700a4401070300c4074184452142184035001501e02050b01d040d0310040350041c10f007403400031b0034440400580e03030004084407000581034400300c6075910401e140d410310059401c08000508130503040c0b401c106400788194483e02c0c0c3d6900070000341c0d0302d4000880071ba543c103490162502000740045501807415100c000d00c58040101003a1a00c0d1450b50350480d945944002a034245a843c948030041c861150700410400c07210203403aa1420064603218070007006180482191522220812403c00c282544004c01520310242042d40c54134264400501901d1030707060050081c42c0040d48503003207041c102189000e980c038950180100706a0360220308014289085e9851307202f1b44a08000a0031201400040c0e03005100d2145269a01d0910700d01424400405200b08101480e01c010440382 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 529376546 1250 529375296 529375303
    0x604050601023906071b0503010b0a05040e1f02122220090c030106110a080d090c0b04030807051b011b03032c0127021c05010222080d02 60
    0x410741c3d070262044081c00c0b5010300c114400c06100c8a40000c00000c1420030b0090120800c074054a086a220f0b2483c2d458400789801d0b21000b2070b500e82c01c40a088000d00840c902908082c0550b5081003c0702c03070916203400c0452120003a000d148820361382c0000c420014840c4007114683c403640224010151446084001c9403400141d6406404654804480f1401040307002020420400060104860b4200440840b01c2c030340c0b007072190f10b001c03c00e03001701407030360601c0401d001c00e1040e0091451414294072003884c070003401c220303041100d200c50840c0000c01c08040c5540504081c47c01025100d446406900d0b01074030380440041918040040203020f4000341c2e034441e641c0c19000148240c80c0b000c060701481c0c240e0240400022511182524001c2e1040d2440b8184680c1c480f020344c1002800354040e031810400040f4480499251100d9200c9843c40140c1000c03800341d003210b003801014201c900700c6526014220380002c42001180107991b4001000b00c44088107a001420b0868040c2c82031819a40b0041d40c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 529377796 1250 529376546 529376593
    0x1020f0114151c1a01050f010c0312020403080c0a11010c11012001020c281109040314070b0a0609020306130506130914011a010f050d0f060b03060405060102 69
    0x44030048502c4281e503102c464107422000c03032406441d91a40c000b0310704042d000b80720450201402da62900002034620f00a5040e240840d410703101d00d0002245502c044903141c600d40641055282c08002c000001200c42005000380c08109015000b40f04682c0b408169994030043d41904000c405c4803040d000c00c408056160700100c00b401c15000740c500d59501d0490102d41d6803215035a5520204001d0030b0510702040c4803602d1281000c44000e20700c0c8a55034141c075860740340405040e5040c4018404a5820138030100d54101d0702a003425170341c1407146450307490158040c3c80b04941c00403000c03040c0040d244850040301c0140004034019815454001c01080c203400b2482005840c02e80c0b1000450680e40301d40300031081c0352078007032402c6c8102d00c024105a03480c61842c1c01e203c02990b00c1e11000344104215069030f0040f80c036050b5074180b0b01c01007201c4100c0701a00100d11850b0016a03504000c4071080b15403152000500c0c2d120034040c3c032407929104000c100d5030014161819500024200003002d683c3c00d0b0540b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 529379046 1250 529377796 529377811
    0x1050a090603020309070b03010311010207090c02031e0d0203090d08010b12070e010e040608070e0a18080a02011e0506011107080d03110702120c120c060703080415061401020f0114 79
    0x42c0c8076940d070100c5d60700c4e050441d4860704056070000004000c0c00f00c020402c1303400040c00c0e021110926600c07031103802140c035a01c218000580040c82642e044081c848505114800c100c0f04503420076481119010480c3d02c2030b51641919844000b00d06920341c0c0001d039907401008c1041c4500e0820003c125038005a140041102040124000c40e0032410f17802210000100000944100100744d150040305507982060f0007403040f00d806c0b07070340020080503050140d1244000e061001d107141031016941c04029402c554503601c20365480b00b40c45640020000c1328400c903c0c01120700842c541c1442e200140c07014025508040726500301e103e0030f00c40e4010018050641c52010300d000215242c481c2007280307071780c013480000941c0100184d820128103640000d40d0505034608a90060945002c40c0000d582d40e8101c400d116003000d8140400000302e400340c3c40c0c0503402402401c1c81d850103502c041c030307500c00c40340c440e04540152001c04005401d5964100702c80041c0b040300c50003c200e6400c5e00c18030110604c500070041d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 529380296 1250 529379046 529379051
    0x2070b0a09090f091704140418060203060315040b060f040c090611070e010f0e0c07051c0504031406040c0b04051e06090a09090219060f0809011b030e01060501050a090603 75
    0xa000f0701c105902904029800580138030145807020403842c025441072098030103019021120240724a014411035681c1c003080b09400181c03050035036401019400090110307078580580740d4078038036405d603203410b0340e229611035084452140382c0b0f030781008468500240124021440c0c05101d40010350029206410b1300c059085c0850448401d00c505494103a003074100303140041500c8000502e012034450a2001e490751030f44007140a5032040542c0b526402240400b034102c0d4008020200c00106400e0b4403040314160b441e240c1d04e00740d103984035010304000b880d1609440e940554100b00a000da000e8004016020502c449807906183c440011075054502c4100c1110241c1200310070724655911088966880020381840340390b0f03a0380d0803204020100c062013607025050404240848204001c0d0003019201d403601c07921460120b0040403078050800610b810b806658401211250300768500d0094080101070741c2c00714484042c1c0c0704084c20340701d00790f22541c1446401d0201a80c8550091241c2c000d0300c43c00e00c0c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 529381546 1250 529380296 529380311
    0x20c21070b1009021317030a0c12140a021b0a14060d090b10080c0913030e03010e060a0f0f14010b03041a042a0e01140f06130602070b0a0909 62
    0x304000b10803981d0115180500c005070f0311301e0030040210b0b45400c07103030384d14a00b1054007a0984055128030038071520500080c8400640c5000440f800c0301074007204c40ea840c1850440712201012901580306a074054050f030f20403180ca0300311000e00d0716054040c02c030950700ca0303000a00d40201142a1040000072611400d4041401e00381052154002006250000050f41d2039042c0115441007035a103c3c0210b0005000711003504c80c0c41e06080c0b520303501682001301c4032505411070740c8080710356a080701c2005a1654071498042200b41e010072106001d0704000c6400510490007201c404105c03024070111180980c01c0075001411f116200d100b2074111440c100f5459502e0fa9240381c1000102000f40c51540a011010188000d000088004401d100c01d04e0018100007500d44d0080d500450340d5200f2203419a40d1000140464540120045d10341038001c1e045044205900c8d001420075046080311080300ca812400030409203604121b100010000e01341d01d00e203401140e5000900e51007090240b0103085444006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 529382796 1250 529381546 529381561
    0x80d1e1b0c0503070210030b100507080406030c050c01050a0519060b090402030c1608030f07020610030311010f1a031507050924070c060e1e0d0302070e0a020c21070b 73
    0x110b55071309034018000200910703100d0b00178004100c8418441c1c0680700117140e5881c1f0030701034011075a00d20340107000b29090034600381d0200d000d450100b8528041110038001201070700400d01450b0f008004020303000c12246002e01102c030b80302e0301c00d81c03040c0403c50418070100580c041d0b040c00c55040003020760300541c0e00e541e003c91600807803040320091101440607041c040244581b49004e140180400f40000c8030035200c40e50704903900c0d00c1c20303141c50100c5003030b0b1081040000c0c0550048100c06100d4030012540d64102c420000458400200d03540325550017214503016880d01b8041c0d010440d510502c802e41c94105580b0081c01d9024030f0083d01c3c01651003010350300003110341c020306100a040040c509982c480301c51a010405000d284105000716070441c4110506152032050300c003042ca02140103660910130981003001d051802c1c907007038083d401003120104442c004604a24031902418801590340c1d091b281100c0d28080d04080c900e50800720700c04409964405200440d4500b45d041030042d032598030f0b00c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 529384046 1250 529382796 529382803
    0x201180f170705010501090f0605010f11011b0801090c030203040503030c070c030b010816080606030d0c11030303130c0f030c051017071d09010f150507080d1e1b0c05 73
    0x4811200c003040403405000708141500114180d5865507c18844c0c0100181078100303545c5c00340140c501095402403408444da01c03981118403d8500a400841c0580032264500240d007100d00d07504000440d03c40040c40205010b0080c0320300c080c181d2900b1882c52a00e41c540a0300da02029040311001c4c42e00240d01d80500004143c0d0700061074000c142d944e143c1d650740a0311599920300740006104154104000a1000004079087d4410840a0040c0c1041005030380c0803100305203000300c01c03520107282c19002012900c08101442c880e030600c2071400280c44040c00c0c003150241803036105260281c1d10b403105100050301d80b000001215000e4800320210f512140041d5514054130180c000d014490034104098258808219107080c87c085000c45082030070344050080c0c0b00000d00a491483c40880410498088081407500003001c4078600942001100c0e520400143d212200041c042e0740c071192100104010130f00700c00303207138042408100040c01c10000407842262040d808a014444c070207030351105220050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 529385296 1250 529384046 529384073
    0xa0525170301060e03060123030a06090f0c0906080a0206090d060c031b08060f0d02030a05070b1c15031b03020a0b03010e13032f030a1d010201180f 65
    0x1405000814589100c0152107820911603500003603501c1c2440d88560030081142d40c1643c0b2541d848555020f0303000c111801903044041d4007501441820484008079025116403a0454404e40031501c0748a45410810944665500441d2515103008020000c00c540081d074003445940c180c411507142c0510710700090512003992000340000307040407134284540d03906a12414541d807040200c3c03084654542d608580d0200c04503401c90b046524251061121b01d49140c058200520003022590761034006d03510b0505004495120181101000c90b10006243c1240e00401f610803290408100141e403842a01800000d20700c00601284005403000424000c41000c050140d600500480300490341e40343d840d140c40d4024412244c041030031401140c2045100c08507015040e0709541c07066540d5048985034a00704190403100071340d0079500381c0410100541403025080b0407605480d41c407880011120380b200d2003d20301c920141107906d4480340e9800303002c4443e01e170101142c0000310030340343c01d480c2d00c0c1a09100014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 529386546 1250 529385296 529385303
    0x130b13050609071701061215110a0309060c0311030703050a020f0a090503070503011820040c0203030703050105190e0c090414101a07030e0310020c0a0201140a0525 72
    0x4240030090201c100140600444592501c40c011042c4001c01c205d01301d65440c000c0b0b207100e00e182e42d403080c04202840301282c20000302d800d00081a8000e54401200f079408201c0b4000880d45542010007403114070700c81c814401c05103040c14450000d55000713007025888010310340d1080c580e60f2804110f41400c1036050b00c0d100c8003168212641c401d10200c014100b400d5901c64180300f403142c030102003210305040c0a1b03100f1a0311006625103d92070b00703075103503004604c1d2500c074481194801c2c200e4842c965514001d81c0c0f03c4102c1c64018550340c0c18803c1005061b81c030305030802409501300c2400c001014120800b82c1007128840030403504a9240c0406010341486000000c5a1150420000c0300e00103600b00754181c0100040012119080e56034050011100c0d141002103441540602800010a0083c84122030a503c02410341c0c00c4c201450300c03858101e800001c07104100b5803280c0020300031960040c0c8091a9070040303203600c505020034140c00801e140b01c1e01120755510f00d05080040c9041035100c0c55949021352 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 529387796 1250 529386546 529386553
    0x110f07060e120d090b070602220305010c020703050d320c06070c030e04020c03090a1512020306060412030903120305330f0d0609140c0603130b1305 65
    0x56659000703080c103444808951191540829158514000007414a80d0840c240c54009902d0310b070440c1046a5000241c1c16584203401700301c4c0c002d210003c0c88031030b4801410407401418880c1542401801c659a102000081d50b001310001e2010500010300f45030440e01901e80b00f03005c8000c50454907d8102111503c4a0010407004071600400949010303120101003003046500a0f43c0700300086400170190312010713001c629042000495403d007034005226400140c81100c0c500440107001c2111901d40b5071041076240100c140b1155240e03408485c00e048010308503002c3d400c50500c04c0018045200d14402c84407480365000a2608140c080c1e07101b44000c50b00b011090001e40c0c0514009400381c0002c9601004445070b4980401c00c40203440700301c00c4c4007060242c400208040f80740601411403032052015171321611211005000807024040e420305540704110403010461f80d20002880d00190302e00d40c0f481120140208002c0141080f4608031a80c0c000c1040c0015032a0103000703254500210780050901d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 529389046 1250 529387796 529387799
    0x130308031503120a031407080c0a09080d020c01180b09130603081b1204030305071104060f0902040e150315250815060406140f0d020703082d0106110f07 67
    0x1c3c1c001c0301030804480251424001420011145007264100b02c0320301005c1000e8a000c5001c3c816044040c003080d10460034458405621f42d40660318011a2024403401130b40099910445940e000c600b134441000d0500c0000140346c2072001082c500d00626220502034030681c0f40c409061000c64001000035600a00074950341e4400b140100c0e01040b05101d854290701c00d05540107201003104044404403501995400c1c02d049060362514a680188200c040c5c1c0a900c1c2c24010503901c0f020600d02d001000728250044e0b07580c1c50183c441d4684071004084800500a282c000e5a1680700420201501400d609038848180e44620080c0c6510b05003007503a454461881e0020540c460300048802d014525040596003110707007a00402c030381e86c841c03800345400048401d200203160059901c060649004020140c2d403c01001d640c4100c226000100c05a000403076913803c1c0b00c0741602000b00540c248030541002c09e410000d01d040046001418887d000801018140c401c02c19002071200c0958002000700303450206 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 529390296 1250 529389046 529389073
    0x3122d15061b0812013f2a0f050f031507020a08070c05040513030504050d03090e0a02120702160b0a1701150f17040803040201021f090611130308031503 67
    0x31130382402851070031041400010340c25406107000c0100098000c3c1d0400c0041d0b0710031102074500342101d0040796119a42489400886a2014290009195050200003031880c0c0104201c0c029441c0c0d101d10300071a00c41020020a0b140418401c005440150b45599580c84bd0b9508901d031820126001c2d000080104d074500402208200301c100b1101d040300e00340500e440302c564089510548440080c04100d0400003002607090050148600c1402810200741d2260342c1c0308030302a604400c5401c100110b5000820410040e031030390039182c01c40200d00c01808903071400d20340484284024000d240d00b00b40c01040200d90a032062001d4001c1c1c3c0c2780008450f2655039501481c00a0740220344800b00030907214000981d07410710a0005c01515000ca400e140d0b215100c035190009640e00140050741107019031043c0c014214180592500710b8504c2c088002050b06a5040c9042100c220040203000107408001200000d046a03c00c4800d50b600101d41d1a070700d41b42c446c078964150886907205900b602035010481000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 529391546 1250 529390296 529390327
    0xa140c0307150f0b090f090c030307060b0909030f37030e010b0f0901210c030524070206063309130b0307060c03122d15061b08 56
    0xc1c005110b03020f20002200e80684800e071088505484c2d088a1a50000b034090310300c0c0c1d400340350403451600655442e41d400d940480c0c00d41c0d00000040d10940c0e1111580050303070034130386209a231103082880658104503c582ca0112584240d00d1441c0d01142e5001c294002449000a026000720090341c000d00c4400e181c0401502801c801110300313509505c0c108010383e96027014403800b02c50550050a102d6181c0c00c20891900d0343c0d195840e0204001500301c0c0c001c0000b00543c0d1884099030155004054601e01c4041e400054020100f1514400d82484203004115070000f60701504240110f60a950510900000b510241001d818011054040c550455103121a00707008003911182958107050703903011000c58009444030640b0b034a801d80d01152003044054410302500281034130174500045400b5074907034004144c441601520b91144041d012240104848147c5c0300400300c80c403003045c000d413543d00301e101c90103020b684650000d122015040303240343c088180103501d03075550240c80c40d9102c060f0700011045 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 529392796 1250 529391546 529391573
    0xc031b07060e12040b12101205030c10020f030a0b01111606020115030c1a07020901061e1817070e09061f030f02042a0203030a0c030b03030a140c0307 66
    0x4241c020b0f07900e40e0030006000002c54007a00d0000c5416407a0040b107100c404410900100052001c0714031680c0402c40e07018201d908078103036000e00c004544558551440a00702800c5a410851a0384108030145180c591309050329401201c402c40015820070540c0103a94081c4c180f8a01000b50041100000b94000d1400d030031404e444559008003e40600400802c0405909000141410914000801c5001c4040203000c0600403281522401c10015030301041003c103081e00b2280206441c00d0b0f03d1595500110808210b040e507501d03107521149007400185281c481c1074041c00d805e802030341d540c030900308070100304e890000c0010354214a03251500300c11064944405407800e15180161001ca1502134900b102c82c541683c0e0488081d180c003250035400c00c402808140c1c1c104040f0074a00e210001c0d141540303010340003180300b81c0c3c02030340c1e4900d002c45005040f100c0d1401590103140c40d25420001c0d603203000080c0c6015401a00700080c0d0b03916144051100c5024140d11100244000500c03102000116900d464 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 529394046 1250 529392796 529392821
    0x1509150606170f150310140105010e090f0f09010207150b0325061b0b09070302010809010c050f070614130605010b09060901030906060f03060518030406080c031b0706 73
    0x20802c03254070300d0340d440c4800251090351400c4030100108000d10480b005040d428540141150402d1241c5103100040d55107024400f80d0498540b4010086560419200030b2004002c0711501078910302260b00c040404000f60503003103450f030850b0014400290950407101a45c1e00090558502c141c0714000b40c02902c0540e04c80c5000e40500c0c14480104071100310b070a081103030400848203500e41400c004440008408003200901c019100d03000002c07030381085815004400c001c018201082c00c500001d05410b0010304a540b07580e01d004413410800da07001c0143c4003207034000386c41e00b0360f0343c2c045042050280c0743c01c5c03614000e060f8400b4103110b040300c07001c40034084040c0300315401c3c4080d0382da0704041c6030107000c1d08a00c2c2d508034204200c0a0155846036011501940c41181c0004020b929418070850b010160780081303d11550b1241801310f0036038a114110282510813005520b800c0c14604c0085c19108042d0504400341c1700440452944114004200c018000503d0815100e0760f140c100310001d400746c4910366 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 529395296 1250 529394046 529394057
    0xb04080106060f05121e0403030227013509030a0806040b010e13090506012607061b1a04120f110d0c061104090606080106030501030c031509150606 65
    0xe00d250144000904443d07040e1241818441214030340e540302000203207500804040200c20034480004216164000c41c005c2e079005032200304100f1041c20f41c01411200044603191400c0442260381e0103194024414045070700c034407074000708880403c03040c1c0302117200301e1800807a41c041218010001014040744595565000b0141e141c000c10f020440f00c101c0c14203400540c03560008402c500b0040007080400b10701000c00155082c95840da5801c0440a8200c072480c01200e80380700242c20f0b44000102104ca448402030703c5140e1034510060640c40140006110b503120f10b1a049082c0440081d42c05040826084844507034541403400c4108001c940300404003084440100e00b514070722030746150700030104280041100401381c000540725503d80840480e0155218850103450151841c0540000d24102e54041111070803e00b010b0482e0505030005010185040c0c010030114181011310342c02c5a03002000305c01061041461200500304c82a030103882a0407480c0c2c180c210880c2980420f04540786950780 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 529396546 1250 529395296 529395299
    0x21908010e040b0f04030c0507030308150a0e0f1f06030b120102211302120604050f15010303120b041a120102160b06040608070608090709050112060b0f0a0b04080106 73
    0x71006080020780d00907124901c10800192858504010702c2d800070300900780706032451640d55400b1b00c0c0115a800450002c0c00c4002800b03464203005050800c2a2030071100744c2c584a040541e007008045008241048002028000c545100701090700c4400b52104040c0f80c160304e503243c04020300501510303070000d4020000100d028908000600c00d480c10140c0070700030b8045990b4282120700a07980c01500b41c440307119000300744d540140d440100300142c82c08000080c082c10311b060b04146080490340b40030070105812072800c2030720000d1040320b180d06403941824074030716001025110100038489482c907503400a280600c0100c50b4600804001c4003020119841a408080c40341d9141c00c0c1e008540ba0b06000c80e032540325040000d4510400e40e5030145002d4800140c40c2d030743d08842460840264440e8012841000c144510207070700b880382c140a040405000c1c02a9450005001c184401521014207484d075280302c44051503441c3e82d1a1541904014103294045072a20b810f8a05a803183c482c4200ca986800c20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 529397796 1250 529396546 529396559
    0xd091b14010e010906050a0e0111030a030e1b011e02030d1a28060806030a0f21080f01121a090138061b010903030c0215010b0f090102070902190801 65
    0x80d84c806444150351035a092031103113007040d00e110019200310b40c180060400c00585e000390410103448119115680070810120213220141442e81602025210101142c0000302e907903085941312010410450389409844940682241180287c03002502224203005ca0180c44400d203245101003010215290031021141c0c4840151540008004c02d0340110f004100300000c0c0e0085c2ea00c03991204000c1d0a5681103102c13690f0b14112144074207012104c00c007003400a407004132111182c400d428260f900b80102241020181c211281005201d004112a0000405010401010011441d10002c0054009141800c10103a40600340106a4500045a800146039041140310070014a40302038141543c3c94060314060102d41c0c1d2040e420011240c545c8245200002c0091042c200c04a00980c1d0000d1540b9462800034240f0075404003140c0e245100030014040510715408035043e8a22403000e03140e8812510300144e003450010f5008000803071004c500040e0852034800c0540300c500155460150b244e88804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 529399046 1250 529397796 529397807
    0xc1709061006030c0c060e07031a0403020a0b04021c05030a02120405060405011b0510050a0f0e15130506041506060804120503040c09020c070303090603110d091b14010e01 75
    0x2104014004008841081101d02951010403040032a252100d10815a500c6c0e15051700c80164003a070003680002c1c810002d000080c2031152340c84400c201e00814900b040e4038000e69076400c0041c0179041e0f540d400b01040440d650701100c0795102d0040c03071080c818a80305040007500d03600200503040250085245440c00100e200c0112420341d00000c0c101810541800011030712074146a01c980261300e40302c004000032a0303082020020f641600b007000b14003444c08030400700a0301e101d80b030245502410a09130540002c0b01040a941a01c0c12446001c03c2e03540740010b074100d000111303001078080c5c0900740070f120a0107880c001c8440d010014103420301007907507101c200b1151620300700c50180065006011001240d44500015a04070740a03400007850b583c0c0314440002281d000843e148490b901c400070030820580c10207841001807406007410002d0b000c0c0040484040d108170012040040ea940c6109400c02046490300b400c040039440c51101010748440000c4518000400d0950100301903140c1c15000d9031080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 529400296 1250 529399046 529399051
    0x1508071803170c16090e0c1008040b0910110706060503070b0406050703210207110301020f04090518060c0703110303060d080c01110c10050c040f0b0313060c170906 72
    0xb0412402401c0700300100d0466040781c840000340e0702038800180101e03800100c0000240c10448000a03007041000d030094545100881610701420021102441c5a0340149030654840e4100603048181e0b42c030200070509094158138040e81c0c0601d4518034008105849024044441c40748000b04001510748007095541d200074442c44901e01020482441200c0c8a5000307013050600c2800c10102d40100714100f80c901603c0000002e141540c0400c0d5402480080c000001d08804250300840c602103030b141291032a80b045029141c19252208085589000c50f0050310300146030044c00d40761241031142112417254400ca100743c00266a20000e000a03c101004803030050400600c141a80d59250703071104003907040002107103180c0d5603500e1240c40e2800060020310701290000c025000742c04071081107808540000d08402055802400288070072200582c07071809940c0302203a03440e00c0e17a851a9065903040d0301214000d01207418296201c220304d80000000700e20320642541204550780d0541401d91f00c4004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 529401546 1250 529400296 529400303
    0x405060607030513080105040f0614190e0a05030a0309140304080604060e0c0916020d0e18040510021306090e06010c110102151026030306040b0105041508071803 71
    0x10004000083c1c00750008000d2403140000003030149680d500d0b0306003140c0086809940311181c2400001c1080359905c41d144071280180030607441410410345001407101541c14082c0402c0c0c3d038604e56080d9150030440804c415501c04220f90b0345110440d8000c01504440340115a101c16564042c0e10000021041e6010744401c28000e18140d903894503041c0140a44400c0c031401800745038107508403629403000e0140300c0c1e400408621001004210000d00c2c1441040b1044c0030030500b121840d21130780c0c500c1014a006120155204165111420240e013405d02441419081c58030000302240c0d60006204a00125415a256604650343d40e1000040880d01101c000d40000c1c541c2c807042000a00100180121542c1841110034150520079010003228064032501a00352042c0810041c0d03210000c4170042c101100c1e0072250780141003071040340daa0f00000c1c09007441592141500000c40c0d00c64401d0703d0062048458400e0320b040ca40d1070241a01c103055400f00b0004e0301d642e640178801c4621119000c2103a0b1b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 529402796 1250 529401546 529401559
    0x2030c030a0e0d2a14010504050907020c060403060b09010e040312090501111201050405130503040e15040c031b0e2b08031612050f130c15020a060605040506 69
    0x410000700c0d81c03034440c20201540000060100c034003282080d081241c1c2c0151940b0004401030611000c10004d040d02d0303000e02441c140a6100740e20699106e000e0318100e480507180520f03d5202c4c1d08069080c01c003100e595580007140441c0c00014842c09400c41000100c2c16134081c41142d896903800c0c0d80c481000c40707025001c182a8210542030040a5200080b814040da00002c1d04a501d08000c030b01a44c4400300300480341c08000c0052109162a01c50f031900840c045e410b280345002d4994840303440e4000c0784035004061000b6400262031507600c15221140c007030000c004018070079000d040503004114070158035540501804074440500e020b01d0800c410b6540041003030380d20031070060040d8000340c03902c0941d081000300751607d40c000030b100401850017400c40c4140c1350049800d040000301094095030b00c030f03040141004180701a19208920284c0c01041d503e218851b000344c18240104103c0441d40241108200342c1d031070072280e65001c1050f0090710320034a42809495512420441980c0090301c0c1590700c002c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 529404046 1250 529402796 529402807
    0x8240603040f1a0c18040b030c1306050a030605090d020d0207090b0613031202060c0a0c14030918010602160305070e06010c0f1217150906030106030602030c04080d02030c03 76
    0x28000c484500000d44a00c1c211414034810244042090f0003d0300d01c070311400130114500842450325440c3c3c608001040d10200118503a12000a64072130105110074098803881070802000c00da19044513004d000701402400305d9690303e00e0305000070401291000c01ca40150300c00505054808201901b4440180d40148455414481520000d1800c1103145922103400c000d0010000d850329401402180a0803004280311864003019042c91401044552540300c2000103640c040e80150050070210303089610081c1240046800703604e1885101c108940c000d0710030158440c0c0c40da81198190583e00b896090f81d10800c81070010703850400381804020116040303e00c0c00e00081420640d150380c4404140b6000010200396101c03112454800d0030b050b52a03246164400040e80d400000030300f070301040e08080c14454645110001c1000385880900c5210740948408503103140c1d004d4009030055508200110b542c0c2c10003203680e900f81e07401482051814040e0107800d6112078008012748040c20351100c05949000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 529405296 1250 529404046 529404053
    0x210020a050705060a05090916020d080c030f1008030c10110903100c0e100305010609060509030d031121100608010e0f07050d0207030201290d030c0206070b04030824060304 76
    0x68100003002801c100c41401907017210758070032403081c0c02070a0318404224a020740707502c02820300c054034190000344041202401081120f1400312a070200d4005854102a03c0e4520f90c155080c0d40b1381e000c0f005a1001140798110510040741c80e8049514908003007043c131034400c00c074020340c4c080c1220069058000041072954020315030424410801c551400000c0200c0950004c1d841402c15482c0e080000e0b516001844182d8010101130058180d604220f400c240050300009c1c1c3e2192050b1500f010940c07624140100301054400780c0d604040550408480d5000905084080c00001c603900d903100c2e0448000000c0f036500800070f05041e15440a8107204a940310302c1c510b6040440a0403640070407508101d0b0080c014100d02c082e0041c81e10a074000324030700c2580a910000e1240102040401e000090700c00e000715038030103203680a80c070340c03500b0400e01040c65400002c003680203090000c2d04040c00702042104140c6e000d001d4520481890600e61310301ca84030510708106079444900503801001c00c00204020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 529406546 1250 529405296 529405309
    0x1060b070f151d1e2a150a03051003020a18090c1d1e01050907090803030109020408210d09060207060504060516110703080913110904060501142b0603030c0210020a050705 75
    0x44001c0c850517124204090800f18561112607000e4400ca910003249202c0c055605010b9660010104014841c405055400062002e0b20501c00c10745950300041c4880c000601c42c1c3c100280454021466045541d0340b290040c441d689041303a412034801b10703080081e445529103d040041c042110010611507828030082c03007244940541040c05100b07414800180030070703041008502034206a0809a02c651803e60013610300801d54040112805480c0c982e60002411242a92203c0700b086002203082c0c451800c09030001d115050780a081c45003410100014080356420180c0107146070a06c0882c41085c05400b211681c014188141e090b82007960104042400e00d000740c401200c00501101103d02011703080c800319000d02d1480c02c8900f10100c1c21241070f14141c0f2a4a005003070030308000b00c0b144480507050035584070f602014046884905503400c1a9544c0034541c0d088185801e40401c40366440c1d080140400c1c1100714101d108404030140148081d1000c9940030351260310000804100d41020104082e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 529407796 1250 529406546 529406593
    0xf1401090b0a08060907060e100c0b07120f090b0f0c040b03061c050c0a050a031104020f1204061406040b0907030504030e03070e0108070801060b070f151d1e 69
    0x80c404142c882c0851603420500510340548002c50040104078580075016165401e041c0d072080c403e407400f1130008440d0b9000351141500961005894840750b0b03c0c001d091303910455120300100d4003840d0120300c10b801e071116844490310901a0550090b1070303403940280b104d061804c8803460103400d010700080004c6e00040c00a10380100d00101a05070b100148241c0e400b040401403400c2c2d646505c6500518014105468941e01038681594840d15250540d202d96001031240c4031041e005941c0000c10123601c1c410380c800d60769a501c02007043c0c00e0504050911101074040254414071006881e008240c0c58a0148940382040c0000350040c5c901d50303076056054005000c002c200b901403104a0359404d140781d900340080d1010b060f5111f0004403950400418914102050f045a0031a0b03150110a00220609000f950301c915401550040000c5880c81c0c01c036030911440c014158a00c0c04c011865035000316000712805240500c0d002c848581001054810581103029107858058000320074820381031010508030035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 529409046 1250 529407796 529407799
    0x5070b040204060504020c061b13050913060507120c030c0c0305090d050616120b0913140106180c0801032409120c05070602010e030a051803011a0102010f1401090b 72
    0x43e0703d9564404203050f640b110307681400a4120300c00304100b00044003256221903050000e05410100710300c10a81140b402809811311420000c40004c080d010040e4181100c50723404178052000d424103040c0074065640400d106808241031000d005806171003807003082c810600036543e07000c003544a6181a03645502c4001020340081c00407082d0000324004001880c0100c01242c4100482c02942c040100200d517107088941c1ca6504046000119175119411241c1054030b10b5428214043c0703500d001d035040700341001c0000f400d50800c4000a410603441e0001e001c1d00104100a00082c0d040c003504403000720b001d0000809004091611940402000a2045200c003a400001942100545800604030901680e1600013418007140d001048420b2108100a100710f00090041a2071580141c0d240c1c01121201c1080040105d01c1c0c030b0046000b80c03540840804090000c02510144a00070a10f8084c80f41781c060141d800c080e03c3c00104400b900c22580e0201c00241d1424041c0d090080303100c0074109401445 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 529410296 1250 529409046 529409051
    0xf09031b0706120204030c050103181a060f0429031014070e0a0605040b0304060b1207030b0c1c020a05040302030318041103040305070b0403020f0f01150b040605070b040204 76
    0x880a48103400054455048200107201c16460403500500403c006038603110380d0b5005000030000510308400102c1a1102420b0101d5203140e00c001401c0700700c01c0c1d8100540410b01031501815400300300101503002d204251000764550280f0004e0000b5102c9600f0b404554a8001c001000c40320340e141d9191001b860024180c0c4c2103040c01e0214441030318480e0140014070500c00090020b00ca8000e1604200c0d01000e407000c074038481c588000170346180554418403415041c000001000c0011303642c400c503c0c0400c02401111252080d00520741c0d65803150204450400460b00030501502942081d07680311245000c40181d440d50300a1400082c1d00a07010120900c6014800800142c0d000e002428940c4a01d000b07501c848a0000c00300011f13a0394400b04070052100400c00c1c440441d520074100c540d100d8108101042e503403610b03d0200d1512903440540380e0070f801051020780c90108190047d1541c4403034410300d60419a00c072300c1c0c2a2010310a92040c0d0f0007051003049030200241c40700130480d50060004000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 529411546 1250 529410296 529410307
    0x403030506060f18211c170a0506010f030b0a060c0c090c081015050a030b030f070b0c060906010f061d100918050f180c0d06050115020f060f0903 64
    0x200300301c94009181c501205144501d03d0384160030404210700755000c0140c210300420782c65224854458650080300646c1c039032268038103c2c600d40601030303181e0002e8854082000d503103403240200004217401c0e20414000390300c00309035a10183c400e001c0d00f07844090003082e03402d0051511800380c0d40d00c0508101240c810094110002e5620f40c184117640d68401c564907404201e00c0d02c2e407080741070340001c0c0d00103903c1035a1850407298031640c40f0040d12083c0495090004007030020000191401000c5500c50a0602c161000450031003814005004c40303000140440e4240d4440000d450380364202405400d501d05901182002918818441c05130b01c3c6040c108000102d0240f40086070000c030803030190f0f07000b0542a241c1000f8140300f0b241e0501050003030070020040c6080c1540300349045c00019046003184c400c660740c01c150750501070003014042e040041800000d41c1c900e20707000000d000244180e500c40c0d0404540b17850054004511640c02d0000c1c1070150400780c2d00c50305c60907582200505070250700d100500c103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 529412796 1250 529411546 529411567
    0xa120b0603130302010f050a14011a030105090a0f060807061706280815011a0a0e06090a0e040f060e0a03081f0e07080108120703021009060b1909051e040303050606 72
    0x105401201c10705800310305109c03089480b03100d504041e03100354481c45010303600b0762056200d00241c84c150303801150010403030307202d06100ea40038007601d40781e002a55181000010740c0820014220f0211a510745a101303d00c003600c0040148040205d80b50b07508614a40000221280000d07034a18203c5c1d4003120b00030010351030b0f0801e80d11300140708100b4249683c1a40040c09850014000c0c0114032518032003032880c1c60b80302c004c010009100100070030701484010400301c0ca20b64034241c2c0c946c060401258030400c10710301414245d04443d0101c00a030350113440d000c1c24104c0001c003c505540280d802d615100925168003440c03903000b80900100424181c2c140c0804211600707066080ca000f5404d0366103000495050248060804000703001588085100b000017400103900800c0851950703204400c00507112145041c54805031820000710341e4020f40841645036100a480c84003401d884210310100b15641e1a002d000c6092000700c81c00c1080720098400090000e4460b410140d44408040c0400b41440504070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 529414046 1250 529412796 529412801
    0x40602070615080a02130504050d08060a17060103020f04050103080a0c0515090105090706020c010c17160f110a0b091903060f090b0f3306040303050a120b0603130302010f 75
    0x7000243c807038011400c61025483e1190749000c50042c00c0e00200200c0c181562403603a2051000d900c1ca0911000c030f4000341040d5217220b41c5030020400403ca0505600924443c280c88910034003049100d16100240d0384039a00f0a4855607050320b43c844802860320b000600c1c15143d03244203203c00c441910640f189400350032008105580100941704c00400d15050181400e42445190b070800001c540c000020303503440b40e82c07122095600d55009100490010142800d0785070910035080303c881c040e072034a1040320030000c205c520403100c140149103038080c0050200400202180600c10011403900902a83c0e0441c07806042d41220200301e444e0600d03030641d0765568001030b20080c402c081c0781d065844c2e2486050203100c100322540f001040039045400c0c42c002c0720101c4003100285000405001302d50341700581c1200c5000c10184010020525611250382e450010034551003e03600000007054101040b103c00141c2c05402c2e078640c001040c5030b06660300c04601007080760100304190115074842c5801c01c00e01c2d130a032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 529415296 1250 529414046 529414049
    0x3111903150519150b0702040e070303050909070306061e17010905090c010e10030e0a1506180c021e010f14180f06011511030c06010509130b040602070615 68
    0xc010120b01d500d44240462819020f4402c8001e090341000026404a000d80994400b0303030711452079880c1c0300c2245002141c010150460860403522908502001381070300300c1d020b032148140880380c11080d41c0ea1403c0803015505280b10b214049112060898814082c1500008034400d080c5824201031250070100340c030850082c0c1c0302180e965918014401d2120060040c440f03413a4007800c181041c4003c0c2c1020a00d04080c1100d10307020541d0fa2440f0301c415040c20b200b038a40064001240844024280a1400c01442117200302d0b02c803d9401c2241e03041d0a140d4cc0540d4201b414544c000e411244260400c840a170016600c6942441d569160910b010b0000e41c40f400307285440c01850584140303400300c4100d00d01d2104401100050348400c2e01c8603d0380b4000030300c0781d041d24034144051000b07550f02c1100390307001c4440f144c051030030f8080840c591100348400941c0300d0481d142207a00032900c2c0c540b1041c2000605811002600710814400061301250454000b00380340c902c1101c1c006510364501c045403800c9201c0307 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 529416546 1250 529415296 529415333
    0x70501021305040c17011404150305160608010503150703061a07060e0106030c1e03080f030703050c0f0f090307120b04060b15042105010f0c0908060103111903 70
    0xe4500b409181090302c102182c0c40c41c5070400c54020b81d1043c24072140a101441400c0f54a02420000c655030340302c5402912017488008000e800407070300c134900992126030081c107051003180c00b1400010043d12448100b4102d51010b40a0030100355204420048503800510160a03d92109000035000c8215095000c030344c1c03042c80e040c40d00c0c2c5149190110a03070340d030300c1e90b003071989ea052203002c0c0081000031602000301c484000395140600c1c2a4054051406816071002d02111004140b0f0001903031110020b611841d615a0100403550b902c12111050740102002902d80701c1003481000c08403c1c60b040101201d000c000c04590403680c1d1010400400900c280f800c461030240c210501c810010750f4045c0000200b0100e90782020340400a02c0903d02d80910f02c60080780300409246410918400040303c5805a0810024050000840c4001010342420105c000c00220502000aa5490f0105025069135031151000d091a200c0302e0400c04003482c500110281041920b000000155807000b440914408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 529417796 1250 529416546 529416577
    0xf03021501060f030e0d0e010f020c030d030e0d0c200d12031e0203010501020a0f021309200d050a03140c160f0501020c090106120b0d11030c06040e0f06040207050102 73
    0x100482c02815184170324032601a6030300410400e03150783e81100040011202c2840e00035104035580f8000c0340b0708541404100e03050302030402c01031480b6900d500040e080e607101c00101ca1028480d00c0c0221807082e020303030f000350000302e48442e003181c41e0081c2100590340c45030041ca1036660340d856480d1030881c941086002808207544140034240c1c071030581c0d120990300d000c1410450842d850500042c0d200d41541000805110080d00200119070783c030202e0121401c65003d00708051800c61500c07001040b9900380710045040900f092107100d20304042c0d1000d4481e480000b400c030790381c859501590300c50030400501380d1510307050002d5050130308100004502150347d2480030f41900d203000c4500e02c002d4020b400050441d00440d15604c8940c980d0304489044412078a0004102143c00344024010007214840940c0000e000c84000c0a200080c3c8030300a410b40c0071800d880c1c1c1c2c01001000c1181c41e21503486080008011800020b411010740b0380540e510200c05080546410544d42da22400c90344908030381c540100c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 529419046 1250 529417796 529417817
    0x503060a150608010e011217160b0c0708040e060f0d120e01050307021506010219051501090509070603020a0c0827010810090509010204080303010605070618030c0f0302150106 77
    0x408000814000300b842d41405034540d41042d0b4405015101401182410402040c101d000c11059210802e080041c80e10f00580301c0a50140a03204664071007401c0e00c44442210115006480c0d941c1119240740e44165510b1600b0300d401010740211000500055002111400400f52529000e000750780462013482d070402d410131066000f17090000c00c002c219040103001c1c0108070f19250005440d0840e24000e42049c2104d0b900c00004070b04d00b19850300580400388000c010203003000000600c0c09008050307545e20001603030700c8441c090111002100c1c440e04550020a040154074043c2c1e001700803506a920302400c00c02c0b51501c0da0907003948a6002c60310021849000e0109096150380c08070700710042440d1100782828081c008019125007809800c0300140d940700420040102541154001c040c0c0304142ca450350307034904002e0200d820402c410740b1140d0501c8241240740a00811b42500d8641c140c54143e00d40320151540e41000b980900d00720b0540c4940c02c80b1022241e10690450f0081815540e800d40d481c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 529420296 1250 529419046 529419071
    0x30203070e0a060e070e12010e030d0c080a0509150405070e0f15090903180a12060c02100207050d0f12090c052b02010804020d0c080706110307121202040503060a 71
    0x110f80036071020800301e10f03034030a02102c113a102c1d00490002000b1961800191309031802c603401042c02e94100d0000703100010b0b0840200c50140c1117071030301840d50346905441350395070480c40703081c1c070780803036050055030031510148285205443d901504180900210b400581e25004015401d0718180d43c1c0004448140c01005030442146a190f0070381002034a11425606289a110340d4070301901c0c800050541440340070050984921b80b000004040c19600b220002507075082072002030202c01d90200043c000d48000d004800d4003402203585590f4000c1c01094044403202044960806a0404900300080407041e000049001c0c0282c0d040b941c058a1003035151444c00d010040c81140d00303940030781240e89841d08804141050203404580340e40a013405589907030707240300284000142d200014007a03c036490740424070ba0b400048800698220b521550403001c160462076640307005055009001c0d43c031288142c40003521401000071651f250744000b5050a44400c0001c0c02c1201c200c4060840c0f0b0340d640c420007842e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 529421546 1250 529420296 529420301
    0x50d0f1e090f080309150903031c05040302010e0616030b040906090b091e0309100507020a030b151e120c060a031415030d030b1c050c0909070503071e030203070e0a 72
    0x604031400110f143c204004081041c0c07451b0000303914002d42e804100460399440034012103076000c00c02c058045040d003503024050014001a0390582c0150310300030b44d00c0c0c1805030000304140600705c3c10f04c101c070040e9080c920031006001d00040f01034100d82c507003403014002641170180c088128428140c803151460310406062501c84c080e0301c41c110018156201654190010088a51000c002da4944003410b5401d10252124450034400a402040500000040c00140d0840500a020001100c103041d034000080140c101c03200aa00002d45405080b00300103850b00054902c00000208156041c6840640c00256a0f800080864001c2030311104102908803c440b05a540160f03094082082c0180010103e99908003010000d02855510b049070505a540d401c01c54510070154101140c00800790300d0496100d110521896001e00c981d03402040e40350030302180070707010390310050024010103240c415034881e190315000d044c0d0701c00c040c100404005600c0510417000940804070b24150b00f4103107041100704 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 529422796 1250 529421546 529421549
    0x140120120f1e0a0906050708040e01170105070206040210210203071d12070e0c1312060c08060306270726011404020f040b130509070501020703050d0f1e090f 69
    0x2c010408001c00180160404500070980301103180564850380c0c40e28003100c841c8155042008121200d41c000504d000b851096442c2c0040600003d0160b9120100244d03500c85013076034001d5200300c0082c1480000351003000300000c825112031401c10b4600842101c0700480c0c0c010ba9080707000811a13002015a10410b11700000424070984010250989041810303442c0c24050044500004c00c400220b101d15008400b81c46101c0a1204403103000b41e0384207240c6d844559040f8040350650b0501070140d45031030040b01021701c100809005040a50381301144102c0c50340b007405901c00c89900900d10540001410444c40d0054010100003210301100008030917040c0301801c021007042c0c0e0400c0c0584e03128828240e08590840d80c183e40145d0031001c440001409001ca4458054100c0c040c0c901035941000103800c01401010104180d82d201501c450049850f41404d00004d80075a00000180c100c19104090308030600380300d0f240c20890380c80740d40b199000040364220300d03000148500c01c0c05d00580344490341950 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 529424046 1250 529422796 529422847
    0x60507030b101b06051915050f04050f06041d0105180f030304030516030c0f1101030f060602071505070506010e010306110913090302030d1d0601140120120f 69
    0x400340301d0851240c0f000144a0080181080d441e04080750783c0041500d4164801540e9006c2800403121540001041d90441d2003181c2c030a5030150720407005400d1900c28180588200301d000750351541d0700400d00c005401460300039054010046041443c0301400c0c03281705e001d00d5150303041c1c1d0100051012541d25082403921f00354a01c0e0000c10600000a41081c2141d41c6a2a46140700a001c3c82c142002e5961179280c01015148202410401c400c21082c10034400f82c8a0302600c0030002062a5400c3d5402c8034020300540026a00910092285c1d140b102c40700c04880131103151261404499948050400d1020b91000d008001d00800502c10400a0700070b5058400e84511040d0174000c00307000150300c1702050100c540b01244e0310070300030080c54805c0c0f086450078101c0b98805d100014601422090798146059418028000e0000104281a00300c540f0203500105a58483c0380d0a03050401a8402d4030018016a0b18840ea00510320110889806020f01c00d00410440f0344412851340c6583c00c0340807012604 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 529425296 1250 529424046 529424057
    0x90c0f190f1406090105040e04020f0a030305030f0c0901170a09050313230a0b0c1c0507020103060e070c08030c0c0d11010c0f021e2b180f0e13060507030b10 69
    0x4c589603644201514111244510603800da5200d80c0040342c03480c0351145031181c02888030301c008410300d504503006502a00c1046400045035070395203101d008500581168a00280c8100036184041040900c0d2a40203202c00f80c0c0050031308425601d25103594020380c104c88070800013810400a20034468520b150710280502d80d4240100008005884881030b4000d4403a6414046084101d80804000c2e100e9003614408074001c03072510200c2c001c0c00e19080740d442203001904090011034520359140c2c509000b404140c94140040440c2ea43d4480190401040340c641448203101e00c02c0c08040401aa104080143c1c454030144e04011a80c41d09441c415001da03030901194000820340e5a5000525041514589d00c411501c00c40c000c000508000c2a21802c00000d40001006499007002013024021a0143d8482c000c0005444c3c100071940300c9984519071650400c21400c2003041d4004501c103070b011030180701c07041000580d5a200030480710140e4a400010f0391ba02642c030f6060074032914044242180d402c20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 529426546 1250 529425296 529425307
    0x7030204080d081f08012705031b0a050d030c03050609092a03011b0f080f070c1a1e0108121b010b030a1a060405090c0f190f1406 57
    0x207554404180044007002500c00c0001e0404100d065103504540f80082403545440d540d1700d00da400ba0089120000000050300c4080744207107180c064180d00e85911001860031300035040802c40704e00d25000b106042a0280d0000040099001d005002c09400c040c4c03000202c0107030842c001000c4802c020401c5010340c46441c1409503401d0001a402010010181d556042c7c104400c0041e4020242c25103094041d030810341602910a11707100c0c1416107100075540d4130102040c0310740c1190410810340c3c9034803000c401c4d0070115440c3c03803041158030b511354094800c9101c02c2920880401d00000c0c211940e0356400b403940404030710701d00c12200050041074050020907203607d40901d6000b0074400c418188000c4543e849906514040c02e40080f1680c806c0101038844540c03040c1004200c503d190f4620a258464010020b500c40c90f05100385030050425400510b010442e0384180f242c3c03180c10003174599108000c9005944110300701e0940764044c01c403100c1442d84980c41e0010402c0118000b41e6502d2048500380030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 529427796 1250 529426546 529426559
    0x1020c01050a060e1b130b04170613110105070b01060302090312030106050f2a03220605121e1302090105090705121b030a0207120e090c0c0c0409050a020907030204 72
    0x2e40364001900c1c4400001007103241601c06050302c52490080c0c06e08401050000e031140741346000c2d02c200c80d10740e61918905949001801d4441c07400320740a00054211209280124814126642d0300c0941810400d14142403500ca054605070244e00500c0001e800003460036150509000001d5582c8070195130f9800c40d410a040a05a80982d03c8460483d91303021030312402c2c00a01c1e41c0703240901582134400140038114000314549962100b00000380022a80307684c00070402011129070200c2e4503540c1c0312030500d00b0200300e246000401605000b03140031860300c5081805810b8807500d0060038a0b803561002c45d000384c410312840d04c1050340074070302c1035900d04204009613030405c00300d59404028040c4c0400c1903554081d0188110b92166469025010100410880c00002d90080c54058003481d001d410020900c101182c03174148624100da00304095901040c1913050090180c02181d42d4030041c2c48020564001180840b0002c000a444941c4001100f0095080080020f90001c44074501503142504219 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 529429046 1250 529427796 529427819
    0x1060e1e0d08091005031803040b070201050901120e06060301060e0108070311180c0d140421030b12100501080a1e0309090f0f050604140414120a0201020c01050a06 72
    0x9024040c18080440340200700d9541c0842d075200e5401407601101a00f413502c001c0081d0802c561480080c015100c0e051940e070781c00000c0e50b0131100252034840c0f4100140d80110382681001503114140702d5607422100b0000030b58002c0020b00c016020040995142c108105429600720364051624a01d4060051003c0c441c045090b10035aa003143c0206d854000c25000f080c2495648400c00074251304803070511072030f01c6401000703100400b88201e0600601c010b0501c000300d0428140e4009200340c241c10000c560110551141c101c04e0010703400e00040615524020806882905411840d02d4104580d156004600c3d4441e0780c2c09041000010041000580e9908070708480c4d07501c8880a10501c03301b074404042c4200078100140485101c00c1c0078624001515002505109070300a41417800c1c54006041ca0030075110b240141071810480300c140e6190751301c41c01074200301d500080c545405119100990500090000c0c8062120f542c0016900c40100c4c420b1401c555004d403100c02d4035420180d04011215002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 529430296 1250 529429046 529429099
    0xc0a060b060717030702151f05090f04030809010605041a18070507171e0703030605100c170702150c0118020a0b030a0902030d0c0204150b0a05030703090507090501060e 74
    0x151610303942c2c1d11200020b900d000e000034407248003003816004108d00304507500b1807141940400740c4d070341001c16102e00400488580031a40e40030521929400034010a11404400d0741204c0c0c11720001030029240c10105054170b00044080381c11010316000284107003040c0440c01d5003060180340440640c01c0244006107070340710395003014206000714800032226101c02c1085920b60100e515109002224200160a841e0803e102c1a008240707400070004140c100460749402c4800c0c2c0c2e03510b04103181e0709566940d4080c5203000141c0f8002c0750500c10000141c45515040c1c60b11101402002d8803041c3d52840c05080d600720b8106c8041c0c64121402510040c1c560417081c0066503c0c0010703054072692214903480043c40c40308000380d031502c105038407842000d80203c0b245000b58001d0310140328070540d00500c00c09045052090020040302002980c161502c100041c40d008500c0346070205049040741c40380c4d854044a074000c43d0259654038010400f458001c020b5001005041e42c001c003582c86000c01c40501c400c080c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 529431546 1250 529430296 529430333
    0x30c03061509040603030905120f0d1101140109020405090a0902100e010e0a030b220f080906040b19262e03051006081204050409030c0501020c0a060b0607 68
    0x1465540a929030798002074840b05000608100151940da0800401500c510b114060054500c032132040a11040415105103040d0071b04010400320304260000c8566203070704c03503082e0040d550f65044031242c0150141094001c5c00c4951015840e141041c040080304440030b42540085881c1c4000840182c88407a40454401c0181c00c080700c1c03400d08080140d40d07000c5102c003540d0740b10640c00808400c00c80d04110380d601407404943c2009136a80e2800450f181c40480720700141032038038854407000004d041e05c0000c0201c0100070f800c00341400d6580b442c054540d0068030f6500803844129613810307543c2d540800c6070310541c26403c1046042002d81b01090100100180c010380d08404042080038079100801c0c80032503560810722030002d0b503d42d43d00b0003d0721364440741e803038100a034245080020714031800114010340280140080e850103103407104000c000c02200c0003c609110398a95080041402031010780403100720743c4c0241810340307130030b1030300d5400c850200c001c16204010030701080000c01c50781500c00410b14171 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 529432796 1250 529431546 529431559
    0x313060302090f03030705060a06120305030c130b0307050717030421111f0506030c010f08060d020402040b090102150c0a03020306030f01060f1a04150f0e090c091302030c0306 77
    0x4140442c0342c066642030f42c40d4151100080031030400a00144d200d120707034014441040344030344490541c00c04900c10503003d40050300074008521104030040090070a000c600b030500c070119589030540c1c0c140740c0045480002155002c5240b0f81445a041407031303104a110300c0c0b20140356103010b40e160f540b1900c00030f509000d040948290780b4a91800b88950041212070b180c101e40003034400940181c1000c01941d4454015410540454076600b0001004220701405071122701448545200440718404000c2030700b036000e0304a407a0b0345c2c0562078030f1008002a000c06509035a940c0e43c05c10002e03142c900a42400885080440d0421110311034641c142c1d540b600a41c94050b0f941d45910b00080d141005091185c0500c0d46404000600b2821007103440b0304480d211041020500c4404450b0f0025008611414041c00c49081201c08140e100783c0003042500341504150380e242d080380e000300c0c400b030703d04980000b4010360000c0c603100546000e0480d0b54184002d00000d618504e0a101d080040303000150410b400341b423 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 529434046 1250 529432796 529432807
    0xf12020112064109040f330b09010e071b08030103080c0c101416140304030c271e0507080106020c030c060409110d140708071b0809030724110313060302 67
    0x947c00d03641811404032444800e20301c880380c10030f02ea40e10a492101b11400fa01d0302d00030000c18200040a0350498441041d0100c040d61144020740e007110051090030300b0000313690104070004445401030342c0698056540310340c0b6002c4411145141c1000ca14071749200303001803c407a4101c10b900107500138200200c0450b10f43c450170140a203540032281f003540108130328414582158070f80c070b0004c00340045a0182c680711320480c0d47c0752140300d42180c0025512a03030040c0e007000f0207000d050940000c1c0e0340407802012024042092840507088803c20b0390b00100003007210004000c220340c104120020000103c01905140c80b41e40001103040c40342d8070405060644500d0410100e0361814256501e1605800090020304c0c0064030280e2440000c40e03031000802c003140c0c042610188150b90403669664103846e020823440b21612407a071b494010003503040d03040c40b82241c045400b0984040101041a201070044100840d207540900000c0c0e034002094040d42c800c1c814121104811444041101c04909005a840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 529435296 1250 529434046 529434053
    0xa080a0f1a040c03140313090b0f06180603060f041b020c0102070b1209120d0509070906080303070c080d09060e06010509190c050f0304030210060f12020112064109040f 74
    0x14000e400c9000c00502030031500181c0750356070382c2000300481c9c81101c00c02c014802c02400c000d064040c0d40c0c080080c1d42c009050308061420204000c40e00054020481c800e810300050008041d90803000c1c0310031203805543c0e807040301141c0411010441c05000d00182030006d0801015000b140111400361300e141c0c1000c80030950908042c0170008500c0c450070880380c0c1d100000d4440743c0150405550140303861040b01e1000908282030321404003920b014202444c40e603110700d10121a090000107064503010f400f0451a03000c028140f05242003503103d004045890000018441e0410a0580c000c902481d1404100498001403414640b02c40d0400580004c00030308802d4221034900a0400c2d074409848000144001c1c540c0000d202a480c0106240503c14140c4500ca0b2041d40301d0140b1034500070414011500005602812440400061640e00000c0c09561807078210a000320003000f0841600509049843c00d00441d4856905885016001300074810b504003c10703160361009201602107034007144000c080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 529436546 1250 529435296 529435303
    0x10501091a220305070305070803040501120c02120414090a0203070c0311070305011d010b030724050c0105040305040e10030507060e06190302040f140604050105090a080a0f1a040c0314 81
    0x150381c16000b540c0a0b0342d200d01e01140c2d00c0d0743e03034003098820b0701c00c00c0b4000501d01e900204940540c0c0c01a500c0e814015980c81581015017010f8080100390301600007040350500000c0040d200801c12480d0200b0341e6030b407203030038003168010142c411001140100304000c00e50f80c0060705e81e00b42c0790781460710704083c40d04c031400b05007005046d8000500d01c1d400c100d14052071408109040e50a8248580200011130480042603950f011920500d04202961018410080070030300c02c9055001050501a2038114441c02c3d00e800c4a4044408802086003c80c050000340c401101844d4000c0700e510880c41100d04640707079165115128405c50b010000e50b0602c0c6022502c0701c40550304105000c4101075490500d0500280194010b8025005440001c3d20005000b54212808801703004018050a103028140703001102e05903c16045690001f190b0140041d1000c810008441014001c0750500a0b0064502d8010581d08016044942004445c020710012400240400003140d81c40304c1501010410503043c0b505 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 529437796 1250 529436546 529436587
    0x51902012c0a06050a0212010602061b030604060902040b030a1d150a020c0a0308040b060114030a020a09120c091802061603020709062c070503190f110d05010501091a 73
    0xc1e450500f01800314949140c0c000d454180c1c594800301f1010b03a02c5203c1265100780c11a03520f9546080c41c00da05142031400401107401110141011950680343e901e1007050741d002d5071096140110000410031000c910b880f0b0228101c401e810849500c0d89280e140e15992102d0019441041203944007140080800e07904840c013030851002a03441c104401d09001d803684c4411102502c05400c000c00040c3c00c0e610450b2803140d1605d590044900b10741316080c01b10000d410901451042c0b04038030802044031191000c00c02100780c0f0911118551504000c003160a40d4002070001100428041180006136100d205440d09a05040c400750131f003403540e0404a2802103103600c55042d1610740391000c911190198a0b040340300c20440f200c1446026030010140d9030303120844007840015400e0003c51000b91002d0000b400c1050400d03c08950304040142010450300c2203c440030b41c0c0a8005010110700c0303000e01881e401410309003008400c451802c0d10641c003201d502081c0005200303000848002003031f40c0442141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 529439046 1250 529437796 529437803
    0x190b1e0402160501090b22170d1118030a08041202130203010906030201020c030a020a03150905010f06140409050c0112090b070521060a0e07051207051902012c0a 71
    0x5038010342801c003d0700800d50f4580035150700007100000350042d0010340080c0380100b160499440b0302c00320b0b6150103020410403074500240000402258a1600c07550188064030902d00079903640d41e595070000301f442d01d0a0031a0403400307034018003d114086410102514110b034045088528010124400221046d90455582550b5480400041007050403603100b5000e6900c03e8080b59030003da0201015030310204480000d6201000100c1440000ca480e000403410145640c400300d6a14104d80c0c0d510300b500c541d000100280c0356600e8042152080c8000329954500e02981c0801c80001c003911020340f60403400307070014140b0400b60124541c2a480340e1042d000590800d0600b0803500300f01c84020540d5000070700e280490f40341c800c0900390316070780701c22001c0c0503400c014460f030502890300c002c40c0c489110042241062240034021089115408056103125a2055076001d40d40c04080c800220f409507807010350021a80f41094a0442003e1a01928411600103140d140c50240d0f05090b40e16003486408004c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 529440296 1250 529439046 529439077
    0xa02070210080a0b0d0b06060918040f02010f1112160510060504050603030c030702101704030c02150901021f15060305042102151f080303190b1e0402 66
    0x41c00310aa200c10603e020b0410030a0901c400344910040180c502c0720722001819184128021030000d180040007880c2451000e001c4400100d081410070300c44c000100e0381501c84c000b44400980466900c06104a8005041d052110240364070403003240d03071080c140c644181c150314000380b510250034441c48005000ca46c000111920060240300c42409041d2030300c5458051030400000c0b07800741c9000301c00d40e01100803000007541070260540800c1140303007020304d104081c00104480c4464514502d40f14506c918080e40f120481c40d00c0311701c14400c100810041007041c502080c02b040000b0b030381c041001070500d4102c01002c2100c40700401111300606c0101324403e9a0824603000007002501038114620035802018003900402e0410100300337141f19500c0c00c00c8016000441c0c1015080401812650410307445808070383c02d0081a0699a041d4190340c00c10491a171000c0100000b99282070807011800c8903a810900c20381c0035940104440000d04c45000011032400c00422825071110b50540d5030758100715003013 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 529441546 1250 529440296 529440319
    0xf04031103060901060506220e01060e011e14070221060709060203031b03090705030d1107050a060c0209040519080913111606110c1510050112050a020702 68
    0x44400080c0d5280c40c0d50080c010b0900082007014188241d0f802c403000681130515042e86c52104100321a10b803161441c449403488004180400003081d80da0186c034a035154200c80c1017940b000580710400a214481b40b00040425800d040c40e40002e5001100003040c1c1900e845000c28030001e03110007400461502e000554400410800c81c000807154019121500d8600700d00d902e400b8220784a100844e803060303c007507039410b0301a805000741c4000c0d6031000d90941510f07100e03030b16240000c1c203205007071120701d000800d40c940c2002c440c0018810b1a0040c00f0460f0280c0103e072811101501c03161446a001e8412520710b030000c1d0600100340724400407603a4038a0140125107041c60207440b030350061030744103011301c1718451144030b00d0304544155a040e642540f00346081c80d491a011000d200c0c00c0e40d0013215007980300e094464654000130040d250724040752000c0c00ca042600f0900c440d01410080c461654406440000c0001d41d8110480c200420500c02c00440c9544e6004200800ba200301c400094201c80030300c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 529442796 1250 529441546 529441553
    0xf0f040e010e100510120b060906040e01060303020106050118030c060e01110f030316080712021e040905040629010302091f110601080a0203030d0905071a030f010e1510050f0403 78
    0x100d4851000300d0b101c2c074403d40e2034007041d21006d03c110100804410562000c03803420b00d0130b86111940b140740103101180c1842d02d01d2001c0c0c2503400c0795100711302603910b42c1c2c0c0c20301c500d61b00416610072030341074405007a2241d465511580c0402405104010501c06142d48645607030344592040b0885070b501a08586a0200c5008403039600d40c01110200c071880d5407061820000d03440b0391102400340650355030351a01900443d2140340298403680a00c402040050342000000e903058010344010601c190000072140b80c942062000d5a600100c002c11a6520b940c6250389001c8403890070790342d14401e282c01a220004e10000c540080c195081d240d0082d03600b81207221700c2c1035100700d03001880b894810507211941d9032611941d607a95150351000398590402e104a032040722140d406407010302d0041c0201c40c40c150351405214010303080c1d0000c20744ea2110000410490344000a0014010520f490841c0440d1a164154801c01803003c0714140c8a00c080014240c4918403c506880e1520b005000303e41d07031165a0314 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 529444046 1250 529442796 529442801
    0x23030f03071409030a0b191503020f090105030a030302070203120304060e010b09160c11060c07031707020112090c030b0a0b12070317030c130e0402010305060f0f040e010e10 76
    0x15002400682c04606002001c0b1820090340c88140000e0002e001c1c0142035540e8070311400c0001c01041e824240305100642400440c0204030009411001009003d0701f1030041c841c0e07410407891080d0040c0c2180c1c0041207591400140b1782440c98040c80e0068070fa56580c8000381c10301035440d610702d10118000c418001481341c00d40c00204001c0c0628002c0042600c40c80511840000c12205a00c0c15010014165603d500900c040c418440c801e200c60440044240e00040154011181e126560341c40840e0a100700250305d180d20108064040c80c980c200600c030b5000a0a401454a0901d442c5031a101603504000e00d424000700519400851183c0515060651400400a403088d43e80b1480e0340d01f02110010300c021510030143ea0300200d40c0009110351520080595001130704104e0010402c1240264401440181d840607180a030713100700e440e08142c000103003030314030103821349114034a045a58500369071615100300001030103450100e2665401e580d42f9005022840b41c40d60207000d910342507100040280d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 529445296 1250 529444046 529444051
    0x120906060626040206180409120503160216121b0303030f2f03040309030f0804181b27030b010603050c21040f050313052b23030f03 58
    0x65100c08031050306541a251849803e990103500035030100020698101040d003c00c80c841d030003030008201072145584030b000036410003502800052010044c0700d0031203249250607106503103a100402c0700d0030f5040c4103030100c1b40c9648074030081e241c0124601c00805c80c0c00c6007605100b0211052000f2081c3c0c0c0d0342800303005041d070102000112468132403560f805581c6140c07050419241c400c0301619480303074000e04e0402c0780cac001b50042d0140302c0c1c662000000100004050855548250502a1160300d0070600c1d601405000303002091441c1031000c215030364440485805000085854800000c002c91016086c0b490905103204d40b4540c1c00400110601c0308030002c85049030295941049140e540246102c4240603c180001c0d4005000031100303402c010744100c0c1c982050190032040c12048003903494030f26581c4842454801c0e500f00090030000791030050001180d03410794004407038055040302e00050501c182aa0f0051590210300c882004608201d41c40801542d140c1003280c2d600e040d011100d64594008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 529446546 1250 529445296 529445327
    0x172a070302030d05040e04020918060a0b0a0f05010c150b030307051509010504150507020c042c070627091e0501050402120103110d0b010f080609120a1209060606 71
    0x319801012044c1c4200308603002c03500a50050702081d1202d6080102456005d003a9040c8030142c121501251001070080300d0040c0038041001950b0500d010911160782c40c1742c0d1013440c640e4007640c020001d43c0d8002c0c42a0b107806521403400404031922580c0c1100409420034044c0d058031020400c003040003c0041c0600e9400e0380841007401d2585d074064001d00b40c403802c46005081c101e070b694814860414507040341c3d80011490040c2c1d49020545000300d011191910800039548211540d101e03d84803400c880d103149170040340c0113010820304000f07026100e180790342c1c001021a006000080300840600502d64040c00400206102100e034502402c00e228402c0303101e8024180c83d080000409280034030840d201c03002020b54120240c0e186864002424003e141620b400c90b40c262040000180c681445a01820a4031407000007103041000f01032502d107000707100c00020340c4101800e11482c140034081c1da15448941c6094041ea00030096510040d12101c040240300500b0400083b030959000848080307140312 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 529447796 1250 529446546 529446553
    0x31e13020111190f030e151b010b2805090703020a08070801031a0702150a0c020705061c2703030c0311091e04090f11030613172a07030203 61
    0x320700c04899214180b007041d890f80c84180005100024861240885095010341041640386071840c01150f81e2030720703940b20a0044038001a506140c1c0b0440c881040880c1c1000d0b0082060f6400b0001003004103003682c0f15108030044075400d50100e00c0044201c0d0000d41006001c2070280d0800c42000f0340650040d41300d05000c02c0102e0300140d01d05204035121812030750807601d46241c00da48140c0c0d07071074034210141030641103010300d4054484620030380c89072a0140e0307004000050b0033b84819a000342418020307080684118400c0112030500170200d03600c0004041c0450002800c01c400c1300500d1140341c182030f1600c40309003140041c0814141c0540c401e250b040d04946061180d0842841c070301c1e90a00c0364111403580500075045134100c410380709098400411000d07000040d2141c1d07039146d45000560454080310144040120b1207043d06080c0081d82e08107070484110003e1007a15541ea4140c20701420010311030360f40114001c070b80c3d01114549a0041a1101842c440d409200031089403039251b6070005070f00910 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 529449046 1250 529447796 529447817
    0x20d02070b061207030b18010c02070f0b0f030a05092b02150903071214040e0402030d0c050304120f140606030f060106020d081f30080708031e130201 66
    0x5000103690340c3c1d0401c0c4006881c0c25425a514006862005011400251076101c40441000380920547d038a0600a130002e0981d40d19103550761501c07086581040c00065024042482c0f20120141a690412010035011885a0b80c2918043c0743c60204d1401e00b4140703201441484c90740e02d600e0407450340c1101c55070980311f0083c030030901c201014006641504c1c442c3d00402150000c240341080e0b600c0038045510f05100644817501e0001c240b03801079008500e5007440182803108525040103401e020019500340006a2001501c27490744034010391240424108101511b01c0801c0640c00781d20441e158041001324041003410a19941c0d01c5007128400d00901c2074080403d1032600008046040b100c25600800c8100740007541161603850160103060300c0c2103004d880314840120032407520080d2401801003100c048422160301c804800780c11481628400051039100400c5840f400c84000035040a03249a80e1b850f03901400c195401d02a012103450704100c420700050342400c1d40b075032300200c2c001d03079900d18610b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 529450296 1250 529449046 529449049
    0x6120b0108010321030e030a090602150103110111031e03010320100e060f0a05091903050712030c0f140d0203131a13260c0907031e020d02070b06 64
    0x1403c1c0800b500e42407a11034044000190312000040110442c41c000c160010201c1e602840c640201107404045010100b00f4440c0950410041c02c10040c086029000b65146494000240307140c100c200e410024203200d02d90b4002001c00449451003203841c034031451464560b40d40000e80e0402e0100701c4019210309505807040c40ca601161404800040a0307445850320f8240c00e8075401c00368030b036642e000f01e41408500d07611161100070342111031150729803030340d03448a1104015072101c544c106401d0b60308400809002107130300054100e064030100c1a084507005160b00b400d44144040c11001414480d60b017803d64100082e008500d046042d5960488030005040e01080c1e03102d026007409800c81c1c010001080001c07200b02551a01074a540c1d41415190480038400d1122051940d04441c241c19504039490995580029000c251583d4000151440082540001d004948050b0540003010340391a40d500783c1c42c5d09403d50080540c462102103550390400441c00029400c80711060b81c21a94410008405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 529451546 1250 529450296 529450307
    0x30305070c2004060902030406051006090e1f0503031903290904060b030607020607090504060b090d02040b031b09010b030907030615031211100b0d0609020301090c06120b01 76
    0x4190301c226000c209102a01d80100600340b00805a54450344880c00003562032131320300c004d40c0541e00494010859282c8440c4035402d078800c50707101e8001c120a402c01000342405026100d500500c03007948002c1d10b103101d400c031140040c1c81d5401c40c541c14000020200301000c00905100c80d910f000c2d48040c0900c45140d21000c00c40c4403084404205514022180003003480c141204a80c840c0c4101301c001480941000881e25101c3c0450304003025a00540070f201440750000d00304070061070b003140d0500100d404d00443c601c2d130f0700540007064001c070801085e040855030b940e0045070150b000501220342003203190742240c0150071881c807000c4c01605580c001150703120fa0350049a00c10081d40005110700c900c3d65448900078040c0c1d11140143d0030501001100007203401215009490a03541c44900c4040211200350400142841030000d540c5084140328690300c4140840f42656040700300040d01c6001c60010901501c003c280080c6416403145000c58165001481c0403001c01107100708106400010006542 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 529452796 1250 529451546 529451567
    0x19110a081504181b0e040506040c05220903121a040b12060103080f04031a0901050f04021507020d050105010608091209030303010306052206321b0c060c0703030507 72
    0x40e8080d0035000c4030106009503201c824683d2540c1c01d94041c5a65504a00405c0d4000e0700c5c04c40c0c00b078004100780024801030545103000740004445158800740d0761100040900e40c2024103098141d00c802d20581803500501700d01504510b418030a00c15070401040d42d10404c441d1a048520a40c40c0544401107403d11081102031102c950004090990964840003481c0d000240310400d401010400800041d20052811a0141c0340003141045402d01514039400e48500400820b00c241c24001000090303510454aa90072169040d681a9112094000304041d01c0404070040c01d80d41c00d200001889640c0109018850b0901206507066100010700d9600944508909680c0c1648180012702c041607150703100300d401459400b084425410b46143c079110500340288180e40a0b9910921081e203a18001994801c0c0c02c20202080701d055600b0015414600000c1c14104942d04070480c5040c004904408807002d00700e4407800c440142ca0410324490742a8003881003280068281408942a03500480d130088 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 529454046 1250 529452796 529452821
    0x90d021207020a0b030606070c0e04020405070e0f0f060d0203011502071d19180b010504110a09091508190201031b0804030c031b0b180601060819110a081504 69
    0x2101c0c2440c0c80351305075050300003a0800d640108204218000185200f0b2524024006001d840b41d191600b40100400c1712002070604060210740f84a110041d5982001405131410443c2d00500d00c0c5200408221103000e5a1aa0320b80315100200200e6084098420010011080d134216030420303444040104520030607d000c041c90301e01ea800402c040011502c0c64110f000c00704030b4005865a842030b6849050700101c2401da56a0f00d0250052244e41401e000742419031a0b1013083d6850310881d8900148800c0444c410702e2403581d592000454110b10344c01030070005054a4080711a4507890084090114003451401c030b0101e4030740300c40840080c09400b60900c18207420340320300d1403030f56960705c0c282c2da0b0b00301204080782040803c0c4c0040f40d03001c400003034901c08680204802d20302d03441d02d60a06101c484009809805075480100100050f40d80260007581c420960181c2080d512006010750340503220bd0301da48aa000d8022405884950b440b001d50b034490070545a2010315062500c0a11040b52aa0301064 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 529455296 1250 529454046 529454059
    0x180d23100606020a03020d230f0a03060b090f040203060f2e020c0109050f0a0306051f0e010f1a090907030e010f1401051512070203130914131109090d02120702 70
    0x447c45a40039091480200544c1114120384902c40400a50160b00c868004000710303c0c0490140c20f0280d251194501030401c80d160b103407900002c100000c07480200b08500c0e920a03900080014415201c0455a0b82c040e0340103080d810140030792045003c00b200c0301c80b1140c11031803000781644075040d20009a2610840068603903002c107600f01010710084c2091046e1107504032958004c0040051000e215051040c100701700c0a04078400f85802e0004044030f150300589500b08002300500c050007101c080780040ba01e901d0075586011001944440260082211040c0c0c807503108000c011586406402c510800100c0a008000d0035412580711402c8941210003505031129800045c4018103109090380b40324404446c0c01820b00c07029500d01500318401b21600d200580021035083c05c10100350025101400072080107000d40c0f8402000d4611008e40140041384861803442010127015444054030408400a062500945080707132041c1d6079071403445c0302040113100704003600300c403507503a00c0c280c41c1900d40c0100136 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 529456546 1250 529455296 529455313
    0x60e07090f0e0a02130e06010e04151502070b0408071d040b010501050c0a0c1205060117030703050f04031b0e090c1c030905030a05160b180d23100606020a0302 70
    0xa0507240402002c18030300f25820403118240d0746660000d500100701d504404496890200b00040450b510240c401d8003d50070003005445801700c030600c41003030b91044240c1032610011210120703c1e042c05548808030100b0001000300d43d104c4c001c6010800da4544080c104103481fa400c18074818440101c8014108641002c014842507104030002c1c00c00401035070849002c903205803a80c194030b001950040303400e1040c10131010f007041020b0052500400700c54103900d100c0d05541406644078410301300000c00300000082e10400e1364890005a4010f980c12241c146249074010010500c00040c0d0b01580d4a0200c90000040107807400107814101604041c1040d0b0a102d4000d022500b8041000c8085091010702500820503031807c204061032240924018642190070307605030919201141c20501d11524108140801c4000c400b001070342c001d4003641d8250074501e25091807614841231080794580406100c1036801845400103002d4075100700d96200304141c2d0350303c1d04180d90b520460203006001d038000180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 529457796 1250 529456546 529456559
    0x806160206161404060c050c060c0a0314040f09020706140108030a050309150f04060b030d3213080105010b041d091213031a07020714030a05010906060e07090f 70
    0x102d420140940342480d0801d0880c03aa40e00c0025000760b0080340010300301041072824045c040000300103410040d6055458000200340b100c6d2510003e00c2e01070240005544403071203002615080b903008254290a074203440b6240c1c1501ca0281d03018000940d031082c08e203030700700f00d45200d04080e15040f0348248000b9032500105050647e036a070402048252680075680c600b802508000701c25a1040d120001d0b0810640703454a480d4084501c00302c2c05070b0107540001c7c1d10180064020080fa000410b02c0c40d468040070a1041202142000c008404101e6241c042941c15075101d007010190f007600c00400003807046030f0701e03041c040050f400344d032040c1080c10001c16030f0280418040c1c60707580e8002100109442d100480701000035071503807204542c90010030700400b0410601c03810003c104150b2010a405c850305051000e4025078480c00f44c0141180765041451013449650104152240d055018000340700b00740d22414194018003541c803400710b04010302d80014509074410f040f800c0c1510350f011002a0014101035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 529459046 1250 529457796 529457821
    0x7110106081f061a130f03110909010b0a030c08120906030619090504081306030207020906102007030c12051005040f020607060608241501020a080a02070806160206 72
    0x3200031581d96510303100030440b9082e00c0c01c81c1915070220442c40785c0e5a084480514030f003641d42d60041c0000d00549806000207465055030781c000d450700300d4014007135860f4121030600610084034255803241040100000704110321203208215805036040c2c81f48901d0f00300311114244281c0030f8071540050100b001440c586040700c0807020804048024001c141c0c3c94508a8045540542d007e603894400400d43d0340c1c0340c120481c040006080907140641c1030000701e0f8081034240c04050000362041c1001c283c1015020f100e0756103950300b14015000440c541840c10941d6844962030301059804815680010400c9500c5103211400160320100501144107289400e4008020181c011249004c0000c2450b01580d01c9001900c0c07440e00491000810342e14256001d850461080c1e655802c0c4121080060341003264040320719848040c4000080b06514034000407810140004c0d40186805030118440304407541c0022240300f80c5141c2d60844580e5200c988001040130340e2074411000503401040011030000258 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 529460296 1250 529459046 529459093
    0x102010606020c210f1f0e0c1e0a030b0411030c09040b1f1401090e071b020333060105030c04092a030b0a0f030c05100c0503120711010608 61
    0x40f9a1460700130300d101c1c4464248601c50365030b0507140c0d000c14a0524002d0b0810300306aa10300000c6d8040040c0501c0e0465180c460003940c3c04940700e0f004013106510085c0340001415030b204c00090458800503202d15280c0d070520320588098444003c0c01c600b807809800e001404035002c0200030004c941d10b41d16070f41c1c1c155081e40000c24030081041400c1c00d82001c228400942c030080c0c440182c0c518031403501c0b80001000100d1562004104c2c0712007400b8402200c0d08100010200c0507032205122a914050010900e008412004400010613080c29040c5c50b81000b44002a00002c0c148002641d84500d0011111030006070344d00300c03031010204002c01020341c03580d00c6161501d00c1c0004491508114031508440d440c401145900400e8440c0ca20211924029100704042c052412001d504070b17081d134940700003a6895018082c017450b54150f111007001c1c0101050000c50350b02c04102c969810326403810540d044415a41c25000c00c0c0c03039291010700080180100b000f56000d6800801d85801d0741104603800e01d921 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 529461546 1250 529460296 529460329
    0x30c19030b1504090c08010513020d0b0319051b0603060d06230a110403170a181203110f0d08060f03010e011413080d020a140a020609010b0102010606020c 68
    0x50720201d5103651269441010200740004440381c03514034049030b044c2982c0030205201c00300920031005002c07554810b0000c102c0c0314401040107071141e1500600304014000800040d41c1807007800c05091152124201090080e4850307400d90b014104a03035490b2240c0400d50000a03405102440041d800d4280f0605c0760458600800000c5140d1020740035000c1d1919070200b801950b08459010040d4144240c007440004902d01a16180f610340755031500501d00d46c00c4030603060140c000080f081e50329440380e0b05550507607401d19a60000f240e41c407203138840ca003e501030040740403a015070b8004080c3d0304007003048194200150090300f46000e0384c08085424071401480307190701c03000051050388a40c40922458001003001000028015640d040032a01250010400c11510382941608400a865042038500302e07601858096112120281c040d81e24085c0e01108080000700810f070903826503400103455001c0d40c10407000b000724104220049090b02c8075400741201582c082c14034042a07003019060060036241 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 529462796 1250 529461546 529461551
    0xf040f060908030702010e0c030a020f150903070f031a07051606020c0a03090f0503190b0c070f06020d05100503030702010c0f0209090a11030109110103052509030314030c1903 77
    0x322580c402e0480d030030944540c40141c5d51500300c0c4115580c10001004010310440c024807a00802c0c0e070000d040d08240e20416800f8500b80b21120f144001c8c00400e68211400080a07143c0c040d03140c41e92400301c0d0005100540d0020309691521081d1a04007591038041c0a15640d0203180031003521003510681c0c0490000c0303074115400c011140e1640c0040c0082d030b040368880d585914140389440c00b455110b202c240c20051098006000004400c80305418218410f40e000e00034021035510300e4101850b9008014014180d000f00070f02070420442039074000c0040d1400c2d00020400b0342c651030904a6008458007602c0c1c3c00d41d004002c45000366010342c40c00c50205100b0007190071404102d0f4080343d000c04054500101c203500460081082100440c0320800a0030141c00030001c0c0034890301d4507200004006030003418181e40b00082070301e01a00042960410100e180100d0005180e0311004018aa03280f2055002480001035030352910300d1101124040e0b001419058100b031006030000025001c454450b20901d03a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 529464046 1250 529462796 529462811
    0x1c0f12120605132a050403050f01060815090a020a03030522050105090609210d0807020c06070b0c070c03030e0a0812030f060a080f060105040b190e07030204080f010b010311030f040f06 81
    0x40c0d080c20341300030805591030544880c40c2d480c00e50318050101542c100941d04240040c04400000900301102c2c00c00703030069240030740b120305000c2d082100462020b5004000083c02005040d0400f0060108040354004030080170a04907162448171024000c460000b4003c100350709003440c100000d0724104c44001c1c901d560703242d0500f1110003442582410808642c00ca05084510550060700c140e5210103580003829524600070300050551040e003074000c20105083c40441c44418094094030340055102180d00c100c0d03a00c174180a0300c03001d0000111489450300c0c1a0100b26160007260f0020302c0c40c45860010b0540c0c9410110608048008001681102494a00103150f80c41000980c000002460150000d5410135041c40b0960b510400158020609003800040d40c1c40d2441c1000202c40c1d1a4480301415110414110081c0c400c5900c9140721388143c8250658004065106051840098904011030750b4a005108a640421900d180c2e0789644000010b001c00c00038001c489240344250700000b1440d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 529465296 1250 529464046 529464101
    0x12110d140405030609010b04110717030703020f1b0d0e03060406020f0f0d090c05040506060304030c14100509061f06030f06170c09241c0f1212060513 66
    0x101c805c0f20038005c603a440c0c7c0e0140c0a01d080c14071403480300c1d4a503031000600d032041948854100740040710001c7d20000001001880e201d20a0741950351411202c01499500e920713008011084040c0c03608400e00d1805850410300c10a4011a01040084000b90140c5019078440e00c42074020b411900c40c000000f0340800007281c600f61642e000b440c550500c03c030001400061400d00b01e04601341078000c140241c1c5417074180a443c0d43c5610942e584983d15160024488200c5e141c80707520611980789182e803a10a50b880c24041e0342441d0010340c0b01d41d01800844070140e0342d90090300750841c0590180303240419040070510549201e500302d0a8084d56402c40414aa59691070125948854044141e200c0c1c12004009120349000780203641c0207444c04001102c4c02c140442d440ca03018803581d003400d11500e5107061801c101c4e0303a141040d116917a00090030344010300b001d0a000201c1100c614040c00015010341d0b0024480b2540d100b0b80301500c60240441510301c1400c07000600414103060b15020184000c507103150302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 529466546 1250 529465296 529465303
    0x218060a02030a03050a020313020d021908030a030b041a090408040510030b1002010b060904090606050402131d070c080a0210150915030b04080715020a05030412110d14040503 77
    0xd140c55070707000310364941c1c2c0103400030115107000c1c1801c08568010010700c081281c62603400b006454040750103440004440c0f002032407a021071045500160844000018050000300142c101c20300309840c14040c4a0041c02000200d4035861040f00c00b401c030b4030100c43c5607800e100c000b2903801481040e05a107050340b00c0340000c4c400c1000c004103000298031804060f000c4e0900c02994001d03180f842c0002e002d41c84480c00041e40a006020710305008a503901d050000b40202d90300700740000c20b8060021551890410610184107860380205e07015619040c0041c0008400307807224034400c0c500c0da5a12003a0345103550320040c0950100a03120118412510708400041c400e1103031008402d11440b64092a030f252166800903144440c044040b104844076040001c00c9210240035840341d0b01c100d200c2c1e82c80380305241c400d480003408090003500520100d403c0070030580107001140500d0143c4a03200d0204074642c401c50340410403114014083d01300e80c0fa4001c00c9030065111050303440c032402130142016117900c0440d00c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 529467796 1250 529466546 529466557
    0x1c0518010e010902121c030209130e031e0c030405040506010525030206090307031b0203032b11190f110f2b050301150e0a060315050105030712021806 66
    0x1c0381d03559450710004610305003000c4049510750201800c80702d02c01801c100300519102d4a0a011b0640008142e80d49996800e507115100c007203100c04010b124405481c80b55241c1041c904050141e00c10541d14601e07034a11030035643d50b440c80d038001707501d09030906041c40064a03020748200c0c18003409015083c0c00640c04410030f00700700b0700c0100c85030000d071140c103000b0328102028210030300c075400810505020a6101507039008180c0341440c0164545400d01c0807174518801c860f4295255410381b04640c001d5018141c68850070104a4418032000c00e111644141703a1240110380001103d5448203107802d507001c3d003512001d1169030304001c40052150400c031400d1601c0545015180d4201a040d180d141d159040b820081c0e4003660b1400700451180b0601038040e10040c000c62144100340e5072004c890318403600c462080e1120262074403e11a54540c80980a82181d000c585005110800c002c03586521850030fa0748202000d0391998240341d04505407000a60000818141103450111210f019450744e600608 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 529469046 1250 529467796 529467821
    0xd020d020906041212110a0f050307021809010606020705090103060c030f0e030706050a0204050a03030c080c030a122003010b0c03161a010806010302030c040507021504030e040608031c051801 84
    0x41040c1800d00e0549605c1c1059005001400412900e018048100040483d44184d000c00c100d03070911004e08000307245000d10310000358005203c4c040d41012039510700d881402818a080280045134031003030203030b85451186c0601074010b10110b00400100340c258000c4804080d0324140016003695070503000040e220001085e0405078800130307100c420440580f00c0c10303138003030058441141411300f040001001030142c4c3c030001d4200620400031900740100a0112041c0101d640e044940c0c0b00c5400c0710161501c0d40c40314480c4c1049250615102c03403084075485925282d5003c0309107914607800c0c00340c1103080d504110380c240c000d84428049660410303c00c40000d62060300410b10300111003d503c1035030201c0001600600c00e1a00001c00420058a00180c550040d1204a8000ca110f6481c013900320f01d40007600c00c01301001d0f4210024031081c1504218089200401070b603007400780350303201c3c101141d49100310710034000750108040c0500005101c6500598001d10382c3d041e80302c02e441e1000e405909541e007506641 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 529470296 1250 529469046 529469069
    0x1b051e011e092d030212120408010b0a092a030e0105010b0909160e09041109040308040c0f06050f0f07020307030818040516030506040b0303040905010e130203030d020d02090604 78
    0x1d020a418212480c50b43c2c50703900065602891403248180c14468462000034002c14010702c00309140320040c0f005400040d5160031090f122039445a105010f000b5011201d405040b10074008507a030807a130700400b01a182e103982d00310780039440d122002103800310f816089c404040e99202e60a428440a0048500070a06101c0c042c4c1c035030300c0000c2001a00034015000c0c45c0144444500d0b050348541045980b0b0b00c64408803a550500d03500c2c0e04080c1503030707007016880c99071000e140340800040542203800140aa8020810100082d84911401c028820240078050101d4030500c21a40180a81c0e401420901080c42290b401d210056020070320340f411640046030740704030100d164504031120709004583c0b01c001710b4061095040034180d9115503450300e00d070301d8101511000040c4c016243d07600082040f07030000d4200e958413540c905092000b000d00303000c0d4015811280f404101c00d596a4400240c4441d001000f6515001d01d41d00000000d500202442e6002c2e41c00740a4448140c0e00d0744041d100811818001c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 529471546 1250 529470296 529470299
    0xf03070b0a0503011a09030a080d110a03140901150e0907090e07080f012c0f0f0127020603070c17030705070201110d0509040b04020c01020d091b051e011e09 69
    0x10401c261207014034176901d100280817420040e9000110807210b5500031761020b542d8609246910088d00c5055100d000e1883d0001d280c1c01c45580c5948112800d100030103a08440340c449130308e5642030f64000c9115015050f840c00040c0160b81c0380d0b003c0c4503001002c900071105c0d0b90359a42e0f903220583c0e000c42c0e10760b251504408010402200e09100741c01001c100c3d04001c002d10904200c0c2e008054680d03403c902d012007422425489034480820094404040110840c0c0c5400d112010050290040289401d60310840103201d200802505042541041e80200a1802d43d61015005c072105140340f1016141303016040d100d0001e4a0b41800254040c154a80e5030a0f6a80c82034000034100341d01064451025601c100e00c552003d560003029500070041c22180481c0840300308002801900415240d9074031544001103101504505070f000501051003a50280c89941d1420290490389034240300700ba030000d0403c0300b4001d0282003d810b8200d912030506011420041001c402200b02c2c060341d030100041109903e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 529472796 1250 529471546 529471559
    0x9040c05160605190618020702030a0611130504021305010318060903090e150307180905011112010803040612050703060e130506011505040308070c05130228020c0f03070b0a050301 79
    0xc0140c2c000c04d180300e041c0441c6143c680030b001010301d03c0c1910004c4c154041030398411581d051003907140700c42e000300d4180864031030703000a44001c0e80101000082c1c01d160754400100382c2414000e503845a8070842c4c420001078500f200540241c0000c030700812101c4448850320303001505500c9201c04032800790703841c0040c0904120b4a4101800c0c050440020f40c03092040442c031603540044c108043d01e50850500d83c249024041c035101070100000d0040c05035007002c00c070711884488000a4070101129003000f0713006981e030300c2a15071030344075902030301000441443c0d4041140d24a50442c80d08801503280004080d81e0780c00c801003440b00b0546880d90030143c101e00d60403e00230304201303007070141584042c1c1860314445020050914440d91100074109440420010300b4002e4002aa900404002c0c3c00111703000c144e828201c0003035014107241ca504a920f51035035009080140e68050061520740c00406500b03140d00200810500650482c0d54144581140403442c1d502c00b201a01c063b03c02a101e07180c0740d504090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 529474046 1250 529472796 529472821
    0x90b0706020703021b030a02010c03050409020a020604051903050304060e10020c01050603070e10120515012c1506130504360308181c0914090c09040c05160605 70
    0x264150002c11402080380d8007940c6c0401c07040780b0b00d542400d044c59251024501500e41c0e004031740c0a003101c00d10120702184000e0f00451030340e1140c1c4c410070070746030400d1050707032002c2c58a1201000a000101c0c248000340c0014031540c440903448050b20101e80492552140c0706059038800c200c10103444e5101c106002c541c0c1000c02c0303601e0142078003407070780d00c018a01788580011a800a00c58114004a0b01904030244042404031070304d50040030203e215250384603149004103086c005484070aa10081c942d007440341042842160103409440941c0701d036a442c21041003c25080400d4902c1c0b000049000000d51746d850348541d0f00380d076405600301001620740e1070040e600300c0d640d000082c13440c070110050000007e0f40100442c0c0c0c003048040c0e4003003468650450321854200486020601071b480f038403060059507003080180080300c0204030000c900119071020702160507010345007850401c0c41030002103028681500a00303a01d8041e450000e0408400a54060046c101e0300707402d8404030b6403070041c0503c01c0d9840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 529475296 1250 529474046 529474063
    0x60902090106121515050919170607020f1e0102090406090f2a081305030a091a07050d0813061104080d05030405070614070b07090501030c230a090b070602070302 71
    0x2030384044101d45000d9420600303030300c003141031345c03c0260020f41c4400c255618512003050850b0300031180ca5043d103410200c8401503080040f84114402d1b40c0016401510000b906254000304101070800d0241142d0b00100021185092070140d540a001d00c00c0340392102d208080082c40180ca003c02e01c2c4c069005c04c60112100048140c450388042da5050a0071150036001131030f50082460300c2e44203075503480056011507080540081041c00002140412654041008010748900c002014041c480e18032003010a481085030050054205551140034a4014035a043e44085481c418501d422001e40e9410216402c2c241c071b801c400000481c0610200104100300080f4403050b0404c14514102170311401c0ea6a06944640c00801054990f5455190418000c0e10034a952016504106040010014144100700e0088034002450240d23040b4000b48500103002c503040ca0340d20030040c1c10750b007103001000f00d41c0588441003d0180110000440c40c07148401008210b004280051312420203190007820001b51 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 529476546 1250 529475296 529475321
    0xc1c0b070801030c060c03080c0906210a0c0806030a0213020d06270b010c0f020102070504090f0605090712081b0307050706020c0f060a03020a021608010617011407050706090209010612 81
    0x1190360100012303420200d85908401d0040d49191a1000140040d4003481200e0b04020003419017030b944d100411000300720380c0c0078600c007010034052007103a61011983d4940c11075500d54180d00c000c1c100009401e10301010004c80c807654902615008080500b00c090300c0b81584010394602c500114082e0300b010942001c40c034403d0311041030003000b805a000030001c04100c40b01a2800018000110441e0b000b004804000c0101070810320081c440b50620f12111029400c050351294200307c00a01810000310703403c8144c0f045c2e000c10000a030b005448203055500028070000e90550020390840d04050b08002034040c503846100102052414404000d09240c0001a010302610342d030341c01510303550b46000c2501d814900c54a401a161075415400320f1600029825180e401d5016400209600c4030641020301070b03907100954001c081403403080c00303822204a0302c40b0383e60300d4070000302084280d88030302d0040449900801020075804115000142c6840e000c2e03206101007400d1401a042e100620301a00000840 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 529477796 1250 529476546 529476557
    0x518061e0403050d020d11030618041205071a0108061608060d02011b020a0807090c140a110f0102030a02120705130b0307050c06010305030702150c0c1c0b070801030c06 74
    0x40310103118000c002a1000b070034044042846901c003051503041c1e41325540c144005004110320203100ea0750360390050b40d00d1406054100c1308503501c00707809a01d10307015075400b070045070a050140f10704a0f42c1307400090702210344250f08600c0d840c80309410384059000c1d14440700607000078100b80c6600d003d00001141c506042c002c03844204400e55403140448201d6907028284031072141031010740203440310b00c5480000e40c00313600d9180110300341c8000550441950440399080000380080705050f521640e003a915110032041c01c10649076801c0c401d80074010a8001d80c012070700c7d2003200d0b440c05400d80c0c01c01c031441e14207a58042008a40d5184240915030030241c03509203103140c2081c6070310340414076903c0c3c0901c1c03086400c0040400d28540c030500448188043c060169001940c403442c00e80e88075031009000342d108005c140b03141500808007030211070510341d85600400301d403083c401c18098203000303025883c50340c2c81403085540f01040c8002c140070321035000f40e50b0f501e65541c114036050100ad200b51300a2020083d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 529479046 1250 529477796 529477831
    0x140a0b0f15030c0d0b030615040506010201060b0417010b09070518100c0b06060d020403150609050c120c0712021c0f27050a03050a0b09031606150306051806 69
    0x80c072541141e0b0010b051440e00359035402903060890141c4510010b0a8061045104104901c0180701c0141080c1ca8216800d22075a2a8000124244c6159029020848904100400030490005220b10300c0303c0c8200c1c00400c60000480002e003134140b0842d10a4042100001c45040e640340703e01d0580020703001201c00429107064480010004508031310010080036441c2c000c103d681c3c0e540b006450b0303600b880b00815074de119100d141c11160384503041c1e135031a403280c104070022481229030f015040c400d203e145095418400321809500c00c20300090a000c100c00e00802076000031422810110440d90f1850b001040b0751280340e401900c0b546908188201000151071010400903400b1110181d04c0101d1800908081c1c002803410480258a0b44070a5000c0e4002100000f04400483c0300c415481c014040112a5900c60507219101e2140d0144500d086203880a03c0d00051703445d500c0741140c4000d0841e00804640c80380c0c0c5900464009545560344e44500c8042240749220401c07105a10a030603031440394141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 529480296 1250 529479046 529479079
    0x10b030907090c12050a110a050c07090207030c02010c0309050406090203070807020a020108070e0a0803130f08011b1416030203030a0c18033c03120203240301140a0b0f 74
    0xc541c5044c4080e211307152008140c0b00c10b91608449002201c443c5083d549600d40c600c05401c0d0342c000c00eaa18250301501000041602140c402e50781c5030340d0191100291107215500441d20b0007e044011014854a91404900d40d2a6441504060b01c0140d000603620300780311b003001c0c000c4c0324020030710700c210b40c46218084c0050b40d00c018105d801122904100803005c410303d0000c0d00420003504164068480412070061002c800440c440413907280c1c0e044101146c0e200e0721003600740d480500710b1040d0020348031100e5203000d200b148050343c10607a500c1c00e0341c1400c0c2010070030003100390314940990050b440802480341c0300c0740d184910001c86210b07084c400e0002200e186040d007805202d10019001c004a00728640c1c03220a07003504032890055260030459000700107165031490013800f481c00d8001541010744650729005604c2103038012590103000c030071242d0315400c0411072a03544a02168144d502c42d104c0044003501840c50b00d000b86d400b000c01140000c401030500802c040c40c500a90b2040d8000e03640e10491 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 529481546 1250 529480296 529480307
    0xc17070c11042003150d051b12030a0f0521072a151b0309050c0603190902040b1005210106050304080d0624030f020a05041e030605010b030907090c 65
    0x1007521603c88a40365034544010139920310500480c96040100343c40020304000c030118442c914600d480490b8481d44140340c0502040c03800d90403491f289907008200500d102d0b17006500004801007207207090340c50000b1080110000445170701d001d41c807a118484c140310705507410441c140c81f418804004010004900c542158240f0309085014021015081d110b000a5103d0f4000f00415410a503021a40d0120080000d0090410f400140e41d030b800b41050070255490400d003124015482041000b40e00407108007114014000c05ca000c981c0190307200b00c4080c140c2c480d407142d8111010b65854494440482c5400342c20002c94264201004810020052268981081c2925046900981040d4071a00c100320740100a08041c0c0140c0003485c00301070b422600c1c00c0e4000041181e01180d9905001030100c548050702a402030502513008100c0501c400e2244d5110010824010010000c1c48180e6907500d03151107044441c20303040051080d1000080112820301084071000522183c0c1080080518a4100402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 529482796 1250 529481546 529481591
    0xc06030c1103090604090f150f080601050303090901060e0a030507090606021204060203121e10090c08060102060601050c03070c090605010221090607081b0c0f040608100c17070c1104 80
    0xc050351310001d54071f542100783d0000e400300b480f08130381130201c80e00c4100c4145081c8143c411a1058800d54001088904001c010b440f0b811340c024151690f03036420184251000c2130703020882c5800802510001001c10410040c0800505454200203078607810f1400c024103190b842450744406800c00c200c2084495400822244c0884414181210a840f020840c0c1c6054a010301440c041c1d0394144280020661705114602c22141c048008001c4482119829a90110304a800c0b0f0302507040140090600c0d400b50008051285078401503074580b02140d80c615880c00b10700d801400340c40e40d171506e00780b246580400c14010965030415040003214140000110948240c0241900844011403008104001003007a500700e050304085c1d5240003046104003558419006042e184602003481030600c1c4d500b0030380702e00819150082e002d0400f4243d56413040020340402d01290301040100b425400b4216074010740300d80207500742c2e0b076429004451402c1580d00643c0e900c807102d01c183c0c80d004031100e10f203011056644 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 529484046 1250 529482796 529482809
    0x91203011d060105071a1006030510150512040c17070b03070c06020f0d050f01090c090308070f0b010602060f010608010803030a0f0b060d0207051204050303030a180c06030c1103090604 81
    0x40c1c2035600d1000489803800384041c01482000036a81102c8019407850105208081036580d2113a0f0540d103075003c90960700300b0755003403a400e6880102402500c0d507400000ca000f03c01800c0c8149003805c0300203c1901c1e2401107505465200d0025003e101804c8442004401c00340d50800910840742801d00001c0148400b070900c0f0305105071542490104007507030701550b046215100b0981d48880301728860030064201104c070750500203c0c140000c5241c00d418860720704110200e650352a44582940d5451600303501c90a4161003c40000c9038034000901a6250240a4802e60b40a44510306051100800468060300720006109040005018250000059070352100b080c1c43d0100303c1102044441c0e004045007002140c1001000800540342d5195400400060303106008841e00c0c02400150310b00d50b07000714060320750f158000b040401ca524181d03030042007203144c0e00741b40380c440c200715581d401005400c95401040071035201d8482c1c508441c0c0003044901c17500d0424020710314005158001801c0d0744103030300030f08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 529485296 1250 529484046 529484099
    0x20307031e12091505240904170a050d0b1c03180b0c0304080709050903040320060d0902090a06080304062607020313140d0b061201110309120301 64
    0x750303400e11400414a851180350401c200d807160506001140b1082ea20078803100e0b44c1840c010400d000a180e12051051070045030081980b20160208161594050415540d00001c401e458900c5402140103103010041501c4d9160343c0ca041c45860001e480300040258894001000d0007414913168120041e04264940751500034a20f000d000203c3c2c000c1d450700100030219010402e40025280040144141c40f0204200d901680d034410344201501c4084030000c03000d82044c0000c100059a1012403004114482200d10300b000b41c40d8007165a230340040f041070030201e0301c850f800c0c425428150b00060b0041c0030340c14103005e0a4100b1040f070360349118074440c0400704050f000202d5162030307030306a004900b0391b14031446813403c0c00d102e40e000750342c1c1c0c0060002c4842c0f0001090000381415030841c801c08104c4025007104c05040250b00c03800c0102400406450300100c0681c0c4680c492002171188031050750100d0740e06612800c0c1800034525044400c02030f4549a017007000144512700d42c0c210301108550160044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 529486546 1250 529485296 529485347
    0x10031518120306150e0f0603130501050a060612112a192907110f06040813060206010f05060d020f0d05010314070e0a020a030b060c0105040b060409030c2a080105090c0102030703 78
    0x15275054644000190081d4030300b005101030744006404c600e003150303038644e6402e00c030420880c89a000c69841d49904100002c0c01c0280a00b60041800c003801036507600b04a02c3d507486000b800041c02c1c040341c28140d105540440c9001410010030940d00f41d071103a415818110180740d5445d401454030300107080c031400c1c040704245544420f602009401020746000b03090721128109032400c00d810340c10980c40c0455800c2d1000020400904c00150b03a41240c101420000c01c142c6420103001c4564048403080c3c1c99960200310311695214403900902041040030380c00222903245091540c47d40b6051340619050b900300b0b0804020f0a0283c440d10b98010750304000c010703510b942506064008056040d11507401a4000c035409a150300c040d80014070440c09002c04000540e1504100421036800302002404140ee010100340403806c81238429070410348452205c2600d88010035050181541d580c007508541c2c0d1508104080340001f40803070f2814203000e000171800c00c0002d5034050859003c0000c08060320204104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 529487796 1250 529486546 529486561
    0x306080d0e12120d050606070f110a1a0304140c0f04150f0b03040308070e061b011e091106181909050c07050610031518120306150e0f0603 61
    0x2858504095640d0803030f10712864400c40501d664204c083c04680701031800d00041c00e5400c0000803264113540c420750b103401d44080b0f50759485901c2854254140c0044071898045003142e644841580c0c2c00d40840c1c2034940320b01d85803603d80354480421803090815080f1124403521501d0748087e40d1076400b0200c40c04038007040c010221500003000c41c0c1c001c1208101c0c2ca10f000555082c008000c601441c0a5a68106580e443c0001505c054441054142e0000410064400c2452075200a11000030700d00303002007166985a01c502290420002400c00f00c180d44516142c10480600f400f208425001d441c024245100806141c289240c0380c030f40e090007404043c4e401001800030050500250099071030400040c141a283e40301e07180c22528040300ea034421200451143c1400042d9941207a500c2090340000c03d6401c2821000340150380c0d010781d00401c118a007c1c0000c0c1070700703064442c07200c0c2956002441c1454003010602e0400708001c50f00034131100c1048010280c440080201c00030000742d5095550b40c0783d404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 529489046 1250 529487796 529487809
    0x9200a060503061002010e2d0f100b030c090c04090c11120c070b16020f040b03100b0a03080c03070b10060c020d080f07050c100e01200705060a030b01020d0306080d0e 73
    0x1420313064010244c0103841c140f5480840480d041000140c22500008150300b299a81c1464271500755a82c030081042030325545a4110301c2d50800042c00b60f840340c85800300825100407060b0b4451075248001f00e01400305030010b11448009102d02d2810a0041c81150746160300e0310302d40d1000c00185c45000480a9240303504100c80f03002080040c0d4801d94030100b0061108030420000710892060142c102032134420b29140c064009a040b0003005400415840a58540180012101c040d00001c14900010124840e1400307008080a4013002d15134400007481c2640a2600003845500c240700e0384d01c0c0902055030700c0350403403001c9031f41600c860b1041c1c40c8504103072005004145200e4980180040d8017401c002001c0f807070151400054900d003c03440904442902da050101d035080b80081c0088521300d8103055042d1a10100c011403100755020551200041245544480845000310b502d81d040b401c03695034100614050250f03140b90400655081482150301c076040e41c41008104161140c00305199661507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 529490296 1250 529489046 529489061
    0x7021b062704110f0a090b0301030210120e030406050904050601140d020706021b010911030d170c070b041a1b07080309070b160b130f08180409200a06050306100201 72
    0xe183c440d40f1018580d0380000e041d445075910340c0008480080c0040c43d4281c150030f403030680394004c06000c48205101c200321006411075107102d8003540c989906481c60301e0240020300181141d9510650340e4142107040c4000c6d1180a42600c0c1000180364a414444140600b500d01c4281c40090260780c4414508200e1702a010396110391503203182e0116520303024041540403204242c4603206c0c036103030358031040105625820341601d0303240130608500004074003a81c02c203105680b00f410341d1403030380c14140d05807210101594110b9084036801c21202c1480c480031040d90806a02030b2046414400340100c1201c062514010420010040b0f032000c400305610000a03c07102002d4030064002a0300c0340e920700100e8803d038481f44010742d0203030b1031840440c03001c48101c2508213a15400001c125654229603403014038503030119049c05c8048040690410507940c447c002e20b51528050f1041410712074401905500140285044c54440c80325030104010003500013040d01c2d84080c0440f01441c4040400c03406a01402c405c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 529491546 1250 529490296 529490321
    0xd06050a0e090d030e0c061c02120f010b16020f01031d102a08100f1e140f10110313060e030d02030d090f050607021b062704 55
    0x680c0300030034440d210a51051003110344000700c4941e119002000c0d0f00303d81c074110f460451600035000000b03c50425034010000061703082007590501c5038901e480f104076000340004d00300ca14058400d1007207910003c2102800341c210107281e036250901069100768001c5403454002d00403017044090000d107071300aa2003a20907011815034404025101c100c86030b16143d4044c2d04100c1d03140340014195041098022101c50105140344001e40c1d40c2e0035480603105c501c0d000b400304403100210320000c45c00c003141d4400800205101c171400140d03030400303680014803201290840348102c0c000ea0000c1065980e07244d01400b502d4819502c44268840f91817045036100d0682c08034620724440041e00300120500e01400700c0464503140d0b10020303080036405c00c046c0c0710100c030b448480060b442484035044040340707a4000c1c100503100d1000c000c1c801034940d5800e400c0c05c1d411034420003d41c01c201c04c207607140004101601d8400400f100d106d0302d4044020004050580b550801c3c80d00c030303aa21440c002d0580c079203a2010480d00344 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 529492796 1250 529491546 529491559
    0x80c07060f050414010c0c0803100b0a0306050103050708070503162a0209060a121e020a0b1206011b080306030f2b0f050f0a170703090215090906060d0605 68
    0x15200a50042c06003a1412a0b51846030b088600002c1018442c540e514506644c1e00030a9541320344410350795400140000064143d6410001000300da41d0f40103000d00490343d10081200d910309000942158801016101440b030f080c0204002d4075880000c8a500681943c00c4031800d80001400b103c1d404080b010702d40ca080203007240000c51001d400040c1c064144200d030200c116030785000920480c0c02d803d1003100700c0d5a510b000c0400000300e21080505101b82c01050380f210713407445a00041c10b500580d03440b0005d817000c00500191007003a41d1600590240d001e0901142c85404160400b5080346004405400c6d01d40c0403000c600103980c240404015018100c048440c20040400d4816003801e08441046e183c613070961070b4410560151030046199005d5444050400380206400c210542c032a0307000f54100101840110000c120700c40026029079200c1d60009156400c51051090001c41c100c4401ca0440090200e40722030341c2c4034403115a00640507a4042e84400c000300829002c2c00407034000590160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 529494046 1250 529492796 529492811
    0x1505130b03010b072303120a2301060f0309050309040b03030d1d07150504060c030509090f24030a0303110403150507030f090f0b06010203120c072901030201080c0706 73
    0x3c10028151036401109840c608500186040e0191002da040c00415900244529001c1c004940c401d1503210860303020108034400e80c034508805030395541074103086c541746a038018418154882e01c50b400820b12810308101c640310399103d45a0b61300421540c0c62041e5110a14011941c8081c02501c2c1703c0c50769080c060000c1c88a00250241080100c5e4084142c0d2150400010314501070b145000460b1000e51102841c2609040c02110b5110901c1803c0e014844100003580882d01c2c0d941d8410310403603c0f20329150250410541c10031810802d800c52003605010002413081c01c0c0d801084601e0140e07410305000031540c2d0720102070729860080c2d07130010302f5841000d0701000244400d40c1141d4412000380d82c0800000700419041802c88160900203071a01950303c4c46200010700c501c458030307001841401245d05104900f40360b01d10088044500c1030741200081401010089850350011010940d9240814070405d94001818240070501c0040c0c1040f014801040302101d062085a039082e800c90810300044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 529495296 1250 529494046 529494059
    0xc091509040c0e130b0103060c03060506030405250503071502010e0f0a0c0506030f1506160c030c05310207140d1205090d030b0301020d1407181505130b0301 69
    0xc9072900ca00c1d80c3d00850000042c519211400f110308166030301012815680e4250707103d2400900c01444000d05060380c031040401e0b641d503440c02641c4a00d00c28001803074602c40071003e051404034032030380c180d0000103804001d00559a010480b41d040e14400480c80381c0011010701d0480c050f0500e805d606005005500441245801c04214002100e00034540060b0141e50b540c240640c91008807055603d002c4190081298a60101201d40f4034107030080c20ae5040081c9608112551259014101d9242c0c0c41c0b01820410085010750203030081c602140d0f40342400c0b032803d50810800303040072100c2c0441e250302030f0f0900b80750400f0b0341a0340c0da0680164036510042d1800b4070003682c41c0405a0000b0104112003285104004103010700c0e4440d69010740a0030080c2c84c0c443d000c0d006070200c1560282d00d550244134440c003d04851103051002a02060748903c07600300480d01501074150203055a201442a080500070101500c0c0704e002c6005581c6040c5648011481c0050b2402c50301e90400d810201d800000040d50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 529496402 1106 529495296 529495313
    0x3030f0e0a0902030430030506030c06040e0709091e18150c05090904060c1404121e06050a06090b040e0a02220c030515120c09150904 59
    0x4031071404051108104028080c0008980c186c00c9180800d039260041d00d0f040725040d00035000c3c0160110100304584120301a201d620b5140c5004510b08a10807007016000308420300040200110b400d4140c07850541c4444c003000d0003810214a120340420820310b42e400c1c0e9038050003445900741d681e1149006040b0001c180c0c01445814040c1d42e2143d15800f82c114400c6100b100e00080058810b4800780c0b03a8a44003e1422000b08103100c14400c22070400250b141c0c494219100660403a171042081481d40710b541c400401681c141b005000401001e0b8000b80c0542d0050182400041c2c1280180400c0350500392107200d03168406130a04c0e002d8105004001054101c0580303108000c00c11518a10a642c030607448400041e50b40c0c402c100e2502110780c034041260b90100c1d241603804010000041d035030f2030046104d82c81140181c01140c0709580805010041500103040c1201a01e01818800346 = true := by decide +kernel

theorem cover : BRFrame.Cov 529316546 529496402 := by
  have h0 := BRFrame.cov_init 529316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 529316546 ≤ n) (h2 : n < 529496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
