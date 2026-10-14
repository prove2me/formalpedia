-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0638
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:51:43.98891+00:00
-- url     : https://prove2.me/submissions/5f81ed7c-ec9d-427d-840a-4a1737e6504c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 114568345 ≤ n < 114748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 114569595 1250 114568345 114568373
    0xe010509041103240603150d06060506071a070810060e06160b0603100b09062b0305031f030804060e01090b0307021b040c0c030e010c2a0e04030903 65
    0x7103034658500500040907100254000d04d040300c120500b02a104005101040b412605103124000070400e110710b2080c0c0400c070021900c0c0031100d900f402c44041c40c0480c02031649074050780d048080801e411080c8003035000006a070342000d600346902582e9400c4200c481010403144183c02c00c000071000d1141c184201c0c5c00241504000d0080c910340745001440203400446498200ca080e40c09804010b15410244009404070040780418405200c940d00010701101004080741c2c081c001e20494200c2c65420340040c03011010071400c0c081c0400b40b02d420003c285034000c440301503e840078000c107080e2501c840c5101e14212030b0008140e6040600340a0120b5009110140c15410880400004128140f90780e00550044202d90018280a0b29803041030708010f013503841c0240316514101c1c0500030160080100c82d22154140703040c1507800c101c0b070016501000400400740c64078454031918080311804242032a2003e031520079000315244c1d00c010f090b403040c80480740100010780c034180401c0000e41403200307441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 114570845 1250 114569595 114569599
    0x4030e030a2307051507050f0307080d0b0a030803090c010206010f0e01031b051302120601030e1b0402130f0e01050d171e03070f0305060f0d020105030603150702060a05160e010509 79
    0x62160395030710010309580413405d00110a00d000242c1e00d401c0040804c01c2001420401020314241110b03030301c0e40c50403030191f00c901031070b280d49400e8000d02c0b5554001c00403024661052502d9120f003400252240e6a800c05421240035104090001c0fa242001c40955000ca4040c0c5603800c2c0c0307580c25a80d42160a0030000d07014091a006400080340540c0c030b80414001005481000684402c12010f036103c0014015040c0b17411305251500c0f0301c4084c080030a410400036118654aa600c0030b00da40450000c1c4214080c3c43d8400819010209119010782103040031030f00c0001c080c91050343c030f036000c0080c09404644028900002448801281c001104c05000001c135407078002000c01d00f040701030b20b080754001c41d80d510005441c0b400246169406210f02038010340e0039102c038218603c030517010890010300000040d050200c08000142c00d83d508118000ca4007514203034600c2681002280a55201c07826242030030464140340001d00b480d0b6003005070504e0720450707582c1d00d2001084200152401e90080c41c03030070303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 114572095 1250 114570845 114570853
    0xa0e1209040617030d0c0801031a1905011409090d09060f090906090203061c0233070503030403110d0e15070606060509010201110f030c030606070506040b04030e030a23 74
    0x45180301891840040f602d01c0b0051a564040e10101d1412903655100840a110b1b12100600100b18412886000300079003010008161312052200502c002001c1089440c00d41800004a4860308031200f020b00c4c94070643d100304581e21035410158403880d2500601c00041c5088404101e10361207004400b142d5015400d00706400c0d0749a2403004261281a08419605600082401081e0908030400c0300c800320707040e0f02c24034012070640c00224a105980041c1c2a00800321004126200c020900d1000050780158899520304403858a41c2c1c581d0400c96040d408128100940d044003a00440d0b103204d080d6260340c690707030b00c1d682000c100814000c001c148505c00d284140100d20004d84144600030182a080e1280707501c5041e541c2c002400d40740f042074030000c0704c0014000300301401420f000ba00d402030031488600d9100d542d44000b01d00729019900d4060420b1044c07a0038001400f0341000d009000f2806592401015850710050507075032941c4500003040540c41c080c5126445480c010344904528800c4192 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 114573345 1250 114572095 114572099
    0x40614250c0f0f02060c060c130501020307050a12050c0709050402010e061306080712020a020106030b011a0906070f020d060c170606090d02130e030904051503070b0d02040306140f0a0e12090406 85
    0xc0c41c41c1942c02c460303841030002c0004902700340710400b940400c001c000c244029031405031196186902d40b024542c0c01000e0300b000080e45070a0a015409440d13410801d1400c940706079a5480038000a400d0544003a0b004c00c9010340807040b681040303021a007040018800c1c0c035650b24a810342c203c40b03d00f0020a15010880c200450740c5881c01c450005040c04011580041501400c1d420b000c0c03244541030707021a407400d41180f2440604c01c5c0c08801d8400f000f8040750526140d146074201080346465600c0001d610603900b200503401c1100a40c8966006413840d0748017014080d48102c05110303408181e074281c0c1c1c0408140202901c62810750340250402c0d00c046c0c80809400c4200c0ca111050b00c000594801054101044a048a05045c402d00c0c0e401004d68140c0d000b9100c001d00420382f070380307854011015100000a00c5000141c1a60102e400642d44410200011103402c44506083c820584480c14001e15090210300c40e40b046d40590000c2d040b030040038008007041941a00c9196000c0c48625811035100c00780 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 114574595 1250 114573345 114573367
    0x1051c02120406020307120e0d03200307090e0109060609050d020f03120406080a230a060e012d050307180e07090b01090801050c0d0203040614250c0f0f0206 69
    0x7601035031003a8800360b12400e090360702422010725203c0001c502031608c1c10300c600042000840d0710000000b401e00013407555801c0500c83e1041000702c400008220000144080c0961262042c0708941c480d0455650690f251280402600e07094400c07040000c0c20b0040a00c0645044424a03409c2d80c8018000300d041d843c0d80c1c0100341000a0004156909807000c68200b04d045c2e04444520391126000600700100c0114841d40c4410342e0381d52041c070700c19880d030600240f00c0c800305034000e5000d4a81a1f031030032140d60791260080900b28044035100c4140b15085209101d10300d1103105031047d5400200030304981414071001e00030484100025280f4161281ea00c030000b0441030200001070a1040004194558040c2c005401c43d07065030301c490072580c90003080003c0c01d44c1003826645425045440035a80b07403034504100d805041c2d80c0300303100030705040b01050200e079104013013603134101c4103002e24408800300883c3d2b41030b036080c1001d0314040e1907a0180d22042001a131402000201188010520b82c10035001d40c0c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 114575845 1250 114574595 114574627
    0x80904021303110102070e010b030f1f0807031e03020c0f150f09041d0d0e0f040c0206040512090102070306090305130b03040c050d150f180b100b0901051c02 69
    0xc4243d409609803105a1a0380d40c0c14880c48015010b80707021880340c2d51600b14902100c0c070005104c50314000c070400c08501c04010891119001c200794054041c4076588824800e52195210703c41121040480881c203284d01a084101020564040d0050818800b0703080a03c8445288901c5c0258050091040040001032403805000b0804a010340781c0d440e00002d0040c081100c211840c00080101d8400662511010000b42e414988610345046a2034080000100301d240741c8420800780e01600b4150708088180e40019540e204a00450484109401180005032248901c03041d190050704019414030110b030b402e811451401d4841d140942c94014201a0b19914074007980110b0b411540c00424030003405228a88107014000490781d0b410669003903540d180c0c1c550183c101044031291100404101c0300140c2d80a40e0801a203000e165034186a0342c035028001e0306086400050341041c80601007520408442a540d80c40c2068441d1460014440c2da004418100718803c81c0c020380d000c002441010540c81 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 114577095 1250 114575845 114575849
    0x6030605090c01050403050714011b080c060606040807030b18031309060b040b04060309050a061d010510080703080c2e0e0a020906041a270106110a0809040213 70
    0x114001030315052118000707040040e07880c25641003050074441480802d40120742c0c20119440360b2851140310b5184001654406008600b0000300d06860f90f8035000c0c000c2c2c0c080246000356000b81a51181d503601002c00400e4007a60050281c958002a42480003890300807403150010000091400e07002070443d5081c1c0b46034000c18242c504001e01320f8007003140319417500604000d807045200035424a81040c7d1210b0150007948550020152030751414030a0040501050505035000340007813003020b010481081c4519040e96242000d580381400060440d003040c4d1a42043d0b480107405013a0492964460480c903821018036203409000c0e02c080d01541080e020781c040039550306446521840e80c1c034101d0503012144401403d0f895030704041c074510010f980e001482d0b0340c0488100c40001b00050b425a00c0d481303160b000503e668100f05c01a00340c035420b190350303040c0000c5030b03c0481c01900d03180c1c1c07100340c00c95030403103005c09070a00c65003c2040f400000c0d00d402c000c1c10518501400040c1401400005140114056 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 114578345 1250 114577095 114577103
    0x1060c06020705030712080709140d080702040504060b12060f010303030e070f080a0c08151801090204110d0c02070b07031b08071202010f0608030708160b0a15170307020906010e040603 81
    0x5050010f608540090343e030755100d880350508a44d0146049a003880c52b0030b802c1c3e6820700c903804a2800200300b104400c107440c10241c01070400c0200789003c0c44e00b00d00130810081e10b01d00c40d0b400c807006040010000034000703102c0d8804481e11141d076460350b80c0640161248240680003030050782008145c1d0100d0244640003002100020829801103062103140710341030740c100c0c0002d5003017103802c001003000c80e05409400108040720380e6540c2412854041c0148a80640203610070300f44803040500d401880094100d6000c850010045d58013002401e0340c0e01e01141c40745d03c000d80e105001d03c40210307004e0386c4140305450381004039a06121441d9a0419a40e01808084890403500d00310011490340c24403031800914010b020421000d4280007049580380103403100100303260000203c0c0c00c242050062440712061f440340c001060f60811010040140030030711901402004803001c0016030640601e00d40700080a0080078503d411001e0b000d204144100515460500c4009101043e0756111071040d04000d41c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 114579595 1250 114578345 114578363
    0x90b030c06121e070e09330a09020408070f0e040b04080304061506030213060e030705060c010f050c0a021006060801050603090106031509020f03030a091e090230090601060c060207050307 82
    0x5d0000b00700c50098050185580030401c0030000856000780b0180707491000e90b0780f81840b400050704002a000c2440e9400010400c0d0001c01c000903440400241c1c2020380703007041290f00d8a65140d06810385180400c0b10040c106080c48404500807982a4004640043c01103802041e04010340100b00b4a00450707600900010341c1c0000c4604c0001c01008644c801f908641c60000c4000d001400002d17900c114a00450b0312032900000d000345850070950040c4100c24071200140940d140014050400760402040d120150240211540d01d0784e41c075204000070b517078540e2500101642804203000782500000c2c80000d00c0d644c1d0386400f10206100c600841da0381c6000710008903101d0034510601402e000b030110441e000b940203100070102c01c3d800071111415212100c0007028213014891107078944241c140c1c020f00410744000b400b040c1402c415080c030f03c044c011150383d141000b00020510030304442c0403901450a60030900042c40703510711414414455038003071400035062041a441d03030740c1541d208040c2120b00c401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 114580845 1250 114579595 114579617
    0xf1507080f06061c02090a0609031709011b03030e0604060219080402090f0702120726070c05102007080607080f01050405070c0f030801090b030c06121e07 68
    0x340c806203140e441000840010400e0502001068080c0a802c8200000b01c007404550302080c942a03040d50401c070310042840b020790b81c0d2000b020703110700124041650300801703d12160040c40c03c0035040745d826400694500381e002d0b845101d078040c1001481c2003101003540b50310512a45c0042041a03e000354020500180c0d00d805a118207100e80d010b0305611300510112404100141e6540c0c0c40c0d4992040404401d140e1640c0d03080002c0342007c640594065002074045554814010110f5841c02c4c03101084034080c11100f00e0100308183c038003038004000d280e00001c4000b40300b9400d0035116420483c082d41040c1d40260103600c920403000d00001029101c0b60b10001e8100f010310000c11101c0e401203094200b50f4054180049140d02905c0d050040901880d00e590100c0e00d014400d4481c5140550049001d10341d0b540b01c0d15004044240a00c1900b00f275906014805520b40350101d65007041110040071545084899111810a00b0000b401906c4103001e000304050f00b402081a018480c0d8400ea491201c500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 114582095 1250 114580845 114580847
    0x110309070f0f060503011809080a020a02100914010c03031116021c08190c06020d0504030e091006080901110a02030408010f02071505090a050304060c0b09011b0503090f1507 76
    0x1281d60010400c29000d80e02000004d4105040f20b0654544a1803107000303004806e10140500390008005008807400240352034a19070108240c03100500c200c0c1e1103122144458001c407100708080c010280c40c010150b10107040b0350b02a403100ca0300103100742004540110800711121007508440c0b20351500e10503035660a821483e05e0b0440180c00e4400800c024000c003521b0325131441a000380c10305004180e04855000400368090009131480030341c0200c055558440c4034aa20000e040260f07022004075804940f03030080791400ca210144a89400c100c000c150034900310301220a100c024241ca615075580e450541030080c9040c000304410160fa03001140e0341d6242105c01030840d044c040c2108040c0d441407040c4c40001d22030005600c1e1940b003400f00480c0302e4462005e80f0342021b024030401080c0780300010740024035940003003d030054140a4400102c1959030780c12458207844038000c40da04100304100030069035500500155030055003031422160384110102e0414a0130180d0417401e0741c080b180c201044112 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 114583345 1250 114582095 114582119
    0x1203070302061806043504032105030a021608030c0403031d0f090c1204050105150103020f09010309081e0415030903020c010813060504080903060906040f120311030907 74
    0x40006800030b100f41807080c3c8000f545036030000e4401440044044500e510441c0441c142e0320240e00804080b05000750030401048007540584801c58441100030000c148030050156000604881904c0d081d14594925000200940c404103400324910030f18100c81c0c0c086515900518481c4060074607a035601d9085040c017414015150300403561040c902c0e484000e4039201c0c1044001c042c201903500d5115070f00d640b203408800b4080c06020444080c80501003000303128054120078002c00c240c11841400c80c4150004405034030a0300c03146400864100242040c035480303039000c00f601c0f9004403141410302050007050001844135100c0580b00407008241480500c04c0700d0750340010040c540c101044448103999000c0d444284400829040c40b410b00001148001143c04103094940e00140400103803503e4a0b100d480c42c0c01c68031105000c1d215080000f043d50100003141c0e4011a0002c40d40f6a8520903962011200d51154940d80101a10348144003070120140c03002d1030107014a4400782c5502420900c40c2c84034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 114584595 1250 114583345 114583351
    0x1e05030c0f15160513050303030403020705041a18040c081605210a060c020106050d05010e060606070f0807060b0d030305074d0a08070615030305040b07030e120307030206 75
    0x1140b818405100040205088081040d01e80c0d05203980c50703086003000010600b8040c0c0c000760301408000100402c250380440e24000303440e011a0300300942410011b801c00c4c800340b81c0b481c45070401d50240300c0312510504c0c1c2d0052a807040c8902880700c1413548a100751400c1108680b20913403001107030142400709180000e00340d0002071401e41c0f182c100c02030740c020903590754040710800380602d9a1281c12950213071003904000702500000d00407520401c001c4c81d003103009080c036441c000c0040c012040482c3c2d0070f140030b1044900054020f0340c2c442c03d003203042d2900c0c0143c2d84130b00412078610380e5541d84007415484007050070340700c5c50081e10006010303c0d00400113000c3c00c1b00c00d503d00460402c007882d220729402250051460407024845c0303034109040e01082e005540015000314012512510020340208403c0c800100481440341c00e0601c80c03100400681000e144445c00010080b80040c8024003801c43c0500140503080d0217898001014050417020440c3e4900d110500308942d0400107450084c55010050b05070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 114585845 1250 114584595 114584623
    0x1206051c0519080702040f0b150a0905030d020309011107031a0405010e01090506070c03090302092802070c050105160b07020d020d0806090103030c0203030d0c020709271e05030c0f 79
    0x51904650f450911034415244001c0c4074a980d01c02900d07a0f850703250310004c80b07080080c1000e54054141c9446400c2600035100c0e03400050902d44001c5007504000c1881388001204c2e40086040c4190100151101d60f00c10500d098284a00306000004c0b03030701400d90182e045000001c0c620380b03041901700701e0300b942c0e1104410145d9a040542800c001880010500d0b4094101c0ca00441c071500d80346000c8035011402d600181d4070a41d45814800c014100600a00040f42c81d02080c1d00d0480d00300414009030702030f50f4006000c1d0390041104205a5024000900074840d4410140b46030041660318805540c03005c2e510b4100603070040d40341c245e016070100000e84c03c641032401c00c81514036100d00061000f20b0140030040c10092800c0b0f62500315207041065038202441d100c0240804c0e20440802591004148108402c45050a0a021020714429051003035008080c00c0701d10307190301e5526002150507680915104125980c1c3e50100403070810b00c0540b9042511300c014012810156007210700c1c00001c0c0030420f03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 114587095 1250 114585845 114585883
    0x4090618090b0606031305010e030c012307080c0702040905010c0305010f0b0304060e011401060309020a0e0f07080907050301110904060f06050d0e0313030b0f0702010506010905011206051c05 84
    0x1404240a030021903032000044503959174a9899100ea1815452941c00080096082c10030300702c403800000c4081c090100441008000640c5400c08409580e40404041034040165101040403580700341c80c0c50b540104444126460303c81541e01080c00c07150350240568580e5994150180490307490b006060042004e4070200c48440e0070b140444166100c040d10040c16550745200000e06e0f0715007904011212103611044200c0c648c2e4816002e03010308000a012442411480c0303000c580c0b602000c2c1618001c8031030354801c001c0c50f82d03060020382c0c2c203000c017406c14040e511402800140b0341d0340c2409102c00c0c0203014800f06480d18010000c6c001910903039003010f50032401d141d8043c44803e5010065a40c40c0c05600c5011812449940304242117101300e5501d0b031703110041c240010040c040d0400209001d0f040c8910303412102d940c1e140c0100d0803140d09a5032031f070000c1e400a000300681e41c49007020320329410000e24002100b550314000285a01d0006034507061200d8144c12017410b104080c0407446083d00100092 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 114588345 1250 114587095 114587111
    0x11060a0f180f140406030c1503050714070b060f060a1d0d02090c0a0302040306020a090312030b0102070b07030228031407030801050d060209030708061005041103010b07031404090618 80
    0x1100076a2000d025074408001c1c44510f40000c0d958980084c8000d50304890700507240fa80320702d90000303605504c0c0186800b0030300f0b050224001500c41c400f6800048145503442e41840200e903145048442d0184c500d0b903111200b4070303405d41250fa13000700404003c3c12075103800c5030035031004404006030405040001d10071142526040090380750460b04070380c0140d50080155844800301030a60084c000d5810107040148040350901c00c154119a6040540c0c5c0210545c815040c0554011000c0d20f00e2801001c1c010703084480c0070410041c0000c06403005c544a40190381680100c4844810310210b100600306039501d07289074150030705070040c2400081021104505141050b55140502010010b104013401f42d080c0041e01e4003031040c164159800040300400b0342d400150703034640300ca644203000e550003826000442e1000a0b1890944140b1407a0049078401c641581c0c6083d444981c8d5800801c1c0680a1200554519200048a500400c05018091070014245051503d800c81000104c480402101d20301040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 114589595 1250 114588345 114588359
    0xe090303070e03070b0c15010b0c12030a020702030604050a0218010f0506030c0f07030e040e010b0d02090406060e130b0f07020c100504080d1d0102030415030911060a0f18 75
    0x8595115501d42080035100c420680482e242600c19402260110300100d011040c071072012690958103e80c0b03844050040c1d8171101c84510a11859104442c1503020710850132101103500059503200700030744001414206281c000c0790500c40c00321011507042d048010740d00e0440c581b00741d122101c0641d80c20b03801c5066042240403034580c1045e00801d40700e22000300001d020780d085c02040f59103200c0000e40c02038440103030740b0300502000c2d0080f1255210380d0504418210020052081e02401d1000a10220342c0c80d01540130710605100140c020b0b900980c445001240e40ca140343c80701d90040c6144d082c8441007560500f888580450050030045400ca469414001c8280d4000390600040ca4100d4010036094520141501c00d40301e83c1d8041c580c580030316250141107640002c036280c5504601c5040b0342c3e030281000c00490300c038881c83c01130f4104030b011b070307061001c1c403078460703800840f00512500006a62308603d100164070341d0065040ca10003d0180d07580403000c00e070302403450051500045044c0c0d0213030b820816 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 114590845 1250 114589595 114589597
    0xe01090519150519060306020d0608011104030611070c030302070e0a05100303050c10110a09090e0706200303010e0411010305070813031b080903160f051002100e0d03060e0903 77
    0x20040581c1d0301c443c04035080d200e130040c10f40c08000c0c0d80c01d010070480c2c0c0c1e070b85001c1010b0b40100904141180c40c0c080c0004411030706016150408035141561850182140d0b101001001d00200034580613400341b140f40b001a010b112504041c2d0f01076002000700c64508180a6601c030402080e014072613040070140700e02c0382214562802500c0c1c0c9400e1891301ea201012850b07280519100013504003905003580301c482d851300e01004201040d0180d07101200c0c00e48a100c5d02d002d46406520340400c90b48602e0f02040300d03510900011000c560510507031050410a0213503645150401e03000120209075030300c00c3c401000442c40800010141c04e0070180054946460003601d698802040310713403183c840311140c2d41090711070790100f1440501071910980325100c2c0c0c201002c45810401c0305c2e60281c403c0b0341d4801042503807240301c04120b0b0f807c0c0c41c0095806003410240060b00361995400070a43c401ca0650180d50503160084000b184505002007044090705140181501c4065001000010174041407005000c0044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 114592095 1250 114590845 114590873
    0x1e02030703060c030f14060a23042003070f09171203070e0a08060f011a030c0906040b030f060301181509030e0306090f010c0e010e0f01030209040e01090519 69
    0x101c0b000605041500b020b41c05040f601100440701444c0c00b0758000c4100038289054050403040d500e070350103251901c400040d0700d01d56140300400d500c01c21140340c00c14601900142c01610720f818582940e12510440d5a6280d002176651070701054403182002209a804400b040041c20101c214844121a815074680c840300350804a600c1d1070000030010701e52034000c400102c4598009822000c4840d503441d030b40e42d12564107407070812b001e8102c01d00004205043c9a901e904901014003034502e1920740001d0541c3c0c2e03900012805030405418840002c0546068015511681d4101c05440e0145043c00c205400c4400c541541822989070400500100310340d440951254242c01c000043ca8020038281a00d0001d4041c4805034035101c1d50080209910300816403076a80303400c000083c00003020a402c01d079000681c209685000603004c0800846520b00013285031101c42042c1001031510b100d507800719080d10003000144110341c1d11941404204039042010114404840141c0d003074550300d40c6d8445560301000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 114593345 1250 114592095 114592103
    0x507020904030302040503070305030d0513050d08060301090b09010b0102010b03390d0f0309050307030206160c0b040609081011120403020c130c20070b0c030c0115031e02030703 78
    0x410006003054020b90486018103030040486e08c0e01035507403400955a501c8803103510441c03407d0501040400380c0b00004400b03120391240182007403000b6107004840002000f031045074990349854001000c1107c5c414034074000c0d04600008603081c030400c00060701b03440d01205118003d40c0041c03c515048004490408403589031885152602d04001450b078085545501080d54400c0c00138448000708110113030a40c0220b4400e4480811596607001003540360b2a640c4000f80d00103c04009061060071800d05c05810030f480b0b6003560010b41e490319000807035a017294100b0401320300b0110041c844224100305038042c1226108091144000d4424811818090b500e220210304030754101082c109402442031072908007001c1d1040700300700b1400005101805c048410341c4007040d04000329072510352441080c0c4180c0a180002000314510301715100034150f0203070345c071005070340010300030100300d03240a0060031100704800d0002074045096041004814100d203200c5600d00b000c40c64282c00503100482e001040b02d0704 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 114594595 1250 114593345 114593359
    0x806010903151d01050f0414070608010e0901180804090e0106080a171c06031103060402090f13080d09050d020f0d120207080d050117010903120b0a051e030d0c03050702 74
    0x428a10700f14030a078000741841c059420141084910401015800e110324041c40c0140b0035a0301800000352550307914001d400005480f41c00500c80c120b50f0303258141d00301007084000144102401e815402c54142000220b418600001c0e0410801d2094041c0c100d070640c030070000b000a00c1c41d10248503594134440e100180021351072100340040c1101103003a034000040c21284074a031079204241c85c3c0d005001501007114481c3d038055064101317050000700c440c45540d0103003c0c4002910740c2c0c20302d81050309000b8040c5281034002d2600c0000262000b002d081510714004010813001103034500517003880b10750640002150702100d24100d200c0310000d84032600404a040c5084203510079000f00c0040e104242025144010014100040300300c5507119a040362500c880021a072400348d0300903030a94041d414041c000403021509107540300e41c547d01c03048000000500540d1200e946801181c03004070721885403000c4451081d0600881d08040c010020303482001e00d45520383c01c0740c5990152a40c098550060b0003149 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 114595845 1250 114594595 114594611
    0x41e0b01030213050d03210603050d050f120402150d090b060f0616052a030c030d14090a1d01031403030408180a091b200d12020d0c0f080601090315 65
    0x400b4406040099042d100407c0c400b20600064001411040c8400c41d0940b156641e1203107601e10690540b003000322411400c9151410a070a20114a40d0203482a42c0c007d22064401c10710031016002814034004c02540840c20140e923040c903003928034000709001d004182d9071200b6020384c1e84500c2140c40092078031180301507500890901500d80803002e40456400100ba52011501140322000c0410410003201141c1c41c41080741c040c551600e44090700c02740406d101406048641201c48003030410399002400d100d0345030742d803500040804800740c02c0c0b00311426204401402480ba4547c24000c0e801155002540341d410556035030005417040c11034010b82c03061274051130000c6607510f400c1600140901c070401c1c003c051401d010380f22003018080c680303c04150340301d48151403044001038125081d241040504101c0d10398100a882580c008410130303000c0c1e6401c105141145c641440389a040038095a10300c101000003040180108002501090600a0810042000401c00c1d00c10742d51107051403402040c003c0e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 114597095 1250 114595845 114595847
    0x105040501151b0c140420030a0b01030b1003060e09030a0804121803080a0906030605030c0402130e040507051e0f12030408070314010b01091a030c0702041e0b01030213050d03 77
    0x41c0d0208402050000059000a105c54855800310340005084404011071005070100050740007000d5820859401e050000600c0318009030301200c0c4003201030401081c481882c000060030b42c440c44008a022030f6071010140f0601c0d0000c229594030084e440300079444e0614401c4043c1c00780c40c0040004000f09907032801c0071035061103018040d912041030001c80075190341b6440c00e015030381c0158608100194103540d00140540c828025030044840140240000c903078581c060001079406208080420001c00d5400500348032200f24491040d030040d80600321103803d01d0100316060f242c0c0c1401c04a180803904000240e0394502c0c241900940003242c140825442001460b8254084c0f81d000d0421405030500000030b000c8803c0150b904412200002c1122901c00c100655040c1c0e0340d030040650070401e50314075010101c4544000c0d500900482099800d090380d603800207043e41d2490450700f030100c00342d070000a92403115000740f008107142401c0a504005803003480d00c40074840c51003903501c40d0824203020400c0c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 114598345 1250 114597095 114597137
    0xf0609030a120305131e050309060a020d08010f050112151214070b16060e0313080a0209060103051504050a09081603020c010311030f06010314100509010504050115 72
    0x8120280c207848100505041045421a8010040c004682844c0c0001c50080d00c6803020258103500101c889908032100c42511400070070500704a9540c8007c10072481c40d6070303d890107010820b2481c0d0050000741200240144081010391004481603506074003440281e800c419080c0002c00d41501c0004d00340c8000c21118590025175000a620402440f140c00a0110580d003032000344001000b1650300950300c905031500d40c4121611102c0e4003000011080016040c1d40001040174507040840341440a40d44000c0d028000c1d50380417513040d500800d800b00c11030800700e03010390780168242010021850204821070301c038100d40b048140314035a1180020075884040d8021a140794004100c1d586440ca04000a00c00704442d40c0f0540261141e110160707003c1d84030b4080c099592026900460840e01c0756070075001d81c1c800c007502c07541c10315841d221110381c4050b40103140c40c411029644801cac9803d11f4001405084181038101c1401a41848014080941c1d000c554140045003031501241000c240003000442d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 114599595 1250 114598345 114598357
    0x311070513020c0a0803011202090105090402030a020105130803030a0504151a0427050c0a090203250e03060c040f0f05100804020607050a0609031707090b0d06030615031208010807050f06 82
    0x2c4901c080b0010400b2061800c0da6808c140c0300755004419a62a40108009104100e40003541648400c03950300c015482403001d40900c0c0e69805201c0e420b1503e5084036410b5800032121a411103a031003040005014a08103e0061581c0d003076004c22104040b488064110f203407044800f8060398450702d0312032145a0b56006402c0d803c0e541b12a40a002405140c0b0503141c1e88030740c0782d0310301c1603400300000b0908074520301c200ca0262090360010580d01c0310040c0c02003002020100b0803028803441c913049142c191802c0c09010b100c0c0a00301050b0f40e84a040c6100c540030000c09802800f41140d400d80306001c0c41c0c955800b59aa1180c590802d4001603883d407000618510440030000c240e4042c04098108109a641104c56800c0c403079121040c8404160105d050242d0084a5510005a00000810080042c2c0000300707500b0302d84443c0424500c0c0c0304d454060550b00d8081c12501d00707240030401041800b018580707520341c050301403810f220154500001c059843d80203005151181c0580024455569505422520 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 114600845 1250 114599595 114599603
    0x1080105010503190e010e0d0207210201050403020d0c03020a0f06090b0c1c02010606200a030c0203010e0d0c17030c120a020d09201f030f02120f01030311070513020c0a 74
    0x344885c0000058041d11078a402e611152150703011112141e4000b24601c0f0555090000e801e021305400960101500d9428a059040c400100030220150302c4010390b90303a5080c0511360007002c541c918810b00c0418565503003c0d045400c0018424020b041d0311413181d004413107882c10800e86480705003c03a01d0a0840d440010b200511040046090b815010340241e01110903d44402c01c5441c40c030200c1706c0000d040d2301d9170980c03190880034000c40000d0280451159482c0064000154030300140e0440d0314001008541e1408120310030214010407140100352135001800311015815070601119280590091303001801104100b01d000400303900c8258151400b95415507000c2c090a1018100340b081e806118100d0031202500030480e50700c9050060071440c1ea181c1e041642c8846e9902544210000c00c0e22800e01150960200412048040303081d10040c068041c0a030040c80c0e0b945140380140015803001007012140d045030a0410031951081b80411460003140805039443c02c080e080e49040c681300d074800034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 114602095 1250 114600845 114600851
    0x1051e060f060a090e010902070c060302030403180801020705010b061305010f020f030a03020c0606100807050d060b120f090f060402121f0209030c0d02030304052206080109020f040b0108010501050319 88
    0x581d513400031000d0202c0380c0310205043c050341ca41ca004016489a0140a084280700178001c01c0340d20704c00c4e401107a025000340351900314082004400c00740c182080c0c0c040d030314607034021034070b0000c1c06020300c181d5010281c03c0f5002441d1a81c5540d44190720110740c4101810321040442001c207a50090040340c018605c484180c0f41d40d03400020700075000750895401144076106d000c001900d507080010001a40d035105448518080eaa005c1040360315502c594903041d03c0c2510b030070300060900c06120141c55010801c5107251540d03c4d003e0184103803103600400c0d29402e0703402035101d08000f0801103585a003082d01611140d6408034003285507840c0820b503102038084100100805006165182d014203450b1100310b094440c0c2521103410425030400c000340c040e5060f04200401c02580c42c00301c6200d151054410400b40812074078070800002c6030380f150b00402140c1d442c0c0d2019021803030403a01503500d102003101c040020207008800280001350500400741800300c004080f8841c0c9550700d00020501c10050002c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 114603345 1250 114602095 114602107
    0x40e06040b06061e07031e02030304030c11040f090f06110f09040b0d02030303090601080f030408071517070305060a050d0816050102270a06030209010206151f0e1201051e060f06 78
    0x14412030b40320400e01201d01c0300e807da4008403440032085901407505581e41500c40c0010391504811041c2c56074500d0b60140e0b403a100e100d584c1c0910300410006034007850f00030403002585c0c01d0000c02d9820342da40114625804005000ba8805100240c0704600b030182e80004481c01c1c0d0101084200707482040195041c80040104224100c0000d4014140c3d4001003d891240101c1c00d1116940d00a41c00f8211540d080050103101d140100c254804410407140303000969400c9180a406d1003080565503640020780340c1c4200200707801c0c013081e4000141803c0e9111000160b1a4440b01114011501c10008a01820400006000d0f094043d16000e5008007014450b100160480304420585e056800f401105003060001d4498001d2003540c04424060b006809140d48003900056040d44d42c0280700d5200c1100002030b0b40e40c00c44591920324220702d50b00c44a211403200001c121403440c0e18000c0340c03810f07814403040006175138080041184040c3c4110b200300407038076000c00159400000c0b00085030404008039070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 114604595 1250 114603345 114603347
    0x200a050c0a2706032a060302090102030d0b1c1208070e060306300a0b060901050108060603042f01020f0703020f0f03010905060703050610021204030b07170a0b040e06040b06061e0703 80
    0x4018170454a10140300c6115919801903090b40a504409400b6030002d00800c0400072071500b00e41c1d84130000610114810108030046250300f2034074107007035912191070030b88065040c0e08070000640190041c1818007101003841d00050451100420080c040c801e2451004040c42e000c82844402d41d00e15605841c840070044541561070303511403415a5000c0260010072660b00f80340c000702d81031312010780d07552405690303200c18003030580c0c0050002c407800c2d2242040020b844101d2081000c250f11400840c0000b2080e0f1000246061a1482e2260781750700303c03143c1000140d8910010032070218059502c8107600400c0c0000900414069002510500071081080181580b50b800948a502c0031500c0c2e4140c104648012030380c49408081a8616017404c2000388003107000300d500f0350381c010031034a000201548a0300004d003503000251201808203494610300041c501d0305000d85c60544000c000140315a00c3c2c2900c520281c00c00103400c4a02444000400c072220400d00300b901012803181040300c59440c001c501c0c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 114605845 1250 114604595 114604643
    0x31d100507030c03020c070501030b031c0c0b0f190e01060b030109022110050913021c062702150903071404050f04031e200a050c0a270603 61
    0x181650000b842c0090b4510142d004c1c0c030030b5806409014004281c100d08110040d0004c020440719940e140c410100e24044881603c210b180034155141e451a030801d100d4130b8140c1c4007050180c10000100c100320f003084804503c035000c4c10038064030300402080001c01001c034680107100e81d8202207409440000041820340355500101101002006640310100e0000609619135400391440c1c00c502540781d000300010f2601c0400150441e80c803448950f480941503000829078503030b0301c0714080038122200c07402085c01542d126000c590444845824001050a10344604403403801e0b400078491708003030034452026001482920036251014080728a4552a0b10204e105080d5070740b0310700d12031410725000482c4001c11030b03000e6000d642e0540310240c5008084581c1c10000c03c43c03c0d0b0000c00c00c1340d15800c0081d0b1008000d694181500a0800f074800300c0500d01301981001480e8030f20350f000313110001080094040010191160380d03180105002924002e5000c18003600640e8400b03062862044088000046041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 114607095 1250 114605845 114605851
    0x905010513020408060a24170c0109080c0607080706110304060f060e010303050706110409151203020a1506090203040c0819150b0f03030a090302010f1707031d1005 72
    0xe4050710380600c0141c031201a8441e5000340358158014801142503201e150b04201c3c0f015955071088032440320100359806060388580e200b1258042003030700d00103484030240040140c01500386071000101e03050409069858505980e014041c0c0c400040000510900c0e4040c3c0d80c0c082d0703100f10140144a20383e1404041504113171801d0f1703440c0d4640401200c0c004003c0c8182802c5685008080d01e441c0e18548046e5101d411a2505644260300c07140c24100c000ca28400030805001007000c0015410484034188007100e030f04e0341040c5151180c00b140e100120f07400084c050605980072510740d1600341c00368141300107460039501c11006940088107100820101d03a850314180c51400044075151504040a000315121034000a00128484410140d5012058200601c00c4c034014000e90510644400420702d540e005045500015520314000c0c41190381c0b000c0c3c59096980c8900d00703e441085103910310340001101034000300a03d03940f070300510321360040080038410400c246010f0f1618280000500e0010f40011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 114608345 1250 114607095 114607099
    0x6181b0c1a0f060907080411121504081b01020906070b070903050106080c13051302040b0a0506040e040209010605040b0d0203060f1003140c0f04050609010e150d06091806091b09050105 81
    0x1a000181820706c2040381603c607036040422070000c8148801400010100c07840d48001a02421a84620700310400751090b005521541155640741e00c00d002005c480011000d846580c1c1e40100311030a1f240e50303024240c5140316041101c082c00c030f4035484c0c0281c404201e203520081c501c0d401d004000071080d402040d106404031303043c0ca0840e0440360052084040703400407242c100447c0c841e126040c0241c20641d0040883d03240280c5038001081e110300000e009508103a0004000c035102c50704010440c1400d00e03555006003039a007003090500f800c00b2140000307405409210811940d0220000750740d541c2e515147c03400030a0160280c0d86040f0300c050f004001d802c1c00c16100002500342c81c003240411400700308840d41c000700c18004500301030811003000002c0d440240c0d4241049040f040f4180c40d83c1d00c0311014540c05148074181d580d20310440c01c09030281c50940e4051101907250803445400c0300300300e100d03d4a406900c00d100013012240343c9084402c120904868800500444001042400060b131220303050f5401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 114609595 1250 114608345 114608359
    0x15020705031c0206070f021f0905010b0103110703050f040515070203010b01110c04020d020d02040f060e0609090103240f060806150d0308130203030d06181b0c1a0f06 73
    0x1000340a00000b4898000c01030042e4000e000103801103101c0c3c844e0f03902803e0548140c550403590010380a680c0c081047c06005226524150602003150034810700d00c1c01e580c2030800b07008407141010001f280e030045100181c02d21000084161034104e80344200e9001e00001402e4421110f0203030510318160300082000c9010398039000380560300e503016411800c55594140c00900341c0044a00030702001e9080119294103554080c01800c002c0602800900f0281031000100f00c5403d152040041410854022540c007a800c1009103102c1c944500f404a81565004030340c81041503c2034403040d4200c0d402c7c03030b024094140780c4400500f40b41a540c001c941140e0a100450346103031141c1880c0050010400d01c0d15038400508913407400000d0180c1900b81c0c0c407800310000c2d415190103d401107411584052550a2426070b6800c0c144142409029000003070503d1400c100901c2c1c06030341080d0703a0f901c40d480c50703c001c0c00644d0a40600b0410074840101450444c14207460103428404810071078441c0c144ca00703601c0785138 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 114610845 1250 114609595 114609613
    0x60504020f03011103060d08070c170d030614061b0a140c010302030c0306010309050f1c080702030c0a1e060f05010e0c070302030405091005121b0a0305060c03101502070503 76
    0x3405001d80b001c401c10443c1090f140d46c8943c8104001d204191030219034504041c000c00c004a45240001030040061000700d4400520950109041c01001250001450316280b41030125403840000010280d80c1521140c1d40c0c1c03121086d004a2625030f0340c00e40130071849a80168420004154a0104c075520204100c42c0100507400041d400e0740011280d51541c0507081c000036101758800d41022441c20b0240080c0c0f042010360922030360801c40d0141c80103102c0c105c2a4680c007078060707100039140d40c880384502c05142480c48142026850307059000c00940302000306004a80c602071400c00300c4510326407050b4104948400101d415011702401d10918807241c407407000188080990408450403180d150340590f260500701401c10038146c80282c602465102c1140300030a95446003640c51074400c060100506925643c10903006d4510110a5013a00075420201d041000600003d03007240c000315010b10950322641c40301030075580e0700b003c1e43c401c4144c0000c0d03a00b45210960089258402c0d604241c05482081d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 114612095 1250 114610845 114610849
    0x80a0210060503010c0509060f07022115190f1503031101050c16061509050408120115020307060f020c010c05130902120402040207030c06020406110f0d1b03030b030a060504020f 78
    0x30b1751203c9907101103042000020b032145800001051200d0f2075184003401d00b410b68020800d0301c1100c10762203520950320100ca24030005e00b04004c0626140c1e1400c501d886181c850044541400d0b41078070703a001640c5071b0f030000b84041040e4108510034140d515441c0c0320b440e92404c0041030a032001e50400c800354a440040f5040d0741c4000304035214030000c980c0400c08080e10f5940c0340300034044000480c1d101d9415101c0400d00c003003503004a6005600071400030b501c410181000c2080f40c001a44003c02e614802c1420400d000c3d0048281d5005a410101c00503005c6400044040a8410401081069442d0032415001581c0120241241305940e108100b807003030700c55150104a00c20058070b41c44d404852000500181307443d030000c2c4007641c401d140000684d8003965510701603811542003030010500e00885299a5042041000182c1d41920f00421103054800d03406480c0007540008610a494255600d00905019030001c10318040080c0443d68a1451410442e0050905a804070f10130800000107103414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 114613345 1250 114612095 114612101
    0xb04020a090516170f040f0f080409020d0e1c030c0201110a0801081b03030405060706150b040602010b0306040807030c0c1205030901031d06010e0a09150504020f0a0f1203050403080a021006050301 86
    0x144020200c041d000d41b00c03903e5100c1209007442080300c0400702411440d00007024100500b00600d150301026071600703901012201900c44030200d551490780f02402000701425250f100c142540076504000803440f60049049000d800701c881c290340e000d0b170000741000581da403040d03e280c100d650403015120514009416900c1d0685009180c3e54164402d00080c8143d103028030082c68028482c40001074000011a42403900740c40660000054400101d0104034441d0280942d90350464202c0c050b1080380f9217503464000c40d01403044080d040083d964111001c1114a80300c1401618000c41c8286092200b460f1450340c9a01031002c850009043c40326016000c1c80a007140c180024481014003001da00f809410480c0c000300400c1d900c0700640302d54101d40440c3c80c41c1030311015200944004980c504e45030041c00200d60090801070b004000d0b03920b040203604034000807002a5807004d600c0306445459400c0c110756601464201500b441d100003140e00c141900000c08000400350280c091121700d07070700c908142c01c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 114614595 1250 114613345 114613351
    0x91905031909030f02130b04050403110706020106060813020a2105010606080103051509120f04051c0206300a0504140111090607020402070803011508060d08070b04020a09051617 78
    0xc8003002d413040c0c010300d072450003050f0211090000286844041d0001000e81c3c1c400e503020740104071b018210340702c0c00d4001c1c0b061002826546c002400b00c1841d1140092040d03070018000c085c3c900c101d03065041159a50812403005101441c1100400a14584186440381340004119115071a210700002d456004403002c80c1200e8001c400741044400180d081d100d44040104030311428020300c0d00548611a110b40078254032490508074948030342c206001e0050b01c81c0038403400b104411080402c0c00c01039070f0314011250140390320151031884030049907554400e001c06500102d00d19a943c2d040110f1041ca80d441584900d000f140c07031550401041c84054202c6d006021448c407608000c000c03031889414420000c146040c070141c8014030b416050744680c01c55800a800c81000c1029034481068038a40c0880c90341e4100ca0102d4070070741005c95603a58103000d0302c54181e0082c0301214681c00a0150b6852181c804024050703900700b4407940ca00146120a00d010440f01c4001290124225140c041d00700410148 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 114615845 1250 114614595 114614603
    0x10e0a0515060309010e03040603020c0601050301020304080a0c080d060b0901120515010c02031504030801050a0b0a0206190e0703061e0506102f06010f0504020a12020309190503190903 81
    0x10100d1522020300c8102d5000400440c045e40d00c0710a07240755804100020030041c961940c00607110401080c1050801606910041c840e0f8018800c4c4004030701000c2c2200c1c10f03141d860414545041c4c103840c25094a00404c3c61460805280000004451403040c0c010f180300903090340e80200740200c1c1032441041b44d200f80c0d0700e0281d00125104e03e5426501500b8a646070900041c102c4401b04550700c0c2d6100c100c80704840850019002e00d004100c00e00b042e5104c0740c003420117026804d08060030160020b54801d0700800600c1d02c00d08141010040b90003a0b8810345603803040074242c5203072984070304003403025007040545135001030010340344900500003520410340030342c030000d0080b8550201c50004480c4025484c20742c064000d1140c1c900e00c418604200c0328002000b10344080c02c00366242c0302021000c9040d59004070702941c010040200711981c0304a00741d906022441d001030b280e0303c80412591034221100310760500700007036001c01b4081c071800202403c90524204d818003440020810304032052003c13844020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 114617095 1250 114615845 114615871
    0x3110103051302100e1914061603050a0302070615080d1704080c1905010902180906060d03021002130509180a060b01020114010b03061207061d0303070812010e0a05 72
    0x84010b141c1100030910b01c0c0201c0c902804850000703000504001c1703410114002c40441e000041086c03405080004407c50000c07522141070554116201003450301c5580014104000010810b01c400d01a50560b0b13092074001e03008002c405510346400c0c0e1045440c0c0075000341c5e40308200b045002c152041c50345100f001000508a15130352215030b030b04040f40d00111071540d20707030013400039140718012a61654500380f8080c1c8004100d44000e4010b10598007152130b15403145031407890401180c908001000c03900140180d504040080044c10102e0501040341005070300d540c00002c0e070712225100302d0490802d840301100c95200c2926400c00c07141d003030f15100f8518002030b0410f00020001c074501383c0c80108041c1d410700000c5a0311040c0c10704421102c000360800d42c0403a03004010f2101a09040600c82c201038038400061030201e0400320041c1c00d0002d24a003600312044074488624064409000b40d400d0031b0703070151601d80c55619019041d4035805090040b602188643c40010f003150459002c0d550091250b00f15032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 114618345 1250 114617095 114617131
    0xa05070b011e060c0507090525080c0315120f100e010213051504030f080a0315032607080408030403140105060d03080c090d050c100804110105130e0903040311010305 73
    0x2d9920ba00c5031030003614a070080340c10010302d0144c00c8c060a803054131805500008501d41c4403401100560704007426080204080811510100036001c803a007000307452100c00307014427030100065942c1c2c015071200081401500d0481c441c031940090f46400c0143c0d9500d0900014003141d0075a0b08074014809441c03401015030318208a141025038040c0000d0401840082c502501c98941441020001d00121100d0f0000204207488036414803910720395100d0124003240c86451a21040c2812000c00010380c12901034541c8020010104401c03500c81c6548440c81a44840e03840d084142c40b0340080c4000c1e540c0e415004100c0407000c506102d413078400c00d00205038514003061038500316107020000b00a045501010040e06c0c0301ca5440100301007105110781f008161054182041c007005490310b42800092040b40c3c3c0078407000502803200300c0c0c0005402c0c80d003180c90706054418848076141075840345089452190900841d9240030009006490040740e0300852001c0007401102121811240b105103008000c1070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 114619595 1250 114618345 114618347
    0x3040b04060b0310111201050d0b0109110c10150b0a020d0315170c1309020310090503090d0c030c06210f020c07060c0209060d120e150a05070b011e06 66
    0x21101042c0d01c0903046491480d501d0001c28119841000050040000031070031007401010842c0e42409032200380c9060040c00304c03d40d10b8007a220b4060188813a06912249980701841e101c0059501d03000001c412a408490f038155100010603c1588450000b10f140402155905000b4102c0d99191010380c0100b000060400c801c900074031000c03000d0841e4a04d100e80000751003014a414070040ca07801c10141216034000f40c20440d200c0e0385600305108281c1415445005a940070404100b080c04004c00410304e40d00f180380c001c2c203501c6400c0c1318030360148401400c4414000680d1240040d07910492100280c60345511064604112418200f0303e070510880d5025207070038994001d01c5098080080150a10421a45003428150386400001c00070b000520b4540940c40d2045890350844410344080c1d1400d050303030701c0741c040824840b0504420700840704100b003200d84134035451b81001420101011340341d22180300003d2155210140a6807109800400404c1010320419214601041488015101460460 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 114620845 1250 114619595 114619601
    0x402060304030f0c0206030a0507110c010e090402041103070801140f0d020f041409010b0a0f0506030f040507080613060b0102060f0610050c0102190f0c02010c020f0310090305030702010b030303040b0406 89
    0x500f003008200c0c2d8600300180c0f107210140d03001e03214812011825207001c0c8801800d80c512034040740c085a00810080362283d03040440d1820b0000d0580b801040c07603413140040b4000d442c4490501d15903900000030080d00d01c4e80401082e050710044050340c00c80740c0120382003050100000f0906035000400546c6c0e80018078020900412140010704045100340d400140842c80603800c0792000d030f00c6c3e51603400c0d030b03032152600a954070090444007042809560414000c04c2c05804010061141030328140d0214091081c100000d40003010038400701d03925440c00400c41811000460b04c1212010b0030400c030006c556001055640c07003113513644036a1815640303900800142c2803600e00d541052017810001215007400a00050000d4003c100d00b621451382450001072100100c1c40440d010841d410031000c0050380c2c01016100141d40448541d84481300800009007018492007603440b41038031704150801019000070245109200d5a0001c220f140c55050a06072284070464004084220341800900041d50681c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 114622095 1250 114620845 114620867
    0xc030105130b030a061b18050105030702070305071e0e060d021e0406081606021209060703170a091407081f090804120b011203170705090a0e0105090f040206030403 72
    0x14041001810b21001c01c3c1031070450b1806030fa06548403120f80d40d110340d920310310101c0c000b064030300752491511405804151000c43e008450400400002040d0524030130001d9101461704281500e5450365600e40309003684071600e4500540b1104044000340b003190002c230780c9105490161803a0b20440c1103900b04980e1680c4180e0074040c3c40c2040b2005034454580340b089074041c0c40e1110050a044441e0034514271626003943c4000115480100ba6400e40d0032031006503a840a001e444139515920b0600e0240c07510220401c42000300300b01e071030400040b0481500b040c11858040c44c1c481d01d144400c001400d4079440140500782403640101348074a0844c484846510341025071100000307141c3c505039514136640c1d105600540c0c05000c0e1010550602000240e46c600520f081001c0c1a00004540e4010700a413804c100340385160912640000c0130540580f040314401c003401000b05009070b40794040c0d594019020700800f405040f0341d0b0300144146442084980c007a6030006e110606542c0d0381c0c1c2d01211024601 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 114623345 1250 114622095 114622129
    0x901030c03020f0409020904140915070c08030a0b130605060a0503040203070504060803031602160b130503010501060309030e0901031106070507030f03030207050c01020705010917011517060f0c030105 88
    0x20030a064a480303c11002d400605881c00c03000d42d4905800041105035215000180b46041000007803100a1a0004224440601040d0060903c1d41d4020301a0b590020300c1c1c03005008030000004210329110668001c089101c0c00b181c1e011f540c150080444401c840c598051a07420210402c0a940d50701d0040c00519480391000f002c480707a042c0c90300040703001ea41c915406050103520100034810142c456010880e00e41b0840c0c0300030f1005000c00040845c0002051007002503818001901c0b040c030101045ca0100903080281c000d11082d43c3d20b0b1070080c02495658000d0303002072500207030740d0300c0743c84c0c0012000d040b00c1d0010b446800212251f02017124640c440f0380304484d54410150000300042c040d08410a0b00c03802910010303103800507414803e013031807541d00c41241103400c121400e02440c0c0c0c0111900c02900d07001e5921100c0b07101c180000500601220307000040c500120708002401050156410040714004402d0b541603845542084107440001d60301910044c06c140300510007400d040c4403008600500e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 114624595 1250 114623345 114623347
    0xc1c09020411070215090102030409020c011409100609020909071b1703010515070b220206190207050a060c0f0215030a0504030f0c0201080103060b06071208060f04020f0901030c0302 80
    0x195a00090440c0d03504a9810049840821440150700d404c8120304408044001e20501d002e80d00780000b916441180669003002d81d011030f810b4403d01d0254816442106104140b00c0342e0306200500c00d41c4c5840d8602d50181043c1440b04c08208a04103000341c402065018140c0215034407825015140c070120003e41022043d55082c0c028040707504650008042d90100360301c1d503565410001404a800300801900c07424240070020070000648100142e03a0110309048060b140e0054076031030302d01e04116170700c01944c04080850f10254406000d0b10b5620b03074903055000c40c0c5c016a522010b02244000522403000440c48805400011990900003028468401081c400d000d180c0526580081e4105407a0205c026945000f01700408d50010801c0010502505001d2104d15450b40001c00e11007050000401c06038641c1400c2c000758031542d0070385920755070050001c2c000114640f0000c01c83c9000b20b4031503104100c11881c088107420a8400c0b15849014265110302c6d00c01d02034015000303404c01940315020154 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 114625845 1250 114624595 114624611
    0x7050316030906030e1009020f0324010e0403021f0204090c030b0103050901022a0c090403020303160903030504150c051905010b0411031b0c0a030f0807080c1c 70
    0x500040600140c1a1500c6062a400303003030040c4940340c56000f40c0281450305010444014002a004c0f140c840c6900010803583e01600c04220310070384000300c00d5054801d0201c00d46810f4500751003070541c44000c02c6104440da03610300d003030a2407000a07079001e009a08003003690000d0700d4101c1c03548402da1207c2e00d8098541542c5843c903804031622150b10fa000255500302014966078180600c0350021040c0d4001d43c1085105480c030350098000034a10080d2511403c10500b0511060046408a920040c40340c03006d032900e0b04000c3e44a42c001c64117201d4114022800d5001075009490040540790503580c1d4a0416060030050034014070b05d0f05444080c03041a081c1940052400c03c10912440c040e6041c600d0609814038100307080d1400b00c81c0961095050405001140d409503007942d030300034458030403807c4d00390381038900404603c500114040d581c0241c40343e01e07041c541c0041d11001c2071000783d41d42c1c01c034a5482e45401c9441c00401d46040100391000c110490b500e01d4188244000005807000000e0104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 114627095 1250 114625845 114625853
    0x3051e09090103030801230102030901030b030705030102031005030f0703150b030114010303120f06031703060105070f0b06010906110c090c09120c09070c0506010e0a0b0603070e040b0a03020d0b07030207 89
    0x3000f60300c104c0014000c80b0045c00650300d0b00189008040185c00544070014000380040e40300c2c003a00d001c0504040d03565a00329074170744c0d00b080020700034040a0002c40d640e0410074040344001d2514003645019118130440a0518000010704c5011070f070f04002c00c07070141040307485a20090700c04c5c101403903810364039049000c2c0c214182e0002c20b4002c61094943c104e200c8104030340e503000e8551188a030f4007014034244d01000440e00103807211071420720040d102a6240c1d01d4000603600c5001d09034003c0c5c002c90605107604c04100308540014040d00d02621202c182c90b540740b00880c0d80c103a010020342d8850308550743d8002c003414a40d118680003d520954281008455400b00e404128200850991540010002000d030f040181c0841c1d080000c03071400c85040d29070b980341e40c5c0d920341041c854200c550318690000f80031904154850340000780b004110701d6580c2490f080041250940141d898031842ca01104058540340c4004100c040ba0350103001c2c4011a01d4035141c00306503180c020000401d0603001c000c50000a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 114628345 1250 114627095 114627109
    0x905010c0c0305010c08060108100e0c030703110301080307020a0b0f0d090309050301020c0601090506010203040303020a11010c080f0706060603061802030606090306071106010e0f0123061303060b0d03051e09 91
    0x1740801d41d403940c9483c6050313800186080c2010b030000c0c4003025406800d10034800c101c8400b40d403100c0040030843e5240c8880300c00b1402481c050a1341d02d00301c2004000800c0210b004002080c0d01070003203800106042d142c0d04820305a201d10784214010a804108084008800e500a003601c540203003031600600d6580c00109007640d010304074254058120000500942c500c5126047e00060203100550400b819039074003941c0c0e4208010044c040314140c6000720b869a1251980c203010690050000f500e400400d0301311802500410422039806080060210b14140300744180b8040710201020610100480c030030001c001d50002c1c1207030350030103001c1095030529201000101c1c02a6060343d14104071151481c01c1905008047c2c11840d204642071007400f5964035005170343c03810f454005048229206404014424010401c030700150060008501d00d081c4828890034081128000c00050220102c46400c00400d400f0400300100811014019409950b01d2010070300c2c04800104101391400e103105000881d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 114629595 1250 114628345 114628361
    0xa030204050118050108010605030309091312080f0604090c170c04060308040806010902030420061606050106020f0102040302100804260304060c050703020703150f0f0b03010c08070905010c0c030501 87
    0x145901d400103d0788280544100c50041c8020002000918240400030f502c1e07103d40c4912500c01d000d6440440c1d107131940704409030012607010361140e52a011030000034004a00480e10114080a54030014406040500500600c0b590024070324040782e00f002e859104041c2e1100c800c004520580101a48548403032061402541c061845541c589203044521498004140c10150701c8038018404d0000062090500c1848031107080444c0541c0c5d074030f90000c03d0710741c00b58007481a510040800d0b410309000e170070390000341a66070560a945008014545440c240c0c0301e240f0000f90000d04850520300440c0c8209283c0c0e0304107110b815014105001051240b607203043d0b400700040d00c80c500100703100801441d0f114a0034283c2c21403d0003400c000080d10b001e516045140700141c0040352140785001c03401100e520084c201101d040701000302035040c1c084000104130030341400740250710301802000024020602c81e8462a0140d0f111800340e8140401101c00103070340c0344103d90030040d920001c00002d03028058615 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 114630845 1250 114629595 114629609
    0x204080709090c0501050a140306040e060f1005010203130902030702070503030403030503151804060b0f120703150504210e06070302060a0f0507020307170909040302060108060f01050d020f0a0302040501 89
    0x90010075400d2080f4401c0d001d074007880c1809030802c200d40d100c41d001016415140b8110794500c0d201e503107030000b007005070480b01c40340c0e503007405540104114000b6038040c0074021030b540c41113819401c0e150001640e0fa0322420311510841500450104a80b2071540c0003036074844042e105403860f1680d1100401d1a542154100310301151009c0308018010243e200081c40c00101100c1c54915100c0003920000d8800003c0c3c0050126915983e001513903803151172046c0441003020348581c104c41c10045040d5100e0760035010031160b808207098800011001c900825000b650094895072000720000b8080490300a80f6031355200384507075545070281e00e64a070b10207010214000d8018100510301048c40c48211140034640d0615146085c0a204c581a4000b0543d11030991052051945480804101150340190000f040e4440601c0c2d041100701039020805078100d41c007c1e022581c0030340743d0321455145407a00b401116041200e825842002d49045c56206441c404080c144ca482030b07481c0d4001c101520803d030050701e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 114632095 1250 114630845 114630851
    0x703050607110a020f1002330c090f100e03010204141908061605071202030a02062202151c1a0603040203030414060c010c0c06060602011814010204080709 68
    0x781541e0014040528603406202500100000d9070004100e024140e1405000300c0700000c02c220003034020001c04c2c074081c0c01c5101107107401c00100107607d400a003604002003043c54280100d9809400b1030203a84840000070808000214104144601c501080d42c0c003104000c0586040380e19910b0078402031003d05030704084821004120b105105903109202413045840305040c404120100700400c80540000c024681503071004240d25040314280100c000203801c00c003c0c403800c801800d07000001001c079240107400782c1d0102ea480b03c0c000d460702d1407079000b140d45e02288030f2510001403502d940340d1060030360011081800c100c280010950f80d85201d606c03014680f981c0741c41e00010342007003910012101904643c000d1440c40d00d83d0110340c0b6401548600844480920010309143e5510000e9401c204441d50081008a038140d200429900390b40406450117450300401041c901e00c10f000c1c0c2c80505010102d1000d4480b860768a240c0c01e690090502c1d02d00d95400c0c0310200302c042003404008010403035401d004c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 114633345 1250 114632095 114632101
    0x303060504050f1e0a02090406080610170a06020a1101021317010e10050402030a08070506040b10060203090118052e0e03070b0706140408030405100608030906071407030506 76
    0x804102e61001d48000501c0d4120010021504240c151070210004a561520300e151070346038118000c0e0140d284981d902c1400c200d404501c100300080c0061094800c0015860b40595444072074148101d00071402d030b01c50700940050804114036400604101002d4903100030000b2030001e03620b003240c00054030f924101180b154208040d0600414922009500100811040781e000c40615a00e000300382403051016100c40000b010b556040c0440104941c010748550b139150b00c04d26100d40c5800d000c650440340c951801022880b00046d10803804d050710990b4001310f01c2d00314070400655002d91070311000500c640d400e50020955455401100c1030b8860300301601c06000d8184950030303044150a826020400500081440c03403940e0000d003140c200c41349901465a50344481c00e02202034121b007043d8040d0501c14005102c20081c6500c002d41c441d50086c2d00751182046034003803a409540c4641f08241540d03009000d043c08518002d4018103045204281c44001002d801c02100c0c241213003944190b139607070070040070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 114634595 1250 114633345 114633349
    0x110703061b1d0a0e041103030307080702060c0f0703210609020c06090604030f1422150206040201020601061103070b0103050c03101b0c110a170c010201060e0a05101203030605 77
    0x1c080c041041080c00d6800110500e00803030f1030f06806224812a51216a0100f000d02009075000d140360302d80581581d42e00d00c0e0031100582079000686040300103116a00c00182001c0b050015190080c1c041a00300c1e261046035201201d102c1d070001c1010075a0f200c10349001700700c44440e2080c4002400e1400c0090703120034807241920b081c0324000300801c0198104804020020381d100140314801c4401e030400c0a80001c090710660b80354084c40c0080b01c010007488840c0b0785181e40c4941100c2c03c5829440ca4841100c020003412a100c0394151002409070340001c0051180c0d82c080d960880b41c040b030a500320f034102116520b0303100503546c2c00e078002d171001d4020742284081800c0c1400715003a07080c01180280018540c2c44a4080300214840001d0100480c5040c52410880b040c1114544440000c000c0c2003903903103030b0404032881e0764a490a41c07954424160941943d50040c000e0004440d0110511100c0fa5505482d000c003908008064248001e01840041003117510700286542250007650001441414082 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 114635845 1250 114634595 114634607
    0x308030a0b180907090509060402041e0903081005060a0807140708070b07080610020a03030903090e10050a15050418060b0301090203100b090d020d02030708030708190c12110703061b 80
    0x8651078142c1451b0410402e4080054000d40003941501e0015500401001264130a06107014074544a41440c0c1d181e0b081c103034031408803030081c01900490060030340e5031810090303d07126821800c8049441d0300005100940508421113152129000b12454903c0c03c0d6100d00242d8000325080360803a461205024040780d01c030403500d601c02c034140c65420026a5010010b5540c20103000010304140c0c0300d403010010103200d107600750300805109040340070382d0914200350103d01c2c19034004c80740142016480002c4403100d8031120300b02e0b43c5c41501d4203444c09080084032043d2814007002030180c941c403800000b03195082c10b8010b5000b80300340d03000140c80b030800f0350790415a040b03d03510150004501f80500d00e0180d881c2a01003c000c0d40c121000c01b0307184502e00c00301342021341603440540300780000300b111030510a14078010b09551101084002c441c0c21484030a4418191440300a8034004044606aa80d1409070040084d030f00590811103c0c825502d64600c3c0c26920f00f0685400b203215841c40b110ba100b42c00003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 114637095 1250 114635845 114635849
    0x20301080c0301110415051201060c030e01030501060c0803040807080a090609051f031d010f091415040f03020c03010f060302090a05070816030207050111030601140f03010308030a0b180907 83
    0x42c02400360070014064142c180c0240d000b80362603200300410020140d40600101e4080e0000030403100c5039503a640101804180115205030046103012002090b59813080c480c50781030b10b41c1d03034031803013005007003074483c0711064100510455550f4400c000407400f2500d4040500301008503aa10b0490b800e081030300041a803001640711038050045001c010203060b4042a1412041c4054640040c0141c1500100152030740c0c04c14003401d0a5103485000d400890075a00180c1da01c9010b4860a4030000c4105030303060b070350407028500b2090100b5603404980000c014030124000c180c00b80c070440703541201c021f0020f800c44000e4010044002ea07100b00400460928008044c3d1002608508200034600014040d184440003001d02c200c3c1c6403100403e0741e07100e0103607055174400d54001c0d0007002040402c0d221071400b0340c0141c81e180c3c003040002480b860700d20408030440d6006041e01c101c4608603440d55a608000f40c102419104100d501c54044000c95241c2c5800c8070400d10740c684544034581480d14080d0304102c0740d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 114638345 1250 114637095 114637099
    0x1f0801020c0c01030b031c05090a1403060f0c07120f030c020c03280c0e09010501080303040809060a0917010f0605030714100302070c030506040b0a0216030c030909060603020301080c 80
    0x5001d240c104260100d0351488281c8207090100e078103200000000c0c1003160781c440101c116440144040f0401d54820003410614800b520b00e0070b0556110b0003c06640785080848075419031202c2c0000743c100d08007082c0650401940c548150801020307684001c6c1c0d813a600403075400012140c061550005074180205080503d0728000380000b4880440846d45448110032401d25102e40c6010f62900c4400302c02c465011140c00030034030503115071034400c080d08040c01a1840202503003008004252004003100f1640101d41c44403c981c90020082c0500c035140e0420300081090112008000078628a9100a440f443e0f00c07070800022800740300009002150b40907081a8042d622900051028140b0080000708501d4103c0c0e45820410703031103030210068441c0c00c80041103048040000400c0207000075105001c1c511401000200e580ca0300b010000300d0159600c9840c142c074140010360040b03402203152544150091828031002511400c241082e83d02a600a10010b5130001c010024000c00384001ca50788982 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 114639595 1250 114638345 114638347
    0x80a02090108162006090c09060102060a0b0a0906080f0d020606010207060c06060503010c050d0e030306010804060e0106030203010203090a0c050604050a0b0c010204240e040501051c08070b1f080102 87
    0x10100002c0c25080b000b0a401c0006000ca8600c9003071038040d400044144520300041a1068984503a03942c0324030040c0c5242c02c05110b0910000414a090f1070382901c60340f010390041c80285c0d1440198000b520041b074050fa0083d203c42000f0482d45840d0003140007411480c0c0041090b0340414524520308000610768400710f4100350140030a82ea408200c00e0201e403803a24120580d0b0303c2c5400c0000c0100500d50125a066203003050001c001504400644501f2a125000304050b4220078a0030b500c0e4841280c0c8140040c50b60000140000c04030f0780000181003100e000011016100d44c042030032a80282d1b8800720b0350340800c0c1e1403010069080420409020151075050400c3d1910000c02c0d002c103041c0c00b50782e0404101084070221740301c1c25810b0380c00a0801ca003907916602814071324650108011301d8140002041d01c14002c050f030034107002d8113048030300c05070100040700844010075403180c018031811250781d80304001c03803000f041e00307010401e01920075101c031205410b0080380c2401c2200c00e1a403281a190340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 114640845 1250 114639595 114639607
    0x1d1008010315090c120302070f080f0f120301050402160b040b06030c0102030412060504021807080f010506131415040b03070906140316110a14070b040f0b130513020a080a02 76
    0x40c410401c8003c4030445e410b840200d00c10745c0341c00c1c0d007032211503004081142d040c800006080d180001303a8080404d800c0b800d40310f0380b5180c1c0e8201c54680810b00c218421005042004110b24189580100200b0780a00c4200a040350940e8030b6505401081d10309484da2150041400311600d030034000000c0c0090240021880e084c0342130030113603c00583e0417001d480c0079500e000140035502c550f45128014254030303600301c259103001d820180050320159845510070402100201d000e00307102c000c0702c00a0f07840041140309949440059940d04404201584c1c000d403548406458404c41600500064140382c24400d0701c07450100d5000300400199401801000b092001c040401110001100e1304040e442c504044100240076042c1c440c1d01c2114904046485403e1060041c400280c000b40741107504202501d0304180e503840a0003480c015402101041e980c000d00c00c100800d42d910040108648044107003075601d941d1000070790189110500030402c1038001442640843e8411017050744910160f40860501c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 114642095 1250 114640845 114640853
    0x10309030219020d02130507030b04050108060613060b13080d050f07110409081b1c05180a05060f031005010309110609220902091311011d100801031509 67
    0x101c065160030800011605900043d519107540305241d580d000b40c40d048107400181040d44c000c00040f6040d40000b4908241d83c030032482c280c012a812250340c02c1c002d0000d5200d07001085030f1b0b0003030814440c00c0d840d50740c0d20008043d10b0480207400090a85a051051b55107403420345410180e6004c0c03244104881005921030b8500f810064400a40e04505e03c4607800b010540420014455044041c0c5100c0010031444510031400e680c01c040325500d81c041c1c0b250b80515444040724000080e1129001c20b8052001a412480b00f9410812000e801020302c0310035503882000c0742859000040003103420000208011020106c2e0700745600038032080ca4200020100e9841d40000031203184100d511802e400200d0300c800e030b40c40760301c881c140040c56100e0300481c03d20041500014041840201e01440707c000005444400d48030400b03c0090300320395458a02ca0010004660341260354601411150300c0445481d540c0c0c41d4100c9002a0380d0340350f180e010a43d4150705203c094125200018591107007843e0b143e030002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 114643345 1250 114642095 114642103
    0x1506050d030f050c010204030804051804030e0d0f0b0103030206041a0603031602280503071a040608070c050a1a1302010f0f03060504050c071703010f06051e13140103090302 76
    0x210380524204810402c0c1440883e0703203108520048910b03600210f004024403810000400850310100c8000406180c0e513112882490401c0701d002c1c010800403000307070344542000f940e11404103200302040c07400c10817141d55101c0306a03800e030029401a40074400700420002e0f0207941c090a020391160034102860403074002a42c91140c031b581a01c03070010b08940b62085482d28030410100e0b044400c1403100c8120b202141000180c214844c4031700c01d00c148840050740d244002801c4200410250065207854100703402510050005080c442c2080125640880420000c0c8404103120b0300c00d202c24240c0d104400c41400c00301d00e001e4504084041003c401c000140c1e000528210400c0590411164071a8800740544c001c250035840aa040f60500741040340c03400380c40e07008200d45441000d008514280c1c1d624039000901090003102c19400c1c0c401824002d15010f40007500c0885d0f00745440e9008040780c60b42500180d00424900c0389860300607002440351925488110b40741850a10f4100500c079241d8a0003907407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 114644595 1250 114643345 114643369
    0xd0906080114010f050c0102070311010b0406050a09020a0c0206190806060406120c020f0d0e0411030903030130030e0a0501050c1005100e0c03070e0301050c030c09030a020a0f03150605 81
    0x51201c04071a43c004c07140280e0035125000402402151500120706001e841d0101d40d0300110155441c00b4040c43c41c3c3d00d030500c500e4080e104050101c0c650740e4203107840d64009500541c0c001c1c00303000440f0050401a03a440d402041200d807401721903101514070201c02341070721202802c814464482400244080d99001e00b04030800503200c400841c003d40b40030030503414002215020400380c003a0901c03007014260400f124000c1303130f02c0540c1e0411000600401c091001e0005803060740050700104010011602d14142001280300c05820b544074002400115600c407559441e030490100d40200c01c2c4141900e0b02500200003000300b070a0041c5010000d0442c55110b045441c0710080b4541d9503400304010304283c2c0d00f07289c090803209520002e141001015480b0030781007180d10750001010607824600ca0304060103424095401121ba090964880080c450f0464101240603505407003452801c001617682c20483c08002c1100071240d20b00181175080203142841c6a0011114443c1007160410050301c4d0502c0d0404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 114645845 1250 114644595 114644597
    0x80a0b060103090f12030207110307031a040c0506130603140405060a1e0e03040e1803040303050906120a0506040f021306200d080610030920040b0603090d090608011401 74
    0x10380200d69140c040740160354a14040c200120403440e01a6154150307004183c4540121560041d4149c00d008042e0fa54604d408001c01c0d10b50b40714101e604075049110707440d4002d44680702138514117460b040481c0b6240c226240071404440366007070801030690144a1a621030102d2071490380c552406131555036407034102030080d00c4c0716651582c0310f140c00c40d004070280d0020049507078140304c1085a41074139903680d0494090301050741001000701e01d030f107610351141e5035501c3c4002c000395060625540381034078960451203a00e82c10000c208103491044020300492441f4100340700000807a030030140705003c102c910300840c0c40035040c8108103000f00d42c00d503148240d0484500f480d041030f103424640300c100052006510b010744644120940d84100f103402c084403510070002543d40d00b5030440c030b00100314141d07480d040c0701074014250f071004500d0300c2104d4608a809a07002920110788003210758041003143e40121903109141c1c00660700c0706101c903440318201008140601d0469950750500c0600c03807048080c000c80318 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 114647095 1250 114645845 114645851
    0x8030a020904110d0c09060c0308060a1701050109060f03080f03271c090608190b0303070501150806090709091a010b070b010b030106020307060b0d050a0c090501080a0b060103 77
    0x2010004903404444070540c01510610012100c0e801a402c182c0000d0b0a8920b400d041c0b00e014210f0b0351241ca503010031920181d507441e40b41012602c00380d810100203400e903131f04000206c5c404504882c00f031b802c800f0310300c0d0240000192985404a081c04a03051a0845418600100d0f03080010030303003e00640f5020744c01e00f5222652500c8200814524840d00903000d0075005102034070018400740030070009046040c5040b094107000c06460111030203416409003001080115001c2641c01003900355101c001c2c800160000750141248001a2658120f08000c6505170f444580f0740c5565000d1054810007428250700906541c28403c0069803594020300800951641c0c510050092100401e9202c0b05103800c4003180c59156100c02000465601583c000e60b00102682c00008140d00b50404a90480c3d54680c051400c00c0e00c1c40e680d040c00f40840c001019448440c40591002080040c4002c44031648103032541c0b20080d00d492952015504140d001017010f4208039a4000400d55030b0526542c8000246000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 114648345 1250 114647095 114647101
    0x8070303030e0712150606081909050a060e030408010f060501050301030210050412060b030606090106021c020f1902011101050403020d210504060209030c03010615050a09090f150e0609040803 84
    0x2843c01c0c0807607010f0140c8a48800c0e0a000340040f02c01103212441d45124144040c41d103078801501e6082c4140d80c070101c00b00c5d41c0c2c003140c8054122548007091241c0f04005035103020b4102e07203800702540d2030803803c20f01c00c0d0030005080192140902c220300c0585140e41d0240000d518240019000b40814031019010f840e6144408840501c42c1040301c01811401c2414154260a800c14000520425841c0c0d07000380b01d0500400d2940c0780603040319040b50300550040c100f0800002c2d01c1d68014103111081d030158441c011055400c10304c14400f6070a444486020015031600d2400010180d40324000d040803664544020700c03020a83c04511070100c01d000341040000c81107914002c042103209007850f814518500320502c020044150002d0482607030071411591004800d508040c2201c5080c85044508207200c003500b2030440c06030703001e00101d5030359040020b10a50f0b0703090074000381c2d100c40141e81c2c80541d0358003403d40c01d4242030060070090f00d00441110030625040e00030400c0c00314090b101500e108404400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 114649595 1250 114648345 114648371
    0x3020d110c0907050a09080f0c1806030a1403090603130c061403060d02120a0f02090a06080a15060302090106020a02010f030e0303070309111305010f050909060a020d0b0d0f060c08010807030303 85
    0x422401072591104562440d10100c40341e580b2111206401d60ac41c0002c510100700394151101214003408009000d03103400e80c655503400800d014000c0d448504c500040c0614040c40c1d44800148d80715600242e00141c503407129150030014840c041d004038041c011016194900701e40000141c81e4065002d946503404034003030b80005241d9080600c51000544150800c4804102512081d000c4a0748240d0b00002c080e140c840150040e220240607481c031982c003044182020900d81c04500707107080c00c144400140b29850360041075102c54260404070242e8042ba00402c21560700880c010044119480c0c00c1000450f4040040d031039100240980040540300d002040900c0490100910000d0b0f0003403255404841c00b80d00c41000d0402441a01240360688000003a1800d200049910a4000b50043c14250b1f032a21030040094008040d8590340d140d4514241c41da50302e4141c0340d903080c40d00824a241122490b403900c1015107010515010810050900400090800054910a40c0d0b41410042a4881d400003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 114650845 1250 114649595 114649607
    0x30a0f020709111803120a1b05010c0815100915031104090c021c09030221010203070509100e13110903010609061505030c0909040503120403020d110c0907050a 70
    0x2140112034504070740354600000c540d005010300c13100390300c030100e90399103420404d6103a8180c3e0040d00c06850381080040c0c1482d100385d2581210712207a04540c2254600d90311824211250b5001c02c030082007056003440811144402c1c41d5290b140c00b191b031041d1102c0b8442000b014502684500204050389068000c0154041c1c0c021105918400d84503a49440e59101840c01414a10036003402601403465000d0164660782c2083c10100c50702d840c2c041c1d10310f1451b82031003101d80c00015034035800c007075520000180400a000660240e112995540e4844c1c04490400c0b80d1002f840c09180c081c0700e0054020b02450b10f6503a80428600d40301c12000400d0128111103803154401c912045505502c2e140c00031a954619510520070b584140c031a00301c807000301381e400781c0d10792206030b4140089040c103011041480c42c10040032980244600c060ba0300f410500d003401c1281101c00d640860158100d6040c4050310b6521241107400038020350002d0001c00c01070b03400f04540c1080071742580300300880021143c2c6400d0240b9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 114652095 1250 114650845 114650849
    0x915131d09030d0c110d0e0a17070e0c040807080105010e160804060c05250302070803041208070305040914091002040338040303091109060303400906090e030a0f0207 73
    0x2e0705a0307611001b0070000414604031a00000d1140d400c41601080c02ca00c904050000b0080d044000d26415003411040c0c844210010130740c22070000204400714650009001d0340b0003c00c0e404c400403d03254107004107504401d800034003900b41880320031008603141350300c91900d542040d0480000a054070074203208503441e1080342080e0240000e60350707480b150700c8007400a03000410f000364217403214a502c0310480b5071648134a01c54001d4007450503900f0004280f00e00c0082000700e102c1c3c01c2c12886c0030f5507111510144c0f018601c2c0740101aa100341003140c80380c400d10452003021031102d81140780a0441ea00c445290b40460580804e000800b8240030440140d9031480704009182005180d0740c1c034061038006d0150152078811078800c44141103800c098140901c40b1401054020040c601b0004101c00000c100c004c880c0910091010001481501040040c40000315443c0e401c0120300b01420071909606480a560000d2a542d00c0d19400ce00355030000b006640b07146041d46408100102046800c81c0fa10300d103a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 114653345 1250 114652095 114652127
    0x15181f0e130227040c020601060c03050c0129040c020705010228081612020601050105090d03171314030403020a0b030a0f05070306141012020915131d09030d0c 70
    0x550301c0c003419050f0071201d402c4584404c031400d001e003101c1008102d807288400c0c818800821801031034400001c0c0076101074644101110000074154419850100400716010403000310401003052215060a10f405080301c00103482c0000d121061030240000d60b2800e52000d460009017260020102007130165044214564108621b19140c00320140351121440310b840048907804115000000802e0000c62600d0480d14141c40d03550524941509000000803000c108804000c00d071034058007c0b50500750400d004034258100980180100c0c034240541d800f0304100340040f580244400c0006030b17914080d0200b50340043c1c484949030340301c0f506642d020704511640312010a04010810009540c558004011a000010f0b900040751410301270000400c07000c420040054040c2e034110b400790009400800203200080e010844101e981e401c43d04a5420040b0342c030071141d003071420401c4003481804c80f83d118001000c07044c1d00380f400d0950041c0d65a205030780c20441d10980b104550000180280c0d801a07480b124 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 114654595 1250 114653345 114653377
    0xc02030c040e012415140c010606180e09030a0507020a0b04030f0b0106030c021018020603041505010f0b0a0f03060308180a12080d0b15181f0e1302 65
    0x80001100c1c00f130800c84000c071504800b555849041c41c68808598421180c1c0c94078980c44202070a17408807010404002652054007080140005040c0240300c0c000c01015281d0b21554102c02c4030303004103124982e47d0721145541c286401400000c02c8080100e0b400c0c403030207041103a640c0000340b007c92041d4100c1c0e44088072490004c68004103101e559051000705c1c1d8402c0c043d0064980c0c0f112020b034100c5000c6124007005911084412601403002c0d8410341cfe1003d00e051008941c5d4110340c0c0020084d074011201110308240c004003000740400640580760141c404001c1c4c014119007815800e1b81c0a0140b60094001c01c0005c82c0d1944410b4000d90050f005190402c0e54140d03100c107a07144280c16050082022401034a01c07030030004012400e00f00d0600440d900804051800140e0b0703849030f0181c180c06024507881000440038000030842d0100400c0800001d155034420140500100714070b441400c55480d80c0b022044607540d04140d404200024074500848400c1c200c1040c18141034020b0282d402e800701c1e4080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 114655845 1250 114654595 114654611
    0x120423030f0d0f030606050a0804150e1002071e0203100c12020403030c020108091603020f0f1002060a0b090402060406031e0c02030903060a02071e03020c0406030f030806030a03050a0c02030c04 85
    0x5407006583c141c0c00c600b62005d01c01c440d0348850440e181d201c0c200710304000a1600b408a00040c3c8000307a0440350045084000c9030103807030007242d181065074070b8005d02502e0f40c1c001204020401058003266815001141000c0004029000f181c1c983d0b01c08480d5030352495540c805042c07124000c00c00b00040300310050085454a0300ca140103090141c4901043e404200d091000030f8a2040c001790661050124030301c2c1c001440d2942e2300b40801c0c1410800e986a1000d440c610120316a103811031010310004003980103000c107080c01c01d52381c1c007103504041280740100761544c1040f0150300c802c000c880840741503240000d880d41da07907200f1860b01440300c1c0922416070704100030f8903680381d400005401040d00403002d543c0035481700e1020303c04138070448800405030510328035090f183c034084003102c00c2c40b03e000340159020426160002000c45031150000c640502151006078145070b44144c0f1594041c7c4254001c28001c400b585002e8030340c2c01503448020400000d40c0d580421500c051161044040c405041840301d15 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 114657095 1250 114655845 114655847
    0x8060708040213050114100c0605040f17090607030c0f020909071a04030c0303050a05040e0a15050f09010e06010e04021b0d1701030303150e1305120423030f0d 70
    0x28003541c0a030311441078480c0307650070482184103c0e8101d401410780800c088802e1002d12070488075000020081c854501c0400020840d0750140074845c41c071504602a00300c0e8640342020005500c03112102c2020414484503100780c640000f100e60481e05030415207422405854851031109030704174001d404c02d40764420300a410400041d6801902c6105407500b0100c1d5a44900a645000c0c500c070260030320400c10b41c01c0000c070703000740c0091003418003601d8260b02e844e484005541e460107050703c3c1c840c03842e03541d080d960402342070125140020740760031682031340d03204500303800192000018050884024104008100140c0c0640040d001c0c3e810090015074491996142c0c0c8a0040114400c4200714050031120f0030f19980b045400b041c0750810701c41a8252030742103490450082c02d40a11301815512040d2004c2041200d070f1440e184502e440b1031203040c003a20685416030401460554046400006100034401d40c8042d810014012900c0079407209031084a0000070700c0c20801d4403e1078650301989203500402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 114658345 1250 114657095 114657107
    0x8160618140c0109050405090316080a080a091104050702010e10090b070918020307140409091104020405101b06020310080609062217030a0903110706020606090a06080607 75
    0x21500071207030060811035503544152220b070660025400a003c0b2002400039141a511030364019956800b201c0c02c08244c04c94250b584039000c1f005480041020131510b40c99035000d00c1040d80301025210903c030091082c8e8844d0f00c074508111041d03200b181c6550024509510175401215642e400e07008032204910710240240081005000a032071003991440001d01e13131402140588119440030025101c85410403090000035000070b400c24040201d01c47d03c006010315200098230107449440400502c41d4000d00d8003180c1001740c001058020750040c07004004a079140404050307040200d0400d5145400c1c05800a036812440300001003d8a1010052090200b500c9103100c00b07440107001114110340782d802c000e81e500c0e14112040c00b00300c91004880000103800c5803415090902c0740c42080d0418100602142094204481030440315581c0c9011030241648030107804407207900b01001d0403440d828103200a45401006004034040e04101010035441c4000e0350114000300204000e84a05061a4034020b0039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 114659595 1250 114658345 114658391
    0x60905030c09010b1209460305041401030f050c070b010602030304020f0d03120603030e03190510090212030f0703080c2a0304080f0102090319030507081606 69
    0x1a1190484a44041c106100711a040e101c02401d56800c0a03511100241d0302003000300701c400301f4018032410404643d00c0c203a15224400c00e50380502ca045e072011b0502140c00c88600035000740e4800407220140405d4115003107805991075007400d404003018090040e0081d00d01800500d603050725117001c00010740c009801600307403c2d124104482c1141d90340c00e000c070307600c0c04269070117580440900006149842c0490180c1d8005209052034641810808140b104542c0b0617401900455203d00040003145400c0c0603060304008210700c5020400c00b20744409644a0440421616907176550707180605568070803138002d160050104c00c50740c6c0c4e40d40c44860004544c0101d502100414040000f00322904000e10545504030381490000507018460580b80810940403030140322180010840850100c00a1256940c08207060f800540e80f0001442490301d8801224103010202843c00300309400070383d0000c100d4040c981c2116403a6295680301c129401c456288070801031480d8034201411440401e06c0ca1408a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 114660845 1250 114659595 114659599
    0x60109170114150306060d08030c0d090506090a0309060c150e1e0705010e0109120303050402120102120f0a09050d0e06042c06090106021005090a2a060e1003090204090203010204060905 81
    0x40355252072047c4502c921500c24028402c1005000188090401340d000c0c15000454442c003050403280c1d41c039024200781e01901c461441ea001034450318149604400c03203000901c001e00c2c00300140805900c03461000e07200c64400d94889901c41641b03258140041001214040b502818024100c052902d6596100220721485000c901c1402c42100e02e580500f61100403600a521408541b1400d80d90480042800a0041364400401888001a40d40904c06411030a5401c0340c800b440d0f00b881142441c0030b030b000416484a175802d00c0c0ca0200060340201d02002928840c1c10010014908140001c0880c01950007842c8000304050b1416041c4440400070907440c80b01c800020b0041e11401c040c0605603009014038009a844600c41140c0002ca55000c240d20002880c1a01c4070750416031b0b2407a01402c4020030f0702203c00c58140750b130458906020440d03401841ca50400380f002c2d030143d0011078403002c0c650501e40c080c9070f910340e168010340d141c0d50032261016600070000c56031280c43e00c4000e4000c4c80b8900070a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 114662095 1250 114660845 114660853
    0x72105040f09060f0905040f060f06230105040e090c06131809051c050f0c0105010512010504050c090424051f030b06091b300601091701141503 63
    0x11000342d42d1050a066541c540882000360b42401c001601401c1c01500c1102d800501450728804200039224000040e000c402002c00c8461400144800881c070700c0d84280c03c0702610340ca84c8111a80c001c011201121041d1440d4039a5649914414ac00d20740401030075500094001800000800c4046518003a9480c06455880c45558000710004444622000030210303805040e099000422207a01c2541400040c0341880c60300040440141e0540c001221580581e9147d400500182c501224030a140c03658600080000b03252503251b240d60b4900e002509130041e40410045400d00c0040143c0642c0c2030020211001d1846c04503008c00014203049403609546041c86005d40000540c800310001129001015210300361245410018502c60142564100c4800c4c102801400040140a014000d00c03218a180c5408070050522003451541c3e00003a01444180c02045150303030300a00f200c01a181e000100c01500b40301046001d0060a4282c00d440c0e04094030030400a220382d11046000500205030250b07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 114663345 1250 114662095 114662099
    0xe060c19051b06061512010314010b1201142505070303091b0503120f0306040203090f06010b030103020a050a03051507020c0a0b030928030c11101107081b0105072105040f 75
    0x1017221030003841031800d84400040010400705400d941c80c610304504600000a0280c1c80e1f4000980000c1d5040358081c069444200303070703900c10a0030410726900c42e0381528031009000c14031103840c103490740ca900400c082c40340c082a4074040c941300e68000440c1e079612620402d15801802d50340e9a140303403e80b01d82c41c401d00c00c1c1da03050310704101140c0c1611642c10b8400c803058150b44950040001a40004100310314511900c0b882041569040080e140208001448141d5950450040c03003202c4000d500294040c000012003000010350004251020940d021340e050460f46807a88200d00b1308195900036a4005060a03020601c1459440214010a5070400722036a05498900030348803420140c0d00700d103e803403500c0c0e80300011038002d280840103035200d107000301d40707a0700410000348101c80342d08a05c200241103140d007a07441240410042c0044c01e444001409042221799000d00368032100c0c0d42a42c10401d000c25807904114480c7c00300d03120400c48844407004150003243c001c0094005124001e10703258040780c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 114664595 1250 114663345 114663379
    0x3010902130b190e030c0301021c0b180402090a0b10020304090f0905060106050307050d05010e0412030504020618060702030a060b1f090b18220e060c19051b0606 71
    0xc480250070540e080122050f6011001d8482d0144c410700903426014010b000602c1e42c1d42032000b0076014001c060b0b4040030781004078100d021101c034444454091401d0b001c0103080b4012501c00c055109504a8554445640f120f5106019004403c0c0d6107030808101e601d89140789030084041c005031100b0b018200509001900e484c1c05841104801030720340e4124200501c5044e100300015540044a402d1951500200900b240100d840c00d0380030000c034560100074441004042604500008010300c0c040c00700f401c007a00010164485c000b41220251581d05291010352108010f4901c47ca4009007615140700a5084c1400580783e800d0266200361071840319890440118410b14504620503907078692140c0c107100100d141c0340d000300e4600824008130b21800c41e4541d0f9481d250a0a44500309812000d1031810042c4015128081c1281030182c00807000c0001c0d402c02101a2540c0d400801c200c0d0b401c0c00700022080e04c0601c9490244c0081814255842944410006074140100c8090325113000b07442c0a009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 114665845 1250 114664595 114664597
    0x50703080901140f160305070f050c09010e1509061201060815090a17030c04090e07030302060705181c0c0605120609060d0b07030b0307030b010e0708010b0703110102040b03010902130b 81
    0x1131128002c03001c0c01210303141c002c00502280e10600c81e05005141c400c851300c2d045c40217201c2001c111034650000744004d4507400d18001045c01040c4065004c04076040c11721010040c00d81e070083c03050141e5081c00028010369030720410b0741c4016070350800070007602d6201c40e60345480b200c16030480020085503a01241d8020310000e042e801d80c0d50000c4103402c00ba00e080303040f58000d40c405801c42030619024040865100e0841c800c0301c020600410060a0742071551a0113810310b4002800c80f028003106024030301002c0c14040b800044a40202e070720288031800a0a0301d441e444006402614a049901000c640150490010700391031003c0c044540c0996114410008540b001720345142d00110a40145400a12740c61149904814a8240400c400b50044040b0340340452590060300c0c00081a0700400050906c4103201c1e0300804d1500d0005100c1d81050001e0205110b000001801c000b424040c0d545518800e5058030041d000d5801c4041e56541d6401c03c400c003035088200000c4030035114140003d040840301d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 114667095 1250 114665845 114665857
    0x30702030601090b13020d050403120b030705060f0708040b0705011a100c020a0e13020f0f01050405010807020705040c0906020607030603020a090b030c0306040501020a18080a0b09010905070308090114 88
    0x100140040e030700b003c01210190022440f0f0b20740101030600c043d409000710303001a00304030400180016062a0905005224412201041e184140342000800041d01c3c0800d4107000e43c0d0b400e442c1240d075a0140454202540308102000e084891b0109000c95000300201c01000507900410091113925440e5503200d01034906000034aa120ba034004280400c14024010700c40c00600040580d5251030f40c2e01e40e00840b42c002101d000343c1d00b03100cac012107804500e0580640701107180191403000c80795101c180041c0644c407660041c141804240c1000402c038034401c100400107020050002c0c8418251010054014046405402c000d03001c0d00c000a481d0342e202e48144411a500140b41000c120319184d629801010b481d001141c15020395075001c540340c0ca04020940c0114400c03000181d80c1c400c400b038010100011a410102000740041082128000003c1c2c22080d080d0070030800281034030381441040c014240c4800040c154040d80e0350020600c51100040d040c0c40c1c2080c0c84110745071b480014200e0380740c442c0c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 114668345 1250 114667095 114667099
    0x50a0e070914030c090a0b011b0c0b16060e030307111f1e060e0a110328090f0309030b06010c0305220512010507030b0603060303031f1a1209030702 65
    0x40d0704200201c5203072002402d901c001c090700740c50044044c40042020220100d0341c0312842034481c4d002103003550707003c1e15409252210320494030308404960707a11030540400344200410007002103003444041403541811040154020070800c036000c60140a82c0c1c585d00308881000100c1c2c1440c0f0205200080442c4060407000c03090440da404c0c2d001286040001e01104100808000410154940c850030b83d01c65031000d0015010700b00d41d2854094104800e441e11150390a070601c0c004d20911054080040300c41205248100802c01b4012080b85240001e015004010b003410f02910107040030315400c00d14503030a5a01079503180100c0e039074400056810503039040f40200000c00803c41d0404002c4803080300c242066601e41180b01c055074400014503440d1038507d4000c00d036556403090142658051181c01054842070711103d043d4607124000946034003004200d0006680c90082d044111109452070780064002080c0c16850350046000c0401d858008032900003440c01c8800118070300000000a540b00c075980 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 114669595 1250 114668345 114668357
    0x10215160f050c010e06010906091808071b0303080612070b0a081005040c02100b0306040f15060b130e091c12091203050f0612060604020a0203130807050a0e07 70
    0x448000c80308400c80040700020014140080b290b284001e01071000f00c0c60450000381069418014080200c2d10381e40c5c890020301c0d141031072555440422804c3d407030085070020045c50f100c80a600307061541030440c02c096a42e1810300c0001108154001c60824040e91081e2407402a05640f0b50340b445c1d50b85864001c03010259003c1c44078020030f82c070070480d055000d10740380300700c84c0f420b690340d80490169601040d0901c0960070001020405001c0c51107803010413002240245000d041ca03403a9603c00041040016114001c402d03054020303007503960011002040031030a04c81d035409030105081d558808038011b03444850380e0200400c0202c4c10000e10b840c4000041c2041c00517001854005881c404488162000d0190700c030300421b00814040c00f40461400070b503480c04103444c1350000004103070200c010541d501c51815107940300441880001c2d400d90100040c5d0700103a41c1d1040e0f81c41a46036024a024241405c0701c1f030b0002040f401004a1498200c6400350f43e0804155102c80e500c05511004030f074580c0000f04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 114670845 1250 114669595 114669631
    0x203030405040e0106080f07151701090f0209130e070503060408030703020313080706020703080702030c07031b030f0528050d0f11030304030305060a050607020d060510050915010215 80
    0x81c0c03e070701420320400c0326800015000d07a9451194200074180840a8482d080300074200500b801200c0071240d201010718010059600c03e8038444d0050506000310302c02c481c0d07030b015001c01081151341100d00704035008101d181c3c0707004100c540314040e061600116410f4096004001202d040015103a8005c0340c0c44081c95080d5690360504800940004186101c5411108020700100d1000f40042030030390300613400581e4500e86418081e20060300500b907501154010000c000884001080420075030358005802c0820701488940c501d034120007a00701a04110050b01d41400b0003a0008040e4600041590b00c6038034124410b5140c5910322036410041c2107a003224280b608103602c2002039141001c030ed07040c0709404501c0c107292146181c0044804a0200e541c40e0144000c0d0719000c0c01c640010070044400d141307021601e5010a04502412305d0003000c29454034041400980c00d0903840000e004017400b44491841e00000040d41c99a04030011409405088007030b0a52030a04200c083c840c54200807030625100e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 114672095 1250 114670845 114670849
    0x203070206030417070f020414060306040f0c0b0d060510020a1703060312031e010b040501230c1c031406060306010518120c0a05042003100315051807030203030405 72
    0x1500043c011515904801400c40d14001d20001a226940c05035201e2800307004184144802c45500c4d03005070084460342800c002c0310f9500020042c0d4083d6215102030342098851802400196107904002032026010600d20400c544640c42042103c00c210f0f400b044d603155140090741c039903042c0709014000090f908003100134142c052005540004018084a180e0000c0005000680d001954402e403103d0781d8444240714028081074060240040b41c24a030f05d450304e0140042d00c0c020480d4007508800d000100014510305401c3d05680d182a09001038a5032140756070303000108518001654030201e031500c541400507004011070117120303003000f80c511443c5890305001900c00c0d8001120100c0c201482d00c40740c846d0703034a8000304507200400034401042841e5551080004104c40b54000c1401185400c01d404000c00064410350001c00000003c181c0e07039212140c1f482e078402c889800140180a0f10307007040136405003550189108120703500710140100303080c1460984903030181c0b1010754580c0c8144006e120074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 114673345 1250 114672095 114672097
    0x5030c01050c030d0903050301090b0a080613030c08030903070506010929030102091905010e0103090c14030a060603120305130c09110409110301170d0804080d141005010906030c0203070206 83
    0x1110454040742e042540c1d900c580420b07205d111408070001040807004001c1d0742a00d0181d15100c0360100d40200d189428a115070b0755600004000451a80f4428803100516000741c812a40d103d070441d50590380d03072a2041100707550341d1102c48120b8052180000005031030304548160500d0204400350344000d50065884080c1202011a001c5c0c4c2c9951b007000110310590b03070001080c246014074440c8508442c0307041d00150000d000e01d90898141400c022142000411041110317042c0c03949030300010b652000e0200071a2071305543c2200108402c0c6000000320038000d1581302045a1005507405000701c0d60303950360f805459a41202e00821035000341d4010f1042d0192034021040340101d0008050806a50b0350181c0181c49282c01e40c040c60302e50002c018001c091500c0000309001d400034008100849114800400414000340040d11a02c004600324034000e005400040c0c6180300342c450700085040090514001300114401c1c940811803003d03002620b64082d0181482d078a0903500174604140c0c0c07907001c0c0011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 114674595 1250 114673345 114673357
    0xd0203091306050909010b0f0301150521060c030129030a0e0f010c050711090f0103030c0201020c040c032408030a030f1503030c0303141005060702030c0a18050f0105030c0105 77
    0x4054440c0c00218082e141c13442d442e4030801016001180030141c0b41c052001129541c17400724002d9060083c540aa040c2000c410000c0f031318251103841c0e000c1101c011081740302c001040c0c4003a803801020148a10342d181a0041c6041c0d810308520490b8400b0b1000100c0540005491208010302e010300000e085448107502101080d4503040c00d407442c03144851113180c00c56017010a0301000c64030214106e024040284580f5000410a840c124581d0500521100c48640140300080401c4095050303e002c40e4400d20580701c11410141c424400a00e07041e40103009021681c206541001e40484031803442c0410000d8101200c69801c055850405e1003101200605080f0000d003c0c143d84a4450080c0b801010b201c80300214000c0d940c0b03510070301e0320789001015074842c1e843c003d1b006402c00007407040b0203d0340c9a08a046800c03c5800d1135030744c030452020904105003801d0050380a040c030540000c1c91880d4200b107004003514031800b048580d0301c5001000003980c0a00501d90036a0240300103c0065000700002d00c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 114675845 1250 114674595 114674629
    0x5060a030b220c1508100501140708090402070c05040b090c1b030403050312101a04050d15110a03140f0424020a09172e0b0402040803070c06020d020309 67
    0x282c104010b8445040540207540406201d100c81c652080d0a03503817104045800c4980307481d000c0a450b18000000b403a040940344080041240003031202c08000b80700e4110384952802038408c0d5141c141350308080c0780035007403071003014040c03400c114108415251608500c1d2103a00601c082038282441c2240900307610340c1c10142003070280300402011000c50010009443c600100041510322441d00c03d01038000444554428003545042c00142c5945500b440f09403010394406030350940322000c0d58213000440840148109018074030b08a03a080b0701d110810010710b00f031245900c05100c520078011075415450000c0b1010080c003003805000c100000c11140100c0c403484801500001e4001c82840300600326407014580078041000c0040400034401c00d02150020344090030040c00346954464462404250310340403001d04a010004041040845507001d2074404101070021034859843ea443d4650700e501100068904003082c540002d003103403000070404405402d03035002e181031001c0441031106041581000c10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 114677095 1250 114675845 114675901
    0xc0a080c090d0803190c020708030d020d0f0911030d0c0c03060902010c0218071403040809010e04020c01060303020102070c0801060b0a080717070503070324140d0609030c0605060a030b 81
    0x8508a000551700403c001c6421040b42201840d407101203400c90100e060564201020400042c0001310a8506803000544056038401c010841c80e00200002c8007401040c40ca040c803020240710600c4000062648190111400707601c98031426200000b140340010302030f0344071101c180b00043e45030308400c0100703206050810210311f541c0e0009001c50ba04888286128035800c1c20427003910b5001f042e0760401c4001c683c07603924506254442a2003071048000c91414008410444103140e1201c2d03040f5802e83c81064001c101d459201d1500a01075884024103689282a050340460156410301c94202203544031151585010f130a1902075601034801082c45003401a03000034842915010702c100c901c200760350354405a03a4580008042c1c12100d000d030440a0003a040000c0030100c0807400e5042056801c0a4100310b40b60111100040070008004401405641400c00913000c05801c400c008903064400d540601480c0e0300c0710300b0322070340d44010702c00a040460f40d81c003c039464100080c00741080b4000c1074090 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 114678345 1250 114677095 114677119
    0xf060c010b0d080304150b09040b130204050903040611010b011e11030d24030c260f030c07060509030a0809130501081c090503060c03070216090b04050c0a080c09 71
    0x1419224080c2d40c00e4031052400020001080450a20b038400080200d2040008881c1e12002c9400c0b0140100010084802e4a001c10058821600c0d02182c00354004c006014503c4c1075843c080c0c0701d40084c1304e0040421155040380000400c1801000360ba40310682d60b248604000c0c8503150341c03511800c2c030150140003070007100c0595501d080c0001c0003456001500403511141c6075061040302c46901950702d070700100045060000803441040082101e0611410401220400c14a0401500001d1300f6024500c82d02882e281241c0011010745081581d51040d00e81c21552a0703000e90701c0340f1511084640c907411141101d00010074070f1000c0c02d40e502d800341005c0600003c000c07840b02142c20a80202c6001d0703128080d041c0c440c4a88181305810380341545010400c051511001c66034a4002030300800f10b0700808000220703400d1007042420744800700303811258411640ca40c030300d8008000341403000d402103040000040c80304401c58102e84400c0c0340781d95201c51a0790b4000810390590040701132a0b50140c1d8401c08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 114679595 1250 114678345 114678349
    0x21320040b0301030309120b0f0c12010306230c19030b04020307080f01050613210b0408030a05010603020c0c1207050a0311040f0b01081306060f0e0709050402090f060c010b 76
    0xd003028101d0303800300542e00c2d4103500300905010117550240d1580c1c14250708240014411008580c0c01c0203803010800d40d40d4944020307403061809400004040c5005000c00001400016001501d003105c08034000c484680541020703442c0800f04075426424000100450040400d400705100340c0ca021070f2400060110440c4002001d0f60f1013964484009100070040c0081d030350102007041d004000449289152140442c0c4e40c42c402d0301141f0513502444401840944000c5941000ca8001c0740e1104e406680b5150a18205816420540302a501285400300215501c0e00905c2142c14100032400184200540740c130820851580f201e03e46071480c02802800a0030740c40710b50441016521a0416020301d480050901c42104d0004034a49401810f200a130300c41c69030040c1001350002c0c555410802a07101c1800c050b4060030445e88a01200c880309540000c28042d135040e03443c01641c003503580d50f50856992041100b40e001d032b00b80180e0f0041d00056003001d03d2030014020a2524112000416400d01c8000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 114680845 1250 114679595 114679597
    0x1090b0403060b031c1407080f03040c03051902011707090e190b18010e09011b0f0305151c0c08030406050a020d0201021e0901051b0304150c021320 65
    0x40216800343e00c41c6012903251909004d4030405460b0b8800284242131490b81c0108403082d01c0c850107020a0340025584c051040c030341c0488180d400a404201e0790780c1003e1078540c408400f6440160717901d0061f402d00168941ca51002d0f4001c00b0707016515402106500002c260100300042d102109020b1030300310005034144000b104920a07000202c00140031404050302c1c50581e460000da4500c12a100000f401205885e44940d48c103484910740150620750707400c1405401447c00c40403003a03a401000408407419503019000803c2a8504e99040c00161101140038602c3c2881021855001d10b0042c824598070300303801c20302a9000d0040c014600ea55a0340c20055080d98040e8020f4000210005184819142c042060301d490072401c0c4004c5241903c207404810704565215941b2010503400100c1d40d02a81c410030648040e40641a50301c01191425035990755690b01c03034030a107a401200040f621071a2801403804d180c1c0c045d000703050001640900c00458004140035610700052001d40b21210007002034a070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 114682095 1250 114680845 114680849
    0xa02041107060920040219031806090c061d150a020309090903030109060b0c070b090d020415080c0f09130204090b090307030305180a030f05040b0715050108010b03030a0e01090b04 79
    0x40074891010341e0780d410780031840a0014003103000d54010000a00b000342c000030781c04503011187c40c0000e0b03a0344400105280d12744a400c4003410b62030078034000c202440303018115013080b03030003036150701c40128558080d03480c400060360b41c00780d03000d440305801d44250b108290090807092101c0c41230300d00d08640640064920710094440032501d0307001100500c907054252165401130030711040d04c141007002c9040003981d42c9002d806807540000e0041580031301c54030b6915030340c8403441d030080041c0b1142a10310004558481c1c1072003840058428102c0c0780c034050400d0000c801c1c0c1318802800a04950b42c03940c040c50000d90301104102c1c3c002e5669110b03040810ae6440b8418016207055002d50b96078226810001d081c0c0e480030b440107210300b810085401e03181c540011011032196141c00c05100032440000140c074240a41d5015451000002515008103c20361022495401058204114698840299508903006901c259401d40d000304803d503202400b40d103e220001c40149041020541c4a01000c00315811503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 114683345 1250 114682095 114682103
    0xe010504080d090302030609030910210c0f0e010509180c250c0801050106090608100504060b1c060302090c070f02040c050a0314100b180d0b040507170a020411070609 73
    0x203c05100314030f814407040e0f03040424140150b050042090000702d142c1d030125200c0050050300d42d41d1248801c1500e0b004002d5a041d41d00400450080501c050301c04d00141d209800040c07116030410341150300510680b0b980e03402c0130703044444c800c05071a04103400c003901815001804000f030022080c2e00420800508103050038100c4c0d41c090414514210800f0030441e00720070700a904240052108950002c54072044407454504488079484d00ca0012100392a50381000d81c103c0c3c28100040f03415003801e0f00406a0001e01c0702807084c6080d1100c0d010040756a42e000096114490b040400c0c80903001d01c000e4440d07640100340003118410341d90300003001c444540214002242c404145440b0045d00b500c550b201c07110390307045440d049103040c05842c0c820001c00d004114403902c005c242d40382009030060305108404000f402804008883d0704202c0d140e48070455048981e849407203008118440200e541c4122440e141c1d0080c40b20007801d4ac01c000c0a8002c0d502170281c50b01052001a0205059003c0c0341c1e203050007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 114684595 1250 114683345 114683357
    0x1107080d030c140903060c0a030207140f100b0d0201030e070e040605010e01060c030e090a0e070b03160203070c03080f09061201090632120706030e19120e010504080d 73
    0x49102c014002c000355480d1014103c00a111940060300d012441036400a1003c240a650f943c00000a41c001c2c002c504001e409142c010380da00b100324100061721180c041c01d200c2107500d0211030760034900c152101195400d8001000720708050065020b80c1003511090306003001d80e444103846440d05450302104481c20741d60540c441d401004000303034500c1076501601d06031809000401c002e1710003900e0a0b105220603405180206c00183d0000300f00e40c0a5980d0320031a1003502c51003aa035001040aa81090390ba500301b100300c0c0c044800111780008100c40d22180e004002808040c03a40d03e40c0105a005096100c401a000302302c48050b5a655100501c095034940041042d9941882020b0044070f4160f0000620420f44064546c00482c1c0c1c440f0503031780110440c17500046902584046007032900181100c045510800034007040707098140e0400700000040034101c1e1081c2401100c981041e020201010388289001c2c0c9608184901c00d00c40c2c0812208181401407a082e650301c1c00354a40781c9072060700000106 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 114685845 1250 114684595 114684611
    0x3021806041b030506040b0f014109040605090609010603110f030c0c01050709061b0c09020c07030b060102030a08070e19060207030507050901150f0210091a0f090606011107080d03 79
    0x140074402d14078805001d0f54190402d801803000070300494854ad035104450000c41c0b00c0a02c8a40d80d0005441a20410946000038414203891000642d0007107002c0a101d9410003102158904080560900c20400244101c000b64038204080d802445daa1800c001c5020080100d0070b0004105030042d409201d44c80801342c4e0346e90100400500b125000761000d010020000410010541c1c0040c04421403081c60882d0700324000203140403115180180d005142e1a4004944102064804210081140e000300c00300c07145c590310000120b8891040ea036600010a0100020407091032090000d9046000050b0a06e84071212221041c1a560000d60001c00180d102c81e00500c2089070070f204050080ca000d5030183c000c2d504108103040d481078400e4025080141e00107075459058803c0200c2030010b0000b1204000034061400e100701d1000054925110304140203002c50030500c940024a40300d4a0030401034011922900011142500c0301303401c1e01c4080c0b04080000c940300c4000d12038504a216203440014140b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 114687095 1250 114685845 114685849
    0xd0b06010215070503010506090f030a080712020d0807260901020d0c020c0a06080709030605160e030a030c060b0a0305010608010501050a05010516020d080c0610050102060a0603021806041b030506 86
    0x100742c0d02500c1c140305100c0410b115109030058182d0f030555800f00c41003500d924450011440410843e41c0141d854441d510055050007003400082c42c3d2180a044041111300346400f01340d81c0c58204400d0600000e441400080c00c0900c40c2d80302072070120a05040340c10308d006030040700c3c403492819038050241da54005482d20312a0741900c00c00c403540015002401d6130580100010b032880310a841075401f0710502200003520389200e0341c940409154010002c015904110000e1045c0084000501c0701081c50a40e03110b165180000d42001780c039a050f50f4020315203d10380e030385d4400b070000440460303008043c000d0080001002801513002400e501e10000813198074200400400403c203900843c10b01c4020010b490041c0440f4100031000f5405440d2107003540f000e440c10044901c1416001d11081c02805c0074000060170044d2010100c038001d0342201d0254840600c0c260840d8168800254446000030303424a210000404156010b02c000b0400031710b480c0600da100310307824440c550400000c1c0c0d031481001414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 114688345 1250 114687095 114687103
    0xe010507022a030606370306050606040b07060e071508101203080a0506150a030c0e1f0c0602090301050f090715141e040603060f0b070b01031b050d0b060102 69
    0xb114a82036200d200940ca0700804d841c0c1202902c10780c052030749403507800600e0b981c1c070b003d250b40c0b0a64400503003c915250489201d1465031400100d81203030412001c90014604a82920301391a2040e5400b40740c400304d55a01ca000700441c4041d44e18078011580700155120f5248048601c59601d515807a01d14509104183c841c004030350007030310700318055415190100394000f016a40c08007500c3c80010756038a440300000c48042d051040d01110702800140200b05ca5410b4010450f51001a240c521000d10f19504015981c1030701035203402d004581c1d4a407244d00500c42e00c615000180503100051812080101203400d40e90100c4592170780c500c034102400340e0100100807041c002c01c981c00c26503d0540300550018101c0011000700d654078640419904891030f20012410912403132450159522990354802801518007407003403880740c08443e9030001c0c80504600895010f140c0c00342d200d003540c1e0300b035a1b0707501540010003481580c0242d80c0721000c00c00e51240341c201490b89000380030141c0700b458054002490 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 114689595 1250 114688345 114688393
    0x909240e1e06040305031b0d020d05060a050f1309020916020f0307080307111903020c040b0a14060a050705060108060a0b04140103230712060c050315090402040e01050702 75
    0x3280340c407101032040c8201c002c07a80542141e45840d185a4075210390800040130740320441100304074800041c002009283c954000c1a545440c0c003c01d000c05da58203010858100d015110b210341110300f4a107450035034501081000642d00340f00d040000c1c0b02241d90007042981d8000c5400d00b400c5040344a94001d610340402c0004511410b43d00210f103800410b5880140a00010f00f440060000d0360840440c890030600403139049040102c10300d84a0301060030029a2034102040303003070059160034900c0b990f50a24140c01400d50b23225039040035000e031003a41840788544c001d4048400b000b0b03003400304a000840500c0107a00038007540c4c009100900703200c01c5440c225003243c0603040c030842c603158078100c21424080302141107982109011038038407012810040041d42c0f40704400d20f50f0080500c00b04401000c0c001c2107444034081d060801000b001c504041d1410310042d100d18440c4140b001683c5442e04d0b04801d842c0d03000e44090800300340364024000c4a401e50f2016141d00000da084031082e9011501d81c41d0094213 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 114690845 1250 114689595 114689623
    0x20315031903120b0d05030c0d0e0303040303140f19020312060105180405040602190c11191e03060c03140906010b090108130b0f011d100909240e 64
    0x24000085590260034180565001c03d6016128150200180d90326401140d626400c5000d403503403441c1d8450107036140c94030004004041640c1041c20340c8241800016942a030781d050300d400c001c14000c8090352405801c01440c060100d4404c100780024507000310b55030200740600d13070000c5454912145040300040e07402010141001000e10425012041e501402c5003820b00aa500188a884d5410000080d104202d192100000d41c80c0b9202c1c840d40c1c6c0412001045400756210b00440740000042296850140030030216000550310140441c202c1a0384110040d2082c9180c3c20406650383c1e40c100c01d03101704252840201c0c0c0c2d20008403525640018060358460740c00000f4000c50741c14040280300d64010502400e0401c2a454002a0003e0031800b052030119046018400d580c600084446043c031404d0294a001c60034064800107100072440c5036a02031482c900710408540d0400030800f00a0440c4d00d03050310850001c894411000b2100e075403d0303801d26203070800131650300030b03545500e40340150300c00f41c4d80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 114692095 1250 114690845 114690883
    0x61902120307090509070210180201080a11190e030a0303020a030b040c27031a06010f05071a070507060615020f06091b030f060c13150c0b180102031503 67
    0x500b080d40b0005030016a4012504c004140c0c561407070891405243e1030b0303115100ca00c2d006000c040c01c04110003e40041c0d100340c0c0c440009036200c1709042d082d00c206c103101d02100340f01070042242140542c40d442d540039401e86400d4418a40940000c1d150600506083c0c0100f0350008001500c0d035814010b040504a00795405d00402d8034404006047c3c444500141d4800092058040d441c00100e0042c80e00841c0c04c5402407803c80d4215192141065003550b5617030108070a0b80034208210300a00c283c52940b5005805800211250440d2175041d010003040c84003006010059400040c08510549010303080d11006201072091404019240c4204010000c3c0f5680c4900100540c0d4640004c010450035900c0d4001c004405000f00800d1910500c0c0b0320384065401214200141c0b80b014070098044007c1e15282c000d04a0380d42c010328141a0758001c400303000a0103031580d280c0415410710819820400303a047c0301510b5888041050708a800c1540d224100c85440c1044041c00e02e4100b11001c84041441004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 114693345 1250 114692095 114692101
    0x224010f0e060d030f090302060409020d1d0319031d010e0f0304080718020403080a03050402180105010f14091503010312050307050304110d060207060902040e0102030c070212010b0619021203 84
    0xc07510f1400d45002803c10204052080b4650b03c1130f000341d00290b03030261040b0b40315500c0e100c00001a41044081c007100368905016600a000b9544040c01c0c0010504069460402d400e2505203c0da40c64840250a050701c031600415100c5503902c20000d030041c600000114021803003d00c40c02e041640e81200e00681c0300b4072080c040d42c000171400e10704a880100e80c1c02da85e6181031500e403019001c3d9620180c42c4420118042200030b4154110a02c034a10885085045c010745070803145410400f8041c3d14009102d4203112440d1a004120441c000800108200d044c56407140018200e0341110811907006030001c0f004100308a01707039201e054410361a0a00d2400c6107480c0c000108107010003800a04520030114a804094441440780c0c048150084425951360b17820342054400303420201812405240750452152003c03006100390780c051444c0120007881e0820b140c00f0081d040720a410301e6181550384200e01c41c4650389034802800c5081c40c001c1101c4810a40e90006410403041c1441131200450420030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 114694595 1250 114693345 114693349
    0xa0201020c030c130b030c09010314060c040308030105010305190f02040e06060703020d0c0c082b0e030d030f141519030308042901061d0f06070807030224010f0e06 72
    0x2051a902130300c610005002210200000e19000c0030040140d0440c841e40004010b0148071480018130024842c1162056180d04440c00201d02c19448042e02070107003480140709030346c0704c1e030841904444030f140c0d8003501d14103e46001d411a03420140007080b00b83d000801b0041c2d40c6e04841d100368010000c4400600700201d544001c1c0d1201600d4143d602048a00d640100c100f0000540b050b010b041408202c034031030000700d1407150829a0390140c404000040380402141c030303440f0b00d0790680038040103030182014085c0c0070002c0d009404809200c0c842d45455005002176001000c2c0380c40c0c886e841035090b508459900e101401060031300c0c1001c148064074003807010301c0402d82040c2055000b55000044030100d80700c200d480c1041121130030808120b11030110000030a641d0004010115840d5032100074114034203032081110340c840b244801a0084d03c01d22100010450060181003071502030300540d03006440a4402c009884101c03c000e03540031662200501034502a0a0307140e000e1b00d10380403605602e080441c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 114695845 1250 114694595 114694609
    0x61103030a0b12010c03051005030f0d0305090f010f020304020420030112020d050f0a02120705010c060207020406150309050709020a0c0605070e030d030e010507030b0a0308070201030b120a0201020c030c 89
    0x1025840d5030300c58100c40c4181d140e0b482c2060000394510f0003040f4034070754128000d02070072081d07412107400c440843c0b010030503280c00710750080a1504080200b440c104070a82c103602402008041e81c50700d001d15501c42d00c4240080c050300521500e22100141c2d00d142600c10027003100c2c9500115619010040c104248400743c090031179065514501894020000c144001240040e041c0ca000301180198031002c11030400018107014428030840c0c50050700700030450f440e9502c0c1d8541c0304540c005818120580e0108145500410070503001601c0803803070750b445070010888580c1d240c00340c2c4000b980d6800740300180b15040c800c0f0030162080c0b42042d80f500801c014002c0c40140ba910010700314941d200f01060003580602c41c025003030800901560501502500041c1c014074000c0c2c001a819400d105c0060006403191082101d060303401400c1034103250540e29510229048600204d060542d00c26180c0e4540d600e050b107588285e0558002030006503040c0c0b00080c100344156500c00c1c00380e402410344811319aa454 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 114697095 1250 114695845 114695851
    0x3010e13051203190903080412030c0f05090402040f080f0f0304030c0519180e06010509040503070807060609090f0203010c090b0301091509110901090b041505030604090c0b0a0906110303 82
    0x508943c41e0344450f00c403005820280140d800a03246400411420550002860b0f44280d0040039441c80440d81c400d401d8040e12055590900007446a207561152980208098600514042c000606154880317002000e411010b42060030640d2000a85121044040065000d400c0c0b400c005141010702e141ea403203401c405680240c9104000034541c0d10a04660703030600d01c0040c000000410342801150b28040010700429002143d43d003e001d00101c0d11b0305001d0315050145500c84001c41c684140c1d5101d034840f07504010411a040350302c03140c001031800345901580b030815000d00c04091802502d0b00c100350846500340640d4080c4140b00f9803c001c6840c000007900d044a40001020403080a1850020030003d05500302c2603c1c94a000c1c000141c042c1046c0c082c180c80d1400b078a90880700d41c2c803141100543e0095201c1e0100c490161412070851314032440c05980c00003800b400106400c9100d5580101004035904925180040441e00e0526a40c2c001030b000014140e6003041d103460408004040e41320300c070003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 114698345 1250 114697095 114697123
    0xe074b061d09180a030914030f0d031805010c020c010305090105131124030406052406071e1a060402040f090e03070b010b0306130c0f0f051303030503010e1305 70
    0x1000240e00000745100f81d00d842c0e01c591060707841d041400c0c50050802e2000d8014040d80c0c20300c4030351001c0383e424000742c02c4500860f0b00000f0311150094460880c0074000140700140c821341002a40000a40e0034007511545040c960040d180788840c032000101100e0001f0301b00100350303052105111100e0f00083c1001841604000000032101603100410303105860440041c81d001130045425001043d41d00185004900c00c410500c525251089409a000c1d04122124103000707080303000080d10314090006011042c4600d40d078040c685051001540c224000300e000b520b240c2002c503c0708001ba659601ca041d400784c02240c04604103030403c00861202c8a00d4000d10380407940da0000200c410004009a032a02ca5004004074515a141c1c490b8010641068032114020040780044c1c809010040c0985400301b1019902c01900e0300390510300702c0d40040f41d050342100380141001000c85c0418030000c850090340c06034880039605e51408a0f280c00c80f0708010b1500b40d51402110790600006c0c00414110040440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 114699595 1250 114698345 114698359
    0xc180609040b0907180902151309090f060f02030a050603010c090324050c0a03050c18040902010905030d02030702120705010f050c030c0a0f060c030e074b061d 70
    0x848084138a804625003000c2450302151003800c04040554010500c054130030388032454095107055440d0028026202d00c218140d080304028040000c0d20b5001500260142ca20181c56046686509045501041c1100c0c05a600042007002c03111450150f203410402c290000c2107044076040c0005c094081e540030051a1440020b5844240001280c9604542c513140310208181d0030300f00b91064040e408041c040c00480c0c01c010010b03110440c2001a20400c10111458046000c2c0750810480140036048080b03050003134031407010a490724108030303200c0081495002107a03584010700400808580241c466491680b100800784000c0e40c0c41880070710134040b1810460f44400e4000421411401b1b02001d0380c51030b101d21407121052000b980040340c1114000c1d101080850580700c000c400b5211150900c1c00568090141004000c220148441000310303090000c6610003c400481230401114807546000c0d002d0110403c0c40e0380c01e2004520005003054180210124440b503003101c2c6800e40d6100705445050703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 114700845 1250 114699595 114699601
    0xb1003030e040f0e0d0e01080a05010e040201210c05030114060301050609191701021308030a0c320309030111070f020d030c050114160f0e1e03030406020c180609040b 73
    0x1090300708001d03196800b13098800c007245201000340b0191b111702d440b90005000e4404182680494400e140c1a1041151561074035581c540043d0b42070501200b5405000022441c2d81c441e202c161301c11080c09500b160f0b1116525490203070011140c1c20704682c8584138007401c0004002c56075625046400460301924515408180d00300c00c2d0114903411382c400f88010181c422424070554040d801010059035250100c8040b58460b0305003660381c021104500c0c00300740c620041d100031600d09072840c4403100000c41c00d0015882071a0450070a400c40c0103007080319900120310080700d883e0030b005d640344421f1003506d0341e81424101d0b00c0300d0010b4040270b00043e0042080707103540004c1c14400ca1a54085a4100c00240602480103103807902c40030301201d500311036030030702c201c02c42109100b5201180c1340c290503541d85490341c4a400400050032401828050110845a14681c440d10103002906c001d110035000f9101d0107949206100c4000e52943c980304402e82104100030403076a503440c0b02ea80050700170a001c191a9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 114702095 1250 114700845 114700871
    0x130905090a080d0e01050f070e22020a1205090d1b08071713050616030503150a120b064608010902030f0102030108030307080901021e070b1003030e04 66
    0x100c07038050180c01d50a000032924940c0000b900941c000039121002080903551360001e805180d003050b01e0030340024018208684035440e11590074190301d4041400078403402140075242040340d004004000104a15169441c6040c2031032140e260720500a502420301208002c50081100d0a80020050418a0205600d041c03051100a0b01c062130f5100245007425644002c414103640c210031382c8604510140000480d850070801c00340c41e102c691000304404142c400da601590136805c010a2110681c94091008819a640a449034002d0100c00826403515004d0b04004010200081002d802410002c0d030529512914407103000c1c0d20454140c0002e034131541c8101001103141100012900310b160104041541007044d400181000e00c21001c0702c00720051f8051640c241d0209100fa501c0640003800014440c070302407810141e100c020000018a81400c541d0b02d42c41c211602040d0144083d0081032403020401144182c41d040158105a0040c0c00e00e5540c0081810030084626409180c5402410141c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 114703345 1250 114702095 114702103
    0x60636210507030f051603170c190b0106091410050a03140c040602010c0804020d02010807110f011a01020c22020909161e0804030c0206040b0c06091213090509 70
    0x40c0c1c4078050340d07480c603680d00f45401c544060b071200740c800d4028a018598020b450303004034411254801c00622031034031a902890260307041308078882094028a0b0b03902580482d404469500b00c0d01c00c0230310b52001d50420780e008201c083c072500703d800c0042012004048660b16400810810301c030070300e400d0b50b88401c40784d8210050901440030318450031425040c8801e80400344042e10681c2c545034000c0113029a00700c802c403070f10202564060740000d2030031098000340d44600502c03640100303a41820717145500509038180c13030b0500400542c0d01c079940d511100080c0e401100b42e5141914403d1008186102254000520301e5080006c40c000078100281d000e5401030954050700c540d6440145444050b00c3c0c0501d10380b04441808105200061110124100710000103540ea0302e801155503401803196117690302580d004a01040030380e801403084c0400504a0a541c00500c0c05500180142001e810040355061411031041ca103444a20024403a440031182c103115142c00300c500c1e07400081015103d1501003420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 114704595 1250 114703345 114703409
    0x904060204090e0f0d020718050601050408030d050403021c0f080924061003050103080a0c031404032102010204081207020a080d020d080c03060108010e040c0801060636 74
    0x5183c00c0a08002040d840442c240307002c02d000009a034407151409400b20388403e194000c0030ba281c1100b025100c0010019440b0551100c0107061040ca40350720303030000602d56000b041152100c2500c550801041590600c5201d01e400409101041c8428111340c0290201c003100e0043c000b0000001e000989480d002c01001c0e40c01b1030480ba005662448020039528401000c40d4082e019031041d03220b162480e4403c0c032440d030490340c20030f01341c0381010761000341100c00400244080d0100952a40c50f07480100d9158000d0006504c40d0780c1d862a401d07900b901d018404418100d0030700035a40306007c100140c01002c00c0301030032801c091031075980c2c4007468030010b0400c6a05420500c454030402c6840860103800003001c00c003808894480c1000c41e078400340c440f200c51000315510b07400903101c40300401181d001e01a50307075000361140141200701c07a140c0d52000d00b1100c2540c8400002214040c03903100b907001c403004030103410030b040401e416507803031031b20994601078071a2261004a400c2c0701c41140402d1003040300003072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 114705845 1250 114704595 114704609
    0x20103090b010915150f0f0c1e021e03030d090507080f070f0f03030c11040f090b0a0e01091106030612120405100503070c06020c0f070909030e09070c020904060204 72
    0x295a5031140c0403c0d0050460b030241e0a014403540340085086001c808007806441130a588240308041c500100300c1e0360300021100310040c000c2d41c2c0090300019400444004a920058550311200c0d2003900404c800142305481aa141002101401203075440c080f080707035a124800381d0040707000c1c101c5160080c5400d2655000310303c01d014007800700d2900000031900d0385c2180c0c043c0c0007080d4135544800c14106a4103a920001f400714912071004000a15008062540400001c0c4002101801030303a04100f600e01075081243c540840c10b080041241c80d62050702258401c40c402000b0801703456441c484040c00344c9084a00c90700e00880010366542e81c02080413820709485099440e1040f0f10b00c40e10942d0740140c002d01d4170070b06903401c0c40701c40c2c180301e03000303607880703000d075a0342d12031008042c0e44030300e4000e6000f4612840039002e00d040c103030900c000402c60000103003810900091128001c3c20014001446140c106d0b128002c0402404103181e802a40141040d404445458543c0c490b4a048402403003a644512 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 114707095 1250 114705845 114705863
    0xd0b04021309020a0909020f0409060e0f01060f050f0c0715091805090f0a05060f0c0703020d120b031f050a05010302060403060507020102041a0903060a05060a0b070204020c0102070807060b030c0603040f02010309 93
    0x2309030701001d42c02070300843c1c3e010030301888620b459400b100101042214009040020100108400c5200e801030880c9691a814114581100c01c942c08000d584542400252507000c1c110811149188200c0404902c00c2e501e0458401d50400354581e80100382c10b000e411b6400e88070360100300100424070000000c028500200c4458100c01c1c81c00d80c0d107460b4216000f00000b1101400110040c1c2508115443c65605a001c0c0500c4008080213589813101d4070410030405960b0f00703e40c01180c604010f01c2c441a0340b50408201c0c004880020b1009681d002080c00800c40d00f024010401600c0782000d50b82900e6200030081501d6880d014100c7c02405035911100002054a0b519040500d01000034100004d050302520f030f40b50707200e208010a80b0301c00e48080340c21207200700c030400c200104400038007811840100050320303081400f41c41c0ca099070000c0c0e0040c0d40000c000581c1d1030070020544502d0714019000d074064051050f5500000302c49010080c4060010307080242d190342103a01ca54809060154011089 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 114708345 1250 114707095 114707107
    0x7030c11120a050d030b0d0308101a0d0612050d120f020316110105060102190c0f0902040f090b0a050607050c090103030e034b06040302030d0b04021309020a090902 72
    0xda903aa04881e005035994010344483c00340c030502c41c1c0207410070910701400c01e1040c80e110b83d40855a8001c000c000c3c5008041c101d1011820bc9210340441042000b5683c040351600100650141240c1c0981d00180b401088105144006440070810300c4c242e136403c0c01c11010070140305d04030101400c64000c5018046200104024071000360147c030940b080041e03610568250080c402d09400c07a98140c40c0139000d64071400d40182c00308640c5803008202c6200341c140011642d0350365a1030400350800e40010f19100d03000b00c1c0a00520741c42031080c9000303080d4000305006600c2000e0101e0084030003405428028100013a1641c1446001c008501c03518501500c1e04090390b03900e0a0003040c6c0781202058a1190041a051000c03880640308150161061703400d02024513101c2d15a00311034450317040e090000c09046102c0301c0a910001740800d900c218080c0e005595190f100010030000c8903103010809100e50b2051261245515400039000d0a88500c1140180d6a00b100c1900781c9001017107038440c0720200d00020300d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 114709595 1250 114708345 114708379
    0x8010204090b01081b0906070206030a09051c17061810140402040b0906030a0b0d0b0915071d0102030d02041d09030406120203100b0d0c0f02060c07030c11 68
    0x80c412101c120340100210382c020030044449002c01d982e03e4941e1003121240c160124103d00c005c1035901001440c4516081c0c0c240e0200c0e505400c1214101e207004e03940c0c5640d10502105200070111100a001c2e1992003100f8403801400701c5458400c01c25a82c0c00641c00510319072540d06000c01d15442019908190f07203005202c002c40c80781940200c0c44442682d10301440c1d603061a0003901c2c10307101d0401030309040c85c020900307000b1030303400c01030008400c580c4424441403140c0b034088050000c43e0003410070b0314a41c41d2003111240f0700040070810145c51000482040640d0364048050301d144181d500110307109110000040b46103000d10000307200c09900c0010000f0701c11254400400071543c240500344915903030f840207107803640181e100e40e401141072100c1411506a2640c021940001c00c080c2e40d14640341c4070401c000188d00003086109903c0d580390085a1aa0b80210040611400c90300c014030241c5011401c1060368042c02e1002018848500403410412140183e04140140058035440c0021500d03c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 114710845 1250 114709595 114709597
    0x3021b0d150b030f010e0c06090411040b0301170c0109150306030507080a050f0307020f090408040b160213050105011407060605060d0c080a060e01170124170a0b01170a050304080102 80
    0x1030340c20303c03078401e416403818810018080c1d442064010070203028144a04801d000c010790060507810350150b610002c80207503940c6d41029002429100b02c816071a5814a4880d004c122241e14259107203a00c0740320b55404583c1c0c072042d0030f0180c45111400412070790540c2c80640242c078158000074901d02030103902081c0d56070000740d20800381d07010700704440050701440300954403417150764000703034124421120403112030910840c9103402500c6009a60f00d020785c1c80902018613042541422060301c27403418580d00b540340010004140305012102004503524040019061b1600344050103000000440c0050621030b096000174000c0c039001d000070390744074649a82c040081c0001c480241c042031240340440c2612007a8420101600d0101c0310500440c1d0030f00444044184c1c142800c85803941d203402c2c035010b080d91000080e88841461002c22580c0c0340c28401005404801d007400c0c41002c2e40b00f0801030b4003080300c0303082160440740412108112038007414091303414403c048a01030090b02c000680055000d00541c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 114712095 1250 114710845 114710861
    0x40b0403150902041b020d08090c040902060d14060f0603091f0207140309151201030314040816030c090e060a0c0c05032110050102031e041205100c0c03021b0d15 71
    0x10382502c03418182c5c44000d2341e85c2c1c0019181c050244c2d10105003c0c0d12800d0940c000c0320030600040102d03007007103081074452040e24180200e010342c120451043c8000390a0002d801c00310300130200d484504614000c00c0c0b5a80c1e60119907005410908091151a01460303903504030740b01d0941041255401e8015205610745c0c0354001d102c03007406403451450411001a0b0481603a5440c4103000460815034619242100e2100a02c1c0c0c0010f250032040ac00020864800c024400c80c0c0e0082d007640d68120703851420041c0d440900c0b9840026464205a0031850301b01010800e0303548103407640030008140407a08404c0310301800c2404018140e01c030000d030403c0a110b20082020b000c0080c0140740740541d41e0007144071500b02c1c4901c10749015910a100340c2ca401d424000c900e200e40300e214101c1c40e0030107551340450340854681010039207164010744604400b00d8400e0103200a0040c15050011803694039030340003075451210844490400528402400203680c035142c81c0c19a558001965070047d00800c039031800281401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 114713345 1250 114712095 114712097
    0xb04260c06040515130f050102130602010e010b01030c050f0c1608100501050d1211010f06120201320307050c060a020307110a0201120b010203070611040812040b0403150902041b 78
    0x4003010200741d07020032103002e21179540f0302d00d140d40418290f51100001303c1c21250446455400303210241c0c1c1c1c0380b4071685035001407681f60b0000c0f0700c040c00880d815003114081c0b61468105420070540e00d00154201c03040f20740010f405d4000c165550f403400006030504141181503100a14541000207184c0400a8803803040414020208150b03640c920420603815140c00e0002d00b0407401200320104140200c0101280c0140c0c2c10000c2600d0752000c032842c0485056030480f10014056062103025943d000070b00540440c50000804920b0324050410501529158854040e2003070020008200d03910031400d4601c180010707400c031405410045205806074000302e40060010fa40c0004c1c49200c000c000440101b210f806031104100d2810400380306001e0148c0c07445150551004020880002d40f140c403520343d0204010381518ac540e406c062415051000742041c49441e17540500003441001c4a44045030100e030344c4407203940206c803418440c06020344001032021303511a182540250302c9504081039080040a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 114714595 1250 114713345 114713353
    0x1080102130b0403051e1006030308090706020312010b09060c0a0c17010203040b0630030a0e010903050309010e010c083c0d1d0d180609030b04260c060405 68
    0x940450207994081ea10000d4282e0b4086d113811500590608045030038007440100751192031281d4080c07181503401c2680b04600003910360003086441281030203040040e0126201440c50d10801c11400f8400746d03030601450075204000a8124000d980301c2040350781c608400001e90b1080303c02803d103118004601c0c41012406216440c00034040c90041c4202c03031060364010905412501c2c1c2c0b4007803181480c111007e0904c400c108800900280f801030201c4018110b8410003503640e10f80c5448010b0020380c0b000c20160620502000a100143c401300588981a4080c60800d0003080310400403030748076501c0c0401801d40000041c0e500c07240c8100a20041120850f80e0000ba00140840e113401411904810a460001c0e01800344440c20411600f000492001152000c46100d085e400c0c81800e180c000740300640803860300440c401202d80502d444000410311030034440c40480c51078070f030a202d18038001e02c000c017014000e0b02c0c4841680e1514000c000c4000100d4102511051807102c1c80c2c0d5268426501a1502d05c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 114715845 1250 114714595 114714599
    0x1b040b0a030209130501020c0a20090709030807081e0712090501120509032802210a030b01120e01151a040e0c0c030310031e03080c0d020d02030108010213 68
    0x380032a14908503a409400442690b5500c95070483d4040c071200115102c2d5000c2041401d403030707000c008a410242c001c9840300e50407039464176a5080040c400c1e0005008071070031801c00c10540d401442440859400886c2d440c1d40d84200d1400c81c6042c42495040c0e00d100d40b110500e41c00300d900758409003018501c5200d04101c00c1e52101800d0707504052074413902d4005082000c800b00c4600045d004103030011441400c1303e042c94030a4950007010480803880100d50f078044117847c544681d04000301c158400082c01840b134044134035030400b1190311401040c0805e06807915243c2c0c0e1180d2007844401c0020301386440410502000140c418041d014405000000c0b840e04403000c1042c85c1d0712004a0103441c4070105452410f80340440e08507083c0401030180c420040d050084410801c410310041d84101d9075595030503c05402c6140200c0321441e0801d03094403440b0040078070800290050440c0f80c00c40d4172100000e46442c82c82c0340c0b0700d001e4485d514000c9051800440001070000054001d400d40c3c00c407070741030400825 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 114717095 1250 114715845 114715849
    0x70f03060b160503040306020d0e0d030209210f0d1d04021603030b0303040308030a050a0507050a09030204110d020409050a0617030409090c120506070305070c0209040b06060c1b040b 80
    0x10300140281210303a4400c00c011018001c280901a288611440c20b99042641d00c0d200c5000300e8128043c07043d601501c8000b1400040000d1005448140c1070707080450500d00c1c01008189400c03404500343c450854920002e192840f010001d5030280700e02c0004841c000c00e62050010000b40c03920301005107884101071040ba80b4a01070003900c2101c10422200604500991002c501402d0051042074041c0410480807003c9500c000003140715000da910081403504010454000304c07000242404100070082c04581c00c01507010b165401121380403035000c035648040342e400d160a44142c00700c4200091000a00280699075a0800ca20844045c0f0040182c1641c40d900304054017144c0007610003642041105000719106540080482405040c0f000d84c0c25444450461841007080c4040c1c0e0a680030300b04201d4075039410f01035242d04c403c040ca01000400c2c0d01e540031130103043c2c0182004100e94520b000141d61074840d881a1075000c00848120340d05000b1646c0040c075580d8100c00c501c3c0c01981000b114001038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 114718345 1250 114717095 114717101
    0xe0f0904050f28060504210207060f03020412021e0d0f02040c0e0306012306040b0702040c18060305181504030807021f020d06080304140f03010b010203091203041508070f03 76
    0x21180403e01c0119860082d40c2e400000d000080044407201a40360740b0024809007144003112030884d54001300752603800c060018008602100d141c1c41090300412040c070220001d10700241e041941900d9500300760040680c50700800d0080743d032043d0003c141d09034213001d0003500d00c62414514001c1c0c030100400044120704980c0000c800005c6501030740840010403031410b03c0c1e40700030300c219002822401903600318000104a54000d901c50780e5501004581c1c1c0c401e5290900c070fa00c59000860a18031411480c0d5114224114014032840e4245a80c1e1400210030300c1c528000d00d0b07003260065050300d402c41e01700c5042980c5003000b031343d0a80014a0841c0058030041c0000740c58104104d210f00c92080103960420000c000e580a2822100041d4a07010001140c60701040940041c2400081c40306245001d442445002c1d00e00d8481d0501c280c0c10300001c0451a45c01008485558005490250070b203070302480d03210320b988150751103014003094400316896410340c0075080b00d006e8041a40e5040c1054111351048007a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 114719595 1250 114718345 114718393
    0x18050604060206060d05010b090a05010e09010c090b0703051b0102040305060109110301050f0f12030901030c14040501081f030b0a0c02010c020607051308010204140a05030f0d0e0f0904050f 83
    0x340e8850380204895145c12801d0140e1188034000201d801414070022a245030400e684440c8001d0321800180310b8407400c071132119404481100208000580054001d215122074421841095000911481418450710440c2c0e0000d42c2c039a0f40c451044001c10049001b54003502c070a0b1840d0142d0000440c0d0450301380180740075100c211072164190390074181001150243e1608559004410010180460301d6086041c0e40c100b0402c0095030300c41d03000c500094241c0782d40010300c3c01000b0304882c4c91f044054400c01074400b51142071a29144e1541c40c40100702d05261b1b91a407010b5404103100f0000108028690b04506c140e014020910202d42c0707012042e0700740c0c3c0c007044441f00035030801000148807511540150182202c0c2ca5503075540c9664038080d00b42280e00581040c4600715071481e041e24a403c1c10b40c500801042c0035070003005455400c030200c07900c0300c0005101d003041204660104070907944102c1c15001040009001c2092070405180c0543d1742d100424030350710341e800b900043c03404100b107241d00054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 114720845 1250 114719595 114719597
    0x9010503072709051903021603050303040b07051b0703050705060f0306010804110a030c0305120307020706030b150307020c0f090610030207021201060b0a0909060605070807211805060406 82
    0x5200c08074503040c0b240e404850101c89030141d03030b100181d501040040000310002142c514440c86005014200282001081d10144d684005480e10400c0017030300c000122079005400c48074801c0d0701d03100d213a022161352181a4200e81d1940903444503c0900c2c1d00801c000b0200d07441002104e440c07981e10f0341801440e00440d0300e0b4403a104020700c00201c00b9409409c00c29031161160351224180010301000a602e4080c0c3e030029110415103401c2441000810000c0c580745651b042d95039800c602d4601740c000c1d03440c481030003040c0030136441c1d10384c1c200310f0703280d800704e02200f4158291a59200e280100c8000c0d55201003404003480f41c601105800d25a00341403528034080c0102916940030340d2280784058008c0d43c0550022a000309600e4102e8034045020310a28020b441a00442ca45e60503800740002e254210640299a07064030b8801c04202040e04801103130000d075072101216440d044d440c01c002c10401c5101102c0049400d58408810400d0741c131a400c2d60b4001b08600341d5010484d203400a014090240b405460 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 114722095 1250 114720845 114720869
    0x30215070207060c0f0c031403090901050409080910050d140f16091214060103050a0b100f120311070b0a0318230304091e0b030607020a0311010204080303040c050901050307 76
    0x140104000c919500c1d070082c0a000007a11540d81c7c1e50382d1000032194150140e22981000c030709201146401d4404034010201160140041c111b42e8903100020300c0780d000c003640300d02c0261041588071401380c415100c001508417000c00c405c003603014102e04461421140010249414400100441c4440c2254030710892181c4e24881b5143c00c1141d002154400c50300b0945c0d1608008010403101141040914040c51155010300140c1d1481d2801942003140505a0026021038000c2805608001d00c02c22048400c014900398102080d414103440c0c18956480e11034070380c0648580031170b00c49400c41c01402040b020303035020001441c1103040802041c03801100101903080b02d0480451014040d440c0010043c56002960703e0b090f0f0321050742d002c46081021501d0711603d0300d580211000058424042184001d60140c16140340c207000c000d40302c00c2e07426001801e000455100003682e95003541a9009460000c048136545d003050304156415269500c10700d4401d603003080002c205810701040721400c50310030fa0402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 114723345 1250 114722095 114722117
    0x10c0c0306020c0f031c0501210f0213050a05010303020715050910030e100b010818030a180503011e0f02040506041205010207020a0603020c16050607110a030b010303021507020706 79
    0x44000b0390702992040c4054410b080044a541d1010710050180f42d0740c0c004040721404c0040d41103010f6a6050b440795200000c8002031800304440c2c0c0c1100c0f480c0a80c0322a00c0b124001961000564a000b1191007400240c42c0004102450201d6403000f4181c0c1d000f40c007141c450302d6413002d0740c40020741035100c031300700081040c07205080c41d09111000d403500140600780898424140303403400c4d141401507118a182a03444e45010115035070410794080c2c04c180c244a4000e00341a080303000341d0303903803003072280e442e04000c1448a4680301c461f60040c40307006000b00400900c943c64847c111100100000c0d00942c035072514150420030041014400c03623044a00250505040c50328140514104143c00901a42c00e55000c0219000607520562103002501d4562030058440260000c8a46410304020b01004040312110060203241e80300d500360350303e050f400700404100c007070400c020541200c59a40010070b4104480004410940c011903c41e402c2040307884d0b840e041d6a034441c012039440306288130316400706054400f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 114724595 1250 114723345 114723353
    0x3061503030732031e070c050f01030605040e0307060b03030301050108070c14060f01030620040506090307030f05031908010b1e0c0d02070501260c070507030f0b060f010c0c03 77
    0x880c0450000d00f4038486009589804050155000c1e081c0169882e040043d100e03c0c5034030348031581c200c5180101111410005196181034021402d40642d61003501c40000065080e0702c81c0c0c02c684041c0a020784103100c510035805e42c040d83c070b4104142c1241c14500300a1410300905000065a0486405a44164560f1a40c4030706640245464005451b1500c1c1a05071001542040090314064840c001c00101558994200300c0200c56200e04891960345100300003480d4841c042c4159030540300304450701a501c41d0070b900007901c4c0500b5a84000c0c181c00c4030000340018081d011010b480c00440203c3d2001d83d890030344408943c045000d01514840400c05d10800004001c440d490b0b402c61014034200b03600d0b2401c460300c0240303400c0503070703010b034005a1241c40148003d5030300c160103e2000001140d048142100031090880001000b000c076400d2a8001c00c0120900c0020000c143c010b64015032400004e0071642829200f80d2801c035005401500c071a55003244952141c040070f100c060b0007100c2000342e0703400e40d92 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 114725845 1250 114724595 114724613
    0x4060501050903100b0310180c0e04030e0103020a0e0a09051005120604080f0c061f1403122811010b06070534060203130501080618070c08030114030615030307 70
    0x101d41c0350103100340410100200c14601c52103440c400c4003440806100c009180600c071009c0329401c00366001d500c1c00107000c00a82c103c100b40980100c2400d0250302c400700ea6a04507075414034004c81550141c1206000141000b0a500080c0105c0a54041014403511001400040300440c441d0600b140c2c40b0b20b000402092a07000580440034810139140d281484035061503251080545000d08650901d080404c56250b0071308850000308410300c4510121491800042e464600000e4400304450001030300000d000130f54080718030101840c107030f68400d20740182c0008001181d1031440c00c00561900c82c07900418a0020203507941c0c0e50340003000b45140324030303580c0c8003480c40400035646605007007103124400348030641c580c02c070058aa15030056884003d107240350251600d003030f40641d050020a006000c0c2c01d4a80e08140f0301d44051040f070140d1a0744414a0494034010980c1c40074000300b50100022620115800d90b4183c0c0b0340701141110602d40301c43d90301200899040110760342c154020082400040c00c000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 114727095 1250 114725845 114725861
    0xf010512040219032003030a051801170f06130b0d020607150c050a020706020304030b0a09051509010e0606040624050903070311030d02060106120b030309090703020a02060c03041a060402090d03030b0406050105090310 95
    0xb14121480b40c08145003107331450010384082160100c14002c0110a041a60305a238000c590028180451446200407441c08080b6050107401950000b03280e00500050110b038414154455a0410218038548070051150b041010f5110050060bc480000d11707510000645054039040a202c658035100d07044003000901044c842140c43e400344c001604065416000c4907031150580703000218a071070411403201e08103031005143d944994270304001403000480003030241003004203a113500748856900420988260140c1c8409541c1407241450200030030103111220802d402e27041d4102c46126400f64008c0c2d0b2070300402d0040304001005c61011003441402c9400c0481440006410350f8030303000c9810049000c290080341d00c1d001082e000907080b5010303a030402c012a80280b4084a8a0131802e00d030759003c0a202001210824031004400414084d90317031641100c1c1c44850003020001a0f09130f41c1340103000340104040d450301c01c0d454a0b000103400e5001d03100300c50b0b03003803001406001d02e5008040146d00910040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 114728345 1250 114727095 114727097
    0xd02060411040e01140108160f080a08090d060510150f0f050a12020f04170f03030604090201031803090801060902180402030a020702190e060f010512040219032003030a051801 77
    0x2a43c902c001032505c0d6030618081c20302e40d00901000d00010520303204012040d48812208071109074104040b10012608820b03040c0d00040c5591b4883c049400a400081024400f5218500e444103111040c0c80c146040c00445501d5442100c2000b07603840203403444035030f00e8001d0002c0303014580250000d5210b0402013074001c1440c00c044129001e072100800884c0c005031003d455110700000c00b801014000180d01311540c00b0f100c0200a4400d0020b0f0300d0351a07010103402c041c0600e880e0240300c000c581c026003140c140a403819441283c2c0308280d0034028040070b864400c0c0c034600d5203031003004280c05403103008480d800070345081e0b0100c45410b180300703010003580001c1204045607424000f020060780c0740d0703040c0b5410748000c4047c00c1d00c1ea814a07450701054440684002d1188196a2041c40389036004000e40f40c0c1d403101e0020200c1d0701d0b030304c2e8004a0000f40c0d0301c51000034007a44800020080100b0020b02d041c2c103529000c2e004180c0803181b0b040c595248601c01080c4045081449100846001420070000d0482c0c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 114729595 1250 114728345 114728351
    0xa0b04050115090b0a0803040308040303031820100201060b1e19120606050403170702011101150914060a0e1009180501050f1b070206090901030b07020d02060411040e01 74
    0x10b151a00c206251040e0855000c45465150445040c41d007021800d01520458010b07510701851036440704041d1049200040074180c44011290a00c04a80d44844406d6006140d01e0400704040d00f140c3e140c3c000d443c40161080844a1b85025814414030807030050383c4e15058a1450549648110100000e050326074400900c0700b08105154510000d08040540c0300e10b0712030880800745803401c0006c0c0d81e40d07600301030308204003400104045408900546641c030f0030341a529640d41c2d05400101c40301d0f681c00714162095824120111302c802c08000305d450403a40624010032104800c000e0910000750255002d0760b0090f0007020520801881114483e0002c000c0180b0318042e0350b81d14280c4003900c0580b001c0c101556030000c40d4405001c828050a41e209480003a00c1c1c41514018500580303a900d0400500701800001c81c00b04110b40311a0200d07102a800208000000d6a40b0700e0b00a8940608682c00e80041c00b5004005100ba8000500e06003d05d5014140c0081100908240300050400e05200c84041d0740b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 114730845 1250 114729595 114729611
    0x30f0d0e07030b01030c0806090703080d0f090c1401020c060f032d040314090d060203070c0602190905060a091a040512010c020c03030f04030f1a010906050907050c0a0b040501 77
    0x301081498000c500c2081031011940c550b0a1449561801c1d03404449950001c90805c00309a00209014051300c0e803044000b03803901000780325030004040d9440100c11080c07410030307600c2c00c0c80500c0c410034048401d14840741e406500c00000498907542e01407500c681200090040f001d60100c0040030b1a07008145c04100141e003003a00003000001c0340310241e200740780800c03502884141740d40f288240c91074020000c0c10324a0300c2e803c00081a000000e21310042c0840c0c0e4088007240c130031803081481c090081d801c46025502d5008111035180d48124045100c0049089080c2c00142810711506444032411a9281c01c5d0086151274000c10040d180030304841c02d41c0d9070030000400c0b1a45c0c0d543c030320010060014000620980d60703200180ca00f82e421408144641c1c020301c00c1d0f00041d001d990407501600d50003840c0022001092400703c00003640108204420745d800c00000c951000140e011104803a401c80d1140083e4403024030568051042c845096850b030040d1800001081c920780105070814820000081e440c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 114732095 1250 114730845 114730871
    0x504091802030d210504110d060e031b0601062604030909090b061203030112060b060d020f030f06010306031208090f06070c020102071703030115020721060e0609030f0d 74
    0x140303558800c808980c0c10800c03484403111341985071403000900742e03041040d4149502c03000d40c0f10007160034461182c003a824041040082d2500300302c01c24581c1e40216602d43c4240c0a8400c08075140405041a521030741c000014120700c216281810754600510481c62081a401c2d8007070441c600800076400c0c002042000216203a2038800c0c512601d000f0040e50030282003803001c00c20007042d1070900a1099105000600862000301d1000d0700c6240e0016001170b00000001c0802d05501070040c1c0000018400701d050010400000020b5210343c0e892040d042150391804015001c032480d600000d00300d86006150050580e000302d02c440e401901c1101240d1b64a17031100040d602e82a000c03940000040e0445410200710b5804100142c0a01500408641c035081400d000e01d03500d0105204011261040300300110f1410f00078494500a00314150303098088201d80000032000d5268908100c5107180740c0165407006d0b00002c20302c2c90068072410301461030a520110f0042450b040b100c0d95810345580d03010481010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 114733345 1250 114732095 114732103
    0x619050a0b07061d030a110a08070804030309061e0f0210090507052b03180e0a05060f0f10050f04050a0f060f02240414030d15080c01050409180203 65
    0x785001c410441d6107907440e2802d0015200407101d400c101c4010303210000150072021080e00c0703412a046c03505c2640b1a2004060394030340200310b03c02811f0000009050801d100c0700100800943e8088d454840015559900441d0620803441d5480841d03114014181f0380f0b603100c0c8007035031034240c0140b0490300004050240c0310704541c140841121140c1c4200c004000c641043d000017003c9903c602003030203c5404181d00a82c0340540510024100610b560550300c10f12842141e05019001d807090818a40c0b602e407024000a140541d250342c8282d42c00141c4045600d00790340488172515014140b07a410880f102d905445640040d1100c5072070303400500c40440c0703986412200d5001801010801d5850070300e011400740401d0300091003041150401140207202078010141f0070850240112003981c02c2d40e0760f06001d6204022001c00000e40d000000d580007100107242c12510f0038191200400c45081d13980e1940540c0c54415103000e501044050004000e00300d82a4049a005d0b0350100a5008850403a4006414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 114734595 1250 114733345 114733349
    0xf06020a0e130b030106060906050421121706090717060f03190c091b080406020f03130b010b13050409080903030301060207030c0503010605090a09050124180203010b030619050a 78
    0x302c41d54440850b840c51900340110001032800d410a0300d10b103414110001c206206902a800c100302d100706101a040110003080744005402032641e0102c0c66503031300d0051403884c1f20752142d1031200020f8042482441c161510303a0056100c0d440e40c44008082c02d0b1100000d500060281c0d40c410041d400c10b503220b480034000c5503400c40b02c00010300128030040c50401c0d250192600682e040078500580f41610301c0c1e525503034904a0a1130304204480d03035140d2a10402a20800040c410207040201c14048680c1c10417118aa1941c0300f015410007607a2a880490942c3c000c980f2401e03480e150140d000c00c0f29041680c8840180c07400307240c0c403c9c81c080002d07011038615882030b403140300107074440002042402540e607000c201a00e4120300030703c0514a4140010742e0010301400d0820016541d21491007044405d50103092221300701c402401c41e450303511000c609809054800c01050341803050b045189901c4a10840b4140c1c2d035100001421500d980040c051078000180309080030000c4050702007010740d40c2d1514100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 114735845 1250 114734595 114734629
    0x3181203070c031704020a0b0d111b0d020109050705100212030c0309070602031903020a051303060c031503020a1403150a050a0608030909280212060910030f06020a0e 73
    0x155000b21858000c000302c510110f0340c1640044041441300603690380341c02404130750030f001aa6880d0400800c0560040803200e01c506003948000560a4401070280b00b0b100441d800d2000381e440c000c028840680c240d070040c000080003900726000074400c41c6048004044070b10524070450b0f160010000400650340d1066803126500b12021042181000e4108040340c0036103020310140d42003890395803107101d4090700c2c141100289600403a01a04944c403c206940700c1c0c4900740e00c0c000c1d0307859030303070038005e00030104c0d02110000079042c801950828041003200390200d980c040c3c0b00c6004140345c050310320720000018540c4c6600d4018001054000d64055903543c1c06005403540c0000c3e5820b1501646084840c80e5000c3d80382a0818480540c01da562810b5142c0e0120100c0c0c1c810084c031039080c4540c20b0082c602c500d02800148041541c20102d1400d0741c40e940f050b84151000c542a895103c030f4600d5090381440014050750039589800c0c0040c03499006010004024200b810103403221f000011000d49a0a00e40c007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 114737095 1250 114735845 114735857
    0x120e06010f05011103040e0c0c1f05100b04181401080105090d03090809150f16111903080a0201090b040b040501060905011505071509030801080d090b0318120307 71
    0x10062401c1a06204010682401c2c14090621400c03095902d034010781c86406004000a0002804400d505040711b800000f8031058a0403801c04c030581c40d04000240805046503850000041d02c13070010008890180c950504401d8181440c09541350190b8404060500100b40c480e0000c1507000203003c0564007805c070504c0040340d180340950050717180c20240c000d04801c02d400c151801003c10b4003031044a940800542d2104186000702100140c00d11682c0c070340491058000800c60140c071014074070304200300e2180c02110b0340e82441504110300100318806080802c00c02c0c40c070803c009034240000380261841800082900a0b550300c4048400350f0440701562544201000c00040150070311400019001c42d13102000b041d4100f80020407665924000c030420301200040c00410f000390306500c2c06841c1032101041c0306041341031800420f1070100b88a950040d215001c029a0158050a20b090541d0600b2440c030313042d43e0b542e66401c0c0000145006210060003011400c20000008900862003075115494071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 114738345 1250 114737095 114737099
    0x90f1b090e09030d090803180105060d020f0a0302060a2c1008130b040c0303020f0607020c010c03030e0105011e08010504080a03050a0b0a0602060717040b01270204120308090d1e120e0601 82
    0x9100c50207110008013488d03074507140411111713903100043d5084442e010364100740e1211400012404941e916003010798805800300d000b256440e0b11900140c641d004400781640c003014299440d10310f00d02d407201c409900100d80d82e108110380c1c0c171881540b6444100e0b1410704443ca18a0345030010000300966080e6a4586181000c3c8140342d0104484400c001d4090000c18a51030302d40300081d160715030804a80e04100f6802043c409043c131a030806c0c49a42c01c05c02c0204002c0d65640280552500b00d00d100401c0341290820020740c0d190107200b45803045410804003407400403031120441c01440c00030910561659100c003801a140c03201140c20b0064a01ca4004002c58200454080d1941c506841050008600c1904104c00504881001c604540c09803110109101c0c12454007011001c618a0342e1a0f20380c40810006141e8018981307906900f8042d858014164444002d00340d151070f00300c6000e0002c03a040080540644041e840720b640400c901d40341c501d240780c20440c00001a120039107602026a8024401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 114739595 1250 114738345 114738361
    0x81e0a170c0c060606090103140a050906060a0308030c13030614010f0504061a0d140c0712050307081302041104030c150f080403050a031104090f1b090e09030d090803 73
    0x20a5800ca040540c000781040d82c405201962180c009000900401d40451030020343c0e40a90048d09100070050f610350321501e4141e0102c00109030848041010303119131b0300840c0c5281440310044050340e0b080400d0174959a10345d00b200300d166009202401d055a421140000030480501c100400500350030203030555545480302200c41a441da4000c544110300c1c00c80c013001446040043d00050400381c1542d161a400b401503500002c0246070507002c400398010f0704010440b0300201c000c0c1000c030700c42c11403000c0000011000b2078842c08211000c20110b01c000021403400174150012041c4030384010408101044240c1080d2203d03005640300b00d4494111081c01e0109202c011214107804025150081e0319420491004001c21006440902848000100031003410300ca60040c04002d0142440581d503507581e2400c1000500703203500340c800a10314190b20001c2c2e400100c450321403c0c042c569522064a410b10001414090025001c62001c3c402000b852554890900840c9055406100a03079200d18003884 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 114740845 1250 114739595 114739637
    0x30c0f0501020903010f1a130b03010606020d260601183803070806010c0620030402040b03011407121d0d0914090406020c0a05010e0c040b01051204081e0a 68
    0x1b0840c0380c5401e09011580060300500e0012142d0400c0342d0048100c2c008400034130040000041c0d00343c142d400d002d008210140c001076103107146521039454000c0101500b04a09440903112201c0c0b058080c0720000c00c03015880f6161215250b00719500402c80c0941e0f8151400f00c035a110003030101400e106078900c1c40c0345400d240900d850f007000700001520314542140c0c0140750000c000c2c04a0b05004148890106000c0030354442040c200d03180c81a034a18440301c0c41140040e80003220224030850410000010f181410b000e52001100d5004c0e807142c90752141002030300c0d801517058003c29440d07522222000b115404413050083c4d09510409032142d0480c13100d000708140d20b03980061300104185070688115072210340889901c00c0d0014401611090452103d1b41091100540034200d036003000a0710100c40c0e0f0100b601807202004840801c0034424540040d1184d000c1da1310311000d1310101c200080c2c04640c030380c07008180482e50b0342e140320292b00840c0c5604040d40c1103078000c81c001540404916a001542031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 114742095 1250 114740845 114740861
    0x305071b050613050f01020f07021c0b01050f040b030111070303060605040e0406090804030b07030f0b040b0d0b060a1505071209032004151e0501050310030b04030c0f050102090301 79
    0x22100d80380101592500355070b074038016200307400c0000d6828105080c03103c140030701003034884030600a45d6108201e4801c00819041044242d201d20a24640800103801351072080c900d16500c0500c600035030307281404105880c0701d5201c17010742041e1a01e44a170383c603580a2094045c800418465a52074034003908004044075060381055050140421007807007202d5081c3d65259015600c0b001c00301e2002d0942c0380000650089a1000300000c0b0b02406000601e90981c200c2116003101172010406e04120004203c140e850101116030004120300602d80410414038425030300c941e000c0d189001e010342e42c01c11418400c070b9003080d000014070080342030010001d12049c20640b0f00014504810601c1c11601c3d004100c501c082c0b9000041111f41d07d11480b21349541d0025810b000d05034800004040c0e680c041401c03503424a020402110090190200701c40d8061000d9900078150308000c0301449046039035681c0611801341094050003140065400020b00041c1c039200300074481e000240c0c4070301c0c001c0213040c00c1d1040c036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 114743345 1250 114742095 114742127
    0x703080c0c040e0a0803040f0c08030a17060a03290108030703080a050709090213080609010e15100b0d1404080c16030201120c03060f0324110301060507061506030507 73
    0x109107442d002400904c0058854201034240e65071348540c5806c1803604209000101401c01c0501c00052003000071000c0c100c40415511282071000b1104d14020405100f01c4143e41e104a1208013480411200804910103998011545010501c583c10420904038243e00c12032869100140700410035901c010110303004a12803000344030900740710300003600320701050150304c544a41c01305002e0b6012600c42d44203402000c0440c1036520310b080000c0c02e14064403640781c1d8040180b1443d40c0c111000d209881c2d216100300880282c00c141c180c1442274490403640400058131501d80c0f0341094212102c0f403103010500036489034031038507a2003040c0c41c119400e05000c45c2d0943e201d648420010030260f6005546030360128854000002c40c3c0c40f80e02ca00358002d181c0790f04181c04071009180003000700101402881c0c0c0000d1002869102144200440026580748802a00b41d22005100410606000380050640c140c424074010907640230300342140b401b00c00540e01c2880043d840d0001c1c031241c0d90700720300c40743c54039181c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 114744595 1250 114743345 114743351
    0x4080d1b050c0f04021605030309010e030316050903120a080109060821090a1d22080f070228090e0a031d0a0b0406030e07170a0b180703080c0c04 64
    0xc503032940340d200e05441d5100b034041c1c0050401c108460b5260303411118072851000314090701d4601814015529001196615481d41c80e2140b000d410420000c1600c1c0b180c112383e2034804100c0030f13088084580d42c0042007000c2e01482100b0070140405d00354005801c503056507903541001903161920210030748005a210003940e4101038000302011940341103208a00140c61440c95440c5401e8002c01d003551290f62080003240d6054a21014668401c100b10b401240c54459110040000360095110b920700544024007001082101703078000304510b405004280c0c002410f0900026000200c0489450580c0342658a013009007001d1044bd259846405003051060b001040501403c1d0b4020700b1800c026410304075150030399a00d202840c0d4541c510703940502040c00e98076480715600d0310090050400f18290590600503480041124a2005a40c80303801d05080010904100f07240c5440056140180c0300c1940281031b8914660801010444003004600c54502690ba4044d104162806c0400c2a060148aa42 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 114745845 1250 114744595 114744647
    0x102180103180f02030309060c06040b06010e01021c03021204031101152304060b130e07080601050d0c02070308130303030f0504050c091f14030f2e0b03010204080d 72
    0x7444402e100c85030310905070000f684007400001d00c1d6000388000103034001800152400b1101e80410194000c0f40306840940c01341d01c0342401541c06080c15081d640c0168400c030301c051044413000c05442910901400c005181034080c000e11100a4404c444c2a000320303660403165100c0319401d04c1a91411961160740c604128242a45201c0800c61801e040d5003e0003000304c205107980e02c4c1d03031000c4001c00460790801c0e03550b40b51006030402c2140074828413000b01403140008010070701a004082c4108416502c4d10300d0442030b401944000c180d10010141140b080c43c201000003144c030343c0107001c182c07040c2d05100c03000c0d8910300e40241614140100321144500301024000010320001c1c0c1009946e40403201015281e40318903607240e15116001c018544d00004240000c0d40f030651200390300c4420020341c2516030804035540850f95a101000600c0e0310303c83d8030340380c0081d0300081c0328240d84d0b040103220001c18510383c881c0000703003603800940007003806800180103010100e420030b0119207101d0f008028000700034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 114747095 1250 114745845 114745871
    0xb0417010c0509040f06050406030c05100f020a0f1109092a0303040b0903150c120a0c2c040e010203060a06020a03050306060a0507021f12022a070e01080102180103 72
    0x3c040c149695001c1c030740340c0a45441e01011750300144040c000103030003004016503c2c107042021101611449008030300e818400782800b40700da44200c0d00d0700659001040d00595541c2c0b0091402d885c51000d0303502d01490011000c05644145500340640d0381580101041101c0d002d03584a41161620074000c0e20401c04040c11a81d1004400c4d20120741d155444181c031103a032140440d0070445810880c00380000c18100b0445094250700250a002031205181c0352a540d50b0454681110101b24410000c10758540380044103150748500241004c030a00444e260141c03240c4007080542e00040c8240b10581d4012041041c070703041c01200b00004061a00c02000c401050791800b604505c400fa00c000d00403000080c2c03a0b40c21034001ea0031a040154003400e00040226800c4014845010300400b000000d4200400f100d9044114026155014010481070001c0c0300b00f075000980742200811200464003c050000407940459001706000707144040015946680b07002185c2c010340040340215040c5031a01c0d000185803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 114748201 1106 114747095 114747097
    0x509090102041d010513050901110c0a1a0c03040314040314060a050a020c1005040f0606030b070e0303031b030402030703120309060f111e0d060b0417010c05 69
    0xa4a015038500503010003c1c031803682d200281d008404003c46c4181c0c8001c0d0007040c443c000003001c2120300c0405030541c2103403038031101c203070088c1803840b082c0000340da90510780030304072641d003401741c03404042a096a0101038030180402c650390040402c0141c4000480d00070b150449588140c0007141b040d00342d9104000c441640300c2d0750611000c101c03507912500980700c0700b0036074902402035800800a60130090a00400640f4401d4150b0a07442c0842d80c98894000514059080f4841510f41150060030440400c20511300a41c0104200b02400c80c010b06050118861203510355a40e44542c00020f240c5226500041c08501d01420800c180710303013640c0001c1c25148903900900006a002400340100c400c0d41a041400a100700418480449001014903200100318415803c010042c0140c508680c455080001e1510000030140121505440d048600d000038130028440c583d00a1801041 = true := by decide +kernel

theorem cover : BRFrame.Cov 114568345 114748201 := by
  have h0 := BRFrame.cov_init 114568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 114568345 ≤ n) (h2 : n < 114748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
