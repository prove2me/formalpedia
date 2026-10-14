-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1436
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:58:42.259633+00:00
-- url     : https://prove2.me/submissions/fe8186a2-cc7a-4f95-b36d-379955934cc0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 258093525 ≤ n < 258273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 258094775 1250 258093525 258093529
    0x90a0b180f1507031b0204090c061205010312030e160807050a0e07090b030c07080d02070303230a090302010b120d0f080705030414031215030c040204030b0f090a1703040b0a0b 77
    0x4441d01100a003800140740502c2800040c03180035030005c0d6405001001001c03000d007070007140700e81280300d010b000641040388540c0b100031500030b2034104e0f68480e0070000034006142c0b0950146c14a070710403500901c24802c100d1071076130158204d80014401c4d18090400035041005100504525420081002080c2014010f81075404401d0350100c501119400303803282c42e4001031109501c03036894054558000030030385c44c1b2881c029500a00e561071007a01d00704000040c0070b408030300070180f1540e41c0c01803103160000100904802d812000030240b00388000100001d03640300289034000c3d200303140017141d440310b100100070035005484200e4121560600001900c3d00c060010814800200024100c0700302208000030b00900b0010b980414094501503001b80c54405204801e1980c0010b003140f0070f01c41c244100000341418401c95007600d421203101409541c610b0708401e046034014204106a1181c0c80c81d0001117144003039549150480340a183e0fa99040c1070030141e80f55403020b03085e822010300d01040580a6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 258096025 1250 258094775 258094777
    0x9090f16031506081f0b09090112030c02130b13020306011103070b04080702010306030b1807120b0103060509030f07050f160e070807091205010b1f0c08090a0b180f15 73
    0x7100c0510b01807072290f903070032140d4081c05c00700c5100340a01e45121501044c003a07090000b602d00010151049845d5070f9960b02d0386542e10710716910140c00b00b1124803120000d42011682802c0004840b800031403184038210100d0180c21440d2154000541d0200920080b503a0000e007941030030010100070b5003403042c00d44540d020004041c0c401000454001104002c590113500210000d6800c40700703101c80d5103420510000940801107070b011f094054403c010a5803445000800036841d004051003071180c1c01c43c0e4481008200250805103944401e021050071811828000d0030ac06101c2c8002d08450310541c1a100d10780020f10015050109003021306000e60701c2508103013a4064402e1070002e495807503580050340d180e10203822000740d4039956150a824040150020840c03404191604601003441104807200508400c11890004a211707805038041040c0ca4040c060000d0004c3c40c03004040d80c0c03034010558503406009491441d607803180140000d883c2c541503040324060142c540c2044186252246802 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 258097275 1250 258096025 258096029
    0xf06030f070e0f0603090618070609090e070806270106051518040c090e1b04151b2a05030309191a19030e0a0b0c09090f160315 56
    0x1c0180c00b000001c501e50719000301d801c24074000b504d4030340e030303800c06001054481e14102c03001170701c9041d010706d005141003000a01c88126680759840078043d500308031862001d403181d0610050381d0b220720b800c04100d500013401454002c82c1800028103c002d07a0310b140b6900d07640103044203041649070007000c102d142c1b150b0140403411007040c03441503554042204040440e654821603543c009190190a00e11190081ea0300740a9401c0d0150b050555a6125200c98450760390501030405d1401c144001c010512102507841e44911309030800d0390340410742c03511080351070086110943e0ba81031001880305640641c0c102c484c60700c0103031a403001145800d010102c1d07504d1060038502d50007180031500c090802d0080c045640040d0054009084000f1040401040d045d0800080580550b540c01ca05502803806841101802c0e541c09003d01a03810b42074075144100c02000303124035008c14007000440003a5940000307030f038468044e88080d1201805c00248101e01d001821403036100341450040a203810041858100003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 258098525 1250 258097275 258097277
    0x9240301150512010e011409060319031119020109120c0605030c0408030c010f140708071409060703020a05070801180807110d1103011503030f08090c10020a020f06030f07 75
    0x1004046154125840d01c91100c00b9003205444000100e100114030400c20304903150380c11f03080341c072207251010420110429102d070341e41640200c1e05080c800060196104d606400390400704440d500c403046031420410904803c0418003143e1030020110f6800810003005040002615a0000c0b520350b80c641c0d0164a17805120b080c000c001c00014400c0e40d00004a6003d00b0407842500d03200c00b50641c0d15400303401480b0b110100e10741440b8400454810030840d441c800c1d581540ca84495454410043d41c3c3c012103120030002180e02000110f041e03454001c010301c504c40c400d80c010007861509042180c01c00409810501e8a079041c000b40c1d012410014540810803500010902da8484061800a412010155200d600160680814418403840d01c07444d04000506900074082c125881c16220011403003404020302007100d1084409000e0302ca4464030f980304c1284811110300404240025140000345804400141c9c000c040660450138480211414040300340da210b0b095050250885017540c20082801c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 258099775 1250 258098525 258098549
    0x70e0c030613020d060320120709020f070210080405060c0306010212090406030f080414040903050f07050f0f01020a140421060605090f15190504090c030507090209240301 75
    0x40301030002c641c115800c1d40000c440421005580746099044079060f111081c40c0710062013141417403410603202220b058075030306014041080c20618280f0080d000768180c0c404d500c03070901c855401621032142c0c0b40710703082103502d5030000f510b014a44a840c0100080203007580c10030900a021040e6000101c8001f44200d646c65140c49541c0343c0c0100340142020340c0b01805d20451086810144046000200256a54403840100c400f454100344404c0e209080802000100b00f00801a65441201d02500820f0b11139805e403010784090110441ca40798a1400100040c0d5000a80412243e0810580b040100001c00c456040c9881c00400300010248500180304800c0d54001c0a0300f00035044d840b020240600900005803410811040101c81104850302451005005414102c1d403070f01e4454001c2520003400300c0711000c2d04160602016041821080f40c0181940e4008030018400740010800707003107030000068440c0ba01e11f0030812480142c5441c0f10400d15400b420100011080e01102e042d00c0483e0584 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 258101025 1250 258099775 258099799
    0x30e0307151b0926061512010c02070501110a0f030f020106120206031b12040c0501080109090b01030602090a0305010f051f08150c0c01090606150e090f060315010314070e0c0306 78
    0x42c0c011050022004a01d4001c1030104080b06d000303110100000c000079645c1006512680580600703c5524441c0310707001d40e003c00c000304000e600c1204403a4040c441383c41920580c404560b035820301c01e0f42680c1c084012447c003e02e240340c0c4550910820000782807200080d0403100064003c5144c030700c40503101c007124900b40c140c01c030311200c0c1c0c3d002100e0709010f210218124510380b50500c3ca604242e00c0c001c460002c0c511718000152400c850146142860700030840d0744090b461035a820307009510074031402e500200c40120001c0425800c0c030847c101c203010504082410310701214230940101c414020446d030b00351100c4040c8496100000c40b1095a0703248046c007401a141c80c14514824000c41825403803949c20007004604101150300548112040d41100c071601c94485401542e1030f01041c40445e0b000240c6d400010f80b01e02140303c3c1c044d000340014040d124041e07a000c00d00305032440d09030401c2c1c80088180c0c00300d0202075410810000101001061021542840030700000c00748406409984030b589400c01c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 258102275 1250 258101025 258101069
    0x30403051b0a0c090e030a030c03110a09080c0d05190c0312110d020715080604061e1a0a09031101110102040609060e0409030e01080403030e0307151b09 67
    0x11541149801928000514840c529040d5210707584441110001d2100c0f10000350320f0040d0003000c440d10400c0b40a1420b1500018085006100740d500c450201502c074a40001001400c2c0001c1803d004140d80d002c0046042400141c9052808449140180c2d40f5920202c0465008a5401c01041c16180c554004050b241411898080c0d2600043d00e040c1c0d010069044203500040740c40c0f02c118049081c0c03001c400559900303a89542c1188166880701411a403441c94046c1b141c0c8e001c81d8050401000024481e8454452001601c0329980c1c450004040020500c92070804a40340e40d1110308221400b46010018440101220701c14400102071082881c1c0c0044640e005122031802c0310503c0c030003151200e0345c461004110601511500c804100101ba8400c0141401d020b00010141c01d0b0700c0d280c15a094010044885c2003009000364100355840c41d880c260040280014000c1c14081c0b0a02d40340f2403e040761000c201e43c1070f81c03c160384002c4040140c03203c0b40e030040c4d40481120882e111401076200b203000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 258103525 1250 258102275 258102277
    0x11409070608041419020909010507051e040f0b1b030715020d0e01050723091e0d0f050303040b0601030e060a0e0114090703050f0703031d0d0501020304030c0b060402040e040803040305 81
    0x642c01304a00918100a032003100d41c0e6203070b517001402101c260402d6103071206031b1030884106681010004100300300050000c3c280d08140d0b01084001301c1b186141c295181a01030032241650080c0c1d0080c400060180808400301c0740702d5080c2520f150140d8640a0070b95142c50b001c0562101054496801180300b03030308040036911280892221800a10151034607640050041c40031940000002d180c04054102c6c0c0c24103a8243c5d0003a110141401c0040c0302c403400c842601c3d8079402c8180740d001c001c070101342c00000c100c40d40f801c14480c400c0008645a042c80d1524428200b0014066410107103800e252841c140ea0015166800c202030030740000d42e54801e03803034407409004109040d60105001c80c0500003680d1000840030220b034050001d075a485840c0903c04c6da00d4a02501c4082c6c005904000001104c440c400e00180307180d40700504503a485410741d5103160076a002102c05a0114070303824880f1080c021a550801d038894400c0368114940f5061200024081e80e003c0c00203041c00d0001702c0000c08140c09030b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 258104775 1250 258103525 258103553
    0x50d0903030b1003051006050a020a06181a0a0507052b02041d010e060d210909050c180f0328050a0f1a012d090c1101140907060804 58
    0x2903c0c03880301040c44000030700030b08400c2da0b9080c00780e1012400020040d200d02c0c2912044500c83e4041d2580c606603440d40f10181881c0413100e03680340c40c030b01d04041c00034103500308501c0c9644041100d6403040c68103114290444400800f10014002e081244e44511001c28000751b0b030001c00301c41d060805020700500c3c40300a00a581106010402c120402e81a00d0400c1e02154120348844400c05180c0e912a802c0c810f18420b00c0000610030303900d9102441a10181e03100041c0140707110f180084025a03180400c07030607a0b8041c0e03169803201c04000b51808000900301980024001d064a0403c0c0d40c00d9048003080d90355011880705820b10841305c00c0b030710781c00e501201c0b080a03440e0000100c1b0b041000e9030030510b001c00179502d01100c2903034400c00280d1130400c60280c05812101d40c103080d045155814107480401d049800c040d110341c200c0c0c855000c549a155480b500c60460080c1d0740b8620414003903012542111501c0b030800e21000c000c00104011072100250301c0742074818a01e41481d0a40702c5142c45014103100c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 258106025 1250 258104775 258104779
    0x30f0f07060219350d180f020d0302011e0c0e03150c1308100516080c0a030b0105070b24010206010b090d080f03010303050a0306050619031802030f0304080715050d0903030b 76
    0x3403210b03038509411000034041100307545c1410000c030002c020b0318200441c1000c0b002001d007202141001e002d0314100d003a022195011340000701d02c85403800b1038000c2110b00701780101c5040781e8540c450b0600c1c591200e60100045403c1d401440d00240341d514068a0150090401c1980500010001092078010750070400500c001c40494900d02011002c081c060007007110b464086143c03800c02c05d507816109680507405482e2103018036151905d5243d080b0080d0080c03100b0b4074148502040240d00140306c620629106a0303480d941c05985088402c0d00300401c02c0d060407028115807140005001e040d41e09070865054482c2150f0f05440d1201c3c0b840d043e8030600a500032903171442b070044000400d1640201c01400c2e840c1465600f00540d6071600104911402036070442c0da8101000c14245405031b000303034030198851050714031160205066500181c40c2c40c2c070310407601095800218042008000400072403002c1c04414a55064002070b50302c00811f603014008e05c5181c09601c4c0c410b4101418000d41c80140310b0140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 258107275 1250 258106025 258106103
    0x8090102070e0a020a030c05040b040e060409151409010207021c11090a0606140c03030703150510200a030804030806061b0607090611030702040f0209030f0f07060219 73
    0x8200b142001350083e1160300c1c00b080c02d240c0e807d1400303440762007111f0075110340d43c00c1d80e400e20381802c84500034407200a0042d45c0255440fa9010b010622546920001070705500c1c02240d40e020890314106015009040b542c40c1e68014411a8010780c0c030000c0b1103610740741c03803598501c0000e1b80c0d0400d4000c52010b501c243e50001c0d201d0091006507602078010b20190b03039260720f030242d20000420010140348174844004034140c20034000315410900c80d070004181040702201420030f690311240041e1400344040180300114074110703011841306407084000b01e2503a00a1010b0840d0541c40e80b00607100d0800100001e00304a060000582c2d207039a042c090328400010b11101e89010001044201d55031082541c111020070100f07940091118030905440702e0309803404024508107000b41e07007030002030700413401300030382c041d40a10040030142c90400072180d0505c031001c0200907400036079000604116240d001003003150010b0040403540d98a118456600a9005030710350f02d01790b4602d00d24160090105a6149000c003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 258108525 1250 258107275 258107281
    0x70516060c02130f2306060f070602030a0f0f06081501080601030201081305010c0c1a0403020d0302092b0b150109060f0318030f1106091b0d0602030c03010e13020d08090102070e 78
    0x205e02904214648114000c0035140c880d8001c2007041d011f10b030b030030b0700c20b500b0200216400941e094014580201c0718082c003240283c1c0d07030311000d000c1d81d004014010200b03a0b114010011880108803980c40c42a6040c0304031800d5042243c600c1e11071005010180c1071100510200344009100640010929000b0000301700e00400010300520101c0e810314145d401e48401c01001c500b00e025003203600e015560540041c2010b948840040d4013030741040a00540c00440380322901700380303c460118142018607003081d2070420f007410b02d4040000b01c80900300002021040214646076600301500e03005680036418032103500740e06420110041c0030058074884100599010700c2d4101a04007041c041030360a1600d6050081c16140317103140d629071003190426010751200e2a0b046000c600c24071160031210010b0440080c10003152110010303a44241d0390300340300a20004c01008401c06d801081038200f2001d41100b200070b699900080c5849034110005070260b0703130000d980141d0713a00800401004005d455841e220605e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 258109775 1250 258108525 258108551
    0x40806040c05100903110d02091005030721031803141c02030901170601051207090609060807120b0f030a151a100c0302010b060f070516060c02130f 65
    0x8015602101c5850403180c0205040c604904140f103107290f90343d82d000c142c5185489006049050b6524035420030b81250501e00542c03a01503841c1c0c4511511840b481c142440c05041c14a040311542c05200e80c101c0c100014224113600c410000b01140d003500e8201005a0203650340d10985000d075000414030100903103540800c0c00d0229100072200c3e40c1d84010f06840105440c10f0b40c5030310900240d03600090086812070791070500e40303000a801038030626080d030410311001140c0c400c1d01c1081e5000b10210b861803200f00201540304880f00c1c0a030450740380a201d00c2c01c20460182c22411900695504541c60f8603203001079895200044161a40017411145220418240056940000f100505880d41451585d0151070039428038000d03511400703440384005022842040782c1c0550304540490031552201500041030f91171502a1468140400b402540c4041c0c51510701e00c0c015800440e84103d28440d0001c1204680044403848035a8050b01d44107031080c1101c1c4c69600828030446400c078030ba440c0c071000c41244 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 258111025 1250 258109775 258109783
    0x1509010617010e250b03040609060e0f0d0302070804050607051c0f11010606090513090501470d05030702030604030c150209060a0e0d0c180b0d0203032209020408 71
    0x20712496020f90701c10344d10404560410020305000c464254210030002c0101aa5840c01190300034000d00340002c0c00c00c440d56542c401c0d600c0c00241810654040d14002c210080c1c1413161480509580c1000c61405c4007a031703642140ba000b01c1c0325451007000003003021014440c003848000b240045083c07200243c03c00d0042d002c0e21880c80000b6030030005001d48050342680d501482000182d81c0d40740c644194061529042042d106003400088a645485201c030700000358003400382105811100c4405400300311a046d1f10251140b80d8500008200d43c450031360500d410881545194001043d22800d07609103450400529510032854001e405108081c104003d140d400700360704280510038a01500311400411138003040e40907443e01160311a104000011101d801843c00400b078403405400c1c1029011107481d907441000b620740c011201c140d24007202c9111040d5901c91540744e43d0088404a1742401c643c0c000c03070f90702d0049460b06030401010001c10700c0411018540c807401492030034829503642d40c0380c3d2200d03a11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 258112275 1250 258111025 258111041
    0x90406060f0e0d0203070504020304140109060f0f290111120309070e09030301090b0a050324090d05070206030406021e0408060a060e04020f013507020708150901061701 74
    0x1410b102c505502883c1c1903080d40341c8150020000c00c41141010100802544041c2040b1000d0724012040c041e000300c01e000d6401c115000d4900007030341c3c9000c261440c8c00d03144210a01d4040c103182138030620000601c0d40d15025400c0324a840504c800040340c0041e500381c440c10394400040d105100c03803004003403a050021486501361005880040d0f80d106440300b5400e80aa88090007900140010302a45003079503c5142180f00c0241080c488941da6804a803d0441c07407640260b440c0200c414948001c45c44001c1190054101c0c40144a400d01701c040090207030041e050024420074001000c00e0030f1102640544000c400b64841c16901c90010003240c80741d0382d2240c45510028016074000405860301c500c201012502210001040c0340e03070380d5003040402a000b000c102d0621064a10307084803100900d44032030000a8508416144554510b5241d0b41113000401d4001150f012803014009803c01003140360040301e010742c43c1d1038149c075000703009409404580c2029038a05224041411070510541040f05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 258113525 1250 258112275 258112277
    0x16021203181519030b06040e0f0a1410090f060305012f120106050705070b031519080a0308040c05090a050a0c08070516030306121a0c0c0703110303090406060f 70
    0x8040076008400e1500c900421102c850b0300d000700f000301d06100c0e0081e003084041c90001800303549042c3c0c582c0b0b1b41c9258001d058440d2036050a03624200310746a1054400c8940002d02c80d040c0408901e000541b11003030350902d00411024544810103090100d800307400400166070b001d8001e0100c034100c980300307201c070036030081c403008000168030144035020b114030003152102205200070340413903800e00d80305403000d81c4042d000316500c3c850008001b0b510050140a180940000124550122030308000c000d1941d02e42c9081e9403d40011100070030401c10001030301d90030141d146c140042d40b41e4490504c14810312255201c50f0300300d50008100480700d116a40418402d4800d07040410217880d20420440c1c0940b000c4a5140c046102000901c41f01d015880c4076020480c40fa02e400310f03885032112500341c012090b0a0301191000c410400b041a20280022410740c828459a007035424011695a402d83c1c170341030b61102914030300104a030311409880900481e800140042c005001c0155250390007044000c0c1c010480c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 258114775 1250 258113525 258113539
    0x150304080a081302101b050609160512150402060c0d0810060f0926100e01060605031012030c0203010c09090c09030b0c030c130803040501031503081602120318 70
    0x1c1c66030303400c83d25191095600038100384031000c035401c01034501c000800801c801341414002c081e00029010000548034281b141d005c0c107400c039800700c0c900d890081190401841502d002d03c02140e220342c0012080d0254541d03015120081d100e9002040c103038807961013401c1103406646405140b041e000700b1550300581c1c02c0d03a140142540d803840101c036081c0c6240c4480000030b1031031a040203a0b401d0344100000200d2241c009060036901c804019242c06188030b8841c02c05070f00e40380346aa40c44001c1c4a0700c00103006505046141d840c0c04600780a00d2002070180094609010311071105051085511011850303014000700f0100740a00d10240c01000584203800e2164288810b44600611448140d42201e6102000684984400c505012180c02c01840c40c01c0d400d90070700110303078210310040030381000305191170241d5a0340b81010001010750b401007a4025424100345800c01c0040c4601040b12000b440b0710424001c00510303880001d4084807080100c1006120103e01001d100c400c0c504ca1030542e1384111500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 258116025 1250 258114775 258114781
    0xd0c1d0606030402130b0a05100c02040e0c03060a09030201110d0504020f100509010c020f060708070c0b031b0a181d090c030c1507020d0809040515060f09150304080a08 74
    0x31041d4070046a00a4004d84031020300c0c89a291140c01210005600500031018103456a0104403045030402540d800662485c45040035410075206416901c2c0e95080600610702c02c042c0860b503038503000381c000f840d520b950321210030a00d0320039442014030609598045a480310506155805404151000d03442152580142c40d001d281c030b00440c840b60b9185843e11360401d040b0600540703804d045da600c02d90b0440f100c100200b00503541c11005005061042240e01d48480c00b50070520540703480c54000508c1c200040060026036103800c2556a00803c10400c2c080d61100c0c1d0b010700302e0320075807141101603e07015004400b154403220303c1d140d881c1d8050744c04000c1c0384a070399800e107140e40c610300e01031580d4068014240000700c50504900c2e400441d5201c801440c03502640f40e0101d111900003020641e83c1e4440842c540c000ca2505000d81d6411100000d800c2c800482d004001400c1c51103421407141c41050b001501b1412910380c610401e00b810b010001781a22407900303003403104160740403041001c0050840400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 258117275 1250 258116025 258116029
    0xe01031103010c1b1a0a1b080415090302010f0e07090e010b13090f12180605030907090203060109080f07030c270b1c050d0f0309150203060d0c1d06 65
    0xb400700b540a15590b40ca008503400042c030280300741c1d4010554540b034440941601079203022120b240204646c42d000508003500f110f00e61170180c0c141000c2c00400402e4820320000c18051040000b4507c021030000450b42003900d403c0e4010f041c80c840a44080342406000001c0c1c000c0410360000321070382000d00b40700030311543c0c0a41d8200e441c0d11b0a040d41c4401020b4042d40e21604a43c0080402c52043d00c9003900c0f14890b8540707241e01c0e21118185000228400301d1951021b00f41901c450040c00541805421410030424164803081180540c64420fa404030000301607a1142d94407c0c0100078601c16100c4146200c3c80154071222180810b0b129603c0e80107001403010070780c4004001004c800301d207510343c480b040c80d50070000c0c284e0703055102d901814a81c0c43d49001440c100e503c044a5126000400740241000307005454882d84800140c01d0500d4100c02001140d480c0030f100c104a07592110041c0d9a03511000080d069001c03644025040a42c041c0000c40c55007844141c0100032569441c51003110b556002c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 258118525 1250 258117275 258117281
    0xc01030c02010e07140303071713060318032a0807050105010b0c100e0304030b0c03090708011a0f0312070305031803070c0302130e1605040e0606180c12010e0103110301 74
    0x4039142c3d2603030007210304000144030f41d04512081744005007564039005054803a101c0f550b0020304481d545103000565031850500c500b070000300501c19418103100b11442ca00c0c0a00745c4407081040a01031004200e050000e03100c060781162600c0040f102c0c00c6001d00c1d01800c1c1000c00d5044540c040754191710f040004120316950a09580050242030001d100403244241038002403c89000c400c030b124842031002100262201e6115442a800d4a440c152645020801189000440e40c0414007503407420283c4150381c0340302d2986030300c030702070941350907020300500c00100b0302c3e1419400d0072109401012400f1400c165101c0015406a0403180d401c80e00b041d404014152a4494038030002c1100d80d105c1c0d03082005040c80c9201000c10040d4a000003030040702d1340340303850130904001e0038190450702c104000d104501e400d22509804550940080c511460400040341800e4000845200e10f0384551001600c0f03003000c1802c941001032410b1908105580d20005038480c50400c0c041180e0000219a1110142c10144 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 258119775 1250 258118525 258118541
    0x305010915060f0509030307060c030b040504080d0c0e180105031b09040303050703090515070323010e040813030f03090608150603130b0f0411100804022209050c01030c0201 76
    0x503070340c1400203103070400a5620900c000c183c60301340642032001500030b50b0180301501100e0700484001c40c108120310401400c0fa40d5000c403041c0b04034500014040842c0701401603910f0307440741c01e6001412445014050f51103143c0740140b00c0d0b02c820305020081d8108400b140080c101d690540456401c1c3c0300c00f45102200840322009180c00c1040100083e01091186d000344c0e03000079560400080124044e2070745030038983c47c0c00800004074007240600c40300641c54070840040703da24502e00f030307041001c440411001e81d1041c4180300d8044821030109043c05095001c4440c0d4030203032140c400c89180c0d245883c4242d80c1c01c500c0c0c15400f00e52252400580c2502541c1003510031140381071505000e080c89010010740743c002030039010042c3c80c004040f80c0015161040300e8040c1d04d103038000b60f2061825113480d521034120742003010302512844089200c2950004407440d005627040754005680c542500c200590319a0000c04900c1213801c2208203020300401080e40f0508104c00c0c1d03000e0000c481d108005901b611844 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 258121025 1250 258119775 258119801
    0x22701050a0206070c14150108070602030a020a021017090601030c2403090312060f0e06030d0909050c0d090809030f030301050a0b09040204090c210b060d0513020a120303050109 78
    0x803400103803184c0d119508101c182445a10001c030841d41c202031481c0303070803486040c16101c0400100103000c448400c000000081c01148019494020901740081d1203403179904000b03004545d040801402c244c042c00701d0351100c00e01d1031410130007840c11000071070780d41a00388029103201541041c0400c0c000b588c0281c2d9810f880126200606c40414084100c0050801c00420340403c00b074101c1d43c5103410b940d806410000c011404444a0301401c1c80c508594205000d0302e4280311b0791140012800c95504104110200ea0b42c0b131000084032f07590041111054810186144081480c08180b5030400140c2c1e4003a00c50300105400302e440d80400742d8016a03483c40f00303000b29680128410800c000c0e6140c00401441128009013000d0305041d0303641300500c1511a01814040420120004450b017030141c8a81e01c40300d130120320f80a1140c1241440860407a1081450b4441d03c1a1207100145090f10540341000340d0079400743c2000803003035032a51552076182c0b020704200e00103810310000054508181c0250f051007261 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 258122275 1250 258121025 258121033
    0x3110402090a180b100c020102060907030f030813080d02030906070c0b160210090308013213180503130b3f01060c02040e0d0905060d020706022701050a02 68
    0x10482a11065206007011550b103e0322a0041c44045d151503202da591034500381c83da0301d1145501c0c0f001a04110340200046100d84c842d401c2013004c18441030822854540504201c42c0648a040d210054818661740107040420002082011340c800355009500c1034006005445107503c4103803048034039541e0f000c3c028290012150104111545440c4007888d004000d004640309060503019000036a01d0b10310094021442000c01001b140c030b0341d640c85001080c40d6044030300d070380b600b07568100070002400380f1050301520b511100c0010040b05540003160644602c1080c02c202c00e881d00d800c3c1d0341d9030300c803040c0022036a03d000000119229081c05070f1b02c0c0380000111040720002e40940c45000c80c814041403242480f0140d41600080700d13001402030107040a6951420580f002e4010310098803088070589107075501441e440700880b41d011007004142c507c102d03000c031b82e110206504500a03000310301000e03190380d10001e00d02441300143c0000034184070001450042842d100001501c150103031200d81030150304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 258123525 1250 258122275 258122279
    0x806031f02030a06030c090617060408072006031f092007060213090c1d090601111c020714040605100c0f0f0305130f211e0302030403110402090a 64
    0x1215000b4650026203103900084d00c0c0da40e074036805540a6154005040250b07241014031034a50503000b440443c0d03121500800e002d0815913100d030018401e1480142c03210b10f60043c0308060406c00c143e00407a0b140002d05840e1070b41801c0710602d6103000d030303005c412894035070f50103002a150035280910704440e1102081c914100240307901c040c2d0b07a548103120449026074200030341042d896250419202410032400f000139100c01c840809841400202c40d4003824411019415185503500e600d80d036400070703083c6404a100042c00c5040c0c1e203080c2070140a01d10022458800e0030342c180e8002454000c135408010140128445c4805110403181d0320b0050319001581d504d10050b24501500e00d021585101c1c4c00c4030390368602c450f12541e02048030840100c00160001403c248500740030310001c0064103060900840700b45c5081c0e04d191840b1415000045050400c4c2070361011302808008075002407035070403070100041005190081d1a6846804112800900f40000b800716080c0f91003503840c00c640c0a0400007400d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 258124775 1250 258123525 258123583
    0xd060209041107080a030b0a05090c160b070e030c0604030b0c0a020304050a14040b0a050a14060408070b040e0108070f120539030318010c170304080406080603 70
    0x2602200c0303041c0d042030311400008400e26a0000815080c0d01a01100b80c032600c10803401401c2e100100c05151148a00c00414081c03079940c01c0b01160801c91803a40207640324001540000404101c003000781071480700c40d0810041d9900010203030325429048081d01c000741c413039400b0003425004500024000c1ca0b00c0c5000100000038a5000b0903520700da50044909107503803480003030401c3c04103810403401c030306400e02042c10074242801290380840303044680ca98410304000100340d501c6c0d030500c503009010b5425012820107460b840f0807180074001c1c800030740340c0043d1106208103407176005200300c01c40c04101200029000c0b81c00304000701030fa05650490913190749002c0c680c114051500c10151681d0040c03c90f01490a1017901204040c400414040614015011311442100d0b042100e190700a41081000e107684a02c81080c0c1d0310006001d0824503405c10480c14407aa82c1101c0008415016500000b8881409541c201410440d00070380e0351802582da0707010502d138480c0e40d400308259066514410b454402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 258126025 1250 258124775 258124777
    0x11d03070605070903050106090f1a01230403060501290a0e091b0a080402030705100207091d0d1707030b01020d0c06020d0c1e05040b03190b18070306080c0d0602 71
    0x3c8441494445413140e203c2c1c9605084030510390102c48600d507116019035a10015004120410802220002d05160080000b0300036440507040d9940c88094440c0b405a00140081aa4051600044100460768540d904811108400c0d4401000744900000b004803c01b0345030101ca13280c040d2642c07000342901c034a0041c4045480043d010a141081da05100e0f00418200c03070240000c3c2d8501da540c2140703410180107141c00d101c41038200e240a028590200700c04170f500014110b040b241103c0300003a402c107101c0a401c0c1e410950024603281ca0060b130010818041d844050b59920106204244049032901743c8241c1c02c50b0f03050502940960410645035400c5401000d001140714060030300940781000d00340030201150503d20003500400c14100940720161140001c2640380711050901d1840e241c1000051016400003c00c0c82d0840078109042e0b0000360f60b260814481007402609580800d00300072450300090000301c5107040041c4c64820f0010303ca841c0080d0a16a1500c0501500403408841d190301c80a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 258127275 1250 258126025 258126031
    0x40201020c040911010f11070b09120706020d03060503030910050306040608070f0f090608031c1103010609090c020615101106100317040510050703020a0c0305060603011d03070605 79
    0x1940160340342848140c45a0143c0d100d200c2c0300361141c50f60607140300000350000c4e450302151750401003130300602107208400043c054151445000e0b50f0751210a00c8001426190311407500061034011180e00141240d000120f030719100f1342d00c4d2001d100e03003900d0381c0a059590045008095000c0c1002010f040707900d0107a0300864201c00007030408aa40ea0300c0760803942c5000c0899001203002c41815004000c01582d1a44a402401c0103820621013949040c0d031749a40c030300030101090780c221680701080c0a55180b90340607003414065904256102e40e52103a02602c52001482058921800c00035050420341c40031880d940701e2240c080c6803034645441142030001b034000f030030944020f100380254034140c914030422180e885042c1426441c40b13001d0071440c0410180e641c01000141004080c807083c400c40e940c034000349075076418074a082a1136078041d0408910300100f210f0003800250a2035008400d0000c080341c4280f06150541c000d010700c0184e44406000c084c604440090142c0082c0885000103106030801c0b50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 258128525 1250 258127275 258127277
    0xa1e020c0c0a4a04050d020c0103020c0705061606060f180c021002160501020304200306090303040f03050f07050d0e06040b0708070204020c0f01051b0a08071808030c061915030b040201 81
    0x20b200c248450f0204900c07402a50f042d5420342c014244602e0040d81007142030480042881c003581031074000e0301020b9441a81c3c0c01624070800020032451b418030508140c00a5690b0450400c0c440f840d50340000b02240740380740c0a8452101aa21404441100c1500599010113803650041000d104031100c100025001201b011415403000c80c2e01402085090000e0341c000c43c059105520030610b00c0d12030001c194085c240650190300050100800c2c2d076404010313294000e801c00042d83d100c0b81300c2d1070704450341d2199280104692001040b210140000044e6003214819503854120005c0d0000c010054180602e1244104000301000f0750070018440f00003078030745244094409820b100300f007503915060070aa06a06d0f8001d0795110b04101744c504038841c015004508540b1540d1500d0560700740100307400001000e5000307100700c00848010209000300c2e04401040114160f079210782000791900d4840400340d82d17400300045014040c0b0102030241c86004050340c04c2203000c0c039009146549203081c5000c0280140c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 258129775 1250 258128525 258128639
    0x1b031104110f070302060105120f06070503060a0e0708180318010e031204030f2906060307020a08030703061409060105041208040e0a0b040c0e090a1e020c0c0a 70
    0x240602d00028007901205200b034024008035070425041c402034800202d0701c0c0c003466006040640c1c040c0000301d4019004200e5140060317481d511440030401d800182d03400381d074003900d40008004442d94800e4841d40039030345c1c5000c0410054a80e0208546d03074010311494548103403210258940a44c0551011a43ca01e000380c1510300b0041c00490404043e00507600c180c901d54504410a000c010710318099501f040000c9000c030140184151a80c100840010952802403600001007094180200003000d0702e541e10160140d1b0324604810010041d2500c0d11800c4c0700c04681000410281c0b601c009014411481a07403401d0900749065003030f81460341c401b5020b6800444c2000081000c440d40018140f0034440e10b0343c00f10b64144a50213000c1110224002c900810440120542c40ea0b6240d034046908042e44407404212929280c2d0506900c40708112940140c0e84000703000d004602c4081911024844c0841d1021051940d84580034a030f0301c8003a0490080380c0c2e101a4101080c0700034002c0148609402c0404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 258131025 1250 258129775 258129787
    0x307050d0f1203020c1002041a0705030705010608011506140a0c170c01060f05030303040c0e061503150109050306041a0720060115091a030c0715091b03110411 70
    0x12082496402c804002a00003500b003041a004010b1002110112501117280c940391401c55188059110004801b0500001d561418080d042007610302042e00000200070250f52410224028a2120800580011310107000202070340181c2d08040c0b41c4000d550305070303e00050820116589401d80404582d00c100070f1a5a03400c45c00b03810b000d00f0b50286200c00000711142421182e110504207a40700314480d0b03004104000000d0130486420046030180040416140c40b40c01c0010361102400c3d0342a030714440d01100f0000b80019004450310030401c04c5e01d40200c2c0710385842c180f41c0c507040116006041d118039004000161a00c4010740d0380d107c601440d020400107040e245078004101e001c030315200680d00070760051055a040e0440e0580303c080c0ba06100050501e00f05244c459800b18900301003030b010000c00010094154482251508c9a000c15900801001604080b00410001d0000c0c0c1c2c0007040306048a00039040e0b03500c5482503a4001500c100760000b2201008040c002d028400c000c001c01c00d0203c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 258132275 1250 258131025 258131033
    0x8070302091003170d0501090b030a1122050f0105030106051f1b0501020307020129011101060e04121407020f04090c0906150311131a04031b090e0a020307050d0f 71
    0x700c00c29612503168076a280c0c020003e800641760184c0120641700c1c0740641e20151a0782c0082c42d104010f030b0111109040f0700d5080b0001e00c080c0c01c9080005100203440dc040c050103c140e51100d0b00c91040900108890307621002030500304e440720300503950000d881245071110740e140088201e01803600c43c50614a40c141c9a03968200e0034001c2c0d034045882d0ba40200c14803541ca0380a02803001d100c24080d81c0303000c100c407000344400010300894180505008061b61050610301c001c1d0044c1028080502f082c2c0c0305400c2518111000c41c105049110005185204681802410104441045400411140d01030380a80108001406a108221071520b0055800030b1001002c4c050b0000a0a1000f2651500d04501c8005815a610400c1003142e4820421065403600445d401150560304100c0c000807081c5503c0360000b00034402c5800c083c1c8003501e10415006010042c4140d030003918031700c1c40240402028040c81c0ba544a00100d4000d500d900706003020b10035410150824400f00e4000c1c03844004690301e54071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 258133525 1250 258132275 258132293
    0x80d0c080c03120a0b0405040c0510030209030d02070509071d040209030a0501090b01140d0503030406020f041206091104021305010813080d0e1c08070c020103090605240a08070302091003 82
    0x22404140c01d8100800001d80c44c184100c8880b2501618144058a00b0b5902d40006059901540d8480c15050391442d520380d01c40d0b030550703540344809000c42c2c8400155920203075551990b0300c05e0070720568980c8002400c0b684603103468021004110030700b40401c00108204000394000050441c1c1521030400400d0116109002d01d40c3c9080c010f130707000b03030300c030f50507c081d8148c0200110724003802250781c80c1c80c42c0d00143c40041141e03482900000010303100c3c032901001d101c9e28800c036070103183c0c541d100030406003d0246941c41110a0780c4103641002e03000c2004424801031303000e11200701c944a04030031070410165014041c85584005000005c065508007940c07503800c0d9410441d0751212044d40c03084045210801000300180000d881441d251a40c0008240144035140007800d0004202030050240304590081d0040302c20f00e81d0104003403140c0d103824200008800f07008180040301d4481410200e40d581070840c0f070300b03090703902c1a000f8100301810350f001c5c0500c1280c040c15204041421003c00008030311188 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 258134775 1250 258133525 258133537
    0x40b03010c090816030302030702120705030a0c090f050606070201080a021b0307020a050105030606031f170c041d07090902191508161d0a0b032a04080d0c080c03 71
    0x40c44880c50b031410044a00d18082d04d8116520105200800520100380c000090b00c55080c0e04560001c552081d0058040c281a5564040c03509841012080388c2000420030303034001501c1c07020701c04115651b00485001e0a44809403010394100c2c1e0100305d0000994811800650300401785c0300d01600e464010094002c0d02c1c494151440c010345c0001c0b421b40c0c11450414407400c018182480c1c03081c1182854800240248005005030007060f015007078000c146030301c07180e41e0801060704a40e10661901025000e44d100e1401490b0f80c0d10480c600030051a90314107001141108100f0b000c0108010780c18015400b0080000359801da0b4400b20f0041d941e035800d5002010b20019140701443c1c01000100050050080040500701101c001e81071102c0d50032702e592151240e08541180c888a45c4244501d1011403c0a100c40d0030600600f81c1c0002003115000564615200110754141a407100440700301903008180214020b404050304505501140241301c0d684d0107181078050009945000c0544d10308510b503038405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 258136025 1250 258134775 258134777
    0x3050a1707030e0c09060a150207030803040303020405091006020d0f020106150509090a09080904020d0e0109050105220803010b0307180807030312140a0e0304052e1706010c02040b03010c 82
    0x25001200240c005002c0c4c0421200c0965122245061000c002510054140504004070702e00000004495208018001c000c1d0780015000d070b41c030706060030010701030340c010700840707019010000200d421241c0144c010421280e00760302070f014046800b102100c0b021010f2440c40d0440d9240c0c00042100d40f018000e481005049403951943d82000509200e082a07000b007100e06e01c02d292461410201c0c8080003200d40e141c04c03c07032700140da900e01041204001c5c611008034946d650300c4d01201004100e81540304601039002605007100c0004560710000c206034486400509540c0c013403004200d075040003406950040d115080010182c80e01040c0d1100c0091150301c100183c0c1e1000d10200181900704155600c0307525903110030300c03003a2908040e414441c0000344c0404103269036001e51401e441d20a2042d41c0c0a0840144418117040700980c4030a03005c0c484858915000e00b030070b203030400701500400600641014141444403556111130065030301068045040e0f03086a10384005c91440c0c0e0713082c490000c1007059 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 258137275 1250 258136025 258136031
    0x30a1401080d020c0a180f021c0504140c1e01050403050a0510111612110a030201050f0601080405060114031005160e0109080a020411040f0303050a0e01080105010c03050a170703 78
    0x107002c0004d281181884115002d00302203c020b00031061104c0c130049401120314004560102c21000c400000c1c032951542c2c0d89014544910440040c519402c014011805801c0101103c0350020a248d210800c5182055004114120a001400c100303040c0721070703a4605060141c03c041e80da40368030341062007c44003159140c10000c06509030484078804c191120000b00581410f14440642c14000320032801c40240c55071030f9040108403010300c1500c0c0c0002001c0c0e5442a66a0502c0d0380c64017901900081d0f903c015042031840c0003400a51040c080c0601c03941d0841c0040c0403c3c1d190607170810303103030480c0c80505805010344d40c610f0322105400e010f85402441c1022004562207008000100081c2658608074100407030410100020f441c0000e035080c040d1f404403000141c42c694030940040c0c500c90f43c3c0c042d604074044072000000b859007050250182c1d142c0c6171110b210711440c1d0001110074040c01d028950108408040c01804030b07124001401e100e429506180f590441030503c07003400b11200702d5071100042c0d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 258138525 1250 258137275 258137293
    0xf08040f0e0103020a090f0f1503060f0b062a19051608071703040e091f0513030c030203160b060a0602120a2105041a010806041106030a140108 63
    0x9080040d1400510598414a045505650005110301c48520410039031350b8840d81c3e85500215660f21112404800030010412008801b0485501c10210300c0251221880c4c461007101c00409030241460519004080320301c1c140c0700c0700d48941c4c203807803600c01c1003d10704046801d4018940200842c1710f101c00180c003003070001450f5107082450310004203000700300301590000c1000702c09400a14401500d88a280f0041b2a02001c5482d601d180600c3d032000408808403c00c2c0407424202060b0304807011a44100036100081007168241954026a0031054800c18803495002107485040301c0440c040c402c0c0305403031806104600b018044039006805585c200030642c103000c401c1c6051102c8000404032400500301030b031461030000071035008204c07201003408140c200c0c4007003021091100b030390010702401c0204454101410321021941c14100800790f9258510300203e200302c40003446502c01c6602c440820560440030040c091a608042d115100780d54603042d0361500300c1507400201d03020b420808010302d9101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 258139775 1250 258138525 258138539
    0x30c0706050f060a1509032a030b0105100f020d030218040f0507030e0a03020705060a03110c030304170408190213062309070f0f05040b0f070308011a1e070f0804 71
    0x800135522505424401041d205443c0703402846800c101d9411820a20882040c010903101c9041003a90203c25040a80310101c20800f000c0c0102d41078032801e0701c2c83d0038111884c40040d200181402440b0026031300c40f040000c1072074481d4005001e03040e40224401000400c0d0740114041d140681e0340e40540d00d4480d000c10103050340c5441451407489900e0000d02001c0e803143c402a4440c603060044902804000450444440c000e0300808950b0400340941c42d40e441c8a0600c00d0b0702ea400c180c4044602101441e403095603051340c01c0c2607034203803039160002d0111801801805064501021012600240c8a200745010352403148038840050a20307103082a403010801c40c00401d0300e4900480c1070b115040800c10b000160313a1004800f24144506d0500c40f0407a600c4c1d000c10b4880d8002c55001012050001605c0004280500f008d0a8120701c2074451980d0360341c0307400d1040c0d0301150501904003800300900c03c0213415070842e80c0350240b0401c191421407a0040c141c517a41414a125807094503030240000f0100044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 258141025 1250 258139775 258139789
    0x80901030f0216030311031b030c0f0a0207080705011707030203060102150a06090b1c030807030e0d0c06050a05070219020105040306090b01080f07180f140412020c030a0c030305030c0706050f06 85
    0x259801d418624a18607001c41108c005460340e03c00000344a2003c000145044414011154040c0325200f070582c40b41d01c1c4910080d99440c141c020200e0034003e9400c001582e500518500e9003400c62041d0032403041e9900c410071402500018100f50440c0f0034059500281032440080b64003900400c10b012031400d0402c23442c00305507241404480c0c002d00c80740b40007200c0f901c06041c0d1002c4840e890b14109215465103801100078040c581e4451456000740382d0107840c03051b009032046c1d031014480e90042c030113940c035140c42508840040703842d6405038100d0b03059654001c030042d15040f4082d01c141802400c09403213440e08000c690383d0180444c0c0f9070766550014001d1800401100303071510020310041c0a1641001d80c24140a0404000085400e4996182075055450b81e0059100068000704490691405081041502c0e54130454a0058041c40e541c04100d0308000c114540303119041110200b980d440c6990445146e07000030301340070819106000d40c40c00601d0f640540e03801000c44005180c1c0c1420710070100014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 258142275 1250 258141025 258141041
    0x50c0a0b040b09040c11030414040c1d06090301020d0e01090515130609020411030a0902040507020f0a0b15270609240a05030a030c05010506030606010804080901030f02160303 77
    0x124000901c801c210000c001c0e411500d40ea90140d501060007950340c602079800c491110381c1d01406000216020903810308641c8a9448401c04442c02c0c041c0710a01d107003c2c2d41d1900314661813070310480442004c960508161000f8090000050001450f000c0320707010070302c11507003162659005a511100804140242084062801441c01e52170f52030b0b5080640d04c40150f10f400700740081400e9150300c5050159540c640c00a440100e40c400d10507506d10b0001c0b81c4100070881c845089100780d1a00002c9421030740300090313054640354507000800b848103440c2c460002c00032000340400c040c400050300a6001b500d8a01e04102c404076900b00b08041076103140c0f810031104400a04850141c072071b410812103801d409240d29003461440803c410120314256022440031100d0780c0029030140704840c0fa050415500c0b036480c2864034000e10013041240c441500f01030300d550782561540e000541150103d000301c5c2494004181180c0c0504001809a50440c02d1100342d03003101c81001103038005814a40c0c01e05400d4022501c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 258143525 1250 258142275 258142289
    0x60905011403010219080714030702031210050a030201081008120706051b03010512010e011d070803070b0f070207080604030f181a090a032102120a051603021603050c0a 74
    0x42040c0c1e1303117000511314169540311130003044444130106507924011071480c6400000d03240440d43d60b26180c01d001c1e41d264404c6491060006504002a115001c450004816900d004064441d0546507800456450f9009002d42002c040000c0c0c0010344404c0c02c00c201c1c1c803841e021626041e110300701c0e800c0201c12100c000f043c0300440c15422007022a00101003044a055a100712602191515003034a8280148840c02e03071150150300c1d02c0d00487c019181103940310003d1007603800b00c954154544c6e0700e140d164060b0f01002021103408001082e01141c00007520b940c00b0030706104440140365540b0905103050300581d026008200190701009882c0e50100303081c9201d050031b450100415141c2103000045002c41c10f00d01c510090041102038044d955413099800031034101081003000e07042c030305c03010701c44142840c0345001510410030b205444e804100160303440d084c06078031b899081c104881281c4203010741e21013088045002e21050003030700662000c1400b001e5402040201030900b009424096460b40301c0d00100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 258144775 1250 258143525 258143527
    0xf120a0903120e0a0210302d1d010920010e150d0b06040b0406080618010b0f0705010906060806010501050c06180705030d03050714030408030601030e100609050114030102 75
    0xc010000564100d0840d0705480000b80c410081e5000c0302d0064401140301c01c4010101d043d1f079004000408408003d0400f00800c00c2450071041100307040f1204203d500f0a0400c005034840392022040e40000d074042c2e0120189001100c07280c01e020308545076080300301d44030f0342c0d27851034039071800c01c00c080d520652442824175070850450750000034540c04082d80c0445030f140000400380c000740c02641001c002c03100040d1005840b5501e9004283d000c1c0c0042c0100c0300002c2446000420510f060314015043c152403225003082039080072502c1d0443e82c8045446500d4038801c210003030005509208180e00e003805500d00041c1681444620b50400030181e0165040100500840002d030002103803030303500481403150481d1612422030b2128100b0000d0391050398903001d148021241a5095080b84e0302c900c0159440385a0300034900340c101d6031400141e030081d101c0c2d01c0c24400a88135500075482100d0b15490441100d401d1502028690165417503608018500d0341c0322001000130301c0d0070749580400008210025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 258146025 1250 258144775 258144791
    0x105060904050c090414061807050f070201020102090d0f0b180c1306050a06020f0f03041401030e07030212010605030f060c0a0815062109150c0f120a090312 69
    0x25089016910115114555072004990320405080407605440700251017840b400d00104110b1481400c100d036514010300010b0342c2c0d11000c0303c0201804d07100e4109034561900740101c04131807107006e400041080381959800c01001c0b80740d40c0d4800010100318032600050284d42c0c8136213041d40c014030b0003500140c0105644c038102400ea01e8042080c040b03c05040d50b1441d18201c40306100409040c081e4400da4100604d0000132410a5012401c200462041da044070049426100d5090740d0348990720420303c0c510741480034410f0701c0d88650807200d0000a600c0454044940b01d8000880c514402e45040d049a955810204400e043c18040b00c0c48030800b5401030405413401150200c03143c800c5c14400401c01c020000011803102c0759600060380d641c0701825007030f1500c1460051005020200440444070180c1c0b0001400d40440001d10000703180c01d5140d003900390746411050003c0768000b0032400340008018400d0041e800100c5801c01e00c1070031043ea000c01d0b00421400d020b810905002400d0100a00300804 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 258147275 1250 258146025 258146029
    0x9230c0d0902040906060801050f070c15022101080d021506060304020d05030f07032c100509030109061a011404030b310609030f0201060807090f09050703080406090e0105 75
    0xa941880d50003a80100300300074940700050040101c50070042500d1720f410400f007200c80f03056100303a210341c0e12110001004c2e11130356000e880c8590070440c0100b001c4a84440b170000140590054240308000d07501400811506423044881044245c0115174141e106042451030701c2e604104c00e01c001e232030790003913090b0508258000c100c4034480200080c0c052006221001d0800000300220f42510080e407180940710403151030010407001401905072414540d000501d01d681c2101b406882c8100b9005084580040180d102a185c1c2c1d002000d803a9070555940302e402002c5901030042c1400000c0c040340d0b182c1b05140050014006c3c417110250500d80c0da80a10043c00001d41e91104150032048001820600d92104c1c40c544641c010704440c03112803a04546203503002c001051f0409090107101b0b1b10b0380038035140340f40c01c01c0b42242d601d031140c09480d44c031110080183c03084a41c4039000c0a20700c80c4020409403502d8a943e0725040701c0341d0044461410004003002266804441f04014014060044840c1c0d458a80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 258148525 1250 258147275 258147277
    0xa2403060b1e07050319080118020c0a0609031e0908060c0703020706030207080d021204020901140a06080612030715050a06030305030c091906170609070206070c080705010609230c 79
    0x1004207242c00514401407000070001c0e1040d00c2c07000039000300c00c18a06600207211010030721980840c4174000da00d900480129000b51801c5e05c00800091600c031006894070b01c084c125820064081c40b10000451060810324080b00480103030a4940708600e900d041ca51901d800e20051240070141420701810b00003a902288c03000440d0b1507441d015881d04150305000c3e038244118140384d109a48002004062010440142c51256000329a2034500da070740d88001e04058407500f5841513200030000d00500105004105e202c0c2c100c0006001495400340400c0c5003803031680200b40c00d549003040640f5000e4018a0ba00503181d0010040d001030003030601e107070b9016010b40400380c2044c6441030301190090281d2103421070415811100d0480c00c414942c0c1e500042c1900c000c40b2080d2415980d5000010b5180c100491524000c81c0260700030455035485400465151240e0101114540003c100040104409011b03d1018000030000040d03e9034640e0740140d42c5e2180b42c1034042400d0500d804004014107280 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 258149775 1250 258148525 258148567
    0x5040201080c030c0405060a0c0317100b070302030405041d0d09120b13020a09051609051e18011e051f030e0a020402120601170c04090b0a2403060b 65
    0x20015181e86940743e1307801542c000c41e0021600401c02146000d02958404801c43d400340c00b94541030f8114500042c04202c108003103948100c1031407110803c00c000b03e907902c0240342003402881541d0620340c41c8c40014064031019948a10340712030500c00410f1100040c015104684840c0c1462074101c0e00d880040e8111400b58080a003030041800006103440c00c0c00e45014240641c006d140710032864a40707041c071000700002d48103980002078a0b450014510f0242c0e5901050750801401c800c01e0031000b405150040007004980c07038010790103400c00d0070141824a8418043d0004d828200c0ea180c00030002d400302d2020345d07400103101e075110110071540c0030000c07440d08070228020702d40418204c12031007416192038040c1c1d01c000e420a1000814240b070070b1000d186e060150009070b0b42c038403000c0c4142d044501859006d40d8007010407101000104500d54441e0b025420300c01028140b0002c03d607694030300102c9550b21720380c010400441d01030600b651960600c03812010f00000f0280c541403c040c40d41d0072003049000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 258151025 1250 258149775 258149791
    0xc0c11010806210133050d060209090a020711010c0b0a050c04080d0e03062523040303020a020414090706080a0207081c0c05030c030c0706060b0f0c100504020108 71
    0x401d01042030ba480f80014424030342d0300001203030b24480500c00164000c00700b0301c0d400222100140c00c0742c081086102d2420010b0b04801c895480e03010708110810580e040003d200f00e0315942d00b00406121620388019452285205000c016180c1c2e02c079003060002e070301d10102c2480c10807806c0c41d86000000c910941d101c0c0c1010303041c0c1c1c001070349a6502104000620031600f250410340b0420003802d49240e4403000522200400707400f0703100d09858051052011540c819000f80c42d400854030a09200d61003800c02c05e1211400b8070742a030001404044a0700300764010707001a00103801c5007680d1019030600e8040ca520080440b80e2148291911481c0c0648810241c01100d080203400804141600c80d942c040e101c0b0250000e1400d5591000e078511a898410546125803229003040041070181c0e00440c2528460700c4001c2c2940d00d1581d8034052151a507000003001ca030060b80d1458040782444203540071f40002c4024420180c0c0e1600c24000947c507140d504a511601ca80c2804100b100603680400c245801030341e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 258152275 1250 258151025 258151037
    0x6030b0411040605060c01020c0f07050a150c150501060305070c020307150e03070f05031213060c05011e0507030b030307051507120c0e010816090b090d021c060c0c1101 74
    0x52070004000c0c02a551200341d1291000c0748084250070194010041c9605d200c0841f9210070803154495103170001d91068980c4004840010001c11a403640b900b05001124030300303a00c81c440955100480b001d08400704d072039001da4500041c0812501361080c01d41081190408160349103056000980d1190300e030042d510404105108003003c140111656001c0ca0710003030075510107a495060854003031007248182d40c0f09108440c200704803601c0002c00c903001d040041c600c12008904005003910410314003041200c15658174603008902c9002d1070b031181800042c40d100070455042c507802c0202541c203180c01e0b01784250001c200c0074000079000112030341c0c400310f0211800003a0b0341c0d91905031883c5402c241107400c128286a550403c6980c40314251300c2c107070403d03243c8460584403c00c8110580181c803110f1070100c0d03159401800003d140d0001b405602c2d0307008205410351265540403d08460b50141c4e41006000c8180c82c1c001048803d01a07900021542d14090000007202d850740b024800c3e0100a180c14006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 258153525 1250 258152275 258152303
    0x5010b031501180306050405060901050105090411040c0c0b070f020c03010b010905040f09080a0807020105160815040e01181a100b0903070905130b07030b01020a0201030e010219020a0b070306030b04 87
    0x1a0078120004c44e0441d004125901d45802c0a40d1900e03000c849410700c95107409c001064a00c5c0c800d0b016801641c100fa015410b00018509000040584041034000d000c404c1003c00005070081803000d100e4412035070741e95880d041811000e454203858507015407186c1d04203201000f0b283d9100100030203c91003141e002c40d2180320304c420301c001031001078030150084000040c0001581e0708048058060002540200420394500c80c54403203070040810040c0005140c40045a0001080c030344072203040000400024140c0c4c1501c01c454219a000c4071240c81d080d0707907009900103009490303000000112079600e9040d5185400a03100058003114040e0795101d00000c240600e10b51010002500078212a20301000300e03091480070484000b120250031521640040001340e00d66110303000351b03200200183c0042c10f81002540c01035018000c00c06640380c0340e40d0301703002c810b2004000c403208407002601a0050081e500c00d6041c81c5940b034800030040030174503003004030030000280c4454850380c5c4a41c000c804404844 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 258154775 1250 258153525 258153557
    0x60203060a050303040e090c060403080d2a030903020606041a09090307120e09060307030c0918050a0f0507090e120711031204050f0a152a0b0a05010b031501 69
    0x58010b9501848080750200e0b4000c0803421290040328403401310b40104031084200919482240002044000123000d24002046250043c1070803003030315050b102290b040351030300e141c04406107042100002c8e200c20050f001c3c0758041c01102c0d0008820390303086c0995451901007100b2103000f05203080c01581c8072030005401c44400d1042e141e0b8294008605070b0040c400080040960942540b02c030300c40c204007400710784d040c03130b001544000300e9610602207010b8070720704054400203140c1c01a4008070310051a0803003000071014030010405500c50500400c44498070f052041c42d0020b10340040c0c0100713240440a400c00000081d407003c0710040c41002941e107003c10b00d40b000000c1d0aa03050a600362007403501010150070498086c2003564410345042c03204801d1003040040d102c1c4548500b00744042c03031302c0655a003184990310051042007142620401e20020981c040f00c803070910401510f600300380c1003c1c040d441c03266004040c014074110380c0850039400c10407413100c0344160848005042c8208c40c04408006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 258156025 1250 258154775 258154789
    0xd03110307050d09060908010207050604110f0d140606060a020715140328020909010902030408040b070803060307061d010f02070906030f020a05190b07150f0b030f06060d06020306 79
    0x56400001e8411003e402c5801820030107240c0603480210f0008000802c4041052003611055600b00d40180780e261165201d80301c0350143d0343c441e59003000c030143c0150030b00d80300c002c00450a02d04c10481075070301c1d09078107034110300f02000941000c0c4a08010409240c245074002040c0c016182e4201ca104100c000c181c02c00d484c1d51a00010410366203201104020180c0d68480c1c5402100e002d071806070000000300c00e404c1d4120f22564240715030151112006019078501c030790155921502c0761003418601916015260079a4200550840b02c0040002c10490a4202030026100800c8141007149030200da040c0354460b0300ca044900c0d6410051106da640818610070003d10008180000c0c0030090f090712402c00741040c1c00300220a90040c0001d10380040c0d142451f140e03646090300500c141403841d509083c90444150300103081603469003840081040e44804d50b1284064418000c0c00003d8a026200b051500700850303510303070f82901e0300104100400c0d0349403144142c0d03186134811401603590756207000003801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 258157275 1250 258156025 258156037
    0x6060b0702060d0b0303070b0411100801081b0321030411091e06010c020909030703031406060415030f05070c020f0103091e02013e0d0518030a14030d06140d031103 72
    0x340144823020302c82071001e2299505007100090340d031900048040441038420342002c0c8160081680a0241152041c0c2184c0028042d680010255062100c3c03030003d116050b26405c80d880074a01e000014001004044400184950006d48000135103241408172001c0c425003880c0c429241108080c00203409038400e904680f0025402814600942451041207541c8d4000c001d003100420f18000c1d0035804c11003521400d03482400001d040c20300c0e050030492907039800d0020000303900525481e2211048a07400a00a50748140d0380790f035501951900320700401120501201616040c1480c04002c0e001091810261420202e2002c1039440445070794030049894a2412132403484000b190200c4090900b64000c00000c0c0303070310303641c10303460003000d41c54155864220700700402003c07460030046040766514456079800c4492004055860700d22164071248000c00000c0a4804030b40c000103501c109007910352040e080030380074064000c400d4140c3c0030301007030780740c1e41010000c0c0030700144050442d01c40c1c004101f04c441d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 258158525 1250 258157275 258157283
    0x20904020f040609240e040f080d020c06070905010302030f06041d0604060c08070801080703060504060209120c04050a11070213110a02010203150907172d0406060b0702060d0b030307 80
    0x1160fa07558882c00720007401d004c0c0c05e120100741c418072401040c0b40d01103905000e46521083da0720640d1642d41d107850107410000000c8a68002c14452a03c15070060b02c003810300070040340050a100d10b01542d0042220030560030180c103251040c41405074844481d1034459010030300307a80000e0702400000002000b0030094500c0d111510680c41084101320181c4c2004001000ba51504802a01c1e0b03a40192490507003401102060b41c01200f0030004a1540c0d008a0f401c24050003006140440140102e0068460105141d0040c0e105d041500d11505180c4141640003544e4881080780d00300c00c031100394a510407490042d10030031080c405441c0e100e00c0ca0388842c0702088c0c400386040d0f5a020100c00a4044d400c12034241d5124281d00c04020b4060401250261240d2816500d20b0006440c4c0b01c03520795480c0b03024009600805110080504810b03980c58141d1214402c0ca541c1005031515260030030644407203801514114400344101c00040c0c17120360541c0c9800703000700300c040368000ca81e00200f0314501030108054 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 258159775 1250 258158525 258158531
    0x70c0503090301020409090b0a050402060a0c080d050903070201021020090f04020703120c052b06050a1e05041a010c0302010207061b0f022d030c0706200c030a020904020f04 76
    0x6c00442507070001031a54400d80c5d007414666140a0311408480040390042c1d08400100329008410340719240b0300c40d42d0748c1b04803d50f46c180b402c0302c80280222003040724500c14a61000030944190760301085000700c18150410140403e042c508104403a040401e0000514000041b030080100d6a030b104810035010f030098411900c1e004982030060030640e920490f00740c0c01d85804c0e410034501e84508100c4d50460760403035044805900c401803445c41c1251201c141c541140d074076040415503070f6409104d400180104241d050015031410241800c000c9642e001c2846540382c441d40001014011032908004e0009013808000940c080c00c05901900c0b401c176004245519000003184841001040391902e82443c0c0d07980409560b241030103076606c81110341c12903c903400c1000c40c040f0b01340c40c80d045000f42541d454280d900b80240003049514040454000794080381c8801211140580c410b060749040f00d10080051191030222800700c3e440f4013400c400030740101c581d500001c3c155140d2031007140e04008050820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 258161025 1250 258159775 258159779
    0x1e0607080c0d0306030c14010503010303081e011e09140c1315020a0614130213061d010503120a090b1b031308100e15071b0b0f0c040303020303070c05030903010204 72
    0xc0c010001408100c48103601e006010855100741c7d040741d005035206071202442d607401c40c1c034183d5100238024004080038134503d00e104900c3d2146400c460080150103c103440a440713801400001c0d1156810a04c03a40b40340603072544400714440189074020951494150341c07860800101d416030421171b00709a041c0418484400105a400510b418480303006032810000b90132690008050040150b864000f5048074182120141c034000390642e09a80e13071040001400ca5888240409a241255207004100d02d40c000402c41070909021280326603048140c004c1c58803a2828029203421441d001705480b500011419041e0113010000c0e0b014000100d4007280e48548103090141f403041018050314126000d201905408541e00c2e000c0c0215244205010f889040111061102072a43c000c104108000044d03440c100004010000c4100080c0203142d403018600e03211003a84412540038064010380b030010401080441e501005982d0088040e1820500d000c5913410854510702904c0c0c1c0442d0305d94400100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 258162275 1250 258161025 258161027
    0x506031510090c0f020c01300905011406060706090309180903090608090a02010e030a020405011211010503220c0302040e1506041b0503100902040e0906061e0607080c0d 74
    0x7400084904201e4144000c42007032100320781c00c04000391404d02580c0010300f103a40941c0109081d00035800c140351610001d16522403040c044054048035060302607564940101030010a024504600700720900604190a041c0c012a0f41b80c403030444040c0040e030b0746e82c40010801d0301c186c0f0000020280000d0b42003220103407a901900404a080d0b04801007030010200080300e13400f5160403885480840702a0841c644a5001520400442d80c101c81e4140610300080c401a0785510070076000e07003083d021180c000c00ca90301d070500501c80e02903000781c1070003020310070491086010110300e000781c0414442021502c9152401e84044003068100940c441c0c28112201c030001000150b071680c0c210070074003106e2241c9408081c4000c950f0261300b1071444901e019005030885010340d001350b4200807280200f90000b6524461302c0c0072600b00340c00010b03600e40100c0500c81040410048039801000840b102c80c400c0d00c0c0c503424945100c6020051790f001d80000318601c1c00b4045414140e5002c0a180019980c5054a07180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 258163525 1250 258162275 258162301
    0x80106030b071d032d0d0320070807023f010c140a0806010c15020909070e1e030a020901080d08090f120d0204030f0609020a0503030703021005060315 66
    0x16042c00000c02000f2010807480540c042a05403100c054060079075001e0310004c1d4100d010743c140380340700080706040c010712146a080051164800140d41c0c00913807480810b42c51450b2410142a4451446080c4000000302e00c10004480e8a03d50448804a09000c0002d400d0803040030003950180c0d0b40a580203c03100083c075804803200052801d4000c000740848440f05071042407004659403240d0b4020700c000c5481c603002e10b640d00d80010050505082c0e01ca2540d5844165a491b001c14102168000c10301c0350450620030360b019005049800c059405c0546880802c0c25034005c08420340c014041105d4032505a1002d00c91000803a801400c580381c40d46e140c00245940c0c6260404020000d0803410015142c00c0c008141c021079404418090a0001555104940341d0f4100094000d0141d0b4200030000c0050b8101003090304451240d000403a60b00d103117004110007102c2a60289000e5002041a07400203076012a0300f01100c03e04031130025064035004040703403601c2c84015400300403910140a000851030004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 258164775 1250 258163525 258163531
    0x30c090803070b01030507060f17040c0503030f0c0c0a0311090703020f04030803061201020a0527130c031104063c08040512090a060c0f0c120c05090105010e060c0106080106030b 78
    0x110407100c000f03654040c01c031501c8001409e0b60b0b0008002d031036041a80406480465001030051081c0302d111a00c90b40040d08683c40744aa028003078500264a1210074000e000700c0c00560f4003140c541c54420324540301c030402942102c050300e104030324400020341c4860096055486021039841c90759103c9440380303042203180c8d105503103041c0301d05000085c83d01454414022140980a01e555450510811640341c88107080706452011251450b0030050384107440b1508458001c070700f070071004200604104005400c607510400c040111420400c41800044c3c0c2040800c12481700105110b020440d003506000e503040c51582c0411401c40010300c1e41101c155215504501a41c0664203403200070b00270b80848030391031280c00f6086420840c042803c1103d6130040030000e6050303000700300c0340c14400141d903110202071005410201d403000c04040c00c0c0e020702800707041842c06441c0030303961b00341d50354148400030b0081d810010a182c440c007400600465140c1702904008020b2072031600a000944e00d070f1629041191040b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 258166025 1250 258164775 258164783
    0xe010306080105060604030b190c0c03030510081b040906020a090303090b1213030e040c0216080604050c04020c0a0c1d150d03110a0c08030c06071103040501030c090803070b0103 78
    0x1040105200300184140f50058000401c050329251940d618217812207002800e400c1c80a81c0c550344451400242c0c010315135804481d81d00c0920343c401500e809422544040d0107500c119400c41400c1c40200d07400903140440381d84850a002c448402000020701400302c01000500160002c102608035540080e006001e0301d21981310010301d2512044110424003400e1401c04220b0200800b060032087c0540c0c40052840c000d00d0b005005000f218085402c5d02c031300304601c0b00140d109440c40710210840f01000d5001e0103031000500803a08054581035030366004c040880d0301c59a800138546048003030030000000703865800140c038003540d641e0380207040311020041c03800030203407440c100010030445101d0380014042e00e00800c151006521614100c0d10110200125101c9200301581c04001c07a96020088004001040065640c1c0b01c0340a00342d0b080c50720141204050113410260b10403400404810b8505640b028680024000609241260685075950182001c1d003c0000d1190a01065654460507203001e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 258167275 1250 258166025 258166031
    0x60c0203252711070f020108060109170c0111151b1903020316091d0a180804050f010206010e19062312030307092607060815040c051c0e0601060e0103 66
    0x2143c1c10904610503940024841100f0034118401980550381b00740d0000301c10315209a076607031600e0381d8030b0400040903452804c0760711100b1030410320b40c0d000641c4000100c481c005060451991402103109050160425042c90504031030324040495800907507a01c00307101070181d680000c00741e402a00030760040c1d03691200c5203c1400c002080d42c1c001c00c2c035401211445210484804921404144039180141c06100707040d403145003a6880e44200031492075072038056075900e0341e5940741004202d100509102d805042d074004000410010b1010f240700b61707000d030394072103182144d0840c22403440003400160480c8140c0103442e0a00c240c051030400f9903c507201425102030401541c0d03044444c0d580e0004035410f00c00200381103070501c48525a040c0300d041c20161802c0f403d80401184074000c1c00d02d903582d008000042e41282c10050217088140b6a004000c0301a54200007500903030078014198841d140149003e00c170f410360402110111680700c1c2116550130400e403141540c48080051181401240d41400642 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 258168525 1250 258167275 258167291
    0xc0302010605100f08090a2306060405041a0411030d081509010e0a0c0507020d030f1b0c030818040507050904140c0921030d020304020a060c02032527 66
    0xe01c4424500c8464190300d030209248904c0404646481c001800780300240501e003420703c0014900c0b2250360310034a010743e000385410300e840d1b4910314007140106624072483c100030500c0041100030a1030020075a6001c4284001d540d5410400c03142003920501075010f1145980f00c1c2c0c0902c0c0e101c54840d0081c0e101e91851804c02da113072020414003d1080c05a4800b000c1070f03101144000c081c030f43c080b002c01c507224245241000100d40004a803080302c2007040c1c020070505500240e5003540701d04a4070100c440e0000010031a100d40e180c0e00304001890000078070710080010351250035002034070341c5001414024400d01040c80c1c030210040c21f82d00140011400386051085e651b01044040c0c0c40725110703440c0940454142114102040b000800075005414002e4103000140b900740700c14402040f502084807c09652400c151041c045501115032100040210802c0b1520050ba408900c020b4202d03891004404607002c1c5214070075603403800d903021589144000b55a1540107800300040700341c04e0540001080018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 258169775 1250 258168525 258168529
    0x1e0c0509040b0f10030803010b0301090e19030e010338010f2f030a020f1902060a0e0301110c0a060b0a0602060a050411040608030702030c0102190809040f0c0c0302010605 75
    0x1080035a00280801e4810b00001d141011288450760711804104140001940c0c9803111500e5500a030060f49020701d0001c0184010016806480e408100c154000c151140398000840c0082851640041c200314030034070f0b0901107038402c1d00010a80300002e4000f40300c611082c990071030516040e903030b03030880010b40e00c811910a40c0210280d003010807250f00d9a5000c145400801200d007070f0300701594214003906c08203d0341c00340410409001551aa500201501202c081036640f52a0b81000d2031b21006240e21117800042e10360380c040d610000420b0410910381d07010700f00002e000d0103d88105d440d0702c40c00498500450500061100b034158050f03d002c0103000c0042060041d4282680100800b60703106102240788600309620207680b00780240c2c1c0e0f5109141c92400050180c0e00e480d40116015400440e0000a62500388a210782c0c14000740010814010001c0e088a9218a8000050104070700811003200d42e03162038200303980f956000b590410101106241c060017101e0420b03010b4005600c1d150002c5041c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 258171025 1250 258169775 258169789
    0x907090218061b06090f0f03071104020901020a0605090106050f030c0f0d0f0204051e0a1505010c0f170717090303030c07062a02010c02010b1509030304031e0c05 71
    0x42516a458409140d070701406201d0030b6402034401412544414600c00f508040510086000341410806480c0810041d001c40e880e24444c28902c3c28507400811518002481304002d0385905942518056107503049040140d040003058000507041a00302801c00c00a04011761010041d90001c403082d01501c201c1400340740d035980c8030400309034100c0d0603980240100d05e0992420100d251140c6543e140780c0c04942e0218041c0d0744241d4000380810615035502d240c039240d9281c140d82c80310440404100784031740d4028044540300c25104440c1801241d081d03003420f02100180200700150404088107406c030100140c8511503110301401d5400300010200312454414000445568201c014011411500c5048000c04107030b0014074101c402c90f42c0e404008512904401e4400ba035480b039869039841540b11720902a007506c5c4202213450071640740c02d071622210b58900e107104068080c0101541d440d46606000b09145109070380014283d21402c00d566804907005030380001742d46218400c0c4003401c940c0d9509001d40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 258172275 1250 258171025 258171037
    0x105100e060909041e030915021c0509060f03130311160e1009090302060402040f090203031611030f0c03190b0f0709050d0f0512090603010306051f08010509070902 72
    0x1c07165080090b0015442d001080c07036001409150028405055200c82c00c156103001002100403c01040003000500384002e0300c0c4403280c18500250088501000d2071301c400910b5010314205111001c42d05500d5611820155a10211400c2030240d507410300c045008103900e4020313012000150001000329031a0008212156007400302445603010310b043c070802c00301100e001080380c52100d1603001d0000e1050000c6c0250309a1038061b8014012605060042c44151a85c440f40e808405007816161001610000129160101c02c844904070500d014601111805089081d0aa2522032001015081d40020602e41351a610840031221400c0c204926400414140d401c054029544100060108164429265400441e07468001c550030b840340c00080006048040075151010010003600c1040010840411982c1c1d413107844500300000c40c000a4282e110500005045c5a116404180100c145160030710100040b945003442441d00e07030014a00034030707048811300d80c140329860000034036031231520032039070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 258173525 1250 258172275 258172279
    0x30c03011401151404060e0405090f12030a060801090b09010c09061b0c1e030605010806040f0f0512040608040615060e06090f0d080918090705150d140105100e 70
    0x405030318101201d03035510f80411034001031082ca04c000001d5290745100a002401b1541c59400c0c00900c200c050104941e0300600c440850741c04008542c203d001c0000d100080d80d10303d0036070f880c3e8136a06d00c00140081c000c80c0d440392055600742a4504104036002c02c0c803511410519000f0003000c1d0440604a032031034560312840c004507100015103200116024650b1040c44e020305c02d00c400c103642e40da0800d00548100740e0030302003028041d40e007802040090b00501c1d0042c58400002d00c61030806485001811445440081000310102044000c11009114603500542003102003030319182e071101d02804044084500b110f01504c1c00107811a10089a507214084e00c02c9582c074070402c4205c1070b061110542c030020002c0da01150041e0214185e55071080d0315100c0d40c2c41511140c0d240c18088092100d4103e00703e080c0000100d03482c00308280150009161801c0f594103d03007400540f605030381c8600041c850580d03001c0c807640c1031110701d114040050035140d049a40c19144200d8038005c2c000202c80204101403102e03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 258174775 1250 258173525 258173561
    0xa0606090506031e070801080f0c1c050a080a0e010e0418150e0a110f06030106120f09080a08040b060a080303041709120a0204051b0307120f0911030c0301 68
    0x100075410118059544001c520312450502840c8494001032080704030381d0780c0006088a8018000d03240144845004800c092009107602d01e841e0000400c0f08010710031440201d40038007140300500c60204440e0764516000410745a07079200040006110000c10741b40680850710200380100d031401d0900c80e0b040c800489404080d1246007039503c010080407285560054261204500404000180002c404c80b9105841100320411030005008042002c0421144980824801080595008960002c0005401100140038180607100e0300040010400c06031900300086520002242c11805e031034095070090003007050a035a4001008038441c00ca0150168a0b003050001c03070006102099040a000d80d034029803400c1c60448008178005404004007910303d0341c8603a4400707080d42018800c86810214070180e07085d944164242c3d002c100d10020b0441010400030022042c100442540900c89140704254103202144090901c0444240303e800118420701404c515801d103890144a05030750204000e0410b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 258176025 1250 258174775 258174779
    0x1404030b0a05040302030c070f081203070503130c260106080c010c020f031c0810060206070e0607020d2028050d0807020301060b12090705011b020120030a080a060609 73
    0xa0090b2034050022010f41c0b2041c803881c0b080c0901400701201604105020310456854402c8281c5402d06480e005400d41008000f1721281561110440c0e900419510003206250712038500040881244e82c03000c450070360380801405a001c5140b14030000c2c004040e00900c0090348405040d611407106401c06401b1a8120280c00c1c010b04110382e000c0f49810b0018151061b140d1814011030039498040c062400046070703441040400c007007926401c001f80100e840149424a00703035101401494501c03040310b215401c0401c00303008540c0d60030940c08810358840000306490a18801d4503440304003220f0918410690030580000144442c00850104480d1220f03010109103090180052264104000c1d207942e5410030100340941c07000d0144500411100300c109070b94100050304031984420207000490250000c10003044a83e070300141c888420441c8000144046200d4030041e02c1204140c040260f82d030b680c0f4502c0101200303020020341002500c80c6c8034901240d4440c40d41c4000c8811300d0040c50b002c640d0180702 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 258177275 1250 258176025 258176041
    0x1603051b061b070807091b0f081b0c07090c030c050f0304111c03081b031e070210180201080c070c03030c1401051513060e01050d1704080601061404030b 67
    0x2c102c441c85808001c2e0341105440e48246420105136402a220045e155044004001507411424a00c1e041c240360502501c01f8200000380001005000503082d0400503085100c1e90f020401151030b032442c00b10440301d4503550b80c4200d81c046d102a041d41000320345000301100314140202308450244100600031451981d03540d603104c48641c42c90440c250840c0140f01a110200415111490302031b000e5140d070b080c203181210b0b4480720b03a016043d010a40800500030311000004805014800d94040400340d000c1782c1c0c411504926001d036030045180c1c44c5080c0181d52015414072030683ca0494001e0380c4004060741c0b000700301810b91185040042c03000c028010304001003485215034544103889240140c10315a040c0c840707503088d0313201520100c225042a0000014030301c1c0c40b46010325031540c001c10511082c0e192145241d120b1034148900f501035140d69484c1c004201c1800e60003513225154440c001d031200e44481e40c07203640d090240110404100400600c014501c800d400340c07011280d0001c1c014034a0355032403103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 258178525 1250 258177275 258177307
    0x506062d190b04090b09070c0206090d03030e07030309150f050d0207050304121109010806060612090304030b0c0301090e0c0f011b020a090903081e0601080403020304081603051b06 79
    0xc00e10045507101000c910700600c000100020702c606400401c9000701e00341001190000900540c040c0108120101c00684844080c0d0305001e02c00c03900950703900c0c2c1c0d40c10203070301912595400c5102802003907804810160051043d03008d6070845604034007404c012841c151401010070710103001258044c0444200700c4110340003488002e110710140c0c0d0415a944031140132007541c0640032642d018070040402039509040d40c3d014010041c010041c0f0301400d02c100450301c107120315442c2d10700340421140082c0c03400208000329001150302c4032141145242c0040080c2c6d00350000e000d04006181800118402c1c80c60014030280355075401411000034401620041d0790b083c80c19000d030180c4a0454010b00007680d506500d80c0000d24210310003040b80c010030f140c003c150130b000402d06003104560780705824501c5401d0510035803107003081c200700c07155484900f004d900c1c600440d840300400d40305241c21442c038081e07405490b8048a02c10310498180404148441e8600003011020642080c014480030b0281d6200711 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 258179775 1250 258178525 258178549
    0x603080714120708120907060518061e12071707120906060602010b030d0c150209060c0105132102060a0f0e06040f1a07080105060f090301090506062d 66
    0x40031640e0b12100400064403903000041c040d0381c886404503401d001404662032003940045542c001c0c0c01c0560400300082c00b9402a00d0b0700003515510024041c1d00d41c1c1701c0701c08603610b100c045004500014284100c99a580d40f005183c03003992001170000c030f040b881c0503040180c0350803401c28078083c0d940c0e40c0001c11603420041a00c01d52010f0744980d0050049a042c0c4282400b504099001091111540c2c06142c40c0c514542044000c00c001140014045552941c4540c0088002c0b14056521184000010401d000304100d04805500c0d0a0502c05e40c0b60b00d40f2880c240b12807140c0e0505445080200d0031072211182800c102c80036800120000e00c2da000e199110386100442200001041d41c2417001701882c003001180d08548440d85a410a0140582d030f00c0c02401e52038106200b140c40307180c10f401c010084013040c0f140c14003520011840801c200300d10010f07a00100b0019000b0400d4035401c0c10f00c0383e0b41f95400da88441c09003824044070010020144221000030400d815072030060440c80e17003403040808a00d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 258181025 1250 258179775 258179813
    0x70f0306120b01080c0a0305030403080a050906030901020405010207090e0607030518032715040311060403120507021003023124020f03030f0601050309010908030a0c0801080106030807 81
    0x3040080388900035540403081c80750091020380659810320081a14184080400c50702c1940d81c0001000000d00002c22201607a80c454183ea0301c42100b2a02559a4000c1c150f482e907000b45c0200802c00e8010055010700120382090342102c070f0700342d6100c082004689001d20258900d410500000303441c50700035000141c005481070344110030140c0841800d400e40c0c2080c40240042c03900c48405140c3c5e081801800524000300311440d0b684100c0b002c03400e031402c0c0f0039844001c0100203460b400c0c1040e6aa0300090707900440e00101c5001e0149402000103102da400312800f24030440c0e1004071042028801c0c800e54003520303000810041c22130b194801c440b43c82c2c40040b0404a0390080b040c40452800c0b05080e018042040f89107600d001c040000d40c02a0030b0090000000c8100d81c401d004205006045502c441e811a200703080459607912585540b602411159038081d00e030756800410301c0510441e40e400f03000b10391106e695221650b600ca010841c00c3c0d43c0c8078032016002c81c1d07080c071060300440c1028043c50041004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 258182275 1250 258181025 258181031
    0x1020c160906060905040b0f1905180c031f05061206010201150b09060723010b03070e0702060f0c0702220f02040b0a0806010504090501080601031202030306010c1211061003060b01020f06070f03 85
    0x2304e80002400d404280d0f80c80303401c04130301c18420011410400680e14010960080e490200e03d002403208140340801068804c0011030a11403a55480c15041801d0160102034134050b40e9441240100c0703071400701560107138010f601c0e180c07100c00d01c020107503074900680b0000702c0c1d07071840c1ca01075004004090700900c109403008086e42d40ca0240b9050512000c0e1542d10020002064141c144010123040965683c4461111200402001f04095002c140380740d0090035038141c0005500c804000c42c0d12402000c070001d401603030000603010201e03801032440c001800e00140c10b0140a410b40c20708000ea003d00d20a52201d05030a105418010303010791401540410103140050030076903035405010542d5000e901c0340d0225080705005006000e100c4c6d04080c880940d81c0010361070b600304040024008900510046c09111445000c501440c0c82010b40d400030780545000c50300c0d2420800c4100c54441014801140d6081c07601c9444904d6500100f00c0405425200700502801da4480c2401c6d42c030211441e00040405507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 258183525 1250 258182275 258182299
    0x1005040b040213080706030b09040b0417040302030102121f3c0b0a030c050c1e2a04060602190308060301090b07030c020c0109050a0303050f040801020c160906060905040b 75
    0xc030000030f10009221200052094a150100240c202c1e038540b0002ca004400710810400440e03c0060398582040d48180d004449101c8480c03d08083c0c0a1074000030f51650002844555502d042c0c0801801440d100340380d5440085050390785d850100b0359114410b240d803071070b60510200c18501171440c85440140d405c900840048080f43c0818500c454000d406002404103079064a0303a41407080c003148070b144d0300b000b910301505500b45540d90f0394a1410350a409064940489506506020481000c001c0f0032030402c800d0b609030003008109800048250003240b6245c4006a69403000500105100a803101218078500d00d49080300c00f10b20090043d034066480325611700c00150510141c0344274159030703580045d43e4542c00400a0402090107035803410001c1c0203a080c002c6a079480c1d05d800480e07916080155541c00510002461401264401021540301040100c4400e2010a05e008028032881c00c80c00855160007030441124101d0013580002402c14070180001e06055100c040b208400900141000d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 258184775 1250 258183525 258183547
    0xe0108091e0109060e03030106020c0f06071202250501082a030717040f030e030d021b03011b020c1302180d020f030d050c010b03011b0f110303010602150c031005040b0402 75
    0xf150400241c03170660000004100c1c0c1795048c0321000030603801300ca400d1486c4640700300255880c0544000504680e1000023180013043c0208a44174581f50007105005141c80001c5000c0c092084900ca49800309940400050404501f202004507402c0ca50403050b0307002e410f2031113503001900020310b00400d0000005000d180c03c1042500303540310b5032040a0b1066407c1452600a0400e821804410300942c00b80307030841441c03900810700032100040740b04807500d00131760350700002d000d044c4400c4140c00440580e280481c070345902050040000b0403c1d10341c0c0c2c91003034810401100724415082c00407140c0380046020702441c60440b00700700c0360794001030000d5001010480020300b885565070072203010440001d080700403004d017801449910b9204038001c00402e030512450701440405035103050304000070208030080392405000c0c9903811102d01c00072252a5a12602c01035540e002c00c14442c28070907100030001d081d00c2085001c4074403c1002c444880886803604007032001034801201d01545c06502801082021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 258186025 1250 258184775 258184781
    0x40e04050303010923010e0a020d020d02040510080103120e010c060f1506020109050303150d0c08010b03070906080c09090304050d21020a020d290405010c0e0108091e010906 76
    0x214000e00141d95254500500c3d0703070485070707026850610f003c1801c0305000a608280c1e00703503044079800c0120304000c0d602c4020490081c800c00b0f4119540c50310110302c640b10100b02d03074050001d4842c107a91240c18000011010b80c0d80003005d10005007010b2499000c00c16880c803403540c4e0701b10404103042070f040e510b500d40d4602040d0388004c3e04210f0340650f200e20004516041c620344000034801030008001d0a14035440700c0b038692000410307403082c02c0b00d00410b81103180c8030078120503c0e094200811103001da4a031895640a481802c402512a00c214240410440c2843c401c000c2200c05841c01040e0817081c42d4140500390030020a64895400284000a4161124998100c40c14850100240c0800c203039a0152402c04440601d1310856000c5e90040006858000c181c0c4101d0342c1040407010a141420f081311f080d4220900d403108030a419009001c1040015000402c0c0c0e49265150003400100910044424403411520f00e00c1c0c941c890210700c0c0903a10f8800d0010f1003201103100110310400191250000d07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 258187275 1250 258186025 258186031
    0xf06030318060503090d03050606121306060b040b03011e050a080a0212061b070f020a0306021b060f070c1a181603081902100e160812030106080705040e 67
    0x1280c4807600d6100604450032551010744a28280780c0c1c00c3d400c1408401c3e90384c0c0c4158028005040c0c1c0c480200305d859940303100380d82c1101e1001071100d049150283c0c83c200fa5845000d412180c803402d113840805c11200072001d1b039007594455500d49085030b1906440050000e40381c00034100c403011101d070201c0d60b81c0303c044640014120440051801c0406481444098040034000241d560084418004480c0d208be403070200b06511003140585443c110305082c2040e07051020000d50104206d80700100300034060300904582401c000810225844041001d41c0f01c02003190b01c0300300c0310a000d0015210718044d061000c40607000c0c10340342001901c0070b050415441070a40d0010034124a441e034003042201c0c1001501c04215032414100005455640c4a01142c018804c00511843c8c01a08811103144208282c0d10250080c910900411101c040d0030740d02c0390503130860f061410901d000302285c684e00028150500700c0003080c0c0c5600d103a2900e0301c100e80c9100094180010003808010002e01c0360410061180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 258188525 1250 258187275 258187277
    0xe0705010f030509191a010608040c05010e030c040f09020d05100b12060106030515060d090b0c090109030b150315010801050f070c14010608120304060605150409090201030f060303 79
    0x51028200000035059000d41e841007800c040c100810000e400320085a0010003d422040c1d81403081c0c00d514110002ca55820710a058400c1d1080c00001c05a84c081c203462300903802018140b070031944402c01140c4035061010a21303010f6000d41195222402c150381329070742889881c0070016004a2176800190000e00c90501a94281d10030740c00703100002c4072840380014040c4c0c101c403c1581c0000f4580b005403034107070510582050542e2100000c481c1410301d4400c10072060300809442d0317503200110307816004004080050303914664220000b40050761201c116107a451058650101107451a603a10701d21010043c801804801d4248540d9070ba03480c2000f81900c550243d00880c3d19a6040101c11403c48100510480c91480c0403400d10000e103030010b0003d00703003030341202281c0c03552064a8006405016994084103261103011a000d0089132600d002d0341c011171240c10113100b035540d0381041040785060804a1114020704000412402100d40c1c01401c4c540c3c810704000c28502c05d1070001c04221a1180e00940c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 258189775 1250 258188525 258188533
    0x11160b0304020a050a12060509070905040b0a0c180b090303090307030b09100209011e02010b030f010f050c070314160803100303030e1f110c0f0f1c0c020907030f0e 72
    0x452070b016110102600c41505c1da2080185400200c400180300c14001038026961900410404102440f41c50007510788800309104c1da06040c900074100300d074202c1d0b0407c1c2040c6840c1c0c2d18485e142c4540c0d1041d800180c10003410b5001804c141c208501c0303612000c5d103150700d13200800c0703110400c1e1800c0c0301d13040040d405803100032032516214140074101003962056030082441045219034980c0c00004030302c1031000300c43c2410380c40c2c0e80b001e0b000c1e40102101030341d05a0522071002c840c00b40380c0054005184c1c1c001c030001c081c8503545640c1c10030101c0313000c1e111000300400c4103c2244a05601e5000c017401140d070405512901083e071589a44141d0350055501c0e02c09100c0612061003850307010b0042010340030150b0003d140c545100b650004061581103240c0002d03030f0b110b08000c072080c1e00706401d80f22000c00340380c152018500b0404445513101900c0501c01c03141d01642501002054258082d5450001281c6a60380b40300016400c00140d0480105504185591036a4268918065100b5502110300000c010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 258191025 1250 258189775 258189781
    0xf1009030b0f06030714101d040e01020306040b0d110105030403200c0906030d0801030605181b0405090304030503030703110d0e01060303180b0f030408070209040303050114060f0a11160b03 83
    0x41401d0400b686c00415100d00c0d019004000b94035100c0c0310261a43d894580f40c0ea510100c2c950b090300c0640300f43c1030164803600301004000c1030350041d0300a6014440441c1d08110865446060201000d51100064800c2d101035600802c0341d4000c4009588c4948289010002c800c82030100c41407040c0412800b04455020320410261070516a40140c0c000d40101c00400c100000d0200041800905000082c03a90b919000412039065101c40302400345c030011004d982c01d0780b510342e0103112181d800107036461003141080702040700c41c2c0002c0b04450550f6000006140f0b1603882c4d01050b406498190740218402d8401c108211000d0f01c28852202000d0b41c1d4400401c25034510300f0014450f411881c030f600304071440e4940810424580300308032110854610001034682e521030418454038041c0001c080d401800f00d20030041010b81c95071007181614082e03407580b101b20749560140002806a51200f080b8031000300401c00081d030080454290000c0800700700c410088516900c040500300b20b07840b04458150110034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 258192275 1250 258191025 258191029
    0x306030b04030f021029150d140112050a20060d02070501110a05040e09150903070c0902070f060e12041502010e010c020706081302030a1110020a020f1009030b0f06 72
    0x5c1e0340c084024540050000f4035009007807120741c100c0e44a004459552202c0403038000d8890038210403202a0722218a030301c401198040f1005080024883ca1640c1032401c004543d0304490020310b28140d821000900c1e00544641c0c600f0561803510f10032000501500c9600c2d45103540315001080c2922864070050780310140742c50943e00792500e0b5031204c01c60040600645901981c00800c2d40d040320041028a581340d01c030040e440f41403119070341038042550601020040790220000082c1807091017507100380105a0b40b442e00504900508500410800408041c8004204a0f0300142100c607900c074103a0b595001c1c84044042590f02a40c4003116550f80120403031400d540a2080140310740b02c1034001e00075841c43c0d0400035107840543c000d542c00c1c8451000421621821040c032440e1190f400750850340400880e00b44500190740000105100f15416019005201c1c40030810601150740540072182c150780000411090041e0400c05204000307003010700101080000c0003041c043c01201d100c80d0301609154003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 258193525 1250 258192275 258192283
    0x6090c120b13030203191116150309080d020903031209010b0f090c0a0f0903050102070510061415161a10060f090e040606080331050a150306030b04030f02 68
    0xc00c1c110b18410445000120350044100c40a0996011800300c1005248409071034035800281111058441d416826484030b042c02000006d450a03140104105189014110150750700541c00401200040c44501114100ea402030b10703c150700241540d0800e003040505030b04107202143c11559a03919500d8062440c20600008004e081003a50b4003251464400c1041003540f14031200b0808009000740b43c0010240300d16000400f460384180203643d14050350900b41d548030040a111184146400c0b00041c200384030001071194514050100c8107a04003500d11458150840e10926560040800c8200c000456001006020001c0c61402b08060b0500c0d00c010b601c4e8040d940c020009020107031030103800715038012800d5401c0307421420240520342e0341d0303140001c05400340b03a021204a1001143e0903010201e40d040c02601d0408800000700d2840382148032900c41c00562040981041d282c0c101880820b0019080300d50f6038070141000314034079643e0f540da45030390101200e041d0000b41c204800c00f0740080e8140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 258194775 1250 258193525 258193531
    0xc0b13020a05240706090203031201030302070b07051b13110c0f03120a18020d081209030f1c090812070212120f060a090608011d010c0e060706090c120b 67
    0x80c40c829600c9996500c075008442c1001c49840700f084000c02c102c03081200582240e8619540a01a00d1301d030420340741d50402ea10420b0000303c0150152000200300034201d0401c1c0d480c515006001060402c051240d884408440f0142e1107030403416503010030100341124051801d418000e035000a607150f00064a41782400e0300070741a00250740042124200140c440c60000c1c0c0c1040f410314000035034280010b60140c2c2e09140c80d0f402900000b80c20310b070106112590020700300160b036240301082d8070b903294270b013280c1c1701c1c030404280c140251410f120101a0040314241000c0c00030155000050002d8584c40d12810358214071a017220040c0d100003080f00440d030500040c46036801c002011410415044004084101c0003803800740c40c240c540d40040d50994420603458001d08a454040240f43d8468158030301a080824a19070307009800c01d0b043c440444148215079812101c4e0f51030800030b030005d40420030b083c0e00c43d2005030b811688510005011451100703450008060135014850f00d2000c61800140b000401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 258196025 1250 258194775 258194779
    0x90e0d09080a0c0b0a0c060903080a050708010501020d050c03040512070501180b03040f110907030c1710060f12050c0306010305010e190c02010e010608030c01110a050a030b010c0b13020a05 83
    0x4030a2841c006503402c072012013600c0c400b0b040b83e900d1744038480c0122124034954078094401402c00d01082306041e0408620b034040c814400b004d01096581000640302c29400b0310a8034016480a0041841107100300003400801082e0400e0301d10b056600c000244064002c440b8a40c15504840b500308065a046250741d00c45109010855059500e40703109007200d03000041015000b1202c0011071010407045001e540032110005111341e030142012035000b001001d0100002000c50728840300b441c01007407410711641c424103c0d00511707201582016811a000c1d8450300344842800000840c84500c04158040c1d17a1040d0004c248040e128034002000405444041c1e01030800c241c0601d040c4402c1d481c2710900c60700341c0000c0c6100400c90100d9904101e004100c0c038660842c0951826901003000000400140b1014610740002d000a01030052010380310703c5014015004500208042c0205034025048100041c005047c5881442034940b00c03119908422540415004010780d0305004628200110801034081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 258197275 1250 258196025 258196033
    0xe0609010b041e2408060402120a0b18010303050a0806100c020f1504030b060f09091902041d010c030f0203061c050a12111c0806040510090e0d0908 65
    0x5001030812141c861406098404a5030b4032030801031040c1c0e1401d040040449008107005041d1100c4108480d1040b01038a00000301307101c0101b1250714060090b0f440c2c08120140c3c0c002140ca80040803801401c0810129800104681079040c581182d10740d00d60084d0301079203401d0742d90402d041009016010050030244105200f607816862143e00910301000310b035041d14043c62050740c1100280c0c2a082d810304800c44244000740200401c0f0705801c2c1a401020b00307a40610900007510100301050108403540c1549510030385000e0300c44403080ac0600c484c240042c100181c00103815214a100458481c0010f246a44400042020716814401c0b020341101c4840114214208400003070000040340c0c20350484001400e8050080c07000030700c984a4200e078445002c140d034090303108000c1d00301c1600101500c424040d003900103900c03c1a10300302d2400c121141d078a190042c0d844804100050002501210002141c0f0401040c001014422482e848800314000c00084081c001c0c004c000d40450b03040400c04d500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 258198525 1250 258197275 258197279
    0x40030515010f170705060c0d2015071202030a050118150b0705070f090902090c0304050a03050d0207020a271802011b0c030b011a03090c010f09050306010f0e060901 72
    0x5000c0241c0540d40c500340f01120141c2e10000851400c2815000349501410008a00b441e407440010001c000311a1502c460204098001006440d910401c1700700c81c05412203042c2607252030303101c1250b40d40070040341003000394564001e034484100c0c1c2080303518a550980c0e490042c4507050000901040a8261000500c1405110700020750510600e01c9801c0210342c000c00c0301020005c007400300102501c50f44c95a00d41c00e43d035581000700035104051080c1c0c000c0d090340700032030301c118203004c00c5902c12a00200180101410766500302d03950b5001d46078010085500b13200c5100182e443d0f0510340d000b060900c845010765a00b6140255402421403c0d0024041c030b401c0102e880005168150f105040e024200700c1800000000c001040d240c4401005040442000c1d01200708200215414182c4200c9003588403100074155000350f00740b000361401c41c41c0d43c0c002c4400d040319610443c01c0c42c1d0300c41068034182d01b4a503900d0001c80e01d400302c00c2e0448000440200020302101c80c41080c4580d100c4412945d24100d54 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 258199775 1250 258198525 258198539
    0x7170412020a05030d02300f090a0503030c212208011a0d0f060e070f1a030c27031e06060f010f030504030e0d0302010b040c0201114003051501 63
    0x34007081d47d00026000745540e14009007480460203000c40304c01401c0b035500c00300307001403c0707850b4894114541b15000c0000e010506040000c2030700c00c00b0b05200c0c02070100d41c1d41c20b0014184540960400c0302c80031402c00544c808221000c01120b4002c140354150300d00749003400c1d001820354a081e80c4021020070145800f24255898814030240203401201e04a001c0c0d505007405800b0b00500c0101c18210700c50080000350201075210b584007160700344242e1254150341a0711000b43d41c0f00a5441544070f40040c001d070341258003183c0c0c80c0f03800125120f2904006d0a21580800c0c00e00c0111584100e1810b0134060340c0b0704468051001c540d00040172a2866803010002e00040e00b0f07020384201c00c40400d0358030300c000703010140101070030010348000610300070710882c140c50003e0103807401620250040b410303c034001c811903005008140d5a00211508141400c2e101e040d5443d00000c00441032140c050211103140d45a094000d011291003c1c0d800b8031803007a400c605004d40780ca81c9200210200034a4403004110382 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 258201025 1250 258199775 258199783
    0xc0221030a031107211103191b06060807030309080c010c080a030608060f06130501050102030306010e0103020f1305030706090311120a02030d0302030702070608010f0b07170412020a05030d02 84
    0x1000c110300b000990181c1c0b2000104950041180c02000140c4105070201900c400c0310a140b00024142d0343d11500c44d03000c1c55041e4036030040d15846500a8404400f00240a0040c510301c0700c102c02d92124200c9400c06626a90143d845503800075505030130192083c0103141d80000700d20003806030000140808405500000c013013064024010f01520307400b080c11503400b48240c01284c001c00e041c01c11100703142040c0f41e101e0b058050589449100b103849440c43c0d2030452040c0a040c0c126141600510b00307545e590001510101c20626401b410076600b00b15440401e00024050254400304003403444420f07041009041c504a0103030040c0c0107012506900f0130014031400c01440410074141da0078020f601040c10210b01c1c0a54121009505004e84890b107d40158150b0181d84154070a5003180c1c0304650f1040c06803a130039804e0080d100d41254040f010712141100318001c12409106841d003625811075030f03103041c280350000d41003100c0074404145603001b9403030455003600142000710041d0020156241020390381d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 258202275 1250 258201025 258201037
    0x10603090807050601091406031914010212270a11060913020a11010f0603031b0804050a03030f03060f120b0703020c030c010203010306050c0f120606070f030c022103 73
    0x405445090350001c000320401503981559009084070301d00d50b183d45150b000ba183c015142d5000200c00701c0043c4d901d1400040046440c007044204145a5441d40c0b981103262000c0796418186640801c50358861000d44c20040740f00e1400c402d9010503440810368031800d04446a1801b241319407000d880d981c046100082101c10103074080711019078529003170001c01c40850f20707a194928031910200d01c10540a07008002c00300c030b9883c40b030002c000c10300d60025402d0480369a80000360000340c03103100d40d0420324014200003442c14000c1c1079060400743e44d0000136559000c16001180020b10b020449004550180207460151070141350620040781402882001032911042c06460350840d0404180700a00950444801007481c3c0d0503656500c5000351124040d620070312086441b0b038079010000f134586402d5003d88050220094403589020b40c0403941e40c401d000007516142e07024100b08040340000395030000e07030501c46129845d1483e05040314010400715a01e03031f40c034502d440c19523103964a170180f00120031982 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 258203525 1250 258202275 258202277
    0x609060e030c0409030509010806041e051e01030c0303030606030b06090402070303060306051e060307031a150307030b04030e0306040201052203020a0807030c140102060a051503010504030f0f03060e0106 89
    0x31090094200203450440c02070100740d04030f864010301e0740502d0b522000070b1910000c280c80341100c0d526480140000c135000440310b02400003140e2091601200320b9000a500700c3c0e143c0e80e0240d400302d2000d605071000d1200380e200300d0b81d001206804008241c1c1500401000306803504081141800341008540a403154007122485282c5c0010000200f501960008000c0e64004e0802c204501e483c4403040b07485041106501507080c60500050604d280c001030000a60b41d1200b58030030075881c000c95140181c40d0182c0045e0002d00202d070158525202040000002c5000e0007071500c407403e04d810094544802101880e000350007039000c000150360440700303e40310308034981c1302a03000040802030f03004841070350303000254003d0101c4000204843c0c001500401c2c0c030301600640c1e0301c0942d1402258581c0c07000030100782c096045000014100c0f1071b20b0388826401a174020340400c44454a90000c1d0841c1c0b41258103d02007600a0101080d40d98032840c18401c3c0c82403070070100095401c186000c2e50007141403141310 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 258204775 1250 258203525 258203537
    0x108150f0f06030f010e03030601090509091e07080a030807031406010807111213030203122107140c0105070206070e09040b131502030a0515061207021c210204060906 73
    0x40c1c003640f010003110911082d001d008106c01000d501c400350b00c0354029980d103400103494140200d190b21b0701c0030210380140507600041404800c0111a110101c11040880c42640102d001c00155000203014040c3d03020b2096884004d18504103101904403090000c00c0c0744450243c408000300c030303608100d10a42100250924084548e001c40d00c6034078041e400c404031542c041005c074100e0300c02d42c844400c0e84152071007141a503201490b032000c40b1459000c0c10790300ca018143c03000c60000c58584272000d00c581040580c606242d24484c80b441082203039000c40010560703603641d007040110556060000c40d420010b94606a1001d06500c000145030700400b50000e00b84528903400b1850422580141108441c0d006001603100c1c0740c0408c240d0025007088840040c0a4141000200c1c51101d840c5065210f15005007410704050005080c0001c0c07a00091158007540f00310202602c1c030701c0c1540d0207107900100a90340c0340d0000d0050803240041e5102040342e2a2b080d801070009001c2590000b641000b981e00510780300c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 258206025 1250 258204775 258204781
    0x1b090111072601060801020f071410021803060109110a0509040b120a031202270103060306061701060b18090c1201060806030105100501080a1808040602060108150f0f 73
    0x29414101c455210305540310340d2001c442818000000c0d024214050380e402048295580e01c9510f080c2e101e80e54030755013020010071071200003900042030b00f002000543c0480d44a00005070301841245e112401110201c4001c190071501440c00304a81c50160410ba1001d1140580105a07440c10780520800c2405001022801051355299540034a4007400000d0007001001e490300103c0f916035440b400b09600141204101c0c0d149299107000701c0310075245c0c0c4040d15a1445d91440701b20203800201c14400e0405403554800008140075000f52405400740d21101003210514030551402c480243c1d10030454a2009e1200d0215103140802d20301c040001904c028a895540400040161042d075500049400d40795002044180c0d1011000f84a400e003540204050344500c54003180c010700610070a0b000603004d07000a0004010340c3c012500d44100b50341052151380c0141e88841075a0030a810040040c0e10690042080344401c0112110703400e2a006d155046042c44210010b11060050908100b003001c103002c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 258207275 1250 258206025 258206057
    0x50309010e04090f060b03060703051005131404050c01020706020a08030604050601090e041b06020a0c0614091c0209100e0408070206070501090c030212010e0309100309020a0b040e1b0901 82
    0x80f000d01c0952080074800c00c0d26161401c1d500800703d060a15020b4817891001404003402440380500030340a100e092090203141108210780a90440101240c20f919030300c00c0b03003521400d662202d0140f84100042c003180b4a0b040002443e21406034040d20440d0301507408003000c200e0f84003c680e00060113440101d01990740c0001620b8681c09035101c0795541c1002010407041c00f500c002c0c003c240c04034500d0380f103601e03031340d0384504a0390340f18040005031001182c40c5082242e10302518200201003441e410080c100310310540000c0c0e4044003440103410713140030801d9400451500b144580d603c92851514440240d05107450f080000b0301c0113000420400001800c20150b48c0c8141c10740e00381a074820006e2005e036002d840d12030900480703480201c0c000c891083d50028030b0407041c000d19004029502c000c508140300e980401c11022011900030082c55034480c640b00260315241a104050440311012a5645242030741500045400070614010a003010800000204452041303561010003444c1c050360324009041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 258208525 1250 258207275 258207281
    0x304091128031a0a140d0b04060f06051503060d0302070f08031b0a1e080904061403010c030c0e091e010b04080d0e01050a0302130e270a03091a19080411010c050309010e04 75
    0x6c00606044015000c010810040c2c1d0400e610803c4020014013805a6070b500f8024501407120391914041001d00014101d0b003402c003c581e00950080c070440310b01903070702c032003010307482c1005d4224035420340000520f01007607070300d9840007240700304c440d002000d0b40080398503510411013038001c0568041b400603141c41c0c180b01c100410345448460040081241c980d4030040024080300044582d80294200821405c2585c0a4456210b05045035101c51541c201c030b1904000140324010025440180c5404000310000c4c155824a070207005440f2010303654906011641c0d283c02d0018907034600700005c0261254260341c1c08401d41e00303000170340d040158544c0d01798007000c600c600043e000380c10504c40382c0c410001c00c800c1030480b126003041c2d4000c580c0398100310112210b03101c6141010181c013045000b00300700071181d41c0c1306041c25001b4600c0041820180c00b10704c000e108945c85020f4400182a207003d01003445444000c0e64404c59090074030f18402e6006039035a503141c0c007a00700001c0c140004142440c91686442d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 258209775 1250 258208525 258208549
    0x306010c1113061d06010806040b130c0302040617131103030c0a0c1a0306100f02030c07030b041110170702010f02040b07060b120304091128031a0a14 66
    0x142111010b40e0b69109440c02009148110745804d440c03900c201c0c0c124804c032004c013801400c069503a008660384160038400a004010850b03030b001104104002c409950521804c114015943d801607541c9290000050140109040b42070f04030284c1418413803c03000130250704504070750004c040c0f44d00c4d043c80c0d40024110f0140c180340c0c09460290b4214201007052406440084e1000303c402c10340c80d10540e04580d40c85000c21a11035801003610802010418040d081d8000c0403450f80c4100c92405488450a40c100384069104907402701a8000b80020081c0300d580350314a142d4265039022541520800c02030840c0006000111a4034a110119221920039040080c40c00e102040565a450760b544108a40307502c89103050720313007500c1e10600e0000b038506140ca900d0354045560095081504280e60b21000b4220000003003243c103010405104003a0340205e00131281d42004003134610500300402d000e0b00b03036842003072000ca0181040703403100c2595a40041c0c4809541c1c22050011000340404041041078400c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 258211025 1250 258209775 258209779
    0x3101d0411041409060901180302070b0d0204170c1807080414070b0a0e0f0a0f0e1302041a01020c060408070e04060e160f0e06090a18021203070618080306010c11 71
    0x20130044c4418001542c0c500070111440200a041e44249030008804054100240142c114200800442480b140500080303910000f0043c5016540d9007141d6015a511500c08002e8020300001c04032460701800c0d4030405071a07901e0a40f6585418200104840e10080008092000d182c001550312a01000000701505030070b001c45640d245040c0d0040c101c10503840c000d510403802e45c0c03402034640c20701a07040011100255803203a003039410007403001c1400388020128401d0300780d04140ba4015a5403405400030410640107542d40714040e03074000a06240707840c039640d80140c1c400c11081102c040001501e0003160a0040502c4480e101e915111000e03008201c0c041c441e501c2008000e444041c400d1081e07000b02c51030341c1030050141e40c1d900e0741c401540000b282c00a0740984006d0028007410301c5a08180d060110140b54130140e000039034002291914032144029855201054a0003004424841c40c80214081c04609480303005a0703582c03100902c0014a20b60400030b070f96218800308010744804098040c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 258212275 1250 258211025 258211061
    0xf0209100b13030b15030a120318030509040f050f011229010f060f0207090b01020f1b01120b0918190f150e10020a050c03040b03101d041104 62
    0x407515000c5003120302400141c40c84138080c00481c441c010300d44142d40e2000806009032941000b191596010680c4055031541855203d803d9000c1c2d85c4501c0f010b1084041c400e0b281c00d51519000300501c800c5803145860800024a00702c1400704003482d260420341100ca03455190082c9000b507142c401014840754440e221f42103130142c44114640c0c103088006060710500f45591101c82d0350341900301c41440701d03602c103100560800c0500303000183c030b03e8020808102060040b5543d00a45079029450440c1d1400e002d40304034210798943c4d40542e07104590503500360300403005000329840310000900c07103100641211124148a40350b0303a07503500103002040b0141003150003400044c1701400c105040c40701e160b0040b181400442c132050503001032072240342c0a61460600604581240c84009402503000c0c1a5038400d100c5c0511038510030807410002040036200c40c85040b51603081c284101c044060058100c04104440301141c01c40c0100850281c40d8020f4002298202c5000300c003020800078419071001c404002c0c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 258213525 1250 258212275 258212287
    0x4020a0917030a0f080f0411210f01050705040303050414120f010e15131104150902130b040e07031125150c021504050705030d0c05010f05040f0209100b 67
    0x40201c0030b8103da51040d124140030f540e540508903008001194007180942040e0007250200e118001300c2e800019019042036260205d07005018500050141c55003510b0340001541c00481d0700078040c00d03800c08a1400c05504050940d94064540c0c015809400c0941618405000440c0e580c0709903801400001c070140d80d6280341c5000c02c0c5018000d18035010040f8455010321002c5082c2c8589500c0c440c80000700b62003400b1038990354181000740041a0390f42c0c002e0301d448407000400c0c04841640b005020306000140d44040804090206103415400402210001d2000300029402011240d901c044c640c0b40000c3c0221a0300d220031201d018014840704d80c00380340981d449a0352494600c40b41c41a0203034000c0340d200c20720307112203030306896400907002c006800544501004100d004400ca4101c1d10038400d40d02003035100c4011a10700321081582200207a01070140d00d05005080c8904036640c0540002401545040c2c2c032410000b507501000203010b0f552010000e0342d41c420000240000c0c010341036841d5510a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 258214775 1250 258213525 258213569
    0xb0f13091b1a09190b070b0f010308091e0901092301080607050f04090f06050909010b0a05012604080a090b03060d150b1008060a0605070510090f05070605040e011401020c04020a09 79
    0x28100c03601c100d07000d4087c600810008281c00e203000b03048a074041c40302e9207854000e0f424018600d104006a2401c05100002507169a440034001b9010301a1000000348002c07041003406120040102c00e62a82c0503140018000c81c100852a190302038146d050490350303522840d450810620072540502000c51420301d01040c01d88450308450200c42081700d4005098840349070031400c8a203014480c81c0d200c3c0c2240d200308001e5018480300302c1d65030481d041c003982d41c5140e10408525080222803c9070511000100a08000d40008454000d08205d80240d405e603c1c01c90003045d8030040401020300b03c282045202182c0704030343c1d08041021040580b41180007900c840008d4000340080e02c64610a0240407000b003001881031058500c426046002461414803100000c2c0052510741030036038298a2051001340842d90070070950380209203e5613659501e6180c494000c1a2140603001103001c81c1c1002c810344526030b0b000071305500101048138010b0340c450801d41c0656036402c180d07000481100310111070350801 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 258216025 1250 258214775 258214777
    0x50403050f21092a01030b0402030a0902010f08040f0803191d1002070c120204110c1606030e030702190f060c0b0f0c0d0b0f13091b1a09190b 62
    0x140201c0b24180c2d010f80b40d510f030507a1a0303030340008004480c210b8425945140da401120242c0802c4041c1000150800c0020205050ba0700440f403604034141c44440c240c045503841b000e525640802483c150141c1d04080d03076161721345045504c0180401002201164018402d4100b030031441c90900710410000110884000a01050100703c940320b0140c4100310300c0c91800ca00865990300c1d0300c00080a001414040c00954000000c1c0d01a81c00682d03a0002c05140c00d11310004000d800c520a004000c040d803007101403200284150462010142003251a100c0b41ca0000140c03040243d04980d02403007000d82a5000c0ca88042e5075220110014226400007000b94100030354443c000c1c004c41c100f415036502c46c1c000640c1710009544440c0710940411000b10051915030201c00c0c440c1e801400042140510000140c0c80043c66203141c000c41d644140f40e0003081000c0e640340c4030100741c003040c40c0071a0340350140502c0c034500b00c0301c0d8a4040c2d804c000ba103500755940e500400400313030032006141d285450700c0d20f201e42d030a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 258217275 1250 258216025 258216067
    0xc08030c0717040e0f060301060b0d05190509070e060f060306040e010905250b04060f0c03090302060711030d2a0501090b0405010e12040503100f021605100b01080603060109050403050f 81
    0x190f4100e000c040781c007c1c2818010001510f84140120345801d131a50942c90062a0062146c5450704090051280780302d9580103e42c02030031500001d20300c2604200321929114030107030806200f034440940303489054503110281c07580664110740024649a1080080e07014240a1038018100c1c0a800d8020702e540c201c0115120003101c0a5444072030342500d07008100e05603c80d0340681400328800c41c0d48140c8185c862100c1c0070406110b40f90500c2c4040c0d5950105045400070107003260007400601554500e81000c1003021008500c62601141070b03084010905403903401941c51111309060740e41210305000003508680e00e8694040101c00d21071038541040c500805424101d5040e80c0201e034145405050038005403819941c4c018050a240d842c00600e1500030304400001000310b5400f030044081502a40d0940791905005a000e13007240d4940c19611800c0720b480320941810300194601340300b442d0301e0004005055508407140051507484900341a2224000c0081942d0400d50009600c0b9000306c419820f030790 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 258218525 1250 258217275 258217291
    0x605041502010605030a0b090f030c0109030f020a0210030e0a020a080309041515050a0306050603100503010e030f1602040e0d1206050a080a24060602010504020a05010c08030c0717040e 81
    0x200244a00304034262089803041691680c40710441e200440c0424409039004860f1000301c07500c9480d0500c03080e0464001301006490750355030b00862800d158008241d04020400c601c05491061201c0d03000030190b0424107181c00404d9a18071031201415030400100102580061140304829075454050382da80d805203074154011810f000840171688480700740803050f0380380090600800380202c035045615030480e5443c1c0c0201529504c0009258803184003d600030411015503169903810001410b003540c000d040d94000d5580308200c2c01282c40800e100361507818419440c04a210211400040c02138840a1401c1006002d1240880f60240d00414402200003035200144002030362a030421690b0455441440f0168200020190016a910000f070700305c1e2103109a080f040e50054519502280c005812000c0580e540d0000c0c4002d51400c481240c00410091825545c2e440c40c6986000c0700c2d0101806000c5685030100b04134080100d84a0000ea6400d040c0900f181c540340c1e9218480140f480a8038018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 258219775 1250 258218525 258218549
    0x212310050603040308010b0c03070c030807020405240d05010b03010513050d0806010804260a02010212090606060406081003021306061209030906200105010308030f160c030302030c0d06060504 84
    0x24407420040196441160961100764013603181181d1004581c0c0b042c54800c106020400000000801504e1068065806003c4240d290340e40c40c41404110340c4041e00c540c0b02c0c1e90400014410031103c40b581d8002a48040c0d4400c0b1142c2401d145c044e0141178a00802a895402d040812000c000d509421940150080c022582500d0809001303480101c0107407441800a5500300c000303000315400d210303050031451030034003060a036a0400c44030304095000303124039400503500050003280d2440e410380b0303003030700140c1c3c0501030320702c0c1c3c20054009282c5118502c0f0b180180900c82001850841000044800a540292030114803030640c0392028000c001e02c0c06042c001c6002c140e01a4000c0c0c3e840d11500c100241d040c0c442c07861903814090190741d900c01d0f00c24090400781c440002ea5140305000e00449000354810b4691940341c1c289020a0f100e0110000c00c2c03121101c2c03c0e004081c6200303038825200070780a81c05040050b40c90b19101c0458609120b48084141c2d11030070001e000a001e64040010310494400609070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 258221025 1250 258219775 258219779
    0x702160303050306060f0712020d1701050607330f0e031c0218130e06011a03150111010c09030b0c090a150203190f0f0906212310 57
    0x80018460600000d40022002d0001966a091800042485a00c13050200d810502c0550b0b400c2ea002070350120920040c1c001c0c8403c0310307516412000c500c130190340e110044080c41d810000031803901e00078104042d10200c806e500030158920521703001020110381080c8030001e00d4200c0e501b4005000020b4801002c540b900586200c80c22000c000c0c2c0380340d08080030029610708002d50340780020350000800d82520b03403910b80c05142282e80341525004001c00728440481c84840e03550840f810080c050740b1901007192608840d4040e1b454020889620149204007a901240218012102c02084180b801b170903620f01712039450a160417000741030460744581c01c2000700707544a44a481e0b5a003c5d5200d6a0303048a48a8030a01c80c03000b50a9110100c014584122800c044401d001c0203841601c1760740302d50100d140d001d4540d00c00d580c45440c1001034440782c1480c001d80391074140001c2c80030340381040c51f20440d0386038100d0825080c03241d086950120140248044110140107254000b0002561980d40c040745500300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 258222275 1250 258221025 258221053
    0x1b060705091017130503090d24020c061618030b1611030d0203090a080f070606140d0b06031002130e0a060f0308031302030604060b09070306030203072c09060702 71
    0x42501c69154000c050b01a40713030a12034007000006030b030007140c49000c02d0040040340c1e1242c2855071545801100c0300050410803113141902c1d44850403103d07107090700401901084a100041e800d0300300410101c1c220300120440d808407031a41114407009110341400000000340141d298102d400381202985010600c0000001034a901c0d4104a03441d120b074100f4031440350103030300680c00b4662080e145401c0d207400c408070744e0328003055034814954190780d2000410785000f88200d5120320400360258490b8404180c200d4400240b00c04004130f001401c0001100018a481c0c4051114020200d48c026041d51034000c45030500a0340b080034003903201d01c0c55026001900c1c0c0441c5001c5d520894281c18106040a03003551110f5840d03603c010f01d640d00480a00c1040d100507101081054400ca010300c00000329259540300300032250001400a000301403c201e410300c0580c0d00030400d1b00481c1d1460700f10b0105800201c44200d031180340d03813100810700118103041103901c00c008240e00f48220071540c251805404c41c410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 258223525 1250 258222275 258222287
    0x120311010e0f120a030e0307050a150207170703170f090118021e37060512070318020913020102060907140105030705090d03090e0604110d021b0607050910 68
    0x31030180306501807058503103c09079040040002440380d150200c1d00600d46d0114a01c1d5601c490800c580c0d0703900120400080c48001181e04214082000301980382a4450b00d900c41420000c0b42c19070017401001500d1020180a01301c2c0c030681c0b40f24010b0100c003e20b03100c110102078480c100e4001c002542030800c00458440c4844908204a90041441c0789840d03410b05015250801014140d801c40303242d0640680b001075014040d01c06d80400c1c6541c50001c10501c030740040f04901c80d03003c4018800140800c0e0700c7e100141e40c049500c01d25500c0d00040000e01c40802d40300f21020841c0103500071ba07110040c0400000c208100c144802e0003a000c4070381740d84904070403503503410300c6110f0b20840700c50a00380d000c0590302c00d50003590062078520b412030401d100e0070005011a031030702904402103111060100001010240740b60740c4074004840401685c1404024603165209241c42c150301c041d400500b00381c03600c2a910400c1801050001103440e145011103014003a40d201c403c0c1d0911581d04120000f010511aa03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 258224775 1250 258223525 258223543
    0x5010507031d27091c020309130b06070b010312170f041506140406090e03160c0902121b09010e0d031101020d24080303130c120311010e 60
    0x141e10340e440c001806449405140403020346650010700c6803e41c00c20180d120206416007904003421520300c2c01c1c401034941c542080d5400d000c000c0100404084515500071003a1074504005484661280d00c3c440704020041130f10201c4160700031030214030700091101c03111607141038034800c080d4411000c2400c2c0b420385507101007006d4050b8807443e100006142c0f00418684d25045803148060b001032980c00d500800942c0c3d1590850303580c50000303002c0d5143d20719050160a0040c1000302e4100511148002081c0c0ca03442800c5406c5940024140c000c0c0c1080b060701e115000034075402008540300c03d003d018400b01441c095803150416455005400b0580e030041c000c032402040c0503100d1440011000b014000040b80d00102a01030100c3e4440c0004012000e000418201c4032505001409210005000240328000c1d1826440d00448107001c0c030054400200b00d0b60041d89140602d0b003040190b10348410a000182c0210f445800700b0302d00c5908058000b100446e900202d0760081c0a02ea000b60302181e9201424 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 258226025 1250 258224775 258224777
    0xc050f010612060506060f041208040312080702242404020408070609060e060d0b01031e0507021908031305030403150501050f0d02010c060507050705010e060615040e012606041a010501050703 84
    0x100800c000804003c5440882c9072b1240c01c5003410580d0340e41340d4180b0845241e10942c0403c0e6130004102a4036410302908449841d01c0c0f10b0400060310016a80d59121740007424900c800d116046405d0400c050043c01e5828800300800c19940d85d0340b1009440e0f1517038032601c84c100104206090110354170340a286582c1d41c20101030203050809411220356030140c004200114107040c1c5d103800da02074000c00140700c005544d0300035402040c035050103031000340340c400c01080c10600c8078401c42c088800520204103da800c10b4420500d012158048d0070480e08500c0703a58802094580205c0e80710f01aa09507420090480c1e200322020820850343c2c4060004000c010400240043c0f41980030000055a661001c0d4100203130389846410405175540f4603085a20f001d00d8566140e1101e410405503141030080003190b5803102540c0e90415192100b0088201c50601903060301c000c0161103202180900e500001c076056248080b6201c1c2c0c10603003800480d2100008190184450f07401c00400d4550091088484403581 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 258227275 1250 258226025 258226027
    0x207061d031204060b060d0603141f0e1504050115051203160c12110f04060320180f0402010e030607020c010c0204140103030513050406060f0c050f010612060506060f 73
    0xc03002d015451000200700711460340d43d542e0070740c541d030300c444010700b206848004001500500350f05100d011529010030014066012045074001d04e0504294012141140c100124141440c4003115080001c1100c141e40c84080440810040c00320540003a24118400c440803044141c8400511081b209000228038059004200702190400c11080400105d8082c00d910000305840d403540d03500410281d841075503928180220000c1600d07110402d0152410308840c2045558995a540801d4000a200710022030781241c20088068031032603020305641c104100c040d46a03252800281500700c0080c1e034240e00007401d143c1c4840043c02e0004246000c4d001c00c2c1c0060961904250046a03c5240050b040740c00c603440d203265529400c3c500710854041d42c426100c050b202c20f900b00501070001c400c2c0d03102910503410b100081140542000300e1100310b01c01031800140c0d000c03041c1400d0f480e14860314103400c819880c0403000540300940c8603400c101079100b030400340010745500c000c024590007101845e11750b01034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 258228525 1250 258227275 258227287
    0xa033909060b031e18030a0e0118030c030213112811060c13030203030f04170105040201120207020f09151201050c0d0902010c120c06060e27010b030609010207061d03 73
    0x604e0303148503038130158800e039004509400701d503441d003036070000d242010200d030324900450325640c2c01111000c04080d50f00c641e542d1143c6581c807000e034182041d10001c1c0c0540a51421502c0a10142d0170654410b0f800c0c4000e16076515506003691858408032604144a110240e00350b000715110b00006a01684400001c2800c0d8490304d400c07440a600004105000076490f00300040181ca0074405050600840000691218500340303150300030b004407aa403480c0991520082000507a0409114400000720038001038460034644046031404224480c4254000b1042e420054902481c0b040d40709602410340b00c40c244c002c003c0e5802400e8400603a500140000203214903020400d9990042d2036440c01407420b100d59442e19195141c0e59000d0203c3d901c00180501e52803014884d89028810081c801c0c0c683c40c08071803400b00301c1c08013030402d41440d41c8144255440740588819003504034040e04500201070310428103250000c80c1c002d42c42220100c134124182600d0360b21101e11000e410494400800c0910314000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 258229775 1250 258228525 258228571
    0x50a02011b0b070f09030c0902040e0603071206020a0c0f05060105040b06070b220803070302040801110a0f0806040608030a110c03071208070501180f200a033909060b03 74
    0x39140c4c10b11010444010030001c00310b6018003c1e040285056000140d590f42801041685111700a25140c001d81c09120b0030000c03c41c588141c0000c1c0d507044070b00140c49208003481280c0400c00780b00003600611651000d6014044086074041c101c5504850800c440c401c003034140540d6004002d0080c0017a0490340000d2241c6021001800140980c40601840948a540d410a164000f03031030003030000394082000c4c41611002d1140800617a0a46c1c0390f0303410101c80b0380000305280c0e11207180504200c0350744081015500d03540c0085015004c140b090b02d4840b0400da43c001d002c1e45415803050881d01c2044040c2d4200c4c02c010500c0403c1d1040d155180c00b90101d1522504016800303000122410365881c3d000c2014400749407012008103124060b410b925003071a040152131440000104842c001081070b2404007030b501c0100c50400c47ea0b0091043c0103d503076050461443d8007240329240380000042c4603100c1e0024907440400140d9610032000c000c2c854856540c031400380811603074101d40700c981c02c2c0c0c0c1c09009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 258231025 1250 258229775 258229787
    0x106090803121806100602070f2105070510020a0314190c05190308010e070e0a06030b0604050a0605040815071b060e070e010f05011d0103020a1407050a02011b0b07 72
    0x151040c50000c030100d0583c00b525180002c01c03903003440c800c00214410b018044c0d050100c2001050403604c01807a86080c003d0841070705001040481d80011402d1500080110038481c00c4002e103002090354240e40c04410000e5190070200d2070441c005229884c03072400e8101804261100c2e0041c4c01c6460545000440301070b6400703089440706036403510801e03410b022284031216601c44104d100750380b442015458600041d0000b174000c0c010100b8041680c0301d141480c2c440000c1101200c001d40740c04a50900c0c0880800c146200d00d410003504008610b102140c502e4220300104216140e10044804680d0a14074801d4010015551040000c18491004200762440c40030703420100e00514001030f0300d07030303108102610300b5005510103440d110050004211034000006100300034442802c0004001e03003490003410208a1409050341030650100d0188007a91040c11100091a8841c000c51b64a103403e0501d41c2e41e499420f41c0803400a2400116401c50035140b4496404e40b070350111503800c1d2900e8061081e00c030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 258232275 1250 258231025 258231031
    0x91203080402191418040b0402090703200a0f0203040e040b1806071107050a0302130c05091c0b0a0903080a0f0b060d09020f150f0904020706021c05010609080312 71
    0x11124420740f255035011000d00310ba030000c184540d0202c0e160b2154800f8000141c009968040c07114a00e98108004501c14121140c1e10a40c101c640d91640c3c0d8608100341c004100f02c0032080b030703a0300b0201c5108078074242c1c00006004040e03c0303442d1011801110307141240e583c0309602604400c20703688004a000154583c020940000b14003a00b001c61721021544280740140c11512500060000c02c2c0380480102e091250b080504401c2c0c400c2501c030360a5401260584410307443d4513000568681c411200103114800b910b24078400140a84801220340d0607039a000b00c95080c0a131030f92409400801e02c88070352403285008159154071807120981d143d6078080c0003405034001a4003015107441d04441956203200c020214a02c1645000840c0c0c40e031801800200d00c01460b41900034861461400306d241c5101313040c0c032442d41514041d65075030410000450068020310030000e00302400454626100c0304120505c6501c0550354404001036a600d1404503050220340c4241d1140f07410802c031000c40c1c034070345649650b8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 258233525 1250 258232275 258232279
    0xd0f03051e041a09030a0509060304020a17060f1f03060e1507090306050a020405030303062b03030504060b0d0809060c071a0a021c020d0c0201120c02010203060a0501091203080402 79
    0x4492485581e40d803169990442c0c084408400800743c021040c1000034402d40c220555070011424552070703103c060928450503100343d10500c0044000b400f15511880c6250140c203040c0f00710310320b1610300c11042d90b4624080e20740d080c00c1100c00c4001014403070002c107001000d801485004403282c1c0b5648845c0001c0c08240b1850711140210144070701c505581c880709034051202903a0383d8075198a50304202085400140030201c402d40100010030860f40c0010a882d001981152045020009054140b500f9180780d141240061201e50745101450740590129120b6030180400b03011150600e81000040c107250000100014814407030440d040c10100080c1c0f1040d22607400701c0701d400b45c0311040048008905071040e0041d900000c5d58419460381400004440d07440754100c5481e0355403100c7c0107516003481943d10300c00c0204403461038003075a101c3c480c070141400e90120200041103024000902075031003222200e00808940100041952081c0d007403808441c640c900b404100784007941c08540101010704166 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 258234775 1250 258233525 258233551
    0x132103090605090607030606020c0603040b09030d050c03060f040b0a0314030903010207140705010207062102090613170307080d1521050601090b06120612010c0810080d0f0305 77
    0x1000500707503109441c0184955001444246040d840090580360150802c204541200300007010300e0b121441600d4020b5407080150f2100c3e0b454010492941c05181c0c1045000b80c104018088009500001180980c40a40d4000c40300e080e60003d00c420f039031103100026040940700d1410030200c1c00c1049001c24018020703003503c0c580074172080001d00b640c001000c2624011340345110707000c0c3c50400b0401c040c010002800500b40b940d02e03007100034210040071383e002100c5200d00703030880090449560440302020802080300781c6641001d0343e240e5002d10180604401c91010b9240d039000d0820020a54440700d500c4086c0038a8441480d1400c40075005018a0741012461017001050186206401c002807584008566001030a10305045140030410780c030403102c01c1e10f4103000301419224001121501088240c04103082d4480d41d001c038070700a04002c030365000c1d035103005202044654049905401003400349a12403400d42c0392288a034845250400d614082001c01c1e00340e140890203508a6640300032902000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 258236025 1250 258234775 258234791
    0x9061e1002101a03101806020706020d0501061205010801020301080d0507020d140a061401210c090501090e07050303030c041a070614061908030a120209180f132103 72
    0x200c0030303518942c1d921046030150f054040d855050400c585c100007242040103002d09007030040b0403494400c409101900042e000a20901481820f8040b0307088483e003a80304000a40c2c4d50700700108440385402d803c80c907060602c800000d81071070500907030341618000d2001d06641c1c9402d1710f090b2156801700a08981080520803100b011a1000b4070084045000340050805401d41e440c15000300ca1100b8115222040450018070107010794682c0d0051002080569501d840c8450402d001c407030b005c49e80001307511030800d00081041c607295003065001e12000e4048800c0d4a07190810141c072404119004580244140010804240407505039403d42d0008204a4503206c0c1c29103425003614030200da0b12400b0301c040c0c000d0240d11300b00034103102050300c8054007040e0128240000b030743e141e105086849007002a401c1c0741e02000b202035812035080791401021890000d42d130305640b2410120494042000c4402c0c800016000e101d034508590721180e2109590002c52104501110441580c40140702010354a10703803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 258237275 1250 258236025 258236053
    0x11a0711131d06010303020a020103021c051519030206071b03080a0201091101020d02060705131701050610090e2809050c1311042607060e09061e1002 66
    0x39550001070250003289108542118a00b1401100065400c543c04403004001182d40400d090440540c2481c0159454030034401c0c0203000003041100740703c03043c6058244280480540011200e900068880c2e0280c040c00c1902c15460081a102c080d40180341001010001081000c014019001c940903003440d880c0c80361075054598004200c9080542e549118040601600581c4030071980300910041070f030f14902c0c00d0025110351001c6e103038505204010900d4000c40e0030300b0803450090279510700c03035002c85045c072002c00d8003030b10042d078003140500c03164141c0301d010340e1051050400b40c80220170b80d02c50b1754940318542c520280c0c141c5103003c05c1941241c003a207140300d0303240074840c0024026802040b4910861040144602d000386c4006582c40c41c20000400302d582d22802d0310101c41614840c0e160f200da0304680d030801c04955403845080c901800c140803500b15045421010255070941d0000d8555075036034240100c1c0d00c58070210b808094540c182050007443c1c0404d018042102e64416281d06c0404401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 258238525 1250 258237275 258237289
    0x1302060f030a02072d0233070605010501180e1e16121a01080c07050604030504080606041e09030c05060a0603060e0a020d1b0b040e0103120305011a0711 67
    0x40911641e600003400b113040c08400d01150f0075804c0c0d0008010481c140b1105040141c00c40c0c024020301540410040c003200c42c0850151104004032800042c1c4c910524584c0300a580d400020221034541c1307000000309455210700c08000008a500b400011801e040418000045000611906001b40724441140700c880380e000007580200d500c641e820300c07012002c00d0050542d440e1038441c0c100040ca845149a1110b000c1c1c10040010780c001c0c20281580d44461030041c90038480d480c0c01418910405060004042c1d0000c01402280c0345c10741518000d880c0d041c04c120658420069124500341542c07202d00c0515415881841c009100381010702e20407a20341d698a043c428110b4032050100d0750b410040041c0181d0b400340e8103580301c00c240034000c045000d5002a070740030407c10018007401c41c001c2042c2d2030080c102c00ba40c0040d088222905842d141c0d140801003013040d0900003110440941402001e034140640a002c1c183d6084100015030100ca20032008001e4000c0c120584401200e03101c00103150b12007035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 258239775 1250 258238525 258238531
    0x6010522060b090f011809020702010c0204020c0f060f01080d030c030b100201050601022b05031815071202070308010e0a0902040e010b0103060b0a140313140c01110c06031302060f03 80
    0x1c85507612001040300300103004040d214941d05105010b40003466031b4a12881d490162070020800580b0740703446000480781c5280d4640c009411a10005001402c0308000031200d1020301c41208441d040c1d5a00c28a81150709000c1c8601382c12540b020180d07c4a40703001c2d0300b1a0400070300f035140015034540140005003005400c0610070f00540d545106008003075a041c0440180b0074010106403101003540e1000d010f54102d0180780404002c404808908010034450780001040f020004444e500980c58049119021040c2d9855001c60f0500d8200d01c0100110f0007070384d1541c1d030551130b02c46150b03203071201c0f01c3e030110001458440402c1c1c7d02c120310801030392240300e0160150905c01c00010705ca40c42400140884245800522810350280036400e080c503032104003015036445200950362a070f03c1d4451a00440641c45c00d00030b11186684445010a13000003905006844091380c9a030a40b5414030302e055201c1c00c00303088083e0450b41c02c000050080c4243c044100b00c1d1840074258900e032840603049000c81d0b030416 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 258241025 1250 258239775 258239789
    0xf0308071b1208130206070b090c0a030b0907050d0b161103070605010503070819030302090a030210030207030315060e1512090304060320040905041b14090108010e0601052206 77
    0x80c0e115204540c8030501c1a4084074414000d813078640607400040f0140203402c00100700380d0801c00040c188210a100e81100c00d1009880c0f810b1080c0c5a1504030480741d01110f82c0c41031440340800c006414684412b80340e00302134202005092030307240e0052014624450505841c28001950b4440c0010347c0108010141075000f0107000880d5410002011708000c1d142e40101c04940c030016075480d01000400c0000b10720b56240c10f0059031803608101041c0029416030020358404000d2141e5035a0340d0b01a00103015061207503a0800c1450100e480307480c0300362200d004820000e040104007030700b60308107520422005850a081541040d5074040b22404002c800c403800200c540020804204060f0113020b0440d604c0c2d00001d00c2d1702c4c5181c06c0c1d001019036021311f12425210549400108041c00300c1c0d01ca031481809901003080601030744403100414040b40c0d2030043c900410182000281c0042d043c0b017200d1140350a10040d04960346007404100b4411101082c00c100000d441404010f80400b91151000400341 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 258242275 1250 258241025 258241043
    0xc070503031b15041a07020111070807061409030405060a1701090c020d0921021201050702280f0f020612070f09090c08010b0a0e280b070f0308071b 65
    0x20300c1e00c2d0b1900f0440480f610030100820481400009549a01e0000c8400b040c4555100c40b90385040049000d0080041000d08500e00041d0f80c42c2803110f404020300c04035005580c28055104e00851101e44194210f03015134843d0801c0c40180214035200c401404820b50514001105106071241586154401c0e07000c642c2f030701c0d562004c0c805032039014090454104450300304442514504011110140000c01c03075007400351600605c10086644195440d4100c0f89154000c002c940340045020356aa041c00310849400d660055810b0320001c85008541055a03001940c20084c1d402030b901d074100318280e08000c0780d100905107e824880004821841c1c41345045a450180704650007078060700d80da44541005440e03c0c140300b010130000d504940c0e60790444104041da0380d07441020400072560001011003956001210b06001e0401c20040b24000860b801e078900c10218280c0d0310b039548003061080400050650941280d8840800d001c3c06025500c1022400c01035401e0503d040058201c0c10358180403140748107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 258243525 1250 258242275 258242317
    0xa0e06060708040801140c070c091104350109050307020906150a121a010206191e05100909020109060e0301090209090115060f09051e0409050a1104090c0b0c07050303 73
    0x6c03135107010360300070107920358180c0303881e401c0e480309848282c090040011b00b58903800508003001c60b8108440003050580002d2240c08a08600c507464084500d10700c8161080520f506038601206109805c0c0d40c0d680000290300d00190b030750074001807040040159138840140c402000184446900803e5440385643d6003c9440e1840440c241c100c1d40440c00050001200803800001c0d660002411b940008105000c042110340da001110090412428580d240070144c0c00321501ca540301e60001030042c40d0002008c1036041d2a1301008007207451126006e800151204c4041100501903c0800c51460f00540007042d0f6085580108058050a61300e64141e40c1d91810543d40c00ca44034008000030300030314503000b0340ea60348114006203102554051036224071403401e40d86480c0f26584100c2d4110340e0700508140021081801c255031159103000042e03c030101c01e20082011440c05105450959620858901c000c0e818400320b11941c0d00142c02c03142d00b91040041c0030589075010400340032422580f00003d04456 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 258244775 1250 258243525 258243551
    0x140a1d0f0106081003020f040b04061e05030609070e0405010f0908121003020f12030714030705070f0b030c0d0906060314010f0216020d0203190f060e0c0a0e06060708040801 76
    0xc0c0164040c10401c21204140500003400003420340172203804031804c011018805001038010a021010781c3e80c4941340c02800a80008184040c00031102501c01d910302843e61002490b880306c00440d00e08040b43c10041c07041c44040c405030851034009024a00000d811460800d0100c225000c017201540c400700003040241c44000c142104030380c482c28030005400c0c054910340c049405400c0f00320030030f44984d50303802c0c6004040340b041050310207664110741c42800341c90550b00c4468a075840a241682d2901541d540131441d0517480541c403013103a0640e030003203203140c0e00d0490015042c0c01045e04420320329103031003110010551b00d01504004e54020300e013903122201c0d210040c0382119030641c0e07045400760060010f00350701c0b40140c1c0c600c0b20158056404050402c91880000d041207ca4031240901e803200c040e5075001d000c00900d072040c0711841810100103280c3c00130380703450ba40d00c60191180c0d44514040410300c10308044648443d000040a056941406240d5031200707901d401c0f9410401c01695202d4441c1200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 258246025 1250 258244775 258244801
    0xa0816020102070201090e181608150f1306061701060510030e031b0102040e070201020a1803050a02010c03031107080904050705090a031b0506270901050a140a1d 71
    0x205445000031403030b00b04240d0010344003074014401c1503646506400060302c90754401c1c0048400c00340384030540b0300140c00d60300703d118001041c0c02824036038840d90400c4165000300031420b9014a60344062101580d9400320b0180800f84050000c41c0e00c5078890100080c0120703000404403504582c0c00000c9284d5080201f407288040d482e5086008040c14800f1500750300b03030003004561120b2a44600c0f10700500c0c40d03404c200d000e403203642d02405400e00e10f00f0030881e200b41e0644c00782005000c1d81c0d0b200190881d00110250811220b400090881c0c0c000b11101d070010342c01600c00f256003610074103004c508a0301c044000a019040302e0026140040e0008000070107190a10540d5445083c03030a20b40d003030a00600110b000d900c0b56020007400301c54901000a1008510240c0c0b0700140001050399594200424012040c91415940781e400ca47c1035200584c024074100810314140d40003d8405103070740785802d4905c4000c6520521458018a50403404104510101c18071106482004013802c142d00300301c0400012 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 258247275 1250 258246025 258246061
    0x1a09180d1404050418020603010f090f020703080c09030709060b0703320a02032a01050a0b011b0303060e04061415030c0108191a0109050306250c06020a08 68
    0x800403540003280c0c81111800548040e00c00030390b000a81c00030f0032500468102400b92000e1f6000708040000600d480303c051001054444072030091050400d0382a00b002070b801606002000320380b8810003d421340d641907021b0314021400600301c4015030343c0d4090b04404c94841740c10031000ca0000043c404140740d04110603298140395452840e00000d0841d10b114012034500802e006214000a140c07104030f8405c00035202e152005a100c099800b01501940309440350a04511a06508002c000743c20000207110755181c528040e1030b100c4928080451052031183d41c0700f0300300d0a041d0f070360901059065022071200d2041d80b00d510009100708a4155042101000130f2007903448100071401e01c04a81c80200701c2c10445030081c241208c698841ea801446407100001505d14510301c1c1c2800502902034a25035005180b5080c1c80714004192948141900e41ca000c44410816422440d00b40200d0140302144401012940c42c119466105541e10007040c0d1340701c040392030b001404000502074401c000c45802d81c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 258248525 1250 258247275 258247277
    0xb04020d06032306160c05070305062a0307020c012a080a020c09010f0302090a06080d1e020c09010b0702040b090f0604110a170c0409021c0b1903061a09180d 69
    0xa00d107050302040a44480c40c5c4011010060706000030070030802e0800c00440590340c4581519028a01541c00c1500e2044501110f0b140c0341c10010382101c0c00c0300140449004603010703800740801002d441c006550314010074440f044c040d040c1d82400c41c505501440e243c00c401e803007100d078595241583d07007009180114040c003c1e84074038840001000820705500b00b10b0203da506444138445a629a0003004c000c225961210585020300c04041d00901c0e402603198040c640180c110030800c1d08110340880c4e0f10082c0d202c41c4c81d0403a80d000018000307000c01c1030140940910003400850307a00b602c2c10115580b904291070480c689440c042c18000b041c40e0901403010403080310b601c070b5420210310f00c3c4c00801c80b00410955038506840480815810b405440496000d80031006040d592855910040c0c1c5210000359002c13800d951810f84484018a40722003a0324101c0c0c10814050800350968070b59800510041407282c62440c143c445080c000d4881c00115803007030180c4e8403c403011141e01d01d0541d007000440d020001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 258249775 1250 258248525 258248533
    0xd050609010f15050403020406060203091002060610050c0304030222050108010203040b0402010f03200d0b0a081f06051c05060901140a0b0d0203010905011d07080d030b04020d060323 80
    0x70000600b120080e208030303058406031109071004900305540034852600040d4005040c0100440c1c00c5400000506081d00161100b0120b21103083e01282c0303c00007503420a030b02035100a0300c0369030f030b505c104007030003100d10f5076816030340b80569a0340001c40d2440c00602c60b441880140b242036004446610400f80101303403030002545180341c15694248200340041c00241885010f03041469402e1103070f40480d000100c4150300c482d2904104100100319040501504250390801402c0d520600384034020004a0380307034100800c0c0441c2e40c1001045440e400740050501c05941c1d8400140d55034a000c2280c0b0407045518003219a0805401d08501b8128020201c0343c1c10380c141a018622a68810ba20507400307000640000b0340d002c040800140000024207000e0b606609042000062100644c001540d801c0b00083c0e0414620704050400e80b5441d4600c101c1219030042c0c5910b14400c0c2c0290450030303081c04014401803034810b043c081c21003111015001519901051842c4841c61901c2075000401000301200030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 258251025 1250 258249775 258249779
    0x1810020304080622020d060e010b150904020c030d0501030807030305090a0c0512030424020d17040b060a1203020a110a050a05040e2407180b090108150303040801020d05060901 77
    0x100d43d104000350034084102c403440b140d600c480c4002d501c3e1030b0000d41c3c02800c4000c40c0e201824644080c0c01e08030769618081d4600104415180740401c0303490036a144a6989908004103101000000c2d003041c043c0500e680020080503003504501d1040b0343c007a5103d15a031b00d44032003e60130000c00301d030001840c80107103034422178240d40490b070807001d00300c1144d004544120300c40d0810102281180240d0780810811605942c034008012051585001b80078800e6089070032610080c10100d522141c2c2c2440500080283c101050200300c00120f11580901c002d440c1105072913071090301c0315110504c60019001604842c1003503041219403202c0e65800c40044070b140804604210000d2010640b62140328461540c41454444250041c405207503908a13000942c841c1540800c5074280094040706c0720740000311255040c03411181050700c800f09941651080a003041130040064907405005800300365042055000507105540400c0180080d118640000d41c4850030f2171050302c03da44002e482c16102302048001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 258252275 1250 258251025 258251039
    0x5190c0e100b031317040b040510081308090102010612050615120d0c0501060308280201051e06010e040608010605040605030c0d0f0602210411040b100c171810020304 73
    0x1544e0b004031804280131800c2c0350314900350030b00081d05001301080c0c2c80007041c0001c200f0082000b91044800540b008524030111900464805030f08503180d50740111507641c420701064000019100c0c030320060000181058554010000a00c2c01030b0040380c03a544807008201c81c2516a108661802c00c00f0f130348584002c010241c1450b00e4610602900d010805032440e82020f100d0250030150046d500120b807141e88031581c1e105410781c9061800700c818401e5002016920741c0d0b10510516128401c080c608206513050b0603480e4a04250140842c1d0400c04130440310b90712a0313210b119402c002c080c400b000041c4140b6040901c01590681ea01c041d105e5004400c01c2140741d01e502038944c11050780000012616035031450700300028043c042c5908042c1038280100e400b20032882c00c4050140780104603841801850340104010380d506072503529008030540c00301c04486802801c1350a5424410715110303031504c044070508070254100e90841c440110004040c62220300f00b8000b0b4a0f41d00c84036202452500c4c1c14188 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 258253525 1250 258252275 258252277
    0x1518070302060901050d1404080a090608101503020904050a2f1b0a06060807051e030a020402030a0b0306040506010f12080f070201090803030a0f0f15050d05190c0e100b 74
    0x1003c903040c440006443c4c03c0c40c1109901c4129590f889900a60460616003000c01a83e00003824200201e43d0f100e4010401c0da00481d010342c85840400c21203044141404d01130b081e460030f1030000c0000d0603028010fa03000350f6594052180b2600424400003070052414003005040641d0a208d03d10150500c8040c1c501c80965108442030b181c220b00140d800680d4400040c1c1c03502080e030070080c003d20314241c0046251140400e041d01151012a003042d80c1101d40e00c02843d0007110540040d925a005500f107074018141354002c0c5600150305c400c00116180c0c2c8201290401404840c110350507004a80144080c0c0441010360300034000010f05105a07440542c1d502ca420300c00c088082000c5003004c50b45a00b10381c85100b10401a0540c0c07001d881d2a81401c0e00c140c0041e0424000020174181808030001220201e403045000794890b6901c1d800880345404240601008145400e50340c40c090b1040500c07081031094075003044244a4104d080d107451410213084052a0003409040348103181c210200202e50400e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 258254775 1250 258253525 258253537
    0x3100b0f0a050108061018031a060a0b09010c03050d0609021c020702090106030902030a021002011a010f0c0303050a091718030604030801030b18071202041404170c010b03151807030206 81
    0x28a440d089140e941005030b602c082c8507c03440046182e0b141c1c01104011074502c01202c0003441002d10007282d1219410010301c5845030089483c1481c00b80104134803980704001c3d264a190080c10000d1504408480b008241c4c2d07815009807c0080d00050075101445410055005800d41c1c40011810b204047e400502c03460300600c51001055202c04852066603010300851250580c020b110342050919400003a0203050308100c60700140254842e41c441950140c10388a200b1581c2e03030340b00ca04009030740d0790a4005000141249a04a80c1c81c0c410708001009204510307203080c0c880e8480d645481c180b2500031a28920b4070b00650294004c80c00344800aa0009025810742c0c0d40044402c0d0550b035019030364032040c1800ca0030203015104030800080c0a210311104480f449000380d8050001174140a5600a03401c420741e00100301209290051603080341000244c100d4411610011036400e21401c00039240c07140440d055004150014244035500020f038241a030290380e04009002001c1c9103800180340c0340201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 258256025 1250 258254775 258254779
    0x1030201051b0f010f05160903210e13093c02030c090103110a120b060d05030c01091101030f05100501120f1401090c021c0e01030b03100b0f0a05010806 67
    0x24a00d402e85101007809290784a1520340001c001903104030083c540075180039511901102800c658502009100d2107600b02036035001580550300c200c8041c0c2e9164000d02c1d0701400b0341045a1320b0748154050341c44d070500c401c2d41d41e5015408905080b5504101a8411922004050341c80c900c0721a1525a54036840742c0a00c8240190360904052080c00803e05207045407406a500c141040004800c0240d04000061120300944c0c00010303864440d9451349101c55901710241a80c02d1b1500014558a400001c0b1903810381f082c03003980d090940000405080d10f0724410100c40e0514101c8106010796070500c6000300420500c0e03024019030078503074502d2411807124000e25041100305030002c40c8810060b04480310b403140841080144e40307407411030b82610010038011101c0e11400d1882e038501140c800170340031020b40b510b01c4800d800894004402e6440201c2d5201042c14540c4910500f03800342e5061000d010029901400850003c8e108806c11428400e041c00240c4100c014440a01c02d59078088400f5902c6202 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 258257275 1250 258256025 258256057
    0x80d05070c1a0c070f0606080d020c01020c1e030304062111070204090303060510090312020328030609020c0c0301110c030708030a1d150609010302010f0f090812040f0b030103020105 80
    0x42c0c800c403e80984107114024040400c40c0095108201440c0d1101045803614025074061010300c95040f070f15030140d1800140140e009600388045441c00b005034111036001c51115440812aa201007411500658417140101c2c2d6000b203100b0200180d468201c481600c40041009913004540380700035140104000640526a40e4030b07001c040501a50000c0d01800c402400040310b0341c29407500411007038860000300c0305000c058600301c00d05400002551400781c20510074421003034084c41c442100710030742d1900c002010303183ca100042150306840140520803401000d025044284420315094a2035500c4903038020f401004285200c8101209032014aa80854184c0da00d4480d040c01e1f00140c000076400320003401512100c1211000d0001d44120b00e0b212607100040b041d5a04010820a6002480302a01050016914411962240c3c001c0340c0345c13a107181003840610341c4a46100345041c240f6400004076220000301400b0341400102c02b0302c01000b40e02e08181c0f95606560000704a4018040d0800030040303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 258258525 1250 258257275 258257281
    0x506040f0b03150303180312070803010b1608040609030b070c0b01090b0102030c010606050a080901050603070306111303032c0f011b0b0c0301050a060206060f010e01030902060304080d05070c1a 85
    0xea091401640c3e4005040340c1e2141805c00b110070204094480241c46841407112101900440c4400d6030500c5030810005070460780782001c0049268003c0314825100d9140c100880005408030020703002804207540c0d00d102003815403070320343d0070350030094203030414000101441c0c0c0019480e078125034151000b254000c1803106c0c40e034006034614050000200501d5082040200e07440740d01c80c0241550310440d41e9440400d80754045054201c840544500e03800d41c00480c000d1001c18003a4212009442c05200310910340000c1c80940b0030845406d40044000680d4096080910340484c9103481c5c01c0a5000d0300403020480440005a501e880c90706c010f03060200d114500141550841c4800798401c0c0c0008100e5810f290003401107071a5402401a14415114940d001ca0120320011700c6034440c410207000c0d00602d250003030040d240e01003161007540c1010303119007850005890f020013850091b4801c0d0966500c910300540b0420170307034000401600400c031a8041c500c2c0860015500c121410b00740848080c0580c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 258259775 1250 258258525 258258541
    0x13090b060c030d020c060c2d070206070606080c0a080604122f011112040318050d03020109050105150303030705030907120f03080622020f0408010c180506040f0b03 72
    0x4000d6080c00c0d81140800705840f06031032602c0d0000d029092208041d60941d641c0c0e80003240b064001c2d4031051420560003e070f00701e90f041c81d0015100d40520554459400c048440d8000380080c1d00203e07040b00c40c56182c402c00c0010302c004116030030101c602200e00c1d2a41342c3c00c11820541d5000c00800207028210f0b65030585071914003c04004400804940020169402c000c0440f46a403072504201c910561a000c142c0841c440d05505403100005c5480315140c0d0b030748a81d00c084402000380c10000e031030643d004200042c00d0f84d41203007124296109400118607030426080403800c58400070a032601144440e1a100c3c1240e4010040700d85c044043d0030865100d0721004140e03450031030f085e00300c0704007010f40002d0303c418421701610703030780c60180700b035940740c40035541c000601c42c010a1808007400001a020035a450140c95500600080003852800c0ea0800e50740b0100300c1d087d54401d48000c1d0100b11801801f455840d8070b440210040d000a885c500e203001d140245000c04204076204d040c05590010010074900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 258261025 1250 258259775 258259777
    0x5060d241409060c04030c050f010905090108150c0307081f0e0c030402100201060e0c09010e0405040309051807020c04092118080c030318010903080d050109050a0213090b06 76
    0x10544080100215820340d0105581c01c10280e400e032003180315590018810070145000c9806482d40545404401482e1005001a20502600a5040c00070f6201701083c4c54503503c0c1030034007c041d90001441582069042d1804a41e000382000901c10410000c028445401602803500041000307030240010701d0002e1030a640a000b0f4004100c0300200301e0600040c00b980340003035801a0b000700e4100e54040f012003000c0e030885c1c07954403039942082e0b120400201c030300d5400e03806400c4216040c100341500011180000c0e04445040f1000c03400306041e40f005101a00344210786683c102d1413504400f5a900740440d010791f0b54503401c01d05502c121344a20350a420410521491794000250501e549803180c1c0c582c0000c0c060740f40d0320142c546401d00c030000c0000d80c81400280390381a004054059031034248000884911501040135281c14445029070000c002556000184192400441d0000d0b407541441c3c0c0c041c05444024000d0f04210740148281d1668100d04107100b000c9440e100000500030b42010042086 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 258262275 1250 258261025 258261083
    0x1b050c01200304090603030e0f0f130905060a0203040c0503070303080615040503031206010f0903111203090312120f010e0609041e0303090b160203030f13120e030d0305060d 76
    0x155010103e000902c41d54150032080690344240c840c0502c001c0c640042c0101c0841d2205443e070312100300c40496003d41000c20145444a610340c0780402c0f0740701642c44081c07400301c05903407010b00e41c2c2c0e0020801081c0b11041815030040d010071405042600d1450702c00400941c40600410b114080d550860425050f840c0c1c06c0310000c2c4006801c0e29244c2c1040b005e0040401011508913020541408020382c0061181807002c0c01e4940c0070b6000b0f0b8820440000b403095034001c0c011960300310701c002c01207512103940c10028200b04d603507041314a668410b8070300c0c440441ca10b00a04440000b003002030042c0a00300031000f800303030701c1041502e10b803881da41c860038240f00300e20001c0c1882c030740c0c0030320814070005059064100244180c018044214181c548071940401ca12859038940c005130024004940c90003983e00d06640c1002c0320ba1b071100f070400c000d51103c01d2452580d4903440046600200201c142d8201400317241590885800c0420480c80c0010205840021903007004111714103c0a0210502c01240c4014070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 258263525 1250 258262275 258262337
    0x30711070e0a0903170702070b210c041703190e0a0e13060e030c061305010e120c1c021c0207030c0806060a23040e0f1005071b050c01 59
    0x200c1d6040100c5908020600c4801c20790018940090148040d80883e020314042c0d150346d4000c2c210315103044c0ca40015600103981d619400b44603071503040c1d14407500e4580c060040e01d034580107981d250f2900e0030011140220f410355400c1c503001802442030314160034858110220071420316201c5501284c1c0052482c002c01d800c00e030040c450210038004000281c100c411101e42c403a20302045019203a1a09640e203000b2100943c1c8540c1c0581c002411188500b803148681c0ca21600c0042000d07081041082c0c140481c62030307203540810000c0f82c1c40c032426004200e0b1084030070082d66048141005018020340b502c10701c100c80c560b110407004070400424400c02c5000021034211520880554460400b00d460707440c2078403460301c5000ca080d0045038807011210000c003407c0351003400400c03c2d980102480058080552001414040c448002800f4601800040c8100206020011302807515540c003400540d51240e107100b85800c0c40c52048009903000a03094103c02d02400c00307104a04071344280350b803841c0b00070140075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 258264775 1250 258263525 258263549
    0x110d0818100c0315080a0203070b090d060e030d1b0207290304060209030d0f0504151209030c0605010803040608040b0604091202030c0c060711040905100903090305150c03071107 78
    0x1042d041d4594020081c4815658544000390740d42d900e09596403030b9042020350b1507000014100859068603006014040c0003138200008200c094403201c0c00c94030220a900c039540c00000f06030343c10900610502c8411884424134180c0c0c800d820740025650900b600038032a0071015854035403140c54901c14409009041b4100c104d5892609181c40750103034000e94607541c043c2c81a144140e103424040d05031204d919007940e95841c2400d21381180310f42c800481c0d011f04020702600380d00ea0045c5001c18058001000d0194172038050080640c5014022070b9816445445290802d001c14081030360f100c07442c1ca03081a0018034030902d684031000041c0003046141c100406004010000c1c003512900803000d09400070343e40042c0c40c840242403042c407080d0300c96088001e00b41fa07106110342c0210300c0c1c1a8056a02140140c04482d602403018500c002182c03c200402d40c0440c00743e030300403c04c003c02041a010102028000030440c0d0914481080c0b403404050a00703010b111803035001502c0d05000300403510013442d281d4100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 258266025 1250 258264775 258264791
    0x30c0a03050c0d0c0e1f120c0e10031a010912060902030f03120106090801051302010c15061d0105060f070209150a0e01180905030f130906060201050601110d081810 72
    0x14210100240c6140e00070001c906e64035010340b0704070921030380c40c41c07240c1c8501c0c0700f800300000b9030710050a01c40211028031900750403d404170341714030300c03202c07102e6a40761000074444000c0e4580c2d010441c90b103082ca07070412002d240b041c88280300004042c00d030399502500118140442d440007900742090a0051002c0c0d200c003141c1004041480032000d41243d4280e00c8407990320b81c44008042c281c8604445086154007041d68410044d4402c24451014500a841c0445c0200d0310a80c020700307885203648040541d0b0f4203810803101544024481900505003196000e18150b041d4840c2c0c0c1040c0030b40107010740310340c03052400582c10799910f640701c05c40014014403540d0103545031030640350004002c0c0199800d04c02c031121a0386449080c0d02c070b00051aa0040c00441c2000c49900114000d5400900001c0f15091090000582e611032402410068140e680001c0f6461400c10001441c800d000b12104596502400c0c0c614907150308501c51507045245500b00042020428145034a02400f40d1810341c6101d00c3d041003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 258267275 1250 258266025 258266027
    0xb0301020c03090a0801110304121101050103061b081003020f180f010e1f15030207150504110a120305030a09020603150a050102010c140705070e0103030f14030c0a03050c0d0c 77
    0x10804070f83c003100e10b41c1440e62600451400c03100340580080000c1c9040001c80c0208515524072020044680741244018100c02045825518280c1c001c42d0155149d414440000c50b03510401d100f8018146000ea6182c5044210103168802c075200c060f00400c0001e03110081601c40440c4010f0901900c42c1c205081c2c18451111030100300b00744280c030250701e980404620480441d0f40b051510f00c80c003c181d02c80441c00c00208200203500e10460a052542c02c02040c0c0005010f82e002e41d0805028080c0003d051901342440180c800400c1070252050f80e002d0401e10035800b41d000008042e03a0503181ca07585035a903035400ce0b0000c1c21000800380d400080070040140507144e40c00c100c212040c0503140329001d107a0b600f0040e070a85030101d6901001ca0200c008013148d1404640103403a40390b010300103e13000f0700c4d503030b05141070144400e8000760b0000c0c0046032a0300034103400032101da00d01c5608101440c65071615030f41c050114000c03400004105a02c0360003045088442174244c8880301400c080400c00ba28900030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 258268525 1250 258267275 258267277
    0x10603170d060501170a0507200a05160303050a0e0109030b090303091203060d060e24010e01240e010903062c03040608010b0a05040801020a0807030b03010c120f0b0301020c03 77
    0x701003049820208041000e51041720702c054005105610000076484442d6a2000307840c0081994040120040000b12002c004000c030442c14240000907000512040c10200e040c510801515150904005810000254064101c80c0a520503140030741e4200a000012120f840240c0c1c005000780241005202a4620210045000b031000500b16889400b01a183d03010f00d02040701c02c658000055485540482e0f500d41000701d132a40010155144214001001c6002805101d004248011540018030007241d00004103405013100041c0b07265a41c6211200300003841c0346038120010040c0b240c0603a40c44c0c1e4041c1e1000d902440d40207400344280e54440316a4103400e40c840150186405030031040402d01403011089800303139092607682c040076038200010b2920a5002d18040010007504220028103840c080c0b01411141c004c61303858002078100b43c1c0004007569a900043c0e4801d9260003480c05031a60800318076a0f006402c048045620400d91900300001d0070300341203048d015400055410300c03c004c048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 258269775 1250 258268525 258268537
    0x6090b070503040e0a06090e121806070803100e0f090a151805030c0c0613050d0312020c060609010506190f03060815010314060702060f220302060f0c0909010909020301060317 77
    0x4000c20190049580c10759851000726027500c9900c50400031160300030045076603d0070052001d0310182c40c0440b0f966a10916034802c690000856a00a006005c0442170f03d1900d03800040c600080c49040c02c00350080354039001808001000d031080c0c52030407407001001c2d40000c048480280c0044400441908100e070712a030100c020b80c600d9001d050392510140c0780084c02d80741c203510742d02c0e49171f41c003141450248800581a0300041e02441190f0210000c00080341c002000700481d014043c00450802005110b00407406820184c8240342c00e004085100c004c011260b40795010038500180080ca1040e07003900100066002000e50f40a80610b088225101c81c80943c1203a1217251050311724440300c2001c544980d410b440080058110380041000d4804503640c40342c1181d440100440402c1070000ca010420b41e800e44120056017000040003420f0303501341046075120011440c00e0b8500b60100b00054142034050041d40019a42c0b034840c4801e645007580b02d070010b1039008402014030202c0c2c010bd102c2a400c44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 258271025 1250 258269775 258269789
    0xb0a050a09020d060501061b03050f0c1501240e030606011d0324060102010902010903030f14160311010c0e0d050a080a211125120f030f0606090b070503040e0a06 71
    0x108d8050703401f0f500f020101c0425011b0f6903440c103105000398416815031000100340c000344202845000c43d0051008018000d04000048540f200100c1d502642a1b40c5510031210500043e0f01150100c1d03180441d00d0742d888402440c0015071410a0082080302d41000000039402d4810420070002c01c900c3e0b8a003400d02144850f130401400e0782d55034012030030781da01d580d0024002007081d075007080001d0003200504003001c2c1c070b4100100820030500e02c0c03015a030004007066101c0b030f0b044d404843c24150040f60000005412034002d02c0841090040945680324002c445401049003c0704002484400e00c004900c0d15030100c145035403185001001009820840c0541004030f007640750444003614207204041c0c3c0b120400034241d0a1011320245455000941c40c11184401490b40d0100300141c000c086010600c9681d0703e07020200c0309a200000c045034000c400b00e0714607134501601440350640003032405040301c0024080b10395941c81883c0050650040e540b02c0110303580a0014090f2884058020070259065 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 258272275 1250 258271025 258271037
    0x13050c070605060a1a0f0f07030e040b042d020c03070303050f0901050108070504050414100f0612050a0b0907090c0210111810020c0d0812090a0b0a050a09020d06050106 74
    0x108800c12140343c1e405e02c62541c010828030201800800000041d000c0300d19000c420500380342001d405c540159000b0401100040c40b05801c1690503e011701c95071090203c2650100803010114504104004d1010f80c1d2004074500700100040c8503d050701100d5403c20305c0000d4030348a01c0e075450060049d0a064445c84412600c600014140100510400b81240c140c44004c0c0000c91038034007440001c10024205452008100030150342c1960204170050480303010307180009115407071070039400442d81250844088505198a040040b420000d151032849820102030203841e107843c0c014a181052541c00014602d0401030000f81058000c02d008401e00184031050104682400d0500124031500300c4000010640000501480c20f007841c1c513038000d50340360041300e80c000d21000008681030380c05401250f40c80000107100400c5220350b103825410406c900e00030308011203990b50312803002c60014205c0c004240d0340c400003008880c4a800903003050b03402410188210030181007810281809004450104d04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 258273381 1106 258272275 258272281
    0xa090617310b16020d080c09240309120313030e010207180b030f0d020d050304080904020d05040c1a040302090c0d1107030e0a0f090b13050c070605 65
    0x40162400d030b50b1482e00c07a03070a5640340a58241d640443d0091442801c641d90030100071a0010441c4034025100c10600e000724014005162441c0c080803031043d19001c01140c01c90086000e0f01c014010b582c0f007810000d820340d02a200c141c602001c440c41c601445400311740f1640101c155480305105039030348140d0300e00302c081c0b0340d152454032522025a2000d010600d490100f0100381804411405402c05512880003e5110812a02c954082c05400030002d0304000640c0c08030f45a024004004540f5092444030b810000e120880d0100d80654607958085844001840d059500c1c40c8200002031406055509011840902600d403203200c031001d00805d540e90070700d801144a40c1e259403507219102c1c01d4a0034000e00744031940701c400303009100c00360f801c2c07000e14201c0314040d0a80b41e2400f80841d0038504840818007415600340340f0100180f4003824405904c0d1164020320f0054010b08051145407 = true := by decide +kernel

theorem cover : BRFrame.Cov 258093525 258273381 := by
  have h0 := BRFrame.cov_init 258093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 258093525 ≤ n) (h2 : n < 258273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
