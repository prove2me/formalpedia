-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1397
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:46:26.654059+00:00
-- url     : https://prove2.me/submissions/33217684-6599-49bd-9e0c-93c7e1e3c92d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 251079136 ≤ n < 251258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 251080386 1250 251079136 251079139
    0x6030109030f081315140112050d0c0201120e0a0606060e1309081902060703061403031207030b0411031603060501140903122808091902030c100c050705 67
    0x1085000e800003a0060382080380c40a1a0404441c180e40d40c40c400d1a418459030b0300588003124a01e10419400740c0360b4042d041398040d0f0400c84140d40d8071403200507003030703980c11000400d40d0f4000ca20581116000d0124007020b1403052500021004032a0703001c100ba2200504001c1e00b170380c0210403c0c005c0000901621000d401f031440c10507240e0b185c500018196100c02d00c40c05450954030400d40082c041100c0031502c818100d5200d12030081c5180500954034801101c03584006494150080340701c0070098105020204010000d40c140702c604260702001c058060640c40a00d50382e1103030049251a54015101c204d4043c15032140c492806401090482d92281d03448400c0603d002000d1209a03040000401c0d030880b856505910f1f407402801003031401c0350f101950b090904020030b0981d00d40300005031614800d03140c811090000c08804078151155103068802c00400d8201b02e40748a00f03045444d03101c04005000400b1640340442c002c0100301881201244080015451401c40c6e0a0081c1003140c040140030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 251081636 1250 251080386 251080391
    0xb180c13091e180809130e030307030509210a03060807080307060506040e070e07050702060d05090d02061005040e070902120f1b03061c020312090a0e010f0302040e07030803070512060301 82
    0xc0071884500b407030081c0401442c680c40800e007000e041d269408020300905201b0000c0005040c28440d5070355a0b0021070f0140002810a00001c40780600400c1040741c00d09075040d00d01c0b840200315a4489035803c00101c1d01d042540d00e190028040d80f042008200030002d104c007039550b0700c101e810154142c400c02841c070b5010f5800d080b502501c80c60000b400c0400c5075152102d02c0300d0b940740c2c804c1c2210b5034410900d0103580020045040c0d624509103501c0705010344042d41c1103d09002c542c0c20300b41d844410440d0581c001100c02003040016003000c1c3c009e00b031107140309426601c4580d00c40c0d011004036088680d110103020769000402c881070310f00b0300500b07802090310368004120b20b001341c20198070791000601c0540a8028908404c0303000542c032124591066008060303a020064078a07140d6129002144614410403210400142404020880b281641c07150a0102c0391642103400313010150002c1d0300c0505152158001c0000441d07458000b072340c094080c030744d1130316514040c42c0341607004c00340f014040a10991 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 251082886 1250 251081636 251081651
    0x1306080111031302060c0a080d02042d09051005060403110f19030305090a03050a0f030807050a141e0c0606010e040e0a0204050901060801060806100602010b180c13091e 74
    0x95205034004030f6142c0c11100c059445000c469100d0406000c000000c0050b503011451407250b00d5a50007420507914400452440501880c101001c0c0030030141d50f6888a0844c4030061042c56020b8209980c807a442d80c4140c0740b883c1d40c070004219513a002d0790040d81e401d50742c55094142d42c03811a8642e890400d04a602280d110011420320341000c949200003801e00200240103c04e60301c8000c80b000007150080c0c02d40d841c0340d0003410481440c0507101004ca00103090f00c400903600c00c2c019000d540d1140300d60f076603100c00d0312400307814580140d008202c84603442030161034851314182902d00420a8044090260039117040050015084482d26400e485c4035604001001031010b4000a0a00650b601214081810340b19245820b004004540190074903500b231031000704038210005080e90007180c409044c201e0071075a40400b02e0880c0c0600411940c82483c03d151900007081c005022030300902000c403028075280400c8035003220b980095001d1040143c84e40d40e03069025046c03106803c10b64544940030310490 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 251084136 1250 251082886 251082901
    0xd0606020a02060322140102070b0c0c030715021909080607080c0a0e04200406170f070c0303181a0912040b0c01090204050a0e2109120c130608011103 66
    0x44c00f0041c000d4200401210103800f0030354085c4151766a9a80040041982d1050520228042d511008040d100850300c0d101064800b94140d044540c0e050008000d513050118980d940030326130700554000340401e030302406000040c05084125403c1c40c807103a1100d00b485440e0481550426000811100a1004550401070400d100c00e0446a10640502e4414a04805440090000c003c1d80d4482c8504d9500c0d60380244c4114000d1008106032800c60f200c0c018800400880e900104400f110710000d200b11200100315880d0140303136100603241c46420040b40c02c0c2141034080d0019103d00100b40c40688820b500411125a031404a54021032081d002c0c1200e12000355043d08948280e201d00b02c9011400070340718000400a50040c201568004d105204030304000700b04202505010030100103e0040003480709103052040341c3c00c0100c002c84140741d41401d000c0c8041018107a1990102c070304d41e0081c41e000200c00ea80d035441c82d511140707034030600203080c9007061059400c54605002503c3c20860030014407000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 251085386 1250 251084136 251084149
    0xa120e06010501030b031509010e010b060702030a3905011202210a0f0e0c010207150e06130306050f0907050406060905060304050316030f0806090402090a1a0d06020d0606020a02 78
    0x54030b001307003408030710700d00100c0100b40303000280c100307442c201d0603140c041c40001541034101e20320b84000c400c000c1c411500d24904100c501d2041600c001d605620030001e000014400340d2204200703160651640140d14100b110120100001c10840d07100e60008181c140f100d50303041410084280101031045081034442c102503031000c81c0303082c5e6078180d0700520720014008140c3c9030085100803000c1d002c14090341c840242c0701c3d40e40302026000c080c09030040201c0425200240c02c05800d41800d00e5861145003048401802015409181c4003a00041d4144011010900d240140350287e0384020010425141025940781041c08580200d48100c0c1040810040c556200c0d00e610180c4808881c020b03601d80b910328003a40386200350142c01c5d1a544801801d1070515800c02240e22105174140c445119a503210403c108902d00101c5000b90700c1811100800d4550081d42d00c009200d03031244a0300364180381c002c0d002070b14280040700c040b91190340014ad601176550345406044020700b410300041200c00455800500c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 251086636 1250 251085386 251085389
    0x16030812090c04020c010b030d080f07030b030c060313060b090c040605090316060801031202070b030a0915110903100506030a08160803010905091603050d0e130f020a120e0601 77
    0x8009400407405418050155030560140240300310341d500c2c1c0c2001c11074042c0600e6280b40e88079009240b01c080da824003400c43c3c20720a41e40d4040c4195140c0e0780f032900b50028184800c0080d050307ca42218035400e9256280150f02230700300e03a0084402c6940310b00d040003d03240c103111141e02a1900805108034104000c05803400d442c580e040c400e071a1044480880e00e0507104048035010282d000d00d0004450350082c40150589000d96801c00c02c04200800603039840c203451151001c1d07000704000065072088250300c0206028070031100d8100bc1203005280c40240c0360342c1c51000c01e042000054540300c514042022150400024000344018641300e00043c2d200c01c22500090160b440c0010700340440486114040101c0703900209998403541c40e07094240c0144012602600d0b28032404440c040a4140301d03042c4411254010010850b5146105080b5124204100d0203608001c0c00703845120003140341c0c01054503280c42e1100058860b14007030350080250754406002c1c107200385081e8140300e0b0190042030003070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 251087886 1250 251086636 251086657
    0x21050309040c03110d1b021b2107171509060417040905190b01110a03110304080708010b150301120602090a0b030702010c0f050c0714030c0a0f08160308 67
    0x2e12460400c019030181644200310382c0c60440004403001c0707001032036102c00040385101c1541d801e60614003c050380c3d034000b00781e00c6880320030814402d41114030b4035180c01042490391700343e04802d1090742c40e540d519140007a0841106c000c0040d030b655500302c10030030040c0303030103422007000b12001d051014900f03450f8070020700003406071441c0035442c40040690008940081c52110410407503454295408100d2102088061444606248200006610a405031000a80d58001401c00885160340582c7d2000c000d50101c4802d0005000008103201d0503c500d000601105001003000c101020804c8414403031a1203200c10503105200612620070700300c40740e203140b5500c1800166564040d02c00501000e14030b60081800c0c07400002000180c0c4d6041d001400c001c41551107a0f004100403400c00d407040d01514421480c0c0344c3c8180b03000c001c00a0103180c10043d854001e016a4894480180410071411080c0c12034001d8240e40344080040010070000704920781c5541542c90394071411030703940d04183d226906042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 251089136 1250 251087886 251087891
    0x1030c0e0609010c0b0901151403030d090311070e010812250302012d0c09060c0f17070803090706031e0f060519030512071109090321012105030904 65
    0x51035070384d010700c5070b0848103604400c22210360f1501101842c06803240070007610984910010004482203409030b071000d00c5074001c01441c14603804160800007414005402d400b00710726480081c0e03807003600707203c0c4001070007440b84111015810403907142c0c60f0811040901d81c11010822190854054607180e8001a1250080044a0010908049000d07042a500003458040560040c0320318080c1d00c492030300d046042070020b000c441881d01e400e41d18003d5511030600402c48507041d01c4001001454a400b943e44610141140d140e00e40041303440c00e03040104201c522031400401e00411601c00c0014000422403441e00744224600003208001c5624005540040b80d603d44460340c1403800b15170080d8000d000081c0403040d0710552070268081e27844051000740c0c0c0354000d4041a610014807101201d070348941040e64481d13092043c2c0140b01c0010001420b014817800203202d000c203030242c0040d03050b0b01c566074207501d40310a50419040c5008a054a041c03442800c091014802c00140f021042e2103588a089600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 251090386 1250 251089136 251089147
    0x1212040209040c0b030a0b040c0e011407021503040305030603070f120b04060f09030905040b09010302150a02030c0115090b0108040b15061b06011a0c070b25120e01030c0e06 76
    0x48844446500440c0450b080071040010090447d4842071904070b0846040c01055090901034844070b0000c03d044e030009203208000c2c02d5a40c1204010200c0b01e20240000c00a007c0908031300e820b0360800c0e101140007440020a000c070030300e020000352003e044100081c0b60090300d080e500402c14010601c001f4040140080010140030580d0320515544070340074030a00080c401890014201034050003224450780c07528503c05014105011000d058950282c4034001041c0b6031044900d85401c001070600031440100322824000c0d0082c040c0e445801c010003040102c160030582c03807006a40800c6100c90402001400300300200f00064440c0390083c1c5030850385905c00ca6408081010f40c1310359805031221095184039260b84920000304607041f0340000e005200784a076038031070340e51481c4540f0f00030540551086005120404020000b04031074401182c0c4240c2c04001040c0200351807034050b4080c0d5562a0755a0f15040103900004031140c40304013440c0030049410241d50240c900e06207004594042c9030089031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 251091636 1250 251090386 251090393
    0x103060b011112160327080f0d0c060b04020f04031506062f01060b0c0f070608100303141209060405010b0102031309050402060403050303010b130515180f09011502121204020904 78
    0x3c801021401c1d403000200349150380043c040046e6080d1150303006600c18000c00c031880010118007045007404507500d8442015250701d5610190884e010010743c8640e08100d0b000b007944814004000030b510070311340c012243d500c940c0c00750110b81d090b038003100038400310310025280041044004d018940158600c4c61500085025143c01061705801140c407100300010310400b50000007c03007000110300d2104840d107068071058210b800075000e4070070f52400034a500e41400001c0c003e0480442c005120001c260501c2e48072002041c111500390b82481e40340d04034a05103c1400b0084c000d0700e05001c028002945041c00c601c0400350500c2003482021903041c2da4101107000c555a0744110f038021500002101d490b941c54442081c41079101030317140000c1c25900a4001164102170614607040000210700b2820b00c14100c2510b803030444c0303100c015030b0b00011704070f1407440690b259600280680810000300f84040a03826010b4a8214400e12400f40a481808444204c214009810303910980c180c9400c0442e2301c8903c1e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 251092886 1250 251091636 251091647
    0x203090a020a0b090405011508010b1b100e0d0329040207060207080c1b0109090f09171309020702030a2901080604030e220c09030206030103060b0111121603 69
    0x24002c0d400300e54020b00040d1002042c0281980c20012a001c02090760b841c0c00700750f011030129003d240440c2045004100211644001e80403000c0c10700c07680041d21500b50055804c1900007000311844c00e07903409856080f10710030402201c61642c1410200a01407111441d08440fa044a81050070750002558028140d1510b40603902a240d010b0410741d1a9109490034603000d0700154014202e911070321102c00703000000d40054524003001a100c07400440e0400f0000005030400c0d486942c185074076171070501e002484490788540c0c003400704084c040e00e44142e085218400d50040c0d01c0b00810a0040c813a00016a4020807040400780d0301103950050030f01d4911956841542050001841c50208400040d4130000072607003034480c6201e9501d840ca20000c00d81000a02d88806000e00c003004d13180c40100e1900d00090b40504039044841c100107040d42c1d5a41c4c00159141c0c000d802c105c44203038407001c41e8241035030022800c4845c0b5080b40d003d8030640c41842c030a040640140f0140914a40350100c0e88800d03d400384 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 251094136 1250 251092886 251092903
    0xb01120c030e24060102060f0a05061507060e060903090f040203040302010b13020306010f08070c0b040203030f07050309030c0604030308070e0a15030203040b0c03090d08041b0e0403020d1403010603020309 90
    0x40b402ea0751041008001901c0a0700c044041c0c10582c8000000a25190300c040341092182401300c40c021030946400580d58010135005101540140c0c5e45105001088403150150080500c100301c007041412104620504001025069142c00e0340284880007880d5501c1025450200040e540143c45e69104e040817030240601480c882d8014a00c114544032480caa50004c6208500a888206050074402d60445554804481c14400107008025140c0040c40b4a09015007150008007224102480421a4001940440750440e0380e54800105140c96080520040c03040f10000c503155401c1a1031030710050040100100728a0811003101e028000302e5a465100300c01400d041030150801a2074140e001d0000c2d4001d80d403d44e040103007100010a011603000440784110700d0540541001104108143c1c1d041001520403031380c1c039290640038281e8214410403203005000e60491301c407031402c00703007070181c1400042c01641e42001503404040d00444c40e84011241152507030b00d001681c983d203105003142800c400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 251095386 1250 251094136 251094161
    0xe03070b190c120c0906080f0403030f020f040f0b0901050a050a0c0c090903120b1c0201030902030303091c05040e0f0402041b080106090b19031e0504080a120b01120c03 74
    0x242102140e480d5840780d140f800241c04100104000c1039091030507a83c42c441481824000f41c010000118074600444038a50418800d0074041204003034540715800742c2c0c02454400c0704034180800c0c10030030306980c80203c10060a44244d41c0b860302000000081c031901c02d028607042800303400101c0048541c40b50350801140340e0080034041001707444160101c058007581c4025000941507082d00d1282da81944614148904020000d00307000c60142c0c0050f8806091010507030500d6038425503540542c8050000b54880d8207400060100442c14003200043d40c47d0745031601c420010107200c144212415541030580280c02c2e0725a844d00c5136190320000300030b0100d101c500701c421205139140350000c0b40c000c21800e050390629241c2d00c8106498a142010328011060424207042c0c404101d00a43d5000354000b80384d1604078404c490446086800c88420342d6030684084500000c00108829903692000c140316400403110b80034030806040070b000034041c0c2070074a42f45d103080d643c400102c003000d8042d80c090400301c0b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 251096636 1250 251095386 251095391
    0x60703170408211e090c0402041706090d0903061d03130f05100e040b061e0405090f0106020a0b070306080d03020319060f0b0903120d0911040e03070b19 67
    0x10a8030b0005007541100c5102d0b00c40c02d45030b60791182e512058408082c0700b42018002098440c0082e000c1c00b000b484003030501d040300e004800500990b903c40c1c0c0000e002a01c0c0c00268216104448460189880b00c0206641d005400080848150030741c403901d90400c80360403e2010400d211000100d4a841e05258660000b1740f02c00030305614056080114181100e2b42e031010002141d030b640b82807000c4d00541c1e10081002030409160b080c224070b080d5005200500c1d010748983d00300f070080071700d080c0405a0100c01a10440f8003240c1003080d0300c0c202103910ba00009401c1e02c40e299505d40400a0369990010600600100d4014000703034505110743c1c0840b004009400444444003048100500290b0003512041c08074049003100c0000030417607000e80c50854a250b01004441032412441c50216000326078500d82c5409804001c0e2900085030002c0e0488140409002070001c034280762200c101c0500140c42c42c0264142103121010350404000d40d00d54039003081078481d02e69104842c48088038842c203881c405191 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 251097886 1250 251096636 251096641
    0xd0912020105010e070c0303020d0207051515040219080601120c030e06010803040303020309062805040501110f0712031205070801030c0f0f050103020c0a050709020309121806070317 80
    0x85010040568505034000700315590301c800300b00040358801c0311808042640d803060326002901c82c1d07004200251245030014204034840d52a2410100c60450322155000c0703c0c0180000720244503c803410f501e80c1140e08515002c001300f002117600d00401166020700203c0c00020311982d0055501aa200b04512010400401c280c40c0190040c8440c14402c1c0d1140300c0c4000210b07082c600001145c2c156500341e0010342c2012120410450164018070980c407410428401541002e11008403103540400f4a4403015111800c01c0001041e015110b078010790103501401c01106184004a40c170b40c1030354202084100446124101550f902c3c040c5403103032035203030329140400074807a60000110b03042c0c0b40710310030010719941d60340a15505a000c500a000b840041d180e0f08205c598000d9000300000b015040565041d4000b645401e820034000e5170180f04c40307940001c02c2101d003c40c01d00c0100d108031041c0760307417605068007103200d80456140c2c00d49250240600023440c1c81414090340606101c00c240030328012062 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 251099136 1250 251097886 251097893
    0xc0a08010e0c0303270a09051014010f09060f0507080f0309010e03041409040215030a06030c08010c1b020a03020907030e1507050306040906020421021e1c080d09 71
    0xc003658003030031406000b0481407905503c3e01004540780c0c40c020038494122102000a00e462203440340b00034076170014060200007030160050240b980300c2c440c07a00b0045a200e1820754490160080012a40d04015000820301121030b04100c0c20420b685807840c103001c11a112020641c2c591040350005410304e240401c21030ba01c2800280254031071365842000348903a00032040b9482c3e4134000c901840201c0068030342d80c900c9a00300b10100a80c014002002041103070b8101150750301c6540140c8400115580307411007481400100c4054000800c0070070000c01400807002e0740105000c42d01031040750744249038400341083d542c0d0a81600701035900104544150304000c000580206154640700e8024003c9000001c0789061400006100e0119520b072645141d84282c1000010f0800142c1102c08070350910000c11900d0a00002c0017201400e94545000d810803401044036088944a40d401e900703c22814028840d201d00300c041c5e400394800c3c100649802c525103000b1040d80603500c504d03c001443c02e40144e091 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 251100386 1250 251099136 251099141
    0x3080304050d091511030d0513050609070f0512010f05130c1d0109020d0917040302192402030904050c0712141603020a02060d0212070c0f03050c0c0a0801 68
    0x19074491022a00e000b94002d10035a0f220307000c1e00c9030920003c0d0900e00c113102540203026024407400b91406807450121081400c00494606a4090002c11280c4564904029003000040d400503c01001068051300c0d00d2039402500c0f0190160501070300c01c119124035080f0f425001200341000d01c400038803243c98039940d16424a06200003c1e20303c4d03000464005110b0400c48803500075148009015000e82c0e081407104e4010758402001507034466920804000400d8005400800383d605000c9681e550b14958010080d5014810003101c40300500f503142000980c1a10b070801c443c03c19845003615540d14062005d90940c05003d03080c5810500380810018030f8950a4020000c442c410082141090b2590b401107403204081d124170300072584100501812414060344040c91035200c2c0c030446400c016140d01003003840d0800c0c03465042c00e85c0c0104040c02503c491355000c80e40000c491034540c205c4a0b030b9403123510740240c20404c00340512030300140d1546041002d100ca0400d02d00f0117040948500ea550364802d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 251101636 1250 251100386 251100391
    0x9060f06331201093b0601091d01151e08030c01050402010306060c0209010b09240c0d02160303030f0204231e0108010e0603010e3301030209041b05030304030803 71
    0xb2a02d685000401d00d00414420002590b01024410b00c003040c2e1512075201e600003100c01c0d500502140422944807000c10413205001c0c2009002c00305076600c860030b841d0850404400c0822041e4149001920020254139181c3c0c1100c040340c1107170600d100b05d42c162400f080415080352100380400592110150015000940164400e917802c200003503441e90211502780000d0002507101203440010022020868007820030048004c04001802c1c2d403010080400710b509056003244a140840d81d00013000b4240200c0c1c010b424140090405202d49445d10300410300c1c240401000e07d5a10401d650201c122941607a026080c0c1c18841c0b0050700f5070100c503801d8540245103151144c810140828010002204029003200041c0c58418107642001403070f04002400404c1d9582644d42e603090007140301010407001850a44003155890040501c8401c808507010800d0b00c00d90310440703a401080182c132030381c000b55800360300842040e0400c4003221001c550741005610ac668580b001050100500948100450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 251102886 1250 251101636 251101657
    0x90603072102040b0a08041407080a140c0105070813090501060519050406140d0f02032e060c031808240f01080a17090411030f09060f0633 61
    0x140074031410310754003a80b0690207020f00d9072005004140c032642c080e04100c0c1c1c11038801d182aa1000d102504082c2c500701240e40155107070741c401045e210030301c006d4046180030001c0e490086c0201141c18030028083e03100d0010014641c4030300161800601d140791342e400c40580a610002e01c119651100010919000340302080c583c04002140b050010b0302800c102c40c1114102d488415840c45a40c01703d03401031704200703109103810b5280c41c0c000740600d2040c8000c41c410300d1044151124604420780104545455800c3d02d10100070f140c8c010702c2915000048400c4050307140c40c1c400d40c460551007810400c00c2107035118000500c42c20750184c01000d452403004403c40d070480691001a1303144070105074a10300c00c0c800e00f500380d0050031800d80895102c1c00340d118000c41e540001c030b1401100e0004a41103136513005100010103404424060045e101100b0150004d412000030302541c10511081510f00318081d00d2070744680104d001c003503031140703010101d04281c40761145d902250b81c20781100311206501c070003c200c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 251104136 1250 251102886 251102927
    0xa0606031503020108130303240611030301030b0c031e0901020a02010b0114040608040503040f080703020406150e090702120d0504020a17030f03070903051603020307050406050f040b0609060307 85
    0x202146801c100d40e410881c0d80582d0b03143c43c0c0b621307680b00c8405162269802a01050340f83c3c0300010f80c071904011b40c04400f44030030316403803101d83c9440c0700100030700d02c45c020702c06c01500704000400100b0300c00794519800419100c820303a900e480d0705600c0390281405020410941c04800704000c1c08190660103486c40c6011900280b1080402c04011900385494181d0322076010403d210502c8010302c5043c0c0315510500c50001c680c0740548403502100320401503032008825a209480030301c210300f054002c0c00c0092241c641d20781030118000c50701801e280300f02001c1c0c6002d130404c840091456031081140300c00e808000c9000c240e82c0c40d1354200b800c01a00c2f040314180c0c050100b95000280003026402442000c060304400345061894916071030803241d1000e000c4504104801c5000f0010440c01d000380000c500d96400010002403030b5105040c101042c40d48605c0c49246410740401c002d81380c0c5500f0704070a0b40d0842c0c001480540d242d0026501d0701409100c56000344020041059654004d000345035008815560b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 251105386 1250 251104136 251104151
    0x90605040213120302190510110c0606010f140a03061a0408100903020705060c060f060102031e0c01090b041203110f09090403091e14060705070e0a0f02030a060603 72
    0x500c4264070a40718902e920b025100e40410400c40072201140c1035a00c0381c41a00c100c14a5000d81074011780881b10156981d8100004480c0d0f00c07071203440b0794030091840b002c006084c21010211903071950001420141482132452441c40c00f07038400c1c001c03804241e0050702c0b019150b81c19150001c7c0200b41c18012107a50840c4a41e030b10300400e51000c1038a04440002c2c00900000140300b0042025051500341141507200d6860041166600e9101030125103000c0d60041c8018580300c00c150304090405070100c0c2c1590420410140c50f81c40c0070949400c07254201c800c42e55100114800c143c014000d5490280c071445421048c0010004400b14040074801c0c0e9a80134030000340004c400c161140714804a559400310200070790305890908141e05a0700600a0a0880c0b82540d120800c3e110076038003011104640c005264140142c410400c0301c4c281c40c010546009040c03101036942c0e07075507031005406618030400d01e05000410103602600709114103000d083c400c2d500c80c2019202640034002034040c80b008039040c02c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 251106636 1250 251105386 251105389
    0x20a0b07121a0a180902090a0c02100c02030910020708030a0e0102060c25020105120708060a0f03020a0e090f070b0a030f090203100b0316030b011a0f030a1e0c0306090605 75
    0x40c11141c00e10010550f410f030703d1804d0042c1551070a811980c00055480d600108090703603440b1402841520380305000b180240401c2002828507400404811806241c104a20032290380023065500e9400140c58100a02840c04410781c03400b0303c16030114505100010303036072080990088100c3c44400342a022994507488403059001d6a00034a45042d504030b4a911480e1201c103a080c5800c0007072030040c100246001420501c0d180c801c8011128200411148400c3c004241804000311000b460301c4c0442e4140e1606541c001070782400107110ba450302045070340115030814828801254068044000c90312007558030722502c015034015001c620b000c00c0c54021010100e824a01680c88002c1c0d008000e00b07119504038040000a101000c078a6405118030710940c441c4100b0f02c00000e0146000b256940c143c1d40c980b10140001102e207400c140903e28080c0410013900740d81d4003c1da034201c07103e07403004078620440450480b940311414441d6400c440c1003800603445030b40c05a1041c403e44058580c1270040d00d84490 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 251107886 1250 251106636 251106671
    0x1915050a061b03050d0e030a030b1302070b0406050901150603060f0f06121116062c030313050c06040b0c100e0a0305030c1201240924020a0b0712 64
    0x165100c84112050314580d0010f403050b002485d6040c0b12200c006440fa8100c500700d8516002040c5640203e55108510991031400d46a12942000c500d40d0640c131b010025603d03d5096000600010300440d16a0041a0704081c01e401180d04551410b007000342e481c2c0e41e0385000740502003e118044181c4070705200803a582c0c60240d6000306413900d5880b07189000d9004050000100b20840040c0c0b40311109100d44c5d01c01c0b030700d03c85d2540c00d118010380000ca4040d041c0750a070140719902c4940820200a44004000c0001e004016a64440d590240206204e02c9030f05056042c0040070b1034959000700002004500144020301402042c0185012509107e0241c6805c81c11502681e1030b0b5441c03580f0a5035000c0c00248190f008560118041d8807443c144416940840c0c0028070030380103030120000e500075441c24007a5608a040d042d515034a82883c2144c500840d501d040ca2a078030400d06402c91891142c91414002c000d41c0c564194014500d480742d01d02250300400c03640ca810b00e000c042506100d00b1100c20850300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 251109136 1250 251107886 251107907
    0x20d200307080708040305220e0106030c0219020a030b04030504031712100509150f031c080f1003060207060219111203091504020a0b0a030f050c18091915050a06 71
    0x10b45469203091008c1141c40e1854440340707000784c43c3c100301540210300e200c4440200350007001b1301c0d240410802400788001c1d050914401e501c40001c0c65a0b100031005d81c2d9206d0302c0303a08803a040703d20000345854504080391588902c1c1c20150201440070822048101c5410090142040005c001c50b0589c030f5031000f84031400d000b481002c3e8018860700203d820403443c020950700e1000c006080300300c0302c0808000b185c01c2c541d1300301c0c844004e01032481c2d08891a64001c1c4251b42e00c07841c0004811040d2402088054020100c0e000143c02c0a501080350f4007041110350403514419110440c048011044c041c00400e101c0076003020984c00c0c051400c6416660a1100949005490480160080001c4410f0544c100c0d14010401c0e41e00c403014600c00540c0400b00d00042058455941e80071800032040c1c401c1e0810346038050040e002540040141d82d41480921880c80031140c02200e032070000fa140d880708000d00002020400c0301036403815003840b4503000c40010b800c086802c181c0b008074442d03644510540394503104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 251110386 1250 251109136 251109143
    0xc03030914100c0813180608010b0d0f06050402041107212604030c0807033504021302090a0e060f0102070608010e040f0804080606030115120204020d20030708070804 73
    0xf04203e450010700c61801030844450101d000615080d07840e4021070585a13581d0300310311a02e585103c01e03ca0740e8401e01036803951200a0b900e0080c5034080d5a2400c808014600f809001c0c6076072807020030119503070740d0403038011028520030031900d403100f908103114004c032100203455000c01d00e944958461401a4511030b101014070044c03140140703000462407030a00d030051080301000010382c40c0800061100c07010300802c41c000e0307a82d00201e28488070b90000c0b41a600d9003901400e144040d118250190101d0965849941038030a00c0106514412117000b038003414070720590124000f50046560b01e030350701030303a4460001203440710f000c04050b03401a600c6a101b400b811000030030b4800140400801f000c0c0481d04213100d100b00070144103542d01e44080300e03009604800c0c12078000314140511441c090040340249a41c50001d49852464030a03800c2801c030154000034011500403c1541800241d42e01041044c6001083c0341c04030426012452941d038011180c0d1000300b81e4080200d07114910400c0401d20580c0d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 251111636 1250 251110386 251110397
    0x10e030105011211041b08040302060717070509032a03070e010b07021c0602070609020918030406111005070e09160903020607050109060c0908070b0f03070f0504030c0303091410 78
    0xc40d51a4100c80c01400215145c00a840b010002010b0341c290400181400540d5070b8441607080c02e00e4001d0400101078121420001d502400c6106400f98288140e0010300900b031440d9210030802c0800c0c2030003807001000c034524449403c105440b40120511181c41d407011001c4e100c89075101d01c40354511003020b0141240008041c040c68006003000c50a2001c00149100c0c2e00750003000ca0ba80f948283e911440c07086032030944a0307040c1e5045051a140e010740040c1020507444d0308041d9841d049542e4043c40c0314000c1044951b50302c5807981c00c0140544041c29000305001e010f24a04614043c00c06003844201902480c1c610001402600350810f404500d0388070f550b030300c401c0e0034616005c101d1540c000d90801e641030355880d08070200041452042005030805611541d036502e2804080d28101101a4442c400c9540d04100c0c0405540310304080326070008242c1082004049040400c0300c40e4001c60308001c0000305001d10100601d600813038030703070201c0f004261004203c4c135082c428015000c01101485c004101d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 251112886 1250 251111636 251111669
    0x10c0918090206070b100e010501030902010807030b060702040f0c020d0912030c2d02120a0b0402120723030c060a080a05090c030304031b1d0a090611040b09010e03010501 75
    0x856001400a81d00081c090750408801761615400004103036881c00900844100810540107a010414014a0242020080c5000d50f07000138007840001441c0c1010107a580754404007aa50700000d030346c0b03000d401500812006072543c40c51801019196505001b40c0310704058000b000d03110301c2ea04d0701950000303098043c4031782c160f580c2992044192442200d40e804600751301c1031900116094080c409096644040c83d101450060004e03101500803421501d40140d406c0c0404180c010183c5030700258140d5040d0109035440841500340103e54104050010030040d03081d840181d610b04841c8804012400c0e25092811401041082d1140c4000000490301c140000b0321913621790340c0407550010b84c43e01030303030300000220300080d043d50301c0344d04200c90041c0d0584415010758410030399280500b00500020f4a8611450803c00d2900340040101c1c0300d040c2c803401c3d89000c220940d00f1011110b2000c10219854940b2010503841c150411940c0c0d0b8002480030394821410714050094074125582c02e5094075444 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 251114136 1250 251112886 251112929
    0xa03150507020106230901050f0a0315110406170a020a08060108150310020409050a0b0303031810181a0709120309080607110d02060603120a0314010b0c010c09 70
    0x90400070301d61002d5541e6114002a000d40c441000401c018008180e184650303802000c2040342401030700031500809410b084844141c40d0000010107a80e04490500d010034000040e440103000180c3c030f46203841070003140020b105034004c14416103000d0fa10036001400d540c1d11500000300e0080380c0702d200014007040003003a00c81d4002c130105a042140017160400b9105a040420702c0d00d0401501a030403141d0010701003021840e80c1c81500d82040418205000303034902480066034030700000d0940280b40d00e1000b01c10b1496981041001040c40c03a9140603c65513680700b80c0900b10401d200001d80e100c024640030300564070a01c800461040d2403e03140c0b88051400c195110440059045084040c055011000303c0d08080070490f8a108030a15919030325042088407010f410044c800b1012020356102d901031186c290360200d071100f1780c00c0080c507985859200d030102c00c90240500700051180c2c441d420700041804407404000305219010342000707020410412800310f0b00d0304400d01c20a040400c0030815900306 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 251115386 1250 251114136 251114141
    0x606241c091a06030a021c0b04030509040e0307110609060d05090604110118140621060114070f020108130230070b0304020603040507081f0b04020307120f1805030301050f0a0315 78
    0x11f00b0202c59404061144542e114050300e9010b5406a009c2980880e048480707103407038064042006800800345052a185680700b0860100c00a60301c0e10460010420100303036250542602c2010242c07440074822820a580501c1d00d0324001d85040d10282028081ea0030654042c01d500003004e070714444104000d915000c400054036104003502c40d4401c0e020000046140c0741ca9207029611800b2840d03c5405080850015003000c80302c51a8a00700c6c1c0c4144400800704000168a000d06d90b028208100300d61768448401c000d25440340c80080d401581c1c100c07050902c00d251518028048001500341c0c01e100c011900203a5142501d01c00e01854010410001d80181807210103590081d100380116901151254022410821070300101c40c40c0b000c0d10180121546880d001e42c40504a00b52011840d50030f2048000307190f4419203e028808035103c440350742c08002c1d150701100495006882080c1c12110310f191540c5c90390300a1043d140b09520074201281c00740380c28003080d030480b94003c03c2c0c818100341050b501d001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 251116636 1250 251115386 251115409
    0xf0512070c0809271608150a03060f020702131e091103070803130918030e0f1003090c1a0a08090a02060d0f0c020606241c091a06030a02 60
    0x300312074144507211054a610740c5101e0100c0340403030912000a004c2c3d0701407501c060000c080781100702d6101c42d80ba046039000952140c104100000300345524400c800842c507100000e500080c00c00f49130110b840b030014102c2e809800c04900c2183c01d4220380a40c0050002954200703079000c4070203c00c4080318180d420700c03a4002180940306800f168151810703440042d00344103d590000000d5000041c0b405540350071100074a0203491a0002003110101d1a0003000440c1d00101c001403c2c421000c1651011f40e60b80346011200c1100206911100000c0e1030004014054060049415002d181000b04018641210304000880580116410b120f80c8550446114101804500d024029145813074090f803224070061900f4040c0d110049204407a040e680e5007140c0d0041c3c000320454001c1c81c28011103507075484e000c8102e000300903901c1b15051201c0800d810188508221180d140c1e061040c0c21aa9440d2074104072041c50040300d0000c0c83c3c1c10800305210500c82d0490b1560742c1034200c002100d00614085400d00f8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 251117886 1250 251116636 251116643
    0x405040b0406150503010806100e0106050906190905120f100506120703030e090609101a0405040e0c03010621021011060a051807060903170903070b0403030f0512070c 73
    0xa00e283c0e64000c002c0042041c00040e8002603070000043c40302070010025150406619010b84505a182c030402c1a0426018010281000400a070701c1d41e8581e071303810a940b54007907842510403001045000162070000d4034400c00b4000c00d80480c4418098401042d4408a181080c1c0900302d000c100c60071210080c4401003135164822051240310400000801c00c0402030340c1300780c8400f01c0001e2141c0c04c104030b000000b00058031452410007080300c9101e2003058281200c03403c85080910566030b00020b800d038003d50b04150340040c50140d00f49010b0307400050042103288282d0081020b60385403102803401e0500d89a031130203459901c0c401280107051400704481421110f00e0502502c026182040e0b080c40000c0c1c0e028100b00f611182400703848039002107540c058164070801031203030030319101d0003512840561001811101510182c3e10004996504540000c00010140c408071915200100002d410600040d4000350341c820380381c07072480e02983c22980c4034106403000d01c003943c1e04c580c8111041c10000e0f0044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 251119136 1250 251117886 251117891
    0xc1d010324140418060c02030c1504120f020307080c010b040c0804060c05030114010c06090203030c030705070e01050609040506040f0e01021c0c0c0210090f1413060503030405040b04 80
    0x8052248800000d16101c03860600d22405a00c0c0003410301401e503501072264441c40c500340031802d40411365021100c005500c07201c007050020010000360f086020300600700205015001c003592002d50310106052140b0b10034422803aa40720494022078418000545e040d02603441080400040782414000d008250706a8001094081c0e4400101e0b0a6580c8114400007081c001c3d8240b0003040303183d00410740c0071252454407604542c580000c40003145849844213041c002c0502c3d080c030510440340c101c000201d0b0040e0484c5c5d50740e98103559503940c070b60000c2410f4509002c1d2440110391025010a441d040b00c9000b403074035042c04e4103001000300515010700842d90180d5075070300341343c0303112128001d40d103a6800c0b4400050312200e0013204a001d00483c405268040b601d85184a80100d821000b18407117160180e40b02035044800f0f12003580c4801c0581c00c04801003481c818005680e01c51059503090aa40507610a9415031102d1196402e483d603c1c00f545600d0b0b00148801c2c4510b061940c8881204c40340204003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 251120386 1250 251119136 251119151
    0x10b0a120f050d030e0c010305040302030406050f09040608031c090f0b0a0b03060114040b0102030313080c071a040f0602030310060f05040b0d3c09031403100611010c1d0103 76
    0x1c070b40c6040b840402d9600420789921590390080014420380e5003001080c00c0500c218a000d907402500da201358000d603014094085080c02c2911903510640780c100c807015204004d100e4032041c03150b54a8000718291030030088416a0640207407242d00581d81a40d51100101010342d103140c0e035031802101d00801c0b0340652580c41240068039074013040700c24000c14851240c040070100344414482078070324000401c2e055510410902412007107281011074502c4d0000511511101c800303603040d05060725944021083d00c140503618803810041d600400890300d00350305510490b03a6561040c0c0c0c0300d00044034201a9400844402c00a82d03009860004500b003043c40d0803131a00d030311808035041582059481c01e4045030340e00100e00d0600b04032020010442c541858403010b080d5040d122402101489040c050041d4803940d62a003054003881d2520b00207001010810703168035000056419010b024880e140000b444005682c0c0e0154061081c01480070450362203038548031200448082c4100302c2e2000310704041d40e4146 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 251121636 1250 251120386 251120393
    0x30c0818090f041209052107120c080c0f01050306040b0316030506090c12030d1e0e010b0406060305090a020103110405090c0a09060504051c0201030603050f0102070b09010b0a120f 79
    0x1070300d07442142e0822281c0c11908090400c21103880c3c640c146030062000c0b02806005079a02c070319410102c01c082c0d070139005140d1260320142d810860127a1011400403005110308081013200c009100030742e1038640031a02c2c07a07403811040040c0b040340501540d0200b00208041165400d007608980c0c0d0040f4050112a0b000389080139080700800300e0350042e107142d000002400000082400603030f0f2005800c440122400041e4031030151240b00f081103003400b040d59900260500641d40e0100541d90406071400c0002801e070410041c003810041c10030b80d110754078003080880d40c54042d2103620b020b0300507480180b090600700c0e0700540081c050b100044010380d106020000740c1e81d480e290140d00c07400c507060000e6200d610241001d070221145400840c14000140720920642c1c0f81d414400700c101c00c0c0c403030071014010503500058004240340d41025080e40191100d4060b0100e05400a10900307100303196548160740c132034000500700c410300041107502021080d010050045103c030b2004d402c0c2e003e6500d541c584900d942c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 251122886 1250 251121636 251121649
    0x5130e0304060e091e0f0403030b0306040c090c020604081602040e060c0405031203010b0a0509040f1506020d0c0209151c0c0314030a0e04020307020a02030f0721030c0818 75
    0x103000b000040c009404401d250308001140f1600001c006864002d00700000142c040140c4004100101e10083c00d800101494441e0f00061301c2c00c04058165001ca06040c1414143c040403070042e14400c5003080400c035802c9100049c00751140760002c0010f405c010078003a00c142c48800400b406e99200342c80714040040c01d04280200c5000780f1003000710075070b1642740406240c1840292900300400704000c0c001004904100002c4458103291403400315034401810740010000c241c0d0b040329010842c0740c4080704485010440724003064400380c0e0211a0b5108400004030f400302d83e18031000350003103000701c00700310103140580300601f03c3c02009261022040c988520a40e40c0d0301800c2e41902c190800303041c1001440004410707051580c2001010392300c0d00b03c48071409440507a117a81480e0040d580040040c8569209108030340011358020103555405d848040714a995011030b001d0142610300840b06807014a80300110920415450303190714042d140c10352541d038415000a69590000807450461164554941 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 251124136 1250 251122886 251122889
    0x3010e100209041104080c040b041407090303030f0608070902070c2102040606140306010f0e03010e03090f010912030e010302040b04060302070506060405071d030703060c0816051305130e0304 84
    0x34000103881e00c0b02001008191020940841e42030501040107001e40240407404410901085d9004910101044042401848110701c3e100e40c6280600510030416400102441103034066941884042e01d1103220720101e580b6841210308542c491071041142c1c80a0307801400016019040052400391b41c0e140f0306512010b8001404036a80d400a8a80e0031407409126110182c00c2c180b40c115650410280394540900c400751015040c041c2d000f510044141c03090003101801c0348043c009000e46002c215005640303070805d0220900c1100740180d400303040e510904003d012103103942600c41d44c12849031002d481c040a25080241015003c03c40801c2124a4000074401806240d0b00107a460509007002c5d41403910180c1418450307420700c020321800991100c081c0c0c215040d88003440c601035240d4070000780741050b207038401405a8144488a0000d82d0040c010a00c1902c4c5188401003400346510700300d40034450000b000f4055070382010103000e1800c107881d4000d650015600c0020304a0700440c0602d00d144c006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 251125386 1250 251124136 251124163
    0xc06040303030e0f01150801050a050f0a022d040303031a030a1704090212070f17010611030d050f04030801152114040b060f0604051008071806090e0c13060e03010e 72
    0x40641004007d00910402da1302c5500c0000811141c01d001001c00100c50000c1d066007241a00840c00c5c20050300611a0540d0303503580100310404100e40e500f00000c15400c10b12094000c01e107004101d00001c80344490540c24144014098040c1040d40c0d510301c07502c10010030800302150300130f00011078854620b1000f01065088941300c09601c0c40c109000800140d03020300b0060400a800c0720b46c800c070b0010800000c0c10344807113007401d03030007101c030302c039115180d8010580506411400d200903c101c003c06000710300d014034081d54420049a80303401c00810031080043d0b400001801c8441505540d040ba01400541c002c9040c4000c21045554412035842c210180c8040e2400022107062100c145883e080b035510446c02965854202464280040d04c1e6950703068441041c00003050024440902c20400408a40c0102c0c0311913000d15103a00c0020203051403406210342d0215404085003000084800351000038440507a000c2020b401c0201c1181c0322200c0c08035154066403105820403105c2d1090103040601c82c0d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 251126636 1250 251125386 251125421
    0x6090b0301050411091b0f030136050714030a060503012007030c0c15020d030f090308010e061804080d0c030501050f0d0c080d030e15040c0b09060d020f0703020105090c06040303030e0f01 82
    0x1400c8802b4400701006004248030344a404500701886107481c02104815030609001074559500c40d8141c43c1089840f08030071030a080042000640b0703106030302c44000d5500c19402000b6010a000151410680080c807007411041c0c01d00c0304100083c41240c441e40001e02c070303980f51181243c0e550541828460744030848405a000300314001e003a26814805d54001e040f641d4002d03c42c010882d14094144901030254a108041c48000540c0302d49a0032040184c0c41c0b4001109103e616240c18050201d0f000b15800940090601d518170f10360900c82e000e0f10b81a0740004001c0c3ca0410301c0502048041b400316081202c82028200000520250030f00070303d41211081c5e14042030b0240085051810b01500c0384005000c040d030b80c1c042c000461128030b0f0803801e48452000d8103940700751000008506028070381c0380012260000801c103482c0d075000d07001750090500c46e8000740520f40f140e0034035503103400d2500300b0360360007400034401040401d03c282c22400c815000c070780c00e44142c00c0312b00c207689080d11040e0142002030320 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 251127886 1250 251126636 251126639
    0x20109060e1e120406050d060510020d081509060d03030b0604150207150e0909070b210603010603051b01050714070302090a020a050a1409031006090b0301050411091b0f0301 76
    0xb2a0301c1040c1251403641014114200718441842030901441c00350303200700302021400381c0e140b448650042014200080040401d0960341000a680d28020340b80c0000066185022030303040820109803d0100d034000f01090f04c1a41c4100c1072003120080700000f5020151034044801080c0c681000600280c580000760170102411303800c000e0718001e03681d48030000c016400c009005425030320101110400c541192610400d8940d03402c12464030045410642120000203490b12000c5168182a8464182d00c01803481d01c1d5074882c00c040c02c0b41c94900c009003c940082c075808071282c00e1002ca010004405040c210b0403d001d030740380c1c080d140d541210f0905041d4400e91060096250494010358400c5460006514001100d10001c20b13034061440c80c2c600340202c07041603800c0c5a0201c001d5601081014040b106100d00070751a00c0c001d4070162140c6102c0d2460217000c0c07a4142410700840340b143e03030050410408415410103110030090000c02045142e408420b0607029444840c00504021a84406054495 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 251129136 1250 251127886 251127913
    0xa03030c03150e101e0905060d060c020c120d02070303030b0105070b090102040e1303270e092a0d141f0c0e0a080c010305040503090d0c090c08010e130201020109060e 73
    0x13808150010400400804180b001d405840181a41a02d51405020890740c8a4002040d02d80c1001034000700340c54240000311121940c00102400c0c0c0c000c003110071a8401c031807202d40644070b4840c0300207200103801042040c80801c1c080c0d08440c012680603d4500c1c90090306442d071200218040d503081e00c075030350001003c00000800282c42a0440c0b604a0140750008040e50302400c01d41700700e03400301591b40240200303640d03c0e44501a2240144801054400645445c01446444654481e081230f502c2400900700302c1041042c01562800074006001e90f8000b101503210741d1882d00324911526114464110101962208420340141880c008000402e000482003405000090301500031030007000300c624100600742d800190024119002c0c02c0000d2642c669040481c10340c450001c140381c100e00000c0e1450108035000c011081241c200d41820441d046000c0d108a40201080c41400c410245240200c0c610142415100541520500002903601c00940d200401c0e00c0300786000c010140c200b14000680c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 251130386 1250 251129136 251129161
    0x302031b19030e0a06020315010f090803040b0c120a0f080c03130b07090302030d0e2e050a030e010510140102072315040306050916080a03030c03150e 66
    0x162020602014101a00500091107003030011108500700750312201c0c0c1040c001e805101060310950810800d44d84e0f4a441641c0c4440b2085a180c040d001a0b00c410290740034500c0341c0507403400c0c0c036041d031b02551400c1e00d006074101d4580c020020020090290207021100c2a6a17080203018140598881944000700c5440107450a0401804400c02c60010020013802498040104a406a00046619894a030b03407100711000103494100135054802c0400c2a10050303041102030821480442c1c800003480343d080035030744080e800440c0301451714240701910031900b80034201610801c600741c5400910395801e80c06403403d41c2c03c1502d80509040c445001800504410710389284942003c0c0020711480e450046e46c1e0001e850040030803011035086010300e14069a601850080e00343c0b603407884036104d5450341020b100400701604c842c202d0b446181c0311090030142074845481220b11143c09801c0f401d8450710213801809d0040c0c0ba940405644112100442d4074010601c0050302d080500309109103080c0c0440c224 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 251131636 1250 251130386 251130421
    0x30601030308190b0904030f030e0105180f07150f021501060e04060b0c0c0906040207142404050c22051614070803060d050a020d05100c090305210903030a030203 71
    0x11240c0c1000181c130380c0d80e1034461881c5c1e04140e05161500b122028001c048008224160f12120301707500741418080b1620101030805000c0320584140d561807895125a10342d41c0f0760502c140c21000c1030007200207124034014802418401c03594010f482100010600501400c0c500341c01042c00714034080c040d620541450303c104406000741005181c5400c2030510040c3e40c4040000000d4420060100059050784981c0c050b0348040b80d0051603200950740c0460700e191a84005245000500d100040d00495000102d0281d8041c40d000009000c40503142d000b404007c01c0000e9070341c000c04941c1c003807008605a0707070310682d407003001c00603484c213a21087d0b4200244900d055503440020213000b88038420205058408594000c0780484100d0140481c502d455801d140c6100c43c0a988039000c40d900b0307418008040340360b4030903c8041d4410000c001e00000c058440310f415010203807103035000c034540103a02540c40042048070f208101d815410304000074002880e56020480000c0004d400dc010b0043c8190002c45042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 251132886 1250 251131636 251131681
    0x30302060c040303170702190b040b0c12180102070210020d03051015050705071d16090308030c0c070509010602010606080a0c0e1c0b0c0a0e040e0304091a030601030308 74
    0x1440c0c64659113005021190755240d0f0070b071000f0003c0c00b2075046402005800000d218800502482107003e08041e1088a01110243c0d03126a86100003440641c1c00021940321404100c05172030070b81c03a213501142407004180e0074a0f402d59405c01030000541c2d40c80c582d840704481c143d40282a52740075420018250352016004030b031007641009052000c04281a003010f0381017068540540ca0f8007550a0445c584030f05544100c0c0204503020107070019200c4400442e01c070700549684041510408402241d00c0403061101504401c0c0500101d56900d04540040104500000441d0380f550b4480001071007401c020380c0280050303035580004003c4990824050365100c0c1601c20100807080364090050508180360f414a8440c0000c01007035000c416004201800d581d80004a060700c2c1e150003002c40e1002e40c02282d083c40407a04106405846181c64007420140d030341079001075400c1c90f141ca00c180c0301a1903013507400c020503145002d480c2e0560300d041217094029070080c0d88010745400e06030480c0700050003452615 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 251134136 1250 251132886 251132911
    0x5010503061f030b180d0804020618040914060a06050a050d06020a0504120305070c05040c1e0e03030d2f0f130b13030c090e070e060f0306040c03030206 67
    0x108040c0e500070071902e500c01c03049001d06420480e060686a021209074000030001c003400024840d505a0100f005c0b100c84400038115484000203510543e500b141c101c2d0000d510903020450665201000d482440c1c1d0740802078000700740880c01d680c4400104100c81111140380e4082020026800c62f1400b031407008010a0321b244d06203505110208000c564030420140441d0307000204003a035a03105000b00e60081c0904000c8011403071052030010310310fa00c0442c1c1620066907081d07010a46103440e01c503088904985030ac3d20f1007403a01b1900000086001c200380301d070a00c0411405540d02e92030070f01c014601400f4210000034126205a409003510544448a407002d846d044c00e420350750101031003150f4030142c150328626282c034884900c0f840e4988071a00021079242d0701252200010041c4041a2700f81c074071900c0c030000800d840744104800c07a00070588801c030303079403141300304002d00c7c42034a05030703500300001501c1115000b008202003071030541d05450071a03d414441c84100b00381941401003a0304040f010700c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 251135386 1250 251134136 251134139
    0x1091d1005190903020316050a0c0f05130c02030711060c070303030212090703080f0d0902100309030e100c0615051c0317060604150909060b0901020c03010b010206160903061506120501 81
    0x20340d0b1f0b008074107a0107012400300444405007c020091403408070741c0301c0190001540c48280441c40420350b44101400741c566002c4241216080d80514850030149600071403c12a0700d4072442c01c0d0340d0080c9032082d00440c0c1080810114001400701c80050341c080c0d00c0144e41c0741e814000c61b80f0314007070007440044c1941100d501403000034030302c41c203c500005404452039143c1c2e070501060300040128041c000e40c45040c8030700c07446074150941c20130403c4c81d00079107401084a0800092000d40030300c05081c80700040540c002000018000c0c0e00c03c3c001000d003030040318a255140c0b1701140518031a0354a290b41c640050071000200f60744100c0c40001c200c00715240064a01b460004608580214082c00e0305448480e2030504086104e01001c0008120440d4288807541c0c2e104e00352401c82d4804e01d411801800755250080d820304050082025078441a40240302179501c0c0c05008101d120080b00b007400308080b195000001c5803a0740180b20318610360300e0141c41498600b100117090318940303200003508681030400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 251136636 1250 251135386 251135393
    0x60302131505120c2e17060103021c090c050306010918080d0209220c1815110a030909050708060a0506221e1205030301091d10051909 59
    0x60070071148256506802030580c115071a0504541007800f6401c4120042c91000c100490301ea81c0443c1944007903000c56142c1039403403c4410010401201084a03100e00224246510942c020031021002e82c40c41004584046000016115000300640340000412380c280074074581800128010300101d070080101d41094100440c030300c0360420002d44031040c042104a0510441e030103c42001400800c0504041600700c40280c100f00c0d51a04020b40d00d2410b2290740d10a40100c91001802400600c0f004005103040703c89090a41d80c100c20300200000d0010034014400704208c800c800720701c05c0d00c1d80349165051001d20301c01c44200a103400c0030400c5050512003240c0b90300703c01205492094920945e10786950a00c8604c4100382d15040e5141d40c000e0b040080d02c200e000d01c0f031390b0701d011002914000c0603a4074000c443e007218070031001030040d800803c01044000626400314008125110300c20410050304140039041101c80a45581101e0701e0780200110000c2c40f0644075032900c0480c60800c032641c56a103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 251137886 1250 251136636 251136671
    0xe0108060f0a0c120f06170a0314070302010b270a0b130b0f060c06041a04050d0c1e080a020d0f02210c060106020706031b0e010e04090602030a06030213 67
    0x14440000c2c6a40c07040c500122600c01e1428010a004c102414400b51082002007001480588a16072038405201c010400d11500403845402d403a0700366a40c01d580c90362070000598030381e1100c4011030566581e890b03c9082c1c0c3c1c56411803c0068002040341c4852595442c0311590004001420b120740241b621122140e181c2d25114145134400c1000030004420040b01d0104028680c2802074551014002c00e21040340c030740024503144030780c1c0708000c4089045045481c3e6981258196401000c2c1c1e040b02400d070070b43c00c0c451000c022285000b16902003d042665140b03800060704503000340d03400400021180c405540420409408924500d448001d030817600c900207403100904002d000d410005031102060600e1a18291920000c401d02522555652490065a030b4a510b22418020034100990300030210020312180420411607195038425440d8500111120900f101151b90710540d40c071458070205c1e0f003500c0550700c120728100d0006240e505500411062100519840081c2820104106d894101d4074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 251139136 1250 251137886 251137891
    0x31c090b01030b0702070b0301140f032b0203040905070909150f14031e070806070903080f03060316030506070908070b0f070311031206150903061b0c0f03040e0108060f 74
    0x304050f01c5a11122400c0342813482c030303901c50940c0050100001ca004000c0288984920000b103880020108160050607194240101003000050140b8103550107101c0c2c04d050340c80d800c076003841680e15103516454003500b00d03042500c03044009504c0213014044420140716804044040d00705901049192400c034100400b201d0040d4100d244034034005000da0b4074100038000440700030f0300c101540030003440c200590b1444644100c2d00c0f06e10440d004180d00a00a450034000d407a00501403500d8050114235003241a4409400950944241189051030f442c0d50500031004e140700c1d5000d84080d0030030302030007854405590000e4019800100d020403500070300303000b21038010b03c903000340075200d5680341400d80d504503807440c908600703001c005210001710340000c6001d0301ca03040449554a071410709402c01001d5000b00c03012a9090341c801008a50365060740341d54039a0495161103018034100c0c03c410018100f001d0340c441c0d02070b01e9001140901c0303103c06840c0305134090700100c03000300028905200c0c1082080c002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 251140386 1250 251139136 251139143
    0xb151e0f0d080d05090c011b0b0402210a020312090d14120d02030708010f0302060a0c21020102030a0e03030906040f0507031718030f030a0e0d02090405031c090b0103 73
    0x203244090169140c1c440315070344040d00588400e0b1540854454a4054042102c10f80c500c2d01038000c0a00b480e42c0541ca409081d034000b401540c030155255684c0c400d010102510a81e480820b0110300710140202121541d0034403200b0010700502e80c02071040c1890a0780001d02485013440034451045107440d512904128103030400300070440704c1201c440c80e5050401280b42880620303400a80201c014080b43c00444c0201520755402d140e5a03a9903408200c98515070000079401802084803190b0b25115001448000e070081c0c61882903003014110014104c60f0b0160b60b400541d4000c010400003401c81d00c20189c2581c60b11000d1440c40c80c7c001500303501c0740c0000708003c041d1034525040a080c800f00304440f01c0a164040041d1540304940002d40030243c00007954841c03100c220a000c08040e040c041003203641c0d0a848001542440e074601c0d42a00e801961501c800c1d0840c100720702c2a0050307581c02018600550242d0003940da104000002d41040398800741c9071450f0581083c8143c400205100003c0b41120f80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 251141636 1250 251140386 251140399
    0x609050f090a020708030f011d0123010909060f0302011202030609010b0705010e032b090506060f0d0f030302071b0f0b030c0c010501140103150f06030e0304120b151e 73
    0x40b0442100000c0c007034008040c212403008010841d070801c980e20355074181c072058021800c0103c09034041c5031007254240950103d10075914098a120008050420302a11050511040342a114000b0303004a80d911f50100f020907a2600c0c040043d940c01c440724107440038823802c00b5485d5113031440118500c80d00600c00d10440c8100055100c040c46001e5100250081102c0c2c25250f03110318156119140d001e06d1101010720561407039803003007c842070744169031110743d0000c060161955003004100441030032080058203d103210b449200029036840403121414801d4800584810060078480c0014110300d40d101c0c0007a0800c10b050290700c060724000303c01c56022a00321996540c803202d410b001ca004140e90b40078590308000000c90460050220040901004e030380402c0409001103260046803118132074100c40381150501405460b02c03a8112602080c0f00e20102ea2902c0d0b9a40816209641d0710302c030980d40031f0782074414040c58020610340c0380c00a0008951110046140003400444089501c80e0303039101c0e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 251142886 1250 251141636 251141641
    0x9090718091a09070e0a06051c0c060320031602061e040b070507081303021302120c09040e0303150102150402011704020301060b0408060402030f1609020717040b090301060609050f09 80
    0x40201303101030a1010501c0c409803d1995118001d030149008241c42020b010000003d5400c1009801d4100341e0041c008640c038030300d000403d500030301800e4109014400342610480c21004c903c0c00550040c000b54100450040304844000d08000300504007400514401701c12a0488400000140e0015041a01603010f1f0321440d5040e907440c490301c0001046a400800c8500c1140c60159540702168020f9441c0090500b0003507540d02240300d24420a0481c00d0540046290960094040c010013a00070300f0010310003082e02d40840c51a041141c100c7d5131391000c074500c03021659062005031003072800610704283c2d50a00380d0018001c0300807034180c00383d00e002290005056682c2500f043e001860750000301a86c8984540001e40c859000700d070305171301905c6031690003242c0e10700000e1404040640b03100544201030600c05180065441804162501204481084041d40c2490001c00050030b405400e280d0b504001400e06003560007541c805010301208070f404006903221402013042d1202e00300e03003084066 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 251144136 1250 251142886 251142901
    0x3030e0415030f03020c040b0a061b0f0b04140607050406031a0603070302090a050603130314090301110901020105160509011202190306030b10061d030c09090718091a 73
    0x60000006000d400700a81078004144502c03481c07240c0156009500342d4504071000410b0000303451102a00703030703009030032a90308010003807060040b401c040203000e88800100c041610b4103e04ca41441e201a03178170303455203828441005100541040c480d00c906001c4c1070b8525040c4c80c050154011846a00c05060b12012002440303403c10b0392000e400c580040c0781c00d44070f0510b40030090094104261003400f078824058042100c1c54120250703407040c040b001010300b0301841940c0880314041481000706100700280421903e0340d900303009120400e0302414516031180c45a20009003514406410305030840e00742c00d1162503482d80a021200c5c00902803c1140c80748000220040003071007256030f111101455019815020341d03054004904a0340038540c8502c007501d0340900a031272010303070b40300e00c401065100414070080441140d0721026088020305540000303105902084164000b15003031603464220b90001d01118402500c074416034891600100010340080e600d0030a10355800e0154220203031505d0014510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 251145386 1250 251144136 251144141
    0x1a070c0804090b010c0b0c0a020c040204051f090f0605090108071715190e011d090703060b060403150e190827100314060114090904080c030f040f08061003030e04 71
    0x9180c6e01c40c0341200b41c2d01d0900c0b40c040158004082030001805400e1b02142240790500a44050f81c800a1540c0258040c40282c000111140701c0c0c24001c0c0b20f141400044d011008070940781c01014140c50351561101700d0030004203410300041110382032090303c100344c031401070450860320ba00855028541502840c8140000c45510003036069888100a8000225608100c0c1c802a030498200c0400c545c50346c940b031031006030840000c907441501603004003402c1001c00c4a540115007100380c00b8100c60310307058498031111411a00d6160703200c0d50030384031054500c2180f010031130b0100441d0081c0d6100358101e441d50700c01301c0d00e10404000402c813481d1a024260045410400465142030003861400e07a0080300308040c018108001a4112000e040e00c005031007540100241c0d84030b03007881d10300f00d80761813101d604202c10248060800d4490b090305010045003854104014807052549114898440f031401e402c0309035103003041d00041c2a0360428800d10151040341d0001c24184c07541414410025a01000031400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 251146636 1250 251145386 251145407
    0x91a0304050615120f070e0601020a03050f09060702090403081f06120e33010e010b030103080a0909051305010518030318010e0715110a1106090d020901031a070c0804090b01 76
    0x41c05e00815848040290703002032000e0440b1842c061110065507000016a1500559540900860b108101680149400c04003c01220800a204d40d04200c0b0503000301e000c03880c040f50114042045030301480020043d5482c1c0015201c52032440d445250304203a0001c6c0a129a104004003054407089481c5080c40d081c0030410202c3c246211003003480c1e41c019500c050b00d891020401c40c0381c41070f420001c40e2a00c00031034010705030751038010041d245034038590341d00c0c07010303445032020104000f00ca8502140164250103100d00440b225001008100703c3d50600b06e007101e0001d807507440244034000c010480380308003000f40d80e400f0600c0f980364400503104421443c090210303500c83d00f1740c6005402c0e010501c07140080c0030684d4203156039602c0d03440e0360b05154540d541c0d00400402409030590710000316a9031070994010040440b01600c0102d11701896404214060407c0c0c000b11500c400f2001035001d440d00d030000050707000c42c091030f02c000500c1d140d448414203841980908504582c0b144644505a40a142d4895 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 251147886 1250 251146636 251146669
    0x909030309020310020426070303050c0a12030515010c110409080c0d050a030e010c0e0402030c0d0204140108070801060c020907200c03070816090b0f10091a0304050615 74
    0x22004850000124001d40c03003030080040300c050f040c0815987e003682007841c4c41c0e002840f078001c144140c00d5840a8903039410881091807144200001c0100092007800346140e5500241c5002c1030500788031651a8401a4090615042001d10305c4a1800300d25050024064004140c40000781600c0e203003031404491040301c034a1031851094442180c140d5a1010041031924111381d420800896600200fa00340e41e40c4180010015040d81d01460052420b40e004581003031400d200c5501d0f0240907900030080c0c0e0850380c80b0070000302138898041034550b040040e850b40521a441d0589035581840702c00fa0100b6080072029010f4200c42001406250080382003031000303081e0204076000200b072918165540e00c003d0300481e02074020004001000080090b02d0501c12140300e809000160500d84420700401001c103a01d9031044001e6034180b0951030f0420001a881103580c0c50070041c60a0000d40f041500140c0c4402210384420010040440c1003c1250354216001c0c00784564900342c6400000c440c000000e9105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 251149136 1250 251147886 251147893
    0xa21020c1c0905091911030403050d050c040f0b07020310020309030427090b0907090b1012060e0f0718050f010e0f1f0809060402060909090a05010c0905030f120409090303090203 78
    0x4a520aa40b40d418900c1288590601041b6112412003106000a55005003c140c060001c54000619604419440321054100c10300300380d41d502c100c0f0142080c0e9440100d4081340040c0c94400d50a051003c41c9415044640543c5141000b2400d140d0b039214907c03d1820400702400045103003001e08600300402c030020700d42403000ca4407509003200c000c0410742d400c210510440c400000c0c01d01190089043c0d4501c02026210312740c0104a0540749108600d8400381402d94448000c21480ca40c090030300e000300802031511440e46800c01028221001c000000810303803456002c20041c5a4580100c85000360f000e190859560200c0004900c40f1041a4074107680401401c3c00003052001d22024105a0b4615556048440d1500080540c4402c01540e0180d000f0320204011800e40c10710780e0f88550000d0b07410081b83c00d040c100b0703141c0908480f204c00c0060005400c20748200101d1504200e16149102e000380a0306030316028440a04070b074404e520400c501c040e02d441c1070744241030007540100714544d000340a5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 251150386 1250 251149136 251149141
    0x120512040609140306010b09010e030705121f27061805031e070b0411030307080703020c010e100f0e040612080304060606090e010603020304080c030a21020c1c090509 73
    0x2d061100e05029a421500c00b00c480d01c0f82500d000600c043c100c1d120104030500e00540e80c0c00440b800720800d5582030700f51240c45000106d0703031521500701e40e40c1b0080201030b08900d6841c000740d0103040841100e4169107070400008042143c1d0b206410000703031207205d401400d460124034060001c0c040c00d8882c0e41803c1c0101e4118030601201000a141100c012542c28000412150200c1d11394025a80c0c05044040c0110000700014040003280141c007800808680c20683d45a4031910f250744041c0d001c43c0140c008104105065030402c2440c88a11400c940800e4007580c1034200920380d220650000701001a20499002c003a1255486100940b00180d0344005144860130030300066441a90220b0b007040c9407a000041840c481c040260548514141d00c215903442c1c02400c401940014200307a40c03d94040003c0d81c802d42e801c100819075090700380c4030504950395016034803401c52410001c64810070300400071310592141c0400c61002a1100302580440d010f2811011103000301c458202c3c50f0041000401d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 251151636 1250 251150386 251150399
    0x304060f170f060a081209040e0c130905060a0501080a1209121b050d030c0f03210506040c0509030a0605090f03042907020a060804110603010603270c12051204 70
    0x80507442201c01361030b2104502c0ea100c6040c0e60311207600161300b0038014180020162854141c1249038641802800c039a5600803d40c005201890040e40050107075a6804101c41042414071059038002000001040a585030012080c0c171000101d40041c25400202c0e201c2030710360701514403031020f000d00206400030040b552611200d180710041c0c40c040c01c030200c01c80002e82440d0040c100e0b2035855040d507981840300e03141d56075500111b4141034110140840c11107240d6070401a040400700c00241c0d210045000d04010013030008603a05168018100107003081144845e0320300081c0b80164a90001d0300040c10380d5604125410140c0c141d0f10030445010004001600700344501c010111981d115406101d12440c21081740020700c50450002c0d040070a142c0e082280c580038102440d480f0703004591800d14100c42c0b00020305103501c240c02040c04290f480e9550761000301c0b414008140b46d2400c0c4100b504048086e140d00b80744410500c110320400300500c0303c1100304401844041c034010f50042005403a5502c908 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 251152886 1250 251151636 251151661
    0x90103090f140309030115061b150203041515050618180f091b010f0809030d0c08011805011a1c090f020f0904230312090102030106080906090304060f17 67
    0x8200328806e40c2890b0009500e40c41d03510010b02242c0c425165101074079290210042e201042c1901584c00c82111000308a401000d40001e510131417080141d5448900d184214800304d0b1022000c03d0741400d914174041c0015200c00c01110301200c1071a8440ca9018400b50000720200403901140b0f9040c40e41380c05109107207854840541c081d00460042c0c40400e000302800204030840c029002d40001d00c10241161941e02030280b1a40040e0003100b924900f002031004442034032407268017600041d0300319004002c0c0c00e0790900007920102600005102a52622000000f04001ca00c00c1c9480400002015a4000d001c0c1507000105104c0180a2012284a040c03007001040b1089080e03003d0060b2001070040791030203441d030a224036880940d13031034045450202e0380c03140620000502818801040101c880c00c030710b000018440c851202c0056134940c14010300816016024102810940c00403042c801c0040c000703c01d850070742c0c405182494005025543c02c4540031803080300c000c10010028140074a0a1166 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 251154136 1250 251152886 251152897
    0x90705061c1e1b1b0f050a0b0f060307030c05060f04030f1a0c030403080703053312070e01060f0c080a030903080f07140705070e010f08120f090103090f1403 69
    0x80003c011901c5022801102c01240b020000c0008611182641c0c5114410b103108a020f0b0051804506820903552010b181c00440c0c036007607d00c160034808019132030142c031b94a10750260058014101d458030310740d142c07141d5040c1405407901c00c1e0303004141d850020181c00140c0e0001c0d5004910520816040e0500010203412166040043e580c11000203071850500b008890055505585481c01c0b03a8510307000b10000c2c4030281c245c1581909140d8090301507807110b49442601c0300d5484441c90400214020481c24400544088503280c01410080040000c1000c4145c1110348a060055038184441c80c2180c01c01c1302004c000b402c60720041044841c265141d031060080718402d8417048100e8850081d001e41c0d0324411109080060b11121030322211040307070710103007620078851021215001d40f0b83c405144143d030260002c0084a514600820860342c0070840d07880540d03501c0c510340d0b24000708581a40c1c0a03104900905051549a13031300e45040100148a80824035080758540d0110190481815142d6105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 251155386 1250 251154136 251154191
    0x412062013060206040b0f13080f180a0305060f071101020a05040e06150d180b070f12140105040c05070506040803010f140303090405090f0f060a060e090705061c 71
    0x203801c0040381441c00041c41c280907a4205441c0c2c0030541d10103040e200f065400070b00e0190300144408801d40080d83c208041d06181d003182c0303102501c4600e00c4031520485800c1910880c0b00c0c5914000c104040381d80032030706941100c00d0041481842d507800209840002a0414050040d8130002d0800c481c16130120150040d1280464259030796101e1408001c5140c04291188101c81030400c0445066841d81e0b00107540c400c0c0c6c1804180c030203a566214200c42c00c1c01283d40c8070220341040c11051003164000b0b407200e05205803035020008811804c00752005100d05000d020700842e501e01c204055580100242c80f2031551080888440d46007925040055070401c2c401e00012151081c000700c0c0844141e0360350851900050002d40c1000320b9541000080c00c805021000e080c002c09038030390300101050000d82c503444c603601c00502c098100b0180035402c581700b90b401284261b910b00300744400480f01007900300465008a43c0b45484800803082e1002c4140d00240c030441131440d010490701182c14168030561080030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 251156636 1250 251155386 251155417
    0x2061914030c03040b070c1a0a0b090108010b040c0f08040308060d050307110123030628060309120c020f0d030315060c0c0b03040512070507050901080c09060103060b04120620 77
    0x440420031f58181e00c2080d00100310800000000001044208a043d40251410008141e214a4001040340500280c0100c04a40d464400904081c1058010780700c160500f8a04010400190034008003200b001401c01001c009002d40860056503d41418900e01a04801541c0d556050361403e02048801c0c000003c0c040307440c0d503007100640313486c40036000601070412458901d542d8945040050042c10464008841d0001d4559035003d501c1301172007000070300059100003e40c000309060940c008001e5512075030030840c030b050151006840710080d410300300c00c003550152203968035032800350060700481014411036103050f64001a400d6012091a88075070054210398946900c0d254450414481200c0217401544400e4007900d00201e060000c112003070164003a40d104070384410008101070002e0340b041800e41e0000c0d034412002d00d032040026800003000d08040045a160000307a40c400e0041d841a07540f005800d0040b441444401d8000a10003103414211366052800303000b40801c550400181c0c0b164081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 251157886 1250 251156636 251156641
    0xc02120a0806031b0d150e01020f250f030f030905030a0906080603060915041b0b0a170108120c01060e0705031006020c030a29040320060402061914030c03040b 70
    0xc0c101341c81039081d501c0901aa58480615100d4801ca11074405001803034a66401041008000a101070300595003412039981e941c0d03400260350b254122150f020605d0740c1d0316400c074038070008503141090301203a981400d0803c1001500302054009082c2d0303140160841c080040e2081505034448045401d964450305c9800c243d40700c01c407d055903120100c0301070310158070000c02d400081e48012070880e402481742803c00c0c0081ea0b0011f51400c0102d196004010007a40071580d00c18a60f0483c0c10011018142d10003960250714103c3c00f00d41c4d41010030140384002c000018104c950b50400e40001e80a080da11500c0c0341e103030800400040032079004440e00c1030100241140402c11500c00b19042c506070200400070f043c28034058480c942c48400165114041c1071607a080c103481c5541d02030505e48207a001c1e032603c560380804100e0041c210342c1220355030003031908203104000c01a40c1b040140c960407030020004003804c1034501c5055138201c5008201e034404100100802507010045001140300b5407040245c10200d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 251159136 1250 251157886 251157913
    0x601090f0908031302190b03150621070302221a070b04120c05061611070503120904061d07091d070804110d0c05100905130c02120a080603 61
    0xc412100c0001d15000040010131100c50241d01030604c0319000038511481c03401c0030380e0700281c200c44580c00840c4c080070102c100b000c217281400707030404a010151412443d00d85131280318403503002600c00301208020b480020981d502c0c4a075064504100220841c2000c4650091041c00540c0c01840f404c0c14000318181c281c40030965400544d21103d61201502031191242e0340e900c290100046116001c000e040e85e40e480214008000144c080c003c03012220561846c3e55000505480d008103080720990f0181908010b81d40b0000f0356002600d944845881d15800c884001070094405a4003900000c0890046080000301c20050640201d02540703588640560740c0340c00500150130400c00414403604580002c40d40390003800750741c0d4010b03c184518501018003d00081142500da5030655008402d00024071290410f14a44142c010150901080c081d20b480001965103071400000d0045031344600c00813000038020800340242c8998069429181e10041d48000c0405a003150580e10a100304051000c86 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 251160386 1250 251159136 251159141
    0x702130b0a060302030405010b2809020a09050603090a0204050c1b070e010302010c03110601081e0615060a0519030b040b010306030237080a0b0108060601020d0c02010318050601090f 80
    0x20050040c2514030402d15006058009410081c0b00360b941c0e54030b846100400f5a1000f03040542c1002c030b0740e109003040610039088242503d268100d40242403040101d00d0151740c1021406046a00441d1000d94070341c2ca06250509051400c0d034000e40041c140410b0042c9243ca007006404240880070040e010714544160b0315a88580d40d10801103c51460300051000d944124248250b86010b800e103501311a1740d900301e141c41c02c1426401008503400501142c0c075890720030240304041e40e4050b8018400c90401c5008080280852802188a520009404035200303015074240c030201c1d1226074030183d009a200c4006000b41010303405031031040b440c141907101198000e03c10002500c1e0060312100201840f04038015136809281d041400d4040d008001c41c034103140c00d0807420058440800900080c0c125441c0c40210100d040c0c0040d6500e4105200304030580e603002034500d0b4440d8841c40c1200385080c050005800070700356114100084075048540760240400050054100c8a4a201c01c00200b071014404408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 251161636 1250 251160386 251160401
    0x204030b07021218090604021c0204150e15031305031c0e0118020609061b161502100c1106070207061b03080a1a060c0a020321120c1c02070213 63
    0x300c01c0c00402620ba0035090a40701e1740d41c400b6005d00014a081160281895040707000c03040e20055a4001505100101c03a001c40d941c0c0701e010030304000d1100c3c2d51000c002030301050034624121500078040001020640003003844c081c1a40c2000540355203045856011808418003200d40c100a800c220b5488081e400c140300b02240349841c20002107080f1019400c0140791381c4003001c501d510070018051821010062003080c0c0190042d032008110000f8480c40d14202d02c9402c1e800010039a220fa000c5200708c07500852075803007101000d2800240c0e16184001075520341188181c8094503c58082044070880e0005540f0054450342c0c2c440c4c01c010113884201d004555415200100060103400c0403507058242508a00407040d075040445d00d030a054200440e40c0f98000042518855016103200015030606000c8c0705910313190040d0914410715242c070551880c0c030a400380071900d048550300250f608035140083c0c41b503c1545c0c0022103030380040603032101b010b900907c1d4143d100311408080c2d804411070f188075011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 251162886 1250 251161636 251161657
    0x311060403080a120204050406080c130507020d0e010314010803030403030614060702131b050417060c1b120d090c0b13060525140f0a0b060d0c0302040204030b070212 73
    0x20318060f14007600f1140e501644c03200b1903640d5024440031039141c0c0c40c0c0c080d46002e001d00d50000d003c240700140400005151000d402154503141c030003803120072640400e40a48480341400d0100e860044840120014548452000c08004c0c0001c0081070404000c4000c5020b5030281c0d60a001040d111002c242c03207a040c0341980c81c0d20080410501c0c0040c242100da400988503a1500003541d98007000d010968076080401910008000240c180030f030b08504030700301e5030000c0c4a20050010b0700e0b00d09401c00482c4134034800f01914001d0203460002c22a420014100740a144680e005e03101d101e81003800b030280132228022a900c04640001003a800700d00001d81c1c0b0b841c07440030683d001712890860140c8040d440704201101c0c1080207255443c1c104000b04454018600c5401c1d200c045015120310035051045400b05030900d40c00070710310707040401d001001941d00034804888040d40c541041c98410241c1003580e0009410a00206001050000810325280b0803402c5800342c81e0300520100c03001886100f00450340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 251164136 1250 251162886 251162903
    0xc0509010311030d020f1e0102040807090b100201050609150319062702090c0f160c05010801060503270a0204050f1e04030c11012a06061d0609041a0106090311060403 73
    0x120084080040c10b0181c00d4007d00005203000c3c2c40e034018500317048507a0480d201e072903112107004015040284450030000c46d2840200060f0610340e00040c840c0c0390240c00704600c05844a0b10803e982c0e130a20190b514104107103480541c9501e980f4146001c0c000c000801040d0399661145c01042d40307824645141d4440e4010f1004925581e9551b40003440c1d003011a40c004072000c24040c41103946018081d41c42c2d014020b18143d0091480c000005040890582101080090078802d00002482e01502d4001100da2109141c1249000342003461920494983c06980700b030608041c00b5204c07140c80c00e280e010351803080214071000c62031040c3c920b810381d040d1380007000221201c8411010400788402d40721000320524050084a02e140e04105018450002e001ca021024103507240c204056449600300902000801703030001400d44a0850300e40754000c1125000b0100c08001900300102c1d401d141ea0074403058102410507503100c070b50003003400c242c034003003100e1020402011aa503842c2c003105580031a98000c922 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 251165386 1250 251164136 251164153
    0x3040306090515012d06050a0c02040b030709050a0b091e04020f060f0a03140601050d020304110414040c06030911040b031e0f160302090402010503040c0509010311030d020f 76
    0x500d030040200c0d000644590003264040c2114000c400c0f003483c0240003e070701e01028a28985504260134907214012422594500c40030403040750024113484840140382800c192030001e90000c107018100f00a4655414003a020000c0340c00b40880c2e03c050301401480c3d00420242c0b5903607044c403074001310a40b00100c00c3c10205201d07900c400c0c0040c4240ba03210748040c1c9840200c5841d040440c0e400e4000210408100001180d98007034542c0c18843c86200300b40554610329a4103003240040d080c0c1c455098000c1c501038001000609020400440d9040018060000c006060310100441d090709020754040320f050092000c006000c0784640209503075580c12510500c00200c45000300402845c80518041d050301461040400314010060086803000c201e001500742c24884071140c03030825050762001d03020b180e0303c06021704c0581c0351013a400d60700c03542c20b003410341d40c80c0c8407405d1083c1e0724111548407550000c0c0e210008403c1010034410030403034010507000c803641d400a005007a41c82c1c0c03c01d1034413110703103500c000d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 251166636 1250 251165386 251165393
    0x60815091906020f03040b0a0b0307270b0303310f050d0204090b07021605150304060c02120703020703171c022b0e06010e0f0a0c140a0f09051002030403 67
    0x281d05000920580c40145040c102d03c6103100d480d00102d405603040348000c410408002041d0044c000d010f03030700314068100c080c20004400d203130304134210a0390800c180440031000c981c52940d00c140c000746402400c803a2240041d00b144420712004002880304a0030507140141c0320415000102c2c02d036203688609400c814202001d100103d00d060205a910648911544004c1100c0602e00c0b0701500903035000e0a6549010b0042c807950044a500141c01040420440b150320520f0b1010b1b00e030001d5001c1c101003526408904102d01d026164100a110160b00041050800d60005402001c40e8418094010203002d0f880300c000d4240134440c400da001d41c181c40260b015a450983c0104403d002c1e10500070760340018400005403000030b8061080302c850f618102a40c401d0380030410507004000003c1c000d0085e1811180342464403c1c00b408a20120f500e50f09014400c60086040058051010450a84030148000300500e00b203841d4100320041400e40d8404141030410f60b900901800303e0f60025403a03c1d21319607 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 251167886 1250 251166636 251166673
    0x30f1902011b0803070c0b01060504080a12090806090708070608090a02040b190b03060a090e150c04030807060f050106050a0509090604060b070b160306050a05190902030a06081509 79
    0x2001d480145500000b00c07800122450060742c0140c6465a41d0700c0200820714217140144c4041c3c0081043c000148000c210103080000d03481a031030340c002b40400d10305c0d1401c4415556414103410021250290138100700301d0920015019040f2852036003180c1f038031079480c01c00391105101540c0c000510303001520386d8800342c101382d0010012000c014050203803020418885140a0103079800c88400144001f06214003440c0000819000d4030350300d5400c0060341213000449640b1004000103002d110205400100c4008030181901e00564210402550766504d0340742900007050900e042c1c40240b8544000851250311880582c0d51882254686500e00a40d68040041c5908010b043c07a0b032007a15000c0100b0204640d0010b490424841c101e2421141084116070b614011281d01c004109458048200b207540c1d18407814408640080c1c40d549000301c148180181d40d400d06803c142c00407800001032001c0e50005510820840300d003001901c5000422175842641e443c4207881c610000e034003004400e040c4001a8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 251169136 1250 251167886 251167907
    0x6010504060c0c0b032a160b041a0c07050d08040201051b010618020a09060c0203060a0b063a050c040b09010903060606260f180703050105010311030f190201 69
    0x700701d550f4001d6a2200b0495040d4001c0762009015209034405045244984801c40c0504c0364083d11070341814044000a003610411800240128505130702080a12000b00c24450700b51007903406401d114500700f041c3d10f00c191300002089615102c2d2482002034507108034030b0340c0c0c01070350705a4495103010b2019103c0c3c080d500b98113110b0700465584400010300340079914000300c000c900501002d83c5924100e20b01415007402ea6110109200303940340c0ca000107a4001c5440c1c3e5010f110040b000501920784e02c0402e401e4002c0c0c42d0300342c0d014181c40120100d980410f28800c0712401482003205800c1803171419100903504160380061140d0010b02091128803a40070203420a20010714181c0c0095541ba2122020307200264003900108503c1c10405160010280b29410f2a6203c00d40030306003400e00069100500e80700800748072446030385150380310404006011210095400c41c000b0b0040d0b5849040010000c01701a0659200348940d018032140760501160003040000441d0154002c40c40395001500c0306541d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 251170386 1250 251169136 251169143
    0xf0213051f0b162006030109050a060f080c060a0c081b07060302070519020d0512090103050a020a02030306131b03060806090d080106080402010909050705180102070b04030f0203030412080a030b040506010504060c 93
    0x1d13124400c95511004003550082140e810007152a082c0b001802007220740541240d02101c5025005201d02c51002a490721420340a55003039075681a6903004032900032803104002c3c4490303400224000040d4038801940d040b81601c00964400581d6644c0540491150920080130b9802030014041030b914400c03180c1928074009404400742400c2e998a0504002d01d400e0302c0e00001c000403d2200203541e0500c00c00303174001c4080c0400c624058080e10b02968034080102058422a000281c0300070518060700401c0500e012200c00200601070814050040c0100d40a0180103118200003e00d20a0b400200d40061015985849101740d0806600300c5040000078030076410b20103070380f20001d1040e025208403031041d0010303039945440d0164070302201c0c5020041c0c0d9106045501041040c0700c4000c83c0411901141e0340001035000803260303403000c40c1c00d41c003c69008078052417000c4251001d102101c0010400710503203aa082040301d0340b0230308100890314192450b0340002c1c800d010030f01c002e81c020b06284c81c2c051300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 251171636 1250 251170386 251170433
    0x51b030a122c0307240e07030b0c09040b1002010b010201050a11120a140709030b1e010b070203070504020304030503190c09150c02210114090a0f0213051f0b16 70
    0x2200d882d100c122a40c1c03480c820b1280105c48000c643c42100b548038070a500c842800241c880c4610b192100d424008000d03101c6c0200800010314180035513195849100392070b030060618603d442419401038020019010350902550030b00c800540c440260b4488c100034204c10f240d401d806c0148030065801d40c89002002c20500c030383c2c0e0f010ad2000200c3c01500c1c07540300340159514001050704602c0c080e0a042c0d070243c142d0301102c0c8610b00d840c84414410f40c001c1e0666918900c0680c0703039909070000901c1d01a459003c0350300700f072001003403005060388640150702c512800d4107949a01d00512002c0070440780d259a0070f000051500201b8050425611190400c0440901d00032040c40f07900d0300003515070400c2c842050140c51030f450807215004400e015405241e2542c070090007640c501403000d941c0750340201c000144170007130110810045640e52810202d00b0207214034100143d181060001d0300c0440072502d842d00d441200c02c000240c90a10300122560f000344100814411102d0ba51944d083e803c00c1c02c8681203400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 251172886 1250 251171636 251171647
    0x30605060a030c1412010203160f0203040f08010516110c010f0c0203010f0506030f24060315010906031e0f030c14031c061505030f07051b030a122c03 66
    0x15030f284180000f410559820842c4541080100319805a0000d41e902a0780d00600c10058a181c02c1d02810000d0391540c18034007041041d0940c02c900314411608000300e0075103414404214400c056002612031209010100041c061809007176419540160210703099070b2200c0c001641b554841e1401d14141d000030b00f0314034582c140302d90000c0d0960301880090310345190303104100100c40c07404000c0966101ba0103406030038400341300c0c000200d900c060081d0300915180b03080003007000c68400700301413108800520058102c1c0c1d40c4400d185006002240300503900c1515203c1c11200100781c8800c5947c0c0c05500184c6107000b010703203039000c2da8086488103068850034100c1c080d40201d494140000d05a148000b2400350700c440c0304038240001c42c0c4880d00300b4004035000e10f480000c1d2503081130032240c2010a400811a407030790790903802c42c0c0301e100d03244425202e48256034100d803e9440000180060f441c06444007654902c00e450b0300000c4402007041035036252812040d001c0080d4903241c041010480c040309803468803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 251174136 1250 251172886 251172893
    0x31204151b020102130f0f03082802060403090501092706030204020a02151305060711010603051b041d0d0c0f08040e100f060806100e0d0c14011404030605060a03 71
    0x1e078640308004050b03500011280c4092000410100c041c08140100d05030a900340102201c0c51072850000520201c0001012800c2c405005201c4c0041398580001c00c468101d0394000a4503440b05860840c080713680c984011038258003e00940c0300b035800c50310030b8009680301014a45010454044580d10341d0750388090101c05078403580003c2c04002502d4000700036500b01c20b40d5a21034800d004101c10111000032a02c1030004a011070480e4010500345020310581512102c49401001135910003015407045401082126102154120554800b1101004070000c070444407a10051080446001500400c1062001d54007034002c40510350b01801e80622145449d030784011042e4412303000012800100c40c20004002c60a16166020b01030400c10742034445d250400140640d0005005144904083c0340c07943c07103c0c1d12901e0f851824840c000c01d840811451420281303c3c9030a00d0150b8002c00380ca03081d1030038240d4014142243d0340d20f04280e0952400b4070710749409000304405410598401c0c0f0801000010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 251175386 1250 251174136 251174171
    0x2130c12020f031611100e0c040e0a12181d09010510031514092b0e0103020d020c03071101080a0c0e1201020f0f0408011a0612090f0307060203160203120415 69
    0x13a1003146d880010003240c07022080d444c00c60700c0d083c0300c0d10a03418030380e003402c000c400410b03800038150b403002e0610309100505006650940c008d100341c200350075140600240c43d803100f020542080c407452088000316110a03400b00e00781e03001214441a10720300d401082000803c200c50142c0da0080090000400c228040e003080c031300c500142e4a466190b8400b01043c440880040a047d0080c3c00180e401c000300490070401034060410000b24905056010131214001d0005404841d0400000401d40342d40d000c141c50601202c0250340c1c0319500140c100c0c070004035044114400c44403507081580303400494410381020000d602031040680d828954082c0b2101c500c80c00210040c1581c0032203001019201c90a04940c41c0c00c49041010340d84281d9031030301a0381025182d13102203d0071104100d4005001c1da41c0c2043b068941300b040440032190340700015454003400120b901460007010001130281020364103502c101c0c2e59016030722500d031910303408202050000b817400c840f05800027018000414000700c0444030002c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 251176636 1250 251175386 251175403
    0x20d0305300601020313140301060e040f031101020f1c0b030607090e1506070f0c08030a03090b010504060803120912040e01090b010c050706050c030702130c12020f031611 75
    0xd0034401c4660060307012032140c0400758003203000c0c401035081400509a446038520284a21094012801d0782c2c0c0100c5c3e03d0a401c443d001d40a640f40ca044d613820507203400b200c11960204103500207001c0400700606403106008560b07000703000c000d25901f8503503c8114600d40d484c0401e4801a5260ba4403903050907518188001c1c6c0c070a1140e610b54514076850222098001c072001482c0d03282408140c10301000300e42d04c850580c2c00e801d0b041560721060710810720300308044080c150016078451001244a010032075140c2c10400481d4410040390345540da89106100940ea41307801003900c103400600c69022010103210109501000c1ca0b0110360f010f4141d106020110303442034001c0000640a0801071210060302e0041821707801003071821101018081d21000e40b916102c0c01500e080090005043e969000108103481510b40c00908640100301840c04102c02446400320f65030100d4000304a10310b55040d070b8802d5520740040b0480140c6555990b081e01d0703001d59500726201c000d0218500b0300564480c1c0410240c02c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 251177886 1250 251176636 251176687
    0x5220e190e0d090e09010501030b011809150b0406050109050f060906160b040c0e0403080c0a05090307080c011b0b0a020906040810060e0610020703060c03020910020d1218020d0305 79
    0x3e8025062000d100800800206485070681c1000010400140c20f100000d044551504040d00d08144443e2400041d288070a40034000703654010705803a11105580c400504884211000c11116603030b50f0041d610b000b0288206584910a02605059030419030000c0c0080e620041c452490403844216609209000810075942c889440c010001001000a90300d006032008580c031008a28003542d0060000c0d2000700951031300900810b000440600420980d40fa5000040940c0e20303664a0313811541d42c03200000d440d280020742000300d10b03400c17540300d9007101603040d0004c6a489182c0e0780e2114001c080c0d03115481e642d0304038000b040300155165040c4020400d10a4524001c640c49190013102444420301411103032113049403030302194640e50000307140400c49510000c00f20b00401c2c071741401c0c1d0080c090352402a4000081d82c21038a4550b50200d00000c0295043d196082d42401c000c6980c408c89601c0300c402000f00741d6a2440d400540b40040c054a40c0c940300b85049450110342c1854407100303444000061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 251179136 1250 251177886 251177897
    0x1030803070e06190c0203010b0a0e060a1a0a0302180a090509060a05013035042706032a080607020d0c0309090c05220e190e0d 56
    0x501103a02c00ba03240302004080f0780b440e040ca610007080e07810215000704400103100c4c01c2a14181103460a400104003504003c040f0040183c1c2d404a626545c04101d0b002071051a0381d0348007203502a10f800c000b4008072a908000e904050107540150300950003040205500400700c40c00040c00c0e07a9111403200079252404003ca220700700380196500d4544064240d1309101c1c10320006000102c95140358400b04c01d405101c8100000ca28a00c81d6204408100701038620b0700c0d0303192800c2100f0114030183c120048000150114603c5814400a060050b030103000c84480c080c10009c401c00c4c502446100d071284690100080e00360341e83d075500e2501e8106814140907202c0c400c1000c00701e034452025081c0184400c1c0064042c80c640000001e480f94442c005000c140030b21615107800303141c4154411800341044038410000c1c61150754000e0708a40021035164283c041c0d00b400c0780841810140760b030081790702404001c8602d45542ca100409600105e22807081700303985101c410300c0340300100400d01104255071201c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 251180386 1250 251179136 251179141
    0x51c03020c0d0c0e070c060c1d010c060f05070c120309050604080c1009050c03010c03050105130903022401090518100c0c05120c0c060309031206010e060c0114071d040e120301030803 80
    0x115058079001c401500c09c0c05402c4490404105010a10b603036041c4091902c25040e420760f2400600030654080d00000452810042151a6800c020b03241c000500a5200710400c42c0d050364102d06039100c40e00000c0040e0000b00c08203001800c8a80903100504000d03068801c0b030402001c91404480704c4405c2a12aa0f00c490006012400d080c8a88507190440c0d1809200d10740c100303804034003d0f24030300745041c407850755030b254103400d00d4802d00440c580010902d82444001500702c440c108804130a00071000d0171443c0001241c6280140b0b0410b85108244602078040f0404d404c80041c000c061000c011824400007100381c100046003803210542c9000c1c003917500313600d41c1010240f062918548500c9140141030810501004240c00400d4514101c840d01801c2c02d03958624004a0300c00d540d101985400c070701d000c65640000c450640251821030340d011080c403c281d4030b441c0120350326a030362140030780e074507848112003001c50070030703402c2541002440300403030308446203500c120030842c0d000364000c1c2e80348403000c000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 251181636 1250 251180386 251180393
    0xc09120c05131a0f03030f03100810020405010c0b1503030408060a1b02071a040509010b0c010e0c1c080f0a090e0a021e130902040f051c03020c0d0c0e070c 68
    0x114008070300300c200c0b041040d403401000144001d0f800009181c803510202d80c4003016954200f048072a00801c01c000c007612400c21b0003000600700168020402d180c0a4100310384107050b00c0344281c8049990503541c0c2d151075242a15102881c210141c800b03d02110310001c2e940c1261005c0004000401e0000e0003410b2a2900d0300b600b204907a600080400075010b01c5640c03161140e4001048001d8800c803800340d80703588084541e112428802d5510540d0083c1003503000040e01103070b880143c0100c8450900900802803d0302c241078030380c0c0240141c50351152060041e82401291010440320442c41210410b1400d00d8181d90115035801281005001030807046050045c030710200001a00030b0f59610041d824035160008851b520300700c1045030001103502240c0a01e4410011010500824042e8070841d40c854940e400b210424000b809183d02031218520b9003002078160002c840101505a8042c2080d00b0740b800410200c0c5964920644031131702e50300c40c08140c0e90010131103140954915220402200c4a915 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 251182886 1250 251181636 251181649
    0x1504050c0c0705090907051201180c0302010201050603070605040b0a091d0907060903080409020c2e0b060c07030222020a021b01111507020a060203012606040302100c09120c05 77
    0x801030384c05070342c07220144500000d000681c4010b884080b11014400300c051403440d07004000d1500704880d2944407012682c03e0000098000060364000c2c1d0083c40759070360700f01c00d06580d4001e502c00e40e0300140042200300302011804014000b0040140b401030038540e0b64000170a105104030b040300c3c41030103101b41401000c0300c007005640c00401290400702111407a5460f900440d008900c00c4010103900003c50345002901440501074121455203501c440c42003a08444038402c0014260031295461321200b1541450410103507201100c1c2c0e03200600c21301e4299801d02051903001c1f00031074582c07800c00c10045028005400500080e580701c2d40200340300c50200305c1d50001070b00400b0ba00340c1480418843c0c0c0a40c81804510080340300310240c0d01c40125241c03030000301c0c6811142e42c0041c0601e0300c040004541c10301d10a02c0c00c40642860401c29802c2016040c1c019101d04040d500100960b000f40d807001d404c100144c1250880340c13010b003020040280d4a01629900710444041101c020406070420302051503c030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 251184136 1250 251182886 251182889
    0x50301020d06050a06021203060d0218070f030c030e03070f060b06030a0209010314130201080705090a03030905130b06070b06040207150b090f1e040203101104140316030305031504050c0c07 83
    0x506c001c056a100c3e9410701901c0d88009000e050107503940c03590750029912021411101d00101d40047c90305481c014a00500d445210019400024103212604415500ca4000c0c50b00940ba01070180d49230400c240e4800d0301ca1041c0074001c46855071034800c495410354441000d18401ca0102c640585d490415900041c1140d10300b50345a19207600b0075091182e071058512040000942c20700309100c20b511800b01c141c0300c5009800900c3d40c8000020350200030998004070010480d48150360b15a40d401c4200064020748100d03441b15508114103200030404100007010564010300040c100501d003880507121011742000d00d1085030388281d00d4211035141400c040d00d40e19846800c1040031409402d10840d8540001c0d85d813615064100b4848010500b59034040c0820811505101000c0085001c001110069901301e442407101c100c282d58800c890500300841c03010b0315440542038032002e003070071945d0954940d00040c100d1010080103960a000301d480f44e101d094086d52585610941b40d810502c6214a48640b5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 251185386 1250 251184136 251184149
    0x806041b0e0f0f180d180f2409080709050f13020a050105071103010606080403080705070512070602270a05040204080c0d0f0b130c080316080a020106050301020d06050a 74
    0x401000440c07081e0070076050300321203943c291060319150382c10404041c240003038100303950707025500000040a4015170001c04504e803600030307032420301c4c1c2c1c64940040c4801d083c441e5400b519481520541117071075044400e03092001504040303400a460b60700881c40d161030340d0410b140b9141d4403814404042d0158209070351010f03042e00782160b21182035010030002d42c1c080c49900d0510502254100c2040f443c245405103c034800740081020030307612078006260300c0c2c01b07840680101c0d50785804240080e04c103100f1038404680000c01800203188a140c0038089074000c2c8020b0b10b2072507003400304480e03000c41c800c81d1000e850b4201c1c0c3e002c0300d248040383c104400b04050b0361080c4c0c443c84c41008200401c41e40480d044000b08801c0325689202c00060a01d04403036a1a600003c141000310380411140f003100031040411140504148103c964681c01d24598a2044042541200300c40711003880000d01d01c1001044420031501c00800c51542d1000400d00b07907080800e0b01c10005840712170900041c24100c0c03046000341780 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 251186636 1250 251185386 251185409
    0x906080a0b10030c020705060d0c080903030906010302010c1106030a0506040e0c150310081203070201050c03010806060f1f121a0a03060b1c050f0d0905030c12070806041b 75
    0x30103001602c2001a000c6900074940c9840c03003460514000d0010000421014229954915000100c40024550341e412074006c00c800001240c40040d0000540b44140c0202c00104841e03400d50b001074901a035a194200c0d100c4510464509240e1594400b031030181810110101d243d0920748204001d40d00340030564501c0d60f200c480050502ea031207003800c941846c03410f00115500d070ec0301c031b003070005d849480c0d0001d200920480100361481c41c102d1000b91722a80480c1e000b0050360300c0c0c82c40d41d85110720082c0b0803120705510100106c1c4d01071501040c00d8004810040012800c00c0f6601c205a54100d61a41400e0104103101086880c00740b00f80512009e0541615090000b41c220100141c0d503101240405020aa61012019200d031903921800320030522103180501c8001d03552806031381e0ba04903501450090b000b041540010940541c01d020706075a0014040e091702c00000703080c0002001c084075410705a00c0741100000d4001400e101060041d80291101c0044103090f029052800c0d00590000807103c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 251187886 1250 251186636 251186651
    0xb03070203070b150d0b0106030f0b060301090e15130309050405010803041502031c0b0f0a030206090f060403060501030f0311072102011806120f09050a03050309120304030906080a 79
    0x650110440e102554403c05004003511a40380703440301c031070400400b6a000b4842e805903005004c86891018101c404d035a0b018000c00032195401415944203845c07039604104140018400e1140755004519003180b95400c41c2c40145014100b41903191055038000070780c12280038482d0034564040700d040060042600c0c180301a501d01a6200d80d42c0c4540e01c164640b0040c000f8240100c1c1d88240221082655455640004e08001d0685007006048040307002d13200e040030300c011140302d0a10030618411aa0010407450a068106040c0100a03544004c400d40c84031080001200007242c03403082034041c2d4000e0124100d800f0541c0340141602c201e000c2803d807141d2003104100300906000c40304032102d018400780c6001c000b8081c40103889003c40b6000b8494815854500450310b154016084024007520810501901c051001741c002101c03800c030300c0500360350080103c40340842d014034021740d00044403004940f4800014920000242c10584084000544061003000b009030b0100806801c460450401c02101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 251189136 1250 251187886 251187901
    0x8120c03090c030109020a290c010b0a2108030a0204050d0b0a050c0301030b0c0f2a16050f0603040f0b09010b01020c040c170c0910021606030908030a090503040306021b070b03 77
    0xb021035100e00341c07040450a20702381c42c4010218000000702d0403400f03800d44683c6650340c1725010300310410320380f805102709010008000d01405008202240c0d50754101c4031100791600c6d50102a0710080100c0f09081d000c100008071519180e045c1c1c0c1c1103d00421030502d0740e082045840d020394001910703d0002450900061010400c0c9a2085030025450321300c1c555100301c24070382c0490a002c1d0f1202c101d0340c5130034400d100300000c6000c14498256403041d03050f9070300d0249682c0e540413614018014075401158100014012f400e00e040210f0300b19000e0b60446070f141c0b0079603845640d00b590031104104965103c8918002d1540c0401500c40135090882d424000c0c032000d002c0040c07261000c840e20b910f41b0042c60021900f018a500101c840850001d0f011100c00c00184001071b60754000d01844651010140c503001071403034072a02c25140d145900c8101546182c40b400203081c0076002100d000c1d40c03203000400000001503007a100510110034241c400d02e801e00701e42d030501400d0010079404102e0000c020410002d40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 251190386 1250 251189136 251189149
    0x9060604060e042304020f010f02030f07140613060b0a14010503040311010507022125110409061b0306080c06070c08060406022215030908120c03090c03010902 70
    0x1640c1079803610001c540c08000005019040f02500780561441c0d000040f4418034010340c50034840d5000796000303080c0e180450700440303900852146c03c0d030040c0c10900102513000d51600082054030b009098040e49000d035414142d0500c24203903101f103d0781e03016941d41c000304003981c000c0c0000c689040742c09448091608600c80010011810303417904015002000504042c0984848201010190000c110324a007018000e0340d00c51600301d640c20400160101c3d003000a503000d080329003000c901504e0b03010800c902500f840317288020b40030440b10001085031070201a21075226020a0a000751800f00c0c0c0f0356210100c0118442500380954109030034140c4c1440500c400007000164404181c40c9075580d0481400c04016600180c0c0007040540a920305000074018150041d14200202468150002203c07500d0001140765a114044845540e0050b02a5241c0a540f105845038050300304d151900c4440e81e02e115601004843c20b02a410b0040103205034100100811480000190000c01585401e500090344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 251191636 1250 251190386 251190389
    0x2a06050705030f0a111614060702180402060c0f010c09060c030e120313090c020105130f20060d0609060618140102011b022401061e1b0b0f010509060604 67
    0xd11680c0012241300740762040042c904810a490b00391884011120f201803948840f40c800c80100200350a5144210300d0710000706d4160590003001c0303800301d0202d1202a661100010b100741c0e402502800280c0b035800c001d0240c081c0c0b0360380400001904005c0b5210103800424076800900420140036101c01c0081d400898451070070100320307080b020240d000641c40e4075501c19100005042ca03009000004c1c0800c0720b800c81e054091840e0001c0c070540e40c3e0182c4440070742c0d03010180940341220b0004100b01040310701103c013050019480b42c98080400140c00715906034000001c602d40c03559a17000810503c085403040c070f000303401c103881c180307480303425000000044100d60b0203100224814003c002c80c1d00d038000d50144200c0011401100c50741d04170b03050080c3d1a030b1414941140141c9028004000c0f03804400952416036080b51181c00d403006caa64141e090300e100d24400c41c800d114000c0e0340c04124505240c00f4031400391040e0004541807400441881403460103a03c202c1c091400c910511280b40c0d02d03a4160740 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 251192886 1250 251191636 251191657
    0x207050c040f0209040204030317010b09010f030c0207120f020102100b01050a051b07181104030f0609050106050a08070602072306031b0f07030f11030301140105072a0605070503 78
    0x101c2c00c803400040d80080c403903d2402603100c5c1c0300150000801da080004060464000300c0c0c0d490281c4e0303a40d10742e6a928801d1105140c002a1100c0d8004140350003540201c0055249104507008586c4a00c907410303405540110648207000c09888441c00c544c0d0410080319802400d201c144108070b142030003e003d5008003001031060240108000301030080c61402200040c10390000c0307c5606070356521841c0754411035400b445e030b150300b02480c003c022003d2004481c126640521400c14001d40b50b00e0f044000c10380040112155501c03041c0005940c1c0e00d082080001d8200e01020b8003049181203006072814001b50300180400c16101000c1d03203140258a03a103070044005450b0940c0c2d80c4e465448101081c01c10200043e13181c0f00c041203054001a03c04003600e5034a1003525541201450800140c40c001c1d0110250300d075903071040006008141001d618041e8003c41814a40d0606803140c5c0c450301c0c400001d100c0c01c0014401080754016103500b41003000010010340c24810700d001c841c6d4903801c3d228410b070503121 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 251194136 1250 251192886 251192891
    0xc0516061b051c03050403020d03090203070b0318071e05030705130c050d0f0c1d0f10030b0402180f0603040807030f0c05030a02060103030e120a0f020f10021f0207050c04 75
    0xd202c400d000e0008440300b00e042a0701e104101c4031024000300000d40e8140c0041c85010107040c0304038001c0c80361185c0300760024002d007901494001051010b0307100070140380810002ca82c011428010400c1102c0152000b15804001055158840707460000e0592126209a110032001c20458545c50401c071711110401102050391458138006852500c0781034089288107142599884911041c0c4e4410b92400700c10755241c1c440144803804034141c20410052440e80a07060f441c0f03810240ca0040030b01202140c0b02d040100340d07020351000040880c0c104650891251211201c00d4140389000c07a101401ba61086800c0b03400e50400d81c03200341c2c0354042e03650010240704100e503180015500a020640e10f0350b6100045aa68040401d4025240c3e0320070320080300030420040e1340c3ca00341e1615040f800f00001b19900241284136198840d8942c05ca00f958080c0e800a4140e43c0310100c5071520080000401d20b1341c0c00030b1605105081019421811540c81081c916105004c4800014030104264948400c01c4801 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 251195386 1250 251194136 251194187
    0x80c1606020904090203070602030a231c0b190305010c03090f1412070609060b041118060f0c0a030806011b1407091d060c040e0c07030507020901060c051606 69
    0x2043c020401080e002c2e50510492400282041c0e00100030143c00d4240c1c1e0f69008400e5005040c0c0200158911184620020500c0070740c11074003c000d140b03200c440e44400302081015040d4082582c10350500248500d044c1d0742101402481000d001e149044106898108090b000548a800c5554684c890040c041c032404000307180d0a1a0802c420f0f60460b005047d590751f95101440c000e001810b01050855109080c18412901460140b040200e40e500c2042c405207417071130204580e0380c00c1303048201003540141c050007020340080c0d9860241c16154201001400059901d05010b050600c001b8580740c104500e000c0070480c05100f41041d10050303070340410122491f280d0941c060b8103009483d0829600d1602c1d1034840f5034071425441d22154144407010580d400c40e2284600f0401610540c000e4486010303011022964607108600204141400303890100e00b084a00e50000d10303592020f0b440800083d2102e103102c01880000d00810700c00f1540c0080e20020b00d890040301402400031104020784108440c1d40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 251196636 1250 251195386 251195389
    0xb0408070b0f0a0507240e010507020c13020c0312041a012c07200105070f021c230406030b04141501030e0109150c090b0309061f12030807080c16060209 67
    0x424101d22a0340b0103682500500c280071b004c0146000e814501d0b0960800000c00c20f0980042540c105108000d403042c0040300685502c07a01a510910780b103410751000b04026501410300c1c03800c00e801a440744403000c1500c1d0b42e00790014011001070308940d00038010100d484031041500c0700b08400c102c070b080c0712842c101e6452000c1500c5840d001074401a9540640c1c60714081c100b03041d400070f403240503180c50b441108121003904aa440f01e1041c07100c890202c407400f50014043c0074101c038005480400815940c8581c4900c10a60f05401c1a888000407a4036a034645845180a005400030701001001c1000303a0301d40b008520f05070840c0d0b01b050038103041c0d039071500644186007900300c160030300c1c0c00c9074450268100d8080020700a2011007141000240005000709101c03211800300d0b03002e4034042000b000300380c582c10124502c40032203040c0d83d80203801042c000a5054000340458008a0082d11030203000c2c03501c810003518640004042141050b070401076410740b904040214150300c0c0d0020401a120b140c03040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 251197886 1250 251196636 251196653
    0x6030b0103090f0c0315060b030a0f06150807030b010302070201020a0f060b2701080a02010c06050702030d05090c090903130605180a0b0301080c03010b18130602040b0408070b0f0a0507 81
    0xa0b80905021008950340c0180600d04a10300200e0340300d8039890320982c0407028600120b038414040c25106040400106003d145181c0111080c075030200d00000c0c0e0281d6505090031204a034500b00e201142e850020001c4440d003520a896007100b0a0805510304205075000070b446595915008041d410041112070500c60191b101000b041005800e1200041d9611980c0e10154001603444940680050000c60540c034049030036410543d041c1c650710f11440c0240d89500c00741070000c080d18110b00c0180018004004c250281d6400b07550b190014001c18915403090100940c801400a1056803041201c00760140719600f20604031400d91038400d4840b990b150b038034402035013801541c95004200e294041090000366000310b040f0740380c00c42216140340040081c1802da405d08084140e01c031031565245028008000c050f40d50040c018407016545824681e180c0c001c0344c0007504034443d40140402d09001200f400c100d008050015a0017072814507403440c2c0c0f14800351240012580c2000b602040c0c0c14208240301c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 251199136 1250 251197886 251197901
    0xa020f15130f110a090b04050a14060607080702090411040b0909101104030203030403030e1c120c030318051c0504080712030908031903060902030603060402011809110309060f0c030106030b0103 85
    0x1480d5500749a034502e2010046e0030359948280c890f030729110104a0b1400c042c45003122503e080180c2101030342d101c1d01041a1608540720984110004000c6400166500c0c84424415032160f0f8500a00c442c109088c07000300c603039020f04c06029440540602103000c00004504400600b0010086000c0d021000c0b20502d43c040e40d84002d4151001003000301c03c041c0c005c024200b42190030b0f1214044d4060b46a2441c46450f43e10b20701500347c0849854000c0107500c1804402c3e00755020f400d010655024059504156900504041c0c0c0d441d000f001a07000810015800a20694075500d091400c050030004819281c0b082d5124040034004d42000300402c25003d09106402481410242d94880302c24030a0405c1d0150750090b0540004d103080307004030303e60300c0070300c20b407030191001500a0150303540e44e90041d28543c60642c1c9888083d881e840c03000400907444c3c040d01001ea51300180c0941c0ba81059040e00f8030340900903100c01c42c40d0b1080820420362101c200b06890450307404d0b15010070170040c002c00680041181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 251200386 1250 251199136 251199139
    0x318100c051509010509030a050d020a0905130917071a2e0e0c040605030a0507050d0e011b0905100f031b05030402100e030304030b06060d020a020f15130f11 69
    0x8181c45007124200d9a240075120b0f0401c0d80092000b030346e400d03895546910500e1402c8001c0b8806100003011003034290302070100c01c0000c8c10005032040d228000510320122408a1031001c0b5201d00c40307142002603d600b9042c900a00007406810f215482e91108160308624100c0907041c2c0e4202c00091800d98403d041d0b200c1510308860004200d00361400d4041e00910a000784238a800398180410310301d800c41c00444c0d081f160142d9403a4215103c500510025010140002d010050148454100c400307052081c020255501000041c1c80322010a854001000041000040c055500001c01481d1115060000020181c1ca13150b4054030903c48160b00410f403030705101d5400d806000200801c0c80d00640154029802128020311000442100310f40312055500040e405800c188410000207040c1064075400c030030010030203414001c1e00054007007260041090b6030300581c020354650310701d0303007091248500602c6015200400d510340020451010034050b00002d03d00340140a560091000380903030a00745040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 251201636 1250 251200386 251200393
    0x50702090c0d020f0315031f0f0b0a0902130504020f030711031204030c02120d0509040902011b060510140609090a152d080601060c1a010b07060e0318100c05 69
    0xc405000c0013540003168000301c0c1c2064071080050398580010340d414001c0c0c503482c1e1104c004070030000c800080c11441000700030041d141c0c0079100c840d07560041c2d00b10241804020040c0c64a02e8814800c42664140e81710740e00507403041001950400950f41140e03804052410503c81d040000d4420301e24502c507406800800621302c4061004060340011152110b0340200c82d1030304002040991a52604a40205940803800411919095090540101103014014104020811021064280c01c1001e0f04012580c0c02d03a140c040124010080c0d80c6800544035070101c0c59003200f03036580428002e114402449102e5074807400058075000305500b0907201c00756000c5041081c00c2d61440c1300038160a40c280a00c640204026110a62400d162500700440e00b420001f0304080c2d28004003580c2c2014240c03400d544890103140007950040c1c00d0031a00f0f008100850416984074120305000084940300c18020140750030030042d03600c81c000e000c4000c0c490102d04a4a40040c080301d51000d50720901205001000c601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 251202886 1250 251201636 251201647
    0xe060d0f0507180507020705191706071b080d020d0b03030a110d110717010207050d0f030b0a150e03010b0d0503091801030503030a0905010f06170715050702090c0d02 73
    0x8000b0400004907251a0750b086600842160744400381c0e40300322090001644402c80800c107274034100e000c1c41c012547c00c8410100d41c50310382540b004a031303e450740014015030203403080c01806640500314901c110551004058180e505603501c00703c070b104540506010507004074401c180d42002e0b500011840000a04507681ca825000340034218820f81c030364030b80590003504030b440c102d0740c000c00400200b040f442000d0035078142011a009030543c624a68120a0342d401c0c480300c0b002030010008010341c84101e0700c0c1d0401c4400e0140c3c0080584000c0b9202c00e001d0130440f4400c01401240d5600c80c4608040c03820a41c00743d10841010a00428000d1065580252a10070714814404003000924104805889084202c0c032281090144940c0a11004026034010000141e00f02016482010951b10420010030060044800d010650f052034010411010042e425182041010040701c8020014001c510f1916280d454003d881d5010781400030b070003100903000082c2040f8500044030b582d1100c0320021074445 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 251204136 1250 251202886 251202893
    0x10509061902070902090d0209090102090402041e080123090a020a0605040608060a05090718030b10080d03110f0901030207080412021215160e0d0605190608070e060d0f 74
    0x641d030454a000580501880451008824022202c03000009041c10998540c0e6030f007400040007005061660b655070a11081d400b1383c0c1d40d800140004e02908210000204101c205014a81165400043d01ea85065268005000d400402c4c0c5541003840541c01b80e03e07980e0507401401c003120144002d5100e03100a81c045150380c0c00c200908150703415940c0b060403a03070383c00c400d1050300c1c40c65014255102c1448000030b42c855100b80e442550b482c036000d9170711402543d01e070b441c2403010a0075104d0385000219500144000d420030094000030411a180034400b0245031417400c81e540c880c0000300d41c28000c0000e0a00a45d0340a90115100c00350310480155440c1d554901601104001d440c0881c4508240c0c60100031454001a00c140117a09002c0071007895122003410001c45a1189a00014021303080310105599031400c0b82c00040c54041c0303102081030714051441c4600290b1030740403454440c0c60101c061007080f000043c800e00707840c40d0143c4030b4110b44604d80050a55403076000020101c181850860040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 251205386 1250 251204136 251204167
    0x1505090a15090801181214030403020304060e06120114041508030415021f051003080a02060a0c0c0b010b0f0c120702030105061e0409020a050409030513050105070b0c0901050906 78
    0x701c1010b90b0ba000900c80d102c104450980310382c00c2c20618100d080b2030980d404148841c143e002c040c812401e1410110a400351403020f51341080380c00390050b0304045410000c01e9001150000308110840351030785003d04600b0030080140040c09290b891100303110520481d621194081420303901d4030640342804503620700c040c940c0c0750700c680074441d4440080e004507001c10380001110a043d9039039041e1440400030f840940c40041200030003c4c0102c111008002000c9002c03a03004210354042c40d40648003034549080f0450540d1981e004800400c05d2402c2c0b04000705038905c0c51141520b1441420555070301001c80000198000d8502c4611140250742001c070701849400c000b809424401d600030b004580c1c40b1000c1000515414940c4001d01182018900a500c0c041e4050010184000e0084031410b884d90007103011140100343c01c80206800065440d40350480309040c8004140900c0e0040c40c014940da41c80860080240480000c4040860390110503801482034414201014080c2529100b03050903a048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 251206636 1250 251205386 251205419
    0x30408010902190b0d0b0402120910060816050108040c0504060e0711010209090412091a0915040501050f0c0a05060403050a0f0201060b191b060606080a020309071505090a 75
    0x3c40c0e81035864031010300c08104621400c4a500600807400c2207143c84460f809001485001a0700c1030b1f0030424143c40d60310103112180a461048018620b000e0003082d2441128983e81041c40c0590051100c001c070300c0e1104407014107484003840c3c166140e448600c0d0062540405802c120b52140c01c24034085003e08030502018030411260741e480c110410300c0ca056034202d1103007840c1103401601000008021030010120078000b252039160040e08596504c0b03140201d1043d81c03030075006071940000c540c011841d0503440d51070b8031040b0034500340c0350500e4400064441d10520396108001c40c404900d8070406442880313203206058000d425140d152603c0d180042c0310350301c103500360f50102d00b10903420018244140700d036106591628140038508140e5200740003414000f215039070200700300f20316415040d1600404644000f44210300108400c0c0c14008054803403013009042da030400b0300c140100000707110700041d100c088450502e00007201d01c40ea010b0407255441032000244c1c0017400c0c0d8400080b4421032100942 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 251207886 1250 251206636 251206639
    0x609030a05010e15040f030f18090f14010b1209070315050a05180607051803190201030e0d0c1b0b070b0109200f030603031605010605031603050a0320030408010902 72
    0x184c002184030301c0c2c03080401058801500183c0e0819580001900800c01800300e036a980c105a0b40200600740100c050030071a4114007407554940b04501084030302e5002e40c0f2115041c03c0b0220b50150304112000600740240514040b8034001130020a8294800340040300180d40c00c0300243c0c0c0c0300758400080d00082e1400380d0340e04404a14103000200c51041c00044072071b008008801801c1c0a45031507400700c92039001030340e444600c0c00620307252107100d035010030901c1040007840a00507040c1d5460b0001408403a0361402558481d0010a001e108095104a40c2e801da41d80c031031003800c103200e03040e400000100541d070045201501c000800c0d809108a82c024981200c40307075107081c810343c3c0000038150402000c01c1e4800b10703011400c2c407c200c2411030a0700a1603102c0805001ca0b404c018900d24074122003044c0d03001c1030390345955541042c021414107004a001103142240850320132882c50351042d958142402c806001c12180841752640e000420081815003c02d000c2181e40365030b00c44e9078060080204d000107d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 251209136 1250 251207886 251207893
    0x7050412120e090402030307060b011107060207080f030a0503130f06090b040501060605040510080604140117070812040b09220b0108060d0c030b150307090204211e020609030a05010e 80
    0x102c14910f041c034030a5100340c1e8060041c1d8104070f8590780d440003400c0b0102c005810b02c440d060b50000700710700c1000400000e02541c1c0c010700300507180c105214100414980d1013034694004203c01400c1c1034010044030b81014140d00411801141d81c01d210000c4210440010025810aa2014240f0100314042d50040c1c0c0603200800c02d0598800301601d5030320407803103540c1d0001c03019203805c10f9480c040d46405512240180c40403032511442310007040510400d8124042640c00c0c012031f0300702100208407600c0600303000002042541c283c030b980403040f8011403161640d46040000c02e6501070f21005051340c1d034805080e649404540c428103204010785901500c160001e200840050000c2c5056000c51088a0304110184130103400d507115418180e2005084a111500364040351807961810030a1a0080c21140d000603281c90034060619807201c0d00a1040004012008190011078032050700824100002c3c0c424103445002c61003c6005401441a019030601600032070f64140001034000044410001054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 251210386 1250 251209136 251209157
    0x81203041a040b01140d0c0b0c07061b0204021b0a03030c0314041e020307080303070806040b0f090f18010204080304050f190b0703030e03031302010206090d170705041212 75
    0x101240d00c04980c060b000b8140f10f401000542d010303030b000d000e1300c4801500d043d9102d103042d10340d404480b583d50b10800d01c0e0131000600103240b4500b4051400581828545001d2680421103c0d04034054200c801a106660000c0c98244000e11424800301c2c019050060f10f0300c1d83c00a0801400600c1002c1040000c00d0500798844640c801b100042c034031580c1e0003110965a40151005400d00480f100703c201e8152003120000316100c0380401c0513501c10a0703280c0c0e4030413051904009000580749910f2030940103a203a013a014030f00d0b586801c0107680c400e0400f4100c0001d07a40d402c641204c4000d00310143c440d554070020b0003089207003005c40140281c0c1e1083e00d2405c002c20300c520134480121261003031400c03a0407009100384a81d4240c04000c00344039000c0d281c04501c40c004030742e0359421944155000c1c40900c0024525004550701800b155a02102c40c8000e02540c60081c070b0301602045288581c2d001c0c07240d4400001c0e84003030003102070303a014103424000c204100006140c444881c624107480400403507500c105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 251211636 1250 251210386 251210423
    0x403090315060602030409150803030109060f060806130905121303060b0a1206050a02090a140a0b031501321803010917090d02220f020c0604080f0408120304 69
    0x8074803c44105500461800340303003208407802003200030605c000c880345c42c1d040003821103c1017004c1c5002c1c1006c150001401c52514010044180c1d155102c2803c0c09280001c0181680d10304400f841c00380c051106c08030707800001303117052400c1c032107050543d9101c60400f0a002200c25560040001540d2042004000d1600f00720200103061500d0b02ca411910080c62580e180002ea03960059501300d00032100240c1002d544200103000504139400460a511400308220054a0165002401480101c03003981c5181400305403903409224988056042c8040025500b15001010110001e030140d02c1010706456640b412041f440313540840025a144522180340041c5454188104407080d540420f050003901d03100381302c190b065040b14840d584d0204039010424007580f2074100101e68003010351402c000c19080c0100510848007003450b50490107205001c01540c1c036000080c06500b00760080000c64a820440204c00c1d994800d68100c501c01e4024000032a02401448014601541c440e0340084ad4038000400c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 251212886 1250 251211636 251211641
    0x6181216050409020609010f05090a120312060605031302012d0f020c1f0309050a0503090301140c0307031805100b150a170c040b0301080d0305090f071511060403090315 74
    0x20401380d8001400c02401c41650b0040c2602d411012240c14082e007441c46100000b00d40d0b03042c40c1d01c22298007403480d25000030194022584010107400c24010049075080c6040204203000c0200822104000301e28140d041d68012000701000d0491502800c03000d25a0020155103105601c0e101ca000c5071500b03401480490001c0ba03000d91000d00540880981ca286405041107052100401c0042c5955082d0280c041002407140c1c1e100b141c0074000a5545024000501d030031100e0351880011451560310a012801d40c804088a030400d4052a022540264000002030f02108001004045104500701c0c0c42c50721969400048410404543c0c08800304080300000e076441c4609070030000000c05420450202c080d1409055070055010141d5508140e200c160a079604e902c00c0c1c004400340d51080112158240d41401000c3d800701071030018180300200850141e56903040360081c003420001c080320036441288108094107024214a08881240c2854140905000c3d1280401d81d00b824040449440c110400d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 251214136 1250 251212886 251212901
    0x9060f0b0a12050604061e080c01090305070e1b1804360c080114060907020d0207030807110409060504150e070e130503120a0f0c050405061812160504 66
    0x181c07034005446030350909542c02008024080355000b80c0d208030100d1403215170b5803603e5401c2049001c85844504001c0041d00d0b00c0040b554190400442d01e109000040300800d48100301c64010707800020036110001800c1c010b000c01c00200b800c48d0342c00701d0051a80c00981c4079a611202c4255000c00c0321174280e9a624a101100301d5084803041059171074452a038481d5a80d5180881c050201713481019200e541c0c0d20b0030b40c0c400c060100c0c281d0141030705201d030f5840e007507401b2504003025000810760038244441c0651161002d10000c0c00407030303003c00c84906012441501900202d40240104000501441d1800c01000c0a5400341e401307034019200b8940c6100700d48a44850b07410000000d0034114640110000c140d03000420401c0404001407154001443c200007611859120700900300c110310f0070444001c2283c20008903400c90508180d40302601a4014040703406403002502c8540d42c4410f0010110303510801208150307008000340c160140030883c0828180448000a0211000300da5594104020b0304ca00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 251215386 1250 251214136 251214157
    0x60c0206040b07142d06010503120d06050406232b06090204020c0c090f04170c03070c091d011104090213030605010803040303170f06061606020409060f0b 68
    0x104400e0206001d0480980803140c40344c404031010901000d1614141015100001078409400c2020500d642c0046070b4201a20841d2008000b0344d803501000130b585001c01c1c001618404000102c001140c80d8170381010029100203441031003034030350b1020111b004002c43c0c0107144030f20055030511801458801d103a0b0740d0300c5560b0410310035031202c40030904070721111488003264000d60f10768441c001a02c0314000350110805140c05000f83d603d826040c459000002000032242160403410000003502c4c3c045ea400740451041203540e280c00f0f11100c011700d18820540040c0c40f00c05a0440010f01450702e030010f81e8540c50510150a02c1661045410300765030644400d00c1c00740506210034080d02800d503026045400203035800307228055a0b5103d500c100c4d40e003070308180700c00d4000003022310070f01d90400803003400481da954203003902d45803c00241d90610702c00780401c0c0c440c400000c1e905c1c00e25074004110001140d04410b00b1035442d1364840540000306040d01c50a8064294440000b45040c94201600e020810 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 251216636 1250 251215386 251215399
    0xa0c0608071719090b0105030105060d0308070804030905040f0519060308090f06210412050a1b060f020a09030204060909021003050910020301140a0905010b0f07140610030b01060c02 80
    0x400c460b600d402c0d020010018400a42116034252001c0d040d400340300d100350302544407080340e941400706044c00c0d91001040345000390f001005140000b948441c0955205c141c9150544140c0c40b01d141c1200c041e5101d81c00315510504002000d80c061004d9800746000b4034a2501c0d200d5000000390740682510b40030303c4060005803050018a10604207424040c00070300300100306901e070441c403460305000d10081480152004540c0300420042006040b1350f55100152400c02509200c86600c004080c4c614150400b03106d07042036061641000802e4000c4405040403450a40d141c141c0084018003407010b071300c0264070071810183c1c0010400f6082c45080c005540180c40000e40071381e82c40c03096018250180c0003800510601910403007038003081c8059400380485400030101180e2143c02c10003400c0c2036030086184030746400700420440c0d0f0003108403248001e4000e4100c0d294421401c03c2c280354080341d42d094030640542403c101e0701104c890030100669104a00613072003641c882c14201d030030422400c0000d401c01e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 251217886 1250 251216636 251216657
    0x60601021e071a04031704080d14190c050102181c0c0501080403020c09010e01031a06030d030b1804080903060a06150c060e100203090c0609030303040807020109030c080a0c060807 79
    0x1003011449002551912a414540307a640d40d0b0340d98100138a80506c1c24400720102e418002300380180190140e0140c00c1c0745c201e005a030105600710191003245a00d030106100d40000103526401400c194425a810000031911840240405030149440704c4409200307410021246022054815010044540240340107c0c450308090055482800141060b800d6100d00b000e15040c0ea6100c004890280c03584110200c615455490072150f5000042c00b0101c1551450003000781d2510002748001c0904801c0c58049052101e44c00801d800305041e40d9407105144c000402c00081c80703000c80080c1804101034007291442c1c2d550340c031a401214464069542e510041004c400f0040b4440c0f09240005030295000142c8054800801031500c0385422403404003d40200c00c11491320410f00c21030821101c1507451503c0d1a01d820002902e034480244001d10300c1101207402c00035640729034a4080a1075015510914080d103802c55169500701e002070031039404522850104103548030340d00e905c2c0920007540f00e821110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 251219136 1250 251217886 251217899
    0x21015090b030f1b01050f19200c100e04050103080c1903020a0201141b0d0e0d030207090f0b09041401051018050718030309090c0201020a0504030b07021509060601021e07 75
    0xd004440300c1d040050511200b40079030030304401864004070000100d031003042a80d82c05400209030490b0741c4c00240003075600e040d0709d2401160a4200400484903400058000d0301e0039142d0f894181609a0040d1500002004000140009121615168086a04031070039040c0320071244006183c01401a00321400000041d40180c030002900011030111303600f0300c0089201052510020011554107030700ca5690302c100e198110051050740302d0195100c814040c0107880180d940d002c18440c240c0b01d85e5862076012807051700e503403160401d0b0f10000c00300071060038076060801c5004420030485581d9460f200114507441d4004801100b20b03051901100310a403014011075005040082c160320500c03000d903038110425074104c40504007030340c0b00b40c4400070124180f00101045403007048a04040d0b82c810001c03d1541e6801000746c401304c80d44541c0c800c1582d683c21500301e00f44191184514be904002c08288003d9007004503285104d60402c3e401c030f4890700c042c440e01201c04081441c003d0010303002941e060005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 251220386 1250 251219136 251219173
    0xb0a0603051513060507020a03140a0912080c0d020d140304170304020d140d03051005012001020c030a120c0801050f040903140703031d031801050901021015090b030f 73
    0xc00c40b43c2c40c0c500b0301c1c2034054840c035007521300445203000160880102d00e010960032502803c801a0794440341c1d414150328800c00741c20704029004081003101418406401c001d0300d54115080c4400798400c1d50b40c0c00c9486034011f580d55000040c4000400c401841c0d5028000d600030950b48501d03000700c0701a500c8a0845040c01c020381c40600182d80050506144c2400726441c00328007054002070600922a44008160040c01c441c0050300c64001c503007039980c0400190b0380c0318091105401c000c4c218508260020b40c101c60082c07045032000c8cc26804003040501c40d05800517020b00c0d00b4600480103000803107a103081104d03100740901445030b020480d1502c00c00f0a0625610204016101c2d041c40ea0310444181d981d442950458001100041e071540c00c0340414003c4809250307061407130307234006504012a040c0e0304050822071041581c1045000714222195a02c00c202c00c3c500e503072018030104105080001507580b000c030107000304250541011040302083c1400104001c4c14100c11001d00071104c103075041c0e07003203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 251221636 1250 251220386 251220391
    0xa08030103080318070f06030c021504171e0405040c0f0903140a0501020c010504110a0303050403020d17070507050f01140904090309080607020102040519060507030806190e040b0a06030515 83
    0x10304184040585245210400011020b0714801e045446d59900e0018010140c0d04080103900464001d0080c44070804130300000d20b60031a80c0600244215003c00601e546c00f40500422050080360701c81458110010090040080d0783e020340c2e00f48100004d40405072480552040e240000078a000b00070404201484036800d0310110030800d60300c0740381c041d071501d03401d980000c031110b605650f54005200400c1602001c1441032607040d80c01c07000ca0b40c84d40d10b010f1b007a80140d10010340914142021002005640752040c3c21003000180384076140c6003d801c1855617801c40b0b000f118024010340920410540c06000343e06025510000e06516003000c0c9820320020b4408100c044090000605011503113035810710280388a50460341c00180c8030b902d08001c000d00201041c9203260707881d00111040c400150311808a030781e070b95058144100c0301e0311184003003541c10046440b410041c1051542c0800c0110000e19400c0c0107501850003191540ca171503029100b00c5070507110060036a440480102c1c1c5d010200c01c461076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 251222886 1250 251221636 251221651
    0x504051e100f06090e0c0d080306030304030c031103120c0a020112090611071e03051b0c120106260d0f02010f020f0c060f041112121b0601080a080301030803 69
    0x245504460360754503042d51100c030461011640c54071403d0100c0b038084e209410489100384010000303003a01074040f41c15201e09060103041c0c50300010000d40f054400704200c0b802141c2c031101448a151f41ca0514600000b508440144a4003a00c184d45140141d800152040d4521030400340039280310903801540c13606404205028015107401c41480454498420440c0031880400502d50300d109034940035201d5203080d074003040310880c0110f440c0c011a034020f0940300c0c1d0105480700d0554810a044004e440c06000401c0a43d100c160b000141303004600c103400c49004c84031140c0e81d0380e407800f10755003107001c41403509007520341298000c1403202c02c1d192084503219a03440c518000040c0c5444a101104140da0010300005640b000c001541030304040301700107643d48041750a05140321410250b0f114241c0040071208140304a0702c0300020103040760305202d01400d1203c950001d03607507100450030035030314901c1c00d5001c024a402074100005030b00e00f01094101c0425403001ca100d2950f802c5643e00e03200e40e0006040c1c070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 251224136 1250 251222886 251222893
    0x317070203070906090912020f0303010b070609020a030809123c010203010b180f090f1005030f0705040c02060103080d15031202011505010e240708030a1e0504051e 72
    0x100d0f0600c40c441c0d607018000c01d40c000310312001c15082c50790702e40f01d0281e0901c00b19402481d114082d10008811749044d188410141503640080e41004009050121070181d40f00d10952400070030007100e40000c210058007902c540d0f404031030b0407903440c0d00c803144076001501c01208110342e200780da01a288804c0800c0d2044031507c42504008243c2c0c2e089030001d0300715000d024030004210007054076500d0008101081141d1441000b041d00c8040341d41500003602e00d1010107035a00219401c0b111030818400500009021034880d00b90a8003041d0f43d44d161849654002c918019104011910128038a0b042c0c030b0300480e09500c0d229100032a00010b21880203041e62003204680c0c0480020300e03464a502c0d0184069001280400c0b140c1200000d12101e0342c4414103026140080710400d03110110315051211030701c03102c40300640320408504168405c054000f8403a040000402c40d00c940164014459601502e050b120359100404001048030340c10354000e031066000d01d800540e90316250202c00c8140c07900c241503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 251225386 1250 251224136 251224139
    0xf011d0102270102070f180501090e0a1721040605100302090414160b030405100b2809020403050a0b1b1207020c1306050f040c0816090e270106031707020307 69
    0x3c9140d4042581124100c0907c080c60902502d03100d0240358050510020100b01c03886100810907644e0a01203002014800301c00c820f4118220f111060700c4c1040b0408a008400c4095100003240e480c01c00c4404aa04c81e1070080071500708141c2c0407800098950280c407130a4251256102d02d051540070100c4050309d8882c0110415042c18480503c41c01003a4041c0340a0b12402c1618000d402c240d810540540d5203841d1512400455031051104441903115144214001c42000710840304403155401047d82e26000060000c104100000c420405a01070100c00600f07880304194945a240d10076420300601c5000e008509003480042092a0422070500442c0c401084143c041a0398032940380c00e190410760359000c100000e05252000005c0703040200c800308088400c18a000e0300b084809040811004c0d0107900001400340982484e5010b0408000918424a00765040510701c5800b01030302d0480c10b01960301418001c5050042c1400e80e82d00c40034444034042054911012a040384e82d083e641031088450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 251226636 1250 251225386 251225399
    0x1504050310050603010509010506100f02030f04061808060f0109050601110a030809250b0a090801090b19020313030305090118120e0306041a07110f011d010227010207 73
    0x941c40700c1c40e0200c20045960b2804070f08260856000402100c1d1507410081040403a40d501c1100a002d2a21404e02210901c0e164400300d01e940590748603400c0450700090702180e070b250411000050b613100d045120015580b90207919480700e01c151142c42c0c200c40d814005108584554100a501440601d88108821405040549404082002a4040f40700c01091102d8840244015242404605420501038020312071043c40740c40740d84201e615214012510583c4982f00e0001c03c03004220301e0000b07204000c01c0b406c000b185082c1c2a00c50341d0000c2818032801442624600036a8030400100d40d04100380034442c1c400f500600b0004100b40c056546e591400b0240d03458410b40300798002d008203070440e00047e042030046c2c800190100704034401d6000d80d00308000103601d001c5004510b0610600c6982c43c0c0c40b00341c000c0c0c6102c2800d840d414846c0c0107160344044030090552010b503086c000010605291003501e6803c83c02c03449454900b060111141c1401003883e025000101c40340b0300c0610455003140d56582 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 251227886 1250 251226636 251226643
    0x7020415052409090601030e0601032d03020a201c050705010230040510020d180605090103091518210e0f0a090606020304210305040515040503 63
    0x246038480c0322108418003260404041c80c80d5900e01500680181d07031090000d40003140100d00f405032080540c440019444e900c0383e00201c090008050440300b9558481c40e184600d0307070398080c509220041003021000c040014000d0b02c14102d4068015000300c0c50030f601c5004945041203103440101e13000010080060310380f40310842c40620796003100703041d1248920346542071400b1584480e045501c4100d01c008044107020200015011200c5003c05158a501044420340501d5101c41c5d032042d01d1800c004100c580101d42c9030701440446c1d461600000902d001141c0348410b0b40140400100180041009940a1f5000e002c40c1801440074041441c1648031640c00d4034016040f011400b0403456451040020350381082c02c1c140094030005103102c0025800400080300c80100b544034260020740c04c2455100c9810441c094192103030f003848202d0725010040d54a600c01d119004000c40d0722042c0304c0803800c0401d003009100303030f01d03980d45441c10b0714040402c04042e20304c00427507071003410801000a40e541e040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 251229136 1250 251227886 251227901
    0xf03020f061b0c1e0a0201020f010203070806060705010e01020d0209040b180c0a050d0c0f080c03090d2106030506090d030911060c0715030902090105180604020309150103050a122c06070204 83
    0x71002441d450171a44002030910349120174a6003580e00510a02200c0c580180720560311483c00e03900780e5211141030500d1070240c5048200107406500c0082c4140c076441041e001030072214400d43e800e0006902c41400c2c4103a110700000b041c04020b01c0340001c6007003090305100a1401d103201d0b1401ca410000d46007001801c948180780f03580701180100070740c0c143c404c0c2c1102400346c0c09403039149454258604100c060380c40c1d100c28250760b410040000c2c50580402c0d01c81850341e1407910003841c20802d0340e440e0303d080c40d030300c0c20280c4d2021a24820b41c014064501c2c842d00500188550260006110008034000e01003140c1084040b510103008042c4082052010b461016841c1d04607560040383c2c440031401404120f0006810080c05071101d0100003007600d041020f1560040420b4900581d242d680b02d10040c24030301c2400d4850040e8240030000420b01c0b0000400344a10707400384003540d000c8e100414040d56070f1800c076110300366581e401c120014009240c40012240da00c00c06801a850100036a001604035401d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 251230386 1250 251229136 251229193
    0x4110d112112040608060108040c030f02061605060628050904020a0302060a02010b0405070f05070b06010302160311010507021504080903070b0d05150103051005120c0d0f03020f061b0c 81
    0x1240811405a1100702030386c1090081c240b1031060305003901c50440300c2c51300b0f02000e01400b20401140c0c085441d420115544240e4104180c00303810114a811900c4070030554626214030b980d0341d4012114015404c11000128070410306032400c1386807000340000102c000308281d0380f101850b4800000741e1a03000082c4806000d5034000109100d0000c100401c40b540038001c10100300749800344001568001c8100c0d81c45035000003400500d81d40f1900100c002c0d1003001c91b5940d646900c001030f0820076410102c0c00084150640091000303a0391044201d0380c031508030068550150000f4082404600004002c16009402400b42da40b855114801d95501e40d0107981403040c42940c6508100c2401c0311104641c3c1031020905c0c0920250a02800074100144940605031040700452078203808444108a020b1410741c000c0d0007040130720041d041c0b95220240c4401c06402501a10107a00801e11003c41c50500c1003180c01131409e00707502c01d601c4140b03480d04448150303c001e115900300c02400a403011101010440c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 251231636 1250 251230386 251230423
    0x61e09050304030c0605041203110c060a09050918060f2517070c171c05100612060b04150e0301050f0a2a111009060504110d1121 57
    0x55032401c159485015170001042200900c0f060082d200d0412441c0c50b1160580f130f06d20b40c03a0216070400740c00c281c030310115140e00ca0400180c42c80c00c140c00c081150100c80048070401d0705603a600c00c2c510418a00c02c1d441d040103410030000034040110025450742c0017500c890340040d4034482c900311214031160505c054000310b41000c2d01003141304402c04070141c4c841c03624a00300c99003141c990b651a110071501030040782042004201020700c010f845100315089146e2400c144154202006607115032001406200300040c9c02c512001d103022074500883c002ca030303880150945810f00d040c2c2c1c81000b00205501c5001001020b40600c03070300d5603090184071300541d01000811014107003030385c560088408180e4100740400d42610031f103404410b020780000c00c000c0a414006444407451101604100249014440301454004e100061040960100784982e205040d200c0f000da840303408021003100c059a004008881d03004462141c1e0401408074900031200001b1058061031b12511607040981080080c4003260 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 251232886 1250 251231636 251231639
    0xa060614130510122405030a0b150f06130806010b070807060902150d0c1220030c12010e0405150f04020409210507150903020a0611120901020910080112061e09050304 73
    0x65015017400f00802c8210300404642100c1e0307503000c081080c011300540145014070550401912010808828650014040c5603140182d03402600b0044c0310703001e450403a10a260001c80d6280c2204110350445800c0215182041c0b615030310368025041c3d0030403ca801420074666881403a000e04090255240303111004a540b633442e2000614007080c4003801005207051203007206201c1208105607000c01ca0703102c426543ca9581c100303220301512130110f100c81018100000099074154400240d8000c034450029580c2c0402050448883c109081c1d40e081940341d03451010900511b4158013020700300303108200100070080b20781c2c001c4819205482801e008110000b600408110310b0321111a81d202c1d0040d002c110500344c1d510000d40d070780c41c0802d00401d42c07903542244186400e15a020307260b00c4031040d80d690130f0318a4642c1e00103000c0d400000005029036113100c004c100850044011a0503201034024030045c20b039180e02c44401400c0103800c004240c200c0382000700c000459a0080e0b810b101e003c1d0008503640c4c2e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 251234136 1250 251232886 251232941
    0x80127060f0e04031d0f011b02091008060c07080306091003061806060b04030b0610050c0a08040801051501020d030207020109030c14090c0705330a06061413051012 72
    0xa4042c0c085208424007002c038170910f07035a0f4540217580544081c64072161002504010f903d80030243c01e80039600412820400007120208401c43d400c0d07030000c009441d107a458210003951680580324004000f201d003840040c42c0b500386200203d0303100b0207e50808503c541d4030745800301200e107181101c00d00840801c550000740702c800e00440c401440a112420314207072070742d01e500d02c043d031025011503c55482e8101030391380d4a1240341501c00303000c8400203550700c95000d4034041c3c03126803192240c0c0b8029400c280014002e0658210000380442044e0041c00d001500d0300d80445c000c0d030041c1700407418815410070100c04516208038010241034410600000381d1051420042056402089049072100400041000800114540703020791742102c448103020010020400402503070105014607030017100100418030800b900000121030760307500c40c19408004886040b2041c854500500140c001b45502000b10b4107141032510a0000396252410071440201350f40c4044e141c0c4a01802e0604d9400c2c0b00300401d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 251235386 1250 251234136 251234147
    0xa0b0103050325020321070c080c0f040b0d02100309140303060406080a050703020607020d0501230112051f060e0a0f11030106080f0a02090d031101050106080127060f0e0403 76
    0x40d05190a80c00803602d4984d00096549884030300d2904c0c101030300204031900154100c2510324460344580a8800c25459258865480600300c058600c00c00c40c400e151441803d052141071880d100113003255002030825002c0c000481004035641c420540e855044601107180440d00140c2080400d0103599241469410041501c03400e0300480781603000100c1e0000000d500040801c01c40c2d85c151017480d105c01c00c50002a801c5140200f0180465081104c0d400850f0500c20601603e45482c15080711245d80380c20140d03004104140c03006101c0d50088000b1602c16a002d03c60290080050324003240c842e40b5174182849000c001c4c0d034501006a2940c0340d400640c0c060307000f4418000c00300e81c002c90031580340c00b1004000b03076000342c40c842101ca02d04000c1103114807260101d4140f030802401e9008280c03400e2a0040030081d40a0410300c0c154030304000070400f14400c1d200c4c0e41c1294401e1070200d017070f05404c0d42d01140c030481a03400d1500c1d07140d80d01000107540204001070801820030485c68510392404d0f0030003500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 251236636 1250 251235386 251235427
    0x40e0906100b0a0f09180203040605010803130b030603192f0a03020120030406091d150108100e010609031a040201050a031808070609021f02030a030e0a0b01030503 72
    0xc400a00c1e200c1403140c51103803800c0e51401d8510b4900312101d107640c1c4600380c4100300c940d0402e080481c44503e041c01c0051080d002540581c2c81440100b2407680e03202d0105442c0d0080c855004001840114104594910b050103107802c0a4000c5c16581c0e5104500c0d0011645150b146085400c2d45441c03e81d1500c051a080501480d4041d51202480ba84014000960a03030b40728000241840b070140c3c1c100b41101a8044002402044a01107036034075502d506000c0c0c8004914070075480c004182510b41c0d042c030b85900c07981600a540700c003401038020305140019568400f00410441401024040010324690601203a80c02030071251207003181c03381141080c02070841c0c050750003003240940f04203020041c3d0740700c0112100c2040350302c1c00180c04184003102805d00501c807040503014010204a00c420300c1020b902c042c214500c22250b8204c084107005280034610641032050001d600203010b00b090300c038007982203001c070940e030f540139607034840095504c421000400b070f08203485540c0040b40345400d52001c034683c1d09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 251237886 1250 251236636 251236651
    0x6020d0302041a0f220510030204120204180507060822050706211104080c010801030c030605040804031203090b0c120a0c030b13050403030b040b0f01030b060c03040e0906 75
    0x103240608102c4032041e541e81011015030706180004168681075130480950b20702506001c85410404070f082501c0c6400420340c06406e21031506a504140e00c11300900c2103a0803a0480401800c0c040400e408000c01099025094004441c034218100c000680601422024001381e44a42c010fa081c05403229902c0d420b18408100d0010340c4241c1c0178045440040d1130030850f0001d1601d070080b6016a10861030509100e000d040c0c005040c580b00c0205984a2070140c01654440d504540760a641d22004403450207080c4000340c03450f04515000d01c00301d4040c0d000182d01c14010204a03182c9560790b501d030a80c200714004903d001960f03a0748090100103c540105400100550000b0700303100e00808485081000070340f215421035a00d58442055601903001090510401005509030414000301d19020707100c102e0301100003e10304900380e43d0600d41803061a280c0c1d50f003c2c04030a6001e90760401900181254500701d64810018000103503e840100b005001402002180c5034060400180c01c40c034250f00903000c0c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 251239136 1250 251237886 251237891
    0x2060f032703091302040906030f0209070315060c020a0b0a0804060506060406021e0a0203030a110f01020415050c010906061d0f0606030f04140604080405010e040b0a120c0b0c0706020d03 82
    0x1c011512002066800341003048403603102031120040d058000348241e51050507207505100e400800d000c880e40b440440c0a000b0398101404e80d84224040b01142c82032100e500c1a03c00d2282c060043c9445004000c0003544003030700b1006a69201d240d14000f0350070001008000550442c104020494a400307525080407003625454101030a141019484180041f004c9488031444107a00701c1d2041c0401c14201c1132500641501d94817aa580401021039101000e0208180f050321040c808001341442102c0487d0004d04d4840c50b0059562021900d42d070103007010079070540d2142c0050340802c54910521004042c84103104000080030001100f0081e07000748506412040e00081140c4d9071200070850354840a141601e6449903240c1c40d0030640101c058a585c006803044008100030024502d0041040c0c070402d07210705017042040810031090302c20002000d0f41010a00300d0400c01c4900030002e148040d886105801c81013500d586d081007494124890424040e44801010404590180665500151a0302c0e05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 251240386 1250 251239136 251239201
    0x1b0203060c0d1e020c0609060105010504030209041406010f0f060215040609150203090d090e100608091011040501030b0a080d14090d060b0f030a05071403070302060f03 74
    0x80d226400142000000c040000d00800b840040758851216111070a404014408001282100a4000c13100380501d91050300003040d044400024101d0407110165209490107046500b4060030520140c421030b0b1020505400582411050100901a204030451005003d281001c03030040350f5000d174440400d5400c0381101189900d4411045030303001c1e8010034042030b00701451500c0c0e8041a20218603c103154400720500880c0a03012076908140c0c042c07a500c1c11405070703c80006030354000c0162820003400811681c100001402035008690180000c01a01c81103c08501a01c0603500e030407584e2015540001001d000e69a0940300d0601c1184003529001d0741203042200e11a074a802c850714840a00c070308140001c0b010b2501c05d0480300c0405000d00480c0680702d03e4a400c002400c100000c5d40d11400080a4052040c02e00180c442003060b00030000346210303460070b001103e2002c89250000d070180140f03940403004d6266940180036a00c01c626496a881c40c1020800000c0d21040c0752914182858058 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 251241636 1250 251240386 251240389
    0x2706020f040e160917060604150503070e150901150f02190812010e061c0809180702060105120d0309050312041506060e0906130608010615021b0108070513031e02011b02 74
    0x43c0907505c1383d800d035000101d00845807074a41c810318181d07003d8bc0c2d00d481002c40105508442c040c1003802507204114504030142c0509c01c100e00b0346002d01030700403190035640d025030215103d50810103c000c040c6c01074400c0c05020080b030880501da942e0065507403c8001400c038942001440d42c0c2d0b8010a040701400c906401c060b000205102110024148041c2861007403800740b080d04000ca54944100425240001940e01000003003031400701c3d158001740c0036450002400c1e080c902210710304000c4c1b102c0904901140c5074402c0d8000c007000d09055844d0320052050031020411030500c070740554082d001ca03060071441c2c0714940e010303102c0a40007507041008101400b840e0b502c41c101059003003e012240c50500500d402c0c03c41000f0080303603001d4034407907080440c00108100c900303d002000c00ea69900b6a0071056403600c40b1950140d0483c0050300040b4800000303841540b20b0310240c1400050701c2100300305a9a681c4513544c40130310721180a44007c0c41101060215a00704d281c5110184c6118030524000e01710380c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 251242886 1250 251241636 251241643
    0xb0603010e06071805040204090e010e01111902030c03070c050910050102030706020a050d06060908010b09010b03041211060702010507110d02071e05061603032706020f040e160917 79
    0x40c207803c01c0c03080e081520245918014902409002c001c1e100b151a250744507260000b6000301840c1303441d0395203400101403065130103004908100c4141b007412442c0c4500c001c241103508000d80c045004501043c84a025500000e00080264501034a054110541094200301c801107019000401940c8429401c2003181d0300441a142000c3c0c00580058640070304400581d04d61040c010300c2044249082000300301150031400c09001d80b185580200030301c110000900450074028054001501410700000c0c0014030030035030096400101d4500080d00c11803110219240000607540301025035100ca040142d01580a252000682413402c0140019461050041d4513000c0f10302802d615030440e9070500341a0002c4012000007040e025082590700c0d201001c03200120641c4c810100e000a0510700400b22224000003617131003018018038070603982007142c0d440e280254096142044019010700001400100294442d441b469803442507454070440340030010a0043c0c6a04000302c10030300e03184100079482001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 251244136 1250 251242886 251242891
    0x31921080a0c0c05060708091c02070e0903070206030a20030618090c06070b0114060a0f0f1b0605070305100f1e03060c180905010b03040308130c0801090b0603010e06 73
    0x405000449680b11102218038064041014016202d40b800b0b1046865001d42c0c1617214070030300f0040e200312034aa002c620039000208111440140e01c182010b011281a2441c802c0c2c2001d06101101c0c9030004d580e0200d54950400ca0344062443d950312a9014001c06000c144000380c034540b11514a0340c030700207000903c01c1c1c02c12800060040029400180000700402c28554512401001d403900c84000d890005080c0b102401241c07201003030b2890110031400c224059503141409501c513403a180040c030b102290051090104002007000c412103032000d108514000ea07080038060b100200c2c0750703d01018060207854006c4c003174440701075040c5820004a81803200e40f07410740c0c0e1149025230864107900a040140c03849504060a11032410740400c07602e5402084002441103910190f00100d56100b901c0804c80b102403207941404d050802c0020300103841000d080340d0103005190490506500d03626110482d000a4001002c41c2e9518003038502408014007040b075000300c045002b03011a0340424442620342d03101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 251245386 1250 251244136 251244151
    0x320106020303190b0f1309110d0507150e040c09091404120e010e19050a060810060f030f05100918020303160507030f0503040315021306050d0b03192108 67
    0x30340030882c4c551382c4d55810034200d000c0c000b0303d101840c80030384400381c0040c005d5580894400c0340c0d9040c0124079007004003904d038000da00703d0040c002c1c643c45d10014050301400d09040c0c800300407001e1040c0e81d850b81c45224501d410680b598425654505190ba55800c54101d4450754580d91a4501004001841d080310fa800070030051500d00c05d010724500041e1072014802011590100e0100d540b4091000a041100200c4031308481601205664044c103540c0c4440503070702c1410001502d942800b05902035210818113098a02c1c001070044014040a4203e690941e0115040054008100400c840c01c0c0241d00c1000503c525081c035809041e800a552441400078034141028101c40140500030300384078000003590080d10b282d0b60b0560900d055901c0b680326000440e40d00c0c44180e01c603650300c0100e10a03561b0030032005142640c1e050911105440e02d801c60360600c11507644540010711191020702c0480322150300042c404c5420000c03403800c14840080c550603047e030f4100764840400096404001c0c281c00c03141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 251246636 1250 251245386 251245391
    0x9060405071e2606070503090a060b0f040e070608011a09190b040801094110020f0309070b070b01031104061a0310060306060507021332010602030319 66
    0x1542500718a05151940803600d8a01c2d103034419000842d03901490f00d00d4020040590396655181401664680421782e002c40c03842d4400c01c800d00001742c40d54000205d140b0010306840d45010542d0004042c3c9291400d0080c050304001c1d02040340507040b89510b030140641c0c1e040c1024014540080104a018084141d442070f00462154030304480100501000f4182da10540740d80e46d03032550403d07806042c20241c121610074040404038014102220203801098442c4d40500d561580c2e45074000401e28420031840a074003550703407901c0e504e80c01480204200c02c020400e5540364508440443c0c14042c1c1a440b1003800b8108104400000303500400710b40c1902c0e4481000380d528184940890014031036500306044c2030030448003404900308400051403140451704085800c4503142c0a0890580b400c074420240030070028040000185401c904e503441d03400e116000050070041044141c81d01c0e00002c8120700c0405451005001d90302e006103d028003400050000714998202111005800b25020b23003550f05099 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 251247886 1250 251246636 251246669
    0xf040f0c1d130213050616152309122a010e0607141912050a110a0c08091008071d0114070201020307060c0918110901050703020a0804030c030b0906040507 68
    0x103001c05070035005060301400300798440d245c141f120810503000320b40035503241145651450040d109400b07145100229056010402c1c034075001c03078130a201c0001e081102c0c14050302003100700e40300111014003121107070100b20503c480001a012601e542e2410011006a410034002e030304030329800a5403503000120352800404a009803a10452140600d42c042121803602040d2040b001c0c1d400708503d005a010035904109641399221240704a5034000d00c4030f60b419505202c40b552460184000002190280e50700034600700b60031002400c04400d0501c44000701e0601014403c0d00daa2040c40e201d415800e03035080e080f03a5038904002800c0000030b01d51040445400082000459100f1300036603122580c802424013040041410141a04a250080d1410020400d000c04040d00060181d840300d1080040f54030b02c5c0034142401140c40d9800200d0680a51040101240c00a803840004000030350080d541034041c28110310706400c503000c0140918041c1d500100912010a0001c40c00350102e9411071120000362 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 251249136 1250 251247886 251247907
    0x70f050a05060403021b040c0c02130e06090703030e0105030702250806070c05010f0b1c080408071401081b22050a06020a1104050408070b060f040f0c1d1302 69
    0x145400300018528002d22082c00201a0002503211580264000d41b01d24841c000f400e00040f125103450800c00940c08060880150401d400a4030714161044000f190881c9484c004ca85400c1c81600c00710b01075805183d04009141e44100501c80041d02440c0c010710350305110000a540b05002550070b095040941514400e48140c004410001d004190a540d85860101e60190281750346030b4064540d5401c1c444050a2020b50f8841d0f1030360303484003c0844103100340041c4500319604078400300300d80290003080003003040700c1c1c00c0003507500178010003e1400e0807010030000189902e601800841951100c2c418095811040c0d80950b207001d03120307a007220300d9514082040c1d0078580e800e0707114503008044000e01040a950100780c20400314040d0051224240c4d0300014042110b100310340c040d200001c18043c401c00101c03d01c04094020034020646070381880001d0000302110304460141c040944c0d40c06030000300a030046101080340c0000c82406003000504404104010010364040b03092941c0041c807801003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 251250386 1250 251249136 251249143
    0x301150302090d0c0602150105120d0503090708060f01061d090105040510052101060f0602060412030905011404050c030a17090d080a0215010902090315190f020301060f0c0206070f05 80
    0x7007a410403c4c000d10980c0c2d4020103034940150000000041c07070120000f0a9508040c40f84014030080f54000740740d444c603404812161754001030700003034030307030050041c00204400c00308121350056900403a600e0003549400005441100e00380d242c00c065020000340110150b44191340a4110f0303d00f0764011070301e0795940031100030020907a003181d80c1c031400214008142038407605150350100c01004c001c000c070544408441c100940b40344a0700d40144d02c00e20004000500c000c030700c8110314409040100e14441140d40b06403c0d9078002204000400032101004148542080702101d032841c140e000d801d0661440d1104d0700042c940404003034104200143c120800c0d01c0d011b403107980f00c0d904101c0c1c480d00d500c0980c070001d444200c02c460100d0020300032070011410076030354400c42e4200a0002d00501b04030343d003005100090080100036000c40100003e40c50307ca0411402850750350020101c00681c2da60400d04081c181001e0400c010342007005440c00500140ca4100c11a840e440d0000c900300005202858541e00c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 251251636 1250 251250386 251250409
    0x903020a15091703070e010207080703020613030c08010c27031e08040e0402030c10080402042013030303060803070c051e06071a012408070e0a0303020f12030115030209 74
    0x110031000f400e001d544420080103140034059980d100035036058610012a40e641c65802203000903004007a0800c01890402c00030101113080412a0780c0d4580c1e20b45842c071008030030b54480002d80c0d450312081d40c0410361016910382c0a0010403540c0c00188240401c86a0f0107000e8007000b02031140b0710480710380c401e1000c0c0c110020307039601101580d50340380c07288000c200030101a1070880c00f91103482c110082a180c1182e21000110701c0340d030ba084042e07036280c08000242102902166152800303c4181507075041000042001a01243c0036102807451482d00030100c9003181e01006054100f400000c0c000344404038480c0482e0400c0741c03500921881c1c41007000644c1300c0180307d070b030b4441d2000074407101304042c00038440c07080402c0e000a40180da903038288800c1c00030b2486056800f002e070311034810b18529000d081c00c0380e00700301249400c41460070440c0c04100208410f8109070003503030040b601040501010081d51480840c1010311904552400840c615601804518003082c99004034003c641c54440d45105034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 251252886 1250 251251636 251251643
    0x50c13110a1205011202220612051e060903070620031305010b1008070f03060314150c181c060203040b01170607020c0d150501090606120903020a1509 66
    0x40e038860107610040c08040015030600c540741c3c1440c0c0006002c4140045e2840312640140c580c6035121603c1200681e01c40c1090b00001d182c9540d000040713103008541d100700f0440380c0300c0d900030420704119001a1603200600f1078030b1240c603030183d0200025007001009a8104a612020220348100c82c440308980300121401441d80c01c0201204010110204880c03024103940074070000c0005c071035103e0502248002c2e8802070b001140d500b001080040d40b00e948160180034540c90300003600c0d03449956066004103d8005d06070b650b40300071082c9031080300144a80b9005400c0c01500d52130944c170030030110301c10684072840d640b191001402104544080071030790140360382d12001c1155603141c5441d01c800907400a0084448003402e010fa4044030346000034500b40140c44540081008000b05400c000c10645031602c2140c080340c0c80c042c100d0f42812140a840d000c3e000402c000700342641061001816101142805299181070802000101340c0101c0e00c0300072160485000080f0700c0c4d440040320090083c0d0070004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 251254136 1250 251252886 251252921
    0x11090105100e15030a05040213050f070c02040e0a060b10080103050a020105281d04021e1312080c010b06070309180905030a0314061206010b1608030f06090a020304050c13 75
    0x100500d1420781c4070030720a504c03c580c20203005c1507400d41c0d0401c4800854003080c0880c8018040cc00190050550400741840104041202c040c0079402c54103000062001701c0310380e13884902d21081407914080cbd0103903600440c03400340419803461b2200d980e10a001c0e02d000c2d040c040009003103410141248480c48403100030100c01c1c4810444106e000304400005c40b6100602e01069000c030700c143c5000c1c0211032842c0d6040002d1030401031403c0100209602540d0180100f01d5407010004001c2d40003018170190501481c2c0361a290070b0890303400741c20340741c84030816445440c04102170340c0040d8101d031040040d038180d003120903100400b103100e40004040c01d850140c041d11012a5000300c841c0c0c9504900241a103038841c01245485500904c10703904960003031040b083d00940014440b4041c00006025244100146101019115110300203941d1041e6107000103540b07500c0400c100c5040442180e0b82003134042c1c004500c0c5240984855071944e4031000c0039403040346031010010b029039813a00241e180c85a282201d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 251255386 1250 251254136 251254141
    0x1603021308071e180b03072c01090e0607030b030106050a0803070302010b2407020604120b041101050a0504091503050303181605030d0521070305010311090105100e1503 74
    0x1400d503152101d11907008549004245101c00320801c9842804682c44130307640c0400070384140081c00140600c0031405815100e00d810010705401e0320059585191408107040f009100c4031440f9180c0644144c000007410341c1000e908006c240d2000030b42e5a4001060b00c0c0005612880c8000203000d0a000e6001c0307607202e159110045240320703012005200061098000700720259050f400e0120040c080f062160701100d4100540e00380103006c8000b4075526200505283ca46600c8074214542003542c481d050b01d2031000003041200300030360079070900da6140c1d00b42006418411a400000c0c041d204600620000d0b80d1100c0b9110803101c491010940035590000c26a40c0321300e00041e00d0041100e4181040c0307114440d10990307072202c01a000c0510309842010f400307000030800b0214256032543c060b80c1c40d8070351a0035110a0310040e11004040b14002c081c903a4010445500d141007404550220245240c404c01d1350302c004000d20396880d400720b0045c0d401070600d080f4009140c400141070003c00f416002149100008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 251256636 1250 251255386 251255399
    0x20c150f160204090b06101403070c030e030a1a010b090603130f020301140702070e0c03010306051003060e06100501030209131d0a051533150c0c0909120316030213 72
    0x602c21401074804820082182d0022100240aa20342c11212384040010440d414425144003920030b0103828503241e0f52601c8404603142902e20441641c6a44814051418941181c17407140d00501c03400300d1541c103041031341001400d1071201401c0e000a00e003038691000e0401543d1f400b4200300d031b41c006000700034055100e50b4101c011901143c10400502400da00412981d034410529070007144d4140703100c3c0c1168290303a1081d00a000c0602005070b110901f640000c00108176005003045d52041c5d0002c1c140c1070a20000c02c0c901031010b600f0617418940107100c0300304e03203880314801400031044420003c00c030500d16400c0c441500101d10340e03010740d602800c00c1d09010701c039000607040381d20012602150070503510350103901c0c007900240c0c1c820180108820303820740b0441c1d0741c07425050300302c84020844c424400d100c402e43c0c00d01d40e020141c6004260040c415164803403515a10b11a44100e1500140c214500302c07490050300c03448010203502c941000c4200c81c3c9803651003507058904e0512590304803100d0940f10513 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 251257886 1250 251256636 251256653
    0x103110703093609030c1e05010f09110f040b0a03080c0712051e1c0305060f0105040b0706090807060510080c0604060e060901030e120a020c150f16020409 68
    0x70200f080c1d151034115204141018030361600e10500b60f0240c54036040c03040800001d0101d009003601004000202c0b8004a107103550050380d4040347c907684440c500c42da032900c80c1c03d444480541030b640314607040024010800400c03154207071000c2103800c001109441c0c1c00040c010186070010301d8009032491301c08400c104030640107090001c0340f88202c908155031555000500b1a202100030f1040d0000c0f203074a40e0030400020101010705016081d0740046428080c201c5e40d0030341c500c4c00500042e0301d400921003a402c0051900070300d20005e1a1180c0b5042c140404a01c0c680714400c00104942da403020f118061029079000c1d1ba0110754046400d0201c0d0901084c4401d4100240c01514902d008800c0700d0b90b0a482d0030780484003210465103d032840a041c94041201e1504500c1d5524107040d15143c0745a0721030001c0c0450031a00b80d10703000f01d1b51a80140c071300003868061264890340c003031500c603094a50b811441c1802e40701c00d00102000c1d40d60343d1002450703c44000351108802504035080c8801034041249030f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 251258992 1106 251257886 251257889
    0x3020f061e121f06020319020c04090f020a0b03011202090601030222060e01030e1b0613030c0e090a03120f15030f02011106010602100b010311070309 66
    0x5281e1000d280d01140101c00c0100300381c0200061802c2d003620a0100c0240c540e40d003036440d0708104001c0e58a1140d000e10300320b505c1d011054800e4030703842006561000f6002810a2141100714681001c3c003800403c4128481e00760300740042a400440400d5904842090345a807074001070750b07001d00c071100001600b814101502000403003583c0d82d1500502902950300015804200e1400e00003d0201d034450504034101070400c01000d89403040042c1c200415940d00d404040315880000001d582481203c2440f920038030300c10400070510010035602c1d0102c9800903c00480350380c580703010b15244c100300a00240440c0039880841c1765502d00390300c0103003105818000003c2d407c0070b40d024040300c05c00590003190008024468103046507400810a01e92030540c000411b4154105000651101d600500316001180e807044c601403241c0c0b1a412020300d0380b90004405039990114280140001d099 = true := by decide +kernel

theorem cover : BRFrame.Cov 251079136 251258992 := by
  have h0 := BRFrame.cov_init 251079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 251079136 ≤ n) (h2 : n < 251258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
