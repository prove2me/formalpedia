-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1371
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:37:54.113987+00:00
-- url     : https://prove2.me/submissions/9ee0ad8f-5a3b-4f89-9854-fffca74ffc68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 246402877 ≤ n < 246582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 246404127 1250 246402877 246402889
    0x603240b030d09051201200904021c140105010509010f11120c030d05060303031003030804060605130207050c060f160c0801020f1b070501021209060f0307090510030c0206130602120f0105 82
    0xc03180741d5090b494918000c7e166401d0420601305c070610040c640e030700e072140c0c0320100f402441485480c45071681c54450b8110240610b4209909140d8800400c6019903070b5480190b4440c007070030238040d0105001084585240b4850440a90451408812a0741c4148082d419810740d0780821a8401d458000107140c0881d04010b006036030304800150011841c52502c00e01c0f0000b00003071404001d00f0000048042818010607811500c00707004001c08055003149031a003980300a5003e070b482100d07140182480d810740c500e4811305468142c00b50321101450190008601c0030314005071034084980c1040000f0100d40c1c881b00340b01500000303029641e00f0f551000300d442d1010005644a4500502c0d901141045c00140d0b408286524803444080300b15481b02c08040000d0141d001d10241101142c802008222201da403000140b0100c510540754081c0445069204800b40d6481921400141e4001408948145100070b0030030700e4280a200010b00b06101000560f086107005d036a03450070304c0c000030010704c43c0786800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 246405377 1250 246404127 246404149
    0xb06040302041d1c0818150a020a0221040b090a080a05060114060703020a240f02090a0608010e01030209130807050a02010e030a110d0201110a080d06090603240b030d0905 75
    0x140c80d46000c0c1d4002c1c000017407115100503da00034010b02201c0b5a008100308014840f040a80e114503011f441c0307003a160b04c000030341020384100014821003603031050b103e001c0020140c00303505001303a89243c2420020b070784155500c5000003d03042000540f0002d0703d810184081e0070220b102c1c02c080c02455140911052580070480001c52040d00b0810030840040d0b00042c03011203240e88480b00c10114007a1050b0540c08400c4502c0c2e1030006401e00718960f55103402c90b401802021400c035113803c0d0300d54482c0c0044030070150074001d0000792948c100042c805440c113411050f910907500f1003070424000465444840f1381d0001102142c41c1d501caa940b6030215078100703c040007008000e40051008a0341900e4003050b4011420f40580600f101e118088156403040d0b40b90186800c00304200c0d03001c40300c40d1406840b41d81c452182440400e00e01800401c20071054041c0030112030f001549000e403400704520028032101011361400e581c80d41d410070540306440500c410403171848142c44100c1c48514020500540a1702 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 246406627 1250 246405377 246405403
    0x8040b060603070f0804032f160503120708160f030306050609030c09060d060c0f0206101d07030f060f08010f02070b1611010f02091c030905040b06040302041d 70
    0x6100308443c103a84226865445801840c00f03038000e0301c513402e0a03070b4200c0d2001200e100e00170780002c9400103a0300380c0040110910401044030180c12288070304501000300790041951540145103d038141c1c0c081e00014102c00760180150918101d010303005203002006030320b4112101013800940340249605840f642000704400e46201d0f207040035070701c0002e8407100340d540038621800c038580c0410680c1e1680c0341c080c10015441107041207091544035001e030907481c0d0022072a0040c0324071000203c11030a01c80c1d4003402c5900d5941e00032500d810714003400c0b20b0b000004220317604140d0340c0e00304c01e101490b0340d00070361004140781c0c0b00010490b800c240310030f829211003046010000e4010005040003680b0302104650201300031003110f03140641c4110480c1e001c0020080c0b42440c0d801e2502c01c0940c125954000d1400f458121108090001524100c4840d43c2400c0c0e07025010a8580e042017040742030036000508a103000411040c0703859141c0c3c2c0020b0440d5428000c00204825010350030400403000c00043e0f40c4954 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 246407877 1250 246406627 246406639
    0x1030b010305060a150c051603022b120c020a030803100f0503070506090d050102030a050708011502060f0c090612012c190609051e0114130e030903060708040b06 71
    0x1410801191310022240f2a5440e1001d40105500b02c41d80300d500ca641015074418251051085264860f50324120540016485191100030b01078404400c03990703e00c1e03000d800054203c44100c03140c40f0805034601c1c140300c01c0c0038416034500102c0141e9035680c2c52400f45120300c1469880b81014030000001a0890308100008400b1100a10031590b001800000b151412104c00c0c2d5140c9132000801d0007402c070301c6070040c502d40c0003100384401009650001c0b441446207a440681c560f0740c8218411201000d44011000f580152011565101c041e42e90240d10811407a141d5182a40ba400428625440074086066400c110b1006114104503c17a5400c00c580c040c02080b42101105141e0100407040034248030480d0b07441d46418040100550020402061807410803c17076072500071031904100c0c090a020b1840291a00c0010402c4050881e00250b12500a00500d417420540d0101000914910940a0051000b800308000654003040881c1c41160b081d82c4000310340c142031a00300d454860117461684511 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 246409127 1250 246407877 246407881
    0x21e03070f0809040b0a0e0a0507030b0603072a030203130f050306010e10030c03050102090f0415050d02030a0506071808030307050a0507020a0f08011a04050103020913060209190501030b010305 85
    0x20051510021a00c1d00316540320303034482c3e01c00b000a0080182c40011031b000b00904800007200d012007140700748218030191007405180d072184000c034119410640c0d219440031003800440c2c41680302d4201668043c8031243e011420700644a40400b5103103030702804400681c40001c19030b110741980181d0302d0081c04140c48503c1c48a003403000094460b10140159140303d1401d100059903041090300100046070000021b0f1043c03a00c1c1c0c00c0080c0070303500200c5078602070a03048140100f2800c2c148504c1c0020044210740d00784090410040044a44016206a03814401e03010b84070007040d82808074030700642060719400741180388600441d44d0031050341e1190001c2e42081c01002015500141200d011040070302d00a941c1f040e5500c0011810790711a0000d9601c100d036480c0c049171000c1f0541c82901c10403542c2d002441c034044484108401d8a8090000a4211350844046078441010b07080c21440750384074000150500c40342c0c1020405040325500d15103d02d0032050b41c20025540c1500c9000c003024002e1801b4050346c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 246410377 1250 246409127 246409133
    0x203030d0c0917031c061e1508060f131b030e06072607021e160e100302090c1603020601090608031204021302071703010f080303090a061802090403021e0307 69
    0x6406102c5194464a0203540d01c1442800b0b1507000764060801e001e100740700c903040071f29005002c83c80b40c0035100854810400c8508007901600c0b07003c0c4140802483c82241010305418040200e9500076140b9070a600c54401490005000c82650038a0700c050340d001035020f082c2c580e21841c00c05e02030846030920403180182128405400d130321071030965210f125442203840b8100100d01d01070041590b4a4500703000100f48101070b10128109000403010307510303082d10766200c82989140100585007001c0c2c94101d510100300609240b400d2692001c0d01c40c02c580d0801d02c4d902c40142c5400c0a003a4102e00582001d0018030604003e4841c0602812204004604041d103000d401b404165002e0300c080d104100450000016241540480d040705500098404040303030b0810b03024170260002e0180c032480380350b001c074007140380140002030328441d4409100400915016844036401051007440f4510f03c803042e0540c032409a00c0d100610350140d440b99000300a05852140240340ea407104401c80000c54104002c00004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 246411627 1250 246410377 246410383
    0x20a03230a0c0923190f151412071701031a0603210913020304030f050c0109120c12080c070b0c0405190311030303100306020d090203030d0c0917 64
    0x88020301d00c0000403030668821050300c40d039100d41d00c0082e0040076881200c44104032141206040303403041d9415800c90b00008a850383c8100c2d28040c003021142e249100b00f00c0e181030007180d521600702c1070034800101401035585030b4042d0304c828482c1440c044440280194198455802442c019081010010340e5045985000d80601e401050308803400d800400f003040c03650306010798200e080c01090000c3c3e1a01161a00c0c101e1900007920141c410030018107100308804490084a10942d130550300d405000342000c0090311030f44c201084202c441e40d07075200710400280c840b1b5003510b1990029111103003020014500f0070040202d05a550041007102814400408180b80946440c0f59000440314842e940302d1003011403d0040b036022071740c040401c422041030f0900403039010041d02e002d050340000b1101013406041d500c0c80b0541e101e409040b801d400800200c0c038240d000d40740c03a414409002c0741260b459000a4511f0b041000d100108958031070303d81d0705190300850745000a04072010405c18554203ca021780e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 246412877 1250 246411627 246411631
    0xb0f090603060f0406090c021c0e12030d02030c0d0506040c020d030f0221040b01060801050a0501050c100908031005010e03060606130b040305010f0e06090c1002010f0906020a0323 79
    0x100403400480812883c0d0340c0e1003940f407458207018000b00060ba965005100240c134655001c0409402107051800300b45000910000644081c2c2d11350a400160f0001802b00703d0302d800c4200803890000340142102d501127400114002c0219401854540e82c00c2e205000032103c020b130146104a2078071a0710002a03030081800b504040080c1000143e064281c3c02040180c416083e485c1c07a50b00d0300c03005003200c4c0035034052814081d60003814103070f81507a220402540e80d00004c0c003d0b15031111000c0c130100402c0d071150000380411506142030b124420104440c1a0a58411050840d00381c00302104120614480604030360041c40246041d58100d043c2d00042501c0c1c01c8080c100364000d01c400244ea9001e40e400921541c01005501516541c599a078108203000b00503030b01c484c8003079a0505118484600001694601501800c030181c080702850300e003005041e504000c1d0f20002e6540380d80c0040144042442039002c11400f9443c09a960310b070809008040f20055000b10204584444040d983c5d000150030301341d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 246414127 1250 246412877 246412879
    0x503030a1a0612041b050916080601170c0a030212070207150509130f0608030a08070306050a150809070503101a0303071e15090620040522020c0d0503100b0f09 70
    0x2017842d030b8800c1c0880000d220036422032a0419401e40234042180c83e002801803c440d0f5595464a40380c4070580110380180c1c070b035624020700f503c5001c00314849006032802807030890f035a410010700d0b1624918264079401003c903418009030700000e40c100403d40d2680d50a1124410078035100d4035094507140060081d180702d005407603030341c2e50390000300e8075929a80c0c0c00540074121043c1202d850740314543d4002c0c0f041d8411505000000d042c108001410308103800d102c001d80d5050520303080c0d100c0c0030b0f2808860004000340541800e2190b642d001811740c4060040c91046000150086081c49a42e4140903484001c40c00c1c0328002d42c010442c040c082124040403250403440c1c00108103c2c0030311070910002042100c6403c202803460681c0450810506520500692161000a850071a040d2100308071a0041e486000d40284005840b0340c8021b440907403400b407096030303880018188071800d03204c20324219603200707246e01140002007442030601000201e04000e103012910140703003082c00c01d07035422640203150000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 246415377 1250 246414127 246414143
    0x1e0c01091712030a0b09092b0c2a060f110304060207060f1202040e04050606040905030a051b071514070201020c010f02010b1915050f030105100c0503030a1a061204 72
    0x4a0740074002c070f8120318542d2400406c10465828000c00f45511a04118400c0c1d00e9031041c05803004080710310181404d582c100a0312071340c41811310b90301c801003110303404440a00c28415000f064810030480c0e05d0f01c0d0000d881c0b40d0307540300040001e85801400c00c05410702c10300180c0c0d0041c001001819030000d012000e07a100752824200d00b0f14200800e80f460501948008090381c00401c0200e21510340c5511580314500401c1150220384826051004031204000081d0283d00308002000c0403a002d0001017802121100710000700c040507010903424290241c10080c2101b4440d041d5101891f8070030702040303d14809200e141e00e0640750750f00103541c9004943e010b5050103030140007045128002e41c4003903440c0c00d01400c107034860030404590070003100490003900c5c00310080305602d003907485c42981603c03541494046618030b56420039041240d008107040e40c0e50100100c0700500000942d040c00518001c0a03038a0001c148840903004004d145800c10420038000c660910500301114001c040040c0c00c2604800b030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 246416627 1250 246415377 246415381
    0x501050918070305030414152118010e06090606010f0807120f0c0903021005040501090e100b07050307050601050f100e060d020a120c050304050a03030507021e0c0109171203 76
    0x115041c0301c401c1d44050400d010105000132203072440c600305041302c0001c859404141d071001400071410f0013568503403a800004e409c010440c80050583c41d54008400000b0740784540181182642519114130500000c2d1b00001709000d000207081160030303000442420410384800041b1001403420800600c02001c11881c0c10304620048855403000e880800104001e0003185074481d00501092400d200480c00341a000300c0002c5000d10403400e440c02da03030051752980581441c2c1405c0103c440c40c05021081d840300604000a10a62402c004080c101e2141d4051a121030b45428003d0400005911031030244002c2091800151b686a47d0100c065620b41062145070056074041100746c00b4180014008904c0022500c0015400000b40d0400856044042c0b201000200d401c442ca4002643c00030526802680034200081c0603410555004843e881154010142002101c0d01d5152519524a03182c00c54010f01c5c01550348024a640a0000d250403191520110b400140e610300c108070603071260b00b0300800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 246417877 1250 246416627 246416671
    0x150a020a080a0b210a02030714210f1e010c030209010f050c011b030f0501050319082209020901021e1015050306040305040e0115020c011b060f020307020f0105010509 73
    0x1d8940d1000c41000c9081c1888000403c5d03031101441c0d81a0703c244210000080c03203d0303505a40f00300e0060054880401c0010b00000800840e080c131044c02c8090040100080c43d1000411452901c15030440d6078158030f420f074044d0642102c803500c0c1e421081500401640c207882c0d80140e04541e0440051801550300c0d0112400ba40c014040007149032001c441003c0d05440e500d500d50468945a518004d00700020390b81c5a08065903054202403415005214408810104061030094407240c0c8112844444880c2c0008031000352a215412900001c1c1c1c2c0401d840c0343c42d590402c0801e02407042c80c1a003004d45a0150300c40c903510fa80c52a00e020085488000f0010800401c007089001800c2c0901103610a007003038035019105030000d00501000300240c0380001145503180c007413200209802d0300903000043c10f42004580104020b004038188072502e140c444000b580f644100070844421010058032070a100350000c1c100711034020102c1941c0e041a0060149686c1e00c100140c100d600303d5039070803144080c14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 246419127 1250 246417877 246417889
    0x91506120230010c090609080616110d0521070c020618032a190608100b07050703110a03050c0409050f15010501090902040e060f010e030d02150a020a080a0b 69
    0x200c4a00403042440b2070400ca0020150480c050302149912030b41151502e40030100c81044052243c08040d43c00000030030002d5980c5006d80307880c00c0041c5440c0604400030141d03645010707550962600012000903c030745421406460007058180c0362a81d4200d54140204001c1140c0355110010b44108070010741c09000c3d10076020904030002000d420389400c14004520010754a44030203040d01081c14030012090285014440340100000c910000c43c0e40c0c504100742110324250007400c0f8003c1d0a825100401c20940e00006040c40b41c0c4284014400542585042d0251800e801505401020300c081c0603c00504003141c00500d905066400160413180343c10304a00d049403503205801c46018140c135114146520043d00c40c1a0f0f1002c0c0c80e0044a00c3c1d48003442f100724462486901040c84040d000706a96203041412541e00860500d0044420b070312003030019040c102c0301265400540c2c000d410120628056401d15540304814a00441c01d10412034400341030000300a01c24410306940310b00281150f0f42e49 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 246420377 1250 246419127 246419179
    0x110d031116030c060608010c051206030c0a0806100803180105030405100504140c060f04060804050a15020d060503031207050d0e0a0b091635030d0915061202 69
    0x850030704004031545041c080c00c4182803400070344a180c202130b00401d8900f01401103c44540d0965207440c503100791120b00c0e206601028200c03035891b0103094800720f0305641e00407811000d400c41101621460800281010011103103500544141e0030a0041205081d2803140228414100307081c859965079a510746903041c507400801c080c000903c0c160a02c4244058044004a00c07021141200e02031490078040050b580a00000d2000c00311040005220083c42422115040792040c0300303c402040c810781c0e40d10b4100400c1d01991001e16404540c103001400a40508001014140c000c0c5143c1140070144440c2e0380801008031081c0300001406402104a503400064403600390702c141e941070544c526140310a1041030b1900380e02e500c91082031184400280300400200c41c41c008044000b40702c110101c0325980a94400301c00c4425060010092104d020320041007914500140010845054941501100a0302078440da00518105041c8004014204568a1039404545000302e00c1c6501d20040e80d60040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 246421627 1250 246420377 246420397
    0x503041a040f090203130f05010b0405071d0109030c03030302090607060c050403030e0f090a0c2016080f030406050f04081b01080c1602040c05090312070c06110d0311 73
    0x500404034020810300c00303401038607040800d41e402d5036550314a0405900040da00105c0d050040020301000031090016210058481c10011643e00c07000c000080c200c0e24125100c2c000324a651500d0340e0111100c12130300c80d01c16000d0070011a401d003940c4071160b40c40010301004040c96800580303984030b55100e8055900080c1e004030709000c402034004c030040154000d440200e01081e141450b8003410710f801e09070a500c60a01500c03406d0740703588014003070b0083d20b8440382c1402801444091811256030078081480f1030000f0390f000b0250050401c014414500981c0c1c4800340680150000082451000c0120b50455040c1e00d0529202c0c6582d640e103c8251065031310a0000e0301c110081c04d90340000e0f060743e1a200c03002c04d8031000300d01c2c0e9916041c0806071241408400d000e00e000c020510040c03425602881041d501d0b0315100f8185080200030a01d000000c680581002101040d400c0030808805201d00142c00f052500301c0200072102c9101e03075240300c0c04c007014060584503903a0310780c0504d68805445226807 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 246422877 1250 246421627 246421649
    0x20307030302011407082406160b0105130506030319090902030115020f070819080c1603051b010f0f1101150906120809210a0b061206040519050304 65
    0x5501d24029000b0804a41040070103141d02000405150040841d0307441001034210340b0306141890780b01c800f01800f241c0d4000384d01c884140945140824035911154a551142c0c0d0001c40c00d50408040116a98141072100b81c46400c0c1010000c56840c00320607150020044080806011310a030415151030001e5044080340500c080000525243e07110b01500c10380c417031902071b03640c007241900704d00380c070741803203000300d20b0654400003241000d4010081da548556008042090400e1101e9008906107940c42d80613040300a14000709206010f800c0c48a08426821316490103608101040041c100300d82c0420080140a100c51a04c0f40342401071300d8041c51064084001c110301000020003403003540b0107024000010740381c25004220507034001408030690790004140d078104480c1c0800c00900d40c01d605186400034034941c0406c242c0e250304200c0c500401e44560680c420b5403800e002800a9140050704400151340011709102c046000800d041c20144c141740314201201400b800c00c249148120713403012042034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 246424127 1250 246422877 246422879
    0x32a0705040903080f0f04031d0f120a05070b04030f06050a0f1b2003030109110403050a0803040b06060304020a0e09030405090f0f070f0e0f04090813050f01031107021c020307 77
    0xd03a004013800d10840198640c40343c180c45043e8201100c1504903401404102c48503045601c1120f603038a4000310301401007040c4c0c4845101c20129443d000c204240341c00e1540480b4400082003014400000075124880300c9908152071500c900502a0040130060303c00c1d9543c201203018080c00703030040c6480d40c2120a0610840030b4030708030749003580d007445840700010f90049044060034a0703016103a45000e412500843c1542d080081e443c004103811045803110060030000040080c50500c10101d201e405000e1180e140e2429060200202400410f03507840f07800c04008000050ba04c07120000280c98000035000081ea640c1580d0525621841d00030301c0e8030540b40c804000d10f48150a00f01c902c01c044c10075080c8496103d02d02d003034402d8040342021001140a000340c240390b40c01c0608200d840d421000b0300204042185484000e02c55000c003075051100501d101080c041420000d000050540081c60100700c0c46010002c411118000c414000384900c1008000c0c404110350325004100c3c807500101580c0f595 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 246425377 1250 246424127 246424133
    0x50f070c060809030f180109080601090c18060f0e040605030a050106053307020d0b090a0c060912170c0601080d0e190533070b0603032a07050409 64
    0xc0c6500c100e00002c1c0146000030009600881034680e0f54010152150038503003441d208100500b8841807090400210041c00285650100a00b600a240c8040002401c11000900a04014100c480142d00c0341c8028000c000d0298400741c0194002c80618181411025000014024000e82c1d17001952501c10034258205101065220404448084410354044840802c610341000307100845102030b514450310b0b80f003000f0359041c02005024401840c6001e10402d66a4412940704250340d1403009a01c210695010070607507008010107401d0038100003900354a070445007091064050b800400c01c0c0101070105005e950b03594241c42c0c040e01800160f03140d035a195001d46e56185500d208400c0001d8a100c0c0102c0103050601e00380c04619004100f51418500341814842c1c02c0f50000c0c00003a8261101d403003190305c124044040c4000c06803043c48076540f0030740da007080610407001402084c41780c0c10030400b4024444a0321240d01845102d610f0200740d40c070940000750b0410b5982d0388420381060400d9104020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 246426627 1250 246425377 246425393
    0x30a09080c070518010b12130c090e0c0111030f0703020a080304060c140306060301060804110d05030a0314090604110a030503030408030a0e010b150d0b0315010f06020f0a060c050f07 80
    0x15140255400c1c050381d900e43d4110880d200c0c00b0322502407120000c02004c40e9905408407008d40c40f11508142c806c4080e86e03541c540c41045526400007076005c1e034644210300c21100c00c3c014803680d0720f000d18184801052485103d5201e00c5500510101414000349000405000b40403004c101504036007815243e02e0103083c05000f82803106800d200003910400404861440c40302034070300507000544500c0c21a0308180080e0760503c0c000c0d0054400c402d00c02448002c6a03155a443c3c0c0d08540720382e000d540c07a882141c601605462142e40400601d140c0d076420410303554400a031b102e0344241c001c403404050817000e402045102a0350b810241950000108110030b2003001c200035030042e01181800c000e1041000030813400c80342c6e1800115071100e072180c0380c2c00b003c6d03525102030a5100940c110000360881c610000a1600d880303c894450549a0b40c0c0041204040003003840c17000b0b181c40e002401c48102c1c245034054031a50b02120003040d45544005604809105d0230903940d42408442c141a0380f08114100310303503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 246427877 1250 246426627 246426629
    0x90e3702031008010e07030c050d030e130b0108060a03030806060708070b0a02091305011d190f090c05030105010608040602071a15030c061614010f0c051201080307031202030a09080c07 81
    0x100c5903003030620784001d610000541d08100c07a00a0a10231465061034200b058030004100b00381c0800190b4200c25003140c4d00c0c1c3c0b10a1400781059100001c0021745400050503e54005000d10300c198155041000880c0e002081207034840030855413156104414a40302840f0702030001d019141810003400c02c10000c4880e8010486014110f80482c05641d00011040944009000d01c1425000d040f02102558114040c01030300450301c1200a407a035406480d0039421074140c02141d51420703031100302d140244811000384c0c1010f4542a002402950b04045003c0d05c9101e0250004083d1640022100c2c1800014541d05d981e607030700324424a090f8105032210000c85503190000d103100c1c0c0503000b404d4031700d46010f00031580c160221840c805d110f54001e03210504d06000940318000c0a5480d40c01c82110160b0512031b840710302c0002e4440c903480d500d640d40c1d5005982c1050300010501c0c0d00c01c0090300300dca50800c1c903c000c0200344c040050b03500c1e5580d41c150405400c192100401c002404201c84640d5840030a03598 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 246429127 1250 246427877 246427889
    0x5180c030105010303051602040b060c0c091b2b181a01051e040b06070b011a0c0c061b0a081b03090a03060209030a0b040507030201090e37020310 64
    0x605211254410142219000e02c00180820020000d0100701c07100f24004901c1c0c24001000000c9184000c1c011075603da101d41c030380c100540c004803003606452408420858010305038900050090210354402c8401d0302c03503400700c44002c031200100700240944c40c102407141c402d0020b405005005407e1050030410403049821103d81808204c3c00d0341d51001a403d680c101c40008081c1c0700814100800d00340b800c1c1040041c1500991544904801915044024081030f840750403080c91a41c0350640b05101401d614400c4082218100200c18a924001800072a41c0d01c0c1181c209035515034142c016000e403149410300c80c0e29030080c07840070814456040702501201d01075002c8000300116041000340c0360700c00d8140096000e100d0400510105240e68060812800080e00300c4180d0300903030b03c80001c0c84004035022186607011a00a00440d613001d442c0074024100345d802c8050038109190700080e45042d581200c0003055a035031809094142d201020b450041c0c00b454115940d0514120361003030390010f80115 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 246430377 1250 246429127 246429133
    0x31e0c170702150106050c03130e0103030908060708070327110a050d0c0315060b040b090102070f0324181b05010806010c0b06010e040c050903070b2a030d0518 70
    0x240800340042003040294140140a441c1130f07003016400e840c0b0350400e81c1c03c43d519100c1805100040038101c1c3c3c2400c050700049600c4d401f01d40c507610340104290010380003200160050400e20452503000041650450b41c1420041845940801c00b0680f000024982d541c00c401310000b80c1e030034005404c545188809050394082c0704240c8030ba080c00744043c00d442001309204030060003000881d43c1c1c1c000b400d0180008000103c0d030345580f2480b40540c2c0d00305410148244400084403103440d0380410a80d00106100911603503800d00d1505c0704120a541507400020300102c142e00c0c00c00e141d0035540703c582c0701811b151352110011070a041000300c82c5120966500d010f000d0300800318040d80580c03181c9124000c1691503180540d00755903940c4e008075011f40703010705000302e4404900071643c90340541d0b00300c1c181a585558580d000c0c001054640f4840c0d900043c1001010807614820000002e00c428941c80c580c4c0d5113122280d201d003201b071310b140301c1c8030555000540750000f03010340c2003200c0c64a011409030540403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 246431627 1250 246430377 246430381
    0xe0d030f090e060f1504030b010b0331080901031b0c020906030c030606012709050a0b09070e011103040f08030c1513230a03020606040c02011b031e0c17 67
    0x9a842c180684580e64411003414000107549008907180180c6080e5074000c038207182c1c0c1c07a0b8407115440b03800e0f0000150760304040100000c96140c2a86003074a21840b0001140850718a070300080d2440e10010702420b2803000044046245e4069000b401c3c924240440c3c213054106a028020300c042d41c805800c07032140b240320010a00901d00020414a2070b03e00130003500e00c0b515944010340328043c034003000181c3c1d09118156010002d02c840e046600501303c03214080703034030300c0c1801280040741e901d200c0041c0300d075042c1c405001d805503000050000c3c40c1c1080c2030012074000121545843c0d03008680c0040f06075840203001080441022014042c01c07540a01180d9219400c00007110b000302c8120381540c1d860032a5505c2d4030204125810b100032110044074050b10740c40303420300c4030760400c2c4a031503040c0d0159000800384141c600f854854590501d240b44001c00c042202040083c40d881c2e00980c441080648884284000020107410100c08001c601c1040000502000015280d450300d04104944c00f010280 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 246432877 1250 246431627 246431639
    0xc1b0f0106060f110d030203040c150e012a120504050a180c020a031d011e080403080630010204150c02010215010302060d1d0712050d0512070806010e0d030f09 70
    0x11480709a0400d01005d03125005201d802103000390001401903603c640c0c004c2c000103104a4540c0c219031004115a1654419080c80700050310f0103000301107007040e000c00c0039210440c5800028403004144e070b110307400846107505510300b151540110f400003584a1800e0a002404091a4154035564040c22009000d854103125043c1e0311407049800190200c0c00e00ca905005004040c01c804030300f00c005042555000e500200c16029003c507060001c008100700b1130a00c803d154100d0b00d01a030100c011202c210844c0040300035049441c0640c1c01401c0100c0d8080c0d01e450424100f901070340d000d40042540710242100100c00103001c00a251020780c050b0142c840f11141a51a02c1c0c02c140c180d035005000d99180089416404000700300d1100c00c1200c6681d0026001665001400840c00500407040101c115070143d0801130704010040b80c001c1c090000400106000c0180f0100082c0c0c044c10504100d40907950390401640c16030f00c1d14054079441601d00c07421504050f04810100707a0b042c10703669000c118640b81d030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 246434127 1250 246432877 246432887
    0x201090503120918071407050703060903051e04061709010e030f04210c030b06190815010b090d02010f090509010f060216050a0b070f080703030c02150f0c1b0f0106060f 74
    0x1640a40020f02c0e440d000c0321b41004c07401c0c010001d840c81081180c00055803500c5501c1160b04410f0100e002440014074010f40d10103c840c101c040c1c50044440d945010b1600c1c10161100c014441c802c90300411110000d00c440e00d0a51200c40004045402d583e0b841392188040794880d40903000b100390703914010179080345001c0c545001082040e441072000303095078119118246000c0e4010f02d00e90748005603031002490040d10301d0441e8014410440201030400202484942071701050b0005040320801303015541c42681c8401c1e81c100c40540a0030a2190304007a0f80301140c0b65825900b02c9601f1034500c00000030390040c4101200100d0b80903509490803005100c050015010300c80c8246a4000c030a000c0a006a502500c0240300251048c0000742e030121051b0f4030004250040502503001c41e0382d5030f108944082c1c041c0f010324403c940d03055003915103150800505858202c0039180c8210308002242c00e440e03803291101c48003001000c0c001101c8a981184201c1801382c015401040c00042c0c4007034002807418018 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 246435377 1250 246434127 246434131
    0x7020a1a0d0f0e0d0906020705010c020f0409020303070602030f011a2809080a060203010504110c1c0e030a050705010e06040f0b090d080c0709050609010e04020108040201090503120918 81
    0x508030091600400d00c084001a022490320404400d03a64000030000c241c0c100442001c8440e5a00c1e040062883d140020f414900d050344005d06000e13014070503a0059440c0c0768440901e2808a50002e000300460000c80e00c1d6005810008280500c0002806080141c007413020f03048070180710051106240c04400200580660005948005141d200400f840d90005854070030369446454100b140030b690345d4595282c05100309c01514055400030061109003400d018420b14801800211450110b81510840e510501c04401300c5a11540f515403418462090003d00c05e103010040c1100e20703281c0c1908110ba158216882480d0128005982c0c2c1181424840b00361412903850aa070014610b28200384160315501c54091694001c80c1c00c1c0c50800051202c0340070301640b120380401020380c0c5082001e4101141e4016010500c9a10031400400c48600d890350000c0c0e00c036a0a01c1c210b920754899100580f20010349070002079241c002c1c08240805405648007a04007040126030014280313083c98080c2c8401070003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 246436627 1250 246435377 246435419
    0x15060e0a09020a020613062004030c0501090302010203040e040f020406081006090506060702010e030a020910210b07030b040605040513060f0e06040b1b0a0c110306011520030f07020a 80
    0x101c07a0000d820720411b2030210312401c1c0030345400f00f4154400c0c43c008102401c220019400014041401d1060019089441c40500002c0c00e20504603811038002035a02d004910600c194009940002003c0183c0d6030400340c1041e03400b030701c288030040d01c0f403546585409040103d00400343c941071000031180e1050040e54081c440280c0a140b4014403600115110342e0340d5000c032a058440d10091100503154410403911618201c81c800440b18140f02c054100ca90340e80c60131043e41420a03885c1c5021032407030144207411090301c0c24000f890828002c08a4041c02e4654401075005251108020b40d1001d0030000030340300703032061404000c2600103006100864102122001c4258014000140003455621415030070031000b82d4101c034082ca2003180e4180c184d02509101d400a0360340d01d03c6c0c03400c0210300245220510000c03009041c50703604200c1d003100d00240d00e821070808c000da8a10510602404181c820208460350810f49680340403140c0e210006a0280c1001c80c06155141070004a070898844440b0251340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 246437877 1250 246436627 246436633
    0x31c050910020a1205030403080f270a0210080619030b01030803090a0f0c0e061017150607050106140d08040302041a0916080a0b0109051315060e0a09020a02 69
    0x50180240444484408081070a5204054510021601040340080003110382e079901d559924051a004100000c003404101d0400400e50074030003d050760403c0c10925440e041d94249003903604080007454003142e590083d401c00e1020307080003000d41e0310503582d03407150341c0030b8401c05400001c2e05100e200c28103d510010308a00c0c000300040c00001c0c0302ea002190051008000c89110347c690362035820440c8500c1c50700700d03284550322100304500c0c4540304015a000714100c9108942c1411444081c02d00980c0d4001c54002046000000304104c021100852079000003401c040e0b111046803420034024062401200c681c52090105100c0c14603290b50300e1000c9542c008089800c140c5541e080c400079003031003c4882603903035000c0d41000c00c940321300c4001d0f4401c0000b500d00e02e45a0480f0500500304100180004851500703046084000b660081c074007800301c0c0c40540f131040c00400014001070082c0401c400490b1012a0840c3c0000c00d1644501c0b07541d02d6403003c46003880050341d190003002c100e106a00b55407016070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 246439127 1250 246437877 246437887
    0x9070801061b08070b0405150108030a0206012408040302030c030d0e0f0a02010c08090114120403030e01050106090e061807020a030e06130b180306090a0606050301060b0306060c070b0f0702031c05 86
    0xd0107174041c4982007449041201c41c03070f4080b138192000c0d50500360444201c81d0f10200d602401c8950401c511401080d406044421201d128100a034010a03040c0300c0c54103220000700030a0415100300b08403140343c000d04042da6101c550300b24030800a04009541c1300c40314400d50383d1038227102e0004075901020607416100d84103c8010b40d80c9469081d005198114180040c0800f00c10802c142e140042258005245a14240c2e240038900a422141110600b16103a03241c0401403151541104016003070740c0100f195541540d55400024445440030305820741d03440201e10500c241213800284400350b0b2482600c0da000720407440800d0001c00e0152030080c546c0c629a8007410401c845a42e80180f00c0c01041003500d10580d18a00c01117840c06500b0344070400c2e04c0e030040100200744002d900c40c034005030800300c0c0203001c040d2800203510407500014000c00e116150000d449444c0c03400420502c0028203600c058645c4654200707503054420b80080034164042d015200ba0810516090007948a451185442d420f040c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 246440377 1250 246439127 246439133
    0x61409010e0703060306110d1406090c0904091b051008090706030e01090203011104090605041a1002030c061005100503480301080f031602040f0b09070801061b0807 72
    0x72100140412040c55030b03d910110100d16140030786000b0f45500000e8683e00c00303120700900c0882e10080300c0c4281e188402005e000380d03540e484c4055034000d00501c40c00e40e11003880c00e000500a04655800410009d190308150b004044034130120302c01c64100312428441c501550300c003a0b64490040321158140d0b0010601884a0390180c0d2001c42e00c0c4044d80000a041e0f0050f0b400309003100c0c2401401411804003080c00c0080907081c0c09050080d06064034107101d038940e43e101041c40c8183d4042c0c00c0d44503d5101c10b15000b41803007001501e4603484000204d41090502c3c12410005a4403400342d980184030f9004120b00140c0034000b281e001c1e040090391403480c80c60012490f01c00c2c01c20f120316915540b099248003800545070040248440c5482c0e540c090380d0354504144103140c500c0c03c041a800341e4200340506a842c0d0700b41d036050080507070180c802041600120060000a010512495505c00c05220a00c00c6031940907400380d0503545503817100b15080d070295255100d040c03003a00c4000c2148074100000400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 246441627 1250 246440377 246440399
    0xa03050d050c0705030705061017100b0d050a030806150301030209040f15020c010b0f030d080106030b03100e0c01090e0c0702041509060303022109060706020a0c05100209030106140901 81
    0x300c180e010b8540c0e0304045003907031428110342c012001915258007017408d100e82031024400b000000d00c5684403e09442568901d22510b820749003680404080da04ea594080c16120564030012555002d015500ca8038058580034104000a031852405051342524801100444030103c9060300c0c1c005055030b00d155100d540c2e050307095042d0340382102c1502d6481c0004800c90301c0c0380060840c424030350b000482d1407489030741800200030300b070b100041c4254400c51455203183e400803003207070544009280c0400c90349882d0011034501114410b00c0222145807224400150601107915041d140c001d03622956540d03a56698800460f00a0302c1c400150f071300401050006103025845401c03881500300c04648416038034444442111001c0c0e0080c0c0242e004008183c010003280341c80c0d6801030045404060a003818400810024019801d00400282d0b0018081d81c0c09406200d01010060340001142e00c02c07008a200388003e904101e039114081d40c00d203600801d00c4203004040d108010409044408240e1800100d241 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 246442877 1250 246441627 246441631
    0x1401030f050c09100e0a092a211a06150c0106030b040b090d050f04120201030905011d010605010206061302031e0f0103030f05090d02101b0506010608090a03050d05 72
    0x141d2441103441024440d280c009540e44140c0695809490981c50302100f41405800200035030701d500c2c9012500000100445000e0b6007a140361084000214034220700030f80e0f0045c403034100c1c902c03480c039003034000720742d008a2141c2291304da02c60394070b1a001c0f00b03a02042c001035034010380b034807607024000f00e446050f121a25405801c0c0e405034640081103c45d40c0361145409880c00f61010341c0c0d001c544108202e102001040894024600b51410624120030042460642d00482c0600840032540c0c91802056a200740c005500c4250004020072015041148102007203001a400c04510750820314009110340c00410340f6441501c0c042c150900b0b010008a079074000350310046c4491075001031035000040c207039400201e0501c201c0340c03000c4a01240d419401c000c0c18079104c0ca0900e40c1081070400c8291182d8540d041c2e00c0701801e50584128074040c2400e036040c0d42a207000f0000c2985002c6909008040c004001002e030704036121915241c1c115214a22101d07104c200181c005000b04400700b0800340c2d100866400300f6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 246444127 1250 246442877 246442883
    0xb0a050108100e010e070212120c13090f0c090504140609041b030813090c02031b0106120309090605010302041d0702030d14040317161b1704060f031401030f 69
    0x102c0d0b1503856404400d042682078012174030b404605010080c10f5501006296080c8103001d42d800d0410700c03038003d030715501c510040000b00641070128814030b0000d0b260304400c01400020005201c0c40f219407800c2c200a05400140c000003c84d03440c80000e60b42094071850a4007566420030340640c0c1e03546010f10007002000b40007140c000442041c1132551139160146e01c4040c610802c501c079030710542e240d601000e032209a00582811403a01141c0610f00b40c00100300c482c403541108040100842000c0850b00520050340112403090381940c0e41020140c0c040050b1f015901070706010800d1a4460004404a0096014207050900108820240491801c1c81c0c41d5000e10b103841164030300305402c0b0000041d03490310040401d00c00c46040c01d02040540040d4407004808000592107038500c1c1907415182510510044901032115200075a620b183c40303074200441494105001c2c1c0d85200515107a601e0a6015201d9440082c1c1d051030a0824a8400e000d030703120105a1942c598040d03401d64031a1081020801012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 246445377 1250 246444127 246444151
    0x506060708030106080f09060105100813120509010201050f070507230d1110140a02090d12021516140c0114090f07061106070c0f0b090105060f01030b0a050108 70
    0x404001450034006501030002c81e81d658003582402c1c81d1305021050054407d40181d044240140003540f51681e403a4034410301d43c1f4102950352074548a02d00d015a00d00340107401d4101d16101480142c1e00140107001041c000e0f030080009540340b50391285110701c142c3d40400050000c104660204885d409440d48101c40d03084800904c03008686550f02e004003200b04100031800418211150a80030702c1141140d010782c060600601060101ca0050000300602c0d55149503170100f12048179440381c6001c900019800398101c0480240207a000c0d40d0703068120038510300071804800003008501c0c104180400c0c0007681d121803084500300e85044045c1c2d0050a12501c3ca0740d42c50914040081d00714001501888219020307240d401040c0d10f0141c100700300da810841c1841074030000c0f000302080000b0382540c490050b10f44460303062010710b8421013500b03000300e000d04403058020501c2038550040d0b01c03040c098401103560703480d0110340400550607030b0042c007011390b0721003005001082254015070300c2d154270440340307811 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 246446627 1250 246445377 246445387
    0xf01050304350c0105070e01020a03020a03081504020f0309010507020703053d09060605010201060e19090206030717180a0b060111030f0702040605060f040311010e0a1e050a18050606 80
    0xb850380d1a00044600c1c1800d80d154020b0100044e0015120124804280f0144c042540941c40c06590345040c1d070700090070800c0c0300c0f0002e1043c102041c264011414010015903070340a0100e0b488900d60016517200f01107500c1c040205a50f10300000301c05048035804400b82181645d81e505440c00394049220b503040c254003240c0300080505c88d1202c1110402d0b022100014040d606082c04021a0ba50360041415a0325040091024091084006d07074816070b45800030101c00c4810b19400301030050070300001e4000d000070044c442055000501c039209040850107165259071150070440580800c10000f81041e04000c14031004600c185040c107a0005060502c0d940c061240000fa5155034020009000b20510114084007103141502030300b00102001c0704c54608001d61113001c41110b1041d403200501403141c402d0742c0070a60f4090820300310b400c80000c100ca4099981c542242900b0302540c0201c00407500e00203030100c0d2074134040040ca0309542030628250081690f03031801a00812020700350703603808502401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 246447877 1250 246446627 246446723
    0x80a180605190c141c020c0a080301090f0b0105070305340605010f050612040f1a0103120201110d09050a020402030c04051903080712050904050a0204050f01050304 72
    0x507490041403074034040460010100c98050880340803998000400202d15000009042c525058607000c84621580c90b609a04030b00501c0001d1245c5d0b0103549487c09031138031070400d12a150004c1c6040b201c01c00e009000c4034403032113503803001c80390110021804100b042c06100d0200340300c1c20203411003962042540d00200c01442000c001e644824600c0aa620340302070140f420406c0e02c0c000c245c010071461410000c81420304c00010407900a140c140d103074809045000030309011500e803a03c28815003040c80c100c03940c64445000f03801c2034001d00050f12024030342a41d018480744140f0a0940080c0349180c201e04100703203248800d000c0c0c0003d240580c0c5511500528601607030740d40c402135004080e0184901c0c3d40707900d808180300c10844161561210040049003c1010030760050885450f60790100c0f90741400c4006000580c0c441c01103000d400d0f0094500303000c10071008056801041640c0080302ca15440305d51070001154544000c07500141203000c1480208803030304444580c00002c840940c0c0354440314041c0d82d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 246449127 1250 246447877 246447881
    0x305070212060429040c03020d08190201090b090312010509060d080c01020904050112030212030c0c0f06071b05190809090405010506100c1110140c0303010e1006080a1806 75
    0x10301d094840d8106000000394411944401300701400c0301c1c1480c681c0c240781a449407092014188000780c000d14842001c1000c10900c1c0c0102c803200701c52048201101c103030001c0024024a28070b0380440b2240b60507804a88621400019180240d0038042e030030385d0316800c10041c8030420304003a02258000c628400c0d141c00140112010f4110045070500041e1980c00348010072041d240180e0000d590307284040c0040000c26030100b02c0440d1148081c0d0303a16a00e480c0c22002c1541c0f0700c61000f4000341400b4201095060600c0461200e000c1c615568803002c1e1202440c40075100c004074101d00400c21b41c8203620004040a0f03c2801240640c0140c08841c1010710001c040b0715202c2d8221002c40d02a59282c04108003031030300d00c11304080c1120520702446004041c0d0759080b000310410703100324812002503444100075442100c1c94184030400c12101d640740c07010303c190250f50307820a000e801c150058140000b4202404120203000320303040781c0c1d5140d41c59110b00c052040188901840e0300185003100c180c01c00401c01034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 246450377 1250 246449127 246449131
    0x1030f05190e03130b120601051c020705070e0f090705040b010509010e031905060106020105010614180307150e030c040c090b16080703080124091e080106090b1c0c03030507021206 79
    0xc401202c6c0d5540c00140b01c800440e130014445810b001d0107010392300426104035150030042c0209500148d40b102e035414075515200f400c3d03000c19036048100081180d000299603445000b0200300d81140c101d00c1e220020041030f00e46150141e400102c1c00c0c0945a019803081e400100301c045c0140541f240d41e4680400da10a04000d2107040c1c0e010303130240004114403079092150500414440c94810400c080400001560f0b10aa4030001f804052000428080741d03400e010000c0108600e00d01000b03e400311719000b070700c9c1d041088540c511038010300b80d2600c1e580c1418044c5ea154a2803d0341d40180c1b10f420000103800c1a000f012180d480c5071113001c100000118030400410300103000ea11140c0b65507240c070f410301c1003144801241000070b0f0a140c13030803180d058000c000390040c4d4001010000d5a500002c07040300b00d001155021142d01d40c02c0c010001106040395100c08c01b200700a80e124000002025107100250601d02d4000340f4582d69002c0400210348a80c02070038040380b0042c507a03142c0e940d05441075454a041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 246451627 1250 246450377 246450389
    0x61e1309021308070302010c0609080c0609102a03020313080f04181a010e1503130201020f030c0c0f0a0803030406050109150501021203070207031a0601030f05190e0313 74
    0x40010b0255002050901540090030b1040080003d90704560000f040200c0e568801000c03140c0300c403c403804200400003a241300440c1c0740210b90282c030308500016903070310020b10380008640c44c005414445018000102003001d100e0b000080c1c200c421007104030022b5100910214814503408007000000d21900010081c1d01485801940c56038101000c1c00a5164491b0241600d1860850140003000b00040034441d45d5000742040e0140c0f15150010402c0900440000d12044000104014400e48243e46031010745000f81e08480200c03a002014582d41d20035044a18041d0380100c2ea400001e02d84888180481d200180c0942c3d041c540e45e003203482c555002a5000c45500f43c5800c0140803954852040720020060b248054083c58130b03250001c0e4456800128030b1f02d0b910800000109494000c02c0406c005603400180c0704140b200318072900090300020340710a800a424901700e101e001d40e9034000d15018000300c0080c0400c2d4004000c006004011420781c079110782c001400100d051203502c011150003060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 246452877 1250 246451627 246451631
    0x9070804050715021c03060504020c070e01080a1509050c0402040803030a0b03070506040b030c040503120c0114041e020a03060606020106080c03010515090a0f06030305070b15061e1309 81
    0x410349030440c1822160f030070061860700040c0c09009000d6002490020540c04005141014000c1030802c402600843d000560000c0c000120390a000b880095004100d40e010031300ca090503603c4140c09515410301c8000900f9030007107000c41c441a03109035409098200d00c105c0403500c10f50511008039050360010391010b1100c1e000413041005414a500600039414400c401130484c1608090014860340104c0c061400b02d4003000c00000c80100940b401c5070040c060050481c2d0032170b0300b074450f16038043d030040b003c0001070b5090400740303000e0348070402039a401143c2c04032000c04036481540d0400ca0450f50b181301030341d01048800001000c50600c1c440c01001e0101c542c000318500782441d810038a00610b00c81130130701aa14100410114005600761404000c500301c981c4400c9448401d0b521018007190020480e20a10b024000403c1542100c014103a062040705041e40b00e50705e103401c1e0000300b2400208590450300410451162402e08131405980348060b000d4603042003403c409404081c00b00743c002081140e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 246454127 1250 246452877 246452881
    0x100309050a0809040c0f050307120e0f0616050310031416061e0503010e060405070507050f0102040611010b10110f06040f0317010f031b03020913060e0a02031902030c090708 76
    0x420a40a8030300300517680d0401603c01c1c8102c40c1e00504602c0014007c0c0200402800c030a0310381c1d2450b821601c0c035040d04508441252000c08070140d203504094581011003004950302e001018090700070389109104240e0852013081c078585480da030807c00d04610020500480a40c002e900805600c0c507130150149542e64042e6207000507410075101802013109050010070700041003070807070042200e903210030269004100768898071000e0304c183c0a41c00c4000c003035020f04081229181c03015030180c4215102d42c0c0d5414040d203100c0561f00e0884000501b4640c10205590107031400c4c5020310314a16a208581c000c40f08481d010886840c1001c100391812221030118032035031024150300140105c0442034134114078245515005120450415900c00140240c06200503500240782d407022110066801500713400892070450000040ca44203441c0840e919881c04005000f4400001202911150b000c0e0080240d040c10340c0e030004004c44860001c980c1441a00c00c0304a0585860071442d008400d142c44100843c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 246455377 1250 246454127 246454129
    0x103050c04090507050f0105120c0903061605030f150a03030905040f020a09030b09070b0c10060602010606020d050322050d0f02061302211906060e1005100309050a0809 74
    0x46084a003161249003001e41d001c2c0401c2000c6420421604121080c82035841e0400059809005009a400d8800070080030003000204d108010700da207900c201c003568100c0d41ca074456204072468006c15000051814000100d80c01400e130700c42d81c0c02071201e0380c0e00340c20040c0c40400180c40c1036150300120001030690707800300598102400f40203001c0c840410150f00b021700ca010001d014501910016181000200c00704000000501100d07016114200701190784510350300c0d550356525590b2a0312042c6d41e140003000a00c851043c070410095480580c0902000468810111401e80000c3c0115202d00f80100c440e5003042203500380540030900c100040e080b8140342640c00380000104103050815900503404000130b03a142d6840d10700135168100c1300d070606401105200009000391a0003144140f01d40f800000400d0038040300d621082e48281d0040c4021601c2c0c90800c3c00c1601300b0786000010b824918401d0003030789040017009201c1c40b81c51a002a058101d61202860644c2c151801c1c0ca80a00011f6900c48c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 246456627 1250 246455377 246455383
    0xa0e060406030e011406030a030f14070605091009080d09031701060201050403091d060427030e1e06090d0f0c0306090b24040506030f060a0c080612030906030c0f12010305 75
    0x40c4c45105005c1141480c010010940328515000c0080030040c04c82c503840c2ea41800381e0544480610644c60481d254400d038604000140402d44108082d40b00710810301c4680a2140922049030f41d003c07107140e0030500c4001e07003d006403203008411418092a0511044030b1036621112500a0101358004030380c43c00c2508000e8043d600a4014420140f040440041a5004484d40582011058400080040c09901d00b0710700c07006400e0000d10710219401072803003403580c8028a1450304000706c134014109006c030008186040c02c101d05840c1c0040d0184400829480c00066540307005019075603182044550355100c440b03100058101300da10560b0703480340105002c401160203501103543e503100310160100c0500c0c004480c15640b40716214580f2640011074507103042c003c0701c0500100c04200c072481d0078440390b03400140440402c91300006a081c4002681c91410448410710580744c9005580744c1200e241c2400842d44c4018403108004504100c0703900001a000c000303021650f02141400f9680d4114030b09141 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 246457877 1250 246456627 246456641
    0x50307051006050d0b1f03050604030206090c01020d08060d06020418060f050a0e0a0902030106050a0603021c050c031305190501020a1101150909110409051506060f0f0a0e060406030e01 81
    0xc013512410500b10f0000d08074410b07281d003210840a000f46081000c04024000b0b02203900020010702640083c00101900018014054000101900d21881c484001265950f2060860400241800000c103403e4140800d8074003da500400000d4645038840040001d211840086407245541d40c0300d04002c02010802c10030041d00b812a501c00007a40340c82c80700800d580707001d009034454036900c0c02450b0465800358024002440060000035000303550b43d101400940014080500c9005608035210800155125851240c0281000c450442c0c0300d40d50783e02582a4030300c400304c1d864402d600140c011030602c000a503420910400000d41d071441400b40c010a8801c40701100d904980c107005205400c540c00301403503000c0d0340350385000194100030b608003401c0302d0034007c00044d00940f802c40050240700000c00c80d0000381c0d0031181ca11401e0340303e020501c04644030301c210040744420248401c0000d50380610040c201060b541c5028580c00c0d0103500000d14940c80350b40f09034042540c656065007007050a0244c59 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 246459127 1250 246457877 246457879
    0xa020a0e07020f01090b0609061f030213090204030b010b0c030408013801020309040c0306030c03030e092809020117090334031b0605010b1c0209010c061805030705100605 75
    0x2000850141d611b00c1400c1d4070113407011344221036000001e66151290846802c61010020074081070144003040603009500c9030002c2d000ac6254010080750b400498001c40d003c0702e80c842940e043d1030b032801c0071343c01c0c864001900c0e40c040360004101c0040d008a0034069854a620800c0c026900c904e00c10342a03042c187c0d0681485031410042d2074048a1a0381c01005860b074400081d180480d4008031302c50114014400c0b42c000801d0307526684004800c1c180d002003600d41d81d020580c0c2e51801610f524042040749146041402213995419860000d0710545400503c10a071040c1841070362031060f625846035250003100c7c07000c107a500209080d1109a00c000321554450030600040308000900c080000d036190480e0009020312064403408452221006920b10965070003c9040146507103c1c910ba104540c00015004200134440048902d440040e01c00c68015141c16100c0039801d46060751010b02070088080c0c1d01915901d594203400101d8003e20040c01034a11410261030400b43d480140e03001c44a590f0451 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 246460377 1250 246459127 246459131
    0x5010806030f210c07080d020c01140901031104030f0b07090f0308041a09030304030606030302060708070c11012106051f0801030318050a09141b090f030a020a0e07020f01 75
    0x101101280481d80c01100c0c9800500503c4a0404881a40c458419004c0c007800f00e00c00c40c403000901c040003042c4035111180c613071300f03580c2107183c03200045521600042103040015000c00411070396601035030090103000c40004c0541e003417039603e8540c2a900c1080170781c11360f0ba40310400d007007200e00344d44041c0c4c0c40e000c0d280e55010180d0050864940c41e500b07010314003540c01050301d0b1524400c948101403094030310442e03004003207075901c81c0c89141176005007119210480262150a0101e06598026074405119880d81e50fa0321039040c005407110040201c114442030305102641c821032004c44503803428a042072080f5000410b489140505100c600c40c84000f4103050000030007200d82500340e002081c2e504403501454907241c5520841120812452985e0019601c1a444000094214076581086450050245840d80b00e0f40c0d8810780f1104d50702003000c4480c0c9440040100702060b01c2c10207200401c0d500058201c503e28011a4007084d420f002d29046411100a800101302c2c0107941080031143c0c600002c002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 246461627 1250 246460377 246460393
    0xc030106020304030f020a03060e030408120414130906110c0c1005300a0606031401052d04050903040e0112030215060d06050a0213080a0b1501050409090c0501080603 73
    0xe4a0340100c0c0001003111030b5405c010029560303103504010145400c82c00c20003605440c010003542d0303a4014441d030006030046060744c000000010042c0d034115928103101d1600900d8140c20407450301200c00e011030703c0b16500c8902d10003185152081d8112803c1c0030850b03650b90300d04029814070300b001425001e071180c0000b00ea1070b0b007040e0b4010107a803c3c1ca4901d034420b88413070628400b24951417000c0c2042c1c0401c50580420414080e80c55040b81e4200c54080c1c8080050000d94040f04000302c40074058950440040a0b561407040203032081642d200d04c6d071f1241e51280250348000a000d665050721b00c5203240d440403500340b000c03803035041c0403078010518901382c00380c240800c4d034001e915440114032411000610303400081150b01c13081d03859124194020000c0000e490050041d00c001c1d0890424000500008840401c0360300000035040c0e0b40c0e07a0800c0301d041c01a61000101c0720080c100c40f0101e41004010700c0001041c15050003144403291052402c4580541018001401850004e000c00d01c81c0c4c0c000c0d45 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 246462877 1250 246461627 246461639
    0x32703071e05151b0606040506042c010f0609090b16140d1d0105041e02010903170c0327041803030903350708070512100e040305070b0c0301 62
    0x800302194000d440607020301c001c07140540400e010f020900e06190280041302c007021200490075502c1250111000c1200d81c0301d460900c422210465124001c5040d01e41040181042d02021484006654030000c203402c2005000c0009640c403541c000060240c640252004020860b40c1306980089030789927010050482c24030051420203003c5681020601c000b070308006030001d03600101103410102c202041401c0307400200b24000c100403075003a43c00510700301d00030048510b5011001c4032940c0583d1410a00c81c219140c0c1003040442c800b902442031020402a054210203001800541142031500e0085010303441544184411040000788518505483c00c0c20030f07032400c00c1d00c5c2e2459405280008100009150940304509a0607106c01122103040340c000300c030000300155a910a0b49907140c602507403504041926043c009803482c20218505006195259065004581e88207201c80041c0c0441540c9480d10441818140c50036030008900054400512401d41c0c103d582100345205d40342e18542c9040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 246464127 1250 246462877 246462929
    0x10801110a050c030906040b130b0418050a1d0f0c0114070605041104020d020405040e0a0c1211060f030610020c100f0e030f0a03120c0c02011103270307 67
    0x15020341d09101c4081600420000100251000120050a22a5184e4841d61041c8407504a900030743c1403404800c1c0c0204040074980142c03400c560f000c00515204001500a10026050080c014003241d6a29808040107000e44e40e42c0880e4508010060b00c031220300e650b02d01d0b040550040c1340a051180380b465030010001392900312502c1940061001030103854503d0f05ca104c4210b60201c61394800c4c000b003901c001a5180d0b034000c3c0110751003141d00b0000040002c10154407207e0300305001c4d024252484081102058800c480103d80344103580c1c00c0003c959030000540c17aa00030b4200312024a501108000c0a410004891000784140340000d2525014000028010303000140414041002000c45560254041c50f51181c4170b2034001d00b1358161100100c0c08070380c2d58540f50410323800651418101070101103a48249141c44d00d0701d40e41c0c0c810007a01c1e6001540e031001070381610340541c4001c005031412110601107091441c403200351411032040004080501d02079007900304848489985815400801d660303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 246465377 1250 246464127 246464137
    0x30c0303051c06170712020a09052e061706090a150b040b070203060606030405060703021806031e07171302060912060109060b0a0e0405042108090601080111 69
    0x5150490352005000c10340440c240c2c0c0701c010407864508010010815000041132400c00940d21000c88115540da5194000a040080340c0603400a220742e10a00c07203280c3c1500056444103611903084100255900001d07107807980c84400c2082c2c80c0c0c210006203c6264000080c521601101d490b400c050304180000a6011601901c041340d1241e03100c0a110304200c9106030900100403000c034840d1a650ba40c8411503040c1c2c450781c0e0032480790040c0720001d0103524203682070703e0150703800c003000741103503a949a0154020f510945007010114400341f28082e01d90b0369140114443d09a04404001d00c03030b1021552001001c1c060042c605020590070100c6405a46094050380305107116191005443da500100309184a0910a180c2011840503000204400046d41c0e904982d440141000060b54480c0080d005e40a1050844002840001016460b140517081070f07402c00d0141030134010784030b04081c019003400e01402d900408105178004000785c007a0144411030040c0100b0000741302800090181d00554455 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 246466627 1250 246465377 246465383
    0x12020d0c090204182d0e070303080a0f020717070302030405090103080705011b0c02090417030906100f0f090f061701060e0a0b090610050f03070c060b0103060b091c0503070b071701030c03 82
    0x245c6240b59105a494000c0b03001101c40400390740c40c880d02c03410000c1481302c003200c40706516800c014544041c0c83c01842180c0665810890301000314200012849280d40701c900309404612040c030004c54940c2e10040814000d5111354a4983e03612a10725249082d2550003881c04032450100031000340c0150040c80d904540d0794112a45599a076862800c1d909047d9030307442000040e18048100800c0100001e403440c05840d44034900071501d907130342040704101030042c0644064a0803000c0c04000c1100103402408002c126814003103195a110b800300900400d0507424580346070b4441804202d0b000d54a02480d400010058041c00050380e0100811005203001c0c0070240a03c20440d410300742d0034801c1090343c2c07110901e407036065520304092200038240b022039002580c00c2840c0c8911121158001d118105c00c13545503121982c00c0a184508100070070320440c00c0f142801415450b084001003091004103d42e61080c44190b8240c1000ca0000b0a00342c0061507041520582800600204290909c0c00341140c0d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 246467877 1250 246466627 246466691
    0xa080f0106052d0d020921100b03010f0e07140105191b05030a020a1505040c0905060105041805040c2304050402060904050906040203160e0112020d0c09020418 70
    0x8400350407081d0f1610030b01000480f6080803031070700c0078140700c3e0b0000d0600303003000c44030201107103401d00c104100c3d00111058a80c00d0703032114101e2100e40c0a282c002c0080688010000112407a4400d030000545160b03001c840144d170000300081c800480c4616000790b40c004286403a504001c04500c40b120075034000213500050066507440034800b460046010701920390300200703607034980001d494007950b00c0c40706039412030300d00360309040320806c900b003d200d103e100e01d400100c0382034444d00d8003a41c4001040090090381c1007000411010811401003410050301e580140030006d02450300b0300f400ca1000c0a00e0304003031501c00c003103000c00c840f4507212101482224021940080c5d982c07558800a1241c1c4101e0b20034540180c1480208100040c01103003640c800d500a070141d0340701176103100200e11180ca2034045e061641006900500080e02141440c012991000d000f04500f44075a48800c01120b001e41d100c0d080d0560005410300003202014203a805880941c0d10900100c80086032101c0500003500c01108950 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 246469127 1250 246467877 246467917
    0x6091113090e0a0f121202070f1b0911030a050901140c031e04060920031e07091107050f0a170306030a2f0306060d030f090801020a050a080f010605 65
    0x41040c01030301c1245521049070400c404d65403414040000818190f900400d0b001d09420500100034000c490070b01e41d010340c07400d4049019942d0380787c0c40e044580480c3e001c081d0310322000c01c82400701d104921078054070300358041d03c03841c00d400d445058684c014122241a41011000514181011700701d42c2c20043c215005510396541100661a03030091220300c40009030706009000c02d0112950000e0784450081e45100c00c1d1075400c030020402150180d29098042d48010030400740209024a105940c0c80e451042d01e5055985580b0300041d550f030070303038034141070440082c400042100420907080099001030107040c3e500144d0b1102d00a87d003c0030b084404002c1c001000541503a4144803580483d94803040104510a115010940c80e8410b000e181c040400940200700b031030315000804612075030009001580300c625650781100c41c5041c03040501c0c288407000300c0120726042c1c203001604003000359035900c50f11040101d1004003403010141c8091403a08490b401409601d41c04412070342d00c188201100c01c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 246470377 1250 246469127 246469151
    0x1a0a0f11010b0402042c100902070302030d020a0e03070e070e0f1810050f0411070602070218090309130c020616052a0d0206220212060a0609111309 65
    0x90100d0a00c0140d00034800140428014a640401ca10f201c442010440c0821b0450160f070002c5581502c03c400e60241c80030b8204000841030b0000c00c0300e58443e2040da4145000c1000d0341c4140d030400040c2e800030801d11070200015080c1000400010b00b0790000303d002d03074105108054807044d1204000b60154603040284038045e01d52042c0030602d0940d21741030002900e0546138011202565000729441910b11804405030ba250034040e992480c6c0c0c400700c885280410340c0d80d506000350302c51341003242c109802e5854107040040c2e24071210301c80e008040c007079076441c2405010030800004602d40544003030301d00b024580ca0150b0004000da0f102c0c02816034038800e03010b541d0064840707006045148180000311000103c0d8506181240020f401c0390004840003040c400d20103030b84030002201c1c0c80134801d00c5000d1450a01e817544084054440c0042c0041070b0510034603990070304100e811110b45400a480c1d1404000190851088410160b50303800c0c03081c1400840d03c0468081c158600c50800c6154a46c9044008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 246471627 1250 246470377 246470381
    0x6100804122001150503010b060d0504030c02030a05030a0201050f0108060402010804051608011506020c0114091c0f02030d02061506071704030c0f1202060d0f0e0d03061a0a0f1101 79
    0x102d40102011140d0080603a2101c038081c1000c440964030f0180e0380840000c050505008030528880d009001a0030300ea002d041c0390005210082c4107038100f0219103d0310015860510501070010700910140d03656030880300d800317420f45d10b0203080b03c00c200c0701c000010000c148000c508950802da0910f01000c40e503c46041c17051a03c10340700c421a081281c512000030b40d9840541c444800d48585031056060036641c0c041c01e0780c03940e9685000340e01240c0320a8400c0d04048500c0000e0074841e00080c1480641700208500c1001141034030021142807009250541c1940707820000c3c00c2c0313622101d100503c041c0c030704600d48058407804880168001e00b008204031040110142504000541005000740c58554905121f07400d19114807074201210640000800c6103400c501e881200340d90058541850300c0f0000050750b00420841c001d861015555003219660040c00780222015500980e5021501500f0140c000040000b40d10003046d06840800411500359000301041c0014440c038100104244030400740b07640 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 246472877 1250 246471627 246471647
    0x6030515010e04150e013c02070c150311040303050306130903020705060a020712050a02090c09031911030703150c0207050916091502030a09050111120c12160201080610080412 77
    0x910443c900140d680c01070400400d40b24807020420104100011043c0180200c0c810140040c000325040c482c01d01c8000d0bc102c894005039003180c6000101000f0b100040e103c15003040d042140010000018403403e450310b4142c42c4158840c2c22000c0101c0c28550b074003c3d50394010f40c452540030760f20129aa01e402070080c4184ca00419501d8511082c2039060b180c429101c0d00c02d00c030201d01c114264000b00726841d145c10180d529021001d00141445003203988001401808500d0440e100003a13604812070584080c4402001103110ba00010200d00d22801140300342c41e54104800b04644c00b4607010004c0d40d1340c842c041604600240d800c0718009108074803c40da900e1498000b1100010804090060a58004002e04021049555280030103480c0c200464450780e0640480319241d01000a80c003211000700c00500020008038100c82021254040c0d0030350300e03040380003804030030603a0408407015075811000c01640660b00f214a000324002c83d0001a144031005003000d03201d2500c0e40b410356561030103041003103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 246474127 1250 246472877 246472901
    0x10e0303030a050601021e070e06040e100501090f14190207080403050c010810060c02121f0614010206040209040b04020a030213020a0e01050901050a03050903070606030515010e04150e01 82
    0x1d030740c0c0c40c09880440c058070b820340e07000d070061203448074081d801d501c0001d100c40040c40c2038026014040c9080d080b540030510141015500543d11f1514070a070143c1042040200850004c011925600d49890300041312100d1082c021214202021111000d000d6050107070310907404560000051211840030000f0302a140e00100800c0002401000b448000282d0300e41e840710980c3c659100c0c6e5075104119000e03407414419a00411240300c282c500514040700d6011030188558102c514034800c0204180c070070a00460303181c0c0c8541d90360b2800c0c01044d45007182c00100860a000a2512b410564085404900d000340003520103120800418119921130241d4130085400511049560f40744900004c0294451921200418584881000e240d4062802e541075164141c45003418104090401d40c040c11004007280518042005200700140d424442c1c0030180d0700610050041da07401b0440d6040b04030041c1c00401101400c00200f00014840c0007041b140c01da20034402080a40c000e030011809410b10150b84 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 246475377 1250 246474127 246474133
    0x9150109020414150c0a052808040314012a090905091f060504020a090e0601020f0d0c050a0507061808070b1821060a0b010318060b0105040b1207080106110a020f010e03 74
    0x186d0305001002900c01107144180c03550038651080d040c1c103040000b00340d09004040400500017007022840c40302e04600e0322800d580000c2000d079480840080c017640346205240c03007018a04041881942e01c01d440002070081c4c004100600e00385041c0039075403041422040301c40748a1481210103030040581101c0300508010744155101c00340007202a05846079402100c2c1c0a803000800039580e50f100161541c000c40212004d0324840941038030440d40d010094606803500e105210f00c010000714104440001800300d89c0d0f0784901e64141c0c0c80c500d40440001c0e40a4645c5600440050005070441c000b160f031180820585ca28041240c440828952030000e01360445250031000700324502e48001c42c40302c3c81414541010403010800384015421124015000020300c82503450040025901d580301c2100b003081414241d051907540d2131084080d0b07001804270303110b0029010505c05480e8004860a000d4070140c02c003455011030042c001c651301c031300d040301c064811451800c011000d80d002e42045482042c029085d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 246476627 1250 246475377 246475393
    0x10501060206190c080604020f09210610081507030b0409060b01080c12040206180909010c0807050702030a1b051002070317040305030412170309150109020414150c 72
    0x41d4941d4811110140c8800c00c0724008885a0958821048115440c1c1c403684041d80b00d46c01440001d420804498581000c201300d035180d00d0359200d000881e00076501d030600b01c4448483c9102410140060100b400d40010b0385828068540b01042c554100d9030181c880f29010b80c0c800c1401c40c0540011410940c01900d05103400081c04601d81240314986400e888c1d0001c0c0fa1191181d01d48a4070500c0101980701000c075021070010321340003008103442011005403030b0f0310031a804001b40c5440c2c4185d40e105403a80d9101d0181c410243c210f901203500c94520b04010b030412050f6001700340c503900c01100c010300e041e0340c002042d5001c0b505804002d002e400040d1150741440000b01000e55201d2243c0030903940074030551031074175a40048004072000e41742d000c0061070801c0e2134000000c201c2072210104440d8002c040d102c00000c00781c41c402446c03040d0403560080a01d110200501881e400c4180c02445070305004100c1480400c0b0280a80f0500410994448a400c01507494108042c002c0d05140500c40c001c5401d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 246477877 1250 246476627 246476639
    0x40605030c0d11010219030e0405010e0c09010e1201021b12040509040f02120304180e160605072904021002060408031302030f0d03022503080703021c060906090b0102030c0a170408010501 82
    0x300048e0151044c0d400308451f90303c41503c205004412941e03441c04201c104001d080c1035111720000e000c440d1000c0c001c09420070f1100e180500b0ba070068003960a0141c0d94086005180c40100021150380d1075107a0b20910340f606020103c0c0341c000c03006001604c95000482942c0464035948000c200305001c403001d503900c03540c64a00140051103c0103010704040d090100c0c4005007100801c0d0303240030700c902c14840380c20540b80c01c0f800e0315150400340d01629089005140102c0d08090015081516050341d040d54000b480c0a104100002c900c07003100c801107621200c00c010005299030100c9812120981d01c0400c0a402840024038215112414001038082d4071080d6140c1034260b0060005601d890120518400003100b0740c03400541c8400700030340020320076004111181d000354000c10300880441140309089402c0d01a410548200da44609851b642e149010010304605200c0d41c94042402d00c01b4601e0490400700880ea1a055010040c00c030001803551941c7d03405540007140c008021400091049680d503503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 246479127 1250 246477877 246477887
    0x11d130c06020c03070f26120f040303080109151403010605040e06090607021c030b1309030c03020d05180405090115030c03031404081b04020903100506040605030c0d1101021903 78
    0x1180f01d5000340b2903800d000c10903c124000090580e0a9014200e02021070600c600d00450740070340020340303d806a4907000142003480802010480e108800b4141d44514500d4002c01b04601680150ba41e18603104010700420300d128603003000c40d60204a46100c5582e1500028014404d07a0300050f800340c502020300751180ea0210f44240328400c14000d54129a581050580c3c8a0030f0700d0700428034800440b80220040303030181d0302600341090098080013903079242804a0301100c5510000f580031031a82c00741c3c83c0405034104a80e00d4060074524000e41885541c03100103010454070200c2c248200d071544000740a0010940c880546c5e071001c504044003c0303542c0e040007801c0241c14042a070002d20b05e4928210050079000c111412103404a0091503103c84003481c203460004d1015801c1e500c684c0801c080d2503595000c12520288003032403080000d01e8241001017004a031000d5205900917045041164425134074255540d400903001030301040a0a90140109e0402c048052840c0e000820340c1480c0050561103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 246480377 1250 246479127 246479143
    0x2003180307050d06060801060f0305030d05091c05130f120809030a0b100f05090c0301030f0c0807080102040608091212130b07120e0c091b0f0c0a120503011d130c0602 73
    0x410003000223903144c074402050b5400c0c600002e0305035802001b90403440c5010b948801d6020120b14107546442103c0004120f1104070101c0440c00201c0109858400c0b00b11040d003c0020442040740f10f00c403528102c01c03890b000e00c001078050318000c0c010480c3e40c5581c1303080c03142c080b0141d40610610031901d001402014412717020b02500881413001a40840c0394104211303220700a60311070800c6415a817841e0743d040066600c100041f1102c030400c08000400c1d80f0100034900c00741c03e010700007580342c500313100700201040303002003000c18a5802820302030754105483c0e04841c170ba015040c0300c07260150b40302c4601403510003409400511004c1400d00f004045940100c00c095407040302c0806104103903200d02c44076902d189071a1900c0d407042c080c00c041100a20904006201e00b80c0280340e050500308074a502c6041d98210300c0b00301c94640c010790403e408100c0d00c1000c00e920074159007801ca0455043c40e104290095480e560f82c1015181c0c54042120b201c15081c1510480d60f000c105042c0303058036420001e45890310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 246481627 1250 246480377 246480389
    0x7120f1b170108031e1615020c012f030711030403150b01050933120906010f0f0513020f0a2001020711060901051303122003180307050d0606 62
    0x19000001c0344844010040301d24140e14819081c00a0084184000007580120303e034112034541240003000003030040c0c21f9402010004400180c55021540401d401d40d12417080740519012140322407031580d08c1003c1050180c0b046200c1c11612541c07040801c0c1c40b810350305403844040c0d110105000040203d00e0080380c10b400d030580018404540c407a0010341d09400b40092803603001d81c440d54416202c07002001c0304408401c0ca046001114103045059899907403028500208094200e803c1282c0e0003c2040101d0040090440d907200140c9840002030707403c1168001c0e1403050454010f068012980754042c0e400d038803030384281e05030394000e41d500291008101e110020400f6800c180d000308040d10600c2514030142d00100c08082e030000719003c01695520074031480303052084c18451080d2619484140101842c814495016440b8141602808509031000c60a0b0700c0010010680d40855001c01a58141d0355460441120701b602507000074102403181d0070954001c003030140c416092101640001c2c00300c502c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 246482877 1250 246481627 246481667
    0x30309050d0503190201060b0c0f0c031c14040302130c08091f020706150b18062104050f0607020c040f150308160512090306060907120f1b 61
    0x354a10600881c1400c00318050300c1904144014881489001040b503441301103840002034880e1500d0900125820270030080c28503a0080078001404c0008029a2840c204210010310003104020307146003c00d209408a2020040181c070343c2c2030602000320913203000d56070080c5800d03000004a1540e41c001d089644603c00040d0344400807070104500030a40440b400000d581d440070740450104020080d50251800f00d42c09507580c804020498660f5012201611942440c190703103070039070000902c6115182e1906031040c03504000f4008100401c0120324500075841c0c3c0100544d42c1c2e14105039040c60704080700c0840901611042208a0f41d0200386070b860701600f00d45c10803c02c407001c480c42003100c0c4c41807803ca107003850098090002c11031b400b0241c003280500070fa600e0000400c03030b035a180c1481c040ea05201c0b40c6210102d1840c840303290a103c4160301002c16074030a54649001800103001c8506603094500700b030f41d10808a1002d040a8000389034181010001d012454101c02006144185191200c42004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 246484127 1250 246482877 246482879
    0x415020c04050c0a021b10030b1f03060303080106030b100e030a060c26041101030b0d0c0e010f15170a0b0307080d0201050106020303090303060618030d17060f010203030c0901030603020607060501030309 89
    0xc00c40301b2241c49114040d00141610700c0c0c0441c141c004162184200f44d000d0742480c0c0b07040e0300050000044101c4c004560b0b0100d0b05520303600d0301505c080c1041c0c00100a050500040000f1512100400440e200c2240391030390300d212408001c01e04240f00c2c031001030030407404c02c80380c0109103030881140300e44030012500c1e0406003122104500f04000003034ac0d00806246919412403034a6100b030704007041c0d00308002e20301030070400607640d1107000402030b030300481000300e034400100010b04802c1e420400034401524000e1094010b4180100800552000c1c08010702e01c1c800450081c0c02c2036448201901000340071146032a48aa01d641c0c2c0d1200321540d1030006608080021904c5132020096034000e603a607071b00035400c0d601c5003405c0044582005c010610040030001449131036541c02c011020f10807009849580085c82005948a110000241310f035024210700d00404900b81d9002040b2640401107248181d100c01e4690300480141c1a10b9101a500030b201107800400d2042c00d038801130499100381c840c04089 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 246485377 1250 246484127 246484153
    0xc0f0103020a02071a041203080105010801090b030607081b1c1802030a0f080d060e060a0b13060503180601030302030d050f01060807030903020c030f0a030219080415020c04050c0a02 80
    0x30344280b21000780140c1020b10104580e01c50000482010610303140c07a82d05050300c1e98a45011041186410b800113404680100003558005ca03941e400f410240c0003d102002070000420340d240d5020b001c10b0100807400740050350700f280400c0c1200c404403003071107183e6a4402d0084032000c6401211403c498a6160041010442c0c6030280440725407540680640510310880d00c0301d08500c61a0b20041e01c80c8802081149011001840b4810180c04010405c0704107040102c20f0041c418981d801c400b404da038003001510700d08180401c0741022640740b458082d550f1b654800100d41d00041924aa110f1403007110004000c141c0c011000d440080100c14040040e65500c440d4500296400c1c41030710007161003080030910307451098112100440c02401110142c003049404607207003042c20114640c00e908a404c0e42c01c100344e0306129598050b984150076070240c20311503c0e5000b9500c200d03c00c0301541c040a02d45240002d00134000d03c1d820b2074004108025601d820425066194008941d410043c0114041d074012 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 246486627 1250 246485377 246485381
    0x6030512090427020622230301110d0c0e1c170f070b04060207050601140406060e0307171f05042315101a0406020c092404020702120c0f0103 62
    0x5007455903181100e050f02544c0a1105a42c00300640300e000c802095502d9210f144081400c200511160700214401010900c082052140034500b0f94441e904181c510b2038512551800c2c0e0780303c040d9000d000946980c80c00d000b44c4107420361803407494011201001c11f035a002c002d01c8900d0002c6014580010b60106801d484115502c2103079080749030032101740320000c0800c0c40002c44545c054454800149049100d49175180380507002d91001c030760802c00f24071034081c5082502506c001094203090030b682c4050a10000707920b940f02800b130441060007180d04080482d030204206c192058042e99120000000351072058040c000c00c40303082d035058030340c0710b40c4040000301c0400201c0c103000b002d0042c09862009581d582919580541030141d00528681c0c08604a01d8180c0c00c5503c41505200c1c8950b039614000b006403d10301000240d0344030305000c10801110a811414504201268144618050559000040080c01241c3c00690001c0246036104122900052a150300d403804a8542c1e080790b0303126004400b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 246487877 1250 246486627 246486671
    0x1020c0a080a03140403050609010b040c050406080103110d210315081f110a08100608091915020c0a02040b0a180f0603120210050106020a0321060305120904 69
    0x100c2e030301103600300d40401e2080341450115013030110b00e00e00e456a81d4640c1c40c54404161412a6141d40da40c0d4016600c1c80c0c2482086000740550401e01c0c145840d00703e003d403644405200250207040180c1c004041c40c0d0792750300f02008960340308051015403030841403550311001045c200b40b00441e10300840f48a1a0340c047c680f050445000e10010001001c0e0f070350b058034007c0030129000408545924980c1c0b00d186007240a00301c03090003503903448414030701075110003500144c65111209002d9007400303224290b42d0220340c403800710383c0c1000104003842d082d2411400f083c030003036140c03060240301013200f03c2200000300307100354082d000300c0d801c2c0300010401d0b0410401c00798610440d0000c3e10203202c1c54150000e290030040803016134103030014610f0340d01e0b02e481541e04032800e81640140c01001c00416491a5445101c2c050706051000f4240800199400340c5081011014141101d400c0728442115000503000140074550140690f55840e180440038a040c0c1c00200240b4440c0c1d0400811000603980c011a4071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 246489127 1250 246487877 246487889
    0x80303040b010603020703020705030d0c020a0e0606192625050306010c060b0a09090209070e010c03050315130e12190e130911010e030604120f0e030a0803010501020c0a 74
    0x41e1460b480d01409800a601c828402c5083d405200800540d503507041c40010075004144d161048488194410000d50140c140c00034880c11000f241840707078a40703480003030300e80420703121142c44c4039481c900c44151420317900f01d10000c00c6500c040f10495035403901b0782c3d07483e03020303a201107080412320680c00396059035101c0441180c00000c50500005500e03620905103160204d020b4840003400301610300104800b0710031a04403100541e182c55102045017800d03000c95901840501d41440c4152032600028500008210042c0800c00048003245003026031128000540400420310140800700d4448900602000440401c160059800f202d8401402204407168082c180100c40f440f44240041502c0c085039001c0d030241c01c17407103081e60711440d10030074810b5050041c0204007401d0088944400140030204865a56010f504000107110000e000b42d071000311100b82c1030920340a098010542140c20309226040780f5071601c1001c1d00d02c07051225400085060f00e40a03801c1e61180b5107002c003400002d141600c961 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 246490377 1250 246489127 246489143
    0x606030c030c0804030813051c17072309061207090510080a0903020106080607050408070501030b0d0b0406241a03040302060a0c031b0807170919050a06180c08030304 73
    0x60020340b1a07106c103a44959005806040d401e00d0343c4030315203480c0040c0d491041c90008203140c85c3c2125000700d013800c0440d8103080318090701e20341244018003030f110148066540c81d401640045a4000079400c0d03035280c050241800792030b42c101d058000c003581422b40c0c0c0344c004290b010b030b004034290802d020b0403800320500b5201e01c4002d1303d41820a400403c0b07010b009a08556803000003027040c4a05010040c051300c0b00d551880c0d01c640c10b0605090800465520540c14180b8080542025454001c1c400d0b802e503411032003011817952141445c0b00600030b82c80750100130030805010110348038620607072003040c0c4800786456030803181e800c8414a0180310566002c0c000d030b80842e000481075070840d000041d490006241c0410700000d5000711800b0b8900c0000c821021400000422800d20381c490003000892803822201c0b441c0741400c0442c2626020200701f0884032004048030301d0300f1310900b0010321a0040d03211004200303840d0014051038244414504c100d13420b2402c81c41c00560641e0020036a80076941104171 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 246491627 1250 246490377 246490381
    0x503010b0a060e060c1c031410050105280512060906211c0305070806030a02010e060c070b0c030a08011509061b0b0f01180608070308031e0a0606030c030c08 69
    0xa542d034420100c0c14070391001c0f00300710000000005004449072001d1000030400011306c004c4000d401e648031081030340340f01c80c611001c0045c02031500b6074840071280c0a0070802d5a4121826038901402003404400448aa104500031103a80e0b005000307015240c2040a000700c0c0703840304010010002d0082d070780164010f1041e400c010446000b040040d200e130140c80300b15583d400d51030301c0343c082252840c500000031990384c0040219564120401d03581c890300440c05480b85d080710390300281a12004400c06401040c012414003000c035010071104000d011703549941345d103c010720450242d84e82e003e08220740001e400d0400000752000c4510140c9905d526030b4840103000d5041510841d8046043c6681003100181c0e0000b90020030b030032500c118060021070303135540304075818907084d0000104403045010b0300e02c1c5041c10801001e00b0102e0700707905880d40921110380c6da4030703091443c6040c040c3c5a0102c0707c0c950a03c50501c4030280c070b5988440b0072524140c4040c03100e50301c040803d40803100d54050500200d0350b4100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 246492877 1250 246491627 246491639
    0x1701030510111c02070605090a0c031214030c04300f08070b0a05010801060501020f06011806031e120305060d031101020c03040f140a0810050a0b06030c130503010b0a 73
    0x81c1d240c055400b0642400d0038400704600c12685543c194030300219500103801e001b80241c90203031b168801d00c440010811341030541d07209044082144005414800d0201002108610400320400c6c00088010002e84074100a4003203240da51007440303070070780300340414100115040203401c2e21000314032580d078021119001500d64030040414880f086950280030040b400000d0f511514071030141d0040d03480081c0540c1058010390843e05a504114103661200501480c04000055401c0c150740d00c070140c07014103803948641c0c040070b00482d405c014410304080940c0074103002c520f840358580d1800b03600024602200d111742902111003c0d5907442d00100b80d4581074012174016500a080030207540001440e00301d45500f841d0071500540c202034140c0702c0b03c0c2c1c410040240e00d8504950b24580c2204c1c0c0c0050f29141c00c0c0010ba8808002800094054a440000d040c0d6115580070210322440a081150780e4503181c041c41d100740e400840d540b1f500c0918940c021403c0e007414403403010300000181100d100e40c1d08042c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 246494127 1250 246492877 246492881
    0x40806010e070914010c0c060503060301360501090f120221040b03040215180f0f01020304150c050a0c06030516081b0405060409021b0a050d0507080c060708071701030510 75
    0x101c540307062004040e80a80000c05134400c2400500081e030303c1c180c070bd0400e081050f094842c0c4214108802030306901c000300c440045e00d54070f102002407650743d040100141c0307041805015015400f0304502d83d481454400d004414010300c004106580c2602c0b05070300c80c403c1c8001d80f0b015003082040904070500c024030503800068000e64001740000c084488030790f03120f1100e128903405004425020045440d001420b400e0006c42060810f0045401d444010342c03d0000035560b0190348258202c0600aa0102c04c3c600d02844807089aa500034050320385e081d81d0707424100400c090038412480004e140400284c01d0f10740c5038848810b05030440e602c0c0c0349aa00d0314101003400741c41d03040c41c0000040003000001205d64500d80104002c100d44000036032101012040103003c00141100100e40d5000304031403c00007840410b15064400c0e032030401507100c94850500e1040f50090990340440e6104030014004a40e80180c00148204841c0e84c48240c010040000c0c074450030310a20006200740e0200d0b0034074203030395030613 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 246495377 1250 246494127 246494159
    0x7030308090c031609200702060912150f010617150f0d0b0103020312040308040509040809040513021203070302070905060103020708130e0a0c050915130803040806010e0709 76
    0x2074089449424000c0002801d10420b000c0c40d8030306500e0700348200051559030051580c0786000d000940c110100d005040540d610072100000c0c4503141c00141c000095403015507400c8443c0c100c400702c842020742e01900d14441c04042d2868114920580300000b52203100d0030320700540c2415127403a090103840310556460854402070381a613000d8000544400191189425402601c0c01403004507001d502d03600505081c00c401c4d21504210000c200401d00100d031031482105d00b124800d4580d04c2c00c9a4403410028040d0040c029480c1e80981440c0a00c44804a00100c2c440c55500860307500c15100b400380038285c0d80740304803540100035811417502040800a41d5004660144040c100949002c91a90341c0f800240e102c500c400100fa10449000d10803150254031079603100401101c00c0011121406019009008034511140702d15003406805860864140075503040142c0440c00b46e05951b00e82049944940150041184c18402c01000041212010710b0050090003180c0b280c003186420418404124145 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 246496627 1250 246495377 246495391
    0xc091d152b0c05030f060a0c050301030210080601030f0504050102030403022a090c0403020907120b0a0e040b040f08041d060d03090e040606030c0b0406020d0809030405040f0f051608090f07030308 86
    0x24298000030a070311305001c030341d0144051601030710075481c0888035601141d460030318039401c0140070f00040c8010b85405017410720252484c10140000d585440048000e00650f1100c00c0c0420f0420041c0810403105401860141e84603400b41c9201010b94450012007440280b271549030860070820190841c102004c5135500312092100091809450381c0215280c15020b54030fa5000985c000082c8415246a10a289c0081000c4940c540300c546003049194460402400140c04450040041030070886d013052210505680044640c2c1c0302c659803400340070681c0014070140e036404002d0001805600d03242c640500d485038507450b602d810318105103054008c107200506c1100c09941c1c070300001c00445d8040c1e29460052422030001c3d580c81d4145180241400321a401c032100344901c42c03040c09400d10300030060310144d843c107842c0020b200c0c041c0c0ca0001c018050103040c42c0d038a01e1402042c4508540c00d00509903401646884038041d9440390074403140d46600074803406115811000c0180f000078460141682c01c084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 246497877 1250 246496627 246496643
    0xc0d15050d03080105030601060801060f050c011b080601141213051e011a0904051f060b0d061d221103160806010f05010804060c091d152b 61
    0xd16040410644041450141c000c14045001007010f4a800c008541c0505150f01e442c0e0440d51400e0f0024062181c3d0702d94850070b101000c0342c8440005001d40c4202d540f002c00400f103001e1516269405442050103580a60010f0f04030748524941400c0b0004403801901e00c5121417150b5500c43d02450038000280204481a006404841050a203c1c6141d4910300380324100004181080480f81c1c2c0c1d400e10b160301340e10700400a01d0100004142d0104141c0902c10383e0030b888031441c0c000c07240300e00024801a00102e0481902140072a07404410f544444161a6548198110409646001c10902c0f0080751083ca100001c2c010383ea0101c10030502e09a0382c6c603c00c03642903140a075900d0000b03042c0303141e41108190a6180c00c03810020b0540400c800d5004000100d00001513a045c800001c19040c07000740094080740d15103820301d654920481109004001041600c0f40ca0100038161401d40501558040e102900e00d94981450380751151682e8a05110005070300f946416081049001c03105030380301564555 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 246499127 1250 246497877 246497879
    0x106051809010b19082a0d1b140a09141902091507050d030204060e010806030304080610080111090d060b13050108010207051e030405090903040b0d0218090c0d15 71
    0x5150160840440403c0d5034240024030309100e80c00b8508a484618102500300405029102000d9600110358906e01582d03541041d1328942040146100304040c0240200406880050b980e011218400107080003140c1d80400e8591b6082200191150582c100300303030410500118006414000d19081c0c1e01190117409424607a000c000144102c5910346520100e1030005010800c0100501640c6214440750404609003402c01100903c03586421017202e06001500002c00c0b03080c0c2e000c000f654024404101200c801d49810800c20040a41d81d2154003519030a0030819010140440300ba100e0a402c0a007842c0c00c24605074039100050800612002d40109074083d000060301c820f40201e0b0301800c40d000001d41d40f10a41c1c82c02510340300e15a41080c2c0080303904640c0712940c5074048210b0382210300403540e6003002c0d1180141d00d030075481075900c03904000340c0004a24400b40010380107008a00c401341c03490610740d00b102040c818450001c03204101410f01c100840d440c1c2c0005139001c5005101c1c2040614122 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 246500377 1250 246499127 246499129
    0xf0306050a091a1905040207061b031d06040b07120b0d0c18020c0a1403040e04030f09150801031401021303061409030c0606010503070311070f12020106051809010b 72
    0x340300301e4101c8052140c0b100d15981801c00d01100003c512601602c80340c0881c0c0c0500301c4c10b10001d91078000e00d4441e980000700c0b401441465001b003103a4002ca81039510540d21429030140040c808002130003040d8410810880301058045401445641c210040510507614858100d800314104506400b42c1c0d659024240b880d51600b541112016100c1c45130940c00c242048941d46020078001c029400d22401082075480280d0080350030403031540c2c030100120b607106803100c80c00c1c11409250031854003403515404010074582e10003d808200055600c03005080c039151101c2840d80c5005100c032a001c50512401000000c224458104800d81c2d0302c4001070828005094121071800264002d44100d034483c441440c4060041082c6a04071040e0750040d881c0c035090b40c030500d0301c0d54802072660741480f4000c00001c04007070194100000b880d980c04c848503a40d0300c0616003415807400c56001502c1da0121000454407090051048009035800100311a68480041004144821000304510080e541351400c03203411f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 246501627 1250 246500377 246500389
    0x1401090c0f090303031e2d0c020a0807030509150904050a0b030d0c031809020903010e030c0601060e03070e010b070b0901050108030d0207140102040b0705010e0309012a020319050105090a02100f030605 88
    0x9404500328035580b0300c207100c007000b1084c7ca0a039001c00076041d04d002c5d40301204a4000030125400da50044860761250b41c0382c00c00741d17040c0c0202c4090302d1308180d410000112440c50741c0010030002008075001c0203191035030380102c41181c1c510310500f07405600880c9228610780c0142c12480035240300b07203008184c50a02c1a6101092403065010060268000c1901801c07490203008821000c05500001d50500e00c0034005283e64a0041c03107100d06009002d070900701d161302c00b40701010150101020b4405a0750750707038240d1001da501840781590f28515240c007046000606000305c9048074140801075041500b441d02d404001c1d4440d810450384a501d41600074015002800980300400d034800c101d50300c0d00800d003403c5094409100d900540c0d038001300304100c0f0580c0c0110451b0740c0f071600c0340c0b01d04040c10600050a4550306074910081c0d4075128405100000443c1010b80c01c4180d84503074004c0c04940c0300c3c2000c4a03503031104100c00940c00300d68000d900720850710903910603500400501d40440e00c20342d15408684 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 246502877 1250 246501627 246501641
    0x203010b0604060c0309091a01080709091e0b030f2e06060206040b090d0804080c0a020d0c14090c03160c0b1003120206150618041401090c0f090303031e 67
    0x804034411808003c14150460b01b014000e02c0480b9080c40711140c103c0702124840f180081c2c0368140902c2002141100348913401d100060721180d1030030000d0003181d450351000c02600543c00c03c19241400c207071041904000c50b0b9106030a41c034500410400d240d200d250041e0480c04011501c008051400b4030320754a02c14041c150080130307a0703009802d40307017454104034040003801060b954050703004100e8659056400300d99940d0064000b0001074a500711102c1807414900c20110180d0f1000c03c410000043c0000c000c008021200e00d20140d0b48520081c03000d0000c81c59084800126000052002501000284814400a000524007a04a1003443e40c5a1408941c144c480301650018440300340204000c444004140c801c10740000c012600d440c0701d004840c2e0347c04a82c2da84c020b0502181601c540c1c1003003440031150340c2c402003003804007202d02d2058003a04182403041c18400c2d41030010070452180604480040c1050594071902c40c41d05584094002c1c103441c21402d80e2200c4086103840c070701c584500c5442 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 246504127 1250 246502877 246502889
    0x1a0301060b090306070903030c0201080709091b1b02030709020c010902030f0d030f05010302090a0f020c03161106032a1204050109020a0e060d14070510021609050f0408070203010b0604 81
    0x10b441e110640b060500e01074006102c5828800540b0040c03012a4004070741841650342403070304036030a07600c1c000c003220088010307400400305030b0034901c00003445605803940240340c0c252503880d91103042e0078a040c00040c4a00c0742010b50143c00054046c8004820ba800a03c2c8050301340001044a0702e495022070700c0c029070f0030103240803500031128420000358503025034001501042810300803541144c00044076906d001e80384500299035240420603902658042d03400700f109120070707281c0700d80903001d81004028210008481d500700c1c42c40030215501d0517070183c80c0038646040251101041d103141c061403449101180d540200024400b05440c001e01c0c3e0442485603203c1e00000c52542d03280d01c1032101d1100c1c1500002c00c03481c103007002c00801c0d1700c070346c042803000f1a0803420b02c030400000041d00f642230454541080390854160361952000503000100c440c80a00c1241644d601070766203945e00c4c011110141c41e01a8011145000300e800700340d003580540305090000300001042c4010b0700004200e5442a8440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 246505377 1250 246504127 246504149
    0x20d18121b0803030a050c090916110d0f090906120813090c0c150606050d0f060b0d0e0f0606011b240c0f030207020325032004060b1c1a030106 63
    0x841e091450141580001c50007900303902307203080e41001400d6410000c24110000403c170040c90300041c89801c0c1403c07180000c90540b6100110f2800c0103003200301c110410004204986000a044001d52040c50120340c0d05050614003100141c2c0e2311801a48042192084a400756002090803843c078400c0110321030320394569614203c5645021000001085d9001d600c007880c0213420001380b50000b0864585840319280010903a04025000004203a290010144003d01080c850310401e442e81c08070100c403084400f1510b0000e003142c0c1d440e540c1c200450308140000d00c00303402165031450002d0511805c1d840ba10405043d103091246194003030300960a14502c0c15224501185e020717030019081190591b040c0360652619046802080c3c1c0c811410710441010758112084000500040c00a00081c690101e001141848100500742c51070000c604103600c582d140c008001003ca1030041100e907a0380e4020042003110f10411420001802d40c11006600340201202e0f0420695003031007402d0185c1500d00c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 246506627 1250 246505377 246505381
    0x304090b1807020c011103070609060f0e2e02090301090609060b0d0b010e070318030908072103110c0301020c0105040611040e0c070f0606030b07020d18121b080303 72
    0x300100c012494681189020008082c05022680841c08500c2c5800a08040b9000314004040c546140302d03005001c1e18251a200000341084140e411400090800300014040809180e6140d80c0314202054a031b40784084c1081d06003111401c1102c83c081205449400606003515400800d0070340311a41b00440b05030781e840381020108223480c8592651140151a001c511403807556512080c62011700030117202100810025580900c06d400c180f4081081c01c03804c550400940c94003501104441c041d0079101c1c0a00107011600e24503000320740c1d10501c3d02c040112048a05500c0c1510300e0204882401201c1c050390305003e8036074030b00340024003162913080300000301840c103810301d20100c2d001c050f0b5860b142d04003084108107000300c4d6a1065004400300c44050b81c2c9050605c0c00028071021050010166820701342d000050044840d05980b080f9070340c1d000d4031400c0b805000c00f224240340010800080400403041840200b0445801c036504501c600801860721803a00d54091180d00c86510007111640300000b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 246507877 1250 246506627 246506629
    0x20103140408190f050a030905010b03012f03040b06011215080a03081501050403140106030c090204030b071812020f031b1201060e0a18060f020c0c03030c07030305030403020f0304090b 81
    0x181a80502d0b00d14a0081c1303100034000c60003001c0c0e2065406800c105625020036205002c0300b07500c44250340000800030071903001e800c00c50545104003010307503501407245941c442140024650031644070f141c2c4510300c0c0001e50384903801903d050314001d07410401e040e0340f003070818440c2000c008150b000e021000c2c000c101030490780c034004249060080c0380c174040403031203521000c0c266000400e40e41505da12201e884400408544100d0060505a01c003804400301840000741083c02640140280c0f800b4002ca0200b90350b4000d402e54205410f03140c42041804086010081103010001e050743c028401490b020250f6004030019103007555040790000ca0640681c81090300f03142c520f070341c403c510100c60003d0210500c0c10301074002c1c1c102c0c010824080b10751918850085600c14000c0003c145501010400604003c0c83e000c100a4014078a140484e12078170348030141c01d00d03002041da1034100084004240c040d0a6642c02ca605402c003400071001c2d445440c1c1c0c00031010100f400500041c10400c0030008000240d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 246509127 1250 246507877 246507907
    0x303030222080703080304051c050711040c0e0f01270608090a0f061d0102070c08010501060c0f02040b060c03030114010207090e060708061906080f060603060d0f020103140408 77
    0xa42444401070701c00a080100b1100469020112a00a2581d0b9100e55950a0190510a039003943c036004c0b0004046000c030f199001000781050364050340000514440400a002c11150075040180101d0030071500e41d1424a40310000590b5944107241c813030340b002441c1a100d60030075091100d1520400d0510424071410307600c0a04146e02a21010040c02141f520f601c0714000c00c2c5a11001400c100d84403410b9200b4042030100c54941d68480b20021540c5264508150b5440401d9014414481d400c14000103181440b449842d51a503802c503000043d200e2650b42000001c0074900050f40d0814824401d04031000c1d402d01c055402814002c401c9a00302508a000900f004120b81000e02158a806c4050910240001d980c0340e101e42e09040c1a40c10740c0740c91000800d540d4065020170090080200301040300d641c420401c0b4081c403460000f801450f11a1003c019580c0030844a59811000305c80481c404a08544a0008414018103000400c8161600c150101d035030200d07015603900310300241180141c0129 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 246510377 1250 246509127 246509167
    0x9050c03060c0f030402010314011701050c0309030409050a09080f192d11030310060e0f15070807120906020f0a0b13030513080601080706051303021203120103030302 73
    0x1280a0801c528190290b030102c0d0080380d154040c0b1502c0800083c046902a610040410031001c8402841e0340e0b4444000c00301214020844040c2d500340000300c1d03001d80c0000c1c2038078003603441d2002641c2010b040640e645c0013440c00800383c40c0130700c0e142c80b21180032075011401001c240003000c003810368420011079002c42c40c030b0740c00c0c4904081200320704008580b0501c0d8564040f00c02c40e07425010348000092101106c0621842c00c080500c0d02000003808203030a0a40c206034112500c0f078845003440c9008004000c0c080392611002c0c0d8204a1140301280001400f00c001d0a03514420400c20f400c00940351601000e1000c804200004110040024420717560104017020400040034024582c0041d16610101c02c400701500c2c1840b18940900660200350090082d542a0607107590710b1403807180e0710000d01e5a204e2081c070900c1c149000b11100402c0c024072800844024207000780041403150301e50740c00e00100700e911140020450006004600e000c0c1c16100c4214004e500130b0f6000358490441c821303000c02c0b40030382d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 246511627 1250 246510377 246510379
    0x703030912090f051309150b040e0a0c290a020c130e0c0f011205090115050117061005071208010e310203030910051908131212060909050c 61
    0x640c0030308005a0440380040b900713440e0300380d643c01c03140842400d00303130007901d5401001441d06024002968030503220703900c410810034045400740034041d00000c459480d541481000340c100c9800b42c4c4280101a450041c090055540320740d03c6045503519040b0081da42c00c41210180107070043d6107003440780d282641c0405c400424046041025200c1a0529503868481c2d40340035020f120b00e14986440c50f8025201c464525071146010b100034038011440c1e41c005c1c0042c80c1c042ca64503004d60300101e425442050311210211403c1c00c050300300d4a8000402c42e201028264180420100700020b0300021100a0354819980321134650140c0e6506007050004103146c01800383c0c00c80e811688031680d1825000d05603540207141003c14060140b440d0021074110711420b107200c3c1d000f101c100c8942021680c4400100034046542000c1d0314090070300c5204845d0103031f00341c079400004881f4082d144082801645152444011820302d0950b82d100240c0d41019652103911480c06541c1e1a1000c105114041c004000c045038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 246512877 1250 246511627 246511637
    0x603060905090c1020030403020907020303040302030706110912060a0e12070209190204030507030302060a09030917070f0b0c10090b04030503150402030c0a17010e060607170703030912 81
    0x60541e000300c1e80c0d500d01c0011144513880b1134003406601e81c0580b092450307804501165110010320075811030798a520503c0101c1c09403200c10005446548003000752405198540d02440c070305a4241c51f0b40014000e40781c0008996601080300c010680d40c0e44600c1c0070395501e40d5020b00741d1490500f0310041203d2162030780a8a07900090700c0000c82d521000c088400055040750350400a0729042c0c4181d003203600ca2220743c6540c0344000b5021092100c0028084d049921984c2152071694600302e50000b0340304000c1000707020500e050814400d2418007070420b210013103e001100c181d40d5070346503c0410002d80d540f000550400000c0e00398042c1030117000c0260720b80325a01044c0004086a40c9404003080010f0016081000c00b0020860b0116800d001d005105001131065450b801c211005514542c0450400d0300403441c2e2402030320b812181a01024101d451040103900141d8650007884056841040101c50600c8000035a41c0e0b00d200000c00351410500070358000890501070300e010001911180c00b5003003031003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 246514127 1250 246512877 246512881
    0x3061014011724040e0715050c0703031223011a0f0901030506130c080f0a090f0b07270e010602031603050d0e03070f05070b0a05071b030206130603060905 68
    0x70060500b03400c00a120040b40c58082600c054590400e48100c4003139209081180700a031801e000210750381a60764051029034800e240e00c0003a155032046c042540c10030313044158200080ba000f40310401c4200c0d07104c1c001223042002000304001250502c0e4101919160390030040c09105007050b584200100c0e194251441e000098804182a000d84100d586c10541c6a20004120b41c540d8003420804c6003407190700740041c40300803402403c1043d084a0340b1060700d13082d0000510390b603c540110003038640c1110341441c80203d5901c03141540607009205170188004140c4807101c0d641014a20810449200640d003012422f140038818081d9060740060300311351003885815003168089005040c40c681c50304140f80d07101c0110319528080c181380c1114002500010605a080c000343e101c6100d042e030300c140142d40c00b00391280c2c0340300b449000c1d10805000085043c02402c3c006450704d0000c04006419504a05030150f0783d03400942e07030ba4050740b48452140e03202801081165050300030b140c003810080c1800d105038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 246515377 1250 246514127 246514157
    0x80403030f3e030423060f0601030b0117060d0206040b160203010f050708070c030314160207050102030c0c06180405040f061407051909050307080d0e030c0616030207050306101401 79
    0xd000c044d00181c486401e4000303021691000307407980c4400014010589404c0d2501d0740d1100300c803035011a691800f2a007803c0f814030466100e0304c2520048001b000c01d444c072a89408050100100d135100c82240c020f0400c000128044030008050060303465540c583c03085000f90b070b00c1414213440d00c242402e404a03052800340050280c2041c01c060380011b045c600155628803505045014011680d102c1c2d103281590407d00c140f03150306608110261030a40c00701c40c6141c3c0e542e4012a940c1c03280c918000c400d5003141001c51020310b0710a000303003040c10600c1046403e03000c03400d0014084410a0710111004035503d040c80c1c003085840d002e0303008038a1400041d6109894510000350451040d1010303220200c0d030348804004014020340c00c900141202500304c42c0742030b845021080d036403660340c00400c0105111410000040c81c0c00030f0b458051704805080541441c40c004501d50004800322070072402d60080b000c012416440400c440b41c410015060300780c0f102c614007802d4421800e50007030344604110b070848840c441d13 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 246516627 1250 246515377 246515501
    0xb06040e071e030c080708010614160204060e0105011803020102070902030c2701110724090b3601080403080a110403060e01050c1801080403030f 64
    0x11911103260800155640d01c10403211000600b19003101c08000440720100d555259104001040f41520b40c2d0030943c403100002d07119080244100000030b103400e146a5580c007a40c10181c0042852455001da030300075240c1c006825a00c8a4106004a500c6078004002640c0e100c40542106000c5080c8a0310030303411500000d4803903074a809030341019074001021800c440d400d2401c40e907851040e004440f1082800b0f401c0840b520960548507400900401e25505030418046008030441350501c00319800074010b41800d0140143c410654024084051000560380d20700300c008124603c180d138150f075a005903c200c2c0060f8039000002d582e01c00f2198141d02a07a5982110140d41c00c181c150800b10b82a80e954500c0d03e01902e106803044e40d1652010400008001058120003400c00c40710009010590303500e61840500d000d0075902c540f030103100e010a0143c6500800441c0e82107402443c0c00b1580019500142e0182c0b80910840e0516130440e8404511780443ca01c826040e0b46161a0b42c84004c0e002c2460401d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 246517877 1250 246516627 246516629
    0xe0303092503120c02040906050103110a1d060301110c070f0e090a0b22060b030106050904020919020d0501060509010207050102010213090e0708060903030405060c0712110c030115050102100b0604 86
    0x100305505200d0701c80c3d2460040300c44552180d4010b00074441881c1034500900586030a00c021218040102d215901d01e1410503030920595100d00d65a13240000440b0b0140003042d4090403290f0155aa0001f81c18942c80210041c403000c1e00020041070102e107051002d0b00c4c0c0d040158004410340e150b280c14004c140f400030403000140d03600201c0011035926038040c1140d80303004d2030395400003601d4110300860030807101da0400355002c0070440081110035a21020b1140340201128003c0d40310b404080016513024040244198003201e0f5440103081c10307201e042d50740072030304280c00160100f07001040d1300c840f6681c10481e070000350100384001c0d42071850368589191081d43e5070007180602c03500c0e401040307111141001340c10010986002202d015040012000e43c4992095405603082c1c001c04e40043c031011074102c1140d201c2e95020100240403042000100c0300801c955400400c5401000c500c620307566024000d0091803600c3c1c80b045225586060006841e112880003c20f06c0e0314101850f808180e6035202c1560 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 246519127 1250 246517877 246517883
    0x90b01050121050a15090501030209070503040615060e041b0e0d020105160305033c13140d031505031002070314070b01173403060e0303092503 63
    0x2c0c000c0700c1c01e0101151004182c02450540c648020090980101e03005201c3c00c4070303408007502c9003039213413003002040e80c07000d01010f50440711580100d01c12078405d4004603032040c003852001076000042c003112103d8034100e5015038000740c1c0c0b107003041e285441d0a1064400324070030301c02040348400801a0240c0a54410340303c40f4420100c2d225020103590042d01101d0b048141c801b5140001002e91a0140c03058000342e8140680d0440020345100403155000c60080a007811008079407085151600070030403580040c804400c0745070340360440c800100d50043c0c580150b01c03441c001d4101c4003c3c6032401421104656403c3c80128641c89040200b0b440204415030f841080308d50140c0c2d122018142640e402040d01080c1c412450700013010814042d100045605955050688800d03d407004115241d850244000c0403440aa4410710220f03201e0070140c0381e14843c2e05080c0340d90b00c03d81d6281c40c5e1030116030082c10a807042e90400810421240014480c010b0b400080e034a8881e61080c41c86581c000310741840c0401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 246520377 1250 246519127 246519137
    0x1e0304020a051017131403040e1902270102010c03060e13110a03050705030c090105061611040f0204050f011b060507200109021819240806040c0504090b010501 70
    0x65418440d4048100c4c00100e5162000142094980b0303928100001034281c1d951000398098091482e00402110110381c40404410420703101c1c1e04014101c580c400c000608416400c0104088051103490828020700003a807280c0e00010400c0c001900303646031498000304140c500030040c00b0180001000980050320b0741001c1c130155003175181014002c0d81c0c00e5289030340301020040010412100094010a5401c16002d4924556000b4180b1204c11028002c260340188180070a000e441c25030010142164012103100b006580354102050071110314044004015800180900280c107183c9216a4030703802c2071810310b506c10321071442094040c0915400412094503140450403444c40342c03112060b41c519440704042c2a04070804203e00911140380c00720301030210305140340a0800c070452403a10405840700d1502c00007a0b01c1024000501200001c0d000c03011000f0049040c010206805030043c0107276000030681400e06090082d000000c5074000d501c100d050400d14000101850601811a5000c2c00c003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 246521627 1250 246520377 246520399
    0x105090907180e0f1f110301050f0f060f0c01050105120c0105030a0e030a050705060a05060319020a0f0807081c05040501030c111204090b030a0809010c020616030201021e0304020a05 80
    0x42c14050b00b0003006040b028840c3d03c034110644280410980e00e01d540f00140d20906111104941c41550621107201240c01000d000410031420407000d03140c03603540014415001da6032040c002500e41d8000c50900b51040d070010403140e61401c030910030349024100458180b6030b80804a188603942e40000d401c1941009004400314800740c80780d41012001c400e8240590703488408200d001010b80c0c10212098a49100e1840865800c440300d101d4240540c2c0060060306002c0310400313032400c42c104550003c90308000e40c9a40000d0703a506105440f8003070b12021014050031854252021300c2c6c449000360118404514801c0004036a40000480f001c644080c00c0200d401c544610054030040702cad618544840b4041c1c02d00d00030b4640301c1c0c20000c0054614aa404002c0c4202001c10700d6959400046c0050550314100181c0207290301840b030301403100e8070041c502c502d05051180c41180d004420000cc03030145c0c1d0041641101c0400380000d4100d04c208030050103041d032074250001035400c0201d200300c500900183d80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 246522877 1250 246521627 246521669
    0xf0e06060705030f0706090c1712130e0406060815240f04020a020604030f0e01020a080d09020307030302101a100311090a03050a0c05060a0f050d180b04020103050105090907 76
    0x816070320140004c00f049515542c0c14213004015011900003110241c406000219441d0542d10010820103030300002442d100d125206d02c3d1940781e024454903050f190903940b00040f129842c0704101e11481c4908008515240380401180c907110100304d04070a0200030b10304015040f0b00b02041100380030000207101d0081481000450081450303070b00f880e41c206000080c0d21454a0300090010702a82c802d66428010620813a800c490b0f91184031401d80c0160445001c0c2e034003190043c8003401c8600f070700c0780002032140e8055001914028240e44100c0c0541c1081c40841c84100083c401d0b12034041c0900882c0003180a80c200084200d1100c404034000e140e070343c0b0301b0321400d40c05203000c2c0c030b41020380500303602c00d01074507410116507821000c1001c90350303e0002c03140411981014016500211015242c2c5500420076600a80b816000714800d188041e6a510010f2000031a9441b003215241c01860280c0b08c40c2054000103081d254140c0116001d482d150f02409091034002600e8030031035820104d2160109041c0c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 246524127 1250 246522877 246522883
    0x909090304230604151d031b0108181e06060306010308090613030c080106170312071b05060115080a060302010504062d02010209120f0717010906060f06090f0e06060705 74
    0x1800a1320140c0c810b0000200c04c0b5000384e01c0012400401c0c2c0d005c90f411241c04200348e92614003140070712440c42406180501c42d40501201c542015525580d01d0180032a8203206252000442c507070380c9140003120702c0c0247d000c1c05000058202500780c0280440f90f0658440d003605101d060074981c00350324000768500a940308286814051507019030001801075449411030701814060040324a078088060780c800782048000200d628004c03980070400d0950b9038203403068400500403548118682082c8111030009441846020702804441c448940e0344584000000c09c0380f03000810000b102d81c03801c1d07801d101503038001040d00c044032803600c4c0015512203845c401565000c09108510640000748107124451901900131381942001564155503a00e940c0200740d41d0b84548510366104ea070810700091180b406402c4108400038401c20000c200700b00d00d50364500460340c940c3d01807603042c44200390900419501c0035800008001d0703240c1c0d66005508110a081200d140604058030030800003840c401080414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 246525377 1250 246524127 246524129
    0xd18060212030a0f06090204090b09040b0105040905070e07050307080603030a081812070c030506100f06030b0103021b010c080601051c0f0b09010e010f1a0d11040801110909090304230604 82
    0x3604c000c2c01000e9880e240c06020390494003440341c40d907080110840d200c3c00d005c40e02c0c603c5242c100100c80c0c5181d01e4a804e100041c00c468006444a0003025408100c80c1c1c0380380400d0740100c1940d600ca03952841c147e8801007103c100503004502c280c004002c0d07080703061ba0044600e90080030f494078000c00c60400c000d065180c0224043d4800c00c00f00041013a1046c800903840d0242101e0049040e50b21544c1c500701c44004c070581d14003540a5489840105122580c46540800e0020f441814014a82a04444543c03008a103071031042d54039a45816049030300b81d600201d9181c006c2d0081c2842810003500c002c280504903c248141d000b001d56850240d107208109810a0284c2d500103080c91080d540c4034100104e80314001d000e40b440c00c0300c007505c00003071270070401500c014002007000300e445c10004c242c0d1401d07010300310746403400c5081c0d030061001050b030070000e00c42d41c03100410706000309a8407403402c0c0610640010041500020f50030900c004c12022003c035029240d850094124290054400e4000a0f900e01603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 246526627 1250 246525377 246525401
    0x22b060f03030801030b07030b0303071709120609100b0109170a08030f010e0c040501050a0806130509100e011503080310080334021003090501090b04050d18060212030a 74
    0x403000000c103150b009900c0d1416613026110074201940c2c4d0030300c1601075400c50414035030168000c001f001e010a03914401419400c00c0c618030346107003002c0d08000034400c0c11400440e0300caa03040001030240c1e000082108070041500d00302e042c4102030542002905218072881000354030648001c05002170310060200c40c4002ea4040c0210b51607051031480c46410764024050041b803500d100012590b145e8189055030110381c816541e040c60304858590448002e0342c0034008a41200080040580001c054000e07641b180b00710030b00600210b0302440016054491024544855034500907240c01a1888607103202d09594000d0b003001d0760303911401c1d154210807099034400721305408046801e16618070768010354240501440c28484445116803103004900d880c46034025031141c031508003030481d18002e402c60080c00d4010800000e600c0301c9900c9a00740c0180450b02120740b6009a40640400f070b8000342c0701220b0b80507113418a82c0150074a07402a50b00d00700c00b40090394811000c0000381003c07105400c5540364980c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 246527877 1250 246526627 246526649
    0xa150e100c0305010302090c1c1d0106090e011a09150d0b040501090b0105060a09290c032a0c060906190206250503060f040219050d060603022b06 64
    0x20064070000c00400080c00300301d1280900c132000c651090040425181d081c2c0d000000e00c42a4039030003020100804160740c980d01c1d10b0154444d00c0340400c07000c0c0f040030001c106444010402d041580005821540e40000d00c0d03c50850810019180781c41d040700c810307403101d80c8010b010340c0340c05103a00242d124000c5030740041851042d1401c1004102064028039002031185201c4070203a40c860b820045a8001c20701581c000a003000c1c800c003c0c1a0880003442c4091810003140c40c880e60040003011800d600c0101181c4095000048a0440c481071084517401c1c05040100780e001182e4007501c558a4072580300c03019100e068081480542ca60b203c40440c0c052280056205451841c0c9080c042d442c0c80f401c89203100d07800405005900b031f010aa002c4002814100d649041c0f544d075402c01000018414007055940150b400c0c1702699102001c2024000c20810300e13102c413a00d41c0c0b04190300e20f00b90b03040d0380c11502c2010f00600485040c80500e100900b400c03414642122010740b4105c91100c000c00055209009000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 246529127 1250 246527877 246527891
    0x14040f090b040c0609050103050c0706050c0c07090605120c0a0308071a0106020604150b010f081003120801170a020d0f06110f0a02010b1008180f0a061b020a150e10 72
    0x111900e44540304540325625292145c40d0f6803401035080f80d00031180c1e034088241c00c1100e07900044c5181e011542c00a4000102410400100c1d5007a280074402e412441034640d031a03109020501d0712461002d4052107410082694541250204031040b99510005103450b1021402c2e0b81000000c015860044c400c00700131010960b5240c000a5651405880c10307070360421041201090035038140508e0181880684407500083e0440c8812640c5d43c17002000d906035070405844c044005003620500074503544141c1d840071a00c2d410728a9404488803450030103080790748040f01040040c0c54050314140c8043c1c000d4001901e000d150305002014181e001d1100010001c00294440e50b840b0b071401429052060354008c00c00180150309000d10a13150000e00030102d003942c80001d070544c0d01302104048100d0b83c14140c0b212024400c8089260400050007122842d44030700c0c0d82d038600b031076102c42e02c682c841492008064420160702c40103110242105a1107144c3d032203014035110008200001d850251504104101107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 246530377 1250 246529127 246529133
    0x60504021801030b010c0203060c090102010f15031407030c1403150406050a1508030301171005090303062b1217010e0a06050d0b0c03040c050d03030f0f0614040f090b04 74
    0x1d606003400700380807030300d04400742c501c951144130704295075071740500140b42503182d50031074041580184080904564aa01004420900c00d0107201480014911402d00c0e00d81546800d0104080d021858055580044000c00100e403001c0b9a030700031242110b1890f08514000c0011908000c00c1e4100c0b000389180540078001040100c1d40181e2181d41582c50400c070481400b8184541e103501031050704540d51040c80140141c8403041288031401125038101c0300c508110401510941d181114800c80f0742d040032040040c10f0604902d180f407042c4108941e440e43e240d0100c0e200684031f429603005408082c00c0e0740c4100305c1c10302034800050382145d80302c10f001040d070391101d2027074941100f211903480b91424040002243d080104600306000d034445020685691288800562600001d10070b5554070f50300703040095552611b500c04d05620303020340e5000c1800c0300c480203100309440050307030344055061420004001d915007450724110b0400045a01081c1c0c000c50401c800064044c2003000703420340d6100fa003480f0070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 246531627 1250 246530377 246530407
    0x403080402210f061605071502120406050103110405010617090708031201080708210319050702010e010e0d1202030a1506110d020703110906012709050903030603120d06050402 77
    0x4000010f038111066a81c1c0d0700e500d1426038140c0d6025a010480074808240023480f403501882444c0820000141468400149148449c2007520280e038082d0ba43c0c0014400d102c09040d48000b80300e02035905000c1c070b51600d0401400da14403c82e144040520780c0003c555070000a0020034001d20060b42166110b60461000b820121b0b020b11409586205030000003619550114504621490314800c201170050000f0b20300c4056400140740c1c1d03c2807840950650101019486198000c8507150700015120660f00f044a08540712200920301035484206100103c0c1e070300116202d04040d44020140e00d988070307491001c2c060036000309a60006100e5000110f070080d841442e0441c180309280890307a083d6130483d0f080c1c2c0c0310046400b010b414455201140c01c001e041010009412100625003014131140c5010b01c00804400e40500e00c803810196071003008a00e941d0f0180c0354105401c4009036207507080c400c0000366203219804108111910200740007983d181160f0180005010141066650303800000b40161 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 246532877 1250 246531627 246531643
    0x20071e0506011e080106030809060a03020c0109030c0308060d02130f060e090616030204050108010902220e10090e0309040e15070c0308070e10050310091812050f03040308040221 78
    0x10380340000c100040d80c250140106c41c01c80350041001c92412140c00144001540f00d00c0100c02031640070003c6003800c1e2024801c00351114003e9550003803404192400414101010740024425020a0080c00c056070303501c08000034035001c4007000201c4030520351100c00030f00440c0e80011046002d0030f041280803840031a42c01c0c451006100d03114507540b5a04070903000c070b0085000303244c00a0414001403203040e01c664024042801d808401401820503490710b24a003030b4168000c0c0f01070032000000e2081c0c402c0c02c449074034080c02c80340302c3c144402000c41c90740035983d0103a02a1244100e480c4d21304040c050074140101d104907407900304500c44600e03000c1000340000403122012400560100001461a441203059040d105402000600728880c00705003124075030000351010007400c051200000d030207201482980d0340308a14041d803020301c40340cc1c1410070007898a18510b00921100700300507820390070580202da5000343d040c1000c0c00180c84600218113085126011405d13002c51080700f60b44104c4000840b20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 246534127 1250 246532877 246532919
    0xd0b040501051506160f02040603060509010b1003020901052d18010e150715060906181104030c09022d030a061401090b0d0902030102040b030a20071e050601 69
    0x1d070583c0302072018010079100308020040101082c2c030748500020901d08a0f130030090f000500200748244c807612100d00300c40c02074490840c503030b665200900e84c9041c143c0110740c41440c1414114200454040007030402e104140e0b2040580d10b0b05980440c00d5058003402205403641e10340003e40318200d0640300406404081001400300750004000340303841c039100d04181d80058200d0201403c00110365201c03d0521000e000e0841425162203001c10700404610588000b031580310303200c5c03014800c00c40c50b40080355210211488500f00421043c404100c10410a0341214203243c001030b518486541d40030388941c4800350301c10a40c0000f80441079210040000303540201c0c410741c01046865503455a0208044003100d000d03010272a078980811041040502030840c5010081d030106400740c1a41c0000d08907402508903524800c1c0100910030306a24a100782c511002d40e400302141050783c81203d100450046c01d000610f940180d00e08090540e0207200f550300f92a900030201ca0b02c0396101d800e00b00d13407a031b4642118 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 246535377 1250 246534127 246534151
    0x31909150606020d0e060405060706050a27021503090d21060f080c010309031422030507030309150c020618120303010914060609010806150715051807060e0d0b04050105 74
    0x150074645011b4007124101e507001020a440e0000542c1c910001d0007000305a000850742d990032842c14007250400340d62550b070240111030b040c440c0c10700c1007001c02c00112003804c41c507000030710802c2071612000964064070000d40c02c1542ca4055401300301a421b00c0294022071100381842000a4090714030f00f07210080d100301800f59490801f82c040110102c51078150042c00254a00c2d50f07580e101810b0348000c040e84a00d01d500d00414004000081c101043c0c281d00885c1c0940c4088e80800034035920119030400f52410a103601000c001c9420024010000e507213000c0d100744030008544900c9040040001c0301d621000d48a0042c24481002503074032604244142016542010211140c1ca00c011002601c00d000042c035060401c444580111045c01d402070150b81c00140300700580d201c3c1c20041b009848014400c00e541c1208800c000450710556034090a1001c01400c141202c43c10b01d20042002c1080c1e03119844e00d0405008071034001740034141e00060107003445120b0340510045c002c0642000748219284405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 246536627 1250 246535377 246535397
    0x4020406150206010b090406051e180405070603020f1b0d09060c080f070203031b0c0f0108040201051902030d02040b12060a0e011217220b031909150606020d 69
    0x4100150940007101c001600036800500403c0302c010058505403a000d8400100c503610303080440c4d1180780006184110a00f18a80b140b80d07490304611105044001e80010441403c5c5581c601d50780c1e40d024020fa00034103401066890701c1401132015504c40003600703c61110411101e1281a40301c4c12a00307a85000240d003284007140306400b0303800c04000503a00524882c80c000c3c800040003203940000c07404aa0500041004441614222000d411f40e100c80c007010b0000244c1d44820020f0394800440901d0601122500300000340c1c0c0c2050030343c0d180c1b840807403a800c050701841d04124250301c10b400c0d49007056880410b0202c0d48480d80006020034046200d5000b41d5500d8a00030441d41240c01d00c0b540501c402850700510002c56419089c125651041544004071b00214a107212250401050f02e556880922140c40c9000d5648031444014680c604041d803450420000d8450920811108052070503140d41c400340810030f416200b02e54983e0361000820401d82c85801c002d4549a961040302d0008040c012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 246537877 1250 246536627 246536639
    0x70c06030c02030403020d020307050316140a03150b040912090e0a062405040f0e060f042a17010303051903110301030b0c19050d1103010806010b0912010c0201020304020406 76
    0x2090014080c0340b60001c60401c1d1469080100004001c0c00c01c903058045d0b0000012162800c0045100c5c012400f04000d180d14285902d10144010412403d0b200f90b00240c010004650911800b044500d0381c4000420b9230036220001c2800344c401d0410040c4001e401c14098052280d111030001c0584031100800e401d80d0304d508082109582040c010036044202c10380c1604184642c50fa20f0400d40f07042ca080484c00c141ea101d01801c281016075001203100c03005c1c0c2080060238070f480d80030034840750002c5034200038a410100304401d4200a040340b103010b5140300d41d101b03e602030065808210383c4500e120340307064a41e142e00c0c0c020103d4000c001000d0a0600c00d100b2200c0d260b00900450b0180554840f0702401d50380703540c45100a055000d0030494650004010300d0031041c0c07d00000349140525038540742d6541c5100c150800c219508201038820912050005200d4200d021485504582c00c020000361036064900020b00b1229010302c0c90f08203986420306125800c3d4064025511641c000c0b103041000641e140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 246539127 1250 246537877 246537881
    0x403031b180501050c0708061003060c0807080a0c0302092205060303030c0322050d0c0203060c0f09040b011b11031236060a050d180210120b15070c0603 67
    0x503460000c85480d02800d00c41c40d4404c00141030425007400c1141c00381550740c90014106642a100c02000c41c051100500511183d4082c100500c0110b2a0820701440c0549000f0034031003000d480f111050f40c84918a503207051007501a1442010010310382911040645541701041a001030400000c600301000521145804000ea030303c50880c0c000c1d29403641d541c1350f1035040030354840c41010809a4800075440d011030810007101c81340d9005138070384a01c203046600405140c110014501c104209040106603d4440000c00342c4881010a45010800302c4848005a8540b5080d030300014901000c14008001d1180074540e280c0442d00940c155503c800c070b6418420070307600c0b84640c3d12030180c8500c10585001306440303400c07440d090507441c0407000c001c54050002d10340b684621003200016402043d40c6416403510722610800f1042c3c0c00c0214007408095000c10346149074000003c00f4400385204881c4440e806810480d0309650040c501400c80e00d00c0f96028a260300503c0d01994000c1d80d031a4041091741c0030b8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 246540377 1250 246539127 246539147
    0x70602060c0a050306030724091403070e10090509030a0f050906040e2a1e07030f0c110904081b0a0308060d06020705070e070f03090807060e0a02090403031b 69
    0x1005003145403401e0b1100541d00c80e0b002514160701480b030340900003240b408465074401128010300440d01564440c24009080a240da0045504c05064825a0160b6a000075902040318008030b1000e026a54102d80182c10102c1d55000402c1c2d00c0c109020007100e100040014456a01039071540d42e180420f210f022103140c0030b03202d50076411000030042032015210549440398440d084007a010002c84080c01c5480b2440d000d4008981d9642d0701040c40030700710021285c8155a00d80901040d0704000e0741e601c000b003800880207040014840514400300c14400c02a20311010804090150314107070609160000c100d40c824a04000010114801034040040200780b07003440c1a0940d403161165100c04080018510346103c04503040c5a08011900004606002440050107502c815000a141644001d4000c00090210008040c600440f50001421180903513462a401000008540458901503403a0055081c40070f503007d182c241c104000c25516400060036071401d042e45181141c0150019604c060340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 246541627 1250 246540377 246540391
    0xa0917070b04020405040f170c07080a0c090b0a030501110409110712050f0706050a0603020316030302030d0b13090507030c050312070602090a170a060c050313030e0f03070f050307060206 82
    0x5060085800b503d445d400c01030300300d40a0721400d2103002c601d540313400000b424185d0f01d51540e40d0114078510145010310142004049010107825404c00076546c44c0240e4071280200d1850a5450940c03600359290036510002450703001008100352125180d400049802c03520444140300c0c00d0046030715044200000751100d65030b1006207580c2001800d0000d42d0590001a0722003651142407040f0700114203580190b500420182070700041d0141180103150030325100000030603811100403000c100080e4008101c600980510000043d6040014005542d45c5112900701031040d0805800c6000c6c0680800ca041c2140d1080d0054103055a0b82c0040c1901d40c1074071005400440c01c03d120240120322070350010b10314084010800031516071240b9006280c04101508902640d1212020800300180f40c414580303006043e050241c00e40c50040751030b50380c0c0310440400034200107003034048141c2c9807244002d10fa100e0400405980f2140d031140103503010030345a4440c1034400d1044400000c0c2c1c85002142d03181c02208 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 246542877 1250 246541627 246541643
    0x2030910091203053304050912030f04030e060d02090a090c0f032705100b030c0f0f0406090c031505060405060a11030906040e15090f070c1401050a091707 68
    0x2c00c01070240d0091000800a0711011010301e190043c451420301c68409070782150314650107030101d0000b44070464400800c121456070104503082e40189402c07040d20344c02074105207100f44c0307640c031858210b82c21802c5c4611a41c005102145d0744a6040580d00034121543c019241c0141c1d25a465035820305030740c0108400030104101586c244442e610036085824142c0d50414500341d4282e0200c103410b180d181c1d810b4240c903590406004800c400445005040c82107008400034840c0031449000035103d01010554580708145084400c45151101d81107031004101448040011094840d00503000d0001d0030400c0081d000c28883c00300e0f562801030290740a03218081c02003800c2000611003540d20341c4107003080f00300f00e00c01840408483d0ba0740c00010009484100303045145828a400c4103411500141462403042a0010400402c24881c502e0154010302924100300f0194940c1080c012208595000c50000d50a2400304610601107401c207000031841411800400d2110b4205003c80d805924801081e41c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 246544127 1250 246542877 246542903
    0x50c03070b060f0a050a1401030905070602010b010801061e0509040b09090f1504050c0d020d0b09071a0712031d01110406080c040b19170a15050114160303140702010203091009 77
    0x1e040ba10380e03407e081018100050044280d032250361601c680350b070103040141c0d190680c40c2969640424114010070642c00c041c2c840c0301f55013001c0342030b50080a44a004200012640101669958002c2c030640a00580202d00b2803c0a400c2c4503214131890184000922031a5142040c0542c41e2011a116903046400f6200c400c50707a004001d410b464090082c0c0e4854540904440464011120303035002d100094000c0c00e025180c80c5c08296401912100c4001140c0184114808118404a002019030300c91400080018207082540083c3c0c01c0544140c0d180e618001016407403c1c0350780002c000352111030b01c46001c16545c0109006141c0310300c0c000c00c00321003801e00c400000403003140064044005c0f1414401e10030440b15540714000b0004544000d00305440380c00344180c8500b40c200f644007904080c6810142c00d008010070401d50b21a20b0004002d0ba8208103205003458441d510076150111440e006080c41d040c0180004d020b50815142c0714014014060a1b84512406128624a041d0b001489a10030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 246545377 1250 246544127 246544139
    0xf02070e1b0d05070912020d121209060509012a110703120c140313050d02030712120801060f0807050d0f0509150112020108011203050c03070b060f0a050a 68
    0x3626000d4194007030701e12409003600140e110700014007100e20420000042c0f0745440f5400510401480d0720003030840c02c1d511509070150311107000c10050f46030444462030300da07990244101c6889020030144a000f5141c10766040c20031006820850140111500911184140c9400740c0c0c61992400810725121118981c0d4102543c080c240ca460001c80080940e61060b540c1e4603516503c6501051a600094045681c682000202d0201280004a5000450404c4114540320309010401c0c01031a00c146501c140700b0003190b5080201c00090826080c0d240d5401e520b41c81d0103541e51a0000c050400b0908403000032803854441d0080b10b408020b42d94a42400d5150700f07006603050750012003184c10640d200e40b400501c00000c2d001d40c0e070040010500400c0042d003030a206102945041e080f2071040c880c6541d2070300160307901030f08407030640b05044203802440c0800d00c1c05850600c40c40c81c00309414080851a9000e00c003458807418803a001c103030f41607081e5180901c10004402400c0c0a102e40c0320102200a12032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 246546627 1250 246545377 246545399
    0x103050609090d0f0309050d0908100608100b03010608032a0a050304050f0d0c0611011d07060f05271e1e0f03031314010507051b0105040e100f060f0207 67
    0x11910765030178000340072105a15201e007424071800e80100843c0d504101000482c2d42002503d00781514000200201c0d0b0500110300d845140d000c201074242074680040881507030b0f003035001100800710b10040f240d940e1060390700002c0700c4a039001c20590010440044100d40800442e841e2601a131102c041c515060404003009011b0f0300c0d4000d0260031061021100e400180301541c00800340410f5140c0300c40c0c0c5500409a24252084050184250002040c4280000d000042e1030000da62880c2882050105114000c13030306405000fa040355200348401108034517034260086e100c4160401d45898407100030b000e9a40c240c45c001d4129094000101040c64040c4600340c2070402420b403001880b05c51401d003d2800240b640c0c0004045446211106208102c200c40400b60160740c0c070b6003030a14505101040e00e44584448001d02e042c0d4064220b81071240d51030784103100701c80c0900b04c045003000e01410201c2480600440c2406102e014488801c4082352140c01491034440340410f0754020b09205080c1300420f22 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 246547877 1250 246546627 246546647
    0x30406020a0e040203040f02130e0c1c08030c1309020a1b1e050c09060907231207030c03142a07060c0503150f0d060c0c080c0c0103050609090d 63
    0x100410b100d1108529980d50000314081c902405000d400200c0b070340100001984202005080d0380c3c980f07584048040c2c404104507484044c12550b041300c101403071511541c000340c0343d40700820b01640041007003001e04440f00940558481043c61481954440c2500c070200d1058440301e401040300d2210030000800400c5500103200d21960072100d19028200c0960030039001c600c0204c5080e08030300c41c880b46909001070030b160310602c101c2c1c00070010f05100601604081941803800c0c4030b469a1080a0038800c1403000700e403d400d443c20f403a60302500c1c00340300c000c005010614032580040e00300400d620503200000446401030340d819000103c1c2c00704080b05103021112406003204241014403841c00403480c64814201c654a075034a609030380345001d203e200555550001c0103486000c00100218040d181d0350706001c00103a22030300c0090031a0001308150381c125141c0c9402090b010001909070600600480d40b45243d80c0300703803814880ca4550704200114502c01b282d03010002d0340034035039000301c251048207080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 246549127 1250 246547877 246547897
    0x41a0601030b090c04030218060d170c12030702060906010f090b0f1e030d0309050d0e010e030f010f0c0203030c070308040f080d0501030b06030d023c0c0306011a03040602 75
    0x5064010b610100314110021903907a40400d00100e8200258203040b8100c02051419282a1086203050800038221980f0320707202410403690700175503180e108000c05c104c80d075010000e41240e51296002c01c0404490b401100d0b040018013489011407a0342c1d1002882c14141c503068a80c11f2000c6003003680b440010000500200da000d44600000e52564071000c466068074a040c011146240184030700b85460031001c92032400c2094a0b2048a00c0451800700d2010303840c450310300c1c180c01c142c614580125264189020040d515002e0402502d00e10341c015440300240742203040d800e0100d125065001c2e0780300e000480e07034003013106400c001190001e0311486406620501c01c10b0340f401c1c2a00e4a86401040d500920b01a1184550b074600600511452100450744002c0840007811119482c400c025241c541c0526001000645200c00e41d089104035242c0041424007840001035560800005039074800fa43c01e0014007034007903000007050a400da003030300191010404950510b10340742d550790340000b5401201e02da = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 246550377 1250 246549127 246549131
    0xa0c0c021e01140c0703060b191202060705100504110f060702190b0d0b010306140d0605042619081b0f0712022103190509030d0606110f0303041a060103 67
    0x4030103a040c080c001d00600341316440204007450440ca000ca041b80e240000880c80b03a07010030001c100c1760751003103030280942d0003003d00200680050300c003245070b6001d03520313005240d4026620020001207060b80130510507402880b44464160700312040c04a030401c8a00b405030010000c200e000d000d07082000028032011500c1050b10180c59903076854480582200795505459600d514040039950703458002c40000c0c2c6101511202d805200e0fa00241865105601c000e06d4103072224000360611480492a12030003803a003c2d002c040a04a801c14101640400b50503a10b021485800c1c0c420701d03105191141c03051091401040d4403941c010154001a0003003048540300791820080b401c0040d0401122503400c042c3d03a0014803412804143c4040e81d81c00039402e51050714020b1007080520320300c0d400c0404401030b240e403000815465400149042d441103040d8000c034141400c0d000140c082d886600c00d100301c600507003500d9268504456a6440344010395002d007110700700390b0380f81c0c0810550070242d941000d014180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 246551627 1250 246550377 246550397
    0x30516050105041b0608060a03030309050c1507150603111216030602031602060903191205090309090f060f091e1005030f28031202120a0c0c021e01 65
    0x80d2400e40d882200c2c110303000c04140c40d90803d08102c03014050043c5c8658100180c040c41c0400206510074068032000d400c054070741d014070081c49001d00510315444409000c0810003084e61010640507801940f00700c6814034083c40e2811050380074403c00041d81c3d4401c0300d142d000d84420007000f0383d004100441f60b000f80034180b5144a040040d01d0039400441c465080580c50345072a00b0019051039818005d801590007410070400310142c08001c03100b0203150440b20038815261920110b460420410600c8074461a00702405400729001018060748101122006201d5803041c050106542050703c0039a00aa0011802140f911700441c1203603200c0a6840f00b04a5038824207106040c0c4402076604240700c01c0300400c01e1005060a111440440c0c401400429681c802083e01980030304035048901d61f011807400328107040510840e810424000f00760b00c15902d88413580800145000c1c155400d400007440c0050114005001c2c2075411045600100b40341003507000f40041814901401e5600381c104007032042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 246552877 1250 246551627 246551633
    0x60e030712110918070303030c030b0411310302040b0d08030a05060901080304030f080c0109021e01020c01110c010e030c120a1505042003030405060c031c06080a030516 74
    0x30070a440c1e00d0142211810445040b001c1c0600305001402c10110f222100410b40300d4501c0000d0003d003100d503d8500028501c0c5c40000c120028800514010f500509005139076215404220142c20150b0301d90564a240904064111800381d040c100302c41020754507484100003500d000d074046040745030050900507924030680d8444500d40d00494220a0341035940050024070704100700701502404c0e004000318034180c00d580311040701411148001b05418400120b003030407101c0c20340101000075800f600d10000c02c101034010000300c8841694040c010310482c8120a2250f12400c3c945280006c40c10241106000b150011143e103802c06042e160075114041e182085611480120020880800041d08002d03209141401c00315000704200c02c1042d0522091201050b64001c010040d08285282d24820750800c5c1c001c82d003180544c7c0d00041c0c0c441d40203d64400d4091000c401002014840d400140c0c058510b1001481215010300540c40268405200c4200003400741c0002c2c041020142803c80e0244c440fa5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 246554127 1250 246552877 246552899
    0x10626030f120405010b1c0602130f030f030f050f04090b040914010905070b0c03040509071101110309060a1401051005040915150806090c0702040e2b030e0601060e0307 74
    0x191290503031690703242c104018807200b031041e407000410880f5240d9141b015180f010a031400146c03c090042d50b0f00140c42d1055090000040000700101000c8046142d620b041024000384440400e0703020505d48104000100c0c400c108580d0101807008001d81001c1c10b01c0345200c000c18989142c60f070000d546e05112000306400640c49010050040008a14400b440c6042c500f00541540b080990b42070500c40130f0340e0100f01009860a0b0b07101613481c221560385403c001c489010350b144001c4035551030720b0780c01d40794074a04100451240c0740903400c841031610360a0520003281d071480840e440c1502180b0041c00306103410100d4106a0035945409400c00b511090701504403504080781c5600603c1148c0c0030003d005c064600b0004030b400710b040807080e519101c0003140080c0070003040114440d00c0000d030032045580c2c9500c1224840c0d180021112188050403880e9864100b10200c0061113101c04403200e20039100f4000c0c0e5819142c00e002902d8180d183c4242134803500c0d00c0c0401d00c1e0340741c090160041031200080c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 246555377 1250 246554127 246554137
    0xa051e010f06030c02070e06100207030f030801030c1403150a0f0e0307060b180c0a0302070f03080609100303090b030405070b0a08040c0504020f0702130b031b1002010626030f 77
    0x55469a2000d03160501c040e0071030305100001d401795004400c0c204454140c1c621040d03400407040d2440c24510f68142c1c0120300704100ca400003400e04c0c940c01c0b402e50a0607840407900781070b0380c45104802861509c85440551400300000c00c564950710155100001400104880d60401c0240c6000320b02d010503034001c602504c50301c1444040c290700210b0b00d2010300005000f200c1900c50203403850380401d096411000500c00c0002c0c410400c8003070005101980a2296044800d9542c2000d1041d6030401986401030030b0010a03a84944a05a1000801c1000601305100000c9070303850307110100da45113003007540401608001e0041c2d40c240a4880300140e00d40c0325400034400c0c004260784508191515107441c1c1400c0582d5081980158814410400e1a00b0a80102d1f040d450301150f54a508028601106001e411010112a01802003100303500d0040452010021001021543c0e10460888003100303d08032034641c840c8191910304240d034806040c00e5014900b101071101415685040c0e0a0a90040b00f6841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 246556627 1250 246555377 246555389
    0xc02040e0a14070e0603070b090a05060418050f09070603240f0806070f0e090402120d020f1504030c0201051e0f091003060b0a1d0a08010c08070f080a051e01 69
    0x154040400e4000414024003014113070707402c0c80c0491801c0c40004a40e440754240181801030b0400680d4041c00e554421001000f044014601940e0b00c0c0c403401316044219508c04002318460410000c5146a03903100d0209100c2d20040004001e06450408100d0190400300f507040c0c0210f4600702490a21030100c6200c40c0501001000071010a03d481141450300c40000d20201c100b01040c00e08003502c82e0301c00408580c1900449024416807518000203007003070080c4503020300a104078802c1d00e4030160040341c8980b20013103000030740c0e203120178040ea0811041c20407a001000248260300300c000542c0074401030320044060036883c4000a019090402e11640031a1513444c182d440400c4c21070030381c0341002d070401c1604118942030001500d40851111540192083c0800344000714505220016002c9030342ca10341c4100801c001030083ea10307440680281044030045000030902d40024004c2c9004d404400c040514964480415959541c290070060070b0141c64180080e288030b040c1900300707034100081406045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 246557877 1250 246556627 246556643
    0x30603020409051c080105030d03020307030e012d05010b03070c0813030b1605120613110f1206060c0a0b1306090308060406081f0b0a050307090204030c0b040b0a0c02040e0a 76
    0x40e03107241e8110343c5404d442c3d00040054410040c0110780307021421550f045040d04025850b07484044003600603200f04c00e020301c0d841d07180c0700d10f0440d6807d00410300344c19210f401250899210031003418405136042402880213403103080020641d4035202d5540313009a14000d01049007040500c02a56094414039403056510348542c00034013110f034003464903060714007005050407841e000c2c102440c0550507100400c603501c100405003401003007520607000122000341c2440b46a0f0380303603c803404c0340000e50001c240780c80c1203803424000030740241403840c110390b4450410402814910800c1c0c1d01c14010750001446c00c1ca0441c1902c1d03806000400d2401003600b80d03482a11102940d2900400b800f007103d04507480461643c3c02505500300c040010500411071124192011814502c1c1c0d40110300c0741e80321a4013442e050301c5444000a600e400c268094000d60f441100c0060303040c0da4030904007117140600e00070304d24007940c02c000080110b401041c42101041c070142c404107020311204040fa0030300300345003030030f44c0c10007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 246559127 1250 246557877 246557893
    0x30207050d030c410618070504060b0408010509070302130b04090b010602013e160b01291305061806030106021e01050408040b0c0c060a03091109070e0d0303060302040905 75
    0x5041440d110071410144d40d62100c04904001600e550350406010314041141150341d1107000c00040c80303000090507010f1f009001d02a641d42c020a680d030701c18454406e0652800300496600e580100d070300c02c00c03646c004183c0e0415001420814006200132036466512943e01c2402c0070004800c4403c080c020902c80c1c0001450050520b00c07210701a22503c0d0402172540c0090b2002c0b1a99049640d050341d4030030010486840d00304c4003005c240e0180d2403aa000e480401032100004d5100404032002c0b80b0440043c160301c0f200340307189586414600a2080c903001030501e0410900240c1404409441c0300d08051103070280c0c200e03915004c1042507000782c001c01d0040c1c10554010030f181c400000d040d082e003d030303900003000300f89015100c001c510300450103594000e00c00090a4100468108482100b1400c002d150070b54440500c0030150044c18240002c8408041080c003554080ca4203000c40da01c140c0040d15041c02c2840c5007003c110020008003411414180e070349601201588480c4195090644a680145044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 246560377 1250 246559127 246559193
    0x15030b030607090b0301120f02060310060f030e07150201020d0f0c030b060301180509030c0615121501030201110a0b010b0c01060506070812130f031d010507030207050d030c 76
    0x2071001480d40c2d06210100804000c244280fa00b224111071005110001d500c240b231801c14005119260041d60028001c4140180b00c00412b1000c0f0403150175840b8042010b0083c0803d4040d20781c1150000300313580041004104180c540c5000f01e00d00040c0d80300061074414600000001c507091122000012036960081500007901880340c4911044229180340c255803600200105030014540c50081c01030b118030100342d04590800c00c0e60941c07083c4005450251600c400c121240c03180102c4054401c00549000394101040840c84100030144010150810380c2541c006560b802410003800080748a56a92900465051000c443c060001c0c2240381d035640d000c4020090030b50710f15421142c4240703420070180700003c00720390407a0404a0b0514942403140c2c0c581440240c0d405190070050704500203842c01800f05a402550b07100d642c0103022200610403004001141d50303014803440240503034082d1071305001616107225007a5007144249800910801c3e15510105000b202c00b40001c5003200d4032000c4040d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 246561627 1250 246560377 246560383
    0x7260d0f030f0b030a0807020402120106020a020117090616020f010e06190605220902040911090108010b0616050f0102130e0a0203060a030f14030f0423030601030803070915030b03 79
    0x102d18401c040c1440214150710000b500c8055020000300010000111541103440390340583e200a8548000c20b019981d4400c8080c2d2140f07003202307041380007841c8a01c0365503010303508018440c01940c45100404590741d40010350380398460010115170a601c5001031684140c0c0c0240a01c141c404100c1000c0d000d14148802490300e18000245564a81170426205001030b4441a40d801199160341060070074880f510a441c0c001411615006500f03c0e0034131000506010710740441482c681002e81d4210b105030fa071402c9140c01c035080c156203950b00c80c5007081028100340f034a65820b01c04c98010401e076510a85040419401ca0780f002d400035000b40280c040070052031101d42c400541c040b0351f0080075842c40c40d210700000e4001c0414000100120f02c5016280c0a10103607440101421064004499170303405400045075843e0014410013585910001101c0f42a0031600b40102c04000c0240c01081540d007180d6410015400040c074010810000c020001483c1015010701c40d00803540361030003e02554070a05040c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 246562877 1250 246561627 246561641
    0x903020f0d030806190e0a02071b060e0d1a01030b040203060a020f0921011401050f0307030f03030507020f06040804031707030c0605190504061b080907260d0f03 71
    0x4032501d00c510707964000c40d0f04501d05035840102143e450004038281c00c00d4410a8041c3e4100f4100c0e1000f21003000f0b0014183d9004204003801840c1d030320160f0300142210020030313810f8003842c0300042c1c80403c10111424040000510f140c40fa04410340c40c08018420401881000d90080d40c050000e00180f01c00d500b0180200c80c4c2011a41109600d4007038210703880c041c14800d01040e107026000400d044411702d15846020b014000c0014024070001c001e031602c565a2140030301406205600d40e2060b541d151400050b103034200d82c1c0c480244e68014203903450940003080020704503819401b490640d0f0458030814817200780f2552080c0d10710703500d4034190305210303130788458201100000c0c450400c214070120381c20451587c0700990041d00802d5a50b41c640d60072101c3c241c08803482c1c0200e820202404100061754214056101ca11460280910000c50088030f0806d0140c440701400d0300420400e108682121a26250208900401e02c68500403015002c2c900010300b40303a40002050702003200041c95140c06030035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 246564127 1250 246562877 246562879
    0xf02040302031c081806011203090924080102130909060b030304030f110409030c0b1012030c050c01050406092313020a0f02032115030f03030108060c040e07080702010f0c0903020f 79
    0x1e250905501740c43c0d0342d0070701030241c01d55002c943c0943d0010140f00e2101c420107010b5062050110003422680124a030a005540d00d2a5203150040818507120510a60b4a56010b2600f141021464800503200400381d90500f640c0f019101c0140c82c204c1d842c00c00c000c200851140c100d100710384c44a4202400d002c01c000d524284a981403448088c0802c6d400310800743d003141c02c04401900e40d280c0d070706555040c0b000f9502980f40c6400c1c884480044c190002490500a03010f10281e0b030040901100442d000c0c4141e00800022518100050041b203a07410010744068400c520480d0092280c800005d2801101a41e03203565190001241c4002c0c9901c9145500c0008144c0019410468810381c052071241d03010001014042982000500d800100e061552009070090141c44d0685004690280c0300c1c2d0090107484a5403140781c0100d0010090b0600311001c40b040151044a15203030b4410444000001a08520842d92504064603001801d4480e0341c070f40c0022511a94511032961050041e2403103410012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 246565377 1250 246564127 246564151
    0x80d05100e0114220905010c0e01080a05071e030207020402070f02040f06061e090b030108070609080d2016080d0906020102030f012d0602060109051302010207090f02040302031c08 79
    0x124207503241c4e03a1514a52003100a180300d00310328414407241c001c00e80000060500e608098200104942006a403400c03100300303030783d910110740e1030507501d400341d41c015507107000080c004a045145094006501c10000b0102c0e1601501e0007500c1c1c1c00007170507a0442c200c162008810318210208519041c1b28070401c8511032070051285605c5c1c540003501d1840e00008081c142c80049050412662140840b48040c0014040c0240c503541c403000001d91b6007680703000e40b4002c074650000119030708000242d0b00101d000d10b90303140d0740224000d45244004200812010134544140000d0407020074407402410058000c081c010500c055220b2001840c000c1a80d11000541e44100180300c55041d10303a40003410b4071034110003c24004500b030400303104a46045800342e8214184440400c8995003c074005048070208030040c0101d0710b803444180d01c030f420140c90082c0507901c1800104202d115a03001012251079400d401400d00e9565004641000d0541d400813111044400307004015076081000c160b0031003010110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 246566627 1250 246565377 246565409
    0x71a0702100605041503030e040605060403050f01050f0408043609050d0c110618060705030309010b01090b0a0e0301021c050402210d2a050c030c0402180d080d05100e01 74
    0x50f01285d203c2c1d000150401120300b0907986943c40d15003044008040180a030380c1d40e2a503a00701262155410541c044a6500f0400801c2c2500c001c0f0011a0089400c1220035180500e003040105450424010303414040e05241d05c04800c0d0599403000703000a007003905012940605a00d40541422340d201403080500c0358520001001c900c000c0710b0561110b5099030b503242c0d034190104900001d4440e800c9081d03030040002441038200f000100185004005010003030018101c0710006440340869400b0b04605440c06201d0285100d105d025460581c1d880680010700d0040d03110a20605c0c0004031050b414016240c2c2c041c001103040c0203001841100000c50340032130011200d20744a403184000c00500d0100039420b07071040755070080085225640c401d0400380359400f1844c2c2c900180c451010b20f503528464018885064058146030080b9550005141c41030406400c000782044150303542d02c42c068802207000c0c0099100003407180700e282e02401c0e1200c4802d110030f01c2d1020310703c42d500050b0032000c445040350344 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 246567877 1250 246566627 246566651
    0x903040f03020114091005120906010e040b04170a0c0b01080d090e04110a1d130209060118180506150412080706020c100e0c0a12020105071a070210060504 68
    0x3000d5090341d50928110700c00018040381ca80340c5000702d0040380c1d0f10074624032964544642000050040305071101040c8516540c40001c1a00c0f07420074441e512122115100080000d01c00004c1240e01900ca02484102111498916251901314039414008103604625500600a0702c5c0c403200e006240c61001060128011440140381000324495006110405030201d02002003800b1880036110001d4441e800d0b09655526031055020310a0800315050318035000f02c0d2807a03111844038845941c0140c42c1030300301c1d1206401114410003001048644080911001c9070041e034240b002c1c0c140d602d1a24010425007410003c000c0d14501d9146440340c100e10400c030402518562400065103143c01080107601c4824604202d00a8071804448403081d00803c040c2811900e102e902144400805008980030300030f6880c01c0c00350102d001c0c0104903040d51001034880041d84a0310003842120b1240c2c4e0090950400354000c070341c410380c0a450340005a003021405c290045580e10803500100700848023408401c400031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 246569127 1250 246567877 246567899
    0x203070302040c090b0307030c09080606090412120e01051b0703020723040c0f030f0b1507030509060705060105010f0c080306090612070b0304020f060403030f0c050c04050f0906090304 81
    0x403200a014646a00701003200a024484000080ca10642d60a03501e160015000f8000c020b02c0354828040b078808040032600c41400240d0034400d450107000c12240e511562500041034911401e44410003504645d0f98800035414043c03803180e501c6260002c0781c42d007004007401880750015440c44480020500840b4042680002c04104031208011000c540394103122410b8800c0112266207600142400722925100703920401c000102e00700e540d8208001c280700d07044101aa611800c046502800030013005201c124035400a066440c424142649888020000700e440307500a19000d42e81a00f00000402c41960450741012003004586803144070300b4419a5260a03a000182850f4003500c0701c10001901d41d2120003921550340f8073f080884240d150b454041003010351044508034041c240c1e5400c0311a0605080041c0c070300343e0b40d06032218a40c0905a9404a990880c500c0054449110b4820719814035141c0784102405050104549012440c20300e41e010311780360000d803440000340d20421007003010140074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 246570377 1250 246569127 246569129
    0x60e10050a021203071706091009020c160e0108070503150103030f0e1e040f06050303031906050405070c120e090c0904060b130510020a020603040b06041803020115090504020307 78
    0x203081458071010700306001c902d40200002000406040041440304054011114001404072000d012500766152424001c508100756126040d0503058039060021036810340151884000010885801541d03001d0b02800c018502c2e886003000c03c1840d401803000200a010600142809400604524001e10b224010b201414800a01001105465039162501c1990464020b1100033300c929030007070303603105130314100e24400301904d20503444d0a4000c41030a0f9180100d00880e40020702450444e41c4a9281c01ca00d0101e03a071036400056030b40d0306c012480756210f01c80c0ca40150b4090745c40d03082c81a043d107052400c403c2084c03010380601c000221200308507520418042d500465442585846c1e9030f00070081800742510f80c1180f052100007180c14804444400300380b030112a0101c41e010540907040b002682c4608040c003000c0d4114030f0803c005001b0841c144025030b0000c0028000091082d0003841d0010400146042240182d4503403444851180304801441d000c1e1500300c00411080c24150700090392002c103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 246571627 1250 246570377 246570409
    0x503010506090d062a09030f0b07050d02130306060504020909010303140f180108061207120f021306061d011211040312080f01090203010b0a210204030b040606060e 72
    0x590140d90b030301ea6401103510503030b0118040c0008800c0700315030010000385071102d501c25145c03d8602030035580304020550440350001320a0310b20034030b591039135039042308000c0032042400340411107c03518040d68402045095011849468440c0c103510b032000564a40e60302c0341d0b100b0340c0180300b4151160344100c08181103030b9050602d11031080d4a030f00d13900010b0145100350211b40c0320200d41280bc02040c10b8001807601001d1303880d107400c1c1d0784140070010304c1404c2c0341000e121940682d00602510880001c903611940c012544005c5110403a80010584003046c00c9900c1050b0b100d04040101c103800c2807604402d241c101103603121801c001000246030482a88200d8116500c8a90b00070b07a0201030030440e0701a40d0000303984004096000d8018084920a6a6504800d01c00c0f6000261581d076900c00e40f4142d841c0d10712051b18125052408803507548041340c8109405003104150700c0d00c021940300803c000c0d41700312542e0419207800d0802c80226030304c0d54040410301c41d103109040c881e55035083e04450f8084d6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 246572877 1250 246571627 246571639
    0x30506010207050d050c0a170a12090510030b100203180603130804290909042613030c05030c0105030118090b01030b0f0703060b0f0a050c01020f0a090801090305030105 74
    0xa10000102d141c0050360f8441d80c0c00c01e00c2d21100e001405408205581c100302c050341c2800880c0e039a80114180d0714100b42085409030802d81030b680c005495a40c800c203450540746800d1001c036072100d00045c0400c1c54030300614082503841841110f1424861204049207445001031810700a01c0c015025074480d00118041c4a400004000384141051000c51065160400741242e21182c840c03140b41506503106021001d440341c05540341404105900882e00c1140005d0a40040b036161035a503c031140489009007007410104070700c08045001004003074800f1115810181c1d50700c9165040102600860b42c00903030080c0c21817406207060340d0308542100c2c11139290452a02d080b40203107510000070040c0310002440034007408000414010b10000e090f00070390203201c2600c580c1e112030b4025021102030340300c0d101040805002d4518000d40b81c2002e4021192035043c01464102141c00603030881e408000d64103c90300d4007003900d04001368400c3c071041c041c3c0b4406000304040d15060324040c005000520450784520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 246574127 1250 246572877 246572881
    0x30516140d02061801140c0105010806180a02040207020102150907050f0301050c0406230c0c1314070e030712080d0510060e0607060906140109050a0228031401030b1006080108030a0305 81
    0x40d10500c84041c1c2403500e288143c1d10341f034400000b07034082c142c28450b078002c91243c00d000c2086204496181071600300e00c1c00c000c200005041d820700010f90407001d030681c1507000d021002d0030340b10a640310192156081002904c002402d050800100711141041c09019a140104101081c13079204215415100b050400c0340c03441200c04025600c8240311000000006d07804610f4000172040010b500032039076800c0707480e00204840507904204071503c200454003031104500c04514280d00410b001005660003500391b680303094443c00618281005040c2c00ca42c0c1c202c1c0015070ba45101040e21495030016401101c004030540340c240c0041c00a5809280c0c644524000038060741081720030fa102d40c0d000c50f4401001d12449490b0201403400007000d106030381b0340d507040030000780c10880e0380d200f00c1305c4d1a255034440b0f041e800f4005140e007402c030b40c001000e1000d1583c3c1c1d507800c003c54080783d00c11034021441032000316141d2810302002d60b4410380c80d500c01000d002c10400140030980c030201c15544d1480345441c1c000303199 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 246575377 1250 246574127 246574129
    0x90d020604020f03210d0506010c0b04121e1106060414010e070504090e030712020106051c05070b1b01060501030507080403050304060605210705060f04031209030516140d020618 78
    0xf000101001c1c5d040704010b00c0011041030311101920440020b00e4081240c0c0e03940c4001510403048051000b440d41c00007034000340008440240301d0481400a00c2d02c44806050746091269003040000781e00003150700c2c400c0e444244017041080c1c1d588100b0545003400400310101c040c90781414103009010140c405480010403803131081c800d4800903c01c0c0c56007403180c1d20b242c00300349450380e21410b025101a0001e08003001c0f424014001e040490f5000382140038035000200f034500300c1140c0c18004171020b002f41c00c0001081c0c10040c0107440c69140800940c60003409800000d07007100c105601c035074141800c00c409c01c4006e07034103c0c0d400d5a000d900360921907900e54443c90304000030716140d00400e038405241514130300940340c104205011900f8003001c40d407402e40c681c0100089030160001921403280c00300004d10014618114415000303003142401c10a542d140e58031242868054002c10301d408105610401c034072699000b17008110101030790341c1e060b03000094020903528070800303800c80250340600d99507005d9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 246576627 1250 246575377 246575383
    0x90105130f06060c020f04090804091107050106030602090a09140c0c03090a0b0a0f030e19021f0503040c0b0a081f0e0a02030108070812040612020405040513030206090d020604020f03 80
    0x3010708059007046007640343d1801420783c8001c080140c0c0921642003141e03405007440e11072403440035040b5047d203080501e0b00d4000d4002d0721410421010380c0703505020707040000d1400d01130725001d075201e42805604d8607118028800317014000d1384a2040c2c6e600f0103c030140820040001d50782c01c101140541942c034601c00c42d01d0740c550300c00c490344660001309006000681800d074170090101d0741d102d661450300301d81411400b282a50b610101814085d0041d00200e60080131442c5c14038070680c0b0241050815920450f0f0b00100c0307500040e5a5030102d680001007004110a0040010140841c502d41038200701036404000c0441c0d10091030b61881d91480040d046074050b00713003102002803254036101100c3d4a04000360101a41080c41408640d20034a000400c660002040829666401400060030107250080480321500c1405040403032950030440400d0300d840714003815100f0504016140741c02246440e0084c0340103402400d112598001e01c400c1d040c1c955005c0f440c217400c20303011117070820042d1940c400030b42 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 246577877 1250 246576627 246576641
    0xf01030905060703050103110a051503092e0c0801030308060f04020c0f030c0609070515030703021c0e1005151207050409140c01020705060708130312090905060f09010513 75
    0x204510030340c0104648180c4c075030090b07810f1760300c200082c00800f0681010700c420100e01d8020650b00c0792020f018602d0900c0c0c0c55004d0340d4007c4c1c01208603040400b104203c2094002e400c0b90790342c20350001c84c03944a01001a801009a0500d0604e04a80b6031f6145880080014501902c0079200300001d4030051643d903200d406036058104a142580c2901d1283c140d015500da01404203004030f40520b0b0002001d81d1f401181d030004656001c3d2241d41c03100c400e103032140041d5000402d000b040c10303030901c080030b01c2000000300c3d008040d606c0b1303d0010340800c1d0054030900e070103420ac049031b20060428081140c03a24401c04d5142d80c910003914014000710480c2c20050809101e0740260750468602030b80d8400340a50030307008031241e40c00103043c2d4400711800d000480e2120f07800e0058640045040010384000350100e030051028a0b400d5100e000000d0322540d4040c00c0d203000c4443d50340000d900c11000d00c61120184070b05038010a08403104c44040b1043c40100700f110700140315480c0704141d29610a00d16481c2c1e81c11000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 246579127 1250 246577877 246577883
    0x3020a0803090304050f04180f030309062c06161b0209131202030c0c0f31060e1003030302160f06140603010c021e0705090405060a05070513050f010309 67
    0x94692400c8142d4a42e030750440e12540d0b104504009510f882d038103080c864035500e00200040071481340039a0b1242400300b207054804604040d80c90010700081001c81c490070b518501c1704450340c92452008812042142d0b601c034800d619030b400c82800e000f606000d13054080d032144c4040c01d0140f000d00d43c04200c0024554503100280d0484003240070040e0348507002d0a060140740c855141d1031300c59403c6000484e40c0b8020452103215551088503101914074007a0400420000018405445101640d0300b40c4501d4143c603840340301e440c15105815a00000303038024540908050401d40c16103140c0140000d0309183c0c1d611000c4c0c00e042e03000a540300d0060280700890640b03038003d4441d04c941515413074039074001c1c902c1851826107098010042451440d060207002e0f03100c07544e41d009202c0c1400c008002440b00c1402c1002060501c0f6040d0005095117404042c1840750780110054a890700d4184503160603079000900302400c21104000b0890003070300080c004001d0311070541344500024030500041e801040311041c09 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 246580377 1250 246579127 246579143
    0x100201051501122a0f0f08010b0d020706020711100c0309050d0503090a080312070f1706030309030a0302031e090d0b190603050c03010b0604050a05150f03311e03020a 73
    0x8000d01c4035008840c020101c00b656105444140320100403121810075103c886c00190644004200000c101c1018020000710b061006107014510f13510341003240d0001004131210340700300b0b45031122483d04d030321440c600815906203a52140c5156800a003c4245030103128410590300c1c88441c2801420400e945250101400c203d05541e15441c2440d9690084800040860b05142c00a1805441444036134100203a0b5211004140f0600704103030f1101c400140401e4044c80144020f11199400308402900c90303000390040c6540341c406d10800a01c01c0f18407450481c03141c20400005483d6103505058451494010381e085041d1740750504030102d0842c1159010741074a080c080c0100601501103020303058000c0840c000c20498142e401844943d003d948111940064600410001c5042840b01c494600c1125504030f0318116515000d02c21759001690544c1078004c4081d520095100100501c0d841e0810702901c0b400c442e40c065035510520515a004511100c002c0b02207030f002c0600070070410001641c46028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 246581627 1250 246580377 246580421
    0x3060f060510020715030b011b0f080a050c0106050d21020f03040605181023070c090605090c0f03182103060f04060b071205161110020105150112 64
    0x2e641c0c1d8107071300a4a216907000500315810501030710507c0700200d010b85424a560001c0d001030046a01522010313602c5a2001c80002e00041024005100c0b841e80780d11425109c00c0c42034042801c6442a401140c0101d540c0e208145c04142801000c0f0203050144031b02c034415081e40f040807810140c9003441e8030510b100210340403c40a070002c02403e038081405080c58010030202c000c00a4194120300c0203400301d06440358501c031408181c0301c82c00e1a200c0d203101281c0381900315034038050aa8516071004030800d6039120700340202e180407441d030750300140868440742c180051840d00084510020300407004840120360752403010315052002240d001c41c2242818236001c0c99045188980d8401c64109204244550380031031b692030203111b6a026aa909541ca50030600103941c0c0781107510303140044100384002031100c007401c61a4003580d088690b118540d40a030b20418401400b0003403843d0380c1038800756410030040000e01c1075185142581400c00746041d0440303c00c4210080028122b0360b281034800c60071021 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 246582733 1106 246581627 246581659
    0xa1d0108071d060f18010c08090d060b090a05010918030203190e1309030f0504031203050612151b030f01060c0c05100f090801020301060903060f0605 66
    0x1044081c40802c04001801500000030403502c80c44002442062030a400104445104081c01e01c00c80343c401903510b4544c00e001d027a8003580030310f101c074045206010158000001c03414010748040850304103619032002800003401400c103c5810410005030707142440010b400d1590f01035028600700043e840e00340d00700142c5c5400107801c0110000b1411002e907030380030030848640385a07100000c0400103440c001c0c0200305003060321024010184002c10120b0410300c00c0405d000350520b8001003994030600020400410030720b02034028031520803070802e940250000c0c01e0103050b1103032049074555440c103402e06580c8011501c440314103002400400c81e0310700030b481c10508075104450501c7c0d908d81b9407001c41e044100c1b0f400010000381360400c841c2ca107030790040700c1c0074054481e10000b5491581401e030094003550540c070005042691381e920195400c0c01540c030420140100824843e07008078444 = true := by decide +kernel

theorem cover : BRFrame.Cov 246402877 246582733 := by
  have h0 := BRFrame.cov_init 246402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 246402877 ≤ n) (h2 : n < 246582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
