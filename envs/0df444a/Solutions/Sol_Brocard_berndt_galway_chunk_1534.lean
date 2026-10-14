-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1534
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:26:55.194752+00:00
-- url     : https://prove2.me/submissions/04d20a04-ee6e-4b54-ac98-b66de8de11f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 275719424 ≤ n < 275899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 275720674 1250 275719424 275719441
    0xf060206013501020301061803020306340e030d080420060d110c010606080601270b1b0708010513060914030307110708061006050c010f0f0609140609 66
    0x58216a10451140030704441c003840041e404154542c040200994004c4018841c0661018400461059214103510000c0c60742c1c01180d141e040285c0385040c44090843d031816540e9040003010354080782c00b640340c0060107414500070076010303179060810f00c039005891120020521450f081401030350000009902824007041540c091108860440d410010600550001d91828800c040c90b0112901e02195101040c0c2c3e0028211130300f98101c1d1086c4a25030b014082c0c1a60b01c04000880e01d401d00003207208040480c162041882c10540c055001d0a07000940400c0c0c0400900380e203401040b003e4220340d0520384501c055800d03118219000700301003040b9440381c4082001c7d40c0080c10064025444685000082420b907421548201d4000f004500d4070007004480d1030301001403200524000004d811581400a080440d031084c0d407140804200010941c4911f01c0002c1d4002d2405403990302e404c02c03101c1c80c0c9102c1d40001e0002403051850b1145840700082060198072281841035100a0403ca0b00e940c46000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 275721924 1250 275720674 275720699
    0xb01060f02070302060d05010509060a0b0306040b0102010f06030503040510030606020d0e180103060227030a080a1407061b0203070507210204060e0f011205151503030706150f06020601 81
    0x34120861098060000168940000a00e04180b1030800030030300c3e60501c0b00740f0842e11405416a405071100c036100b0040b070380d0b060040ea0740002d4112000700d540070039031004034003618000a441c40c0d281c0c606440041000320010040048683c1650a0300c9c0380c400f180c40641c1107a10511502c00960411402c003000140f02e4981e4a610040c02000304441e80d500700369202c0c44500c00d820403a41c065001640c00c2c0d1041d41004489111140c80c2e5042d080344820001098072806080c4000301f115101141d40c18004e80a451803a40a14440d0112510343d840c81c00d04c0da01400490301c0c48070f0725212043c83e1903505480482241d16140d0404020640c451401416420202c1104407282c8041d0003210b440e4010399450007440b0080440700d484000700d041565004c3d814a4069020182060111004500154002c5003240c013004060780d00d07248640d12185a80d13030400e401c000340c582c0b50000280f00f07010442c1950150100c46540d03881805d495460b951940a0715071303280221030250b1300080041284e90300091 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 275723174 1250 275721924 275721947
    0x10305250e0403030f18200f060c01090b090a0c090506010e0108190903020a0b130b1803041a0c0d020f100e0307080424031a011b052505040501030b0106 67
    0x140009a480b104075107042254114030051209440e03070304a42040c4010054081e03407560040c610581147c0d07051000400b00c0a02d0300455000b040d003c80d12012002080d0710940310b154211403003044c3c518050034100d854001c040f2044903610018580400c0004807449154864001a100d07844105001c40054840b400010000400c41200e44a0203e1240c0f4034024404990301c0b070f4000f003540c002c451525140c025001082c104114448481042c0858071102245800c84810000702c0401c02100c03016600714440c2d60010070540c00544240d0a98803415402400143d1108054455170302c0310030740c126103c0c011101001e00742e9001032113008010019600c852502012003080380d01d001402c1d0703503184040e00983c1c419811082881151106038035090041c90088200d40707420095501c2c80103111610000c4248081e04014030480e0304404581d07030203807200c0100d42003403c660300c4900c0320300301d07840500380ca12a0801e201c0d258140018141000d024460599501114440040c2c3c2004070031a0a03102a2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 275724424 1250 275723174 275723177
    0x30216092903100614011d030703080c100c120f0b0f0f040605100801080d05030405030a0309110d140f0105130f081207120e0a03120f090206040e010305250e0403 71
    0xb104111205403d40c4039400c001e15801070041602030412002521000f1b2018041408001080d0052816540481d84005403035000300f43c15100e0440500c1c5500d00210340c01422495881c00d55507048a641020f80c81e10140c3c44014280803001c01e05c3d14007026a40d5002a058008013040e903504424a403806e1042c10319440600002100383d521400104c0d0004e05041e10303400310350101c00501c4410000c3c04038490324400b44c1021803850a20f0380e1035076a41e11400308502c080550b10f01ea00400c01c08101044101c0c00030060000e2014100e42c1002d04401c2c041101c0400e051040c11000d0301224010b0003614400c3e01a504c04546407032041e2144c0c5074031a50404120383c5002c08103e1441c1c0da03205001e005020b0340d6903a41d5070070b41c100046400b40c116100c220104105500140459001940c0101ca001405003450400b00d183e01e1904500c802400382c2180c004d40c05880400c0200344001c2000d0342c80d040302e01442c1116072140c0254944411010307404401000035500800038031900d000414a540c00c284203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 275725674 1250 275724424 275724433
    0x20609040f090803060111150118021b070503010501060c0c0e09010605060703020c01170f072717010b0a0b1204080f0304231606030914010504030216092903 69
    0xa40144400c48840890440f5402000320a2081c0c41d6030003803240c03c081c1c0d080d00c000c08185001c24a803003500c01c814400c518200716200f000c49600710003601034030024500e03018440c807413900c0c4c1018240c0b41d241d0b0307001c1c0500031341c41d101c0005101803040241540d1141c0000d03207821b9090400280e103100002c01001c03108650349500c00000d103500d6903001040058069805000e00103043c2d0300043c280c00c110340707000e06035480c00c0040c841c1c0300720022407a0390481064180903000c400c521600c003074a15080c51104c0880031180000150748807000b9a00781110180300008c21541854508109295080740609620440c080c40700c10506c0f80a40142c54202d801b8803e120300708000120003880d20b41c0220f0701144c03060901d04081c20190456211280081d0003a8094a9104201c1000a01c1d4078851321400c4101a244c411400500c2041e001c500001d003c00c0000b40071516141c18003a64666410031000b1200013090f50000d182000c3c3d2142d2101440c00c0241e9200c804030805282c0c01840c003880250383e06004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 275726924 1250 275725674 275725691
    0x1d0112020903070515070605060d0305161407060507030e10020c010804051002030103060204140f1c1e1a0106031b050a2609120705070605030907090212061f02060402060904 76
    0x1100038111455017552a54241d541c407252a0000642d400580401c0c01103800c1000074000035040400d40b0149c04a0b0001004640c0b42400d002c244828044203542c0b13180140440450b0241e44100102a01402526190800d54550040c0315900c8000d098000050708504401c816540c03013040c1e2141c000c0d000720120380c640084c0c4041e500499000303031b0045a1596000800b0007080100ca0328a070850344040b54003030080c04881d008100039600c11545125405081d01c112000c008514035124250040c0c982d8a040d215045d1802406c8415001c1140900003d0750000003a05807003400741044040b0308841d001d2100c0003401c002e98154001c01410000d01c04031440d5240d4035a07846010b01c0080942441000e03190034011440c80c00c0070000769070464490410001c0d4004600300141c08011a00303035142040d501e070741d072941083c10922140c01c20b1651a000060f0b00c0491004202c100b401950111000380240ca550381110780716880040c3e880c8056013001c1c0010700940740c540d000c0c00000305d000d4004503150300d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 275728174 1250 275726924 275726929
    0x1a150a020f030f040e0106020309090604050601090308030c0a090b03040c1e0923010b090f10111b030c1f0c110d03171f03060f27031d01120209030705 66
    0x2004002c1d03003440303c00007040c204801e903e1030b010140101000c0c009985008020400304640e814024001801a0f80303900100d511640715005440007503411101c49503c904009044800710341c0070102e5140010313026070b0007082c00e000a1040724040c50340159580c5d02c551414507041c814480f04110781a140071001e10000e0088041d0003480134101c43c10300c080d50349082035001c0c13840400040e0000b800b10740f8144501102d940f505104114280b1007141d0303900814120300c50844e441c0e4100030303070440d00e030048000c00400000440101c503440b4208500380c0d1100709140080c06403400070101c0e058143e1680f540c40038010740c020400d1541d018001e009010507203040e84040b4403082100f140031000540c140104600c0318035152200d80c0c0042401e000349030808518008482591128003000e4410b981d6602032108003046070b4441842c1d1044c103901804c0c1900180340c0305003100c402d2001600415008000c20060714002000c1030020328058403845030300042d540b0385800a4000350382494041c4a13524003c038969 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 275729424 1250 275728174 275728177
    0x203270604170706020304060e012106081c080c03010303030c0c060204080304080105060d0b07080a060e0c0901020d0f02120a020a2102160303020a0602031f14041a150a020f03 77
    0x4046080c2d240108591001d141890080c15521940c1107410505c002e010a0784d016483c5040d18009180c510000d00018034104a0244c106261003500c82c40c2010000c1e0440c0007098045001050414000075500c9682d41501c070390a0440f41090003c808000500c0042e020380e101c030019030000d00d4002c08090065552508903485234102024542c800706041013a110240070701c95000405442030719600c0c556540e000180440901140b080c403151030000b944c1c82c0030170b034841c00c0201214185c5074481d00341003000c40704070313400311804a00500802e1840c28510380101c0171088150030340d60044c016491010448a0a07401ca0303440c0d0401c41c01850080c00c0490a07000108410f031028205884000d10031010107850514483c2c094140d910220710304001190300401e03545021600600050391b00c1ea16a15100c403a514403003008044105c00c0000420910300301c049807588402c00350703002c205844060b0a00302c800401e4243c0c19520281e518600390803080c038600540450b5800b40100d4189103122101e040c2503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 275730674 1250 275729424 275729429
    0x6070f030c0f0501150b07050631081e030907030209190f0b01080601081005010534021302090a0317091f080f0f06040b190603020304120207060203270604 68
    0x240d83d102e508080d02d600c0440a1040288010f201d101d02d0305240b948d90139290400280b500070f802d02a40807c001101c2c0d07560454410750f0109000e903160015600d00482c950300121840c01d6110440000003241d00408000c590058500000601100d07295508108100500806400180388014054241e08146001d100d00c41d10400f0004107003000c0c00c00004060b135a0007005241001081c5041c0070060b0000000c1d0800c1e601c080c82c00c0c99a85540c1c40c1e180704440f010130b100015601c0680100740d1076440d03c0c082110a0f610071134440840e0040c2c0040342040c0d010b0449096403004d1011800c00c005512000c6240700400000c0400d8240004400000c51454600500451400c03002d030504030304540c0422100e900940c22a46040b075401c0c2401500d80d04036009085501456844800c410f255a039482120b1004800c45a022145525070b04014041e410540c1e003103074071301400400e15090034000700d000302c2910055402135051001800c640300c0004054980c6a401090308124000700c1e84586005001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 275731924 1250 275730674 275730683
    0x1030b0d0b0a0e06040c1203051b0c190602030a05090f060c0d030c050304031b1a070201020d06080c090f0a0618091214030a0905010e0a0501140106030b06070f030c0f 73
    0x107052074507005850680d80410750105030368000904020000c0c000c0c4000c1e5040c1d9940c8000580300510b14034050b5668401e4815a41c18440316034080305220400140c1c0040100007a2010060f5464420280340301c00c1c1c16018020144c5c00520188000394440d030082c1070b28940040441000803c103402090031903000c114800c1c0f590300b284881c11100c903050301070300000f1101031500510310300c0c054800406c20070004128941c500314030720a00090001c40c0d40076035a01007094518041fa41454070b4064000d40c0101c0300e420b21a402d041002440c0607001c00e40303407048000035104211700d56484005d001d00110050018181550b12100070680c0510b00c40032000130709100f007000804107250f040503400c0d0700400303800c6000c000c03000d01c89242b180c102c1c10580760015005500840e00342954641a80034100f01042c100d407c0c07291424100034040c0540007030a46c484481c0c100c00385a600c45070202c01351410310726042d0304041d0401c0315400040505c0e205040ca03500a1402d018454407036960301003040350004081d03c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 275733174 1250 275731924 275731943
    0x905010810030b0f040503070605180d09030503030610020708070807060e03010e10020918040c0e010b040b0405060706020d092301090f12030b030307050607030b060705100b01030b0d 80
    0x2540c00060441d082031140980a0711185165180c3c00c0101004050882c11100c1c140842e0030060100103642c50607030310150601c0303107191200c090320004042c0f01030300100b0310032411040c4070349000f288240141e03500600a13520b19500ca90501150040303140e085400c501c500000001c68050a11179240504108000780800d00d281010040c16603220000052181e40f410f4080541c100e4001a00c06580c0000000540c54036210000a4410041d240e00b071341d00e51210404000c204107809000409607042c0342420f010303507621501001154002c0d40100f0b070080c8408c1106001c9440d02d44003034141d2901c00c07080540b0305540e81d400481650b5070801c04544580d6403003464107041d80703000004240c12402c0c100802907030312a80c40700030100c0500c0030b014010b0141807003940c510a205e50401c2d0b4030024068100ea980c0c041c540b800720399a000440b00280000d29240d04c0b01c005150089c1100c40f81c5400c000104007004c0030860001c000d100b0b40c0c04035410b2561768030340d0040701c0c0c84050110304058010f88e10b80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 275734424 1250 275733174 275733179
    0x1603050d02011a100305040219060801090e0a02030d080c1309091406160c110406080607110c0d021e040c050403060f060e160e0301110d0c0807050f0903070f0609 71
    0x40c0c00e41e440d1100380400410205800160390302e440d0b08102c9140703c0e6185c0440c0c191690b00201d2020101c5840820315003500b40b50210340755070082c1c4654100c0d07070507034000c011482001001d0703a12040d0549009505800003040301c60118410441781d6007020140036100c0c038040d0318112a10043c0780c2503000b80f1100d915001040d050001d030341c081000c3d00032101d003d4100c0b8a0031a01d2155444039141855050000c1071140c4001d1040c4048103402458015204002051f15002070540c1c405080700c080c400911490b462104010300400d81810188000e48008644241c036400c01501a0340910786034205015043c941e802e582e0b4a004200300162075864007950b43e401c1d400d006040e9408003800d0310f6a0750400d402000030300c403240300c0d49612800c0340c140c2925028645001310395409400c050f180e4990b0030840e00c1c3c580e04c40418000d004000c031389001041000004003090b20004012511000030850601280b025160f142001b08007500c0001c0648284c05e84407040c03a200040c2507009400094040e1105 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 275735674 1250 275734424 275734427
    0xb0f070e0d111c05060619080709150b07020f090c071a01051201020f030601030c09030507090203010512010911011101140108030c071e060e040b0619081f0e091603050d 74
    0x2c041444101d07094016a509072a1510f56554402806c19405445112051f00c5030260b08100754014246031720903604e88a6403810504013404d4100800c840010091500041d080450f0048456150b40075110a009a038504c040028000c0000c10702d00c074940301001140c0020341c807440c2881c0804200400140c0c6541000240590300901d000c00d10104e03032040001130462030f0400c09807035100409182c00710300915007032001c489406555000900b18454072201080341c1d400c9802441c1603075815030300301c000051140f450a0076038203c6403000d0140d200901e81480c0d254444c1c507583c0c121003002000411203e4402500750840c100036440358804e904042440452820b0521039072000342200186008011412802480705c2e41d41c41c41140148840402c080d5140e448a81111a06000013030440c3d13215180c4280801404400700c85500000303a642000071290003450841108a01680b580022068101b005010b50048042e1001c1a030740710340c81404c801e80284a035504044d5110f40f0183c04191a00d400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 275736924 1250 275735674 275735689
    0x3160501081909201002071a1309050402040f0204050f040b031f09110a08150a110301060216090612020405060619090e070801150305132003070906030b0f070e0d11 72
    0x1342a11802041d610502072139030008600d000d0300c641d0f00720b0403096030101140341650700c00c10b14500e4003481e5080000030f0070300c2d182c2c1c802845103000343e50912070300b942003c2c208201d00c03a0307028042d44910720020044481c24148c1c05803640e100e0250480b40c40381000c0c040d0681d0b4854807d0030f03881c400d0320381034254204130102e0039400300000c055912070b01c2c5c24103003050303145c803400000c4601c41c40644000000e40d8940c495013080c001d16407450b440c0307680c0e0758441c0002902c0d160030b003400d0107401159880004070485948500d60403174512100c042d0305003410340e00b040b028203c050b100c44c0e030112041c1f1040b41007003038010807240750400e20346400c000c462400c41105c0340300c40020842d009000040c00108984400d41031f00680042151400154a0380c4112a0310003040d0110800f51081484c0010000d011074141644070158504404883d1020b41e280c600500ba6800741c00001d14003290040441c0d00c440c0310f03810f055005030403030500c225a014100b020688a450100050712012140796541e04103060208 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 275738174 1250 275736924 275736983
    0xf0714030304030803010314010204121104140c03190b130603022e2709060815041a0603120309030301050a0506030402030d0f0c050609071403160501081909 69
    0x30059410103155460350381d001e002c140f102a00441c101000030300c66000c2981250060070a4a1080e0440c0c00c060078007d400c2c1d80310383c0c0454015482d0142510035400c0e0f480322240700382e842c403c0440c59540e03400c900e89490814400c00d2484141c844506403181d80c1d40480d08100340308030f0750000465900e180100030b0304840c440382142424201d5000c14142c0761170443e80146a1019060014500001c0da10007a0000000c40888038903044250000c1203044540d04454110742e640c07421299100ca0643c44d0280c540d1058500810782001154102d54000200c44c4142c0c1c0898002c080d02c042c049141d00e40501c1707a00c1100c0215181d0000401808a031602c00507600190805480301c40c207520b06540440c1c0c0e0303480903c2100c000e00200c2240c000b0220312850051440c0f82e44001135500070f00b0501c0c00c05903203150a005050040512940041c03040c03c00007092000982490000e4580782e107800015a01c0c034502a021aa48814030221030710302001902410304810300c1402070105400e1701d404029052407800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 275739424 1250 275738174 275738179
    0x203090d08090a0209040c090203181e0a021e0a080a02041118120106170328050708160c0b1806090307090218030f07030308010b19030f0e0f0714 64
    0x1c01480100000081d0480143d42e040e1603982881e12581080001c0c12800e6228130590340c0008100810111074000c9844441c51120844180c04c100034501044a900b2007110202035204480c3d400142c6801e03120443d03226800e05440880030340400100e50180240c3c1c10007811a40151440030441c1850f00c42da27111001c04440c02818011002d10b088040405804a03910400400d804c04025180070350005000b44007200720103004401c14610192607801254031204120014001d4100310460944900800e02c100d0b6100f502c0c002a076510001650082c00c209080c1e001d40440b00e0000424810000d000385c102c10070a45e80725030782070360340000509401036854042d05060002911030385001550000b6244030712809030b11842d00f00c0c00e0081c002d040c812440e80c1441409811003841030082448009d9074000d564110880c0c1e01c4034080301c036070f110340a1001c03262401880e401c1d01c014442c5e8002540300350203400110301542e000c991185407118060045480d80c02080040008203401c0c020300400200c00e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 275740674 1250 275739424 275739437
    0x37090f050708120d021327050609010308090909071203050309010b0a03030504140409060609050106021b0a0e0705070510060f0602070302090f07050d11040905060405040b010311060408100203090d 86
    0x1c0c1d03995003e0714000c0500b560b060580208042625200d01030080300a020614040e0100010501e40c2190302c2226804150003240b404001c80c00364104041140d060340e8000f1b1900d0303d003210b403105101010340c0c000d20b02070241c02800000300d508103815080d504814060f80c1c500d0b4582c140114294219031000c1003540c490340c121a4104006500a410342e02200c441000382401040003c0106001d0045008003c20041c6017110202c0c15180c1540300b41d05940c0700340e00303ea406110990104010b180c0b0750300c205a10400000702000011540040036911075054641075003040010740d00c140c5404602226080d01d262280c8007482503101e0000441c0c01010144001c2c908a0301e540c012402c450030140a203689100300c0c030009121240904101d03440200001c07030800c1041416240d040e4550094016901c1550828001c21038501c0e060007100c0c056034001503c400b8607407030f5a803101c81c4c40c4000011142c000e03902f80000168058107200400e0044207143c000340c0d5034031349424000c1c181807003000d2003401c0c08072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 275741924 1250 275740674 275740693
    0xa18060810060311040503101d06010b0306060d0b09040c03020f01091a0901051303031d0f10030c110d030603050c0111100b040b0603040f031737090f050708 69
    0x101c01c1c0d18403084031058100081d4110300c101020907144103540143e030b0544282d41d8441402120b40e070040e0b245e81d1707040e5002d11100b00506a01926a0420700c038040c3c0110081c030210b040c1d072a00400820850071501d500041d0304c00c2c0e44c2c000c541c55030411201035607800ea0706c60041040d401e104a4070714904a091802403140350510b43d00852002a01100d90400600843c0b12043e41e4054022a249400c40f010260240d5a403807500034000e06121140b2840400d40403013811050038114006040142d00500300c400340c4206000450081c60020222400c108004480f1849480140320b00a420861743d500441c000d0709504009141000c1858020b0421601c030034100704a1002091458203806400801b20b5110034950004001c0c14a59034000c2c2d01040000921003007150781410300300024403d450b40c00c201d000d008040032200740d049412800c1104150a20b42c1603a0307960009a0402020002260f035600d03041d0b81d001e00716601b0400072905c01c0e4840030240b0130702c202002400e00402c3c0c46002800d55030f2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 275743174 1250 275741924 275741941
    0x60305010501050a1211190207080a030e0f0409170c210304120e060301062106030302071e0306060311011707170603030705151509130311070b0a180608 67
    0x1003940d901004001c4101080000450b103501b011524404004080b6140c031030a080801119604000103c05882481800190310301c0c0899440f000c00d426440701502250644280b00f05c9010a0203039640c80707540d0f4608000050009407010705149150300c0056210805400c0040c40c045146a40c09802c100e1802d8005440d0003050440e1f5003d0340c0700b0b00400e41948801c9081d5118889400040c1d40914040300114003a0340c001c901c01241d420707010102070842d451290304021200203003c0540142c101d00c0c1c1c10322140452850480075480002e1030303646010390701d468400868501d6002150180c6103451402c0c881d40e4441c181c0d49400c51421007166041c20204009081005d0307162140d000501c0c00c43c000fa00c41c0d07500340b0540f501b0b0b640041c01e0700e900a000355940404074004445800401c804188041303406e04151107481c0c402e00e0b485040b0002640591001d4400c080e00c1010a8098420702c0c001060312204d076400b0300080001740e1140000501c0c0313103125000500b403c2d00100108031140e0100036104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 275744424 1250 275743174 275743177
    0x914010c0c0b061c12230a120b030a020618090705130501143a1103010b09150a03140a14041203061e0e071803120306260706030501050105 61
    0x8011150081c90041000c401c80005011200c05420300180418201034170341c00c100c0c0c0016090440c050200f501d41c04140c0c40d800c0e8010001c2502c0001c0b00c01c50701400c51483da500001c00000700400715014040f89a0001304254023038003d002c0340014080c0c032071100c0d04100300d516812003034a04102e2b0400318003424840c092012031003607504214180d80c1030031941e42030b4000c9411a80c110b06040344480303d0503c4030700000240e01001d007003a980414180610180621400f104d034241800b80510b5079280c942c0321131a07600014415a80708002c0000060a480c00900400d85031819880100388034201a154201002c00103002c000040e0034205a000c0d01040500100da0003a400b9500749102549628114010005608500c040014408290214a6488080c4800c940c0241e000e101d4960306c0e004c0803118a1403500d0590020320300c03000c0034400500700c499500900551340c074000a04550301e548060124108120b400000881e01c4e407031001c0b480742800031b2005001c25040c20300040d45801c0009015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 275745674 1250 275744424 275744431
    0x90609120703182312190515100e01140609060307030906020301120b0c0a0207060c1703070807020c030607020d2109111f020307030305090c03010914010c0c0b 70
    0x25208001030401c201801400712a0100109180300d8a1080d00c2d40d207041035102549001103c208541c0b01049458036055048003009018240540480096070400d0901d4003001e030400c5603c1d005502e81c10402503140c00c031030b9204071109100c0400c07640c54041a40c1d40c040042e00000c603a001c06c038074440d48c0d5484240403101102d0040d58826a02d56035013204070024400385800504450001000140901c400400d055030036028241c01c1c003440d229240b82111138481d40200502580051808000c2640104094000b0900503030a604138003200742d43c91005035104441d503c010660000a0007401030b4100f1015103e04c600360003c08050609010103540c0d104041205030800041a041081d00b60038074500328031890107900d09005000e011300c1d080c2c01a801c6c0b6101c0600074194580c0244009e6080d40420821400ca90051841c000701901c0440280200034a0507905116100c1018001e89003441a03006c15401071007280740c2510714040303181c251245c02200800300300110034800301251941036080d41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 275746924 1250 275745674 275745703
    0x2090717150d05120c0d05070c06030203090f0d081b030f190e0a0503090103050903040b04030609080702030f06010302011128050a0c0f210803070818070f030b090609 73
    0x7111520001c2c002c28159100280b65024200010080781840009491aa842641030341d0641c03415017000c490600404901030100180007604110f150b009034000c41d004040e0b8030941d282150000301091400400c5034035080040c142004000200340d041825560511070200c80034607500700003084140702003010703125402050301c0c0892000c081d801c5910096025010200f41d81d0140101d0070042e4681e0842600a4086400e0600080a01c1c90200455080c1c444080880d41424216154007000303048940c0e048030010401c20403040565020002d003084452000010001581944001082c0b45040c00480007030ba840200710120620403845a5840038440654520140c0e000341001c40c540620f00401034401c0348542c00c00b15600d4820440351007504d80314104c2c203d0790144034000384500c08c20504050912030083c07002c40c42a91103440160380110011000200b4251000039503810099903510904440c80318076400c00070480d0124589503c2007000020304120f2820b055900d44803c1310000c20754 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 275748174 1250 275746924 275746951
    0xf0c191a06190306020c0706020d0c06020307030b060723030a1d06130b04060207150504060e13050703020a02010506030f06070c0602040f120605091b0402090301180c0302090717 78
    0x1d00640302c070440c01491804008842d004580d503402c0c0307900250f01030f04091086000e134440204c0d500d800092021620f144907500c609220400b602c0310700080d08060010010140c40b600c01c21001d0b40c0305005440070724094800e54803d1882c0058101e00c414858259003d16001404094001d40d08540084411200c0b0141e52004504080025107180300f05440300f0303a10a6808808a80c242c140405001a40c030203400720b0742180e4803008640c03040713017941407290f00041c0104824020640304460800e022100584450140607282c41000240c1d00111222400203038046500d070541942400341d00d821003400d0b40501200c2a00301002916550000c0c502014043e00800300c1e820044250304440c000e2501e40c1100c004180c507031000e04054004400705031006824100801e0800384003280403121158109a0082802401024400039410517114941d00d95665141e03002c801d600e1088118449104602e00d44400d421441000000e80015011008100d01d101817840d44407121381240741c01c2054040480d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 275749424 1250 275748174 275748181
    0x21060e0c0a050705010e010504020a060518060a02010207020a230616060504020604080610030303061e140109050301060b0408010e061b13080319030b0f01050f0f07080f0c191a 77
    0x30b403000d125a04004000303620f00000b40751060310640c0001d010b00d03c05c98081e080c0fa0380d10941200c460140090118001d0303408200800f940c5800f000400d00c0c0321044c0005414252160001656680c0560050b003002c8844030001492414601c00054042c00803602d40e802c1c008648181180e000803220300514261303036000880c0030355440506840041114500f102d4a43c600b900812600d0180340c0f1040380032905082006c47e800d168403030400c0802035038206503002c0074034194241ea0040c04416440341804003900020440361001e005540240c94400c1c1c801d659585820012401c41e0f255090701103007034102400340280b40014001082d14132100c00d04140d110148041604c60141c415403060113540700000e42c00c2071b02050007120314a04149614108404038020003807207109810303e510940010380070041c489035039400f9409030403000d208803921030924195540d1646141e020700f030181c5d80e962010410b0180c1c0d0b07900b04006001000f054500340200007013aa40c252a15840d001c540d800015540c001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 275750674 1250 275749424 275749427
    0x160e03012904140c04240815040f020a0306031a090a060519020d2313030815030a03020a05011a0d02210d0c0203160303021507020109021021060e0c0a 66
    0x1400100c1d1454012456030502802882181d48140700e90031a81540c01c5055907134800c0429a4050840d0945451032a80c1e98210080380c90000080480c2d4852b507203003040c0007220010320180c0f05120051b1000250241542040e07101550020709102e1081d040741d0130440008404a110181c80f42c0c0200c0109407a01c3e0b441001d4951209201010f030260b10208a0410090481e04880300d8825150499104151808280031a05604640e602d2403041c0761995040002d20a81c0c11a500ca0090740c620b613010014600007070300b460000401a4016403018070740c6400c0c0082882100c140200108403545202104070204107110042c020183c0700b0b1442c0d0300036404405a0780040c0741d5030f10f0701005a0b00c4d5007030511030241802e024244c09a000380f013a4840f820440c0c01422480040d25055002458031040c5e00303680c40784248004009c8400c5540314070a400041e251003504801500b1248c0310503042e881d01380c03045000c6100b6006801101801c0c00e0f4204851000e4800e0b16030007100c0901001c2c0da903403c1890 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 275751924 1250 275750674 275750681
    0x4032007050607032601051c030905040c0c02150c0a0303020711030a0605010f05030c0609060318030d0501090c08070f050f04030b010801050601030b0d03171905160e03012904 77
    0x35940281d00003c500d002c06620070321149a420300d6180341d0183e021750000c4203c03155401d02802c0d401159000b01040b00b2403a09002c510071501c64a4a40802070f1240301050070307244000d0000001c140d1406001003140392154980700494004400e2500740300389500e4542e42c801d6000800b405160303000074044207002000d800f040482e04045e04071400603406140c0100103141c2481031080d8104030417808581807601060400000c4802010581000407240c2001025800602083e000c0b9a1921030040c03552414809026540c0c211040080d0302c0d03250081140a8030a25145d003004c0002c07600c20008a42d80081c4214042c0c8410300d0040e840301c0008a00c0a410b2003180c2000d445455908000030301841c0540026100f00b40c2a80c080c4923440c0a01c040c00416a800d1030300901144881c01111500c4044c80140c66006030528049001d030900b4100030411074409a4011520f07032040030080c001c164100c00140300d1002c06070020001d5200c05414100307690410140039003d4508103071007240c03550700c030382 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 275753174 1250 275751924 275751929
    0x7050d120f05190c030b0102061503010204030b0103050a0b1005010f03200d1d0601050d0f0302120a0c03020d0915080a09060c02070e011406030121080d0c02060f04032007 75
    0x4104040d080c000300c480314918000d8103810702141001071070360016111b801914080304040e0000c2010761611403500c00c0d01205102e0180d01507509000006c0466002d19015000794061000b62030100c1083c00c0c5010360000080200b0141440c10f20100216603100d80d0103c8a20280e18001981444000300e560301e80b40188064428920013007105000014a07900c00c0c01d42c882003200d02d085880c42da0703441e9a00c030442449034960007040580a9400f0580500310001b41034400c0c41940c41003018111704201070741010f110003001520510880c010180c04001503012015141400c0c402c03240f0300040900c0d240d091004510801c03049130085003a21440303800015000b079215206000e488030060000303540b11414403c80303403500f440328000a041140c207000c80502c084084c0410389103a08020750b451581d624501404003090030f80c0c0800003c82c0c184005081c1d055440100482d43c40300f00070000b03140c414050a940c9c0c09040e82e40501c800a80c0114280e00c1c5206010301240061003680340440c200406507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 275754424 1250 275753174 275753201
    0xc0a02040606121b0c170c0a0303050402120601030b06060a0e0a030f12030504230309040f0506030714030d260718060309030815060903030c0307060b030307050d12 72
    0x110002c6507107504003000b4482001200400c1255240a50701103c07003001c800e000d440800d110b4a00000440c1d070141425074884148094146031259285c941450140e50280550009a44100f030200b10719010b40d51103114141c1000400203541151a01401c015020346014070500b000990141070600641800f151120004c050711076040d80c0707090403020f01484d0403048401c030b80a841c03400401c0b4002e100f00c85c000c0e13030031a010000841815110300c00b0078001c100c0c0208548804e001009156803030340a10100e06c051104007041c14180201818034240e05500107103c82040c200300b0312400e440c0003440c10003883d5a850100703100420751404040390002c0118100b0b03000100030800500343d80140201229010f41d20550b6100c603a1000101c00b00e60f85c1000040002d100b59000c140540343d00d00d216801c10100800310b915040c600d600007880c641c849626040180c20100d00f880030701109206101140105501442c90300d51142d48007500d41040003155028040240700070320b810346540e8004108815403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 275755674 1250 275754424 275754431
    0x2060301030506060a0509150103090602040b1603020c0d03140703030b0310050609070504080d0806010e04020c0f06060f060d05093c0304060518061920150109020c0a0204 75
    0x10381c1401030f220312040301c8480c00b40461220029203070a0030000c0e40d1058403940348141c01e02e0114070044010302070b00202518800c0d000e000200351000e207040105208011b420054903035803014030b40030b41000700b44d2456a210761898003038100465004a0000c103c00019006507580f00c541c0d00d0b042c1d0040c0188031000c0c2c5c1500c980c0803a00711208469010034002d15088070080c0d025594035004440038415401160004d8010034140e05246001d454296003041050402500900b10703900824103e800c9060280340c0e0381d020440580c2d10700030900595411800c140c0f403860f0b01401840100740d46115014a40400c41e660f0000100c520005000001501032071500c45d01c0040c82c44081050511030b0003004540740b050840524020b0940081144d0454940e51a810705060100b01600d505007409030700c0a4100408100284180c4240001481580b00399150035040c0102600041440c1c9a00c40390b500480d030120b000c800f4881998001d507070445034100c2c4003580d075900040c862400c040c01c03a20002d41203401c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 275756924 1250 275755674 275755679
    0x20a0e0d06090b070c06390903050609030d060f050303070206030a230a18021c080408060c0301170d05120604021b1c03020301120209070203040b040603060906141e030a02060301 78
    0x501c001000b840a009000501103010004480032001d408000e44403207c80d10b1030a2809203203000c0d40704507441c815900300b503448240d5984501b03090110450f08005180c000180301e111401e03840c841d035005400450020032182d0b08150100b40e4078440c01c1c9010b44200c001000284d025100c50b0455a106050b102c00d9090410516590119040040c2c45101a990403c1066002d000d90150609282900104040008007d26601040c0b441c03d40b901980c4a110400c40862908001c01030b85025083c1750443c1c40d544c0d03142031044901ca40410040010300c0d000b040c80030011503480300a075002500b5248022506465440000e00240f003107444800a103081c20700306901c41d00780403c44000305003044000100785038203800210200e1009000d118002e4440c0490320025081c40c0c10416803040c001d004480c80d060302c90354141282d411960049001a80b80c07042848071600e10b00038034004014240c0c02035262581d1200041d00403540c030300041c1c0c2940c0070000d01005a5420401502d1307160b00988141d54958 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 275758174 1250 275756924 275756927
    0x1401060308090907020a170c03121503010b0a0e01090c05272110050a1118030c010503250306050a0303021e07080a08090409060c020c010f0201020a0e0d06090b07 71
    0x1c0012008601c543c42080009a6850010550198096006d04200c46580c0080d5400c1000e4210189440c2240720038802c1d21441481415914000c1c5503540340c03000c005071b0000405003964203140416001c2c4075180b4080103d01e40c82031501303056032150ba60204920320b03001001c0b00c0c68050720080c03040741504100454403e88209044030243e02d400e6400c2c402c03078500c100b0050080d50500d8401c2455901c0f03000440c2d20301d0036540c400c5800840d00f120100b808240307100050811380200302e00d0000d4607e0b2003000a2240b804008040c41c01d0303420b091090440c9441d046c0b0021904600000d55000700703903507141d484030502c69031144010300706c0104907030750840d101c3c100250b4448000c660b42d801c40295200140b01080005003007021176034144028040b0070203550751030300c1c01e400070408260000d85070b00d903000004105010348810868140d00401045d42c140d4001010440780c0b4240f0760039a441049840560b40c3e00c0741103006545404d40e03031580b42c1354191400d00300401d8900c1c0041d281c0a2400140700103c1d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 275759424 1250 275758174 275758177
    0xb0d030309031e0906030902060919150e1f0c06050a021803010e030f0f0405090109020a261b0d020a03020309070e060a03060902040f061e1a0304030c1401060308 71
    0x10342c0a0f80e61651080d041039221000c62011856140210f80c1e048400c2000301d100742c002108091000c0c1c03050b41800c4d0185d0104c1d6039018100c00307406010313400040c10710842050751181201b2800354a0300c16424a4040c011a401d0391005040c00c0e02c0040c005490284503000e0364400409a030720035410400c92608600e40c40003904100800030036984041001c001500e4140103149260070f084014601c0c10304600a04c11441d40001c411041c20102031200007529030b5845601802818500e41c090b0740d49072102401043c90f21074000901c4081421001161081d8110190b660b201d620f000e2132240b0040c0c0031f5000030f151f004005681d803196000058920300b0940c1600a0360080b5200011600d00030b44802171a18002d1044030040c0c0c11071000c0c4010404a46150804000e413800900000340c101d0a0860a400740d03500b85c2c202c981141045101e007032407800c041009000a007c0c0d141020582e02101000d00e046200290014041042440000060140780c0114078030040080000b0800c076580da04c0e0100030f0317 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 275760674 1250 275759424 275759441
    0x100506030106050105090a090c0c0f06020a030b0d0c0b0309030d180201230906030c04080f070608090a050a020d060b030d0c060606030c081305030408010212090105250c020102010b0d0303 82
    0x35402c010000946502071001d0741c2031b0314001091020464101185980180700c11302580e000c101c05100507201143c4010f040e0201140107a42c0917943c0d030544e41c8060300f03940f1000e039400e002d1302c4400c107000082070f500c040030015030358003000069994880343e266500d94003403030081c454020310309220b10301c81c40342c6d20709038010440c801c0e22150803031038810980d69041024850441d20b4140300300810160703484c0a5000350307401a0010400c070f08091b00e595005203010b54124501c2d025500041061211f5500900038561155910005003000c0c0e501350b9486448841c8218002c0c000c41c0c00211490030031810b42c12a03c0b01c02005021600b511286440041044c000000709449a41c5081d1010a0311031081c00b0355009401c0f00d49074031b406a00e40180e400c840c4125000140c400d808140004140d01d80c0a000408240700c1640caa09401e01301241940e0071950090004501844800610a400e0100070815100003080e410004803201103400180d01400742c80da0712541c07001440e840c030810141c05900c040c1c0e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 275761924 1250 275760674 275760679
    0xf03031517160e0906070c020d14010b040f0b15031308070507060e0109032301060e01120c080a05070506030c070206210a0519020f0409020a031b02031806070212100506 74
    0x101943d0710066100b00d1016140111240c00900028900e035019102c4100800d2016015191020b030326101c610030360303031501d0510540741d4540306d008080c3c0c42d10f400741d003040720740468003006960f25003800a5910400c041c94004103c10210000d010340e15000e03054055680c03c00303591582c8155070320707000e6100c90190280303602240c0340781208145540303e0b07041d110580fa8800300010b86850b2408441c141b1070b02c58060400d096480d148041214204c4400150090018102d05242c00c0b14900d0040340205c01500b143c601c61307100c50b00304001316100040c0705040f41c03c01d40f01c40d5035a44404071500c0b2607114429010f07400c80743c00115884210844400d540c0641d0700c40c94030340d210351540003540090712019140f81c0c102e4030019203035030228800ca50041c45841198914945800d980f40041000d90b0402c0c04004e0110b999000ca07550300403640c554805940c0e982e84065440d004500800082002c07079144102c0c06120b000c520305045448200c01101c0711900c10040f04c1018240c603805038090141110082d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 275763174 1250 275761924 275761963
    0x1a07020a0b03060a03030507080c010e0c01110f250807120c05100e090618010f030c0e0702030a200109060b030d0905011b0317040803010f050603040f03031517 70
    0x980c0d407842505032401144010030422200780b868030129000d42150800362004c2004004140e480340c2c1c01d104031410307042d070800540350018081c00090200030400e0b070000c03440c0c0c208a44102031954007044040c00c0d40484403a40e001c10b8050300c0c14a8000722942c1114207a44603c4501050000b00f424000e20501d1050206010075911042801200305c0c6103c07168010940c0540b08110602d8000310036640718002510905c0c8481004000084a04080e44503d02c0108401303401e000b40020b100015010708101d03114050142070501c0025524810600391108000308a0b20b09050b6402091001c000e003100c003c001d024100e00780c1010f02c001c104003c8000e102c1d2240c1c25203582e41038040c5d8030b910304441f4161038901e030b0b41f240468540f5014078200760450411028070340c0c07454000400c45000d070060f0302604600e1388940c10b200c02d50b4890302c0b00b6040584183c9080c000c001c0020303104540302400c19810328001c030b20a215103c0d4101a140326401543c006052540c45680c0307980c0014403000c20724403065009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 275764424 1250 275763174 275763179
    0x30a1809020703080f370510030314221e0609050a0605220b0706060801050c1b0c03030301120215030c030402060f0d0203070815010f120c05041a07020a 67
    0x310101d22440500a0210700c6100008a0305104144440e0f030010b0b038040786543e440000e0b459540c0309546410590000031048183c2c3d09484410b209240d4032054221840c00c0d4076045032400380843c842c908111003403403800604980d180d051842c4c000004400c0300e101007445a210b103601c600c0b5100223001364003090308900c400074410303101c0d04509045540c003500d254242c41c20140b04944692010f90308000112003100c21407809134215074103000401010445a46650b5141f0348a03054a00d20340c000b00d081e07070615045c0321101c00c10000300c1d130103002c94040c90b1900c3c20089040034240200c00c4041a0705000c01700002440307040e000300014025108588003044d41e00340110b9042240815221115809010300c00200182084001841c0014882441500784410f0035007103026640104c8113480012011400e001c0300005d40194401c0740342003401c04c400b002421200040ca0740c0490404284601d444070750510006000307000712005401064400d00200ca0a14000d1074280d01ca0f0f0000c03030081c0708c01c4100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 275765674 1250 275764424 275764439
    0x201080a0920030a0f0503090109170c0904020d0203060c0c010c031a0f030703082106040b03100510030b0c13050307060e090604060e04050a02041a01050706090c0503030a18 76
    0x35015031030703407008030b041c0b80e507180c84400b20038140c0301c4204036014820307450100c001c691410404908144900b004554819880000410407000e40d40241407403030903241c210144010200d05038040400998a004141e0f84500005401f0548a00702079094000d440511080303c55003030050442d1140341c4001e020001000c001241103a070180701513070035030715030510301e815502e0301f81d00c00c8603c0c401c01030859044030303200d840e0003100c0c0d400b100d011203c8422040c103c3d440041c2d140146a8030140032101041804050404030780c60300d00c0011180e1409a481e400105901044030400001e19000310042d14141340104000415520015840204604040e0005420700c0c002a83e0740541d5170660341d01c0d140e002a10706206030301c10058000c40d40301f40c4422002c9554031981c003086100c0d9005d2001801d400b030440c014030040b40c00750b40044409000b07202500e400d990300003048a03100c07a03101400040010b01e030f08020100003065000540d0501001803460086580240d01507681384403014a000e580743c0e103904 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 275766924 1250 275765674 275765681
    0x14011d190e06270a0212071d06030f1906080a0503070203060a060b0a1101021204030e0108150a0e15030d0f08010503030316110708030a02070f0506030105090105100203070602160201080a 82
    0x81454024850880e00c0a25040070114a402c650804e6001d070a09001219a040804044031410f0018034088024141d0724818040c90106c100259600f0b0f1942c10140101c4035180d0b402407034032143d240b101511101d80c0c8890342c4000c0c0103110000907140c0d1a0018a4215240c1c0d12444007644244590000320f500842144112000c40b004915110701c0c142100006940c0c24425000c048070301d5500740f00c421701c0081920702c514419803080d0355021100e07856400240481030068024040740c000c00461884580f07845484405503615907890290319074038018287e80390050002e0440e094002d40070030f5018260080803009401c443c0340c680035141d0fa00c490034036a40c3e0000300c8131351410001c0c1c1035101c0740c218000c5280c107010124003010358800f01d48500d12580756a10800140005910901c002c200d50b0070340d81a42400b03044100e6045155515010002d80c0b6901d06004107486862022241034105000304125090164001070641d00d4504101c00030300400d01d140700c00e9020036410340000d030070080c4c0c510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 275768174 1250 275766924 275766949
    0x5011118040c1e050405030d0e010305100f21020618101b290106090602070b040305070b1c1e0501090902030a030e0a0b0316090f14011d190e06 63
    0x181d0780d900e0060fa9082d1003540303880d14100305050000030000441c090314280f11900c81400180c840c5040804000d0006013140c4006060002e80c1000344d2040c0801e02000302c5d80c1c1c040f02c1200900507040d402c075059803490664449002584035034000f440000c0c070714000326402c011f504201d032014a1b8241240003503074485000a00802c003440c1c90481e034000503d24003a40541d40101164a2a03400c0300d044201038000710070782154000c500f01c003d08201c0558100316007009015901000c5081c08d00c1e40d598207680c1c1e011809001c4800700c3c00705c0d030b8410140d105451482000490301c0244202c880c2c401070650b4a48a280b07251001e242410004140044180101c08003070782d025005040d0341000d07485c2141c1d41003440c0a10f5501020181b00015240700120240d80034a1054414002030710351002c020780f0f0b80440b0750180e070382030480700c40801900d0703400002e0043c1c10798282800281d00010403543da180380108010164403194a07031200c20084110000030b809c3e2100c00305203010507107a000800031480201c0c13 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 275769424 1250 275768174 275768177
    0x914010f0503152805070c05191109180a0c080c09040b060f12011104080d08040506150d080a030f200a050d0908121f15080402030a05011118040c 64
    0x810118240c8000003400d180c03041d0114800300701c04201302c4202d03400d0b500181e42450000d007600d02d54800717101c01482070341402d0344184050b400403500c940d10003801345600c0c40214403520f00c10300041d01c80b02c41c0344807030010000803400365014040507180c40c038500c081d180a80300c0340348a01f540c00c0030300b820004e0080b80516040006c00b0600e5445804009184030313071a0344650040341d00d4404e01046002401403980b0b0041001019841c3d600b02060340d07161000c904020010070080c001880003245020801541150201000c054414076030700224490201c003ea0051040f040011302e05800356041d80024016a80302030b0500000d14692035035500381206c241c40e640380f20310400c0114980b500840082c025848150300c00310307004000b502c031760110760092180d4402415081c410402e03144030b01c91031080102c90424040040d28100301405101c02206111003040c0f0070407801040565404111081b102c541c44402800740e080c9840754125641c01052036100c200804400300c644514060180a034040b039039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 275770674 1250 275769424 275769463
    0xf11030d0908121b032d130b060d020108180a020904080d0e0a020a0501031e05010b1216020703060911030d0207140607050309010f0908010606091d090c010f0302040914010f0503 78
    0xe0442d403c8200b00546c1d00d0400001451101d212000804c04a80d4410460450308414007541420080d0708060002c1c4054403e56481c500080140e030001c004036086102100442070720740411200615001030400040d610901c0d10003000300300102071300100907000107164184100040e4810b529699007d614009601c540030040a02955202c4d03800110701e96a0700380d040504008100c200c00c2218000c0c1c0114042100c0051101c2440c6060707611145c1001d488126036a01c4480b91000940b0742d070090000400890312018003c0c1032200c08588420b0246c0020107640c003100c212940699140b03141c1c804d091140d002c0d070303000c000300d4503008003035a00f079903048000b4500d800c02050046650f0b001000e0314106101c504031021440800900c034840140c1000c0d126507002504001000180c1c8240603032200c403060807401080a980b5002c10b081121150a00b401844132440650543c060300503034011001d0f1924103481061f11035080d010f1281201ca80c951065141e1361201c0906031100b5056001ca00305150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 275771924 1250 275770674 275770681
    0x41203020f1606020405090601080709090c051c05100807080618160b1c0207021e12030705011b020109030f12090611070201110304060f11030d0908121b03 68
    0x66002090004000076181e40b91105100e50404151072041069500c40c0d0b0100d000c1c861810b05051494000e102402d041078140350030328000b0300504040c0100b0000030b880d031404201c014061380170341d050000300c020b094510400c2403200d2801400c0455205c0d0204030212000202c3c0b960104014081e1050b900c06008aa41c070010b44005003101c41c100084a0f200b1007440c807407417203090083c0307102408149266a98886c024003c40c10180e68560f8522040d6204014000050381e460000b0700a030300100480c400b81c602d103400060400032070105160418080010304c54200710040d8402d00401d962003550300c00464901008a00721078000c0d500a0106542000c0c3c07084080c0030f81c0c00c1c404c000c0f900b842c0104070280c81e9a164401d030742c01e0200f250409400400c0d81011981c01281110a80b81e10400450500e498480020160001100d092042c0f2041d1058020040c00900440d404c0508907101800800d4042c50140030383d80c02029031160710f070711a0300440c1100d00c40103075070f641d00c90100014504544 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 275773174 1250 275771924 275771927
    0x102030d05090c0a12030206061e04091a090a030801080c01050702010c0f020a062d0210090f050a03080f070c121b0b010609050406080c060f0310030f06020901090e0412 74
    0x28024100d41818461409401000d54a130307100c100c007401042c038004013403014615000e03140c41c1e0050f2969101d03910b844052001420003000e0703a4811501102c0c081008456401c1c2001d00b03881c1c01c2200d14504134600708200e0110000500080041d1203030360340a06903070780c864000d80c545011540c075a0001d8020000740002d58460b4296000c958040e04428500700401c0e40081c00c0c0b00c1459000318042210403540c0300b442803a80c005c0e2000000d1840300041d02110b8280029120703c02080f07000e0b071071036594111100b4000744a41444032254014116070210a02d8180600815021100151103401c14400284114450a1071503040350384450369081101c040941916030411030000c0701e0b0ba40c8207887c161008109030700c810900030040e5445050310941440248025602c1c2a0021403050b4484240e41d101c0b0744452046130149030001c66015100d403924402d000080c03115600141980402e40ca110080c4000780d8000e00d0f038030b0b40907292495425940d024a20000804460283c070ba4030102c0e030010f01d0117 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 275774424 1250 275773174 275773181
    0x40305210f06040e120315010905030a020102071a0f0d09110117060d03030923070f030c090207050307080f090a090b100e03010b1206180f1903031107080717090102030d 74
    0x240784d000c05444040009504468051b002160321108a002c200e42c103001c070b541c0012054024190a8005d005201d15540011f0340c2e40c50284a5464034065007101e01a2180b005c04c20384001c8070340c0030040c3e5980c400c100103101c00342c1041c02090300ea1150408400040c0d600581c1b55030007179281c00c4486165a034a203002c00140b505003d0064080c0342d2100c141b000051103091f05400c00e103c5021000000441801c0600e01d8040300e074115002c18005c4d1072085c4085a21900c440c01100d11041e8056602c032200e00c4c180c0d045000d03113100200301c4240403503155540c031162805000b03000e00981d540c03e041a40e40c1001c0f000e80f907504c0d1480b074200c2c0f0091050100b17140305071292020362002600225101c0300701d2000c02c060038a00d00f2a14529048041403000ca020700310301030f05902a1290060000181e0700718415105e222108447d000e81e80ca100f503020403d802070b0800411203c0320381c1c2c0c03140c4540260803e100319600003002120000281840c3c00b0410700c200c02640c03e2003070107900a60400440c5102240203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 275775674 1250 275774424 275774441
    0x102120c15040b101a04170f030f0c010513031d04090804060f080f0103030e06210112110409050c04020d06030c090920090f07050c0105040305210f0604 67
    0x1980900c0c00c269024403007104440340110b10030303403d80d900da24002184011060710b0340c22a0540c0d0700324810000b2102c3d9280151015900410440389130103c01458440c64265000910b030028000170035510f024845e400c005d8808080030b24001c0c029030390348c10941c80c40d80383c0c2000003c01284810010351000181d44100110401e00a0000a00c2d9035640d16040c0568000364041c01c00151000601140700d5440040c3c950803994002c505203980d4110f40d00a408003888500d030314021000820304400c10382d03c05026106440710107150805035612001c80c03480c00c01d20380c1015101161268200c000b6410135100701c4d688a50400301a00c050541e440c1000042d60000590711607407a00c503030005c400300b0706851550005000d051000550302003d8980b004e202c2e1410501c4201c4044170040011aa40300c07801950340c0803407a190134144580e201001950715005002404500d903203484200002c040e000001805d0341a0740d81140602c003000351205401014041b9030540100703c8440100e03465041ca40c0001c01c3c13 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 275776924 1250 275775674 275775697
    0x705030c0c0c0406030c06090e10091112070f0e01081005130e01020c0a0303051b030601050304080c150105040e030c190c0302031605041109180402240d06060905010212 74
    0x100386500c8001500341c0e04c1075003064a4411403070504100198101d50f05400070b0620101035010303072500030b604e807007905424480c0a0103035440d000c034610180380141c102c03142035000c8141880c40d81008040103240c004034000d50f00c04120440090185907024031102403080c420000c010f0035960412082c4010340726004d80c1007903c142c90342544020b0042c207001400c00c542e062070040c085c8104905000782510805010000301104080fa01e070f00c0400c9002c1129032080003820306903031300d84070f80c0b41c10510b603c140301418040d405040841150b201454400320b040f2101120240460b122043c0d02582700e218212844815a001042c4500400041803401d41914042c0001e100b00c181c0d6500440d080c24048041d200041c20075040604c030502d01441341c88010380d11420000e0030624030030041640403050707980712108440b902d40000c08554030545005000d1100e41110520146103440202c0150004881d00c075402c1e04044010690621542d01c600071200164001e102100c0c0014505407141d201c0c180400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 275778174 1250 275776924 275776933
    0x60c110606011d03010207300206240d0803060906030610050d06060b030c0d060e0f07031509020c0c010201051b0714010204090501060c05010f0507120f060302030a050a03170705030c0c 81
    0xb0565900b8409405414002e4008984e1001561700a14601d002c0600c440000c10308001d12160b2260300141c69070b40598102e1100d095803031404904891001c1e0015500c0e403040c50006133508010749080514001c413030035100c03804142c440004042e1200405c544202920081c000c00700030520b03042c100c2301346e000e0249500040c950345860030210541d104480701401e030701e4000b6011080c05039910078036000740000d0885070058200a00b0041c0480c0000e0104000c260b201c40e1104c81184d8406c050100400f840181156128000390070315455201d03040c25103000d03529010002d0b038500701e12603031402e08074001c900361850300a103980d4001240c003c1c0002d80300f0380d640c02d110110780c0805c94401c4501803c40754950240200781403a0550a44a103024070300d1a05040c00c0510005c01d800c06001c13007201c1410800450074200e1100320800502d940c1d4006540345c403030781c410f0390b0901c40c0100701040b10a00a1b6140c605511109440803007643e0f0a07509200041c804000103000781c842913025000b0011084183c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 275779424 1250 275778174 275778227
    0x5090609090406050f070201110405010509060c15102106110c06041a160909110c0a150e0a170306010903050f010e07170307020f0a030b090a060c11060601 68
    0x1188450300b114210341c03c1d59590140106000540396196120b40940300074405050300400d2a017850103644206410700c400415401015500c04050b540088181e0f421582c070700c4440c503410000d090b82900c40d00c1d104400c9240110b11903070703900361594550182c1c51450350041d10f06c0d0340c1d01006051080101300001418084081c0c0214140401801035014064032444190003010040039000081c20058003016050700024005401c007181104403144400c002510b03210390641103560380b00d40840c5641c5800361100040c104001e000084d482d0f1111113074100941d805e0b50505a13036481d0405000f500c0f04c00c0d4101008101d900303040046510800624002e000980d0f25a141881c0030107030452208580d441e48103048403680e0400c807500082100c880e260380e807145016200740d1a8498210041c0c082ca007030b825000305507114143c0b207034000c2d5032020b0002c2c100d1030030000840c2c0720114803804030740d854181440000240e2042054030646100c5401911590300d0f050019a02504015040c44903501ea10004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 275780674 1250 275779424 275779429
    0x305040f03150b0405070206060910090f060801110a09030602071a0f04060b01093212030406030b0607110402070303110f040509130b0c03090c0409121b02090705090609 74
    0x804006600c02d040c1203108000c5200200191421200c04a00551404041143c201c1e8001041e80c4c014005884003038035901c0e0701d0100e4411403901d800c00600117041100b01c0000445540c0107000320707140c010003004845942d21034500c0c580700b191710100021356410000c0c400b20341664018004588144001540e44840b900100d405603c01c40c0c4c44450f42c418034081009000c51800340d091884424a40050308600740361644031030440c89210074500d15540102c04040708254544496111001440b10310303008030344083d40350340b907003e0b0060000180c10030150300780700d080900c1a202c8090b40114aa1180413190f818000203401401c8203504264940d01a0304907010306000034400030816100d4103603601d041c5014070041410182c0700711090b807040c01d40e0380c0100b825107120a400c401c494041940c0c94850740034481c43c1a07425007440398071a1034080d50404100320740c0e140500a40090300d0b48690500d030442024400c103a101d402941140941001900d4940300e2070060802d508001d000a0500c90000003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 275781924 1250 275780674 275780699
    0x40e070b031305070e1f08120705010e01111c0e060606090303070605010915240c03020a08041206050603030a0e1306030f062304050307021905030a06060e1806040807030504 76
    0x41101720140e05214411010207a010012001c0d0303100340303403c80e2804001542ea02092080301d1800c12000c00c9480401c01d081d0028601401e84c81c00a0100c034160081c0c5190380d505c6060004000d200e1551001c01900300d82c014982d101589101400d129500e5400303001ca2a800300441c9a810f002c10021000010518440c89010700718020300001c20700b07041180c240f103405158002d01046d00d20840916540c43c86001ca222101c40d807442d201601d0310306031600f079141014011006040c00004100031513085503d120030450341c0d0281405205a86441c02850f40341d21408024500103046122524010b042c4515025003c11800700009603031666a00c403140c42da07401301002c80d0002c0c0c503082e41c4503418101c0703042c40707101d22000c0208100324142652465641c0c410780500030b00a0f01c0d02160040d2680100120ba0001c140180680e0028549441c0210080040b030180d050311160700f1001c101d0701000b03100908801d1501900074001a202c07a03c6c0e061f12038002110031800c104e02040702190070f080c40c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 275783174 1250 275781924 275781929
    0x30e0a08010f0c030e010905030304020d0503090a080115050a062f1207021905010504031e0803042105090102070612021b0d020105220f02150c0a0b06040e070b03130507 74
    0xd80080e0b00c002c0403c1c01030035940a00680307016a8149900440400c10110441350001d03812141c404c82186140f40840c1940105070f0409c0e440401d1500010b032610041d002581d000d0700c3c6c4c802c0302043c0750b110b2040000031505806507900040c1105003a140c200f40200c18116103400607074109201d1060751400c149081c4034040c0b03009050b503010801d0303021400c04c0800d40c94411407481c884500c650414000078210701451001410030309408020045070f03012014a100c1c0f494010307148954920b420b0405d0804844d1800e070514005040b041d12807404c520420566807a960b05034090f0807243d14204c0120744888a501c070940401d90700b0032440e0100070100c4e100703015242e03091029000c0f44240c580064210388009141200f100502074035000c1801070242c4e502245640800c1c00c0030703908058000f1170500d240d03d4111042c0c07900e001648424410002840c103400601c100084010759841c0828001500c41115800b0075940c0101d03000c2c090854610040c6502c04981786000f04400300c00c0d12050324240007035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 275784424 1250 275783174 275783201
    0x1b21140103080723241b13030c23040c1e02120d05100e070905061c0504060b0f0303132702030106050a140909071d0301060b030f130b04030e0a0801 65
    0x1000012288803170310b000c0644185464840881460002c0000c40f0b800d8883c040003900031000207421011451031702107500a940c01c0b20311444120740707682204498491103552000901902d0010411528040c0111950b81241d80d8400d240c264201002018031940e041030503040d80640e0502480d0302d15010090100585c440e83c0102e550700700305030502c070b0030b2030503801c00d446184000003004505500072944404459080d217803140d07a00c0071403031199003051060306150300a07401c060901c000d0142c607030400002d1020440d40e08400f1000d0404240d03403849403090000f2594202c182c1000120510444403081d406074201c2c0c1005085a04c0920080364000d82203400802c5001c01d0171080c5035807010703255421021404140b40b40108210000d00800300c020649020080c880105007442240c9180002d10190094001c0c4891903e42c0c140e40c40641085600104100502c2d0000b89082212102a45c495030004900312003a2110341741141c1d400c5500148603008081c0b0074001a0001c400d102e00840911003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 275785674 1250 275784424 275784433
    0x6081b030f06120d1403071710031401060303090b030705040b03130b180a12110a050a02040c05040b070305090301020712030c170121061b21140103080723 68
    0x110410010143c1d80c040e629031540540d0040303c107150060018804a032a4a02064aa580e001000c54406051113900302002d00300328203000412001010201c1624070034404070071904400e02c1c080f42281c2052002070002002c069042180c1d01d1503100560b000880c0d46000c2e447c0903100c5014411540c0141c604442c0c083e402c00d1b00707100340458030403c01d8000e0814080c6800244165181c2ca946150003400a410001c40203013002d055800350b619030307860542100940707a103248142081c50310fa03031062405a004500741625034020303d12910480301902c0320500d196060820544040b52590861803446403d994200704480114640b0000d0f42c1c1c21000e00da42c00702e1082d07440c881c0104007088141806604000d505c0c0188810340740848800d0081640041001070044241090000b6029a54002e24080c41c040c8a511406074001403c01c00441d00802d0401c1c030041c03c401c1d820459038a02e4035000925080e00041c000038007070b0b07001412410701801465038945440090300716011907a08030707150142d11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 275786924 1250 275785674 275785681
    0xb1c140c030715110c0a06020d11010621050c13021804110a0315091a010206070c02030d0806040207060c09051801030b0c0c07030b070206100e1006081b030f 69
    0x14204440144200280d018142d194a00394102d680401c1e00300d04441804a80e610604892000b00079003010000300030407088006540ba200a501c0310550f5010000140001c2c52981003a14140121170480d0b07804caa0404c0015400d402460000803040f104858500514541003140d82e200c01d02480840458100140e64142c020001c0e0a41d4134901551400b40d41003030410a00044040280c4601c0080c0c0d05000c20784541024001d41054980d800254a40386002103044445100400350881c0c00000c0e000c48100b5102c02c502950802c03e1984001d40c150700180c05140d4640c49100003d40041003e840035052041d9503460380241d030910101302d0001a901e81c003c124915040400700500d035044205400c2c40d50560f01d030040308110051403140480300c00100102e100004011030402160044c0c0043c909007400c5000a440300000c1e100d840102c62107620220b20f05401c4040355010b00c420084e030311032092900c402902e034540000c180c0003080c510803110380a003204890085119040800201c402031a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 275788174 1250 275786924 275786963
    0x2070501080601021f0513020301020c0d030507051e0f04030807060902101b080f1201090c02060c0307052713090c08060601140d092103050a05070c02040b1c 69
    0x1000030071070707411035001a41da150b5170b922104500d411501035100c089502c1c0e4079201d580844c00c00580c0002d40643c40018881c0f200385000c5002c20045160f60b40a0001c1d0700c0d81c51013100c80d0b001d201c400c0340c00d550303100300d00818002035540140150741c041c58136541883c0d52a00d440f406904942401d4541a4480c40030f1011441c0206000360000e4132420700110941805940200042e5659001080e1045c0041c5100c22000c1000a0f59021000190505995030f100d00c0c51b2805814094421005441100c01040e1200e04034000c0d03a100b0986960303620308201c10661008180300c00c20901394a042c0c40102c0700c02e07446d120300004102ca005d0f49d00d8042545046480d04004602e043d9204240e6504800d0a000140ea4814881c40141604042e020344401e22001041e00034000c801005112401107580f0b01040c0c0384030a02c10b6149d01044d1400c1111350786100141e02526012180c020015040d5501c080040c81c2a0f4800a40ca04000d003803402e0702d02421440720441ea09201041e2031040b80b5010150820303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 275789424 1250 275788174 275788187
    0x10050a0c021f12050907060507140106030b0c07140d0c02040b0d140c0f030a0c05010f0504080106030f0b150f0607050111031003020a0801020a020a030509040b0918150129160302070501 81
    0x5e03442d001441c0d03c0740303003580050903401030607001001e141f1480901803454800b500300d003000e1500240141c10324189800e446485602541040b0f503403603240b85000c440c148011600e201c002c440c50f12303044c4c141c00860f800c10008043c00e030021944804042d003800089003040401000454602d40246445c41c25041084800c800c0d03030007440c1c803d4cc00f2204580001e030502c490001152800e0074104807850f44004181c0703490203250000301c0650b1038082c0000c1400449051440050301409405040d5222262070303400c3e009007150660780040c80140ca4000310b0502d00002d00400d4061303000054165403c0f42c1e00c8180380c5c01580c4403203260110030000e00946c90103101220041c40b1002c02180740140c9114041c1d12001c102d100170301030000108200307002d07480f01d8009250054004020980c9460486402629501c0786a900080380c4280001e80d0030499003401c0150594041e04c46c0080305070b081d8405201d100c081c3c0c5800000003a414000ea0717214404030082c5610091003600034140c2542003c0004121 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 275790674 1250 275789424 275789431
    0x4030e01020c030a020a03060209011103121b070c0b22090e0c0d03020d03051b0c01050703050610050306100309051c020610050f13020f040f08060610050a0c021f1205 73
    0xa03130001203204006030790b038100200032286e0010000d61038140d610016500c1c080b0f01140fa4995000010302c40b0720080800380c2c4544a09038070400c0000806013004164283c0c01413807001032440041400c1440400364100c06030011000c0304440d2060701c1c41520032070700310880c0b540c05800c1e10b0b61142c12064201c1010710000307540e20b2055a00400129017614020740d0f03642542e41c00000c0c1a950404280c203045820b0f54900302082c01a45203603201c11101a0900030a01150740d000041e10b8000400e00e14030340460080c010300ca059440c181140c40e580d007040415117030540520b040c5070352003482c100014014131540c002890b000c80c44d04c3d01000382003030290070104010664102811918810b02040d5a0000703c40f50904040d40d18048100420034810000c0c41001c4002000f44004940003801d07595602d5041c060b01c100c8003c4d121651107420520000c0000403e0f0f96001c102e0910446420320300c2b60386a1000139000924800c50104902490340c22108a503841e800000c9245500318a01001030103a180c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 275791924 1250 275790674 275790679
    0x10501020102030f071427030c04060815060d0203010608031804020316050a140d09051b0603010513060b040303050a0818100e1f0207033e011404030e01020c 69
    0x95890f05050405404d0001004031041c084c00811a88040250b402175400d1b595240940004881601c801210344030112042c0d43d1103442610fa413884613042c2406508100c1d484d0340010807540c4c0b040c08641c004e00354003c0482c3d402c10b603000d030ba082c090307030382405400d00030001c5001a5a4907084501104a81c3d084800d01074011801082404007424100340c0e40481c0440600d860b50b22400842c1c2e007107945004840c07079444665004a4101060b1980d07a2203041c03858401e4003101c007a00030201501404c0800420101e6010409000420207403e0001c03461465018030080003803d40d85541c41a145500f0a07041900010b101180041c05507403c0004141c0010050011036000b03048000c4203a42c8500e409010b488981d15160170a001c00c030104480e500d101c800100001218004940d20002500840419400540441c406c40c01260701261210f41601c0300c03440545452046030000e807820f40104500e20b04540d03890300c00c0c0c418608114500c40c000ca100703944007201c030304214000920304280c0390030380707803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 275793174 1250 275791924 275791927
    0x70303030905060109060515220602011d0f060c130305120a0305060d050a020f01030212150a1508060103180b070806030705010516020f012007090c030509190602040b0c1005010501020102 82
    0x1186654119074101550162802503949427400c0308818107111440c10002c940c24080c00d80440c0168064001440920741e01282c4a007010b49800801c2c1e558003c0142071203d500320802098000b89032200500d04a02c0d01000d2602150350f030341e612454034070080706005150301c012514140b01980360040c20340180c0c0450b035003480c1c40c0007920307640c1d1101d40244000344142c050010009a59019406555091512103486180c0340740c609900c401038a840304003036200e04050344021030794000600400400c48a20343d0750106650710400190000c152182d103881c00e040396000d43c2c01c002982e071401244a01030326501c40c105410104140b6240c0451504014148582440a610103a000c50001c401c0640c04590000c0400d030b900d0b00607141c448100c1045182255940c0c0b5092000e140001d404045a090070010802d21500d044110100c4030b05550490b0140c0008030001124940082902c01150160304011b2800d42d035403003a00050303440010f0b4540190003070010910b4500c00351248500400080c00250b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 275794424 1250 275793174 275793179
    0x10e0108120403031b020f030307060b040e0a0c0303081b0a020d09050603010605160807230d09030c030311151602300f16061d1203012607030303090506010906 70
    0x1c5c04400ca104585840c100703010404000399030710080c2035842c0ca68082d0503a03980b0003040c2000700c050f01c507049880c2e005078241421183c802000003070032040303284c100c03849140c01420340c0d40c1241c50300c0c40501038608020503440092604c00c0f40c07400501c0030004540050100c0003040d8005000902caa911180c45180284010803901d5000400c80780010803804074011070301030524017544503014040000e4607406015032482001d00090600e110ba5402079811688241d2100d90215291120ae0000402d525000e50341080000d0041101814058551003501d2035580400503051f06040c007101c21240a650740d03618000d03900d8043c0030604040410151a2a000202400008030010270400217a20002d00061000c520a9490191204014210360410380b030881d5003072080281c03032800c18990504500300002540420001160162610b850343e0490850307207000f0046510325210000c5c1d4003603010b401c0200c0000d80080c02444051071280c0c80025000003a41003c91070004c1c1600701d43da802c0d1400405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 275795674 1250 275794424 275794427
    0x12020f0406060219030504170a0c1a04151b050c12010209060a050a050c01020a0302042402060a0506150c010507020f160911040302130519090206070b041109010e010812040303 77
    0x1c00614902044545001020605d011545440346510407901000384202045480f072000c69000181e90080b54030a0036036444500e6916081d002d01c1203888008070400c010000030842090780075800d815810520307821810103024040c101c141480c1203900da04a880401d52516041180d0310220311080c008605001c481c5000c00c1d0288140e80c0c01005011011031440b640381c1c840c1c8200d46110300d03d40003d54a8107082c10018019400c2400340b200342c507205106030f0409001e0304082a00c95540d40c4c1c000d100d5600e5540115008040151480d034004014403c01070078000010010b21054020a00000b030610f8014002810400749082c5040540c01c4811078242e401001d400030800d6481c17086c80010f1200c400c81c8100c100d445641e20003034000005d030b4070f0301c008070740c0641c00070b48585882150001c0d001000c903818ac00312941301c41c00961260081c0503d60214810301841544144281c44007039001001000107100000c003680405403500d03141006120241c0140002c031607010242c2c1c045401d007415581c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 275796924 1250 275795674 275795683
    0x303021c090b0d02040f0f0311010807020a20060a120614030d120f0c02010c02010506090c2203060e0d0e03030a050d0f0609060602030d060b030103050c060d09060612020f04060602 79
    0x22102c005001007811109600541d044800400000d62040510303640c40801c0300c0440890700c000d46152000340300c0c1c0c2c031865004e1402648a065194080e00c1d14614a030341c4c41e400c848119031200c400014042403400c0c02e03180caa00a21041120f41c03541070602c44180d58000a0301c0711030308052400d1544402c0440e050b00c00095006c0c00c0300721810106089a64021004010024601003808450514541c0d84203180c042d0300c1444526910f90091289503101000e0100c2104255807a2400e22010810300700203401c211081103840740850303c0041d030786070f40340c0710305040e288002c501c04400c1d0055008920b00300d4020340c052704407010a40107142040c1040c2c2024029000d59039540502540301c0000036103030b001c079034461009018440300030454a900c5140081d96604009646c0c1306146c90701038081000b51700481903034101d0f076004004203000d803941e40603c1403642005d101d1607085921002c4410001c0d0351800703038602500d10209001c0340e80f1311500400852251200030315004510701101808200d03030118 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 275798174 1250 275796924 275796929
    0x703050703021002190803060111060f06100c02030a1a090c1c02040b0a0f080705030106080a030302210a0c0f05030f01030222050f1005060c0c0f06040306150303021c09 74
    0x80d001c000412099400b41d0403c0401030740405c48500303e40313685042114401c0550f000d01c00a0340d034401c1100c2a00ca000782e4a0500340e8041140594040011b152441d04000d0003440d9289843d14200f0f68a880d40442d00d803916418048800609030a2171340c100f030f0002d98015030301220344801440c41400300c0d404500a100c50807100241c41840520010554446800505c0040009007080080964944006032104201c0c01860400d006003480000e80f49014000d040c2504c0c883d0020f401c9003000c0356415802544004200f05e08004a5003d0710001400074048921074001000041124000c841005144059160b45141401000d206002d0085009210782e030549e0341c1a1000d080c5505400383c0c68040540030b4800b850490700f001c0c01c0000a0303520141441c00b4464040500364a161590100700c4980101403600141342c1c00246503180d1450002d0040c0d1060102411862a0907120b445800a0311030081141d00c6500d01006c0030800c040d03041155000b0041100c4c03082c6100101484020580c2c0000e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 275799424 1250 275798174 275798179
    0x16150e18190204120f0606120809190e09010f050c0301060c0f02060d1d06010b0f030a11280e0a21050f0303100303020f0a11010809210d050108070305070302 69
    0x100000050300000e0b90440d800751a806102180b14185450920711400480a04542c080e040c841d001070001640b40c451444c00c2d41c442d841608003c002024003e90300e10880b0b03441f05207000441c0005504e034085007801d00800060001003800d682e04218901607607005808882c140e0303000c02c01006615400005c01c84515801462006c0c54905400000e04074000c030f0305020020780ca000418410140c5460000f01e5008540702540e03056a0f03501c504002501805031009002e030010000141a17020550004000c00c2c0b04a4030300d030038410b100781c045031804983c141d04102c030004880c0c0c1c01c404640110b4a03030b0402c51f0030ac980b07594040c10a4810641070018410000d02c80c900c0c000d4010420206001d58161710a5034400c41e5220307d410b00f800300707000b00240301c1680503010340221300c80310b560041a4803103a2600200c0c10003244264600449241d500101200c070700740640000118900c1740c0340c0e00085c0443c00c400303143c8d4a603c4095220001c54006078031000303e550191070f0400014001103800d80480740c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 275800674 1250 275799424 275799451
    0x1030b03010f06170f0106050105090603091207080705010b0f010909090501061e150c020a051c060c0e03070504061d0c120a0f0c0206101716150e18 65
    0x19100424050001e440341c4903a81c0e0308180c80410045285210f070110903104e00700710b0328000e01000000e070032520907008440c00258100300c01c0302c00d42000d00040d5007010003a0100c414280400e0196010b5800c4440100c2d2103200000783c440900c1002d00558200460032100c0400099039800040d180000303c1c8501c0700500c2d100c9100006000007135000800500300044242c1d0b05507141c00740403c040556010303604002a001c0c204c1c0000d2482080c040701500c1d07000e070040c07070640c0c1420100a00c8142500c0c195040f038020506601c0021054000c51070841070645560f034401e0104001c143c10072800c1d4000a00461a203001007054444a103280400365000028190540c0c40f43d030700500c034030b10a0717075442d00040014400f8482e00441c00c3e8404807419500180400654152040890b16810250703600311440c0317941513003480588100a40401400780890448140c186995a4000410f08075400030801841040e01e15095a80008141c1d142c0c5600710703070003035079808481141d8100302c1026020400e09081d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 275801924 1250 275800674 275800691
    0xf0807120c09081b011b0c030f11031c02010b010e1e0d1406040204060b041212120c020c0a05010c0c09051906230303031003020d0f0c03050706030c0e06090103 70
    0x40b082038000c3c00700e01040d0389440ca000c181c5100080b40200225000a160039500c1c074250f041c2c0303a80141c01e00d40c8600314510561440c0c84011113502090380907100100d5218184045540411440c8204040c29640c2a41004580b4000c2d0071a00000c03001c605100b114041202c00350f484289802c1d030700072811051038a0340d0315840401c083e80c0c018403000f0b0580c00c0340200e0610b0f040e07000901501c0745108450511056807142035154860040d841803000502c10b000032400003401c40d81101400d0261480c10490301e40000000000b521850032200300540c208002c03c50480c01c201e040040604400e08060001c07400913a2a0b000c00049841200d0030f443e5240302255401010103084114455a000140102e40d112400c00243c03845044d500340498820202d807621a0401100707a07480b8420240200f44543d18580034072500c1000200c086502143c0c1c41e0010000516840d9483d019501480040c400c1e50701341500030341180c51110111007072100c80d20b2a044a9515074040b00e031951420b18010812a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 275803174 1250 275801924 275801927
    0x2030406060305030f280f080702210d050108012c07030203100c121104050411040e09010204080d020109020a141207061d010e0a12020d0b13030f0807120c 68
    0x450b080180107010001d15065040300003405800390300d041000c0242c410b0b5000041c00442c2100028802c0800c450300307803a400d00e90003013951542c0208140140c42080800b444c01d2520360850425410034600c000c641d0148462443c8101400740215000800001c0b101c411000c0103c01500000e400e2640402c0103031704903039002d00a5100071a80038045640e5031122000d400d001d054607074442c1000503101c1c0000c852038461783c02003181c11441124410720741070034201404054251054040c0d00c00904210008801e540360040c14461032440c1c0c00141c1b91030a00d0040d9041042240d004821a81451030950159035540c035548112135500d00f41c841100c401d8008a0700e000340d0b0081190701030050f6140020165008000c155030303c01d03007448030524041030900640d5680407440c2e01517000002d04605020300f6130403202100b15217000402d007012116007545c0d50724400c2022250229803600c0020390000701030300300040351980c1030310f418801040d1520701c0009044901d20112440955150f40d00400000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 275804424 1250 275803174 275803181
    0x8031003150506010e06120403080a090507030b091e15131202010509060604020a0206010b1803030f0405041109030307110f04090b04020a1d0a09020418031e050c03090402030406 78
    0x159030141e40d03000c10398205500d2800602d0110b8606012400e04200b03d0b0951504500303d8508040000420b986503d5944040b43e840c0802419003030519616000c1c0000b01c0d00410603c40154412140007402d890b01060403400c01030140f0300c041681c0e040c03803c00021041e02080c10700d001c1d419440c10f4129681c0301c5024840d0304032481c0c1d010702000940c4540140c020f6040d00858456101c0904032021350f01d80c034080c0000c9210389481400180c0140c401442551081801807140300c0b4881c00304041160b07002c0010f81940e1018a8078149200002001c005909050142d805035400750b0384205d051407490f4000ca600d900c00c2c450020400c10b40041c90032500d40d0b132580e0382880941c002d88100f010040034504000d504070203542c160311958012030005001c050008005080c4501c00c9103001403900d0702030200740a440388500481c0e000e502c48040c0480c00d45004041c040440c000e6603404c900c0703128403000c6c80c5225086a500c1c0f0403c03004010344030b041031000040f6501101c0c259030040e41c9680318240311004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 275805674 1250 275804424 275804429
    0x30509030c130e1b010203090409020a030b010b0c06010501020106060c03080403030e030c010e011103070c08032508070e09220f05010c050304120f0903030f0215010303021014060904080310 83
    0x888880c81c2880d01036143d52000083d622001c0c103d032826480d500c6103102c2d21400802c0b07140180c0c01000b03618018185600140130142c40581880710040c3c983d81ca48203c2d4a00b60089421640d0115040c081c454040006900421081c0001c00031a4100040100f40700c8407100098207002c0c0780070110b01014803940c01900490501f10a0f00d445084841506029083c1204c0800d010b609080164542948400441e4041c101c541c0302c010003d021942c0d224541e810060210800d600f410f0f40d0001410414900132a49650b0341da030f55403031460315001c042d2402d07084008090140c04888100070b4100c050800e0003280c035800c4032034400b4001d482d10f030422500c80703a640006c00c25400c16169541464100c030265002d02d110303010602d0340e81e0003144100c0f18542c0950035a00014008841000442e0081d02421300c0320102e48140c501c1d60940001082003840280d0040703006a003c1030500c540e60b10107100b108628080d0008050302c2e0f09100e00018401c48014001520072280000480e041040d00b1207003d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 275806924 1250 275805674 275805679
    0x50a150c021201050105030d09050a060807051303030f090b120c03180a1b120c0303030b0a0e190e0c0109180b03150109050106080103080703081b0f041d0c07030509030c 74
    0x640c8582c200c4424040c05003840341c580644100c541d6802043d0280f40101e05903000506108000c030319000342202e440b10054200713014020300300710540044c19050b181c0700107140280c494280340786030b070440102519220381c441c3d0001716007842400d1f444c040b030b034804da034028000e80b000d2030300da0700c80c0030011000740e100701494401c906c1070001c0c800400058060100071000721824401c030055445071a02e43c100700c01c94005100c40100384051000074003a07489820340d0701c409000524125140c4282600900f408d44901d21a10b101d00c4864030000c1c2c0c0c500501d050f41443c0c501500503410004c0c00601101900c1c01010b0280080c1c3c0c4004290b0f010039801004005401400c6130b035000350a0a100c890b803030b820b0140010040c102030011603654005d90701103049039401081e0034580641c9890072110242e0140c140e412600d1000000c2e0f070f2461005001c0d0200307a40712100903568910b0070081030b0807044403354000c2c0301c120400800c241d40c8a1042950038041d014207255681d03241c000000380c10103c0c000e00c45039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 275808174 1250 275806924 275806939
    0x150c02030c07081e151f0f14091f03020603130803070f0f080606030a020306030708071d1b0a0c05030c0703060b090702010504080301050d02040f0203091c09050a150c02 74
    0x3011440003814443ca0f4000304404c1389022104414541c079602e040100b0030488904030f01044541ca2420402107800710300c2140c4070012519050102990030303440e0720208180c401c66901c04203c1c60b1071b40b2115048042b1411440d50201b4550088194115a100c00703849500d0100024940350001ca02d00038545d540a003580e90b41340b034031513805044441c00352044000120013400f2078003282d024508041c040c0c0401019241035544034201400030358801411107405006009000480c080f0400054000c0c2c01d00e1031400d491141069000001103000400b428800309134502a10301003e01d80040b540100600d1030008112991810302902c2c6100b4410847c41c1481816000021f02c4000e50280250750012684000641c8030036004a09031803060718050315500c7e040004001c14a050302d0668072072880500081001c070107103410740040740c000301c4401401390011700c500102c80d004502c1c000c03811002804d0084a035824413000c12041c40c41402510306040c50318000d034034080e02404018007525401040786 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 275809424 1250 275808174 275808179
    0x4050c130912030e06010602030c031b0124051513051504030b160807450306020315090f072006090706020c04110d0c0c0f0501060e0a0207150c02030c07 67
    0x40050040b04e90684c4540251000400c82510120890300c1c030042c40001103061680150032850140313a1204014075640d0b940104075118503103503034040c0003d05000d824041380c61800c0184000c004001c450002c0b081c00411034104120040d007840b80545405a403e200240600150500c09201d40c0e0005481041041c080000d5041012035411548249980f04c6690783c50b6040300307945d015695916444031500040700703006051700c0d20845105000204885400c000180480701c98070040c541c0080d9901d540000400200101c04901460140f03810b84038111700e07140c5544016500d001c0a4441410011141ca203182043d2007040034440f40000801a83c3c024100320000c1035540b01648659005070244070480000c0c1c3ca020301ca40310030719041d03d554600e481401e0380c0b520001d08100b080f40302800f5181a001b8081490041a2013101e88503074000500030b4102040340500050040565400078010098000040c0e6500b04030003103081324104c08503040c101c1c1c40040e8114042c91300d4844603442002c100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 275810674 1250 275809424 275809427
    0x9041805011e060326041d0103170301030b0c2a0a0302010b0301060b0d0e010e01020313110d0206040512011b0f030510030507170726060a0504050c130912 68
    0x14003095140c1682c8184070140b80da2990705941c00343c44090010300c40709510459800601e40e02c24030012448200078034181c2c0300d4054440311a61a205550103114400051081001c10100b6a200c0d005114083c0d0443d851a03403114609100240020403003c03010608020040f400042c184421505040d4400643e42c200b20646e920324002c4030550042d8203000100000303040611840e0140d5040405540c50030403a000d01c440a02668400c044540d90307180d004c103003244028030141d80a2014018612180f20081c00c020420546040c2c0e500d21403515001d030900141c0e1103000b107130119142642d01218803c0016001c0303005010707c40040007158000445c0e4854140c1c401da200c5682605900e041010f0f44030341c00c42406600541c0401002c079408500e06014241c400c0741c2000f018400c26003107418460711884074540040c15210305503400d10114101c89088031041c419641c2c0004507400030022441c054840541c1c0f142101c40160084018003070700c0400b0503640d00301c00b4284e6001002c040e15804007110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 275811924 1250 275810674 275810681
    0x3160c05030d05190c020c01030207020d0b01061110020a05031b1207081b1c0b1203070807031e0c1104020409090b0a0c050f0d110702040e010b10030209090c0904180501 74
    0x111011820031111301d03941540560b125045c000e02c1c5990040010034469030054000358041038043c3d92240c80c10f9000b00001c0c0d40ea90210f40a0b00e26903486906242088540324a8a683c0305442c0c0351082c0144034000c616903000701a06d900c800120301210312a03180c80300703510711480788000401e4901540030030011019002500c19010f000c0705109040651981800300400c1d0040582d902600185580300c0340400c90786411212032400c008000d8014104100111851075000700300c01c840106021914809154000f05100e0048080c0012044191a103940040200a000714014044180d01d4105201c540702d0b0b6040e100640f144160412a0000505048640600031035000e620b00d4104140c2c2c9502d140320f0002d07100c064034940c4100d814602e400010001805c0101c0f254411284144000400340e0303604c0c040e8560340d5140b180001840b00420040c44050030340c0c2701450702070500403c04c08249442d483c2a1a901403140c240f0350b62a0819000060b010302440705012020b84445c28601091010661 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 275813174 1250 275811924 275811931
    0x705060402311d0c0d200604030f06051b03040b0405012d050601050703080a0504030509041103040c050a080d030509101b030c08040c03020405040320070f09020f03160c05030d05 78
    0x1801c0b070300f2000e1428655a203103900c1c46815000001400301000046240761107910a00741120103440103170b94080442d409030070581c815070700f100a02c090070081c0840e52041942001a000b04040905c50034030780e0485501c00a0402031074040c8000c000b40521500303500429528841e5103144910780000b12208181c00c0483c241d07403250b10b20704408903c00d50701841c02c4410081d85030711004415954426142d000382030060056040c050200450070b4240c1c1ca038402c103072148400210458480c10710341005200b01c011600103e02482c042c1c1000e0000c100009550b82000300c207458085425078449104030300b4a00c0205c05405c0950074035036828248100911400811902540d08004018020702c0441e001034040d28054050511903a00b4405800c00c0d40102da03006000381000503040001400c521207600c542030000d542038211041c107001c2102c204c842000201002c1e40c00b542040706029100c20a48000b1702052402492001c0081290f07024031000c0e04025001802c2e01c1d203e0074a001c00001401040303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 275814424 1250 275813174 275813201
    0xb120d021209031906060905010902070b0f01140409030315060c150204030201202b022b030506180a0506120a170a0504170d080903070506040231 64
    0xe81400d030141c0003800648200050007001460440c0c00f00003104100188007030242c0700180c546801041e045180d0007441c1c000c0c010ba610040c2e841e503d42c1018501208050952401d0152440040100002220210760f190800315400502580f40345400c0d0018106403000300c0c543c10b00c030b07100042c0e2680c0041c44518140c1c080d0300030158051044000800720301c55030000034040342149142d80304c120030b00c40e00c000e01300368154100da80520801640e030100c0c24100390100b400791040d4a4000d402603061281849038040c05100c00320b1901801c0c8600b56a0b04822a50b104260f0f540000171036640d6000f809020142004802e1030690074001c1000c0301400c402c542070390040702018800107003058000b5140034200c2d0040300192081d048a034405c051980001900810440e09000c0800c6042e042044036032075801500051200b00783e5880042e1444900920740d030000c4c2c2062000c0d40102d803001c6040d40d0710550440350600d42c0f000d40c4101260b00342c2100e2601c0c50403124100704481e480c00a07800480c6032800d9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 275815674 1250 275814424 275814433
    0x2040209060c07181808030a020319020c10061e3005070305060c030601022517030702030105070903020303040e271e1c05030a0b090910050c070215090102010b120d02 73
    0xc0b10f91000154512042c02041301b03804200150241c41079501864000004c3c200c0f661000707581d2134461050f42c0001011300c0480c3c0103c66003415040c024852000100038070007408403081915500410700381f0702841164640301c01d103110700100844200001105015500381082000d46509103a65600301c40d01080b030301446039801180d10369040c034060f00d1089205074024440360342c0724025003858071500b41e52400c10550004c40858500040e14844c13030130303c2c8004011a1512040d004060a40f14050402424089503000500140c0c8000c011141039035407150741d441680e1602c90700720010085408010240402d000030360000c0c0d03400450150941c9038400c0c803071101d4044a66410362104801001004440320f0000000d200900501c040c691040c00c5600020303403000504081090110100d075400d2103500a80343e204002d2546220b0399420030b221503465410b00d003840d07001c500c41e0b000d20106159445404141940d25a200f50003c510703544e405850314904035001d0200e9941c2e4524554220050300a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 275816924 1250 275815674 275815691
    0x30b031507110f0c0d03030f090203100e120705030a050a020705090a0615020c100f1106070915230d090c0b180105130506090102030c070b0a1b020d02040209060c0718 73
    0x10001103d0640130002010742c3c05a6107161b5059000b0000350a450b640c264403070b06420701584d4280421380c4421031815001c544200084034a606002034959080d2543c04140101d4020440010541c2c40100503806c0683d43d03119141d20030b03442c0410f02e40c4882d90041303000b42006648805d03a0402c000710f40104d40c032580c4c0401140000d9849210110b00507410201c0d03110b0291180d8418555220803050300c0c1090303d005d940300084941850303000c0310028042410715a0400150f98402103414081102c6e190000d196504508040d20b0100e8a05460b40c01c0708021508481c11500b03640132401c195404003c0c0050343da96220284c0c0c507500002042d02d1680952510700c007441d401401140d950306c09074101010701509110070007c29070010603400d41188024402c0e040c4d0380d001041108050001484900d44440a01e00c00070308001d200307440b42e00038681c0c00a02c10016107a08900c111544c1e4115005a26003104001087c10390041c04442051481407400c001070418040d40e001c10021003000c818400e001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 275818174 1250 275816924 275816953
    0x91217490c0c0638010f0203030c03070f1e021606110a1e0b07090302310515100503150306220501230a060e010b0a030b03150711 57
    0x2226103101a0215503040ca145002409540c4000780a50004101304004030b000c100c900b00b10950b00710814225250600407802942c0c104100c1c0b0303072540d03443c40110720718503100300070003641d020150001e4140714085800416560144844005600c002c90070072600c4c80d00b40900030350f2264079004680071200580c8001c1240d502c41d91045140324056401440c100015649000101c0142482100b00c0102c0740100800180512104c0b40a00943d9a41000181c190300410140b043c0110011061503c071030014010050100000000c5c0010290b002039543c2e030f0700385010074140445400755402801c80710b4007a401500b0002542c01002900010300e5404450000c0c903a585130240d03500e40e001d02508180ca4201000380710300024032031085c000461000071007182c101e807400500c02c020110044c01e01c00c0103100c00741881000000d20000c944003641c0e524068596071b04d4031841c1ea1250405171070318407c0009850411404c8881c1c8884100e54810749000100186100d10200c04824540603100286c44d000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 275819424 1250 275818174 275818181
    0xb01080313062f0604030806030303040308060904030e061306031104290408060c03090c0a0303081b1b0f120403020906010503130b040506060109121749 67
    0x828845000364031690400809441509603121004103070000f0003000c00002107100001d21101030440c2c0108011306040c6805007000e1001404107000768000d108100100703a00204480c0c0081050742d0f24503041e1140c0c03c0c102e13000e080c020600c41e0001c500082285c0002d4601c51140211041c95508008a02e5041600c00309403241d07115010020540c4101c01c00d030744c0040543c00c4103241c100c820440c507007541c036001c040c1070410031504401105d101100300413240c5001c1c844a04108800c6070022941421642d01a1036880060608540e031180790011240d601d03460001c40d41c0c4141308102e207485840c10f51000550b14001021a103149004507401081d0703002d94442503509407a4000c103000c90940e1400300440d42c58200400001c2000d00303242d2140c0200b03c240c3e45090007180100d01601c84d52800400140200820383e121304212a100b900040210300200680d600121707005101c10796a03003901090001041c03503030640c95203501c82c6201c10f00e10310842102140d0341c8180c03070784010340d6030742c0340b00307595046 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 275820674 1250 275819424 275819437
    0x60a14010803221503050106090905090a1104230405150f0609061807170c09030307060504030302040815010f510e04110412110109210b010803 63
    0x9a50050240c075602c0001c0d8042c20402e030401d03904050000d0744da6040b40000a06000211000c20340d42d8006200c515800180c031400381c5091101030066090481055545200c0c520001e014507a0810003510b480d61141c000c1e001e08220003003ca0081005800c0d1a1215001600c00302c0340c51182e80d80040382001e20341d011920074400d621103080130359200c03030510000380401804541d01481d81e030120b841600d00d8500c614003403403d59544c072007494001d041142105a0140000705110418455040c040e0341c00000c075800c00d580000041059116854254064080c9403c00705c418020105404204130500c0d080394103e544a1901455040e50f510744043d072201812100c40256602c869a0038020402d04551180311749101d41040c1d5000300f400d00c001c030103010418410009044021700c4030080c6803038083c56411096448501d49028034108000d00c1c41424418004d018032080c1408002ca40e020f50312102c014440c1c454684c0c00703a019200462409440301400b103a00b17006400c0041006a00001034a44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 275821924 1250 275820674 275820689
    0xb0a091404030f090308031509070e13090c09110a12050112020f01412506020702030d0302030402040c021c030f02090604030c06140a140c011409060a1401 68
    0x31240c403151411641d01c500150300c0018021034100000000d40b4003801544240c1c18070f4680c101c1c1c1200b840c00c10194078405800300040040124144039259240c0042000040ca001000500408149007440c02400c45a000c0d000c04e524002c01048410202401410f410302d0903903644c450781080480f0303201100e90a011304901400520030724001400d186904e040803d005044c04002c18856403203040541942012201000410f09130240251034541d90301179000114101d80c908262040f900403050751100000121200b502c02c0400d8240940ca504a03503880d50080c0544460007103008024001e0740c02038400f00e0181d0325015940005901c0841c11080c855010b00c09081c0c104940075085000d01820301801403600c1e82005000d2607a0b4502c00200000e522a90030072482c1031070407101501d440d81104080c41115420050000840d50000f000610788034007130101d44d00d41c140703440f1081c010080d2445a03024854580180a1403550014603207108419403103050114140c2c0040011400b0b00078820781c80b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 275823174 1250 275821924 275821961
    0x12100e0706180b1b100c020d051804020901050c0609060105120a031403191d06010b04210f0f03110606010306050105030a1a0604090f0516050a110316060b0a09 70
    0x800031a5210003050b000712a200c0b49001131243e0700036207007810581c51407038000e10b03a58003550916540601c8448025641c07400e0031400d04610800910401801c80341251190b6400130304440107078052001e0f141c0002e0190304403500d500d011605103544d0482030040910030403042455406004000030218151903260f81e0302450180c2c142c0311030100307030000750040d14034540b420407000800502e03215003400071503a0f107450740742d030491040010300349201030b00322240b504410841400804003481444114204e090b0071800103450703a00b00f48010117246400144507082d0744203c00d05040d030112000c2c1d0384151440581c0c440e601c8190055085900030304c10746010600c140006489640f6542c4040384800c11070081c0c450748281c00d000a405a80150052148913644c0d1001c0d00c9545c0203446038039070150090008048200c41603001405501481c94044c040000130001014050000e00079140c0e0303501c91700222071204405d850700e070000d000d580c07916038061b6814000000f00d065403030068424400c6078080c200e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 275824424 1250 275823174 275823179
    0x40b0a02070b090d0b180f0105010509071806050c030f030c030405070501050c0a06050a020c01090302033606070507050a140915090c130e070305040201020f0604080f0912100e070618 80
    0x40c1552070000c5c81b416401c240c01c0740110000c0001e20081c1c40d058a12000000c0300d41c14207042115003840584840100400c0d245c00c4403043e5050000760091700c5c0c2d1428020345450b0100c16003031031481010f4040784480004424410000e03070240246010700d1290060b43e02c16501c4600444007801200d080d006158401419080030422a500480c2c100131b21000152622015010701402c0d00c00215084005a01c001044030104000e5070031040d4005444038040250301d04030700544504512010041d209900002d100030800008001c0b070001841d000d001b141c601d83d0b54403c1c0c01c000c009800241c6000301e250f640041c0c242000e10100703498103540100041c071503407107c256203c403e0b0021800180902c031507034408240409801071442c03052016560103c1d043c0380a100090030840d1407040d440882d401034003400f0000b2200c2e019298032809440c10203480c4e00d044400203007003c07481d8064103104c0c0600e151015a07880d00f500f110b44400100b40484001c5995220204c0e942242c401c43c4c801000d02180b000e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 275825674 1250 275824424 275824433
    0x607140a030b03011b0203030121110108060102100c05130f0b0a05090d0b1504060801020a211e0e010e060403020c040203070c2301060501020f0312070c08040b0a02070b090d 76
    0x30318440b5400b4000107401800248516050359060102c000036901c040700402004c01d52041d4030000400348204d0b080c1d052110b82d21205020008207005060003034080008603143d02c01c2050b03080b490400107052042c4494020040d007242e00c10b504818007603007031490110b101003030020320504503046a00d41e02c1c6480102c3c2001c4072650040b42c9203035409414446a80302240c40a4095802b501c200b000f1161560a400c04000c02c45840740d2141c680c5034014012841b00a420501c3d211400a10b81461b0840e0050010b01c0030041c10396081c5a5000c020f01466084501090f03440780c10b420640340000c10181c1d02540c0e045030364090480b0f004006900c0801c5803555401d09802541e00040203050810300c810701399079860804042c201e1001c00d071a1020b281d9140280d402d000310001440c4c03c0c0054090741d51101c009e1903c80c482d00c08448a407007111800318031040d100c0c072142c100e5070b0f401004081e101c9450365905d140542c8a000381d0390046c030a02e0400f0920305164412202a0800105070100ca91029980c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 275826924 1250 275825674 275825681
    0x1409090103170408161e051c05030d0603050102090406080a0b04080a050d0501090c0210061409040203071502100b010f121a0a09020a26010501050f160b090607140a03 73
    0x4800b168400207001c00034050b02c040010f01c2c100400e8501841c00c0d14102441c0e0904216182e0980303280d62200c5030300700b04607122201c20300c549030401c542079560f2103541d04000d07246100e03240f002c0003540d18006c0004144581075000e8000720404840078002240d488031440e541d52503500c0060803926003a0302240010b400c0b01e00030724901e00542007075810301d003031450444100c907003d03840340308015100c0302204804e41d410311103400710051001c81040032600740441c0324800c1c1001036905000e0418030010400755541042900000d0400191302d89a00c0340182009482d4441c3c641000d43c0345040116891066004815800c40e00c4040d5444084c4461000300c0c141c081c0040381d03800e001100310103148400d540c40f280011405440d81020260b40e0b44a403410091000e00040641d20300850054000301044218040c0c803411a0000d180281e220b0440f281d002e8800c1c441d0000025648802030001c07002c211b00d800d06a40b04240d668161410355968010551350507800c00862540d24504022107000705000c2d0b132 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 275828174 1250 275826924 275826953
    0x50613140d051b01060806150a030c0b041a160609060912080108070509090a0605062205071409030723060c1605012d0c0b1302011409090103 62
    0x20450310001084000d041281d40d00380000041e80024044407010740c40c821034114000050001c118135480c100500381c690401500030050701000754004c201607036580507403001460b0030a050b074407120750390070f12524654000e02c1074804c07000d0084000c0740b420f9505c1082d2030212042c001d1087c040b000c26542c0e0001014010011100c20f681e030b01e0707200b0102d010340c11000c8a0341131030f4654840f95410600c08514058841d0710880c46210440d040101803d80421880d0050341d21035400b15040d11444000303004e0341650408a2800310003188202154622500010300032036448e1141700c10440402c0c2d440016105410030744c0e4040e4440c0b4020031030f02c101d200000000c04680b4640034181e556050000760540c1c080300984100750300c404c5000801c01740c4081c1d600002e02003400c1c0284405600000d445130909558001189110740b82e68400c0d0702030044514900c1c0c0d40e80720503c42294501186c0400401d801c01106a0000314824586d42029049101701c4030340c030f100101803140303d0380b03035584603c1601c4105c13 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 275829424 1250 275828174 275828183
    0x405010e031c030b040f1a04060f06091a16030201060315091a06040b0301090b04020405060d021509150d14070e06250506160e0303180910171f09050613 67
    0x34100e0003001d00c0da5100c1e010a0104000b81e21000680240405c42039031241d400c101700c4540c1c0c4c0030703040200c036070860305440c02c994a5244482d0400c07840390080683b0700503082c402c2d60040042c44424100342d810f60104041e6442040c80c3c00240c44600b603500e00f05c40309071500409031064484075104026100312100e6015000500202d0b51003245004030f400e4400031101220480e4481060108515260150a03030007041900c18110b60095900000c00c80e1110290606c4849400a806441d64903408a044110b07c1481c44140e80c41c252031480740e0050201010301341c8080440001710380381c5031103000e0188271074900510180c1007c0a8035180e0102d40030410983c44000014558280054014443c40e84509000c01070007100010041c0080c0090700c44070780081c82a08100001e4140c0c110242400e00d000b0000da0b084035a503550361807010429085500001890504001d15140c02a0002942d1015002e083da95844041c0d0b00101e850071340d950443c5c0101a0303008040001d24a141c00c511084185018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 275830674 1250 275829424 275829431
    0x6080a0f06151d060708030c0c010902030a080712080903090f030c1203070308160906081f030809011202070c122103050406050903120402150c120405010e031c030b04 73
    0x80c2c142c5142103458070348011022078103104810702c0320325000e41c9021a0b403001352255480c10136159110b0301d0600c0010000c60302c03c0004120702103102e20035404000c141d54080c00300e81d508036550915456603006260110359050f6409a400c4982e80700c0c908042c0a00c036448001c5080012a00400c0001901c03905880c0d01071141d0362a042165503059014440850700c8005140e03141c51906006001a50051020241e502048032030480e0a40c0024418111103d40c645050b05440c1c10585846c10003443c00b03010034020480e01d000c014444180d000f021645803d032228407144034400001001d900482c00003620651020f182000b885615100440380303144100304484a000b031340d10171404810185180c01c000240d4070010002008102e105590f00192008021410005017030b007070900348080140001e00400c0c0e9402062484200d00b000c1c0d544990300e0a054075404070000003102c0c2c541e00140300b03860000e120340840080c68100821401c0380c420901d1410720b100682e4003020380c013500491440c1a0850341c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 275831924 1250 275830674 275830679
    0x5131d010510110115060e2704031e11070f0305030d0c02070503030c2802060901030f0e0102160b07080705040608040c050d030302090a08010204050607110d02030f2506080a0f06 78
    0x1000c0c0304030380d250b807100040e9240050502e10000c02c510050440306014412480448098800583c0844604001c50901260382d40c0c9910b4120740c500340420b2017101c2110f240000d02c0030349402c900c0c0902c0cc1000c6501701c9030040e50b035800450490300c0c14800035040b40c0003008080421030140e000401f10380f1a500449401594a0002c20701d194407007002d6443c41e8000003465050070010301040c2c0f0803901600002c00310b01e0001c4d00090020b114421113141070540c2c400c100d410b042280e03000143c160038900000c40d22a000b04001662020803801d0031a103a0062000051115000d4510140071b40300a580780360400381892015245c6110103803060f034070141c100c0c4001a1310365480c1028039517035100c0c1e98096210b0300f0500601951000a030400200c5034010b21090005890310001d990103e500500d542094603240750208031864841f0802942601441c40c0039100c1040000301c0c2034003400071100b118110b0505400c900701541d0350b80a0381001404ca032004c6070748807a40385c10404043c0c147c810001078a91303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 275833174 1250 275831924 275831957
    0xe030c03070f1a040b040b031b0318060603010e150c19050414010f020c06070201030608010203010305030721020a0201200d0e03070e0c0f03040510060605131d010510 73
    0x1c10607072042e201e4050402c801d00030340c03110045010407101c41041035401c2c9410f21401401c140202d0289000614001c0300256294014001c0103842204a2000d60350780c0c10450a00e080e19100e00f202d0142902c94800801c03013a00b01485503200341111a0050a51454800485490f080011381907500c004001c1c008250741c2c540c110306103a81c0344403d4031001d581e2071030401110b0229684408140c1803001081b100c0c80c56507000f0690a19109049030142d0faa4009403005030024104d507000200150b20120010040020000042110034021074041c01221104440803000c0c400304900a801604600510070065014061032030004800444400c080c40000350f03450303c0d040d001621071001420090784152070303050a21405000d0079280d00c2001981c1781070b014000c075520441602440c020000030001e8248042403207c500c01e20300c1d445090141e81d56070407004203940c200024141400c40b4401d000224100e008980620003604a01c40e00c009078680780c10803881d03240fa04070305414040000005403101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 275834424 1250 275833174 275833183
    0x2030403050609011b020c0d11040e030c0f2802010e010c02090403030902120a03020c1203120106120605090105090a0e030c010c09080610060c120c1a09010b011d010e030c03 76
    0x180e0703e0394000030303611000704c0e03e50280480c2d1015810944d00308085074611902d42c040c90f120810740040041c00841207600c0404c000742040c60f86402d80e4000483c00141c0c842000c140000324400c1042154180851021a000f00c3c04a1014000401e2812441c440040d400b1301000c0c00c20310014142251222025000702e00d11a4049a048000a590b079041c4021031802d2480c01c040c00c00d001000344030a08a5640203541c0c0c41d00303104044d105e2002070030200b0440c7c3c000c008982580341c01840c080155691003c02612200c11080001002d908284020805080058005049900003400046242c030381c9015000142412401c03118035010812052150740e400f405001c003466090380d11007a0852034500654103082c0043c003110700800c21fa4008001555004800049160708100c82a8143c0c044040039541c18012400003044042d00d80d182c0c3d609203e0325410103110322000d2000f031102c490501c3c011a541031100006451492480c00d480301c03903521503006070000f50009011160300b0617130304001900d003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 275835674 1250 275834424 275834431
    0x324040605040f020a030f05130f021f050d0f09020a050105070c090507020a03020c060c150c070b0f0103020103201b010603080d020c0706020c0306060103050705090405090c01030608070e04060c020304030506 91
    0x1030f940c0016841005550510601e002a20151701c100320604000c000c1c0c20380c3d00d00698000e809030001004100940da50842caa0200d001c109070006c0011400318406802c54015449401d8501d1804100c10040140360080c105950360040c0700040e41070500380151078a8001d0720040e034100d0116200410151410b01c203081c05083c85d600101030b100c7c500d1a0080c5001040602d0b03d004220900240f441080006004480c10030203072440d0b1aa5550100485c0c8d41e0701034042c004d8070007030203a03040c4400c1114804c4042c0c1680e000f03980500100041140721414030141d40c4416818980c20040c43c100c080030404102d440644000011030526580d482e55039268005040e007209603640040c2c0e80003142d108000c1d410040030b16002030400f503c45040042d4403a440200301e1414140c4400c00203403103900c641c0403a900003070010000c001c40d003041c504803655124500000350102e490b01102064852001410400302c0b50495800c8000d507841c2c4d03030f45c031003c0d00e55888010f0962000f0302c80800000c009024840c030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 275836924 1250 275835674 275835701
    0x60c0f0c010b0a0e0a540b011a130501031e0509012a0903060c0309051608071403060402120a0f150b040c020604140c030709021e032404060504 63
    0x407030501c290840304451b00c0c0309141192001e102840599280180d209032003521442c80d88040c00c0c507001c034004d4001c170700202000c110306000240720410419a000c81c1d40c161440d410800c0120750440c202070600e48110010110001110760041000750b2182c0c00c11002c9020312049864042910290b02055034002c0e2019050b030b0351164038418001074043c40b9030820043c00d42103c460550040380c0134103a4842400060300003a141c44040161500940000c0b17407103907000c0d00716a01d107045054501a0b02519001d000741d9030103440c20001d020b981d00f9081502564000b8042c01c0d5a848503400c016520a9003d000c024a02801e181e0802007542c3c40070004100c1e00815444020342664a80c0c481107501f0100110710407031030000800c4d50281c0c0003507055442540303e81c0070b403e024030303091245240180842d0740541c9032040c00e0010500ca6407580180206000c442560340171203034411000001c9002c00c69a12a1490920864038142c207800940309045a00c00361000a5150b00e40300400c0c240c03100c5920300c05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 275838174 1250 275836924 275836949
    0x21506061909150512010e1e0108030703030506010f0228080c160b0708030403080603072d120f08072604080d09060930030c050708060c0f0c010b0a 65
    0x8500216100320650f40c8051038500d25210011816012200e4180035501c0640d4690002640c00c00b1000b1805411011400030b45982d503030340b0f15180d680c0c0d5001c001c08500080c106004560194041d110304007144810303402422801e05042200ca01107041403d4220b40303e1244007104002c1280000100302e442418809003100c0309030f50610030161016170b8080586610308220350b0011030081401c1e250800e5040ca416001601e40c84d00080c9002e0380340d00002912140807224074000094201d020b001d01c0d690801c2c04030143c2d5948404d40207a032030401d003d0b0100004000c007100003001c18004000f4607101e600d1805812101151010080c1100c0101440c03422001609208691081104441c0c030780e11460101101800d11b00c00908000e0184150720711a0118450300d00c40c404c107204c0d00c080b41c2a400d02e1882c0c1084282c00e00410b44000300d6020784560060700390203e500c101c0851594401c0549841c5546014a401c80d42c22080d0b0101c1000d252556076103202e081c41d6901c104c0020300800101031281c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 275839424 1250 275838174 275838179
    0xe090a0606110a05030306060703020c1201020a090806040203060f0c0d090c091a01020706110a02060726250f050a05060a0606031503020d020103090206040e040b0f07021506061909 79
    0x207000680c2c4001c5080a0b6403103245144001030703000048079403040095a0b6103858034100c0ca81a4502001c8142e141e43c00121081140c40806055001d84003902c0a40c2c2c1e40310a0950f03495015443d1402600c0180d01171300441c00195100c030000740881d4116603415031442c90320460000c0302c0304450f030f00304088541200d2160100311a5105000d4a80e103461030a1f01c460f40c0541c50320005c1d50700e03191440780c0e906200b00b0020545200c40280404440160040c00c2c00303644c1c410381c1c6481a071480e0400400409840700044031321800d460001941c0b180400100c0440c001c00c001d9050310b02d00b4070090011110343e440f030141e04001590a11043e420140b24500410050a0801c11070055600c00c0c0c0003142010301d041c05c20480e41b242407480f102181d40644124000801740d00040307020701840000650017500003e00020005240c0d50b0f00d41c402c038090400341300643c0754949800302142064401d1001a800050140001c96040c01030b56000a00103241f00c0c41c201480090316603410806003100049007025008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 275840674 1250 275839424 275839427
    0xb01060201050f06010e0f060c191401020a14032203050910080903040902070c090504140c0109031502030601020a050f0c120f0a0b09010e0a0c080118080d0c0e090a0606 74
    0x50b01e4104071282058151803a150000130000c1c0d2816002c5031180300002d40300c248540b00d000844448442d0035040ea220300d2498040402c0300d5002e0300085909450808090003418010b10a07101031441d030b42d5841302d0705441050199019040030740407071500516210254561a101074050001a00c01d1711440e4454103a00f04012038107100c50500d10500c941e100030440d12160100c1240d0036141c485400580b1441c0702e00704400c0700049504a000c5852400e410310007444100c0480c44c01c421081d5003152022140346004440b1404580300050501540040001101c08190043c65020300e0610441c0e0318954951100b40c680721264001c040c441d0854101c44030181008101003ca1640c4a80200b402c054180c050a50318680203002820f10400c0c0e0010652003002900104940e410300c200b1502c0100c0356041c210864500791190003410b40ca0701ca00c410b1640324203620001070700d1300004030b0f40c2418540a41c060142c01651201c00070000c698a500c000c41d6121442c403800f0b0345901c8070018107079082940 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 275841924 1250 275840674 275840681
    0x609090f05010e01050d110d0305090a0819060c1e1805010219030503060a030b0703050a0b091302010509060f16020405011e06230d0b01030c050903070909030e0604030b01060201 78
    0x6480c000c0d1070808006100e20b0360390b0745903103044032010354071400a001c003401d02c2d81e20b642c00c0340f6003141e0090741d207103003c0145a44071018060b20300c0700b07e4060290300e80c2c8240465032101c3e0741c0700321440e801e00c40c0c540202146541d482040d54401c141840321484140ca841a140084181000008103074100d16141200110001810103440c01780024160102c0e00307a019407911036480b00040800c600040003408035120582c80500550380089070180724200090058098002103c0148040d4a4803143c04814602001900e004d04604400d804442c10079400440e181e510810010360001d40421075442c07441084001401c50b244120800116244648108000d40724180d10143c00d18000201e81d4440b44200355040c0225000c0782481c140309100f05c40b0544044d01800c0252068503000300ea00500079055811103441d110303099034200b2100c01c41c414150f946000c1d1341c000075010390011105010034081980014401406410f00f04e81138083c2d00e0006003558400c0e00112100550180100700c2c40f1380900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 275843174 1250 275841924 275841941
    0x1030e010e100b100e090402040603021003240308120405010b030a050c09070203091c02040609090b04051203010b120a0b12030715110a080a290a09050106052a0601060909 75
    0x154400da501c1c000138001001101a4445144600340c0e202c041380c11592380b40d10500c02141c0c003410341d11034924010400340080600104900d19002144007800d500301007610401c0940c1d51100e821800d100e8000b00311101c0020050084401d90740e206240307001c654041200c1c3c1b81440c07141c070003000440d100302c061140d5144050508400c2d940284070110381942c8002e1340e1100007609401c0e40f42c90701510b000080280c65507a0001c003e607442c0c02c9209045c0090303001080e01c56405081160710703101c134000541d041071209101d0703040300d040e06010291038940d0750321201d60808000b400100d5403070702c050006100781283d2031304401c0c40d60000a0610070040b40a0344080007a49680042100c4501c1103c940620702c100c110710420001c40c100025a80e81243d80300c00c3c0c2e980c41c030300e2410500000c1c0741d00c4c801e1260b0070a548140300b0240300384009050005401904e0585080f941e606040c075118400c9041c419210b4020001103d520340c4815910050030801c060081c0f00c1513650001c0e180c944581030040700c03142c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 275844424 1250 275843174 275843179
    0x120c070f06090611010906021605010513021f0c0507060203030103170f070f02210105070e0405090c04090c09020310231503071709030a020f06090a1101030e010e100b 73
    0x403a042080a801030006000c03a4444d04100041803101d1100ea8010000b2050040130148041fa058101e440121000c42c590740c030860003000140c9030210165800042001c00035440626000a01301d14049a0070440c000d07055810000200c11039561603a0034078105802410042e44040010000d000c00140b448100028402002d40b4186aa0056038a03602c900440035009003d0903c0704000c54a03038030071345c0010000c2042580301c0080c0c2544518080c110940d0b26a00042c0707054150400c0f460548215401000da07400203041034001d490610000d065031500c00d864134075101c0c00c0062409101c4c002540f040d60301d80c0e694072505c2d041440481c2c0300448910340442002c040110300d0507070748502d00140001c654442d841c82c3c8a0360307808000c40302c14480d011002c0b42d411046081c07006504002000d0003070780b407468082d03d80d60840200240d58401d02240c503151142c3c0040303400d902145243c800c500200c80d0603d03010076001c2c1800300003800e4402034510034813130350300649900c1030104203446054203a4804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 275845674 1250 275844424 275844449
    0x7050312070c0c0909080c03030703060303020c03010b010e0405040501060302060d090201080106081e15060c0102040312030e1507020102090603010e04030f051306030b0303040e0403170609070f030518120c07 91
    0x741d44440303108583e58041c800000d0760715958641840450401e40e5141110b480840b0781c0c0c0d28000000401038102c610046015206a90742e00c521480c0c103025401c0d80510603558004048174a80800c40a000d015009039483e551b0381d1303004000368a0301c4004102d950007404000c500c2450303d1000400d8404140d0064080001d07840c2031084090655a261078180d6140ea0041c08644074034204490400480f80140d0307001c000090100c132201d40640140045a000300d02441a1255441c0b054050301e8500c0d40050150304940303d100c99442e6800e5520350446c0c13203480010306020b861000b00f0000e41c000c2c0c0254401d6003441080004060303010300c0f11071195510349091400c11030038010b0800b8910381c0f40251400d054440034204083d4800f041a9002000c50342030f041482d080030300b0003030244040c0080402149164900143c440d0800703001141c01180795560303e668104201300100c00406026000319080c6040120202c0150010007109001000f180e00d195070342e008010100346800003641c004980c10a1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 275846924 1250 275845674 275845697
    0x70302090c0c010e100621030906081509271203010501111606031b0f050403021c06060b0c010e07030b2208160201090e090a080f09060705031207 64
    0x6898100542208201e20900c1c2c40390100c0c882c25016042c080c030080309a206218030390308000760076007280c0121501c0030300c00030655410000c1010740105410740507010568160080103050700c03400c480d6506c90306501520308161007105c005042d00301c9c140c0314a02064201000b203164060800e803145405600c2e0402003280010505000c3e015010500c21541031000070040c3c0b05510109001006461405018200320540c81c2c690240041103181c0c030781161031503020003034000c180c002d42c000e0130000c5045e01c1d298240303440c660070070009910100a0342c00c01140541c40500181e540e0141c40054100c0c18469501e684074440040e00312100401f441240d64081c8000b000070804a462044d006140700d1210700d07020380e82c21600b0120000404008084040c0001c0581c05800f041d0260590300d8404d0b40c0780a040c0e6541c0c14020308841d8142c465100070781008440701c00064100000b04104030368602c100d410100c2d88000640c2c1600801c6c000d841c0740d0030010340c03000101008440c555002c1c2031818562034590 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 275848174 1250 275846924 275846929
    0x4060902070c0b0a2006010f0f03030206040b271b0a030209190b06040609050a0f0b03070c150e010501051516030c1518030809010e1b15030403080405060702070302 72
    0x225244946800f1140008072119032900c543c50050030a0507009840b0750001000c98401e65502c400d21690070809815000402c0d4401241c000f0030840781c05500410f2640c40d56102c210b4040800307440c00c0c40e904400c00b41c860401d000c12074804682c9c0b50380400342904003800112041f034003d512006c68814400b6280034030052340d8010040c3d40020000b4241d1040681160480c1c00801c1005803090b800400403400055181d0700903910400c0d500155400750f0001c0c0d480030b400c2038000713282c0550300500b4802c2c40043d003032501c120149100340b07000c3e210b2103080e512000c050740222214505200b45907510781c0e0040c8000d040c407000000950000014491802c14a00354611804040110003001c003c03000c20f101041c80510000f80500410018040110814818103ea400800d000301140461408400294003901c18410f4401c0c00c0943c45c007910109207011b2600c1035901d901c080042c0e00c08502200d01103048109030155111f00d00c02e0300c2e81400c904050400ca0303c0c141008003094215442241e0600040c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 275849424 1250 275848174 275848193
    0x20a0b070b100b0a030b130615030b15090d0201020c120f01181208070e130b1908070612110c070812040605071103030c1b0a0918030c2f0406090207 65
    0x8901d24540001c0d0006120700107007003c8401030071f440d281c5041c4003002c00c1b564264040242d000b0142c1d20200840003030701c01480061b1410fa400003d0060b41805800712a00704141c3c0c245200744144156070500d601b0b030000aa012010741c04500c06688080c1c1d00c288407500034420020b407090400e402114004035540c2c0ca0301001d12441c403480c20002218007246805005045404011b0001032110440e03c5855807418020218043c0341c80c456800c0082e080d0340300144065043c01d4a1401c000b03000280c1c00c203801601e8102d50401e418070340d260b841b08402d090020000141c50751980c4040904880c2c0d1400030500e240440320324484801c8a4100010800c01b40c100c07048601140d4006074201c1d40b070f80c03110006421030085c03c5000940740031300070740d0704858050210805107246084500c008180d45034210642114010740006110b03496440040001c28069504038030424801c40600c01e541c3c083c01210b407400304040108641005e03540350064010300d0035001d11000f4140c201000c60070074140d1748400950 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 275850674 1250 275849424 275849437
    0xc0c010c021509130612030e04050f15010e0a2c010e0105010e040605090702010605040f0e06130f051203040218130f030e0612041707080f0a0309020a0b070b100b 71
    0xc800024061107907841d060342d0542c04c9040b851003046080e542d0358500c01118003004045000502e020380c100c0f8189414405e140c0604641e000325112035680300d940507001a48a401030b418408000d4011501c0d50315103082c200074004445251103011603900601302922030311048442c40b404074170014450085074012040c1145d500740b801e081d01940c5071000c01d008000706e070480d0b50030100c440100a91b0341d805400c040200c44054070100600c03030000c001002102c00207000302015410000c089002e54088100071030a06020b00000c0740100500d946151501561007100032441d00080108070940c43d0802d4206c0e001e405141b00181d580c5444940c1d140307141c401c0031000700f42c850f8401443d41450f2080c1301000040e00e002c0c2c0790941d81c0354a544d240141d0b510480f412203840c1e04a4900144034000002a2002254421007150070505d10340800d44081e0015014142010380d204446000740c1c1c5d0301da101800600d840807002e90341e00008e08260b80b160200801042c0d400d032903224208070f11028401102c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 275851924 1250 275850674 275850709
    0x1902211b04023c07030807120e25091418060609041211030406201902010c110a062001090506010b18031209130b01050403020d05011d030c0c010c02 65
    0x41d100c3e460050403007a4503500b45400070700c0411190700305900080124050f9030b440d03c440b40000c40340b0b46a03205940840c8054070761500f02c0e2180401b948101310b1110140c40380700409103512900d40f15401c00b240c40030078401d40420000c60900c000110940140d04102080702c0180c1101d10780000403404200010b440188114003031031002400500c900c10030703c45402204196176032244d442100411840040e000205050b40e00741203031545c0c0000040c642484a03014000e100051995001903480407403280094640344c2c000110b1040c80e83c2d40c607060f08040c100c20307154500c203400400d1600349241172098084506a15090403500030410006d03a00781180c18101c1c00301d07500d5040340c0003054220f102490307090b058072032689482ca5815038000075040c0d06100f580d001c0b01c0704d440131809005561480e010203010450402003800541000084a18098086d000104001d4005002c0150a00c410314801405810101d04941c500f0b50501094000f0a82460b00002c144425000100c14080f80e82e000030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 275853174 1250 275851924 275851987
    0x7061e090803070c0602120907140603010311060c070306090b04060b0301020705060c0c100608030a020d02030f09010c0c08150103120201060e0a02090f060304060204080709020c1902211b0402 84
    0x801a1580454141c0d07031a10a2101f01410100e800c1580c1e55002d014400342c400044440050301e0803d881620304894104010000e016084000d0000340c1d0b1000320b10b41031728081e40d80d0110100d00d144c0a40d040c1c103442900c407a0203500e45400d00c00700700c901c1410050320a034010001c1070041400001c04a422002c00c00340c041d914040100c169143c0070b0040c400005c2c4a0405e44c3c006850b0340040060012800503800380e624002049034126107134807a401030440c892405010700d0440b94070902c00903089620a81e002d49000f03448640461900c0b80d03501461500c2041c000050081015140703000c900305401d0f0000384503803420035040e0808084010928010f695010500b460580d0b58001c411a203c1030107040291303a030030182016000303075104d8000c0c48420b129211002035000040e00c00ca17032504040401815142c1910060004541c00f8014141c0c0d1020a03809150100102d040190000c0000780009201d501c00c0c4002d5100f0f00060b400c2d0032449144180704000c0e4035000e00720182d015245d80c14805 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 275854424 1250 275853174 275853197
    0x7120902100327031e03091205030618090a050f0105090307060b18010803030a14010b04060c03020111040b0c060a02040302060702120106091e150602030f0a0504090207061e09080307 80
    0x1d403058189001e4890300010300683c003205054000203400c0104000e040045164000d204065007071b58038101000b454419465140f440c100d20031030145410801c0200070003121424528101c03601401030303401101c1343c0c04c003403524010400100403841c1444113910084c466440d03c195541d842c8c1c01416405000103844904079621a030350f91030f03500c1c1d00c025401c600324502e5845d99105a070300c1e001200d030f00030380b1031800d90340b68032608003150414101c80c81d22080515003814440103d41801200c00d048041d50b4940d8100103c2d680c070329014001500580e05e9094aa1541240c05882d20741d01621540300f1743d20400060025849480403a1019501990905403030380d655000d0b1030041205602000c038451401002e08180310a15800c040b2051413400144008203c0c511102801c0d0024400c1b8000369004000d001c0800040c0409070890000d1828001d0a25658840b40700c00c0e80d00c03a0303000f1241135603240780c001c1141000c104070401c01c42d41094100008041e0b80e0b501e143e20721015049101f0b110703c2c01c064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 275855674 1250 275854424 275854451
    0xf0e1f0c02010e09041a0f0f0a020708120f27030d02090312040b041d06031b04090215030106030615050412020604090e070305010b01020d050306040b0d05060f071209021003 76
    0x1a08034055002d440c8280703a2500d81000f42d4203941101b05c0d4401b000650b008201c0c04000c01c00968024805011000e0003a1100300140b8020b6000c1c54040b5120f21302441141800071080f00620700c11101700ca5400d5861400210f1503408240d071410b0710f8200c02480d0b0a00f000e514000007612900302020000590701c5541000003480c0c90310744003600311220000203010402c0c25418001d00f0494090503420441c26204140454103404100e4460b0b82543c0800c0200350300090300443c0d0121200d000c1c00016800206030003180d41501e0100c2d00001c101d000000400c40d0315030602c100b1004108021407545483d1000070028501d1080b8031460501c0c404c400498000c2d56a1a0202e81c010b01903000100f0001c0d80410780e9a40b50b1440784000d4541d03500c0d01900d40d186500108043c105103186a88240ca15a04d4900704070051408000140c2c02c10400d10b02c10740082e0f800c20005004801054420f6064507088000400307038200b030f452406905083c24810001a03c4000300c0006d40030143c01d001c1504c104d01c245 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 275856924 1250 275855674 275855687
    0x213140d050609010605181e15060f03150a05010c0609060204090e10060b0f0418060302030105070903200105030f0a0912090303120504050a0b0403020a020409030f0e1f0c0201 77
    0x800740c4280514024010f51402c1503000000b1524140d075214562540450401c0d40700c4000c59040c02c286113181007200362800180000303940b161400e0045800014404082480e5070050101003220362070000a0101c1222811800846030804640203143c0c0b504220009150500b0240c0040110780c40b4001141007000d81e40640d40a004801e9040141d01050040706944e0885003030014050352412002042e6460805c0485100c01100ca0030540381034640f010212040043c420fa808116646031000710041e503081c00350b00c1c00b0311030a40e100c0d0398107402d40c00c0050807404c41ca003a01210420704108003900e84d0f002402d0765449907031718100404a40e100008a005009200d0000b00000ca400300e1500038640c0140012055074060364825074242040c0041004868003502c0107003060784903485a44c00520314182c0103038801e00c680f05880b0507042c25400300c1c080c0d80700c81c90110301040c6d0311502c0d13580042d40706d85c1c80c4004c17441c11681c2500800202c851020f0418010b03400380104031402d005242075900400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 275858174 1250 275856924 275856949
    0x81006091a0c06070c060e1203070c0611181207051008090a12020d1b020a0506091801090f140f06150424030507020d090e1005120f0f01021314 63
    0x16110f042c0781c0650001c101d04074080c5c041761402d103000c01080101c000091a5071051405a8407149035860b4680156210080004e0444403613817070f44076042700030502d030025000d5050000c1903001607a5216003040174029091140445a0f030100e42e040120b69102400e03000306244d5410021110384a80d0003a40c10310400c003a020302445000c11042440c550700091209603180e090f5209948140d08507030003200341c1140300e40a944034046000a20552503e94010205800700502c800721000e582040224035034004d80c000850f596035001030304031505890152858000d800c0301081c8075803500b1a084c1042004c040c4c88140100307802109004100d9807103040b100900504c9410040f2100307a10710318415801e0396082d2600203402d200c08108582d000050440025070301e6264034010034184210311000d00d00040c5195010f02c40c402e00010580c03101400b00c07a01003458005021136800241f00680f5000c4d44100c04040d0340e00c1084002900c2d84031201084c01e56562545801403141840d0008010708030700d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 275859424 1250 275858174 275858197
    0x30403110d200301050610020307080a091206140601030b06030a20070606050414010b0406030203090309060c01020d150f050d02030a0506011d1605181f0906081006091a 74
    0x100d0500564040d030202034841410300f1402403100e6a5101c09000306412003030380403405640180b10240000d0000c0024083c6a680d83c540070710340075580d481020500a00d42420b40e1160350314080340500840c02c040c500e61010081c242800741c0107c7d00045900d81c40003c010811041c0c0e6082e0403051021401c4021b24483d41094000e80c80c0c0803a420000c7c0105510300c2002d126601d0b098131000c10308082d18545048514244401d81040d14000c0154081d51008141c4155400200402c00c07003581c49001900101045000040c1c0b500c0500303c80e201200c044e40c003842103015007194108054050001c50300c0c140c49082c2c03941e6814400c0352000c41e142074411140141103014041c004641064105003150701001d00700112030b03031030305c0b0309924100e0816102c0900380003403010001200164555040d10403065400781c0103980007500801d072402601d0a80c0201800912004070400c001917011782400d0700000c90401c484421458500090309200c01c44c810301c4614008070130b4046ea0340403010252040e1001d075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 275860674 1250 275859424 275859443
    0x5040b07031209081b06010e1524070303020414010e0a0b0c1509030c0601060804030c120c0b04050c0a1e1202061308072123010f1811030f030403110d 66
    0x9041005d090b100c5101c3c035012544180310000034202280308649001c4c400300314045150450013000c6c040104948181410001034a2520440c50110b94004000d01406643c0058581d400c0c0030381c000c128003034018214100300c00c02d8070815040d41c441c1000001c50308170782200340e40c815a1700081400d100650a00c0380c81148108104444c81c1c1c808401440c0c1d14107900241c84a50ba02c407201600c8845050300e020700010041040c1800240040c00905e1001c41c042c20024078054096031002800f0600f250100c401e0b41005c0d404414a091200040c1c2c0030b440c0c401c0244a20341c03440e40f5849281d0001e44a0750001d05805001e00055480710412101c400d100d100c600820700d0381702c502155540c86240303e00f0b2120303d12400705040a0042404a941c42c42e48003920000e40d00700e89000024041d01058884000c0d541c50b1442540b520040c480c002c0202c8050b620301e9061034441c20a003222042011500d4040c7e0082344190381841804422501941c1d4030500605264140c40046042c440c1e6940004003032215 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 275861924 1250 275860674 275860687
    0x1200109050d080105010504030812180604210c0203120915040b090102061003050a0201141303060608060105041103130302010f05090102030a0b12030d0506030a05070e01090c05040b0703120908 85
    0x1c021400c440b450410740c40c0c01d803160f40d840e00116560b00c5107100c0501a00790070301030505000d1038020707555000324075621560400303c4884402ea0915000b910215246040859603200048604081890741d000324103208400040c6500404e0b2208915003a02921030b07400134900d81155125807828001c1002a92106e850300e49580ea1100e440d4080c0030380c9405403040300300090400f80145038081c117496000004d00410380700b5900558400c0c11003088200105818010028002100c81c0e921000394040d0b140032440902c0c01442c0b908001c011307040280528246400d00042000c0007003102d401c08841c00744c2e01c440004905080b0f004124440c1210401c1d41002e007480002d11054002c0d502032542c2000811080c6900300c100190742c81006110300240d041403140d40514546a403103150b0100d8050203a50701024141d03202800d043d0750f13800c106601180c46005114411447c443c4580b003081c14180300703181130704055004006004103000201042096024146207440701d03000382c0c51039648051240e44401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 275863174 1250 275861924 275861933
    0x21b0f0c0d140610091103061302070614130611091014070f0c3210050d18030807050301060c2a2606040224160602070303060509040c0501200109 64
    0x1070b2280d14001802c19641e81140086d02e030440c1d0107450b0040c4a0801100c04000301e0010f5000340c1d000b601d40950740c56101d008422803003400d43c400d441c0131103d581c440300c05103401d4044486c024211245281d042c04801046c0d01c903030300d030401c3d01034550500843d8040b0303540d100001440307601d000170100401e0b00d03107110401424425000c142c0307910406c0e0880321245014030300c1e000704198074170003074034000400b800c400d0b800d1807154030307000750380501d892032400c0c040120140943d040a800307494a404000301c42401c1c198011111500060f5502d440c904e554948140102803544040700540501d80c48440074140382c950710510180e11170412010300e45195503240140c1c07207001c00c00307043c04034983d030b82c0040c0d1608101048030f600c5140d00824000c4181040b038220380417200741001d210a0940304109055040001e501a040800c0c400c40300543c0d41e200c185001802d440c3c43da401540240207000c14800020941d102c0c0105840c0b080c6010929a00f081e906441021040c43c00381126504c0d0803900814403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 275864424 1250 275863174 275863201
    0x80705250e1003081303170703030c05030c030a0b010c0501050f070e040e070905090a081201051305010315050a02211b160303021303080d021b0f0c0d1406 68
    0x40050212496a03555076002200d00c038a00701c1e000410b00070010018000558200082c00001d01c0002000400030b4907503a0b50390604080c0e00c0e49141d00000865207034101a45402070441045c510b181c400e0846c02c01407e01b102c02d000103414000c00c0307501ca1540f2412641300e58030186085030450700900050400c1d00c1040403812050300e119000070010341e0850094203103401480b0b030400200300284069850000c580307004001c090510b80c0540a200c99150100300d00c103014045c01200c4d00060801c95141904100914125a944280c00d5051100410100c1c54000c3e00510460003554080746507543e1900682c000e104030880c103151480350005810740c05003d64080c3c1d01c02d5402d0b2421000d100052519594a0702500c4c07500300100c108540c800e4000b034441c0d0003410f010708030309050480d019280d588601c4a50003078030052840981c0440c4c0d80103142203041844030022031b080c01410030401e0901c54552524130b05200c5d10b01807680402c0400c100050500c440345141554001d0300c4050400f04d1240000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 275865674 1250 275864424 275864473
    0xc0302091819050610111006080601090b010c030813020a05090c0405040e0102030f06120a060501240e0604051203070c08011b020c06120403110601030c0f0b040f050d080705 76
    0x2d40780a201011203952501c01c2601401008045000a85450034102c44588820002254030301800780444440c15840c0a500050440c0c40b01600d400e40c1440c6d00c0e0011503948586550402441401e1200441c1d0403545964100030015030600300c09010380003144d09407500c0da04c0981c000041204102c00600d104000d402034800c100c40034014522414045400d0380010b4490155034039607500400c4251800c24810b10040200a00b43c0315407058613211035044400c05d90220f001c90005104640c210355641030307040114403183c1095049500110086850b0780681c0c028280503003082d04c0d0300d01d0504410401d803040b40da07024541258031611200050701a003010b90fa4024406c02403060000d5941c00441c2c8a11011006444941081e0b07508200f42d0601a02400681c14440200c1190389030007c02c4c04914040e40c06501040e0300309190000e1b402c04003074150300240d4801010301c003c4c0301204ca05124041205c0c0115920010340c561703410201040e10600300c2c014407034464049040c0e81070f00144043d184 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 275866924 1250 275865674 275865691
    0xc0203070b03100605030c0406030c211406040219030509010216060f050f0f040809040605030f060412020f031812030403030c02030c040b010c2006070602040e060604030c090c03020918 81
    0x3400380c0d8982003901d45020541f180740c01c01c0000d000900c0400d02c647d001070804142454510198816080e529910304240344031883d8064481040f143c00d030698041d42034000000361011480d02c00107a01504c2c9401018800e01304240c0c2340d00105460503001d406540c541e82401c0d050340300070616803405100410b024103107001158142030019015248000d2000d120380401e0f00241d14581d515903079540298490909264860b80d03400000c0b50588003003022071400f40301c0c0300040045041c9030a0244203100825003140465104840501d01c540300881600c541642b0084180b0340510b408000a6829655040103010780c40302190001c10300da401b464000703409009606641c442d019040910040c0c0303414400050200b0b4410f0030350b0000a209807940e9000f103450400f580c40c8041d0220014810303900c829000d40c2c280d50041801c1c480349180740301d40b50b04078404036205442c2c640341d80c1e64001c83d00842c0c410000c61650b100c3d0340d0b69126000c1e804030382d0314000003440c1c0c1c0101e1070380502019001d08140c410382c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 275868174 1250 275866924 275866951
    0xc03010e0f06070e0307060c06060e0711060901020a0905091003171309020703090b0d0f02030c0a020f0a02030d3e0c10050f070312020f09120607120c0c0203070b03 72
    0x341c0c003a0142504600e180f1300500034150490400000350746461140d01b04603882d0340eaa84001030800304040d02c0038002d012580d82d0900f0500c140f0b015615001d00504881c809920401034100c0071500035034260112102170310f424280d90b45172000144200050703407001d055111111034511003151004014083c40c1200c4d540d01c03202d2030300c480c0714000702d005001c801004905024018450082c0c0e080182c885080c003100c020a5203030070b045086c01aa002602c0031150b8020100380d4081094050264030301840c1100c000f0039204c4e115800103680d0b4482c840b1a0300500c00c0c1002034900346082c02c1582e06c5000d292482500c01030694070682c7c0408080741c681325555029600807a0005d24003c11009400d41d110346e0f440d818608151066030240e801001c041b8141f19000c3c0c00300003182c61a0000c0c1242255205019849068082c280800c541c2d501e6040000760308000200200641c125024070100f44c04254001110a1a07000c00c1d20400040c00c8040e60510641c0400a2600900300080d0b200750141d143c0070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 275869424 1250 275868174 275868181
    0x90302120d020c0609060706150f1a19091d0402100f02100b030c091305190b07030f060b0d050108010c090303090b0d02120103050105060117070c030c02030c03010e0f06 74
    0x603074030791046039600300060308807507000c151034548000505200b0500418141c6400c11540e210300885140d00da40502e1038076400810070a410034100c0000080c94003040502d660540a4544219407140303010104003d54104480072304284035503180409001c1d031500c0d41c00301c079005604100c5560821a800c0f4030a07480001c14455080c0b280f60b80301c502d0f0f0145c0e0010103659200c4040c1001034200c001006400d8403d0780041451a07680b0078040380107451640d10300c8088041b60405905003420744205071b10250950341207a00044005000e90303844010b9260002d6071401c54451030002d40300d2a400011803000c0494007400308256540600d040326601c000800c214800c0342802c0d00c03004d03024030001d0701040d4500810030071400c1000040c2030340400718500610704210040c1102090000303810a94641c3e6484080102a580100404034041d8500c03003c8ec03118904040000c0c000b0290820080400405070220401c54404105102c0013500080080c00382c10000d01e120740c6e8031803080700b45102030310808000c07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 275870674 1250 275869424 275869459
    0x204180207030f0e03100c05030a0c0c0320120c010507090611071214030301120506060108061c020f060d150509060604150c0203070303030606030c0305090309040e0319090302 77
    0x201c03950998191070b0890071092403001078032002e00003428160075003d00030594425200d03c0c4221a0494403a0300e41e00c0d01e83c102030301c504003200d94011500c8240030111029102180d00284030340644045000c140d0700105a050680b414991032082001943c3c00100d41c0e286040f0044d040790b0302c0390300b0564660204646c0c0712030803103ca61803400a25803d400c07420b4284904c4906c646162403140c080c09c060900c83ca6080340103451680260701411505220400c40004c0000500170560804000d2920700000d05140307001541c00078000004100240b012488070086484c1c000b01c1400c07600e00140b12581341d00e844921480600180004620940c07201c08022030305280c004c071980c0c007400000d0301c0a810a4107020106403070b82502003044003800f154000c0080180e500304801c002440c800d130380229101d40b80c414040c040d01c50702a18a4181810242000310f1100c2c000155040c0380700803100800c01c0210b00400d1420b40c1302d8809034001c149601c008021100d0380100108007160310030350b842c3c010010b01109 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 275871924 1250 275870674 275870677
    0x131e06050f0c0a05030301030c1805010e011a0403050d020c0a0f050f010c0302010e011515170403050702210307111e1302090a0e090706021506010804030909140f10030302060c0d0603050703050102041802 89
    0x28a44620dc100c0c8014003010801a5002000120004001c1d151548a1700c0e1586494003602e10580140e0025040c002182005403001004042c3c42101202d2541400000b03085501c0c1c607080c45040103d40d401e100d083c14800d40110009004100c020400791400803540320039008240141d980446e80329600c0030041d8814654040150782c051a8200c0984583e5011a5641c0c0140c00580c0d0181d0b5047c123500004084041084402038500001c598444c1a45000d03c01c15903603c80052044550300801a00c4c010483c000c1004080b089030102102810401918000d01813840c0d440d1b08010541c0bc0820400501400c107400341c1d1041c030484510700d549280c1240d17a22901400b62081210302c20114811394011f1821540061103410202c2c41c040c2c6804215003203900c2c1141c1e10752084065000d000301441d01c854425003180752000c03030804890662714003a41d10700020308851944c1ca0001104021781900741e20290142d64403100760390451750349003403141c040e410600600c0c28084050f0314035404100c4910 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 275873174 1250 275871924 275871929
    0xb0d03020a08090609150903060106090315052503140a09020604030605071e020d0305010812070b18010c0f141c0504060b06131e06050f0c0a05030301030c180501 71
    0x80c010420400c20340e42e5181650005071149030022030a02031500180c0e25045204c1d000030b210800301d511060a801010700e01041070348a0400c0c80401ea00600200c0c1c0405442686010890404155030312000080f100805444172082107820040000d914070310780c1070304000b44070340041c02105c45a88401400404a62100c1c10081d4800380800007000061503d40060398004000e051283d40d410444484071294041c4400d0240180c001d1641c81104681501c0303820b014001e003038020010600b485440e103403c3e00c0f40c0d450141490440300700052381d100c00030b401e808917a600c010090000341d86001010b4a801c040c02100300104021003c0c0149240c0344000b520802e031008221200c19001c2d00d50300d6801004040d10649030f180c0c0b03903880032465403a003000030066000400d1405c54851310380045001d8407030407070200702407200d4210010402c1c80d40c03000c140e03103641603e01200d0340c2d40e000414056117401180b03034000f00130f40000f000010038408810029422030303e443c1d128030030080344248201d044079400d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 275874424 1250 275873174 275873177
    0xf0114010509040213021c020913090203030313050c120f06010602031309050604090614061203030606070204050705040e01061706010e03060103060b04060314010603031707320307030f0b0d03 84
    0x2c10019000d13183c00b0000c0810070410031001071400381c4510050070402c00d04102141d80c5a00020031361040c0c20000e44549001042d000c1c10042c44c1c4a65001a4480c84090100900d0b522107461100a1250510200442c50002040d4080440079400c40c4e540350091a400d81c00b49004080c000681c00d400442110303180b04003290a02429403e014120004117030240c01c0c2d94000e03640f41e0318280003c6030792050440c00e000444080c1038510781740081010505002e0942c00860f00203009001d05038442c8010354600710740c100e401141c1e603503036002d0850b05401582d006500501550000182243d0408003201c0281e40c400203084031680d4842c01543c40143c3c9400742e9070164816030041001c40c1590344507035641c40d802800861a69669110001440e0a020a0309400e954401d0100708064000b884084282880b03510304000d807800c200c6c042e00c50344011101c180c00c43ea090b141e807601d602c070f40c000440310070b40100070007901d130304004400400901c0d06540741007035070b490140e0200092420292003031003540d06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 275875674 1250 275874424 275874439
    0x3240a0506030f0c13180309031407030b0c0703021216050106140d060e030d11030f01120c03082101030302060f0109051b0706020c0129060406090e070216080f01140105 74
    0x4c140011110960540026295114501c0d144811035040706008240281d86003001d607400c0d07050503607926030380a030482040c1d40b001c1020000100d1034040c042e44030340880c00c4c0f2038a90102d0f040507802c0c10080504100c07544000541c00880904112014940760700600080000390344485d101c41400c07050071102540040c2e0703804403400190154003c0c4511903610710690b410044680e50310800e036a64801c6803550500003004000c4c44a680c20840c074010b181034042590407082035126660040000c1c0405004800001128041c00c40a60740300100c2a2044040000725a900d040003511140e0680c0c1e0b4480b410a404000240003030706020f480d00580e2a51010369005c4860b52856010764841242100c00f03c0e0280a0441004428400c00040c041000040381d1080b80c40b441c084400c03400320042c00d22541d0140801c2c020698007488c000c0279540e404459070400d84903024180e20707040d10b4444003442020420b00124405101042070f08100202c40002d01409529020100518009020b842c3c4c009a1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 275876924 1250 275875674 275875693
    0xc1e08070803060103270605100b04060503040323070308070c030828051602100606080402010318050109080405030c040603050a03210c0e130e060c030603240a0506030f 74
    0x207200a68000303038141000241c04c4c034251260400c1c0c88980e00383c0340c0b10201010480050200c240a410340c841854404409601e0400c40342001e075000300d000c3e0804010b030100c001070401d40100e0808003004a0900070203a02e5030406c800300c510f540030000441c000341c0c403071780410311084c0641c0c007103400a9130646031540f5a40d607001c4003182518140c0c00603200d100c081c1d03251f00640806845464050700d4a00d000541c05150982702a00e0700c4224180d0b1031100780f07894420030900e03034000c00d000c0d005542407801080100102c010305244103d0141c02610a5281044210070042440000c10031603c2c258203442190b40d04104100880d400c45c070015069030410400580001e10804920080c46c0c540d88086003024010381d2001d0496500411076000314800740d001140510b0f0940e40807001070500202400341d05d030030042681e202d040180141001c1c02c0d0210208207543e07000d12506000705410000d1804d120341ca000343e14000003068400da000d2a00d0000400d03038904005c25001c100b550280000d142945 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 275878174 1250 275876924 275876933
    0x20a0e040c090f0f0203090f070b07031707030b0301020d090303200906160506070c15051e0408190507140712030c050c090c12090607020712021f0c1e0807 68
    0xc102986412541c4d03c4403034844045141c40030b5800307500084002c5c40b440c1d10003c109890207006411046e180f2038240032503000a5840322a120380c800c400000c032650b540324460190080d200f070410496140d400815030134601c1d29154403c0101c24001d030f4042c00300b20007000d03501e00c10490031148041425800c20101a00d401c110000305101d43c101500450014403d4423103c0c28076405548044c0011000342201e4148644545405c010300e2035054100076070f041c20078030754030f014001c0714401c1c03041c241290026042c030450400b9120030303002c280041003c070100000010010383c402a0300b124900c80050882c04030090009180b8181c44920300714260b0b840b2540c0b019592410720b42002c40d520711403584c07815115215080068000c505c0d40002a0b01c46e00801c02140300a0401080c880440d03011008004d103550f400107107c012070b0007940840303040100600106614100c50410414443c0391070120070901c5d40e0000c0d4082030b06000700a564452030302000c031600040c403410b4018143e5003041c418840440d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 275879424 1250 275878174 275878181
    0x3070e06030c0402040806040c21060e0f01051e09120403020d0f120305160c05060112020409060509031306020a0c21050106150207060318081b1009020a0e040c09 71
    0x100300900715010400c0d001c00040070f0345d010b500b00c02180d40044007170004101c1e400d45404003920a8a44505848484103980e04c1780451511003c0c081d10346410048442d80001d001600306419050000d00aa02d051601c40520344503600480e0100c1c0450740004481c850003050443c000d180d40030101f40790034615009c03c030600116180035102000300d603540b14001a52001401456003c9440114451500a10440e280b0301d50300020000d000039a0030719030025802240d03081c10b65005882c4000514001e001280003050206001414a8a0b00043c0002410000f019002c01000000c0c11500e103a02d8110890b00c2d42d401240003415802200300910800780c0880980760441c0f4400c280007540101c1e510f03080d00b034405650001c1500284403410386421b41d0306010030390140c070441c00d0a2000022581d03100301c603d0001d0304094079000001ca103506c040201030311009060a00242281d082d103640d5141c0c07800800e4800c408030301c9084c0c410030004401d905401300740d02c516088010609442c1c9014948000b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 275880674 1250 275879424 275879431
    0x70605091903030c08060904050c0105030717040f14030c031602130c080403090b0405091302031509030309211801361d0a0c020a020d06050708070302040503070e 71
    0x1240240408a07200780103600c407944440d8060740c1c01090405003000c0180900c2009440c582c01580207004210100d900000c1c2d241c080403003880e20595995418000f15501110318403540407003c8800c0512040c0002c515001c48030342c1c0a07806c50a280c400c4e62960304d9803442030008a60710f94005200d0740012040f04026510032074000340558940c14102410300c002c5440511100c1d003c07907100340910060551140300030024080c0d881440740b80c40d0a110000b00200402450b00b0108425440d0031011514140140c850074000020190828103002c507900362240c00c00c8404813264400c020803503101c402e240d901508144140c440039460089000031000800c00c448007018180210074180c1e05c1030840e20444003007001350b40c0d510090103241c00102c02c0005c2030a54809034112010b200c0c0a880b001c030010350346030000d280a000080012211405905104200b480a507002c03030f140c1c4421061200701d40109210320811f9481c054240d85281058049014502982e5010303403024009225040358541c1140c2c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 275881924 1250 275880674 275880691
    0x6090a051b0c1f060b0f07140f071a120c0918151c030e010c17030106030c080604050708060d03020c09070c120914040f0b191a0f070605 60
    0x1002480754000359040d510054034550954008410144074110000011002403041241403000700e2400203036940c01d005109202c142414000f8030f4004101c984081c0e801c541d000402903980901d8003041840d120b01d214441c0f044040083c0e0446544100e195080b100303d03804403035045031035403144844d072a110b0300003525054003d04e1040c0001e140a00140030544141031160341800140141414007495030350388610b0070240600000c445c40025040761544002d1070081c60b14800148081c1000a86030101c118101610080040003041090b0b050b080b078100580181c82c0d41c07203140c40d5242030008a840440d007600000c0c1a01001c6521460002d01c0803004601030310440b07104c900304100240c0d8407903080c0c40d4107010031844119407081000c2d04190707040c0100707035080c5034914a140c241450f038140942c5c01f006100d26640e482c05200d2a003680d20440d0300d81000350000c0c000c021441000a1881d03114004c00c003480100d441c20301940c0c00d0460031203170100c2d4001c89490500013503a44003000f0f8440604005d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 275883174 1250 275881924 275881951
    0x5060a0b03030d05040b1603140a02070f0c03050106061d090106030b010908060c0405120706020c04090201050c060f060306010f050f060306030a0b0705040e0f0108251205150a0506090a05 82
    0x1c80500f090003064065400340310b0109032801e1004090304014040321a0f10241802d20100b0410100d011000c1a481510840301580e202c4040c6403d11000e504c02c00c0c000d141d03814009000c0144101544030704141d4042d034036100740308415881003440001d00845c0c0c540c0d00040050040c02210300c6034001848440060410400e102d44404c407507803c0003400c07161007181140210b0100103915040b451840580058005003c2540c2000d800075190203101d4401070140e5160b24400341164812412203c4060301d0701d05a40a60a00700005955004199841c0d80300e48208ca0001c190300301c01065120446000070885074200c0c0b1060b040c88959040209100d0b850301681030390390013140c0d411402a00c01c00703550382c1e6680d0350303401c03c14003500481d0003500c1000100070200050054170000a80c0c02d0018804401900704c2030080c0040742d000307141c141c101c545080c080c06114002c10078001038030403001710300d401000d01c1076440354010402c1f80c1c0c04071a8250700075040d90116155040f554000d50304000591841c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 275884424 1250 275883174 275883187
    0x10504031e031107140f0402040501020601060c0c15030c09171510030b0423070f0509190c02010f060815040f06020f1603170426091306030c09060305060a0b0303 71
    0x90308103651548100003024405c0800e940c40d10300703041c0303410790000100c40443c00d25041c200000c1d51a101401400c1c1400f1310502c4403014401c1809884009080132540003905881b8500c0040140448040107000303e44050701c0400c290444d00d1051020b004410300610f0100e0501c60f00404407540601460084c185032000400400c2d031104580748103600501c40c3c0413941d48880e11a0501400300d08180d40c042c0c000400030701181a00c003000c04102c071000c81d41070391142c450401d500c00c0d45440a5038400c1c0b09213844144200660190803012540c1d003e500200105581c03114007948464000c01000340e0564110001000a03004440104555020712001420080300301c28482055004990f85151020f001040c0c004155100791a01c961f039454a80d00c41d15410b15030343d0107080303d241303200404110b2600e81150f02e00c46002c20a580040c4802003044550030400c0c000300d00100304030300055420510a0b07002241d0407400307004d01c4007281d51110040c01039035600a10117005000b0442501c0d8540810001d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 275885674 1250 275884424 275884457
    0x9141006021c0c080a170a141303030b040c121a0306070c05030409050f01170307120813020306010b040f05090405030d020d091b060e010201090201080609070c1a0a0b010504031e03 79
    0x940b100c03013110b4441b1901c0b200c5a030034000707022000900d010300f0b0f50b0503c10252001a1350844d1103803c00c24031500344003020b0b940d00d000c0c2d000d4400245815045841d250720800c0260340030142244160108000f00030030129201d8031b02159410946482c0c06a00500114007002c1c402c80300485103038011b8080c0d80c1815260600c00080c0c680035101404209108030050103484560f40203d010880000c1c0298501162542d80c004a0a254202c0200f48000c80300018110f85880001c404455070003030990f1010341e1500000c440c0b94029004400d400700c400c03070011504c0e04280441a019540000055080110880c80a806503000e51094a100da0f118920320340003401d5a0b114104c50014542c42c0c000c69030400d040204604070300e000550443e810803a071440580d805c0141190401d6095640101503600c049040d1280360600030001c2c0441980c1d450705621003045981c07903006041142060000040b410300454160045010203001c82d02d95811080c810104c1c0b049041005109080002801c0c148540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 275886924 1250 275885674 275885677
    0x60f062b0309031407031712040b0613060b030406050601030e2a09070c060e0111120901020f07050706081b031807030213230405030304120e06030109141006021c0c08 73
    0x1181300d6140d2214800f4010080d102c2c03166049066a021218208000340b681da00701060040c0003c0c0c50070000d40c0103d0f183e51250301c800ea46200041030140720703850360b4182081c2c10ba4400ca400742d600b6031902021826643c407e000f034000c10390040e030040022032a40494812100401d130120038200c040841e001c0710544a404d4106d00c6a0010703140d6801603e10340c144401900c2854a403000964901605501611103800907904840751500039901c0301c1e0365100e90f0342d0080c403075040d44070f00800010446a0401800013002800c1c0d820300d6907815120f0f02c0d40703d4100d80e100c416140d85441c0e1407051000500d004c0214000c800f500c0f20190440b10210780da0f80205080058078204600c0b000c3d29041d01c081503c0300d5810403e141131841118502526158540c02d850303010140c03000b0725080810024041e240d2007081020000c2c0001009103561b035030b441d25504001c00c0d00015262101804100148900d03007811601c01c200c40305600903040c0d0782101003444101400055806c1706009280c880d03100400c10900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 275888174 1250 275886924 275886953
    0xe0109172805041e0801090c05031b1e061204110a060302040e181c0305011a07020a0506090d1506140105190f0504180b0406050d050703020112020903030309060f062b030903 76
    0x1800748c1c8641c20709080c10309111425842d0b942d5020300400740303099034032070401c403000406840e01c90761489801400010114441d090748407001542150600c020321580c095103c11086040798150350041e40e59009405a000d18800d0251200801000920100800350071101050b4090140c80b2495226035252a00c40001d210b6440041e81d110014020440789a41d91450b6a0300134400e1382c208a003130350004120306441e00482e40140e00100d00c03980562106281703070229a6100140c0c55400c0c1d90031710342000030181c41c0315540e5900d000c8035918030307154003d50482d5507000d1400a21021601a03100948102c1404e0021804201040200148482120120140b140d240c40c10100707921520a0030003040c0c840d160412445824040d0302e0314001140058130340c04817542820700c0d807942e40c80c40d411900240152004907401d40000000c1146807040030422611030405949003003003d072076003030501c0607659509520198905111940740c04495000c003540c0c9445100b49000c0c0c44040d00e0382d0710120100782c041c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 275889424 1250 275888174 275888183
    0xb090c0a03090f061d013b01150303020f0d050412020d08190305010f170319020304050d0f1502091c02040f0905060403140f030a0e0109172805041e080109 68
    0x1005d03911400e8800c1c0500d0703404590a05a54410071000c0140300508508040c07242111146440314115151082d000b142540428542d41d0380e1075682ca080294a400c1400083d1540c2d001e1100c0f180f400500450507076040d1102c0d0020200c00c1d02142c1d081c40a401c050f2102550003910a002d2511145030032035950b0715100302d0b43c0d400b0032607516041d80110184d119070001a0f01070f0517406a0428008000282c5909010080c0007041d4500000010390441c416504103d400244e248400c4040c000c0c0340c03051074021442114038181c40601a840c203000c902a043c3d02c41e40c49401c00d507405a44648680c080001c56000820000c2c803607902c1200c00085a01200301118a6009081040281500000c510b0700301610166180e182807450b540810316840005d1042000d603941e07070a00d05044409610941c2c0e2158072102c11042c42da03121a04801c0350300000d008022000d0000420030315821b034280441c1d851041920350b1070a0908040c0340314004583d0721300d01d010429020100003440c440034014603a00d01e00030b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 275890674 1250 275889424 275889461
    0x20d20040f0503011103130c0f06030e0c0a0f3005070602061b030112050c0d03020f2406010e060f04090b011d0109031e0804080705040b090c0a03090f06 67
    0x2404000403240c01c40764482e520a03494aa1110f00201c1808110703503000395114101e022044441c9000300d00c411664114044180075248085490754141c0d0001c000321a0b0042110401c0e40c4640401c0b4004c185801085022290740400b0001203245100001001d545030507404000c0c10401301c0080308003034031074064904c7d43c8208020810b0640501ca003503084140e1041407912101000240c840502c4180328000401c08084503140601100740010b094030000200b04107400003080c00d00030365400c0d00303640d075030254081c0c2c0c1c07000c56000060080290007400c145e810010b56a072054010340e001003103201e103d0342040c002c03c1a400f10710045001403000c2d1170103410000d070001c9140001840c4070130303000981d0424000b00b48425426038200845a0440303074070807560340080d40d4508601a19580d6020000d183c0e260225001c200e01101065000980394295010444410090100400000f041d144e2170354018040083c00c00c0e030342c829000702a290340281d5210020021581d40e001c200c6140c04a0305008861 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 275891924 1250 275890674 275890679
    0x703241104031205030c030402150c031b0106060507172203060204030b01140d2d14150f0118110d090c23130b040908040329060103020d2004 62
    0x250194860a003c80c0382c03402505504e001e41c0303010145c0c440948080c0c030030644000010345a001c070300102d0700300203240760644c0d0f11183e108000f900c00e264000c0c421516035084c001d003ca002403040041c1c604081e003014210f1416030b2400059000b5a2200000f10713201a8440130801c00d141c002400e0100951007278000694491840c20107039952001a0081c1540008543e00000725642c0d40900c0c10440da04603c14182102e607115401c04007030300480b04030342000b0406440130180000380010141450070f000075250000c164590741084690101c0310004441c2c0c00c18014400d21840d40031062406220740c01c0094049015082d08049030007209401070040e888800360010010100c100c7d5004051a020201c480c0da5030350200741d240b50b002c461140c0110240051000700541940000c0038002000c0c00800082007a4100b034107075036015000541d0500c81c9082200401c0c0401840000030400d0541680303200d858000044003e94042e542e45400103861300d059031445403502ca81e0465061041242e42e642e2803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 275893174 1250 275891924 275891933
    0xf0d02191509080c0d0f03111f020d06090b010507120e06040e090c030a03051905090a0806041a040203060f0408190206061003061a0304050f03030a0b0108011502070324110403 77
    0x80e40401840c0c043c5001c485c001c2e000404407064404a503601d4140307400d130245070a078040e1502c1541d10710030341e842030405008445401c9c03560051230400305448082c003038551a003164409039804030608070300140c1c0800c4550041a00c070500c0111a00103881c001441000f03050004010380c000d900581d0040c2c1081041c028198070410150702d51b0b140540241a2505807528050900d00030008104900c59801000040345480780045030303182280100b90341340b06034a45142c981d40c1d60b01100c04a40358818000060148910003801a00c65580103000b440c00f95150040510042d8014ac01100c1080040c010084401042d140350950801079900900301440c0200c00c01100681c02c0c1800001d161406800744001013140910400800300c0c040c0d1555039895600d4864500b241803480618580000b0091025204058024680300d04c1c0903030314094983d0701c17080b0008071200c02d2007001000d640303c1c24007040005d0070251603480ea1549000c00142d02e40d000b40080042d6001c543d406440c1c00030001b014020407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 275894424 1250 275893174 275893183
    0x801050403020c1206160503060607060e01050105190b04060c06021c0c0f09030803180a0b0a020d1109030d08040c0f0308090301050915011404090c140307050f0d0219150908 76
    0x45000e000170505c40c108031000400a80c0d01170400c3c000c02c60000001174840d101d203800c80d4040c6902142c00c108460002c5405c1d40242403c1c044c1500c5066400213881d00106141012425103850700542c600d820302c0e10380203035040c910f8148100c2d02c007502401254282070640b0004902825a02004240c1a0300c4201c010240800a0400b0082c00340611090020444400a03690700c00078940080045801d072200007442c242844500400101201e0200101c507151074026010b0071075045014881690150252842070096014550b0103611071410100c41038802d440c2140c20034040e100000483d6119114020445125001662403038070004444038541801d00c1080c1d0321500754805010740c016402c05080390001d042c400c08000240d04607107404640d846034040d5044540c0601460700e181c0c0c0d0340d81c04000c03042c0d424034620701ca802403000c00165030800c102c1c14050b0704801452491103a0540c0c1c20001890110b2208145050001801140c090003a0040313100c0e6040d96252040810b2030051080d182 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 275895674 1250 275894424 275894449
    0x42306130e1e01023604110c0c060f0a0e0a08010513020f0d020904080a0201111303030e040510061d131d0c0d0204020c010e060412181d0601090801050403020c 70
    0x2a03104010080d01c210300c4041d600130100700f0003040900031621741507010001c5120300c0000d60280c0f62406044c080d000810003001d0600303000d010703640c0c07503503c0e1070411a250041c81e20001c4413440c1040101c0403944540060660107000a1420b401c0540743c01044d800c49104407211031101006072050001e526101d0a08020700c01c1c116074403c0c444a255000c654030b0b440180004020040218540e140316000790480202240c031000c43c1a191404800c010070001282d2000303502090f0711030403020550400d07010f03040c0302b4480342c000d003410300e45441c004840014000e45da0038491400b003c0b000155a603421b100c21190708224001003a00e0b1414000010038507299190285c49500c603519855460700c80181c1142c05503011540161500d4441344507a000d801400c0710a0a04d018040c104420020b00489407428041c00c0e81c1c84c140d4018410001126054107030140c00822030906003002100103042454903030090061401ca0130480c3d0312100c10342540e40503503086000d81c0252051440740d082c5032905c0d840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 275896924 1250 275895674 275895733
    0x70f0203220807050a1206050601020a0506040506250e0603060d020d05060a1103010807030807030c060c20070f0b090a03020d0b0402040b01030501030803060103051f170c042306130e 80
    0x8060b0b16021b00f0030b0903030f0180d15004040649800000c2c031103a00030722104000d2900541642c185107098a009522924101c4aa0211000103014451812a0000411400b000d55103078409100c055008021094100504580d8009d00741400c020068a8032501c2c0301c4001d2140004041e40d06207a6603003000d4845007944500c003400248010882d040000a89404070387d00281c030789540b03808a040440c1c8400d00280043c013410b00f003150003100342d584480c9088241000b040e00b052102d4402001c07646a1039180700310407510078888804c0c40707280b100400528582500a01c019102640c07980402d249689010301603841181000400041d41002d01520031002c009190400c11581595a030316900d000c0501718504150f0b1b51800510b01c1c100303012000c0031042031042c900ea4203683e02c3d9244403211700b40e04001060360080075113192a50030315001d400100f840a80c0e0b07c1a4004482103021050310008007015400329140090841402141c461149000c81e5400a0a4405480540d020520712515080322 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 275898174 1250 275896924 275896939
    0x10140108070b07080f031005041b081005100e0d1b1a070b01060302130305030c01020c07080a120c1a0a02180a0b030a02070c0306150303020d05040b03070f020322080705 74
    0x200022007072002ca4442000084031580c80307454000c08a50009107035000240c00c64a022841509101513494ad10340c1c0724600d43d00c04801343d480050001006405225140d000900042c12f13204150040c000d4407408a009001901035031000e840380c4030b0170340d104400f0b034008440303101d0706000050f1120040380000c0001c241c560301d0b00c50559554000c040051040394109075002c900101c020f031030000710000654204089a4583c07400343c40183c000c2d8012031710308c00342e84280c81001036100b4012650007a0550045070058058034032002c280c846900c1e070343c001c60fa00070308890240603c3c0c12400c422405000c1d8104010780b20605461408205860b081d80030b481290011b50411107880008103ca510140c400c6015850700c60314507114100e01c50f03070b402c000c0c041414002080052107a81d1010b40071280264201c8101003840c00040e500d81c0300314000e07070350821400c10004094a0241c1000442046544122841d00302c0f150402380c0722078041c480b4100120000c00b420813140724104002d0010346005c96061 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 275899280 1106 275898174 275898187
    0x609030d0b040b031b060408060108031b160315020702180a060b120705090a081e01050601020f03120c040f0e070f051903050910140108070b 62
    0x20301e001504446490240201c466030000034002d402c5108154000700c1e08125540c4506403c403008000000300d0301d0040044500801d01203015580b656a0100300c060b14107805103801c28260f018540a0254180d402d4100d82220791000b294820380a541d180e881c0680240d160181d4803000050300c0c0c0c48a16410070b4614428410810100407082e00d9003040d11050103000030120088440100140105004500400c1d00110007043d802403141c0e01c4e0004c0f894291180744454840d40300c40c14404029409019041c0c1004003400a0400803a588824564a005651400c0d04910990000c11a04c00f004400c84002c0d1500105851550b41c580c200768050100aa41e03540000707107144840e22030540308400b81c6143c6242c0d04070b0400e020620b5a03003140034080180000f202800303100601d4144841e140310700490088400c91440c030300d600d4440403a080082d107500c0f0780b11812013040030 = true := by decide +kernel

theorem cover : BRFrame.Cov 275719424 275899280 := by
  have h0 := BRFrame.cov_init 275719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 275719424 ≤ n) (h2 : n < 275899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
