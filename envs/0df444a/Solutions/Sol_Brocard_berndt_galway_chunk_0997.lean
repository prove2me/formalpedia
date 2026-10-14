-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0997
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:43:43.554581+00:00
-- url     : https://prove2.me/submissions/d08917e0-e11a-4563-be54-bb515f08e685

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 179136690 ≤ n < 179316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 179137940 1250 179136690 179136703
    0x60c030e070b0301270c050307080612060712060915030501060b28030207020301020307200d090b070318030b0f01121203090302100624050322060f060e06030d02 71
    0x500e12010b0380ba5a00308440024001c00503002c40018200c0482c14003046403d500030207100c240710360386094891500000060810700040d0450b405140d03200e034144040d517004035601d0391001d81d50a1008217154040601c2005103001da0269004519190603948c24500c12110141241e009a00a12030b45403100a0880540304000c0d1200800d40040500c3d640403416811114412086003001400d040d00c0c2d80200f402da031b00440c2d803480044c02424031074414262070b481500c1c2201e07540d030082001a4900002400c1c00e40c070f902800e0b0b240380c4041191010148130741d220141c04044007000129056491070100700c1403030b040d074010201107403410021400c01086080d02840b1038011403031074079080f005803041d40102003106080e401c42c0500d4500708810342460080700c0060000091500c04041141c03807080c04031001000c144100041003042c85104140c090111108a20020214040030920b01e054402403101c100c040b1400b80c1022000540c80342180d00091080e00164103860903031018140480c1c540702c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 179139190 1250 179137940 179137949
    0x20c03030406110a02040e03070c061805010e0a0f0b0c010c140406120b040e0307030206060405010806040b100e010e0601030e060402210304080f1608010c0c06020703050d09060c030e07 81
    0x203000780020440203101c1c002c900303d40c0c161201510054101a004a0151611310890310502d5100203030303030000c00504d52408401020949068910021141000515419a4070865040200079038904c62183d80751501100207041e900c100301841c543e01c0d03280c5000d075005658000040d518082c1042c440b07a0199a05405031051061218900b0382801d50035140015001030a5050341d54502900c03e41e600d651060070490f862410045807254910b19000b882c152004014500403828000100038881c1d0000c2d200780c0081d445040002c036640d500d1038800b052240c560090219000350000003074082030624203640281c80a0b40d041c0403070341000001c80d507070351007c0d140203402c542200342d0807016001404204204407244019203240c980d4a800c0e8514011146902d01c401e600300710340c040382070900c443d5003800509100f0f000b4040324803400c90161000b01c105401402007034000550004040c480c0e4115802c2c010401000c104814581c203000f8000d0070200900342c0828507145681c0c000c090001840f000f00c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 179140440 1250 179139190 179139193
    0xc060206060d0311031c0615050702030d030e0f0303010303030605090901021306050c01110c01050a1503080711012a14030c0705060706060f06031b030e0c010e0109080d09080607020c03 81
    0x82d40030355000c44100e40450f4a4401a0000340030f458040f822070440d1101c0c3e4015050080394141c100000481440741d030100d500240038040100d81c0060b10041800e42d00c1c40d89030300f000102e0a4158640d43d04208100b190300c005408008004400c25416070b0048007640d50a55500910b6031303455074078134200d1040009412071481c000c8810010315200340010601c03a042d800002c94081d0034249062001d4202c800000040c0c0d4580042195070385092141c0c00300010b21131540361569185851700d0b28644140c141c060300c1c0406003c41c2c12400c1e40101d0106500c075a1001c100017152050070751060751810440c0c0c0840b58400001003201c0c5070b60b00041036403030b540d000001a10300145000704102c050390013240103c44958545100140000c1164000d80040105403404a107100410070030000c01401038400000741450040524141030000440c010030140a0910890700e1880340c0041e24500e0413075020401900c07542c1091b40c55540d00c01c0356502100d03441c10444003203840d002410380c3c981c5081075041e03402d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 179141690 1250 179140440 179140459
    0x4050303040f11330702010807030903050405060a2d0207060c14120c0d0903080307080a091401090c0f05180a021314090604140105040f0e030310030c06020606 70
    0x2041c03800c149004603c1c0b065841d00c20f080003000c0440d041841620503a509504404d9025469140422900c1101d4802010032440d200070342d400681165000740000c420035a45541c0a420540190226409490002c0406843e40d0786d08500400d02c4891502c0c0105500d64482070b01c035001408004070046050304d40103803100c035080c800c040742d4501d045641035a088a007894142c244e45004c2c82001c000461002c100c559039044224810318000381c0c00030fa501081807040f01040817035500c9050700d80100f00c80c6010410783d11221041400b51130b414401030503050110741c800b51b60080c15032081808a20405100c4c0c17000d40d4034003000400000307074821250403055140402d481c2c0b149a40c40c990307014500040041c102580381d0140c00602442e50400602400014603801c0c81d454103403181640704600300c800340000c2030400704401860b08184502401251204000c01145c481a009101c40140c00d01c22030382c50b864038044455101c000c0e0311082e24801c030080408250300e440442d030b15200b244044e11800c0c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 179142940 1250 179141690 179141693
    0x3061503030d02030a09021906080609130b090c040f020403020604140a030b07170a15181107060b0406050108041106030a0e030304060920031203130f0503030a050c030405030304 78
    0x222016000861589400100941e01d1822281e10285020307052901000422442910600ca15440c0d903941315448110143c500f00212a401460796030f100006460050302c540301d4200341518007811002c020031220700c3c81d0420018003000200640e480c041201c09009060300c1d91510400c91181c0e0101a420950800040c860400100120600b2070b8020300414045c40d45d03603c500100c1c0200383c50350b100145005468104000701660841c1e08213003009402c10080d80800320014a0b88001d00c10f005030200030314008140800150b00c0b0058401d910030f4243c0c0c3e580d001c0e1404000030900b140c4600d105078901000410030703521407601c03a40b2440d070144040445a0759101004130320f400c002d0201c1001c0f603d43e844d401c01c000040c4080c500891040c0e1005c50304c952149403900000e8820714840ca000365000049032625640026141c441182c4a1315660f038a46440c0d15410500d6003010300070740301e549100514010003000000961040403040d8040009864100d500348061105440c00b4041d6031091001c01d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 179144190 1250 179142940 179142961
    0x309080306060703211e06050f100302040b0406050904060e01050310020c030f0408030a0305160504030f061107030c0507050a120210020703120f080912031f03020402070b011e03020306 81
    0x441d10303019040440c0d0000350741d0302c40300b003c04c1800205c0d0340b0b0a440d00c542c00d00c60304c1c100f40803c3c5d2200203c1c1c814040b01d402c0501003400000c1140c00342d403044c0719030b01c1c1d4890440d01039170440f8043c014558010781d40b540c031a88042e0081c5d0004c5145800ba500e49040050304010098643d81a05d0009011741b00c4a84194460070184d0014230000065010812641da4414200d5000348000c0541c000a140c07141c8039420040c00311000149a10300384030b00c00c0724081d40158800708480541340c1c00841400002c60a0422400510245450240c10000050303100d0a142d04180c9261256104800711208240c6450600520910320b200e18030186c0c0388003240034014a09030ba03078030710400c8492044402d52543c94403001d00c83c400c8401d442e400306114501c0c848074994401c9495034407003803610040a062800c03410b4408240f000408071504800b4480001d244d00c003a0800d4800103640052040d5140c50300e03410b140c50317552003e210b030040c4600481c44042000c070480c40d015080302e03002800b43c8169501e45070b528 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 179145440 1250 179144190 179144197
    0xf15040b060907120204151e080712020c070f030b0901060b090607060f0f05100602011406040b0d080307020318120a141002030406020a09050139021806010f030908030606 75
    0x12013405085003040380c1d0703a04a031002d03100411482c0d480200044a82a000c0d20764054110243c0000c40c40400290510350070014858100c2c00501c0d10901c59031107052010000d0258500300d07400d90113000000100d2111005440069070b002c0e042c401d86607112200340740c4c201c2c0c0d0303e8400e407d1201d205200d0300e0713036a2a100018103451401400007141155001c43d5860490300c101d0744203210389550b141032003012000301c14000c003d001c180c0000c0010190701c00011610050040449101c2c0d41c40c0c0d0030300007254442c0c0600d2015164481c1d0015101e04202d40c02a440350040e0252190580c2c540d012000d541c903280c0384000341030b20b0410280c2458003290300c40c02c01c0700d1041503148541e0312030b82410500d4600248001c0d8400e81c020640140c0325120424014204455640007070304100c0783c907a1035045524404000c500d42e840201c1e102424458030324030034185002e2404040e5200754820000402040304458403407048009907600864260f20340e400f5030891340001405840da15041c0009140303402e02174005e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 179146690 1250 179145440 179145451
    0x403021207052e0e0a090f0509100b0108010e220f1a060f040e0115140307050103090c090c0207090f020c061b0a0503100b0412050111122707080f15040b0609 69
    0xb10805c041c3c641010105031060074410b41c0b48950342e0703010460303441070a0040c051400c020305024060b01041d0000244500030601590040f00d1140c80890400d0180c01c1041d03000904041804841c2071013424540c6202c0c128540c190341e42c9203c101c80d50301c81219048624402d070350003401066056840341c03d000c024105902e02c101b06640c0c0e0100385102d14101a0404000d001e0350f01410540d4900d0020b150030000c01e41d01182c10306040100c2e010005170345c99117402c00c2d00ca02034000030b090100717910308070b28114855105c00c0003e8941610700046041d02d40003000741c069a4001c807046501e810048000e543c5000900480b080030610034444640e102c0e17401035402c1040750304241c040c0c98880b00880c04a60190b8481d4980c60712400b90b1500f000002e005012040140300c10076401d01c1030342043c580e80000000c2100580a500215500152041030b420040c0c1c201d01e1001c13074201e2601c0c0c01c0b14968480e0416144c3c1d0562003030455a14003513100810301480b66920038104002d41d01e40b1000d11540000c080c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 179147940 1250 179146690 179146699
    0x4060b1603030b0a080a020301061401020a0f05100204030303020c0c030f0c010509032805070b0304020a0905091014011703030c07060b06041706250f050a050403021207052e0e 77
    0x24041c0c50740c4d46000394004c0c02450028094001c0c0d00c3c81090708488a0b9030080c9154141709407000b059a8011888480294204403451101c404500d0300c0da0416a11100b0b4041746032020402100b4580d1641c05803818420900032110700c40c00139410507546c3c00002000c001513034400c2d5000300403940304801900c50b20101030120b035810400849052207621602c3c3c903010303002160242813001c2c8801001480020500301c154189503040c0fa80104e01d49407107038090028070984882c082028200b040082d030030604000c101c10031200240302008020600c080c85860300d03659a4070780c1f2a40507040407046074000d071207800c034091800b40c1ca582c1d500702038000c0080c0315502a0040c031001a16101d80c0316400d0903450a400508224908032041940c41c50a80c0c0f1404100e4502e044e04400158125403503c0a1400d039051441d25220350950464440c0f103030b41c00c029000140800f60400840d0005081810344d00d0031100303140c14815610b00c2240f5001d00043c900130612030811076030085402107540032240a000351 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 179149190 1250 179147940 179147951
    0xf0604020f09090c07020f010f0e0d080c0105190f020909061c02031204031e0f031202041502070807050f03060a0c1b03020a0b01060801080c1c14030406030b04060b160303 75
    0x2400580b0030071045459044c0018001403c03811490004040505420242011100620000700050501c5001030030240a070411561700c20520640f03409803003040071a0802072050749408100c440801c0585840c8222107828062600c840302824000d5408203680504110f0240d52403104000490386901801c0d02c1c0b03501c02007640c0d800b5880511880b15420400c2c0c000c140d8540ca18030340314241c82c20248001c958800040003a50021b0500b6200811407601450088104030707034401c182c1c00030b1285510200070540101110440c1c1034021507443c0464040e00162040140e80d0f006000340300c5c102156040e4141c0210340040c1d9030407030035800444801e03280c0c50118120f200c42c01d1810340d55178031003030240e01503800008458100900000c15034050b0bc50391404d21010b5140003801c960f40e000c03851aa520440d17102e0510056000706400c80024150002d50480820070402c0040340c03030b40d12078001c440010703050041c401c00a0419000b81c000301c441450a0900d80040d8404001c03103030032826001c40400d500c8a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 179150440 1250 179149190 179149207
    0x4150315030f0803010314070b070f060b0619030608010e0705090907090603061b0c051c140403060204082505040209060d0c0206160315032406080d03060b030f0604020f 74
    0x20322100d02d0440c41034084990325411401c200a00e0030b6040100c83e02548036400a202d0798004505550b44076600c1056a00198124940140501200c0519980088012861441012020181240c01029500d081100e2078640d54500e0980d281d09405ca192503211801c100201d041c10743c02c80d54032400394170503140c500d80c0350010136080d160701c0e41c03050b10100c4c1c030707180c125040c000e1002d21490b4415050800c880c1c00280c9607a855202d07251545c5c0c409150030504400d00042c4d0040f441e0084440100ca21640c1d101e4903403078054025081030040492034400c0034810000d074800d5031b445040c3e41f0320404610740040e20f8001008060740c45250050b400081c00d00044074000c0c00790240103805482500a44828a02162000c8020007543c680c48105400d00a5a4030f00740c0090110209481c0c01c00710620340d11841c0c000b1042c852203803566031000b07030b1703e4500005008100480c80c480c80082c295800d002240d5210340c15802c0c0e02064805020051490b000b042c082e1a25a0080030b46103101c104003410135151 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 179151690 1250 179150440 179150453
    0x8070512040309051f0914060c060a2a0c0b06060c010c03140703060b04090b010509090106020a0b1006080a2a05040306060e0705040e190c230415031503 67
    0x2074504034082800188180094944900c13000302000c95105a02412054000014601005803140b114441c46020f2001a00c0d00c4550880b0040045c00c030031101c0e14204644160001c2509003642c1400c50900b43c000344c00003c002500b110014182c3e0b6410b02c107a1a1602c506611680c081d0516a00c035004104024502000b0702400101080b01c0d2800550b034510000e121139001c50007414503040504d0000240b0008101c00151002d44010300300000700400d0150042e1164425045950f600a01c928000a0200d0f400140c003041148141001c0d05140c07240038121344468203500400022800071000904840d10980c4030043c1e40700b248100c0e0700c85144400000015070a228607101c00a100080d0500501c03440c1d01403c00146001e00c4091018a00b0240042490282c0c0c003901209168010100b08044031000c4c1c0282c100c890882c0c104031418444201602c5600301901a100c0940c03a8150042070b407908000703890851fa400c1340c4001c041007110340c0c101c0050160080005c54a1400e81c80400031580 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 179152940 1250 179151690 179151727
    0x1207020106034b0b0604060b0f030106090e07080105010c0f0209010b040504050903070f0b07030209040219031a0108010b1317010c14180108180105070e040617030307080705 76
    0x8211001103210754800c0f15410314846140c0101001c8003030452501040b000c040e4989616003054441c1c40d04d07180e010009003c0e0180d540203200924000c81e90700c5282c41c00f03078002c5040310301c00d48400c80720395904c50a071805107500300c0341e89002c00ca981d1700401195004e100751100181c4500843c030284441940002d04296081e040050617050200f000d10043c01e0905c25503800c1007000c00103500301405a130360009020040080200001c1031074001c14540b41c001d4060b10603810004005640703900103041c8000c807003850380915000290610009419080181503400c02008041e50303001307181da00303024606006610480170094502c03828580080c0c10087d40700c004152100b810b0003c61019280c02000704081e040c0c0905004044c400c000c2e224600100403004402c0c1d04080c00c02250326a81e2035480c04c0d640032000080c007420350a00040120700342e800004001c0e450b100303e500300200780c2c94000f801000c41690080f40030680c02000480c0f0704e00d0080060329030001e000d242192401c100c0350105010201c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 179154190 1250 179152940 179152973
    0x6090609050f0c0105030f070e2d1005031003110d0803150109051e0103110f0c07060813020d0b0a0213060c0b0a0227010323010f090b06120702010603 66
    0x40204210034002c1d04203112501980500f40303405400c42c2081c0b503c0c8400c108019088400340402c145109400b80c640c03800b000310603c2c22840000300803049039810305510015422007031055031482c85480e0114003800035a8001c17070111410403012400c0da0f4401043e000c44586003640000b121707a0010000350f044004503c2201215082404100c181c0005404c3c50a0b54204500c118061034401384c000c980045541c00200703007403801142c00901403107a00300740c1c0724a602c0065035440c002440c1c04010130000e0700200300c4134070703640c1c03103010b81c0e201c0c03c40c031028041e02c0800a502217618401c540100c0c8002c03041c0380d00701c44803070030051a08501958500a070702c42da60200d008590482c0a13003060140c1600d03030301d0b8044d00c0090154038200314682c8040300110ba00360a40c494102000c00400640d1103503000d0b00c905080701130100403001d08911a0400d0300424442c42c040005030640c0030484100742c1c0204442e200014204a040088415000010600080a200c1150b5881c031000011881161000310b881c3c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 179155440 1250 179154190 179154193
    0x30c020a09090606030c0614190507020a23040e0a0b0402180405061501020303130b0901140c090301110c070b030a0e03030403080a05060a030c090c02031608130e071b0609060905 78
    0x240c9103184c003a142000b19070080041c08400008080c410842c0ca0845c1d09034449c841035203040390003405058629000d00c0da4041d4200310200408036207041c003030801c02070b84000204800c8003240d01400b007105840c0014000301854202e8003000000070803045410360004e1005114103e0039100011403211580200d50942c1d403580310308140158946a140c00b142314076020f102445c07451034255141f14030203e045a0003050070031001e0000706129000c0d40414004c0008200e40403540c10404041d5030a40c0080076401e22951034400c0824100900b03100f10703510103120720060200c0e140f6002d880452500000c0c490751040e522102d104540741024002076200c3c91094442c401c1a003481c02140701211402007542e07000b8191110240003140e2284803040c11950146000310318409081710032801c0d409013140c0d22051420707109140d4100103201001d0052050101e001441243e036510611042c00300546a041c00316040d034000e5020000303480c1c60070f110740e40101c0d0007003944042540d40c003048894041e0103460a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 179156690 1250 179155440 179155451
    0xf0c1903020f0c0d1b0203030f0903010902040c020d3504031206091e05061f05090d08040305060702060c030601050f0c030d05040c090905030d0e010603020a0b070b07110a030c020a090906 82
    0x944c12105840180700341c417004020600c21980429642e101d400700100c03501d42e000c980b0b070a4658003500300c040001e60107007080c45031109013407010790350756100f007280004500c84042001c2c9070302e400400c9400307540581e003408200211180008100b90006070095041090f40400c0303801840c0740c1d00409006220302171000441c0b5a44465112041203290307020b0203040c0c00c140a02407e42c1c0c0e140d00391410b00d406d0821034030f4100d05d50002501c1503c1644081600100300121500038840424003910489000d042621160703a2460b20817a21480112200c90b1031a0742480400c0403944990050700004000944191034190001c0d010fa1460f0408038901e03900365210810042041114051034004000d066010303c40507000b5a18140c0f05d00413505660a1a9030f203c241c4000f02da025040303070000b150082c1200d01c0c41c0c0d40366100201d195020390780a6070f00c8550030b000302e10b01e144102082214003201001804280c4416078085502e0421140c00740d80c4150280d402080502c0c4d24030440000502c11040000d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 179157940 1250 179156690 179156713
    0x1a03060117070f0302061e0d0f09060e2d100609050402040e1207061806060602030a0206090c09041b0e010b0c0c2707110a11090f0c1903020f0c 63
    0x18001d0b1940001a901075142ca0800c0103072200c0e030944052200d403c0f170520701080308100d502da103401030030328405d0381d00d0500b01c0c0c0d1041807410b0b40c4102c507800d0081c40280910400040d165580340030049441882c0c40100c40c0400f542510140c0f85201c42104005079448540340c02c6401091341c000f9040140580d9480c0e003404214a001e200d80b20f0603071040b00c09024160f03080000d0002c0c5000d64640580b09a80307030a4030300c14075010325900c2100d0030391028040203141e40358440290350390002e036110030161040d403010403100c0c603000841d03075840c0c14000c1401403142e98030b980e088026000c680140030481030074800400d41c02485009203010348601c0900c02d4a424004450f1850541d41503003a9021b08100500ca050a186400c09480700303654034401d6000c0c60f12001c104580c00c2402c03040b46881402405005410040903000592000800b01c60740c04031034513405c010706071041068a40300e41d9400100310142d182d4104c40c00c040c000840c1800e00600705501300311086500d50014400c098103410245c0c1100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 179159190 1250 179157940 179157943
    0x50c03120709080c01021b010f0c0b04050303041403070804050d020f040c0e0114030609070e03150a06031505190c02070b040b0706060b040b0409021c0905070806060303090307091a03060117 83
    0x101500c04c24070040088a0000c0d041c4100c00d01580007050400070034903014001d160140c2000800140c0c890215502464a130a11540720f4000391400c650101042c1103804251100209981042d0f402000d0301e4a406d181c4020400b042601110032a00306c100c58540310416607403031284102031034098450b04400414440010400c002c070a404c20050641442400b09a80311250b5156000c8298105414522030280c000303840d103040d0700440340c43d040340c0c0800c0019000140e084402180d1280c4a000700c01e0724a81c1e80300c8140c4100702d801c9640801c0c01800050b072800b00340c00042c800410390042d560056141e0680001651064001c0038808000207404400c201c0c6611880008000c0481000d0903d41040ca0701020303403149102e01000c40360040b5a14154148003060311a01080c0a003041111070414580203032100c5407407141e48401c1c000c49000815509000c000c4a480c044000c018007107030b07420411030000501914240c0011010000400401c6450030082e05010306107000011456503211468107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 179160440 1250 179159190 179159203
    0xf0501090b130b010509060301021e04050a09020403020f090411030a0b040c0602060f161808011b021b06030901020904020c100506180c03071101151e030c06050c0312070908 76
    0x20100c4010b54050080864480940d0b107041d294100c54200743c03a118500041d02a015184144100e10301d40400c1c10b1035003040000410440320191000c8201d55036030071200d000c0307000d98400a500400215844409441e02c1002c0e654024410150955040b88103000b003850400500e0341281d44480c00c1051200307100c80e818036200104031605c010149442e0034035001c0444007028040200340012500b0900d00709014442968100341c050031281e10f03841c0d40d00c00a5001e4001e101c04680980c4440103a5500b580c400b0402d07021200c02005080ca102c00c0010a00c403556000812503802954284084112540c45000030b005110740e0000600740c0e4881491001c0840b5005402c0d148100f5102442050710740c1d00d1415280d1120445008039129600d003030043e9908019000c00215075443c015112016040702c4280009a604039403861410010100d101a4441100d0001400c00415181c04110042c800d500a0105c03a0070501601d007402004049111104000c1ea4000040b03038030b0030000e100c981c1003000071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 179161690 1250 179160440 179160451
    0x901030506100c150219050301030b090d0e010c0c030f11090f150913171803030c0c0405040206120a050f1f0302100212070b01171203060108130f0501090b 68
    0x71442031090510007400f40a11034000600d6009211101004c50040d541641c0078076104000a01c2829401600102a64400d000c22651100c1850104d40100000180c80d00d42c82d0541e140c240e10070756110019a0383c800c1c43c040444042044078404000150100034401c000f610030603032044d801c4d8286003000380c4404003d005101c40340104081102c510419280c6112644007924051895158565000640310b45440003500041940c1d03d07081c091444400100520b50004012100702c4109101301a180e1040c91044240c80c0d000007011109440c0a510441d04144014402c40ca411000c46510008640441e6000e0b0010764450806c1800c8041c8400d042d4002c075641d2480c090842c000ba45089010f40703d0102074000c600040c0c64881030b074001c00c280c82c60480c88415090b202c0f2442c2c90410b41060b424010396000c01084d070310101b80c4950009010f000030035415038650666548000450711443c0040403000313580801f40c0322401040d071002c030141d03403d4040d030008035076004035040c1f181d81120003810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 179162940 1250 179161690 179161699
    0x161403030907030f060b100809010614211504050a03030609060e1314031606110309070314030f04090b0103050106111906092307050102240709090203010b0901030506 73
    0x800c0340303070071010500030142c0c2e5108010030303041c50480c1002c500410515499507040b500c103107801501b2079001494503100f945418003d1004c1900c80300581d04031001500d040390410031102c00c06551300240ca900d000300c909428110740d45140514a028042c91017070381c00396059000038240c4000d00d40e0600803440a00350324401806010b140c407190680540b0010035a042042e2020468010409041c0c60082c062180a084035250307480c02c0030400d149120a50100c40c994a418000304085400b1800c0c3d902c01d400e2480a0140c0764655200c040c1180d81140c2000382c0c1c1d00003000b880c0300340d00400c0007400141c214407200281d0f08451034005800c9030b1040c1c010200780200524840042400042c0790040c440c1303c410151107010107480c103c1d01511111034014600c40f1001c20301203e1900400740804100c081c901101e0000e69101d005a0f00d9024200c580200302ca83d100d006144404d5914140ea040700061030103e204565441d280070072a0400e03046020001c07130004210200b0743e85401240d0f0440005c48 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 179164190 1250 179162940 179162947
    0x18061912121e030207050a051b03070e01030809060705150708010e0f090d0c06140f190c0e0d080702040c030e0c06040815100f030506041406150f0a0b161403 69
    0x2854200814900c01842050340008201c002c012040c4007c0c40119401001c84410300c517954058904e0090b445007203402441001303030005030b5903919101e03981200d400160541c030b002ca10006120066200d044140d8613807082c201d07010b1050f070310b500c04076200c0c52242d0f40b4560382d035040042c0ea00c880b4001400c042d00b080440e0040c0007080c2d2010685454849d45070401d18801d00c0705140c0b51001e408030b10f04903015484601e007009030300d1604907640c901c5000d01c2c172030001c06554041c08000840700007166050004040082885160130038151131220940101c516501b88a0a42d0000781520740551407000066116410384080f00c20410540c03c04c04021100b15041034201a41503580b80108442d04001d8629880452402440f140a101c0900001d048400006881742480340e40d0744004d840840341d400906580409200c404641c00c1d010b50001c070074100c08407505004018a15040c00d1841b9440503401000040034034800b070050401000c2c60380117070180c6600e400c10454407105140a074030341c1e81081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 179165440 1250 179164190 179164217
    0x5030a0501081609150801020301030501020a030e060f0606180306161b1a0711190b1003120804110a090b03150f010902030c0d0207060902090105040b1806191212 71
    0x20000c260984050100002d4445170305000483c000e07419074040d00b000c2d4030001c00401032103010f40007099040c03400d803814032601c2c0e10030785002c0d41c1c0c44048684100070004000400da40d4909031000b81102c1c1440861030718004080400642081001c0c0c07500c109034115400c3c0c0c60074040c2c0004d03000282054032000310a282c0c03540d0325075052415221384c00411164040c0002088103004842d0001d00700a07000483e040541501d015035010307100440107a0304500c200e00025102c1c4403032150002520350208420b00b142d00b002c4000c0d18034520241046402d072a050b00005080d4844441d9040200280301000c1100981d20003414180700701a07640241032800041002545803801c03803100d0448040210042ea00c0d9030305035100c50540291602e4418560000406005114468024090741b60003111868600c0e642c0d03408000483d20b12020251b00107402c01e24a0882c580d40140c459400300c0302410401b001402d88040d441c10702c510303411902004030048412420320102030000e0303160308818240780c005100003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 179166690 1250 179165440 179165473
    0x140f010905030307030c14031201140603062206091811030a030e150705100c0e0d050607180e041a07032007021206070f030b060304020f010309051c05030a050108 71
    0x400b13402409215000b8562001c000380c4403a079502501c0300c10182c0340c03a0440340c502c2205c05c2c80700b8880c03101520107142030746002d840c10104a07401510001d20540700701d090354100354203140f0b10886469a81c2d588940000d6000114010faa44101d01d50030310321102003080c900141401d14640c5003a0080c0d101c0805000020b030082c2012040f660704132405200b00301c0802c00c1c50191b1091407401405070040d03400c42c510428482d0400c14458101c3d40360300d4481d1102c0f43c140492211901c101a04940c0503c000c00d1075640140351104100c224031302500700150300c03000c0d5414001d801b61000c4466040440300742c9d440e091a03c040c01c0c0c10100030718043c84040d1441e40c00b4200310040718094083c42d00d001030840c08560b20852094040f507404402e4075007924050300c002d800307040803c001c240440d0030b00d94210780e14580142100e11840e8003c040e0020442013200450041c0000d41085a4074414400344400c600c00c00c4541c80c1d666006643c5081e039034600f4a11b04010340d041a8400d440990040099400814a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 179167940 1250 179166690 179166697
    0x30b04080309030d0c020604200d060b010507080417071703030105100c060c030b0306011e17120408250b0702191e03060c090501051c020f04140f0109050303 69
    0xc00c4891107071a52910703030b03a00c1e09501c6460303815005107281a1010b10116000b04019103e28000d016008102d11044020242c1205642c916a4015000102000050043d5100f0302c005141890428200b220030794031031000f60b10a0304072400000c400500310305801010010140034041e28800c0c96030079100710b0140e95a9000600036140320300b8204031603803480d51183d03070000c0600d90040c40502a241c0d101101800800002403180d029014180020030713928552803042904441c4550212007140c43c1440b02c4041001d4441c42002e10300406015a1816034204041e20140c01f01001034904e100044560030035004204040ba1260102c4200c100007000d42801070300e0120341c05441760030300d8824100d40304154008035004205144040720058283c2c103d15600c00c3c099030301c1054200030300040d443e0240d40d07000091081d18001141081106140070790b920075280068104140903081c0340210540d1a0f5035003164104482c4804d151800c9011032410158a014202080c205040254200000700b5281d10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 179169190 1250 179167940 179167943
    0x11a13060e01050706090b0f06060913050408090a06120e0a120302090f040e0d0e060405090112080c0709090302010b01182c0106020c12011401030b0c130305030a18030b04 75
    0x34005018000364020340484da0358550021040110241d01d282042035440141d5800d035000450300c0c0059158141482101c4514000910100d030745c9281c0745241025043c000c0086509520522121038982c40d1400041c0c0640b2050301c1d041c1c3d07d84603a100c210212003d0201d4020310750300005c856004204200361084100c0790038500585c4d1038062001244c03210010402c0a5002071420014900d401804521300c0c9104409a94440e06c0ea014013041103480c8c010303409215409807103500100551908480c40540340391250043c0b0342040b90f006411424850700354403100321507450319801c07000c05034284a11003c030882404d280c1902d80020310120080382160140090160510414000d5030725610310196100244442c0c2c0c2c481c2e50385510009459180140c58103003d1207209442d01c0308005d06000340740700c000c4514198000c9a103181c46540c045940038101c016400001c0000700c4108010000390300c051030180008565807280110010540c0355250000300d03001c1c841640a1000401c11205590802d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 179170440 1250 179169190 179169197
    0x2010f0c0206030c1b0f0f010b04091a060d0609110f010507120f030207051204030605060307061e05070210111b03030403020f0102011404140c041404030305070908070806011a1306 79
    0x4101c01d201d107071708941001122461611817003d11004210001a441e846010320364001d11075030072020203000a441000200800300e06012044180011525620a60000d001080440e0684850710703840112076486c030080c0c60104102c00d5a200d5400d0110f680c012054080c41e0140c0b03407141c036031a0b001c0c0e00d02318101c8220400131640c5000c0380c42c9105e078050350b0000307401c242a18018100c0c52808480d50384544401c039a00750400c40001d08a150202d0325030700302c034081d0300c5520130407082c50542580040c108000c5028007000740302101c0940c681c0e03051140c1b2004d49442e107010003052402c40a140001c003000d6200444c946080074082600c01000703580807030364141c1d00004503040750801170b4007400282d038902072000d0001080105100003407202416201d4003d0030758040a41315400d00090f500205101981220300b00086800a40700354020f590105491a0042041e91219021800d01e00b031548202c0f40c0c3e42c481001071000ca001e441502c2c100b40e6641c41c8441c605600d10303030101d080c0b15040c421801030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 179171690 1250 179170440 179170447
    0x170703030c080408180f040c0207080c0d080315180f0f06091512070305010c1e05070b01060c1109010801021201080601031e06060801050c0703021b0a0909022202030402010f0c0206030c 81
    0x5e80c9038a05c02ea020a00c00400500c1080c00e10400295a98624810200c0c14407a1502040a50520440340100301e50401c14107407442c0d0f1802c11007001e04e02c21684064010782e03000a009010303407000904034001c540070800000c460a00c051080e50640014110074032900d05c400034001e240400d01b48504086405903207031070000c2c020358504c5090410380d50014140354205202140100e074400c0c944502c6103042c1c1c010303100c01400c02000b1251401180700091035801c07110f005009407030003204d41202c05486030035001c189500805c00700e150814283d0140324203a4000c6090b90941080707101d254050010301c00100714a600d1611030403a170345039004034980b40300d00362100c000a0003c07640000019000f007000a004600b40565084040ea100040135030040c040e20030455218604001101070120b0024203600c1400e090820400052140e5182242d200001c00300c00c501c04c041984105081481c0000c0060726031510b80009450380e13074009032a408000104050341c1c0140d80e001c05580d08110b803101d1603500c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 179172940 1250 179171690 179171737
    0x20907030e071a090a03030c030f02061005060d18060501060e06090a050409141204090e060907150c0c0f050a0509220c17070f080f070b07030c170703030c080408 71
    0x1c43d48141d2440c0c07500302c2002e100100505030808000e8034894407c0c2d450b218038012594040362501c1003a221203c2000072020b0810070703441d096000c0c2c569812154400a44094034805451a801290300d085801940722001000b06a420581c0000242810b82d0040d2402c3d02800c0020200035590090700d1140383c0d103060240c2400042301c1052214042c0908a410600e0341e102a540726070814892150114200303140134540344404180580900e828000620040d401c2981640d0f542c02d802401c2c40412028403c1680865800700744036004000425000d81c40f14101014444841140d030003043c082c410600901c140f1400d560900b00d501c030395880b1715158008003440c100b4102003090f404170041c41c40c010741006034400b010a0301821a074407080d80c1c0710007682c0c8072441c6481e002055030500f59a00941c03002c0101c091103000620850b8801d1074003e034140865030310f5407600c80308048a602d55440108d01a0105501403140f00f0400019090208842c606a61900d06a101e0911003c0340504130090401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 179174190 1250 179172940 179172989
    0x504060603020307030803010915030506060d031103040605030613061a070503070b0108060613050603030d150b0f0a020712080d0f0e0d03020d1116081b1603020907030e07 75
    0xd0350b401001e603080c04e581ca003007124081d002805804912850054031505008070748402c0c00403217a0207230151010b40e071100d04001d8100050801a002e00c000e0b10200075502c0001c0c0010310242c0080d8960f5500d07400c01d101844920020200ca5503011842d0480c1886a0b03030030451540400115a00302030343d02c14140c41e05508600a00c580181050783c100e00204501c0700125006102d610150b8135281000d20700c010321400d0322020703140690150401c000083c01d00d480341d00103031482d2041c042450001c07503681b003240c112070380801c0721004010404514450f54903414031084000741034081c101241d200c00c0b074503030342818072550342030502070766491000440c9000301d074001080c450300203016a411b404100e40064081d510208420042c145404905881d03e44110305076600000c52030301d1340b01d00760002d591f204600d1380f0481a0301c1900746408942c44001004200b10b034a1403119040c00c090300380c0f41d0b106001076240041e0440051500348a4000900c520010f012000c8a684440d1034100d001ca0640310b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 179175440 1250 179174190 179174201
    0x3090510080402130c05040b0f2703100c050301060e1201050708011d0f0a09050f060c040906051c030302030a0b090412140a02070303081009020c0c040b0121050406 72
    0x864200e4024050040a80e40084603640701e01d00a0b940d2904030f42c41010008102c1c0c0821840c100414024881400000d07400720140c21034111854800b468550850002000ca0720b12400c048640a82e5120201d00c1e82014420443c1c5031841040c1030000c28130f19400508540030501400080000ca070b203580920b0b41d82c4100200f005029000200a2820580c2c001070025030240070b40210480c40d4110803030b04c1c00c54030038a64411005032404444540f44d50301d49c00041c0c0507194050715035228102c103981c80a40184001c50184c0a20345020b543d50340782102580c281c41c026440789219010300400c5500c16030381400f4100c01194103140041ea40d590b02d41142005088070403030550010032040400c0b0810402c900381004140481d141c02004400207060540c140c400c6258160068000035010000203001c2c01c2000c0d0008800d00c010fa405075183d010301800c80e0001c6440c070f01207502c61035902c4403030b062921410080d442c0a20b000d100c00c0e0041c0540001081106480003000c2e55142e002800340700d0a944034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 179176690 1250 179175440 179175449
    0xc020a0b07050f19230901170c0c0d020a20060304060c18030c050f1c08031506030403020a0209070203040807030308180d0801140414060607030e040f090515070207050d0309 76
    0x500080381504800801c12456028200f05c80c58240354580c1e60120100242d4203244016925640381c1000c140c00a9400d20f800b42015030080c0c02030000610328001440307035031200da1599006010042003070802070500c40c145d0400400c4007100f5200142140c40310070440c1e900981146010840056103d411100313095041c40d907003a850581a03010040004400d0040200c40c02120051511440d0000f0007440e40c14500c000d0240b951000d44c0c490002d00f4400113582d010010100381c5800e480c401000c1100da510481d011001600425001c1c02186884814a42c0000706480214146030610360110b030b4a1340680000740500c0700c52000034040c00d1000901d542d06003031810688041500c4014040c2800c1c1c3c003805208500052503480e014503052a01c40c0040c03aa02101d00007445444601c18001c1c90341c45060190100b042010503042c0503259801341c540110501c540003e0080c00c103042050604034500c000000503030a1350140099140c2c00034442c400d441045600505030f000c1c0c1d14050712811000ea02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 179177940 1250 179176690 179176717
    0x50a0207031212050115022805060c0d0e01060506030a0e07050a060c0c0603020702060a050306190b03012306040317070c15090501020a02180c04030f0b0a0c020a0b07050f 75
    0x108010210b5002d1000940074181c6202444566201c5440509003c480145440180d200d201d05866451640c800344032001d51000705c4007601d2070b88e80c40d00b50070100d08036140143e6050001d030100340c2010302c1c8a8903802d024200300810680f400d10001a01511010340b02d00d903116124028040c2028060103510000d010040c42c4000459031181e010b00b002264540640d4030303007a1b10100140d501e000c0c1c0200c4100680c000d009516002d810070050705d0356000580015082800a05224019000e504007507020b0512170240b180c496242c41c00c030006c406800d0700d403885440450000d20025481c2d01c000d4505a0350b118201a03001042b5103c030f03d2580c0105807000d420403240c0302c0d0000c2c04090901d41d04542203140e86c1c80311500341e103800040ea5190701c0b82070001d40240d00310780c0c11194070060360b03c1140c100d040d00400c0c0d840c260341c0780c444490900c2c0c2000140c03101901e003000d0200960f058414440304040070300140c28980059101c4600d440f20051400040c070000041c041410302480301141c0ca18545140e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 179179190 1250 179177940 179177963
    0x130b1b0102180306070c0f0206180405090a0b15060306040b06090904030e043b010609020c0102180f1804051005010611070b0f090f0301090203120d0f0204050907050a020703 76
    0x1501c0201002c0d00b114854001c4c02441c004c03440c494441c01d000c0c0320240d04040c0d0014042c4203030b4280880b641c00864601942070100c50340c07804654403030042a0040c000c0d4402000c0c403c4042c1000521424007900b298001d9070305404804036611070710705403940f1a0302100c001994800704004580503204424250742d11403641000c020806402c08224200107a0a940c01c00041c40c80b500030504480101c00c554942c18102007010400f0f04c5104001c001c8001c0d80c800204400c2c5d039900c0f21201fa0b0700245a80704403650007098068410b03000d07030942065007400702c960300310300100780003c0f0340400b8a40d00707040010001140003406010f010400c150400e03414240c1040590381d40c50004000c0c0395120040b41580c02429400554180c49005580300d000f05400c032a80380219003002c0080040d00c03003510300d425548400061001d03075024010300300c0c186002040c3e01e03a40c01804204d201106d0703600c45010f181c02d1040c0f10510040d20382100441d0312800d9801d206a07a40900001603140121a0b84004c25012031a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 179180440 1250 179179190 179179207
    0x1201110a0909050106020304210f0b070306030b09010b010f050a03020f03130b1b18010c060219121808070813060e040b0901030b060f010c080a23130b1b0102 69
    0x8907100215444402d040000341d032181804c0307880344900c1c400e890041c030600c10040219a80b20b09a4172150b4800d4940301307549022560b5001d5480c40c11240240441d654910130820711851202c00b942c031140300340c0200280800c0704006040c0e0030100d4026410400040f4000310071034029070480744888032550f07040307883c0d11345602070110040c010481110b0f44042c103004a2900312034a15044402c0d140ca14481d810912a20a03480316103031152103203410400304681ca000030859a100401019591450340054003018040290511070060700c0380002c149050541401c1041c1d000c0d030605155400324603207542e003156041c0100a4014100040e0714107400700000a011500030001103c007240c1038a00307008040d144410030060500904c0301401c0315070f500c40001d80d01d25020500d0310315200c05040031840d1034595283e87c2555081240d0020104002035114850b1a050f10881401400344503c41c600d0104590083e480082c0d16100e10041c0800101310f000750380c411001120048880b48000f19103a8812 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 179181690 1250 179180440 179180447
    0x11011d0d082e0504060e0421230901110619051506190914060409020309030705030408070e1006020309040f0e01180204060902120415090b1305070b090a03021201110a 73
    0x10f1240c5031245140100001d010b030004003150b44107540200402c50101d9024820500104000509900708564280700300300744240c4041d1130034410f04502143e5103a1851400152842c003170392045480c5079000c4000c1000e050490500c40c08266040382002c1020b0310b80b02411882c002d08040060b03400440403a4010229504010203c035090140d40d400c0c4c5025a41c201c002d0010221041d00780e00b00404020a000c0c001264008541001009040b01d00e002a240c45150441d00709400100568008003001c0140881c91a04c450f0840c021011004076245080350280d501d22820060070302544d1a00503620801c03a00b0f90001c1403c21004000380a642d49102c2440c11503a881c540403449149040d10115855030280b003a1622a05040ba803c40d03c1c0d10b650319003580b041a01e555441c0c0031500e484041d40040c10040505010b260301d040481d44101c02443c003207007015581e0700442d500300e805100c41552aa18103045030700f100d8065a4903000594801032840c054201c10089511703080c00040d84403510741d030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 179182940 1250 179181690 179181781
    0x11150304050105010f0b1209160f0611010c08070806031f0606021902010804030804060f02070807060507020a0203070b1308121b060f01060809030c070611011d0d08 72
    0x101e400200943e0380c0b20080c000149905019800f25854113004000740501080740c1143c0045140044844040080f83e1144601200d6040380d03c0100100c0b000300029604041c8616040800100a1003a1038181d1401091403200074141001c22031480d02160041c2c8040c8582810442d0440801c0940440d280804018000c00d10801e4018454528003000503000030a11241b0303d0760580d501da09589964404584e0104d015105036426540c0b048801c105075150710040003500d10800c802d82d00c600b954104801195402450b28056400820680b00140e80c046903800c25181502c19444c0c0362981884800fa81d00003a0300242081d20031600d00300c4a010800d0094480c2c03981c3e4840c581040e0840c10151912201c083c2c030515509600c0c2401030061b507006180072a8008607800840341400041481c05190501075030110780030514020203800969800c0c040c3d50b00c481c01d64003201d040542040d11030b9540b42d00030510f4000700001d0380082552039030801116200e15040400011100c0f88072040c0d60b08221 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 179184190 1250 179182940 179182943
    0x60f060f0b03040f06051b1204120305090706030c030902130911010207060f03020d090f030804030305160518060405100e03010c1103090f030f070f2c07030911150304 73
    0x30204000000c800381c40004407441030740c0c040745403a2140031a80e1aa03000d0b0002914154009409036400700100030804090480c044844040103c14146400c0032222040c004508008040c00d19080010f40c52000556030b080f0740c0c041ca4009111803907550210006e003000c0d0030080d400907008103410021900c3c1d8112000f440e00580051405020b9040107980e0b8060314410740c00410503441810f030105000c0da01818940c030032444049140e400302d6503020035030b8030b00320000c501050030301041c0804d050341807040d158880001c0c0d41e440c440f00c01010014089018a41c081c0801c500c88458440755500c0e200161001440c000c0d00031341ca45c0c2c0d07507200041d04000080e24458000c1d80b80610040c501c9115a0150b0103500385a0f004d540303440038590601c2074400b80b84c0308840e0903120303208501e01511010098500140824589101802d04101542004410440b8100b01c1c960009280e52054503840b0b100c1a0002820b040020ba1222035140050b42945140096079004410740c10b0a044e00405030021407069 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 179185440 1250 179184190 179184209
    0x201110708131707091a100203030a0c1b0803040c050901030b070f020c010905060a03090c080a2f120109080403030c050c01031a010507060b040f060501110a02011b0609060f06 77
    0x2a80310048807803c0034100303002800c583d01c03048003040004100e40c08407202103040e50a40d03030000310100210340342c48042101c207001648000708004992001d44591000c00d011460009070030035003800c4020800d6211803020b0038211002000c1070810040e60308074401030601601d010b03529a5a803d000c400f140040700d08101150711014031294280c07000c41d075940e144a058440004090801003440201d4210080080134541c0e104040750100745001603120081c40500000e01404901e86081400c0c0740c5100c0800d58800500711048810b003140008814203480e00303442510065000040c0c4c80d015204140001d008550000717070200038140e1082c1d400e0300041c010000c642072400f0042c0110100e03245c4413103031011100c07020003900345588154010041207009410110b04428400001000c4075007038482010690b944e07007000c00c050b5030800c4d038000f81c0030b80b10780c0601028040317500041e014004a4065100a070603020510003049100d42c002500c054100c00200051010304030320000a01d403074090303900319 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 179186690 1250 179185440 179185477
    0x190c031713060503150d050c01090b070b160912030c03031811060a0e031506031204060f050f07150603020f04060503030f030615030a05010e011203020c100201110708 73
    0x22603100000c4901d0320003041c1c80c0008561a268040340d007900301a00d9402980308107048088203036104010302c0d01d00d900400c090705200185400140c000c8849611026001c4414450320740401c2c101241c043c0d00c00960341d2003074002c85000e602141e0240e0b40c0d030810301c80d41010b20a01c606040d800f1a040f09020703c20f4a041054420000400c1c0f4101c204600080540c03849048488050921002502000519082018006021000080c00e107082e80c0707004d42d103103100700c4200529840d04105441d065500d03640070074a01420000020135584400a42d0300c02d000d40002c08144107030842c42110b41c1150000b1000322001c104c91506401340100740300aa00c1000d076103590145a1070036201d210110b440c02001580780c9010403202e82041c1d00010021503000c014409007018451354a80250300c20408240700240c00e40c1844075020311800103810032108260040071000c0000d4002810a502003800c0755905090304a0340d80c120301518102032100c012201c08102c4d04200400407000d4a607401c0b0840c0d00440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 179187940 1250 179186690 179186723
    0x24020a2303030c030106030f0e0309010c0312020d1a0d02031b06120703020c0c0306010b0a12020d0513060e0d05040e3301030f0b06030105100e15041d0103020102030a11190c03 77
    0x1510a03107a14180780307402c100503228bc0b940c080d548a0301014072906010b0f070303081c02000b0800200d80000c0702800401b51100c1e416070203101840c08c01d0802c000c08540380703000000e483d000300c4e1b0344858407000e6142a10f41e8603189249a0307101e60a5581619030445403000500d80282c004002c1e401189003964a445444201d600f145030220b010350503615815001824404022000c542e00003e00c0c03181901e00340d0070011403665038030902880f4881c1c00440c40f005517040140c607040c030407100c00200e03600064003d24035407a034196005080b5000c07144000c5130030005032200e00448070035a9000e0040c40c00410803010300c1e02285c03046c02490000003401d0700e04000a100044180040d60741c121000c1e40c0c020020001400346240c02a901c07082d07c089440d064011821100200d40564800345c14a0103424000c902040586100d100784407248521107402c0b00340d03502d544e0020b5928040c88001c4024807030350722002c40202c1820444c50103145800705010407220b840d81802c1d08005001d0006880d400d101011042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 179189190 1250 179187940 179187971
    0x1061d0a050103030e04020a0e0904080913060503120304020f03060103150c050306151309090b04021c020306150f09270d170a0b09090724020a2303030c03010603 71
    0x904980c4c154685400d0205a402000004d42c00100000181300e003502c0000c00c29125450010700c00c42c405d18802d55625940703420003402e007a83ea02010342c0a07060440c10700090b200415284a0300441c08038040c0c0701d40300c500c009000710741020750031a014424003000105000003502c0e00c1001c1001c00d00d04001c541d141c00c0080351284400c07250150044610351610f6a8514118010501c0b98016201c18603110b456812001c01d41d140c10b40160307080014142480298070f03190b070040700e802c0540404010501115400301f034803004020980b40101c50b25000503415a02c0d0082c228505560080ca402058034103440c00840e00110070680280c0101c03030003001c40c4d120400094500140059841c0d05041d00301da03245d50800120010010240681c0310f10325107015442d070303828460040300400080c1c940c2c0c1c0e08002d43e403041008110b0140c0405406490500c04481e008141c5200700b030b801c40e5104a0103402010f0008602c0481e00c003070900c612000081000c26010f500156050326510381e0b0510821280c0003450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 179190440 1250 179189190 179189201
    0x30507140a09030206091207080703020f06032403160803120a0501030c0e04080405041b0f2f0a0203122203020928060b0c011d06040308071101061d0a 66
    0x1070201d81c1d07800080c005403801e00050680080e00801c441c3c45480900040c90034111203601584003030f41320800c18021840d0054003100303075400940300c641c01e62401da0042007000681c0c1002403100185801c211209450501034094403600c1080000750b0582d43d45903040d5240d112030342c04c5200c10300200128405503050700440303049a406c800507140c41810000c404804000242080b40d80c80820031000459840c5c034000c0f040c41080040d0481000f920f0440c003d00701032085800b400030402022a82100a07010483d0312651008d03490344070582d90b00242c400d900d0800100000381d8988501d92140f8210000180144141e100d001454081c0a10300318090098041900000b58401980340000d50403602c11070b0507050010118280030700c801c11803400c41007250840e42040306010800112010b40080034050904186113003840710605100d0300c4051902e81101030001400c00095002003007000e84500341081004c14840020000607603900026045021000b40d10b900d544106000140a0041c80c0321742e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 179191690 1250 179190440 179190457
    0x10b03151c061a013005040f12030c02030a180308032a0414100309120801080d02070f0e0408130f0303030606020c0127032307051005090907120c03050714 68
    0xc0f40e0b4151260403021070170f81800e003450385c003500c4120072010100541b80110b90146009842c07000c0c0c1d100341400c0804049407440040401d050400c19404a41c40c0e000084414420307240c0f4018010340003140000b0181c84060f44003805400e400b1080c081030514118030500036825210700d021164000c030042d40e225001c2c6109a110407012142c1d01d441070305211070942c4da4240366160002c4c1c1c0850f01c0e581c1031240000700d10628006880c0ca0014013400c3c00800044070300e40494001802d4913403030035030501200c109600400a04410f520301240c04c100b041c0003a102485085041c82100355144e0140e010550300c41e03c400c2e4000b908051000a401c3c1c00800c072400d10002c10795482006c00b40040101d9111051024404c4000c4420000003010a1400500803441d002207070200311050442d8000524200f019008240304100103075000c0ca480c0d412400b1941048015168403540d80d68001b800d44140d10482ca81000305801c2900402c1015816031009201e80210340b03a102c0d0398690140450300c5401007162 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 179192940 1250 179191690 179191697
    0xe0703030921050a06050f0a0605090606070317040f0203060a05010b220b0c07051906021f090206190801090b030a021e0a0f080f0312010b03151c061a01 67
    0x7010302ca124032a20b201c03610a460400082d40d40101076460a24100d0310100035109690744805010034901102c1e030141d00a51003140c1480014280710000300b02d02ca000d005c045c8036510000d01c103802c06003d013180f00c1d18100710003501c83c00d5203818100806101e00f9103500b2072080c054040060388550207031003082e040e1112614560304000c0c030100e180e2091049104140d5010b204840d000031a00c0c5103400600d0016046030107031102c94601010b00c00040700f0b102d50a03881d545c2082080c0207260f400102072400d0201c0041e188801220141603200402a0f0b24000c2c1d00028002081d41e80b0b0350345c0c4410b044000c4601d942704212aa03072410560111075241200700d9040d0400752032100949080f40c000183c80101d0b10119056082090004204055540c400010303a903c01070304020f080c07000c0c0030711211034410034061480d0100010810b034540c00140100030480c070b0040081103c1960128a8400700d031806003a40900b600b480c1441002921280d200b1201241403990000003017008541c0b2524640c4183c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 179194190 1250 179192940 179192957
    0x3170a0c110f030709020903010b0409050d05311d01051f05090d1208090307020a090c050d0f020301170f0a080f070b27010e0604080309031b060a0e070303 68
    0x60741c81c2100640c115101c0e0344441402d6510a041e41c041c000600200030540006a031400e10070103050940e001e8040e800c3c0f180d40390641c00707004510003013141503210703101d4580740b9070352822a8031108401c0d08122032203c07082c40082003084c03600601c2d4079800c150740f00305d5040c4050203100061a07a030a80c2c24080e15400407d03021074185412030b0350340d002c1c0003421542015820a60b8480c0801c144590380318096880f41c51403a0213840c0540c00103206a0010140d0380070f075141c01d0aa8010a0751740038984035040e601540e40400400491040c801ea401c0c8002005051120b850707090131240c040c0d0801e00508041160798031903141446000100e05200043c004082e00e4004e401c0c1d02c4100e00354002c0d01100c0c0c001e000400195000407900354455108041c20300d89098a40500e1480fa16050b40103280c40031140e14142c0c00c10103c4a00007109a441a03020003419501c0e030325641010704501641c0c00c406155008841000c40d1170401044a5104035070201040009041c0d101250380d903002c2038030004e0042040b10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 179195440 1250 179194190 179194193
    0x91201090c0611010f050c07111c0210050405060c0106030204050705070309090e160b041505070503071104020f070c03110411120a1404050c19150e0301141003170a0c 73
    0x3602c3c2c0d10300303101c10302e000064458962032440081d1001240c85450103030300040c024003004500c0781850914442610782d090180f80900e003800c0303171f4012104040c0c2b1400c030198405040070b1050003180c1c058100507020513210340c41350f030085000e03180b02d00040780300b1401e010000c1c00d40703480b800540301c403d501940c8040c1a44d00e041d0309800209036000c60340245004000924100000d50407510000300800c071801a078407464501c80d648485401080a01001007c000b00342c0070541c00800d40b00c00907041940c2c22243c00c0282d0016009114840c0f0303500048401090740e80500001c08403c8003181e024185420741e195074541000210344100c219005a07a0040c00302160000424110344d0340003c4004c0b00140500303e401e0f02a580110440c0d0498941d400900100d0b010f080801001c2115111000f1481a403810803150a82484002d0a0035082015042911a05580c2504802d140690080c51341d60fa0b07081c100d8590b6404101400265009641252041d411000380c0301101c0b0029031564507109174420302d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 179196690 1250 179195440 179195447
    0x10030209130b040b0603040804140303090f01030209030a0b1501021b0102060112080d0501180b040c0203030c180d06060e0906060a0611012309070801050609151311091201090c06 78
    0x86112407900556904d281800c1a2591001507000760b0140c4186511149440c400d2401901100c172080c0c0250001c1c4180f40715501c0b00d0311001c601030001d00b8056280d03003030140030078584085000c2c0038203006a21001e00604422410b03100c0d194407020b074203131409000c00c209449005c4808249460050f07004030010048082c1048030600810b1040e0f00d40781c681944000d20348181c0344282c01c41c94203c6094480312484190a00c140c520300079081e00c06010007031040b88003035168080245244511400050f4041861005805180e1100c1c0014180d9003080320906042004040c140180d02030301c420394340441c502d000d00043d028414080104219070050512108aa9944508683e003415641700c030408900b441d034180450110b103a074089c40c00a2844c0036004c4501e00703900c95110340d22591411040c48515114591030b40c3e0700546c802d00700c6544003801c1c00465102c10601e1100307854a85402c4001c040c05254200801400c90100e60f541c0d500d1060400c1d06080326001c0301c00400d409013034036003003003024003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 179197940 1250 179196690 179196701
    0xe030412060209120a0c0509060108190e0f07090c03050f10140f040c030504030219030e0d0f1e1a22020102010b0315060406060215150d0c0608061003020913 69
    0x4081d0600300e1485a1a135142c0c078200325030704115501e41d030140c024440340c1042e4140641c4903409203010090390030920b00d2995250080418294029202c0c0f83c1660142005c00c404140b4031905807c89404642d200510740003058041d4010000a0508001c1000e400080881c540034450b054603640003a468500d440d0b8511021095143d0400400000b1100340e40c0c0d02e100d800b0510f00341382c42c0811145014036000307040c03104c03a070b00c00300d1200520790400d40031030740c05907010343c0300c000548440e130600d0003e0030524140000c11100030400365503070180070100407594078503103030480c0306088c031031652156502501100d90080707411485858007505280300361513a4007082c4032054010700000506d951350401080c2000c841d402c00900d4250001c003482020b080500c501c900405151002c0c1c004a0718444a064150001030403040d059684d44614a42540d1140710011340d0a034043d00c82042c06560b00700286c560201120742d540325650101d00540c00724064000c42d11034010003440c0c14644c08510320340200501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 179199190 1250 179197940 179197957
    0x510050a0f140d0f0b15100e040504050a05010912030e0a02010e130b06040b3001051909050f15041a1c05030304050a02090a14010302040515040912030e0304120602 72
    0x707101030103000c18444800c2c000098005d00746030015181100841c91940c5031907400074050030702480320118560b8841d626120000b0b00b20b401003000d817194280649001740080000d0441e520703141910003001602d602c0c104c8514241d4805000014803100d101c1d4991088140c007901003403aa0904100500e0001a0040c100e4201b6400042014020b00460540d8015400802c0041c0740003914542c0c9140c4080345030031003c1f10506400280108416010721000d040c414903000b03004040400d02c2c20300310120b20714003400d000c40c0100850f18110300652000c0c2425a801081203510409440c141d0030140900c403508828a04440301a1a020040c450102d0113055050742c507035515001580001c806200950159004030f00504940c010b41c01044100203020300020319041c941031010302c4c4c1540c8845031504403134045600098664070519101114544c10002a0303000d880c0c00c41032410411228000c010403031669404000384003030705070f59544e00e100354010248403010904654001230240d0f0000c21005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 179200440 1250 179199190 179199199
    0x309030705070605090f0a0b091c08030f07080c07051c0c0503040f050f240a030b1206090706030614100e130b090a020313140f0a060510050a0f14 64
    0x880c0c161180c1d410001c060f0414000120300181c040c01c0c61422489280c14a0340440704c5503003003840c0041c017050500c2030022450154403d0b10704c40d420700c2e514640901d05a5000b545456503480d00c103244041244044441d02c020a080402041d055005030007950401c9a00800400e44510308407003070035881d0020005003003000301c8002603e0000380c050014000a00180480b20444c074180020001c44001081519004001090400c0d90b1506800040300c03d05100b004001d1341c0320f0703030744004a000e000c460a00a400c85909183d81108080000e00a40f10741002000c0d552915101c0c402142542d5952142e0440341181c82d01110080c0340c90441c04074810780c942402003200b046000482d008500e910820018940d0303c04ca00715081c14011b03402a844640d810f011481c0d8070309101e0f40f94071081414400b40425420403a412142e0038200400340c03c804494080342d0320400f1514001014040031911580c41d01c00850340040c0508100307034030805403003128540301201070901301c80740c100701c010b0082990300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 179201690 1250 179200440 179200447
    0x604170d0207060b030c2b0606051c050609031905030613050c04061701050105040b2208100b0d0203060712021306030c021b060d0902010c05010e01020301060906020601060206010902030903 83
    0x4a0360a840201100303446020301048800002c0109820114403914150003a00b1001e0350340e00700f00c010241540b45081c1c8a040690841c041d0a042c001460030b0b40149400c988103040030502c0000d005c242c842010b2140d030845420347d450f4180581c40740954020000040e50300301038404428080c0b0007441d0b0100000d404454501030703d10b00726041e92825114450b031071400143c140540c0b80e000c041ca900056040315204a95454400020030900c1180304507800b8400209504140d480340080c85401045580c2c2d0187c02d00703459071007041c0c5034541116105491454032016007060300b040c095040001d0340050181500f6a1007820544602140e07c400b020349076801c101c40302205010401210142c40c5d00d1303900140303042c0c05500180c0f17060444048500200a07030490865556503803c2152001c110000f001300322001da61005079130360784c1d1240c0014032075400c141c246002d0312415401340d030495140c1d42d610b428041c1e64100607601e07208280100e40040c0c004c50014450b0580c290000c540101307012084a15 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 179202940 1250 179201690 179201707
    0x10050714030331080d020306060705060a05190b030309100c210807050c060402120f0102040b070209010b0c0a060b2206060801060201020406020c040c090308030a0c0201060e09060417 80
    0x4680c0200c030000c0101018034403007143c0da07100e681c0e440502440880701200c80065074070365100501806500751308481d00000015103d4880c0c2d401e5a1082742e0080894000b410204081b03000303000c0031580c0240b07000c010b00e40280144034030700601c1c0e085c0b800030f03001d1840c00011005006805a08031320038401d0040141c00301c4002141d415140c6009500e8035202d8420108441004200700c10180c4540100142840340f0302c4014004a0080d0304141d04407120703c0d200c44043d003840c5c108000e40108040d194400700d80012114403400081034054400c4031b05992580c1c0710803d0290303501580d0044406a840304e0400070000e109030340700e81c5880030700a1204040d480d40800c035480a80f00c0a000825054844a042010b150000c0015024200d2800251305003030814000940ea00c00042d600c030311442c5c0b2075090801040c0180c0002e00595040f085071980d078031b004802a005040310305032840056203080320008142c0320399140356008d1065071002d0403290f00c48c1d0301c504130304072041010b5205041b001c0213520f2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 179204190 1250 179202940 179202943
    0x301111204080c0f0706030f0219180f0f1a12130501090c060c030807020f030a140409060b0a080a050c041e150c0c0f03051507020a1a0f070c0210050714 67
    0x1c18049131000200350b10382c04c0ca400181540c1810300c660711140c3c014032018044840100900412010500d4004d22023035106020b40e180801d00e60007035541503a50358012515250650040302503400c1002400420038901c1809a254031549901d540c1d180048000300360072145110845070700710702030000481c004107507443e017a20001c6c465101e41c021480300c8009d0010035400c072026030b03402421030001e4030071042d0f62244d007234036446904649020410f03544031204040b81d050081d20041d2446a40400c01d80c1e40f41c0d035200005038040141ca07404190071400040360200c0300c1c06940d104034005220f45040503c1d0028203402582c0c1010321800e10b0f40c0c0518089200194660710031304171076490391206c1742100d00d401c00141c0c60405030030803c2c07840e26010050001c10386c0022100103407400004c02e10800d95030004101d00b01150808010418504452007010001d040081c29004065803140e1180d180c42c0c030715080d03904545d0308a000750892842c1706801c15050103500500a868028000c00100c641c07901ea466 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 179205440 1250 179204190 179204203
    0x61e02032b1d060a09020d21110f0307030c03022a0a0b0702090c0a02071a03040b0109021e030703110f0a0906020d02060103020405040f2f0301111204080c 68
    0x120840040071010720000d14036405111090140620b5006082190ba040261200e40c000c00c08541e5980361070900b0f0454032110701447c03c0640041f6801c444c0c046440014005841000c04840090b683c90302261140e04003054402040e10b903071004601d0612540d5040c0c6855082080a17020f60050001e0003440343c584028904042008140c07190f00c034000c00c1c04010f00161180c00200b442d1000348011801030b10380640090f044141540003680711310000380e04a03d0000d003500102007a240b88807900c0e01c4000540007071030080e4841e248503440c6a8803540d4400c124007070082c900400c1c90740c0807880421488a2402990021034500d008211000d42012901440e07020300c800c8800311100040d89044140e204803014003070b11582c409420381644909000f50b641d541808044d02c204d9480022030200111090000d02035a4400151001c014460f4014807a10041405c03a80d03451000410030309940c981071103010079a0165000300c0d0709100c00c400543d241780b04000c2c0304032a07842d41008a036070090020800d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 179206690 1250 179205440 179205487
    0x7170f060d140f010e0706090509040c05030a080c07060c03020a0b0a150803090a09060b03010902030705090d050d0906020303010602120f0408150109060603020405060301060c030e09071701050604061e0203 90
    0x2001c0710490f1216060850701c03810f101e040325410402041c0889540884104102c640458201c80340382c6450401c544081101d51000781d0600c41c458003038082208010152415100700416503004030b58550080c1c0709842c18030030082c0180c01502d191b10020b18413101d07147d0007987c2c0c0200017452404080c800c403003401d4603401002981d480810483d0842c9004d080e0702000c3d08440b20b040c45601e18288003809540418013600c0c2000d90040001001d075403040c01a00c880c0e1600800ca6010440036091040d210006001c0c0e010004403170101c0807c0e601d000008480c101c4216070b00821489848480b80b525036081900306010000d41004001140c2d181042140070001c06040050000d500d008484c90407a90550b000b001814010311007000030340e07900303804c3d207045510b50b003002d5001e51030702c0c030b0f003100d510349250421540000b10105000c903040e808102c1c075481c0c1a086414040590301d038010010076001c4c5108040000c2c4041001140c000501c00e107140c0c401150740116420300e440700341c2503001202003200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 179207940 1250 179206690 179206693
    0x60f150803070501050a02041a16060c03020309060f0106021b0d0f0b18070f0e0405031b1c0e0d120203040801020703170a0b09040206030601050c0a1a07170f060d14 72
    0x1404000e0003c20300c2207a401801512086151034a0682c0c51102102460302120110313101284900328109611348911400d80d00590810454001030b0000e030081d0419101482070748200400509002811180c881c1039800f1900106041c006050700800c24090450420f03400800c0500054002544407030410b0000d032007601451f609140c5100f046004007002d84a0028503441800208804014081d54a05640742c0190700b09880d500d50a044e0f1440c4100d09098602d0926914100c00c103020110301143c500f40750600c040c0c03413400128030495039481c0c0910026400300b00e1880b640c00081800c1641c4201101c17500580b818941c0e00c802c10b030f003260132400c401c0e0041440704090203d00d003002e406069100d0024501048008001004150090780080c0020b015020000100b84641e0140c0283c400e81c2400d001140d0044902d840c2c100011006c034008008500501d0001c01d0026010b00d11420301a04650b41c0034019a491030060050220080c0c12140c01072001904240444c90860a071242d11a10a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 179209190 1250 179207940 179207947
    0x90a0314030d0c02120306090a14090f0705030c28030f05030a0e061216050910020c03070605030919060f0204140307050a0f0504110906070309060e0603070903060f150803 75
    0x107548a066403d010300c910110340040c007682c40020110029690003030003c0d200d0300c407182d80e075448a100920707400c0d5000a9481c0d0080400c8008040014840811106081a5800c041e07441042c10340d6990a00700312a4006078207a00109505030700c0c0300c0f01c86005142c24244124a03982d07100c8021009694805680b1030b000000d40701d80da0394110790440c3c4a4441681c00c11314183d10013207054040700000d041c407400500c4d4940d0000906118006652100c00020440404441d43c440081d6803151000d001600a0180c05d02c005003041c00340c420340b4801c4030300070081d00ba80307554241c3d001703c6c540c04001d048880e1175035000d4070780007443e0034809071000d401c0c00c141000c1071400804c101031401030190b100310301c0303040c1100f024130088044100340c03801c03200281d4005c112010ba50700032104600465141a8026002041d05818035611298600c06c0b205c482d201c0680307800b00c40083c04254403084070341d2070100360140b000300006120381e48190b44c00d601e12000003e520158080c54080b400640e40003031906e42c40030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 179210440 1250 179209190 179209207
    0x1109060d060e07110105060105040312050c1e0708150112020d05120d0c030f0b280803130f06170f07050d05090601081218060703090803040b03010612180206090a031403 74
    0x1d06c107158008400f402d1250401c1c2ca540e1710407c03a442d01c02ca00608020b404200480d03a410b04001481c0052008002503100250303030551542da5034424402d042c1c1d00e202d0034440e001681d80c00300000c0d050316041c01180003040200d07000c0c803a000c0f0b10b4805c102c039244a01d6a290b840b07001c1e8140903102101801501084030780d40d039000201500c03051007802c00c202e0b291112509084d502c2d001c14803000c80da00700c0c1c421014100c13166400c41d244403a43c4140014000084c0b00e516607200da8914100307a03003071000d2314500d454a40d041121500c1d088100e0710341c80031074080824016400b801110b0b51016042c07518900c0c0c0001408440140c0350281c030440011703400000103128400d401d01010f6000013040140500300380210910201180d04402210302032000068000c0a0621554010300901402421a0b0b5038540d0f42c41c502606074024800ca10010302079006449c0260703030b1805840304015011480c444005016000c001090313100030b84103a40107081140000020711022940361185041402440d11030024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 179211690 1250 179210440 179210443
    0xc0d05100f050906090f09011d060108071505040303050d0902030a0b0103060b010c050a0204050601051b0a0201080c122404090c0f0b040803030c0c160b1308011109060d060e0711 78
    0x1290002c41c8141080400c1141c5078a540300b81c03560002455010200c1511545e941038010b0850003489030190901035445c018003280081c0003030403a244101200c01e0240d07102030805908555a00398000a0020001080803a00c154054901484403260000d05003200340c0c002890400c040004982e0056001e0040080c0007a500c91080a00001c0c00c100a038000e0f0b0b07980c0c0c1c54540c50400070080c07107240d03200d000c2000c03039104006660810075046449286841010b10340d65450000160480c0061110b00c0054140c4a030f030000d80d400c0c0c400c50700c90b290b131580f11410f9014445280e00324003150100008100006a030f128014013280c14002e20342d0008072400e00c284001203203c20f40040300c901b40100000c1001030400000c5903484030139002e880c1d17100c0c1814940c503401c090201e10600b403039000c009800309490703420000400400c1075082c050401d0740ea0340c3c0e000b64281d03183e515918690311002d005403100c5041102c01082c9c0e5285001c0300084443d00c401004184a4090b03541d034001801c2e0b44071303100807003d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 179212940 1250 179211690 179211719
    0x18050d03050604060f090f090204050108060a0e031305010f020a0204111c020c2802091e0a06060f0c08070c090b0a0611030301050d08071203051e01080a0303050c0d0510 74
    0x2c1610140505800c000c00b00e901c00801c1c1c401c030b507039890b60b84194403603d5150394400c0341c1481e4020002d02c0603580d0307910030a41d104c409440505034189031846860b026200042201c0c840480d41064200d02482c0400645548850b141c201c030560142c0700e0706100685e10b61243c2460011065840c946881051680d4105140d42030310060200b8030402203071001280000c1d4401d0b1031003c400c441c41c1c59000400700c1d0041e41840d081c0c000d40080300c030400d0024440180c0112107503000031240290302691103540810941d04944240c3c00464240c9030840c10031880b40760705540781400303542d03007034900086da60b21100b81718600e91084000585d503c0c00c0144614250200310018202c0c0d203403058500400b4005103440788010b203d150f110311030106d0b80c6000c118041c8140d460180e08820041d1024018643c0a0054036046070020030701d100c0304103c03960900c02d10a9050683e00f0550040807070340240d03034064004090151681e01c9821040c04100c803413814600804d485010001c0070340040c2403070500d881c40c0d0243d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 179214190 1250 179212940 179212951
    0x5010c1821080309070f030b060f0913020609060c060a1506081e070c02120a0c0b120411210319080601020d0c08040506070b061005030606030a0c0318050d0305 70
    0x41508151850281c250701c101141c60b08480305a56940700c010600340b811031a0350000c09424041000002804040c1405510420080d50445980088042084184075007140e078644100e00b0201200c0c00342c1084000b910101102401c140e207801014600303d803030007030100ca0910656403601c100540c80c20080341420018842d5041a13500c50904100585070f1400e40035004162907194400a191030b8841c550001c9400d40180c4003416024a5180300c94490b00658002d139898250210002900100a400c4942d01e0000e504407021a40312175682d10010f07014000301700c1d80310a40410012011f040030001c00c00c0342000c203000b1987d03a066040d8640d044800620704a050154400400c80c0598001c60001000165403402c0400c0c410140b0309403445000f280c0049030041404a840003c1012015403140074480480d4501c0200d1038081d0304641900c401c8030920b810000030720101300e40c10b54581040f110201d072810082014101da1040d0419011007807400d64155100f149100c2a00342c00d485690b0700728 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 179215440 1250 179214190 179214209
    0x9081c050702030a080714040816050604060903031d04140f060307050108010e0a200409110c030403080c0c090a051e01360c020a020312070b060909010905010c18 71
    0xe252100700a902c038003401140b0b80a00800400141d842032090000d401100c00c1d604445031503545580e6070030360300d481300d9440c602269800c0402044030302e415010b50f011180c282d43d4120405045a608444a40c0e1958401001007000c00394241d072650345004080c20084428244100c51402c40c0241201d030178054030050180d04820414813490741e1280040381518900c54082000e9202c102008005065800d072215210080804024180c02030000920440b824100140441c0465070440140c0c0c7c801c1026541040e8020002000000d844402811880030100180d0307005003140c4d40455500001107600c090015610020081468141c4501d11001205418005010b40c140f0341001801401442140d4075103495131302c040d10364110301d03108544880f1040014442032910150203035030b50311850000c07031180c05081c01c440c0c0b20300c43c001e0903200e500e5004028000e41d606d0310b10601c00074034000350040c207495489040d00f001241d02401141c005041d40d903100300d11045842e20380d002145003030b0880b8002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 179216690 1250 179215440 179215451
    0x10e06030c0c010209030f030a090608150f030a060504050d0e06040f060315030c180f0203100608060d170d0e1207120c05061503060703140c090f09090105041203091e080d09081c 78
    0x210401e1039034014082415500c43b0410082007000078a030078441c44c00205203038203000400081120114030300281401580b140d0b240089564104240d50140340204042401d24500402109229030000c074546194012118202c135140c2c2c0b244074907034450390440c00707103400c11880d00d800940d5103100703060380400d901000310b096007401e041f45414507859200320010020080c001c10b00b2076882082c0754a03015407000c540c903180ca130450a4500c95401040030004458076004100010071030110b880103280c200d402402c0d03d0a0100d6403006040c400e0488080100071581640d02c00140b81041a03500030403803600000d00142d598010540b5282c4010418400c240c10305100d034071140030b0500615004440f00120030b8541d04010046075444281002c0164441008000d00140d00019404140a607000f0002000d00c1110001c080d01500c0115000425900c0181b44203000500600a2030283c03510440d100352402d02d96482e00b100b0344005a0303042d10b06140000d03203802e0341400004403c8200a50400c10f111 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 179217940 1250 179216690 179216701
    0x204060c032d0305040b06030c0109030311070f140f040c020c010509060f070320010b0a0e10050303220801050408040b0a090e160e010e06030c0c010209030f030a090608 74
    0x200ea281400020706000c41c011205a511070038015405000025168090001c88164001005401c09407010f4918074000b20102d982800d01048104020308185c680c0510f0ba4610b940c104d54909402c400201240110600440c455513a07507210b01c020031005240b5000710303c91100300510f110494940707a02c00c41c0340c0640704036066000314106c500001d0900707240762200c40c440085070760780c820f0b498288242c80e80007550204041d00301c2c11007451f0621085075494801e80700309581d400c1352462203070641c0c0440380410130043c00141c80c180ea54007001c504004a1881e90728000b107031640e003103050210031684000f0f807042130480c1c00b86d14420040517180002d00c06070400b500d0722402e9218902071511142d00014152403601e006480b001c0040100c0705c3d07507888a01d4200303003100101030900560380c0002e040103485103145d8801e0850307041500000f0240c41c915190140b10860b1070784201005460fa5400b803201c0110f664080c00f2280c2c4520501000c5c0d0358480c08400c2c000c1c28100550403907130910070580107008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 179219190 1250 179217940 179217947
    0x12050c0d050c120c0604060906080f0c0403060b010215071223040227040b0406060b030f191113032312250c05011409010206131b0801020301051003020406 68
    0x190516800e444143c2c1004620140b00e00b030004003825a50468030000d070010b0710030380c071084d0103041701e110390f94260789515032000920f0f01d40c1082e51940d0705c0010500080c00031a000da4488100300b00d05004440d88107548104c4149900c034100c0720349000c9240400c100c0042d41c8e9502030b10f1007220400f00c66003900f5240400b2400310307031030107003010307004008240c0e42612941417041d80e05601503280c80251001e10301460503d075a650708560403181c03035061010000d14058510103503030041d2100301604901e66298640c01c2d10401415440d020215260742d04101942030003030061410b40a9000c801903018110b00781010400c401c113102c2000c030008495030422801010460440801c2c103a080c2c155143d013a03552580b019090381582030b80c01840103003040c0c10800d5091442040750300c00e80300c01c070b000da590105210300e45c0aa0384040d4096080b141c00150111403103507448014901c6041004501c641c48400c40308441440c1e000003800d83c0d40080184050301d0018030020424400d80340551900c0d00784440203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 179220440 1250 179219190 179219203
    0x10e01030903021e1e030a020c010c080711060904180b060f01140c01060e010b1207020303010506090405040602041509080625030e100f020706050121030c080f0412050c0d05 76
    0x74004040c032030300e4584c1000c800e014006000080c24074403100c3c200d10840480e12039000c08a0342d030145c82007006004507940202640c0c1c4d12590882d40e101d050908a46808400043c502446580b00c0d80400c0342803060307039651107070240c7c1c400049000318002c0d1041c034010f121840e0150080f80b16000505030000b40c2d80e4007040c5015105584503819031140c0d104125a40904400d4000821002c040c00010840550407006400c81155810103089240c4403203c043c4e03228842070003803540117001008010250b0070960090740d0020301c503140c010f03d819070f40e6031000f900404034440f210009105220070060100c0c00c1000507004403000d5598090607107501d02e40300000048041d2001031540b94942c1410700321040c40001140c040f0058140702c102d110032010f07002584040c0046481c02e1401c000070912900c1009448060342c1149031081ca00fa03140c0e2025641c8402a60007200c2000080008801610074800948000e00c004211141050640e00c1d089050801e010160f500594900000501055000440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 179221690 1250 179220440 179220463
    0x140601030507170309041a19060203090f03121318052814070206100f03050c0103110409020f04180e0601140d0b0f06030118030c020907270302010e0103090302 70
    0x7004052000754205055004040328680c0c0249080c1d011081680300080324000c0103400c54646143d07084005580200e423560f13006410060f4028000e404039420300071500d03038402c05d0040403208500500d0130f1850056108a81484000d0507070340041101c904078990a06142070425014000c0c0d10b01506d0031181c0700c01d40401d102d03507000380008201caa100c495005492110091203640c450b03140078880655130340c42c290307418109000074210004440c00c00c0c003221801d50764020302410250a0140044016141c0024a80b945600820000604640505c001c1000014000f000e40c6c50314079110074100d035281d40c0c4880c4c411141c10b20800390120a40400c04070306407403211964010355400b040100d0090385140d18000c003160290018003038000712550700710380310340000c40080c0505022502c00d0a60f510001d00018003040828080f07100628142e10b600743d1012a61800d0080c0100f010110404070034821400945444110b00034407d40d680100c0741c1c46100003e00302842542d0181d0390080d42d4032440c541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 179222940 1250 179221690 179221709
    0x120a020d09020306070807020c011107090203071103030a1a0a0b070f03020c120a02041a0d06050712020724060b07140a05070806070f0914010309030207030c12140601030507 76
    0x215219035060310390040c0901500541250883d10784103101900d901c00a9464002521403181440500d620400c940400f6400100140c24114945000e54010350409450300f818420f02a211082e5000100050352160021641c04151400c200c00822101c000c0b003401c00e8041c0556600900608144004541405a00c24401c004100580c01c04a003072081410115038000c10442d140001d41c83c001683d107846a0003241c0801c41c95044240e01c0d40d030750b40c050900c60780241380da0b60305102145050340079030752180c40c90a06040039040625000700b02e81c02070804540e404000b006000040c00380c1000c90680340c031040820411281018031401490140302d00050815038615511310171401d003807003e980070b50341c000d04803a4420f44401e01561038403c01c80c1d0210001e02d8462520f90501c0c4500e001c1c90031203040c0810507803500c0260b4011806030078101019420740c41403140000000e910062a40001d10b42030f01e0b030000707485a07442d00d080107803244155401c040c1d1003900184040340b07020550700c00f01d0320b8922 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 179224190 1250 179222940 179222947
    0x60b0312070c080705012a0501060f14030714010c0611030c0309011a060d0f02040302120601150309020915010512190b0a0311010c14100f18110906130501080c0411120a02 75
    0x2001d0312994900344000c00a502b03102e00024071018495044050b1400391100070b2850959000b071641d1404244102c8080100200405065501a16a05803c24004c40002c00d5a4044925032141e6034010ba8030128111000000c104405400b80315044040f050724207030801003d411000135026000b4418203036829507176a10103032000101c0e58100c41c000c40d4041e00103443ca001070504540c880401340704040b40c1480302c1c50401d103940e00c24807540080b99030081000045486010140b6181d42e03904003940d0510038200078a0390381e00c1d00d01c41d603103110300b4203103104144800d00d86600700296a40300300618040d00c0c41082c02c2c4006800070085811684080c6802c110b15001c50501c2c2d05010403403100101c1502804030000c01c203117096004040e0503848035400384800c4101c030901d0005014140d1020302072010301d1a8551451514000751038200c0e0000700014841240e011200045410a0b440004070350300601070391800742000c1c0180d07070307006104000781810444158905803518100a00034a03203180d000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 179225440 1250 179224190 179224247
    0x7120606090c0e121015050103050c0a0903110d0206181207051e0312040305030304020913020f0f2106090d0305040b0c03040302070e09011e05010602030412060b0312070c08070501 79
    0x8000c601c1145c0c5c1411003e0184483d51301c0b40d0b003940e020f1401141d00082c11700c0c0014200420802c112a0b1055a917500e405082c0d1841e02da04a00204280042d41e118111101c0b80c1b0259850a0142c010940d52864111807882001c1c10007208d0320707612140c80c0352a00408010490755a43c031004501110316840402c0c140c01016001a00305031521950320300c0ca0002242c007105010000018600c118421b03581c03411180c03250b100f800c0c02c0d14007189000f94043c0b541c500f2604d0f1410140505101050040c3c04140071300350354103403952901201c40844c80b02d513100130100019030404100744c3c0c2c0c682d180d9050400481c10300b038640d00c891000042121110640010100d42090b00c00c1005800800c4a5800510390741401c95020b4068550500c0c0e4003030520b5058004540b8005604c50103040f40d00a40046180ca441c010178080e504d0200318080c0c81c41a176603003070100030780c405004000113001c0708040c2070358504103845e102d00580c0301a000301000d940410300901403640c105984c0c0d10300c85c0c20700a001850340000f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 179226690 1250 179225440 179225443
    0x510030206040305030d2a030207030309140a060f0209030a0b071704111009140f04020f0415080906040201020706110a0c0e01080709110a0305130507120606090c0e12 73
    0x154402500258002800020300c0808406410b040004150030320040d404803000e01c070300502400e034001607042500a1f00954a003c2d60080040502c00c5c00c020822058030b44412404100300080d1146e541c109000410412201d44200030248510000850500d0001c1001c82d0f51550340d018003c00f89003140c0080b0f086a4000d0020055800030910002c240d4507140c44c202500000d000c610f1b9004031071a001080101780110b105400703550b1512001030b10004d183c070410002541100c20203401c55030030010b201c010080350005001074014a081050341e420b010b94010000c600041a00317541e50089814000140c2e0302184400450f080c51400c0744014015010075401d16003c1040205180c0b901080041c0b40880a10301354106c0783e001d0251503c00d81d507070b11180e081c1c900d48015111080343c1080101c100c0c9001707034001c3d900014403d0007680c41c100a0383d50303039107003900e0b580052916165007050b48040004600030309001d0002100305000050070900c026180d82d010f200c9075440388000d0001040030090 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 179227940 1250 179226690 179226721
    0x23091f021e1318020a030b030a170a03060315090c0501140f0a0311070c0512011a0607061d060103020405060a0501050921010c090e0906060a12050109080d0f050609160305 75
    0x90103140c0703c41107210342020002503005045000c0802d0910365082e046150108803220169000001d105080800340b51042e4940e002074503402c18584e4030321000c000724030a28002403c0b0b0680a00002e80c0380300ca828092403842c1213070700c5a4100000c048a4000305510401614590f0701d0071180591511516401980a000000c0c120030105602088460500540014050407620f00b9500761a00001e6a034046090b01d14641904011001ca40c060308924200100102035203401380350000743c075a0802c007841000c017100008401d1035174820401441945801d1140c03d401c035600307c0760515403520304000601a0f00801d82ca00d44604054064a504403040d94010450354084900030801c4051071100540b08091030702417031a0005881700003403070b070240020715940034200c020000c0e2052890040d03480c40703184070107204480c15522025240d00040c0c598000e056403502c1c0d640301041043c60515003c00700e9200401240c49800749030705000070003146000e9030740f00608600e00418a5a2482c075900001c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 179229190 1250 179227940 179227949
    0x316170d0f02070309091104030f080c1c020c030703020a050108130605070f020f01090f081303060228030c120e0a0804090e06180601050423091f021e13 67
    0x9080c900d881c988504507900402c03003140300c3e4840c50015615090044101c84410380c03c1151440100000d0000c58a00881ca0340d48922a600092400708070340d9001e401c00c00b082d84600e090010808039091015014044003402c1c442c00d03002041e0a900d50740003c0c014491500c42c0906011070a004130344400e00205030324140942102061015042c8104020407a0305000d86100060142d50400341003c141030103101c6c03213103400001056002000d03072215809a031023032014200c034801c4105c0000000342c080c00945215048491007991503c0080c000001410f001e506040400d4a010038088250741c1000d0050024020100c1c0001d44041254407a45801142c40700a080f461000c10700096007200c603082041c2640700d00c3c00b5504c050711101c200c01f0400502030b11582c05070300200300501c0300f400e285c1d02c0380800e20400c8404500d5105801e0282a4402094403114840d40080301d00d0070302c8c080c100388000006007080c60214a00710103840d0b900c00780da0000c108803003020b0340003910011408031131442f0005070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 179230440 1250 179229190 179229217
    0x40303080a0e0109051b0405040203030405010305060d0605090a0335100803040f051203070519060f14060306090309010c060b0604080d08060a0e010503060610180f080708031617 78
    0xc060b9801c01c0341e90303411b084c0e56440c030700e00d207a014400081c241402018040c9074007900560805080100541c05007000130043d0b03400040c24800318000c01c109010f11070180000c0006081400e64a0400501525003036055120310803101e0f5040034030b0300e0119460040003001817801c0c0d61645a82a0490159405070320410300c0c1d210210300890181040c1c601c0030b04440084842c00b01c0728800030301c10741e181d000c1c2500240954205000107040c0d508090315040b0100d209000000d4485007524051045400d41003601c0310074042c0b08100070031404c2c1000500d810010500086050032a0100024501c4000d58001000c8503101c154996241d100c0b002550007900c1d294054030840c0d5810300d40109a0788046034401d11540d1088000035041c0b440729a0503060f1303040580606101d907501c0f01032003001c0c00562420340421410710344001e070841c0e481303041d8005800542110b0b54114900841c5915085154200340348640040107448880c0000170b2808031b80c640d00548141200c10a40301505503406800c881c501c08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 179231690 1250 179230440 179230451
    0x90206030a1a06040801140a0e150709050406080604050c040e0712080403062f04030309050120031902150c0901080a0b0603043014070204060302060a0216080d05040303080a0e01 78
    0xb050301c103407c041030650584101d80e009556008196060f6000681c0c3c1d0b8509401c60800c448040d000740b4001035201e04035092510009a0b02e00c00b02c2c00312601640101255040503050008214040c40180000d03002180d00b0300100360545006601e0781380601c2581e04103600e01c0084030400440005840040d600075108200032504040c5d5002e1001850020444441d81308007500368540f9078506480503241c044d5103c0100314200001500c06039036501ca0851408003800d017091001c0ca040000704048640300340141d14803038000e40003a00e0030b10000e500a1800c4103090802041040f00340039100211400d01c0c1c01a42515188124401010400c500d1600300500001b00070612020140800310340c5440c09031507001403543c90009074001007040c0c1c0c1000140500e040c28506500b000050121580010b00c009000da55960014150340e1041c200e0070050b81040a2a0100d11086207031400101407000180c64449011440240300d84100d010050600801d240881d00e01c032055800003504001d104020085d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 179232940 1250 179231690 179231699
    0x40906020304050f191101030f0b0d0809011b150b0d0b0106020a1203051603020d020d0203130203010b0303040303080415090b271204030b040524010e060103090206030a1a0604 77
    0x44460039100c00592911682c54001c148100e024003085482d50400c002440000030345004602078041c01c0180c51030389480d5100b94ac025514280c1381d07204a03205038910381e40c072416a0009021104101103501140306400340f003001056100309000a401071b410000580345d40070400050080401d070700e0180c000300e1917034004581113400103410a00c4a0180c1100d04180912120072415140100c1d00c00d0051840c07106070400060298019001d24540d482c400b60414054666030012038104591811820b0002c1240790700350304080c400d040e401002940514941415030b00c0c007400c19680a04010040c1640700d44242d8078101d650b1180c04250342c012010703001414440703070009461000180d12031603407071280711202071180300042e1406903102510b4020309191030760300c444805841c000c00555007800390a280c006901c54814881c0c0d9100c0c6c804c00c1074402c0d035042c0300441510400040019040c1841e20a07000d0169648509480d0312040c40d0101240390144015000c19103014650300361f800403404100410f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 179234190 1250 179232940 179232943
    0x806070f120b010e090402060c01020a031a010c051e100504060b03011b091703090607030f0e0402030c030402060c0f060c1b030a050a2a140d18060c0204090602030405 73
    0x1a104480d036520407070854452104000c48107007460b5180441c81080c000741880c14004c08450348140014103042c01e06250004035426070b400f145c98000040d41c1c0d0341400300d8a810310164032005c0c003428680440250401d0340c03419641c0401000c040c0c500c020440c0f0102603290708000c103040f80c80c2004018842c908051800c20090171000c14054425400c0c13102881c0740c1807402c1d404160140c03140d50307100c000710303e002e401e400a10f000741b02c1a513080c00b08100f00320b026100c08008040c618400e41d0784a8580004d00c6008180694200550340304500410501800700384000580e42c000b501201d402d6914501c8160380c03480c2c50004107048046000385001c001110031510050325400840c0301410b80900c0e850303c40345403248074200d4400c0c040350060229803402c62151540207080c42028a071007001021000000403000d4510004035410001d01e000c10107001420710040d001004217003000020101c4803100007d402c1c600d40500c0c010410314032219815917803240c00c44276001c5d0b0009011540c030f017040c0c10101d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 179235440 1250 179234190 179234207
    0xc030d090303061d0906160c0605010602071707080a021002010f05010905090d030203060d08090d0b13110d02100f02030904060b040303090611060402040902120313150504080a020409020406080607 86
    0x240749244128001049113050707400301c0751049803488090070880c2d4810358641c00c0035580c0c4804104002c5281c6006001513444e00c20507010b041940c0082c502c0915020321010685001e032034401044e0881803040111610002c0d400107080c0e8102c552816401c0d4055040303006025528410007142e05080001400304c2e29640081d0041203080180d40b480801004141c05a200030343c0c006030064800c900110201c0d0700a005408280350042038100b1204503515401d00020040e104020004202d4050204000d401c0c44100500441500c0c0c40100030300580000f03103030740000c00c484c0050281d0740c1d041400c010b00c2407003220402407004000f0006942c444014402d10b4001c2d00045000c25101140403030902c0c0510140f0005006603401004180e440f07a003440007524011400b04e800200c000040d0030220024400b034405030100382e8120b0000d030301e464204400d091308015440e041c80f2040105000040c0046494190720f60142c81c0840d21209601c08180100013036031240310140561824096120b60000380c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 179236690 1250 179235440 179235449
    0x90408211005010e2407020a0306022106090a0908040f06020708060703050f01150509090c03041b051003052d010801050105060910120e0d020c030f0105010e0c0c030d09030306 77
    0x6050304182c0700c00041d1005404500400d502040e098400d109414540c280d00340e992521814003814264540c2c00310318054042d40044469540116541140c0c0e01603030a00c0c1c2d280e580481d00320f082810302d640880c440e00f030003410032401540c91340048414819018102c1e002411080701245ca41a9604802034440b4014042c1a40c5400f600c008114880e1103400340a003e50403440c3d500b4200e9192600303002001130b004401e04140003052002c0710107559600c0c0000c0c814001066107592b2450700340340c51141c66542c04289031070820114018046901c581284200c228280d08000840e5100c0e005a81e0120030303000340c1140da00b8040304804c00201e0080b00e1450403a0704250013803005903215410821203001e00c21000f81c101c009078521200b2a4420300000007441d60304e200c0020544a64546a400e008450344428056441039050b012581030401c520301708180b0100c001c00080d41084598244200e003e01242d8007240007207419403010740180101c0b01e00d401d040c3e208020384603181c80c018002e0840e6103c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 179237940 1250 179236690 179236711
    0xd050f150c0405090c07050c0a090501090e06010602060a09050c12011e0207020f0105181e130b030601141c030201060f0b120103120e06040b0c011b090509040821 71
    0x481c000603101c800b594182c440040400505a841d21030340e406035002518103079140e01c15800c48c00c00c561145138412010304580d1102041540c1010600c1007900c8101400040340c1e030040c0010896640d001c204580c21584003240400e002003241001403610320001521a03200d0101e200000307a50105612555014203010007c10819512014101c100e0080b00d101a40168405401340590341c8150f00070801c40c10822800041d8a1901c030224540c1695862844407805800da180d0006140411070382c1003980000d142071042401003c042600c035036040c4100746a0041d60310540d5034aa840d012160007940c45050150203ca105041c024040e08040c4200d000c56140500042116054201111040703504d8801d10034259185a65220100111891682c07c0114a42c01d2100540d2050002c00040c0446483d403034542010b07240450844254a6030300d20034181c42c2d44141c3d0302c0c1d030300002c908089070011200c0003a1541e441c1400c4900340315642c0b82218012041c0c0c01011803103400d5a045014051404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 179239190 1250 179237940 179237983
    0xf020705090a090c12051c0903060c0504090f060302041104030317070e060a08071e020604031101061203120f15030809040f020c0604110a06140304050304120b070e03010b0108040f020d050f 83
    0x7001c1f1012640a03040d4000000d6114200b400450000e4002011a0089140c810701d460b0361a00200225a40c00400c4c1200c6901c5880c108154a0103010302131013036032401d40035460030786160b0300075000b03051042e8800b002100300c1e00024a42030240d0445043c0b110094805582d858520b40300918a040444940d40410343c0d0030b2206030441401111201c8200040e0001d00454403a0789003078542ca4540c5138040e000750340f0307400003094400d8103101c3c207103400b442501c0c2e000d003c162161114080d1034036120080d0050f0b15110f10b030148440720070f59800407070760040f030310555174001000454050f00507008802c10050000075000e4844c4000540d80b40302e01d003c2c81406803010019401c100ca90701c0d0301c1c40744c040011000c0c41c1d41d680c0080144000c3d6040b030f110350212441d050761842107850f00d55048a00380c4100034000c1c200144a90003401050743c1c1c0744c0841c0200844886200003910015011b44050490400141d40e03108540b6030103005c002c03854000c0c04a0b07100a64240401b076079511703c2e104103451170000d070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 179240440 1250 179239190 179239213
    0xc0b010603050717090f070807030309330c0204020315010e1905040e0a2001020f4c05010504150e040816080301060504090605010f020705090a090c1205 67
    0x1e10819014203d2940e408004201445810350382200152510310341d07000340207404285800c02c0150f00010302d07905001c3c000c403500d1400d01401000d40781d441800304030b03041030201452007420280c1503010000340303200400c90400e52804544410724584001e40051000040c010f145140b00b506c551203540c240d03207500414500500b80000c04601c0d040071082d00019280600c0701d072401c0d420110100350100210703682c0b02c03003a071144c1d40c3c074951b9000c00780d0010b2080314110026580c144412410100c034240148229142808812512607484065800040c4c08201a16032070701207018180d540204001881039504403032841c04000d04081c03090502c51440c18000f2580200400c42c40001c03141032843e290b4580c0d403140c50b1294183d0000344008a401c4154400000040b6207002171401703483c031039403440c1d1140d0405006004a510720341029040c41500310062020035400201030041e81c4090300c0080141d00c9407001c00c0c01400c6404d60042a800900b131020810350fa01003401c00b07009000e2821184d00c00c005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 179241690 1250 179240440 179240447
    0x5030403170403121a011d030a0516030605100e011520060901050612031207030212070809070b04140f030106050301181112100b06120403080601030e1f0908090d030c0b0106 76
    0x85581c00b40424029948609031410007d00c0c010750401c06826030300c5c440e207135959484c01c0009a013012380050300c0c00c200901c240046485003984c890a40c1707210b00f0940341010b0100007964414032030b03400712210307940c0440c043ca44122940c46c0384540c08510000000440f11a140e22580c04990020a9601e090001150362410ba4010f421000000307024601e00303003450180c00b0074500000c08040505808008880d6005a495130103441030810365207054040c00c014220f00d003401d40340c2d80a104412802c1c0800e00841050341a2454401021076200561031070040c042409021654817669140d460900050b011408108441d14010301c240008001128003400b04200100d103d80c0d6040b10b81d002e80101c0826046507404102e4458006000d0741c1044200300c5007200d00c860803a0202c00040d01d1000340b21141d40c06000e01844072810001504040d101450480100c00b4110185018140c4466a540900c40c01030110381990742c0240682850046909020700b80100000c400c840a01070100000f982510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 179242940 1250 179241690 179241731
    0x5060d0b1818210d0510030b10080601060e10081305030a181703040b030a0b03100209180f071215080c0a08030906030109110c0706111501080c010503040317040312 72
    0x4030243c985090948050038030f802410024607018044810803404004541c101250341d01c64803010380c51501c3d00f030400703081034244001a03018009110a2050105081d607034a116040345d40b200785003911b00ca5584000400c0c00109030300c0060304a01001600c58092741d030100d100703028811428070b401380682d0780c0c0b03202c0d054003440400120380780d401c1813006000030348450001315080316540002040705444800003d00780f402124007501e126074005007455407414540105c502c80803400c0c445484514060043c2c0c250b02c60020041c01c20058050b4059500b800c1c03d070702652110b00d5003c0241081600d4858042c2d07107455030660303288511841d02000460039000001c491180310050401d40c250391070100c141002d050341c060003814601d002e1001c8060540104600340c000c22043d41c4000c980004100d5541c1000301c2503102400080c2040700600612340009000030741481c00303103422543d0307a03691b08003142c460602d4071540101e03904120600052541c80b603180e0340352100da00030400030800441d160390311816 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 179244190 1250 179242940 179242993
    0xa0b030606030412120f06050a060305060d02040507210b030723010e013005060f150a09030c1e0e010806060f0f0d0807051605060d0b1818 61
    0x1d90401c001400a05540d42a0100c3e28150a1625112182580b85816030304201d200c1d0701c403550f5a038410443c0389807050300301c40100b886050801040c180341010a589500c41000139004540703030000f25403403a04c43e81c1c0c80550510a02c0108000c4882c600003180039050b4410740b031f4424030400401250901d01a0801442c0104410828a010b03810360015035581000321071480c10310940100300201d40543c0d180f48095081d04940000245c3c0c0c26400401c00c8071405007809002d8509001346c65240c1d00d03070b04c82000030a0fa159500030b4546a40d0002101c0c038125981000388152180d1400042091224034003ea040705504003ea041503220a89171107201c00034811034403968020b402151407414046440044918050710761460710a4a502054189102e84004c403200c85001440c0d03c14044c0520828603082214400d603501d00e45007100040d040d00511402c6001107a40b0240c600030341e910400d401d041c0341a0000500440d2400100c111510038034800701c46140d003e8890103800d003501c81081c84403400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 179245440 1250 179244190 179244199
    0x20301140306093304050d020f010b0102030901050f0d060b12070f0c14010e030301080a060f0204030201051b150708070f030603170a0e040608010615020309221d07050a0b0306 77
    0x140f00004401c121103001484501d004a0481c042d0603513405240e03000d030b1182d07011741c0051000b0410100002c0c03400503504030402e1075924082aa550903039000c03040b96400039091a00540360b03451000e01c1b803003030700c16001440038191500000003140c20080c4040c0c141803011420341c800c1d5031b0315450261180358002407071030300180d0104c00d40c00010b000c0e00102c5441c41000ac00000f8682e58075040d09140d6071081e002040c090f40490000c40400101c0d015a03c0c860507881010340c1010314643c0047c000d40140e40d00c10400c0c01841012411540007000412207540201c541000325040044002c1c000c4070042d1101c0001403241c0102e002028060301070541126407000d103030000030f0722101c08107605412114882c0200030308411100035542c0c4a000e046e02601d901c1c00005441c0f807a02c600288079401c1c0d0103e100a54005001540780ca69903903100c0c8805100100140c0d107554040440c000003401d01e0840340c820005590800045e04100042da4810744000382c03010b0683c291200c0080309240811601107502 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 179246690 1250 179245440 179245453
    0x60103260a1b061406030c040204081e10020f040608060f0904060e03070b09061608070507110111010c08061002070806160905090c03100501140d090c0504090602030114030609 77
    0x711442071140d0302c2500c41c2c0c0c07002c50030800142d40e100301c00d0344c03446142900c1450801003840040d150501109011002c1210218981490b2002c620b80750040501c02200d50031000116801070302090001101100d15414219921117429810744480d402c5401424000303100780002070241d040c14842a804881c0c01450328034641c1d43c60341d40c900076000e240c0c6000b510b400107001280000354845080c071300580c1490041c2080b442d00e103056580c0e41803c1d00307a03041041134440c244080070390000c00312420340350000c103604a001103890060300e9a080c1c1c0304260780150711700031700604080d0b4001c1d4ac450145500315400e5562051003101240d8440183c0589a419048200030a808400913502142520114100b00f10042e0741e9800080030200c085075030945e0210f00000f0000701d10110909070004d0f02c424202820190540d108141c09805014004204955a0401e07142800310340b88810004210040090082c002c0916201c2c000e9042032060b4082d0942020980c907441c50702003122441640260003c210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 179247940 1250 179246690 179246707
    0x10213090c0c12030e0a05100b0303070209040809060f0d0c0f020c030d080a061205060708090a0c05060c011d01021c0b06091005040b0d05040201020c030a0302030f090307050a060206010326 83
    0x2445451082c00f0410b0655030311245000e02020b2044006c0d1901803000b070070051607100029420b031000e404840d40700c1e4000300a0000140e0b03404180c81d4001d40c01c000d00c0b0f40c0300e00110b80881d115214001102c000c50a003c66a0b409004250704003104d01ca10300d0369521400c0d089010241c0c1c0c5c424801a1203641508040d15100e4110f11401c00142c0c420103840e0b0100710b03596254940c2c402d02060410580d02900a401084034058000309880e82190034440100014109078451034209030045c01003a2243c6400201022070410035080200406009440350162000702540d641c002c1d0300194420700d501600d500284825001ca201c0c0040702c4d80007a18040c40e00404004011000303050900304814040107100100d54000320101502428041d200001440d04240c0000f9141c20490040607200340c0c0000080740002c1e6020082c0c901000c000d03048180c989094400107070074100190405d41d040020b200002845c5c0e80e0029106040324040c85009141e28400700d1402141190a005e00000f000d0410200b078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 179249190 1250 179247940 179247953
    0x10f17150105040e010306092604090207030e211605060a03090f0b0a0902181302041a09100617100302010e0a05040203040f030212090315060d020a08010213090c0c 72
    0x41030440140341030307443d194490303440c060440c4c001c3e0010f4030b081d681d0f42c0c81c0310300f00802d4102c1d4500102c20748036071070b0135100e503145c0c058900d10603030080114058011840f03504060054808040c1800300030b1111651030501e0f0403007011400502103000461044e840c3c0c00503d10b00410604098600141035245014102d020540180c407a800c81280ca002c001c0303c2900c007113070040c1c2049000f107060b0039021800102900400c410440c640d9079852282c044081405180c100070750103007005503415100424044642070780c03640c624508980003a044940882040201300c100324000007580c807551901440d0302d203209100c4045d0101100e070481c403c2503020f014000366000740720140d00c2400040c100d1030030747d40700c9002c02d0507a0130a0746d04036900d8940010303007020981c06200c3c01241038039030f0f44c41c1400c08006200080c0d40d60b50309440301295001220202c0d80703d407200c0d10500b4245401904418680b66903150041c000c0d0f2000305202aa0590f0303000c0401c03059410300800251110a40d14100c901c9240d45840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 179250440 1250 179249190 179249221
    0x100905120408190c03050d0302070201031d101e0c050903071a030a110d110a020d18050f03030d1409010606050f030106180305100c170408160312090b0402010f17 71
    0x2640d40c4c070400b46000000032000c01c00d84100641c44d5902689841d140e1002500f44c6800510700751003c00e414480026a0340c1c00102c091704c85c10898400304800311038042e8601d0303d16109011900241c103021480c40c041c0d80000041001010075401c40c0d5000307540314a44078524840c52100700c1c1010701080401c801341075035003184403000c0342c034080700e40b4104841c00c80d0800c030b410100640c3d01c0c42c1000701302143d0715a01030009031000c007074a04120342c00031001c427624072061410703024041c4280c150781c0c0b0251a80e00c0410a941d48600040d000b0001c2400e001d5080c440b1200840b00030300990708106001ca0031313911031400d6403800081001001e003107900709182622000900c111b603c90344000088000040b49080010300c440e401c100d1f40005e0000b050100040c6170648a8428940311744c800828400001c8004044481c80820341c0000941ea084615017100c44591012010310b045060a21000c20b1201c1e40254a000760f200b620f07480341e80c20110304141c540020413198102400035610010f0860001d15001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 179251690 1250 179250440 179250443
    0x9050d0b01180e011a091006021c09120f2d020105070f0f0308090c04021e0a090f0e0a0b010e01090501080705070807050d03060f12020402130810090512040819 70
    0x200d1200710b406143d5084881900e011035030150013403141181410140c20f03143c1c010300741c049450307503841c1071410196680c5041000d180c1e51407440495a05d0035485481c03001d0180c2001c406111400c0d03014142804c1010b0010340959810031032000104030110540c0640c010440c131111409020322068006641640109005072006041c101201001501008110300c10a2103511014258103240242038581980010018001d920400640003460110680c04055403010800550345004000080300ca204140c1d00c500400450f505c00821307034035501e061551060200c65400c000400c98440115100d00d03c916000740420280001801994491902240e0019040c200345140248030740c2d66200650004106403801c0d0042210414100d500d801180000d020040d441c0e200e440c1401741900c02e250410750000d20450340082c0d0780c4001240c418203040182942d50a07a04100f01c813030f441ba406022801e00c01c440c18061108519086244902620203691108000f0311407501e6030040040ca6100c400360 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 179252940 1250 179251690 179251739
    0x91504060f0c15050406090c08150a05071713031206061b291e01050108071d04090503070611030108030711040207080c1b0907051218100c09050d0b01 66
    0x19424100c1c00a00030f183c0502e21402002506200740c1c00d0230441040c4039003000445400c49e05075000502e01100b20690003602d030110000c0c041e10b82c44001e64010310318100581a0820100c1040140000c1004e18036445019459140000100740c80c81803c035115402020003044940d40e1b040b464040414503000711a1186060071400444404d0419801700a02d014240042d4070404101e02e04622107211a1b164288601680d4103504050011b041880e00900000c10058400035450511280703a4541203e4000a00f040000701c9250412940320b62142c101a1607003800c103000d5115141340041200e04841c08a00990305003111681c4003101c070070b140ca201d10361080d000e00c00440800c081d030000344002c602e0300c00108500c01c00b003c4004000009043e206200c1d5440c10108a0026042000c0f1203c64245006440482d5200ca90540c2d0707a081c0c0c039020304128410401a408440a41e80c44001100d250751103442020b41e50350104024046021300050500003410010003030340040b1000760f640301040c00c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 179254190 1250 179252940 179252963
    0x303050901270515041406070c050d062c0c0d0c1805060312071a0702100603060507090503010e0a020409230102030103060b010804241d03091504060f0c 67
    0x80c00300101114292030b88110741031000400883c90000c039140503125003901d2240c1050703d04020003a621448412079802400c0010f004002c10201c0b0001002030a40203281b07040d46411810014000c06484800941035600310144210034000b038120a68140100303c024000858070301c042c0980c100a9802c111a140b0201d1000b156014507000f482d0141c403d01000000c1520b00341040500d010806003588001103030801c90356010420b0303c0f004540090781aa298030b0b807500c50a208a00d8551500910f146203868984044100200740d04900c0c043c0025903141030105840d20100750890b0072403a032800c400c0d4400d250400050400780c0003001c00c03e0060060b00c00341c25030b0014072a0003131440c4d59001820396000006004010040c414070701005001c1c0b0740345010f403619a840f1080b407021002c804504003881040e0060ba03a045800100ca2080070f40c02085e0320019680c00e141e0b03170741c200d50003040c0300325003000d505c840314031a900503241150505d03511004502d2440074165000c28041d40280c030404404c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 179255440 1250 179254190 179254217
    0x2010b0405160e011701030f030507050d02010b1002030a090905060d120807021b090414010b060403060614010c051203071e0c02120c03120313060905030408160b040303050901 77
    0x1c1c0710745031080c280c2400d1110300700c28500300180440000c034a014140100390300b000003d5034105840f581540d84c06000e80021420908050b140303401901c1006225100ba80b486088042d41908442c030b0b10b00d02035442603036149000c1c406036100d014441c140000605003500800400242e0f030841a00b004002d02456a0b03824182c1750a00440440705050000c40e0442091050305941040032203402c44086030461483c40c0d00c9c00014221400240c40503020f03c40ca140e91240e400741c06e40c1310a00110300100210764555692600e800034048504c07480005070f01c84440c4042c954041c1001003000d07680000501590700c412006000b8903000070700003504010f909107403c0321150016080108417180c0b526504001900d51040181c1d000c2698000710140e08064250700c2c180d02c000072610038418030000c1203a220f40d262079101c03103046803409010b040c2d5402c0007081414454044001c0c4280c610702403c0e1111180e4420040415050a01c2a000700b40c41c03c11007080404c2c4100083e01c400c1c20140751189414414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 179256690 1250 179255440 179255449
    0x62102090f0a081c0504030317060f060309010c11030f030609043f02150a0c0e0402030c03040218010e1602150a0b0a05030c13021308030a031508010506031c02010b 72
    0x58200c102e16a108003011210329000e038204c6000c046107444c2c4185801e055540045c80c0d05c0041c8a25000414003034003003201d6556a0348001642c03100a04003d80300c0c9440380700c030340c080c0569442038008181c04c001201084100401100c1d1032549031520316281d52160030a11009080092040d11ba80e9240d02d205038000d1540443d030480c04401d043d5129034951400c2e145008a00341003d4103040d5841024644188450310f4155075015642c86070000320f0810a20040d42c114800191180d4020310001c01c105d0311000101c041d5004c1c90003564004213500c122031102c120140c0c01e004107180c0d40328400000d5825101d08640d0001c03d41c83c0d105031090842a0150b1440322001036844500361516024120918180807580c5401400210018074590805a02040c040c40740d00084801a60b0005043d820007000082290010009002226070300e8030000001001822076613112070102c0003004c4000b504610500845010f0b01004010b480107002ca0b0f030310258001490b0620b1002d554a912000110750364 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 179257940 1250 179256690 179256709
    0x206070203030c030a0806040b0603040c0303030b061309060303030c0c0b2202030115031502070816080f0706020904060510020c0103051023031005010803030c0705030f030103140106062102090f 85
    0xe450711165041e003014030400096822030100140032b403e06204010200d84044414000c40780c141c200011004004001b09403503124901880b1000e040e4143c00260031503080e80b20b0b0007203038000e5504010300ca041641c11a0400306016018024016038400700b034003802481c0108a42340910700142034009031680c01b10b0300399803071080941d20301200d100e000c009000c6655112040d0600400d0114135103a241d41c0d40000d103005130045408002e540100d00c00070810b6180458411800b034103d5144c0390746071031819102039805a6241e1b4003480c14204009002e0810325600b01c0303404a6178020300108400040110014900109000228442c1d0140010039004040310035401c2d00c06031201c4012030341c610040c146006d80c2038032001c68003032500d80100072581c004000e0ba500030040d14812a514601c6007000c40c0f0758081d044c2e602c0c18900c8000000810460100c40f00360030040b42000906c88159903582c107564440400d18408140700e910000125403614540c000c1c0403c00005010140004504011640640 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 179259190 1250 179257940 179257957
    0x6051203030f010b090109060305060d0f140d05040302060307050307090b0307111b1f050f120603010b01030c0e01111f0905150702120c010212070e12190206070203030c03 75
    0x1000002800070701c02c001e42d04203001d80720340c0204924207040040001c00d810301c0d80c45003404150307031440401d44550303840601941054106155480d40e031118200529000349c4000c04400910039550b4010801c1e0280f0255070840790010b040d5811951400804c0e1101c2d8001802c0c030080012110000c5203505444c405036009624540e11002d02d050300f610b1841c03401c081c641010424100d0326111421581d10903140303004180701e140010112880401c810388560042d40b005120041010070740c1c041d15485019403074481c800c1103000f841216207280045d02211541c800300400200c010301200060350141031001c498031420400c483c0740510340d601c5499a01c585003414003e05840743c09020600c20100216011014129141c000c1400c0918002e03680c1c42c0452008460450301080080c205142941aa004140c0e482c00ca481d2602d803400f0000c6c2aa2191150644100200c580c070f4140c0c401c00050420501717603005458100d1200030380030004a90440c4d9070803a818071003000718180d1080c0c00d00240800c40e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 179260440 1250 179259190 179259193
    0x902100305010503150c07061820011e0801060f020c060711150307051606091208100b1213110a0f0801051302060d0e01110f1206150f090301060512 65
    0x354100f404050a003c10301c500c803610300003a00c06110140c01150b00716400507a014200103082c20900071090302c408101e050180140c104040c0d468200048844515002c0300d0036690300501d07003d00c544083c4a081e0011020000640c0ca800612440d80100c80c08402d0301c0050040710444404a000941c0650144100700e40381c0070792190440311404d24450400c44d8030b521030705242c1036240082c8018198010300c0415009203007007850b26800c1c42a00c0d408000350540208809520140c1840054081e16058445001c5000c0c100400259120b04106070b400c0058040c0382d03107109444003c03034042c2010b410f0006880314a04e8080700d042d103a81e1814010001c02201c1c580011161404103000e0031100001c0200c3c12810100c44040d005035107140c1259245000c2e01304c009440c480c1031113460300411b2011203207901032000103880140100341e0000f6040f1403041d40d0b11894541d44040501642413107002c2c00080d140400c2c07041010150461004e0400c0700000f400026a240da0380300000e2200c40b00c010052100d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 179261690 1250 179260440 179260451
    0x60a050a170c0f0108040f020d0605090a141c0c0203070807230d030c0303090c17030d1b051606020d180302060a0b060d0e100903050c0d020703020904110409021003 72
    0x80c00403082c400c00c12075035076402030488000a41a104002c00080503155401845e4046656000c0e6005015400034010041480d06449250f910422181c069544450403800c0f400110780014010081c542c070256a0700708501303048004d44103541c07081000c03a0305005441c80400e09030030410810340106003552a541c2141861b007509030112000d02e03085409803005000b0640843c0c0c001c154464100d515160009440080b0705040440c2ca000d03400c0106d00701155010308814050000c040c0c80c0646031050108803a81000750508101501c2e10012400701e1000d00411502015009031135010340d0041c3e2001d854650900068400c58a4030f5120300c21207400494031209140d0304100040d48151007000030041001140c0000c0d0060044c40c840c03800c0c00342c480c3e0362b000fa0a00d0030b200c44994031345540d0b02072082815a00e009003054000c018140d40c3c0d4480d10b007120540601c000741c00c0701201d401070b000481c2e03515640c445803541e00d8041c02140d0400d8407100b07444010b8598010f03c0055281c1903400040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 179262940 1250 179261690 179261729
    0x201020903060405011b03050408030c0c0c0301140106030e030306100c081e03041211060105040f140408180a0b03041203060b160303050a090309050d2a05040609091a060a050a 77
    0x1c042c840d0b00400c004240c42e25080000080ac01d50840e6048007440c8180f98441011003800c0e49800c0307032182c4064040d401c0540402490705d800060724181c41b4162800d10045c4890300225960703020850301c81d41e1010702c0c10f1007045a0fa00441c1c0ca0041240503401ba9440c207006025880c00003031106c0012402110004200028001254241111a085440c0c41d02039052038442040d40e685043c081c9520a5643d604440c044030180e034020040340d41c1c1106d00010615203810003c131395412600301c8071000845640c85402c40d2031f103181e03070b54142c51510200754195202c1f40c84070100742011064410900d5900d41021440c10b00c03d0000c1e21024442e40182000c1101901d030040a68001a00819400d4103008848001a410604c0001030301c6080ea15142d5071300382d42c01c3c0012084003020307510300b00f11000042e00301603000013000c40003500c0c001d450074855140e483c504241150760300c0c14040c00c80d440c03541058506c0c900004102d50404001404d603003c25442d03400043d124146a4003030b01c0400c4041d05981d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 179264190 1250 179262940 179262971
    0x60e010210050405061602030c0d210203060a03060e01021201030803070207090b030304060c060b090115031419020a0c02100e0a050307080601150207091404020f0f10030c020102090306040501 84
    0xa551501c081d00034070041c01c090355225a9070001410781e0b000040960750200d89544200241c034040202a8215021184a00c102410014070071030310540a1080345824415211035008490290001400704811145540c8407600103202e23101d40700a06540812102102d40180069240030303501031360820f6030300d00700100702034a4010554000c034040c0c0e04214400306680c0d008810b44045aa407800d04070000c200c0c41c036202c0001c0224000043d4840300d80d40020030024221072420700d0005a0303890070054031180c03c80780030024200b01c0764011290741d0304454052640d003e4000e041d044d449414044100400c03980054058080d020b02000001c0d052581e02c1d40b940340078540307240180381c223a024080e1103061106040e210f000c140540c605c0d100e00c82d00c800544905c2080750300c004040c01c410800c5001e20f0310018041902054906901c6001115648000c624000300d0707161200300000c0200b02c000e89602d900364064107103104108107655090011100e036440c203005185c4182d1192000041c09044040401e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 179265440 1250 179264190 179264203
    0x304030521010305100207020f0d03020307050d11060103030e01050706050106030509191109040201020a080708120105041a15070b0405010e01050f0c030f0415020d0506010806040b01090905130507060e0102 90
    0x1d44400000c20010008940040b41d10085400840005640c800b194000f00720501162001c107034101410640d00018154040080e05506114005841c0070846200d4200c50014202c11030850b60307000240100002401442e6004c000a0181802c83c140045a10365034111502640000c000c6625001000307003090342809440314480c00082041c2e00d900290302e440c10741001c90218607000c2d008480c04203096a000300b080b40445680230214583e02d20491a140c0c84a2300240b180d40358442e01036001082c00d1400380950119880e24640140c104400b08007003160810380008211880d0504200b0340020500c690f411034882e070700800c004039002c0c1a8580403400c40380024008164030903d08144524908140c0442c0d0704882e400b022445907459500303120392007002c81041034a02034400149982d40c0b441031b0b004188545400d07220001256150342c1840141c440285481c0c3c0002e29540d01442108102e900040d04514918032000c2c5140c8a40d0300c0030324002003500708502042910107440015a03040000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 179266690 1250 179265440 179265487
    0xd120e1c140c030706021e03041b0510050723010f15050103090f1101090905040b1506030105150f090a080f0d260a0902090a0606020f03070b010620010203040305 71
    0x40b440c1000d01491542c480c050000c0003050a600083d9001703850ba40c2a0031008800c00400c19242d5a00346460701c20b092155000142401050505001500389004400c103800220152521490f06006584009070350422404144241c0b810020032101480d0034031540841c0c004600e4000340c0e0003a050451f0f141c8050715400241098185a0600c0004a50f2040d1000d416401075010f050340c02002d0059580b040c1d03542100015900d440204010b00a010100c0c82c05035040c00020403190503420148040c40c8400d00407190440c11a07406910400012030050000350303ca054403034103210002002035607000950b4481c8209034030041902d070220740c051100b185001c5407400d140303030341d50703420303405003540040100b00307a1043c10002c0d00059201d112500300700c403942d80c001d1009619182440c0c0000081480380036010051041901c2802c0650001088606054001345207442581c41e20804840f6818070001802d074040d03a0310740341c03c2039601c240050360041d403007a00c966454042118940d211f28008481 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 179267940 1250 179266690 179266727
    0x4090f0b0a0b0c011b0302030114030a020303160309081002070c0e010602190f0218010f08010213050906030a0803091e0c0d02100c0507080703030f110d120e1c 70
    0x10036481d5079414030303100484001c40c428645a184a1115500501600b03c0d0420084459448440402d5150b4000e50507181e00b04595030011201205040c0d6030420980025010740c02003240491100501101d045424842d1921000e50343e1078054190030309900d070031300150603038000c501c0304108035082130312001401b02c8120f910519858408020358840804c9809a207013900515a030091001504d580711150750007406614194898250214014109209213206250b00c4c01c40416000e006008a07a055050001280a80c608040070403000c58006892951301d032040401c0f142c0050340c0003000e913120303c1c0c45202a218000b48880103070610001d00052010580042414002d5556480204460182c040c0c0b0754101000d0702001c141e031317154000031020f01640318400000035080c00c0000d030242960f01c6a5210500d01d034201e1010703a4641756031101045503400c80d1070010180392240c0c826811448180f20701107540340c85106000e080460104c05600352101c5c1031031051b9583d4000f480340d4450300c0c0d0b001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 179269190 1250 179267940 179267951
    0x11191505061806010305040c050d031e050702060d0506010201060e090606040605060a1d040f0e010902040609020f070609020102030904020a02010507230a0e030a060e0706030e060c0406111c020304090f 88
    0x54902d0074640004103400d040c156150003040500a54034426406480c0150228060352042e04001c0e0144802c0d0071300020141c080da4601c0417079446072007921941e0b64042e110a00b44101d6400c51409050014030050441d0350b82c4100180424a00c0c0400c0d0185852034040c05260030030005000c25200e0540005004034400c2180c11a410744c00986002c90012211812121250560004011300b4490300203180007030411510030071403d03042d8000306000f0310860b8100f01065503411480e06078090030080b1515030344107201440c082040e9401505020f071052045da860300007908001000c80e0013280c940c400507955a801c1040d200d42282006a4419041204e000e9042d50030862140e2803181106c2035013003050600d03225625440811000d02086d60050060012200f90105075956108500c1040c000a0829028030503410300400d41c1c82c0100303281d514441c0340c5802d010013602c0901030b103030100c0c00034424001e903103030410301c0c00380d403490780303200c1540955512480c2400f14405e03243c80c0386801801a10b0103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 179270440 1250 179269190 179269219
    0x1151703031e0901090503031e160e090705303d08030d0c02100b0915011205070801051002010216111201151d06010801061119150506 59
    0x400b10701115141d1000c90754036564928085034094401a00d00030402e110100910000381800e00001d207480521048203046903590520038010200328080c000041541141d4030886800d003a00001e07071003072040c18036500e00425059811100c3c25100030541c0742d410400009002903040c03400854000c980c000d0340da0707010f00e10b0144081108181c1d5480c0c0c00740703c0200d00141d00300b480c4601003100900380101074030f840349d4030201d09101401e0b105095000501908000c80501c500610455010b17840c080c1040340c05030341d14034030341c0c801200c820006810300209501116548080340517051040c4070aa071103a1455140c44180120040b8030615042564010b0103080070f00c101410340d4205041e00460346250200d554070129421088a00380c0800c607501b013041c56500104241c1d0000201e42800d400d403c000c111200d00c2c6114440161812400034641c2001005250322400e14501c031204e80700155811401d00303000080381001d010004580200f01c180013880307078200034440d642d030210b001e9542c84183c0703902d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 179271690 1250 179270440 179270461
    0x5041e0e06030c090a0e010609020d050103060b010912080a0c1202010c090f031106030a02120708042f1002100f0b12010b0307030b04060912020f01050c130b07140115170303 76
    0x50400182c251b0b00c2c5902c9240e502c003500084000c12490004555904a5015040161001b400180c03210707401c11009503a554400d6035154219201c500304601c000905968808060f0700480042041280c922039000220b200c0050000d000c5200da0000210b61010b104060100000e56201c02c00541903079000b04041200c3c6003038842c51800c12108141e80b9900c0e0ba03200c400a001d880b101c140c04052210421403002d400c0030006005030700815000c004002d90180303000c4019101d04034401840038401d0007592034140440804500f5140e03006444008004a0185040358104d540780028661036111421135400c01c01c1120360f4075140741c0d0080c00134141d07400100f13948050505c4028404200e4000040c1440501d5100d9046180d01007411000d00c030071882e00079900c00c0c18150071450340d40382c00080f4040c512010f00b100c2829a81444800a0b1440d0640300d0180b42c01c0b00f1810307244a6000318595603c10801c1c4220b903244104001c211005600703000500d01d40400e0918403031255403081042c040010300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 179272940 1250 179271690 179271709
    0xc140a050a0801090219141204050f010515010509011b02090a0f050108010605060a0c08042309070e0319060905121c140f0a090507090b120105040f03080705041e0e06030c 75
    0x186414144a0004c10511100c07c91260003002915044c0280520081040101d4607407000c905007002070000380c580795148001322211045943c0492000c12041c56294001e118040e500c80140440d100d264125030041020744d801181c41240c0079039500c03821014441c451040030f01604018000300f03c402d0910b0302040f035502c00c0e164010103002e601d400c46410424010101d4020f460a07041001e150380d89264191900b41301d102050b4850210840000c2006104010342c4035202030041c010881c3ea1a080c0b04000c1c41c2100102c00e81c0c0043c1c44082000100e9410440d10941c0d4022000c6296200d4001d601c660041039401ca55401807170501c016a42c0242140403240d420904c010342d41c4c1582d0b1a0050560000d10060200800320b000382800050f1081d1168041c0c0e00305942581c400d403404540c1c02205080700c03022a001820404150a000003084c401c6c50002e0380040982406441c1039181c00d00380510807140400018000240c182c14001900c3c60542603401220075070042000c4a06039000595104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 179274190 1250 179272940 179272987
    0x203100e0c22080f0c041d1c030b041d070e04030807050306040f230105060702010c0f02010207030512030103151103060415090218040506030606130c140a050a08010902 74
    0x568500d0b4000311801d80b10754802000d42034121100c400b11505442d843d0002d801e10207110307914200c103003007080caa50810a0505c07010040035041746a440c1d5551200340c881c07016064209581c07840c10714160744882c45002d040c94124006411a5040d14141d0703454402c0302d400c010710190302c02c0240b0001036040762049030021854141140c9039034441e0041001000c10460040340581404004960209910300b80e200d1100c5a2010030720503070302c840500c221440b5600000b800200701820090208401c1c0b5050274001c2d00c1441999145941c0b500c400345407103c50f280204102c84000010010005110b04458a90310406800d028107084000c0c14841800010302c3e07036009503118920001420002c20440303019000c0404119201d940b1000c1c1c0740c00c80c00a44401074051868400882c1040c0341c00140c07540314201c000d00078080500c10208003400340241c900e041092151940c95004480351b4100036000c0003034181c1d14251120f450800040c84500180d0045645601c108070890a03078102803500e41811 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 179275440 1250 179274190 179274217
    0x2030106051002150402011205010b090102011b090b0d0204090e0303190b100806010c060e0d1d03030313050f0303040f05060f010302090115050d0603060209030706090e18100905010203100e0c 84
    0xe545c2c0c0d000590304540071ba40001d0709070345020b0000c903032014114041d001c070000c2a0f0017000009064038542c0c00803034503480000003140d10700104000814024008084440c00c0420140c00c0503990070040b010384400703c800000300d03000481003020024950800c80f07000c001c040c106001071503121001c1114120303c5021002001a2400040c40a9004a212441c200e0340301d84104544d150b042c5665032100c995614180000d0086a140d01c424800440303060b440d040e004028500d10745840740c803440202c48026007180c081c02524110401168180051031056024001c415000c401742c0c507015051a40041c611020300810f07500500158035005101d905440081d01982540c0040c0b0a0694040c015603084500c15420040040204407184d0080e20880b0b10580c1142c1c0d00d1522110180c071041001d02a0715416406600021031040b1034010125a040220701900d6081a0380e80f03400080c3c50f003015090300c2c10b81d000020b1164649900e015980100104150404181006023240b0180d100340450744071078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 179276690 1250 179275440 179275483
    0x90604020c03070c081c05040f120507030503070c06081e010605030618040f12020f0c01030b1512010312050403111e0a030308091506060d241202030106051002 70
    0x480c1d20400c11281c0356900b105200742078030b40e503505083e13540707010125503031110b0040b81200b20b03018010700903202640c1c20340507500d03441814404a50443c07928180d05071418820540000041402400280b09080c007605120702201c0c20b00e00007901141000e0001741048a424422001c2060900000d80c107507440351404c0c41d0307030b501c840c0000341102e141c4400c4007051140e00d01c1440308200c90b680b01034030314501c43c00c800501c03040d8201c0140d0311180d5295620b80c1c01d4021000e5401e166102c0d6003c4445400d0052041100c94000860885544c1201c03000028081c1144018030911070f900c44000394a40c214540603142a05650302c0204c600c4552a03254058244000407111021120340e00ba0303203803003010340032070030780b40d52402c0041003840709403005c1140d07008a11001d00c8408261903103d101e07400180c5040c2c5402141c113582002083c0900c0350790458110740e20400011a4841c81d018000c00000700904180d1100e0300405085130060790204d40b06000072082898403036000b04481c10140f4803e60100309 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 179277940 1250 179276690 179276707
    0x71505160b1b0c100f02030105330a03050601021c1403040507170a0c050301060e0c0c011d15010518040f030c0203030d09050f0f0304090c03060902130501120b09060402 74
    0x512101c07001c03110003400b408542008410f5000401801580702440180291000c2d200403030101d20080c017499400221841404128100f9140003031882c111031031032007100030700d4400052280e802a0066a000903100c8081c0801503178104814040c034034030f150030034441e1100f40c4006040d960032000c0b010f82d280c5002c00080c05200c410311009004080c201d9511507026030008415460707481c10442104c032a150220042140d080510520069a0840e14085240c3d1102503900007030750030005501341d956403200f280220603c51008001d100d121001d00610103510700000030011080d058105501545c0c100720200c1c06030021400041d00942c2041800107400450305007252031940c0351030041c0d01423000240240e4004465402007620501500a0f6811a0310500030740e900c8107012244012143d01c244020f10203482e240c1d0202800b09201d0030b00203600b580d03c00c0c40c4000d9800000350003405a80f00c1303404000da96001244414070045400701000400401d03800201c2612001d0721007401154003084481d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 179279190 1250 179277940 179277961
    0x2a0503060f010e0d0f020a090203070e060f0c0109050c1002061009090c0b030c18060a0c080a0908060f010f051504120201140c0708070501050a0804062705071505160b 73
    0x2000d03c050102e912800d9141080141c02c072520740124020300c040e01d0000340760700d09442a41d0096000d83e4510030003c0440c01000840d8008a01c2e00526001c20400460117520900c9440c01d1288124094031581444008210f0801741041580065401c040c04102260f0418180301e81901c940350400600010103080034900b00c046030b003099500384800400e01c440c140400c400383c401c010100351030740c4080d500e0105129060080303440c1d10001c80d2410900c4000154002d002d0001c601003450013010665549080074a084c0d0107071010703a0b6240404d00140840040605090082c1006039001c5080b0710301c54548009a1081c0d10030694842c40909031401168440c0204030f141d034000208081d12600c100c544651985203a1149460301d104d4800c0005403940030314103403004c401440e11180307041e81e180d0311540d0280000781c20b9442420308100014039400d036610f44464059024400601086080ca075140a40f0701c0791503070380303c01c0c004207004024101856601034014a130344116040801d4072102c1d00c02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 179280440 1250 179279190 179279207
    0x102070e060d08040803030f0103020a1703120a0b0d030e0a090506010503010603052715070212091e09040804080c01092d0b0a050d050609040f02011409132a0503060f01 74
    0x118111b000c00400c0c0010f0f60398003840c0c14145c13802100c2c0c28403c0c07540ca0310000e961040744020650340c1d400c140003031855030564144072a40325000220120b18141c2e05c0d4009560b1404a50f000c40215480081e9642d0b01c4c105003803142c029101c0f0301c204108034102880040d013680014440c503010551503000003038042000210080348000900f19142c0d905d00062104c030340b034420581d081a4094500800a11a1480003800d024903240007108a4079100b05003041c000300340158410381d28644080710f200002610741081c5540b180b805520100e0f00c50b414100740c20708150b10300c060141000303440c02c2d0900c032100703441d003040a00b1700c0e1308480c1d80b041484608110b480840281d119600d0002c005c1200c414030b9421100600348104084020401030b91402d08118007500196805401178007940030700780c010b501480744520325801d4078521904200521001a0786031001c10115103840307131100109541c0f40c540c032480d22602c0d5104c1c140503000c0320904600401038013008200d688901000c000c2404641d0044100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 179281690 1250 179280440 179280449
    0x190e01060303080601020d0e1c0507030512030402031203041e1407030318060201091214220504061d040b0c040503030301150f09060206064b0102070e060d0804 70
    0x2403100079030307908000e4400c440c12940c450143c05450301e41003410788203015203514001e00070480d801402c803050381101c01c54110031085886105d03140340403010030010002c8041c6801075240c055502d142900c10f250070b101a824000c2d10204051062000164200002000241003100741001030600ba0a1004034514001c0c2a80c1c201c0c000c1390300c04402d01d50300c176038154540c0c4e00400d505840c080e03079817508034201c45043ca00038003500e030b0386080201043c0c0315002440c41c002c50002d005080000040d16074070943c40785401268480e8030a842006581007500442c8020b01c00840c030380d000b40c03825118103203403220f0040c001040c117500c0c40002000040b9010a84018000107001c8076280e603103920802d0185aa07003203506004c594140b000c444680d04c60456901954010780c00b0b00300d00d484120900c0fa22840e8409903612036582070003211391904440920950740ba01d14100503111221441050f1044110044160704540042c0d009110030742110542580103041504c0002c04030040c3d09000300c46000d180c12 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 179282940 1250 179281690 179281693
    0x303100b0d110c010902031b0d141c0507110105072319300207060813020607050105040b010515040303080a0207050303011d16080a05070903060c1d09040209190e 71
    0x541e000e6800f41580880076041c82902101d00d44102a007084070610100c044550340245440101800141d81014803c008926001207900d0090034200c440c0008201b0440c40c00095400b0030110207105c0715020000c006842820140d02e041d5083d1282c4d02110201c1d0041004040c01d502c10502230b180030003103005035108404071501c0070200341c40d100ca912110144460800440c0349500d04030f00904010544180c1c040e50010075a162400c41705403054200103080100301d014000801c00503031100c10040c85614841e100000751441d2910f03080c44200410b03005a400f0f1354600751601501103050040b58192505824091625601d141d017030030183c070904400034090300000c000020125815003601050b9020700c0380c5e100181d0b07100510107251508902011001990300340202c3c2e541a2981e00c000d070090b10783e01c1c0006005031030740c95590545180b41100d40018040000c1140301980401300903d00583c215000692404c16800280205070058102d040e20188103003190b004103550742c0100c510411490 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 179284190 1250 179282940 179282947
    0x1c020405070c0507080d02031903090f0c0e0702010e100e0106050d05010b090106030e03030f0421021b031902040507120903030606120207050d110f07090203180303100b0d11 76
    0x700020400c05190204659903c10030700046a02c030b40103d600241100e00e1f03401142080000348036283e044480c03041240034140d4404800012070f5010400581c461b0090030036a41c25427821164102c001002004003045901d07210f00300440f035101140c0760041000544c4042a07050b4140001070050a45900a0741d115000c44400420800c3c1074101480ca00c0d011108050160b0b40c0381ea095056485c0350784400307003c2d04200f0009929034050840c29400c28010307021615140d00307206a4400c41507924403a0400b682c451407100156885ca0641c1c0170640e01c00350060a204c43c03d40b1580601180b80040c02881252250b0004c0e240034402c4030003941c605114039003030004030518140503000f0a01402400006120700e100e2141034a8980201c8a44d075510000605612018007400c82d0039285007603082d2158010b1701d8000c48980420085c034005810740b8880141d4a0406a5100030300790034040402e5034a1b08140104003904248641c103000300e071703104602141d032040d0555844009125011011807940743c0030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 179285440 1250 179284190 179284201
    0x1107090b0301140705040b0a210b0907020c0306040b37060e0903031303110a23150109050a0f06080d09050301060b07030302090301090b0c21060604051c020405 70
    0xa03040580c10010a5008001030300c8103030440c040c441e00c1280d4800c04560300308070400c4894494001480000c1d810300d040481e180701d01a1803c890b0038034a02e024102520b0703640ba010180303003580700542c01a04d00e00040100d601980c01094039000c1c010030107000d0303ca1800000c2d02c41a941200d01050043d0944090350341708502445032030010018054400c1145030a0011400951291440b0300030300044d00118155900c4d1103c150510400002c100c080126181e480040c0c4201040607100d41485240c802484034203602001c0190140e10000c0480340d44a14105a010741c110762186040d1145030308046616900c6480c0e0b00003900072085601c13074a81c0342550000329643c001c910483c81c0c440c940c0d200d1051a070381d2010542a070b520360145560f4a001006002c000a00950040156000141c000300700d800e026180c0c40d04210084070080d088100005041c03a034102c804955201c0810103c0030003007507040000c007060b40360003180203180c011102e443d160405406841180180035900510600c05480d2a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 179286690 1250 179285440 179285459
    0x5010c020d0501200a090b031302130f0509100e0c063403080106020105130b011e120b0f0a0e06060d020301150902040816120b220807020f030a0308010e071107 70
    0x100b9005d60004255032030200c1c04507491401c890254126281c5951980c0040e000c00000848078001581c04c61781d070710000340030450b050080c00e12075007442d0301030100100701040d410300380ea11810030000c054100321840907140da00e21040d554000c500c00b000d180c20400310b0304c074101c5051200f11060030700c0320038100550405600c180014165091030340240020b440300100789032404500714004026058003030050211b01029000f40940c55001c8100001c02c545e52414401c05001062003503c2c40f000c907500f04074800141414032034121a00380800c05c0024a448007558a8460203411644101164042d100540d5400d4000004040c800c4050203000d03607503842d198000b54014441e10003079029110b40c4044d1440c031200d0100c11a041d40c00b01c42e1034881c46686031610010002d00c0040541340e082020030710b642d4074140c0035a1491103040000e69400c014010410107260640119220b03520560242d400641c1c0040c0680c111100592500d41c00d8850070829695800007401e4280284122400000c031000b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 179287940 1250 179286690 179286697
    0x26070803100317030f0a200c030403030f090311040b28080d110309060304020103090b0106090315020a0f08090705030a0308180102090d08210f04051605010c020d050120 74
    0x807501420b149500c1c0c40c0900c004030300007210000004280304c400202c40402c0c45e004a1f00d0720004030507060130500824040025070b04409510310350f517070001c5010f00030150040c001005c041e595042400d6014695a0781c00d0f2900d0009508900551300d5220b6620a0f403103860312480050458080b560103421001d8045a00500c58491003410b441050000c3ca40c2034001c1401844410b11203018602e00aa00018400c06a0000e00b08134101079450003004085950707140c0c604e02800e03603942c40088491640c1403448203044c2180302d981219104000003c521a08104038100c500d09600304020941c0c1c03042110707030803c2c02550000382c060044403245010103a102d0456841900d450105800444004611908034010b00c21b002e5000a10810030b48042503540e400703030219410310420f9060510200c420300d901c7d482e0031f850103908100e07000305000402006021480c041c480c85000c43d05403030315000c00200403910482020b070050803081c009205100d829001a0584036111071a00360402058000200c950f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 179289190 1250 179287940 179287943
    0x7180c0212120f150117180102031f0902090108070c03092c0a0204080d0503090f2b020606010504090f06210201090f0e0105040203090328020c040603260708031003 72
    0x1c140310024200c042600ca22030f00b440d4040c6d4580003040e5411200711180e010181c100307803d4150135054034050320300c2400150312414100158044e4022014003c924004264104000c464018042d139880390342d2010400b544a20680341c60a4049440e0a06666850b81c40e040308888280843d40340c40682d43c0030811000e5203080d070180358982d64030184010100c0c06a40140c10260300800702c00d14001b032051010395040440f51003a0751011404000903480c1080c1c00b2904610011030b01040364241c0d61a5000c0300b881559400940f0007442c08c000000d1139480b40d809003000003680e0b0741c2d03000c0c0c0303100c0168882c00c080c0c10009801030358601006000704204c3c4508a08900142c0b03d5800484d01080000b2540c0c00c40310301c07103a4021343d82d0030901040041e404c002d0120889202c24040090055032400390340e42544014801c2e80100040a0b10081c00c089000804502640c109401000003030b40030700081084400210841a07c558240300420651091040c054080d202c04002d1000a100c0c49420300b0449 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 179290440 1250 179289190 179289211
    0x70b07050c0d031a01140f0a02120a0206010509070f090605160c030b150604030b01090c030e01140615040e0103020d050a05101b0c030807110c0a06080109060807180c021212 76
    0x2813003120011070b00b03400c05501174511050180318481a1312103a00203010f10002a0042d40c004450f42506038803c1e0300803540c8500142d001000421160030020000c03038004001e880c0030340b0700f9083d181d005008181d1903c00c0e0001c01100051501c04918012844031500f644102d6034030001c1d540c1d051200124609450003100032820a06e2481c051a00d00d0031074007243c3d8000b0000605a29110324440200340a02d086070515480d0450b00d2010042842190b6000b8401c0020f2021810704600784250a440c0e2480070605420401c018403d143e14040c0310350449a0444241c0101d01d91440c120303041070818080242248940007001001141daa00f000fa54540c000310f400b030440c0c1180100321480d406c40386000d004581c908021425807485550701c03402070ac000000701c4102e10b0301c4402141c0307940c13030b00e9000354000b40502e00103022181450140300c0c0200202402010703001d0500d0718132840c02c418042c22404407560744c81c5c00c9024600034810b01d49249c0d40c504056468117500107a214400c0d41c12203824800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 179291690 1250 179290440 179290481
    0xb06040b030a170a05040306020c061603050928230c0603040b040b180f0a020405011e0b0d0e03070c090e0619020a0302070b1f0605090303070b07050c0d03 68
    0x39428005660a411a0080001507440c400d003080c0300382550040c800340d010420b04200200c0400c42da40000c2001842c0000285030303502d031000740c00595814035200c50007050b080c0020311943c030f40c0001702903000d640015800d401c841c484240c29503100b110040020076200c0b628103031184510800d40d403404280c446034140c90b0562141c40030020300b84401c82c0c0041050511601240215840000d1300d6441304280d01e200b007244031041042c514105148061001c10f50100300b0f01c2c4110b0402d405064010007421454072560391004441210061046c0611021001d0110f14175000000d0b0707070000d425491296050720f07502c00180c00c1496280c240ca000368100c2c0d9040100d0a80540320000740c42c0d103c2d01102c1c215120b440c0700301d002c01c0301130361141406004158081c000540404c4900c200d040c0074110044641440244141c9101c003610019440181401000c1c003807032096850200803074060551000d88081181e54101d01910f403801000026241c500c01c0122071542644c055020075640b03100f0a518050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 179292940 1250 179291690 179291711
    0xb0108090f030a1b0b040507060905150a0f12050c090405011512020d02040906140a1703181f0c03030f18020d060b150a090e040809090702030906070b0604 68
    0x35a4000d01000503040d07482088643e001ca407050151030f00c1100441c201c000208202c0c1c403040001c400c160390a94a98110758410041d150b000518100100829524500e050581c020200f44a0080c2c0032424140301c0d0081c000326226101d0a010309000007403843c02c200034141055117240d80c1e008000d00c240210300c0c0a00110301c901e65400c0320410646c40c4da0700d0815420700b8042120282d0844400254543d03024040400c11081c1c50048001510242044004041d6078008020740000998840c0c81ca2210a821391007440700040100c0b1407054401c11241039006040000c41e041e01c1d0842e0b01c4840b034584007110f0901c01c0d940582401102d50007983c0a1089040d81107468007182e10302e403520030541c01c0c81103500c0c005003420030320f070180540030780070008218cc120341c081030ba0103a01c18090000390800041d410115600480a600545510160301c4410303e0107558a5016120310250984280380e404005441c1c248208100c1d0000d4601803e0300352500f60f24941100028415105144294104140c020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 179294190 1250 179292940 179292943
    0xb0304060b09071e0c031214060301060608040309090e071211040c020c010e0111010b04060f030c090605010c062a03020a140f030115230301030b15100525060b010809 73
    0x1038a600189122101c40c030b03113000c03d848480e09004110144802c14003e580390300b10701d100d24040c000d00700c030000c05d0300d1401ca403c040c2103401036001141800026030a10000ca5030002c04101990b590300d07400203d5400c0041c2d500d1508003141e1102c5809220307200a00d040000f0265120031603502610148106280300340141d881c2c01d1894403090010b074030580e160350958822034185171480a20400014810140d01c00301c1c0c15500150801c41005032251380400c208404d171001c0000402c2c017a001007081908120000b4a040c1009a01400da07603107a0a1000075442030107031750103c130304000003a404161010304010300650072400c0c3c3d10010a00e16248c00406011010880d4201c0e280e2601e010324503800d00807000400c5480010440c1001580080303040300c0c0508200c0d200c490740072107070b400d80c0703035859031034502c0c00c101008102c1c0340104441d891083c1c0a0310b135204040d50541060038403035100c0003a8145000d00c00f0201078950b901e01c18460701e0006120007640046800300f82a600c0c03e0140d6130b480d4107103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 179295440 1250 179294190 179294207
    0x13180e0f030f1303021519080108060408092220041505220801061401030c021005060621090105010815130f200a0501030606050403080d060b0304060b0907 68
    0x500003500104031200404690302d00a2840603e01d200c20b0320310340d0f201d80100300c28901050450f4030502c400a0080b0380c240d82c5c0c0103207450300e020318500145150b04103040c1c1502e034031018000420004001c1010603442e039036130040c04a103c05200003480140e0120000c4009009104140340c8440d034403103445040c50000c00116010b98844010000507056100402c4485a011001c80c0f940070704060300908002081c1c5680320f0080c4454000400d81d1820002d1108912a06111250525180c200310325029034020070110084940d4030800241c958441020074564801c100c031810704403401c02d0001d681c04000b00b0006004141400007044683c1c2c95030000790f42c408040320360388010f484038000540050f025000003600c4612644d1580c07007503512a581e80e010028400c1020102000d03485004a01e41407420020b0020802482c0a00205103090340103090303480b4030300001c0e00d00903000a0419100701a80c210500900d1082c1c0c1a507601d103018213101e4000d02402285c240b00c0c860740004120102e2044015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 179296690 1250 179295440 179295463
    0x307090e15120307020a0b1303140109032c12030408010207030306080f060601080f0907170a110a05060a12020c030c0303100e010f06052802010c080109020f040b0703030213180e 78
    0x110b05405052901803001c64202e234072407452046c2c6800003c4001000c5140c1c02d00ca65407010000308541816180151090b02404d15900d11400340020102d4000c08103050514400c0094680c1d40001c0642c0d0310041c02d61195800c00310040d030000070142e0130154580d202000b02c038407000659420444c50421180c45076000e541071b900095002002c2542c5c5070808402c150480c84080c00c84d2156695282a0701c0038410002c4120442e40020003a6000e000ba046220360000b0030031114610410b040c0400200ca500810300c2410410030b030741030701d1514840e480e8121a1140c99450441e41c42d021030341400c2da542d5104881c81e21440580c408000750840c20000c01d20705a40e291040c16242505104088802d500068402e1366a41440180115070130181034201c40719904950002c540c1a0341400c014090100680c0480c03202c2c5d204101e074a006e0101c3c0030a03103050703501d2040d075aa43c1d21060f0400300c002e80648544801c185c0c600d000300061210710214428603050120701d05005503100f216400d81c96090503501e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 179297940 1250 179296690 179296699
    0x10905120c120906271008090f0a0308070f03060308040f03050d0903170a050d050405010f0b180105040c02030c01050106030b01081e010308031f0305010504030816140307090e1512030702 82
    0x134080b80040c05c0d6120540f107060b00e503031040c0e40383c3c58040055484800368000340049034030f50301841201902848800d01c1c0d0020b500080084420a0f9002060000014010800c1024600d4600c00461090304110002c44d0481c03c20303500e071903c4407140e07040e0f000c442c801299540703d095640c210060086441904480d0010f0352550780c08a10b80c4218010752055241508010041000d030207104410711415008600410002552690f0031904c201207030b2120014504c40c04041e02070aa03480c00b00807250b41561025a0003096070b2a0100e003c0c0d14600a03035403600d0881d42814000700300c0c2a499800b40e0350304202642c681400741c072001400c0b8030441c40041c0c0f038102e002c0c1c1071005101082c4404000e5801c0722451000000c4c01c09440c2c840360b4108080e400449169441da020b000505601082d242d40124034060810440d500884c2c0c048d00e0740350b0807440b0100e40d40c0c0c08000107408600641d00d040040c0070107c02d110591030b01d05801c844c4a80d03800e1003107204a84a030101e03884a4400400d4610b219405032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 179299190 1250 179297940 179297947
    0x60906040206070809060a030603050c01020a240b06070b090c01090302011d03100e010203010e25032016031e1b1401020a051804020f030f09010905120c120906 70
    0x400b032041552014005845819003002040c81e03581b150300090122a1550ba80003840506620f011030401d8101c0f01014110341c0810144808500003481000d4200047d0070788885507220451030340c0c060304d42042c0b2150b00020105aa9041c4841040d04910601e9600d042c3c2c0d006252400064807921071500001c3d001520001c0101c4001c405010f00550400005089880c40e00b422501c01041d01c031200b050412694001c0010003030b05030792500207500045040030b42c07140d030643c801000f0440c0c1d1515100c1820075486150710fa00300158091110502580300010541d07c4450840d882c41c0030300c101c1c0c2c2c110000307180d20b030040200d003401c1c0100c0e00070701107156038400c1d0780e9680b0514603440d0058039009803000d00014004880c0003009100600140107261922910f91000640b21001203ca0110b102d004074010040f0200b0003180c0c3c02140da10200001080310940c03a6519154010011960003d02a1051800c0300d60300145602c0038124042e0000100da140c540c60b0302a00c0e010f03010b650b582680003c002d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 179300440 1250 179299190 179299193
    0x1a071704020d0c0510020f100903230d1b080603010c020309040b1201060602011d0115030204020d02070b07080910060e040222020a050430080904060329010806090604 73
    0x108096114240542d20f080c4a160316000026145003910709920056400301380640d02440c002e006035500c213018000c2c10400016103403000303441299180c01555502c208100003505110f042020341d1302e00c95410400f0810807000500100b01506401c0140f4041079020001640034903050140f01500251980518202100c607010300000d000410381c410390000700c52240c03103900321b000d104210082445600104003000c0d4055480e8804420800e100c80d145d051404122461301240840d40882e035040d68016079440c5103003131500090050110042c4001c40c0e07a8144440c0e00d9111050034007607400c000c19141000410203011003121040e10416411006c4034001402626103018142c1c0c41c2c41024a6510f03420400503e002d04a90140c2e003450045900407406005c160785565000d800007000d00c111110b0000103c001c400d000b03c01002c000d0000000103100080f0341c9654105000a65100d5000d100030003880000e0400e820b14003401003884006000001a00440041c40300d0150340c00602800641d182c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 179301690 1250 179300440 179300449
    0x1205070b0f180d1109090111070602120906010b03150a081005010303021b0904020607050312040b07020606040203091b01050d0c0203030124120908160f050f07051c0507050d1a07170402 81
    0x11b000840c955039984202030129020001003e8484c4601c00060b542c0103100d0389411801e0000c1c1126131280e002a00500841801001300d81d000640c108005d10405260400a02d079812550407225041c0079855001041b141e131900418180d0b8440e07001e4580300a14641110b0380d410f80000030980c860000c1c1c1c00314000d41800401081d6035801201a40c1c43e1020501811002440c16242181e24201400801180d15418008250003904c111019440c6003030007000c0700d54802c80c00c43c10310586c2d1000041408680c2c064400c45441012a01042c80144161480a0f4490f0424801c0f004208040c41181d8815400e141000740ca117107030707a02e502543c6890388804400914041804860940040000c0b081c4039455110641c00f003803040424005600701d0349000340c1442d18541642035507030300c520303018095540d8070741d111742d018039814035000004c0380a810440c0c50404658000c54100c80500450814404c3c0012441e40301c0d5a151032000281e120b1810884240314000040c040800403d40841d005260 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 179302940 1250 179301690 179301709
    0x90d050903070b030412020d02010911040507120509011a1f120204050315010303030b030d1d150f03220b06120a172709011205070b0f180d11 62
    0x1e0304442c505501ca0b0300c52a0f0b958810340d0140c075604070400c0e00c0c5030710683c1080301c0d0038002c4051009001c0d81c14203942d81002e51240700d1003148140e495100180b602440f81510b401c000300952400c1c446410f009400070b00803c1e208004c610207207903c508100060a000259a0f001d40908080d081c501d2a040411941c80303540f84146503480d07800304000502a50100b000b05484100c1d03141d402c411307502d90314000c1d0489951400050080c2c224503d40c0380660b800444010340315800300742c0d401c3c101185d0000202161040c404000146001051031420884c41e000611310481506444501085002200600d91050350000a181403040400a03803181012091050001085004c40312015860341d1940c4a012402c0204000e010010440c040c0e07805041c007070705154151078101402418802c0e000301d078040320305002d060240c40e5440143c0d801c00a0800500d4001e020a0318115111100c4100c0a1104c0c0c4c0160006070024030329101008480c50603580081c3e5071360f400f0b0840700f20400c070003090049040c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 179304190 1250 179302940 179302957
    0x80316030e13060609090b010c05100e0a050604060614031b060d111804050c0f07020609010221070309060906020a02010c02031006030c03150e0312060a050d05060a05090303090d05 79
    0x3103a800d280b000b200e101d4010310b009484591500400582000c020008503426040014100002a00d0b040d003c030b0b001086000e808080ca03000803550300141c80318903103420407800b0010024800d580c100024040b1552041c07064460740404008e105008808043d5901940980c1c00410910000d0040b040c1c50460000c0500c031480290105111a11000c1c00c0301316004807034994900541a10135090914146c443c05234411080503500342080400154030540d80160a00240110000208078001c3d03802041800e003020b010728030a0f2200300c0304414074070700d40d04003407403c40200d41c802001141850054900c8010303210ba96004207102800da07001117410341405101070f80c050289000212131f0b03078814000c800145018601824101d4994505952040c41340c0308401201403a1001c0702c000703000c0100031100c12550515900c2e02c03d0b2079043c0040d0654041d40d00086c2d1002200c2400340802501003080d40c405c44081c441007020340e9400c01d41c182c03039102c2182c3c0c2641c01d0b0013005844a01c10f028001428503031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 179305440 1250 179304190 179304199
    0x8090705040203090c0f0a120312020408010903020f010b1f0c0204060e07030c0210020306010503270601030605040201020d09050114070302100f0905070b13030b040f021f09080316030e 81
    0x503916808682280d106403a85191038001e001a28a0b40c2001403d12041c5001034a50600b9540b03450b12030100001c04400c001c0400080101400d0f02c503003145c0513100039207180310003080400107501c2d0180d551025144200055400e01007030404514106a0602e03200c1103045031680304000d8102c0031a41d134129824221ba00039943c40020460001d40c0e030445100340d90369217000452120301c1002a00d810a02e00148004500400411102d0b036400419a074015203d0140464086900c5510b59000480985c200b9100d01c2200d0002052092541041d0b000700d000380c081e80d2b01c00c0609001200c4c64212801090f000c204c51103030304c603141d060307d000624450f07010344142d0700d940c803c43c80e003030040d80c0702c0c2d107600c0308425214030b041c2c0280301042c04614010308070310391050310b0841060a40f62000d900703071001800d004081070000b814484040080c00c5119030040c0341249520021490700032030300114008a00156089401240c80d0303400100310b41b49441c041c50f401904010300d03901207507000914040706070072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 179306690 1250 179305440 179305453
    0x28080a030e01090f03091d09070b030415050903090a0e09121303170406140a02060109150b1b0f030c0c10020106121a0f13120905150717030906070809 66
    0xc505820240c8070518401c4d0340352503181c0c0c40d04655482d21f9a441651600740d0050005008801e08000746140848181c040441d03185c0d942c905280a08400d0f450a2030700709818102040300229020004040303403c0e003120000a250703261b850304c81d80450110303103a81159100700d03502c541c40000c100191081c181c0120003840c8007500d03991f42c0d14584100b05101c4446500100f0f007805100e4100d01c3e00c440c00076490038001c0c104048080001c4d41c80d507040c415409017540d1102005c090304003048408029241d4070074034a959644d0b048031011070303114242c1500c1203805a0210707016109408402c40d040d4010600082c41c0c405044000c02441101960014041d0340d030340c410000d4001e21a5800d051094010007007410f043d10301c0503c00b161820001c0000203803c401078100b11040804144080d1040e4102d2000f482904410700c4c1a41c80410a4000704d174048da160482c0800380e81c80000510303d00c6c0c8103400e12100c07140302c40c0c0c901c126400705403466032954200034000703802644516100b40c0d10103c280102c801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 179307940 1250 179306690 179306693
    0xb040617151201050615160803070201020f0c030c010b090c1806090306010e0a050702340e010b0901030e15010e07050708130503150405030d0e0709020c28080a030e0109 74
    0x4540b800010b005a51100c0800101d440e00c0249a40c80032900c0030910701c0e0408401e00f0558010300150300411440010000c50b407084d1003541a9007000d0b41c0c0701451540e4180c5210101c1d5240c1050f42c0d080b00b158280070b9003501604012100718000e0261649240c1001c0d0b12514170b40030301200c110200d0300b1640500c00c4200e690350401c07049000385450303044084181050300d9000306841000f40b80c00c2c10365100004400030301c40c51031508643c00302111600707102070b41d40142da40141040d81d400b0242c0c0944000010030030740d2842c40100b00c050340903203040140c8105100c500e6110007200c000381d10034464005c0100441c2c481440a55403002031403034018a41151948c5d0306c40030780c000e1004005510b065641c00d01c241e060810100395189a211203001081c0340c580c1e9a1039482c81103603a04102d03a81c640d4682e000d1420108440c0c00a0014070070103544403e4900c103150340e691558210302e400c46454100882c02000c84051580f15285c1010744180390100701da02c10307805440c46104401641d0350300d400140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 179309190 1250 179307940 179307949
    0xe09010903140a032028080403030b0409140309180603060604020c0a05031c06080c090a0b1903060906051b0909070c02040203040b10080c0d0b091507090806010b04061715 75
    0x2010174600d540042c2c5809000b030040c041081546040e0340054000b0740140b0702c240e0040c8019510640c94603020070805070443c0170a0240203a100000c1003218080e445070041080800a8032214038142c41c403080c421441b001d55441240d00341c0c1d11a400d44c0001740810014141a0000d28131401c0c504101c409a001503510545507901040302d4108c4641c80700b00214613070348680503100c000e20000c0c005111404500001500c03407580a09141c60142c2da448203000ba54035031903c1e44045840900800d00c1090b42c07420f1200240c102000202d4110345002c00140c03903d2483e41007440320300420080760381014102d40c1030150302071006d01240103108422061000580d5140000d51280c2d00c244da4980440c281f120070300c92181c020b500203441c6034105500e100019161950a4440c5640010500c00c040e201d450100f41018a9070140d00c4019480c2020484031a4101c184442250150310031a0359681e43d0720b60100c07050013640908000241480c1502580301404800c0d590800c80112403006210080030006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 179310440 1250 179309190 179309231
    0x160506070311030406030902030c010801260f1b03010c09030305070b0910050705070c050603150d11040e0d11060403080c0a0e03071d0f0610050c0c04060f0e09010903140a03 76
    0x9031700098a074503181c2c0c03c50505010320142d10000f03007001e50465040c08210752400c000080e08418071507540e5100514003008210a01d50100200e0a84801a20102c060560540d00e001402c5c000e44c00e000c50703078031070612580c1007074101d030b070141d0b81c540c10728034565a48480000c003d0306a045901c035104030078190f0381c450f100b140e000b403076070b6111503640c1c2c1114604a407018039982c0c0124461401801001401d2410340102242c40d90212100050880d103032030022201c1902800382500103141122002624000041d20900f2442645841400890350700406a0358481281d004000601c020b0219800281c02000b61681c40e843e4207058150300d0300840800c0c40e1140590100040da02100540728450000c1d400070346d004a004603900f11246044e2005c9610300e0038003024041000000612240041014003552903103030401041440020707961f0071f0402d03124805000c2c001400038074401003030040174140b0400b40d10036455141c0800c6002115002101ca8010310301c40c0c003c1c9600c94030010078180c95120303403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 179311690 1250 179310440 179310449
    0x32c0901120b09070f060e03010f0204060c15050402150d0b13051905010803041403070f0e01050f03010b010c0605100e010e0901110c2112070201060806091605060703110304 76
    0x14450070728224100741903001c001401c07043e407642140d8003e00070001d03440c080c1000d80306103040500039112140c010900406e0541051031132184041004a5450350000c040c0360100e008a0081400300202101d030000c894058a000b58000c681b00c100e040d9500920014020001802d1000106a4130300c002195941448030004908296207c4c1000618140000440c280c0d04094100300020340c10714813110342d24412401000241c0500140282e001d40e0208059800750132805600c1100c42c1d50b0381d0280c07144540078002e542c42034000c100c04001c0c42c1014851040c4200c8140d59082040d02c10b6191207000303180c090100403004400c42c4010640f0010400202e00800c803080518041c1e26103156602c2c215184d1800c107240058003007100f180c84080019101d042142c00c001c2d8400a099910408507c510030000c54241c000706c80700c2001041501035005400b100c280c2419a051591140344090b100c02d21703031550040c1c580c0401024003242c2003440107032500511a0030500e4505455100c21440d41e04181d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 179312940 1250 179311690 179311709
    0x1020f030a0804060e011a130e10090c0f0b04060f050a1b020a090e03070605070504050901140402091003021c020903100e01240303020d03050f0105091905100f0e04032c0901 76
    0x905103003030305007072000c02340c900046c20b42084070712200b6201c251a992041d00c130107ca29122214001803206046690300200300c9120880840c0e5518850005c00782c100b4481d60000c00c1022284541c814040ca00300ca040d918195543c1001c145030f1104280c40c0c50824400366042507007401d0101f60240e551240c2c0c505a0759000065488221514000d0300b5a00000c14620400000b03120410445c3c660603100c90540d10250a002003070010640454028016a001d07554409001c809c058210341c1c0541c000d00c0ca00c0c80d80c0d0300701c014040080f1142403c5e40b040701020781d0580c0c01a00c001c0f0001c03041c1d030310104204203094008202d43c26101c9100040c0c0261a888209480d0603020030402c142d01048035a003202e0503414140b00e00e10b401000c0c0c8100100500c105c0340603020060004058400e0703500440c3c20038504600070010741c20482d5400b030403220140141c0080c945103901c0071070402580c0c000c191180d80d145d030b910707280030303403811002c0d15210244903591001c070070a80ca0344009907413050302041c0078005020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 179314190 1250 179312940 179312981
    0x4050d12021c0c0516060203160302150106081906210309170d0809010c0f0806030f0a110a0f050d0609031101060b07020103110307080c0a02030f03010f1401020f030a0804060e01 78
    0x1813507810001c0352040e60314082c2603501c08104031500070060341c1244810402c0400320211504090781403003100e03a82011a6480030002044854000c541c01d0301032114041c810243d04c0d01c88548070102c1d000343c0507100d60003895482c1100101c820320100040b0701c0c403a14102401d0b0fa5903c000400d054001c205036070158000d51540d154460b40701c50203951000f0385000910084411210213448943d12081d05006c100c441800100c0544040004040103000d0301c0864050740000c1c20009510032058541c1c9110307034600340d80007404d4146845400300b628402020b444150b006680c80100909000c41c00703c042c030009005209000701c0a20415006003904030b40169184010f2000604407001014030080d11306060051004059000424552115143d815155110900541685036014418041c10031610020000c2205003945c4640400c4030110313020400901032410041e070300c41c0038810140c9000e900a002c2c03104101d10900b51260058045d00000600410300d00c405030a4400104001404500d2030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 179315440 1250 179314190 179314193
    0x405030f1b0402070611070605060301050c12190b060a050c01151404050601050c0129031c0e130903200c0f010c02042301150504050d12021c0c 63
    0x60008445002080029100181d0141950461091044401402564081440801c20100d40d000c0700c00700a0810340240c4036002494660094441158268002d508050101d80303100d90309000e840c03405074003401503660b0303559002144201011000910b600b15440e5409052240c6810f8020202480180d07142c0344d56401001d412130a640910780301849200c1000d00c20400c0c20030b41242034a80c000105c801181ca41c0b00c070b03030048465025164080714994600360f84c0c1c00e405009041034845032501140f0b0f045000500b0010161180c410841002503004040000e80100b4450800c0c01007c8500030a450030101555500004a400c1a002100814880780114031081251040c0004540100c001030032030b960040e000c0750406000b101c00e81d0600c130071074540d80210b540e145c2281e0b850054841101c900910407078420745510b00f084c41030119400d05105001209840f500440c0e0a9601c081d06001080c211a610814542c0340644803401318040e520b41c1411002c109052080d130265140d40f0910282c006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 179316546 1106 179315440 179315443
    0x90e0a030e040923011406041503020d03120c030606021b03100b040906020c070e0705160f080705010606050405011205010f090504051912080108060402090a0c020120040503 76
    0x9030f51320488a000f0542c031a018207541c01d0300704610781d2100c900384012540017040e641a42c0e610300906101605040880d0a040380c40ac2c6000d035076405800f160702c400ca0b420035030044001303511040100720075581000b07405140c44041780300c10110560700000913139400d004101300d014181c84d0140078090340d8071a44540602a000001507541d1160a60240d898004a009043d0104020360104075400e11503820758000c031500140c1520129070940b54070303140304034180d0211039a41080060a00045081c0284001405103454080e00e450800d070001d010440741c2ca1900c8511440c00703004114900b201c43d803501c02c40d02042000503d0361641e00f0106d082000e1041c4404200220505d500100f06606101c02c1e0001003540d29101641d8840f4602515200e0a43d0082d500c140c02c0c40c0803810300604bd500115006907980000184180c202084413000306407046541e41100c0041010007031400e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 179136690 179316546 := by
  have h0 := BRFrame.cov_init 179136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 179136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 179136690 ≤ n) (h2 : n < 179316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
