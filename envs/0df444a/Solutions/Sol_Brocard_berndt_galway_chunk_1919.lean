-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1919
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:09:17.677787+00:00
-- url     : https://prove2.me/submissions/688b01d2-6cc4-4eee-8851-4ce404789235

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 344964028 ≤ n < 345143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 344965278 1250 344964028 344964031
    0x7021c0801031101090803070f0218070e040f0e03040b0d060e0907060c11040e0d03050a0221091204081011040b07080a030f050108070303080f0103020f010f02031c1a010206 76
    0x11030840040c80866844030083e049120141051114107941c1c00030541146c00180b0705483e1408201540019409e00c02d000801c80303052001510642e280a1801405000010303006a0040d680d50161459007505544006d007104c2c2c01c442126101d40e40c4018007075041d408143d03c0c003413540c2440340000307200e0719124100d801001d001015015081c18010101c407012441c0c82c0070380c0c010b45102074240203900c4611403d00621000d0780034100600c03100ca0050150741002d803c032520310748100441c0000418082c1141034124550901e00c030940c030360342442e03490276000c09560145802c000030001000003001540e01c1c1d0220b60180c050000c00d0040d402c8603518001c40c480d03640550020420400040c1580c40100b05030311b02402c00180c441c00fa5034410003250001d030060045035014000138801d242d040760f01d1580c081041d1224108541c15540482c6a4030141e0400ca8148000d064044ea0124000c0c070540304a242100c0607881c4240e8406500c0303020380b0284003400403071000c00c0011001548007045d043d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 344966528 1250 344965278 344965333
    0x150f1505091609091b030506091017070302040e010e060f012715030b06040f1b03021c050403180630060b0304050c0a15020c01030203040c0306050405060702 69
    0x849555031004450210415a03040314010080f4003140829915824800c0341002003200c030040204100c2017078094101c40b0041c0c4024130a8490a040111050034004c201c1d0503034154604212101c210340103040c2c50240e81d5000258000c4c10b2200d4552000d0f070550005203800031400844000380c94503010184d100100380104030b5419010346c1042551107012101148085140710009000f4000701d00004190b43d0940007143c0d80700000b41842458545406900b00d04e00d07040c071013048102d80b1001048030181c0000c66800500d074003c6080c84502900d42450403120040340785c02e00c068501890014441c0754000314058031a9003015000c20a20f00c078466407500007507000c441c85003400800c81e181d5882c622101030082c40580300d41d00032581c98800c40145010f240700d60001d0414000c0c0c001004004802a0050346004000350701c45d84440d40e000441c84410700003030800581e40d0700d0f0b03820000c4102c4e10326000505102d06100030b100810100041581c0301d01ca0302d500b9118100c5818140d103803014000c5443c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 344967778 1250 344966528 344966539
    0xc0b0304030e0f01140a0c030f050f0409090201030617010903031a010f0c0c05030d020606040c050f07030f0c12080402090f01080a02060c010e12030a060b0703120203060409150f1505 80
    0x80301d030318100483d41e00d402e50014140700403000315520741c120741a400740d621100014000000c2408041e0031841049000305039040250500740c100c0102e1a4038001c510603040e4840c0c030341c801c1800b507900a40c415409080702054070005012600a01b0303000e00361514040340080e00e044103030381807010710020002d1507190595961074110850320048403043e4a440741615110030502c3c00103401d607001c0040c580104d24a0b005000a403808400700811107050400f48801d01c2404c10028542c08000422503400a916041c801090041e91008855203490114000c210311860f0700e00a01d1b44d500a81241d01c9035200302c4400c8a207a64504604445101c20f124411b016409006c0b2400145081c50141000c8051040005590403a4400962521401c0c1c4241c80d601c600000a00454019078001c000c0034181101146240c42c0366a50b005240c2e01c500201600700e90f6021001c90282e50350742d04046c02d078a03040100c0e501d43e021356200c0d800003044445914890345142842d454509800c03001070500b2500700030030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 344969028 1250 344967778 344967797
    0x308130504060501080430030b0301060f030b0106080a15140405060f0a05060d0207020d0303060303090902030108030a08071808100608070308030c0c070e130605070518060c0c0a0902070c0b030403 86
    0x507810704208101b0340c0c7c40340004081e420304514111060301e0a00c24030a41e5004225220704000b80343c00c543c4117800030508200e03001000d101061003011320b90704444141c600400300d5a150303c0000000c2c0100e0901400f42680e0800008801c20703c0c0040c080b4030b40323085500b00142d45a1604211032244040c103450b400441d00c01d410402450114080d01042010741b1015182581e1940000c5100340e03a42002ca02003990783d1428028903070b10005502c0502540b90085283d17504044910391f0720300070280328008110b000400905440d05c118861410300101c401d8002c030158460360039a031035014040380031501f40c1c94490000345604000454408480d08030310344030f2441d1100242219030ba40858001d888610401600048002c02e684031203100c2d030399103004071500148500d008415a080030f80040c04001044c40683e10000409506a02c0014100d0f200f960318005203600c0e60400b1400e00c9001d5200b202c0c800d0000c0c502000c0d80040080520031042988510340380c1150000074001560003800007200c041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 344970278 1250 344969028 344969033
    0x64e030801080d0c110d14060121031e110d0e0f060a08010e060105120108010e010f0b012106170109110a030803010e0a140408090109050406050121060e0103081305040605010804 78
    0x280f031a9003005004d4106c04101c43e00780c44000c2080321180e0119102d42c0505c004010001d59002c0b905090180c0490b011003807402602c0040c00003036500f02d0f810360075480d90084100d040c02918101401d61046050f03070050340080700e01405514186000902602041040ca01140340c11411511a050640c8840030329908040f03e900c00b14000404643c180041040110190304000032024000c0c040b00b0008101c2286060845081d9562510300003140c1d4240540c2105981e0003850b40c80c41040c0380203130541c44080845c0f0344800703051a5400000b4203049600507030314444040d004444050700440199008080d20824844c01c0565840003625503c3e052006103c07040710039241a0300300c03030354500106091000399204844100140c03411118071074001030391402c1e540c01c00480d0b4002c10741205c1c10042a4a480c0000c0d20b03040060280140303c0a600784a42117549041e0320240c003400b03141e4050301c9607684a2518404541c444503640c10960741c05c41c80003035149024000c189c2035410695980460b0f860710b6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 344971528 1250 344970278 344970293
    0x7020c0d080904020c070f06030c080402090a0c02010b04051006231213170918071202070813120c15200a0f110a09064e030801080d0c 59
    0x101c00307541c4183c0070000d20903417820400040002e0f10012081807111890f0040113402c8a02501c03411040c46020401c11025940b01c400380b540c4104803510201c1d030b120594000b20700401c05001d50a5010340b03043c0a00003086828a030036800e59005c1d44030b12805000c0c48a0801ca82c10104c14040ae94071030030080842814804034210342c100107080f440902d6200c144da11000c0c00312003401c900c0d004500106074165186812000e80021a810340c800b0040e50030040c02c000c0c010000a40404a10354000a50b4802c2182c15404ca030300001000d41da030107446846a0703203a400081c500001341c40080c015003010940b5aa28a000c0701c8003488ca8484500b4103540c11000e0000d1100c00c181000b0314024406920302142601c3c03a000f40403440303028003425100014080103004c118070b410510400385052414014001f10b034401c040c809640002c004260b5642c001e420422030308070120741c002900303408414040c80d612102d0780c840d028801d4450042a82e229214581cad15080c1c00403520005038420301c41004600325 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 344972778 1250 344971528 344971537
    0xc0909090803130215070b06210d0f0c050601170f2b0c0503030f0a06140d06050c09060c100f09050607080a0609180c06080105061e0d2307020c0d08 65
    0x1d05051072052078591641d05d00e41080c142035551801c61001c01c400c610f8542038242c90101007664030f0a689142114080e075520154201c0000d214102100031100c3e40600c0080d4030855000702240c0d560340c3c450b148a0702d1181d103600300042c0e52080104d102248900418149c0b824109500d03101c1802007100350f42140108035129800500c0b880ca031003400411010b00c003c2d840b0314207150800071a401c00444203021601031317610207170f07110880240511103603942c001c91010480e0003ca021880da1102c03094101c403403142041d00740c3c1c40000011003a49000b000300320124040c04011302040f0a400d10680603060b55112900140703503401500004103641d01422600e5000390071004001860741d02d841240040303a5001c4102080c0e41c8401d0141801c02080c0c852903400340c00e5520300200da65261001280b030740c1c024481c00c2035000c504035030036200d00340c3c00310265800108050000c1c480f4500c04140c0011030100c0862230300f580060f170800a13804c0b40c00010350808000c00602507194500641d00e5403a00c6801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 344974028 1250 344972778 344972783
    0x12041503111b0c0109050916051b0102041805090c0a0b0714070f090f0e0d0f0c060606030506180105010e0f0301060515031602010b0d02131e0c090909080313 69
    0x101400b54004410388a050150a4002040141014540f41e0000340021030140e10180c49041402c0030448001039019001200c440941491521006803008a40d10300c0068111100c0540c03000c200011240a2100e10f00160002c000003003069032174042c2001e40b68010702d1103075500b1610002c82040a055480c0041c41c141d4000e1308814181c02c0070000b09400c2c15103a134415810204960001c0c480f10f40300d4070441c0400252480d0800800080b46081038444644443c0710040c0000c2c0c2c580f0200181c09018003a11044c1c6c1f0410800c003264480c50082c00030903041e10081d020704080ea00701d103140e101e0300c643c05050790720584440001c049035034200300e000d5500300c6000e900348d521260f0004c4c640e00c444400c40142049003c82d25282e281003c580a40c002c4440007c808581c10b0051841c4603850300380111900da6019516241d80c00c0c034040e02d00014000c5000e4040d01c00c009044206801482c81d0302861840c032080d46e406581c03c0c0c3e28200202076440d000000780918100b040450303051440200070401482c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 344975278 1250 344974028 344974061
    0xd08041a3f1305010603050303010501030c020f0601030f0f08030903041505030f0f0912030f040605240d08190e040606020c1c030c02180a0b09251101090807020312041503 75
    0xb10103a80d8039083d0f810640c01140c01d584040300500a03036130103006045060741da5100411400c600752001c10ba4890b010b21000c0d100700c3c2d08003000c0c402d0080b0070300421485a002218a9600d0500e4925156640c0c80f91044100d44080c01d50345840051003003048a0082d00d004014131400e40700c071100603156190203409102103104030300700e0315410100500034521030b03841300c0c030514214a45030800c44140c40d4010400814030f5400300079507050300702a01500544101c01e641401c4004a0751030036840c28481e10740b50100c410740044042a10560003030100703000c074409030f0b024491035507541c500b6070f035a549090040d40d2002c000d620216401201085814070a03010703140c0704507408015004202000210030311020418001c4e003c221400034103004001a0030001d44520f030207881c19202c8050300d005810b1a9843c08a40c440c600c0004034800d0583c144a4080c0b078008028143c0245050041c591200030200e00030b0107407100101c0c0015403a41074404860070318800326482004c4402c1240184201025100b020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 344976528 1250 344975278 344975311
    0x120a0f061e031a09030a08070315120213050c1c060902040b0d0507090b161407170c0d11091e0a050405101a0d08041a3f 53
    0x40079140d0001104040148851240c41e0440c105483c4000642c001c007003040240600380035941000104075541e0380101d20f0801110348501b0303003c501414109800d01c04a03014180c0101d0090840e41c50380c42660b1003110400700800980804605139102103420807100c09050005107805005074182c00c660202000d8002450f41d00d4070170480481c0c2090700408141c0e503011464104900070f41c49003a41060700c505086490070300d08244841c05100b14041403021094070701044040094012043c0440307080d11041c0c5441a07180c0c40d0714198841215201c000c079224410b01c3d202036040403021294556040a5030800041440c0103000045001414002d62400c0e08109402c5100d417042100d8040c03070303064402152600f8141807407441c02158004400d0750768a40140b6051030b0084200e107118081090b00d100c24041381c00c2c10001c0d40c40c01968402c41e001d02c682d010f04106898810020001e0380c003019440c00a50b10700301300c0d21003009036400040841000e00c2c202c00b01950600c00d14254005900380d000400d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 344977778 1250 344976528 344976539
    0x60c0a03020c0d08071d0f0f18010306020d061403062d010b070b0c0a08010512011d030306030d05190503310308071404030b0a0b0a030302070e0c120a0f06 68
    0x180f4000c640c5240010700c1c120b091103140c0c2d501421a10303080c0402c80380458144420000034415401c0c8100c424400e10b02d01140d8070040c2c0300c404594522008880054440351781d241001c0010f90701102c0c8a901f0545024404242e00b01242c1c2900c04000000d001803841f580d444507000c4141c0000c0c0c0c41c0c40b050024038000000301004641e1034a010b0a0261101e5446006030f01d840c6264520180414518002c24482244620750081c000350459004807205103603862903001142c01084074080d41c5c04403e02142044004c804000010f5008040c160121100c0c010071410441d802d0194001c0c2088820555552020051092010b1074001ca00c4010664000704042519041d81c00175400741c000e8900203070300950501d900100d83c0e5500c000039050058040d8407036008011107205130b000c01000030400e20049280d19a196110b9142030385e0103495005026181e060113981c4006038071912790f2020500b0700180d040d01040c41502c0d40c00f8041c0c0c04541031610707110210300180034000c0525014a60310200000e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 344979028 1250 344977778 344977783
    0x9170c0d08041e0e1302060d2c1f2a030507030b03030315010318020402220902070b040321020301060f140a0516060b0907031a030f060c0a03020c 64
    0x120184a4145a50754a14140400c088500b2031180c1201044260404205100c1e07040c003640d0307000000000090a03003e5600c00500f89004610030345000515109c14049462140d44448280c41c2880d080c18940d10f8121412664520005010b0004214250782402c00c180c000d4100c0070416412240c00d40c840140301026540d83c0102005520009449405116030960580b003000c07050300094000c0c1d440c6180200d02c2c070720305625201416040540c0c0e4031413000c1144140e0484444c03164000c10039540d9400c000e15110800c1181400c1903d0210480000a20000140f08982805500280c00e01d0959a503860540707c4080421216100000c0f40c960000d680140344020360203011207455015030300e82e07ca44010038120700001c0600540104000861210303400906a482490707c1c070b02c5620400c0c0c06880d20b40050910b10706502d400403070300400d02c0b0415806401c5508150395480c134124001c4107100405545441e165003001840c1c1101d00400c1414a40c400185400c40c2c050901629124013010f5051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 344980278 1250 344979028 344979049
    0x5060307030b040510020307122009150f03070903120201050106090b070201050909101e08030d0b010c050a0b060423040809030c03060f04050f070303021207030903020d0b0414010c09170c 82
    0x200007a0020b901c074041c20510b00c00c108452b2209030102c03a003410703942c209001c80e00c00d880d40c86108643d1008814000b058250807a030b990340303040070390036100d04100c000600100650b0004a84100c80340c4e07401e0701054414885d00d03048920740e0b910720300024646940d8a415900c07503101a030400a04100300546c544034000960b02a8941818a14005251903017004850b000284000740800310f00c10204581d91000064420042c0303840c0300003551040790801039131001d40400008100340074095502040c0207032182001d00c01d12064505000c400e2a00801100c260a0724030312581e0101410040b402041c03414010b040b890304007030308540d07250b8035030700c002450000111980505501d40e10200400c1040034011412400c400c10000d0041500316900030f5201e8142800054601102041d24820705110382d440800441d0042c18490101409003450340c010081200e064031f00429900e04070100601c140700791148101903945115000303040c224601c950002d0040842c050740301e018021465075480d012b240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 344981528 1250 344980278 344980291
    0x20315010e01050d150e010612080307090f05060717041802092e0c08090a14041505011d2b030305090615100c0506090106050f0405060307030b0405100203 68
    0x441580d8035054041150360030581007140030314031001c0d180c000aa00c2e2000041d80f0022100c001c0b44030f0710f00c041d086005150355030024501c140038518030800c1c010094002c600a8046680f0401c1d842e0700d03909105500c034506c2c4505500000100004408501802101e592802c0d208005c1c41c03a056540401c1c010041300c002840c8029075000030306400c1d0b403404503c10b0301d481411a02108040031341d00144d5903440341e90b101c40c00911400c0c0120360f04225080c0b044a4407600002d0400081c02c0d101c040c500404425110740502071850f0a020010341c020758090f100032950141d50303115083c400c014842903180b440308051600048180c800090314a0318094501110900c2803200000e688103045c0201583c0000e06860f419403c1001807041c42000f258424801c9102a2000b444c00b001e541800c0b12a201c1c020005460745c0528007d020ba00d82c0f0641000301101d2040324011009024071003007008442d4280e8076243d06621640c81040000d44d90010a684a400f030010f0741d00550480c0040c1c02a82e1048800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 344982778 1250 344981528 344981563
    0x11e170d030b090103170a020106081e0c0a03150209060904090b06090c040f1505070507090e07080f0c150f0a0306170109050a08130f080a0209180a030c06090203 71
    0x224040c496140c440c100d145002281c4071600e5502d192250000e0000301808108444400201212904c1c001d40040c40204401c0085a034825040100c0c021050100d1140408078090a0140c40451501a0021040d20f4000c1c558080c010b07500d121a50003544002111500311409024a986039079807442400c0d03a042c02000c20484c1880c010042029804d0020012412420b0900040c41000c190140c2e55040ea001e9117010465500208015101400b55040081040c400c42c803020a2034010340c0c00c030120400700c40b0200c0310f156407124021a2505600c43d44503a0b20703401146008501c0c505050706122801a49508501d004400380340000c0e6940001f05d200042619178108118541c40c40301d4402002603d000200324140066803990303154a900b520146c5800c00c04100e0001000c3d071074864100030030021540348400380d61100510348580d20300c4008ea205400050020312050002443c00031290f49031005000501c14641e02619110800c1c00b095035919581d09031400180c40c200105100503408203036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 344984028 1250 344982778 344982793
    0x5041d160e1c1406060102070f06080c04050909071403030702030a060b12060405060f18030a030504110a0306061e050a0b030702030706060801150f0b07020906030c0303070813050f0108011e17 84
    0x283d0138603208010344910304642c4846001c10004c62038108040c15100240b400c10072a8581d0110f41205000783d81110341c1c080c0d5080d043c05460840041c41d241200c0c80c01c00c1000524106508040d01ca019104002c0c0d050b4008840c4c0c0800151644d1003030070807070382c01040d0342c13401070090705510700e440400c4070110b540754041c206020560000840390380c0c1c40401c041c140383d2070902091f8055101e00400c0d0000e014940c4400100c0c003000410021401d03000400381c90605841d94a00740704001d8131152050124005200c06450003c20480c0003800581d800034110503d0545081d941c0c04941d4801041d4000b1070100740710700301c0045c50340c0c014080140402d17400030814a4000b8520000b10030b403584540d10a411410040141480030f4095408498048948160756a00c807804281032030906e000843c1e1500000034450208a0918007811141d8042511642d40e05d44600500000200c0500d103580403a8489004108a21001c0111843c81c0d079444116901103580781401a1030480b010043c80e01d035000b02c030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 344985278 1250 344984028 344984063
    0x2903280804030f080a1d0a0608060103060803161a041101200303041208070804030e0f121221060d06020c0a02030a080405040e1609020a020708030a05041d160e1c 71
    0x4103440071b00c0040210b2500910189000900a20424030800042c40001070009030709a010303070310600003030580f1002c0e2030740c9904aa034031304a601030204003200c091100441d00b40000032002012071082c3d511480d48850b41c840b510054412440d445840c140e00702e480503805481140600141d801030344034070038070507814039040380280c00e80c503000b8030180c100120b00f003c00011035800384a0300d400000555102e070001c0039010201d03030405441040200c451098079180c00e002c1000500602c200304035a6080001c0303a8080e11008150381c03083d690540d000f003440781075030081042980104803a845c890226180c03070146502190400042c004250341001d00405c1c1001207041034080c04d070a46180f60081d080c0b200040c585c00701c0e81c0003940235001c4140c0d4003061005000303000b080703094090301401c001c990b00c03158406401012607004d409100a10704a1981000c403d4001d81c500b28054549105942d2003180c0001c412107851108ae41c0c500e5000720f900d0b084c803810080b0040134a042c1400740014004081200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 344986528 1250 344985278 344985287
    0x6020d0504122a08060f0906040209010509070e06040e09010608070612020a0c14060406110405010c08210a020a03060b0309030702040b060f0a02031b0705010f030c02102903280804030f080a 83
    0x14180907c81d0809420000141c0d100030103941903490407511010780340c07039041044032016041c40000781c11100000c0c1c0800c00c01d50304008903101da00943d000380000c940350380003c0e407a000b0300e206240214801c003c0c401b101c200c2640107400103c2042c030380011880c60360b44400e0340089c4070108000f820b41000d01070105000103401080c900c0880c0400c681e02d800c0c0f502000a10854101c9005400300c1d10100d14800d44056500030180c400c0f900014486031810040301b40d0009500240c601804280f8042d4000703401090a410307a4800d999100c00740d802d01c91240c0a01010380084551558012401c01c040b406a60703400c0090400004954000c507251520191200f0545d482e200c03181c075865022410801180c0c0c0d1200d80e16004c94802c1c0b07000b04440c1842002617140c1130351600d2501c080d43c00c00903650300080d12030344440f040348401c480c02910100040281521600350b803400c2c01c003031800d84142d03c81303005060b506c840e01c85202d80c54051405a403900c0340b00b51145890300448500d000014003500e143e500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 344987778 1250 344986528 344986531
    0x50d060b1801080c07020a0608150d1703100f08012405090103080c0304090903050a1709030409090309030b0f0906010906060807110a0b07080106020d0504122a08060f 73
    0x1080005103414010903605980350940d2001d50b0400407680700007560300100d0400e07683c030940d0103411441410f850b444050312a4408903480c80c140034240c0d130b587c203003440c01071074030040d4a41002184105011011310a00b656000800700507906240d240c0024264600d003045800611102000148400d420203107440701d50001072400c010f1004005080c00240d44813940c840c11a5408003032a9980d103090322000b4114091070380014031140c90702c001d1405143c7c10000030b2000404c180d2f1400c28a0070101038481001100b60f943e07c42c1d0398001d05c8140301c000440c2d0311039034047d4080d04100304060703902d070b444c0440c0c0c5604844a0240700c0b4010140203041d9020443ca038050020320006122640c109500200003040040240041040e21001852a4003082c4600d0020350f801600c00c89840c5440ea0300035021703510030301c1030b000148035594880c00303a1885081920107684a00a5441c604e804685410401550010070200e084901035201e80180344c9507000c4034001e108100c080d0905240c8403c1c41118000e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 344989028 1250 344987778 344987789
    0x1b050c10140906090d082b0c0206010312140c010f0c140304020603250c020a090e120f04170109021e0d021311070302010e0c10050f0a120c050d06 64
    0x31050144000340000a40c0c120b41400d5840d82c1c1c48860070000550b04400c0c800c40549000b1002605c4500741d241d00c090070b03030700e0b2440000009012403405a00c00485072001491b20058000d800144002128000642d207980d00c10f1904407c0b4005da80282c203c1c55000f00440440750303549a40303840d00400d05005182c040e5407542450202c544a2912046c00c511004000a100e00c00010010300b01820254881518031003452740c510341c0e00d80600010304007001c140c0c0142c1c8150b66041c00091080e2141c041c2d1100702d16810068084590070220078a02a00411030302400c1410600001c030303200900c00030a260000c08880041802c04060040c80560746510395901b010700e003241c032f000c03d80351034030304101c01c1c0268103494803d8006040141280203020400e80220010b01c0080c81070140340e41500040c0e002c8403141d06803030108503100100100702005c45442404218140f00300071501c4075038006888015110b00b40f209011554154240440710100d01d030300c0100c0d00106601459000c18070414001c0c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 344990278 1250 344989028 344989037
    0x30d180e07022e1b09080705131a100c030906030b01050f0a0c08030c0c1005040f141216150b0a090c0201140906040519020a0302040b011b050c10 64
    0xa011000030740715034900d02c9000c0c10314802d001060000e60421010448a00e20b5241001010030007005146442d1306810107500044a04401241c860004520401144c40003442c0d525035107140c0c000130300603000c201c0030f40c100c002403103031003102ca625002c1211001d801c4c4c07981e0300e4041d04d02614010302030040d00c1d00710000b010b180919010550340c000d0100e4040d40c00c1a00c99903105ca071101c2b01214034540c8a040102400e0740071041c00b11450640c0003901c0e04444c0e550075034003010820024030044a40882d00036050503401e4115901144a2030740380303401c1c64640010741d401304400d01d41c818400c4e84044c07195210485000c5244090102501c4000e184151186013405080c1181c40001c1d40781410340200650703c1e40d100d01a040c518000d5000b1124558000341112042c0342a5003030035101e80d0100c03420b440c18050301440d000d01c03405865802140650007440c0c04251415502030100506d121080c0906005052040814100a03606020001d91064005000b00c888500c1403042c0c40382c1586024040c071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 344991528 1250 344990278 344990281
    0x50d020c0a030825052206080a060e090c060f2106040f0b0a030803090106090e0703050616080a110c1c09080a020d0809030a08070305090301050106110c090403030209030d180e 77
    0x9111009403481c40d58191a201b5200c58451815283c1c2c1044c01004212011588000042c3c19400c510b4407485610940e004001041d52000103a034650000c4580300c0315a00614406401490040c0c05001d10a919054150030550080d12071700d20010b1038503071502651103003801c014003850180520f031007000a0140902c0301c01940800320b806440e850000400b8450080006100c0e00d00951000700104203404051191a44049245842c0d8401c0d01054646008810004c1c83c160a0300b102800300c0b618a80c2c0360840c036910351461038014001580c2440000c801000b00700001f120800001e4001001041d154500402c1e9100162900b0044d0340b001c0c109402c09c130050b1001d6a20303c61f00a03409074104030000d6480c088200061304142c62890008c09007017012411000780741d40600904000c05080d00208040d0341c036031201b031380e0a008228801080d5441404080080c0c1461007407a90403a21905016041c170b000280000d0034080550701540c002000c01a000c415003260220103c000e006200700442036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 344992778 1250 344991528 344991571
    0x2031309060503030307030f0f0903080118180609030c02090411040b0f06070605130c061701081b040209031612110907050717040801020304140105070207051f050d020c0a0308 77
    0x481c00010702000605546480c0c41108c1c030326a80019041031119401000104014a40600959020b01810544001c0690f0741106000140301c1c4c0d2480500300002c6130f10100307503540c802000d0184914200c0070009144408030060300c5101056005034800d107a035040300c080c204103110032606d10b0704243c0c0c07141000700c2c8091500d454240488140a030030201c0490035584480e0504094441d504004104002071380000444907800004208507240906120910b642e80b119510fa40b13508000e038540a03c0841041c128040c07900354014030170700301c0140944151080009004001c0c0070141d00c10003403007840c0e5255004100021092a8101100710b178500c0c0d841c01c2c910f00080c800e0280800041c920102d1041c01d9a00380700250640b001000380c00001d6690740b400d868250302d100700c43d000d000595030904012070407c5001107184016620098044044545d00302c440042090741900140e09000080080c0d25100c000c9000804a4480c1e00300241800305035880c0090060350002e24000310401049400340300c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 344994028 1250 344992778 344992783
    0x210c0405040b190608100608070f051c0e031e0f070b100e09010b1507021807090302120a031418060702060d14070908121608120702031309060503 64
    0x150382040c0d070300042410914010604102108a045407401c109610014204d540900b40030701c15118181124461680c0d031074140d840e80400c0d0750039404660f01303c1d034010f0181d1140c400390089112645007411f040c652900c03088121019038030302a650740c0000034032000404400448003078850070715003280d1510340b105e207074070403503000d000c1c0d0080c900064003000c50136030901001400c025011900d0f661165041c5940e27801c0c0244035800d0a1406000024a0001c1d10512039050300d00e1181c025103075000380c44510031040e079074481c001c103040180402980040301580760014040c03010f10040d03001342003014460074050140c164030110a01c440d13000300304982001c074080e443c0260140066840f980c4640c850b2002450500070844940d60302482c00d096030001c0d0304190b001d06d00a00d00354842501942e120265240c88006020800906c0c1d00208541080c00c2001e481d04981d283c09084058200320100c1d01805001c8019a1600c0c0140d102180c862080084034442c04000c0480c88400c0009510702400720780c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 344995278 1250 344994028 344994037
    0x30c0a06021803060f0a0605060325030e0f010608061617090709050c07140c01021506030304090c0909050601021f02130e0705121f030b07180605210c 66
    0x14480d640200c0c200c000d161103080d4060010714000c069403101e01e040c005101c0c0800b002c0b1071910003642006400216070800744126801401c2c0c0c44c07417517101d100498800c42560611a030310340b4109039440360300500415081c04411040b040c0c00f000072412034608203099161800181500c2031240c140310102340210340103d2003030300400c9160020f41c01d80d0b98504040e0b0505201d07511082215051404010031109130b0b1005105441c4122189100681d0281c1c0080d501c40d404556640507034001001070010300ea501d040c0c1584404002c0842c1e00c0d00703482d8001d03101650030100b4404007084400301c0c180080b134800d0048a5000100b8401031031402c41d61282d0f20101c140700b5801041580c0d00180590700680d0245550015107c4050204014240100c0c002c105a00080c0c1c1a402040c118011580009245080c600c1c4c0c2202011243d40036800c544540c480d0800180003107040c410305c3c0802c603445074442404900102a0794440a84800900c0355104810150200d108204803400c002c12119030203060544 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 344996528 1250 344995278 344995283
    0x3042c090c0d050114010b040801140408041701020702130501030308090a02030307060216060e1b060412030e061204030c11011110050a060503010f09030e03030703050904020d2406090602030c0a 85
    0x2c0d4011469401c00d50300500c642c442205400702000e00100d40c0c04401d000400845116400801c4041883da04c045420a800d490061400c0c00030841000588400001d4064100300718000520700416940015481a025011031000c141c481c40104141a0041840e940c0281400050100da001c9940000c0d1284540c03030000b040d0300e9010074a189210086250251040d500c00001c11210950b58241070f510034100d103c01002c0c40000c4142c981d142041000c3d5804c036104804600f03030000f85941c0070b03500d003503102405642280c4107000f04c20100d0743c254501d074003480c080d8944041c1c0050354100b250b5080c2c3c510030300d1030601500c1030f480c290310709000a0342200b4000c0140002003a48403400c0640240c40c00750b01c0640d05600b004490040c007042070780542c2800c0d1082c1c55250004060b42c0a041c0c480c01121405004034000344501645820240c00030591a000707134800240c0907014409001c1060f400315200c00d4802c0f0035000c1840550b400c401c0d19009803840740000c0d41400224240301e0f07600e05122900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 344997778 1250 344996528 344996539
    0xc0f0303040f09091a0c0a0f091508011a070507050402070206091306230108130221100b0d0209010308071506060e10030204050a050d1b060216240c020d0503042c090c 73
    0x20300f000340b031044909c070014041059111810503856400100b498900780145a4034400e0780700040c5110f5030f800300300c0f050f0581c000007800c09640380504000094000110503a0810700400c0b0000d0256120f0002d00b10211508000213841030030200c04540b09403840700e48105a008140300040541e800181d600c1c0c3c401003ca2500d800810170384045060150901503c11200e014091020717803031000403680d100103214001040101e0244102004230340b6402400203500101d8400041c004110350400900342c60b030040e00c84511000c43c050075841152031a501010005003510312034000c614000207c882c02d00c280d8a015800e10b814600020403c02c030604c515407051080c2900c40301049081c2c01c0d80510912405284d404081c0d880b07801a465210103c9501401c062400d00842c6850710701444040c610300d0785d050300c0b2106400c904150760340b45c07030750030240e034170040b01241000018401c20003030001c0c00350f0140240c0320a449040c1000c0081e102c940e0803020350029401c1100040000803141d4800070100e49 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 344999028 1250 344997778 344997797
    0x5040b030910020a030207020f0d0f120203071208040b0f01051302070f14010509070801090308010614090301050c04050f03010501120308101a0702130c020c0f0303040f09091a0c0a 79
    0x401ca071800c0352038141260700c98000300e43c2814003038041d4080c00c5254000e49020300712900010400ca68041c4000d00106000010600e400109030b41c00200a10025180104c0745060034540f5204106c0450601d60702c0054030003810441000242e042c9150007803220b01005085506210001d80c0415620002d010302d0395010510300c060001003102c654580d900242001244a2050362080c00b0341411140c0d00e00500c120800001d10210510440034107540540c1c0e03180c104e03401e02e1021106651240d064120f10301052011041a030340a1040e13078010485a88825038941c600014014484070010000b8440d0349021f0040040c4681a20740791080c607898038052705643e4411840b8441d9900d02d40010034864005001030310603c0c40d00009003610390003182c411425403c070721541c00949414001031801030b0000e20003181e507800c1519040c5c0b1701c940000c054a080684501d00b081030715416501810009840c3c0303410b00305100c0c5038a822800a503400403520051718110080c0e010908c6202071034000c0044519 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 345000278 1250 344999028 344999041
    0x60903180402032a09150a0e011e03150510020601060905061303150204081002070b151f02030f0a020c18100308130e04050f07080c0f0103020c030c030a090801150605040b03 76
    0x44c112079038040010038800c5442009503500c159600000301001c0404e003030041c078580d0356020391003000e080c44c0c404000b21201402d00d44224003900500041014030107640202155555423400c00c442120b03502d5000745603a40c03401c5c000501c82106584101d00459041215001500c2e01103501d00940b078000c05078050f18820502c0d500e0081c40f41c1c0e4044000750054840c0e1302c20b2000140c0041c200385000b0600006107440300c08403000021030003010140c1c407200030301003080c489044c00c0c0d00340800c40541c0140c4e0304150f0220364054690f8460007000005070403480081e01c10b41360225811078103128000c10040c65142031490300c600c644403800f018040201c00b180c407450b00541040072038080c15011a419541381005c0c504070380e9441d00c00d1640d444034002c030300011030b40308400124450041001049511a00c24110040d8002d5000e00755410349070004000c00110790300200010501c81805594440c8038a113030012103821607007000e001d65001540203a04002c40740c2d01609407030507a0503001034540d907901c80c00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 345001528 1250 345000278 345000361
    0x80304200d1b0317030403090f1d04020f03011802131a060c01020c030a0806090a0e07121e0525080a20031501051203120c03071106090318040203 64
    0x41d030004024003c0445159013140b002400785020b03601ca43c540c01a030316200d0440340901c01d030750b0080d25000c4400d01142c03515074070201100c5400c94005800301d00d8610041000c2402d40b034808480010629008802600310704084502c03000c8006880c00c20006550034003108810074884880e1544a4070b0085071201a00c1e00a50440d0100b83c4c0050032203503514a4084050007018044484a110b18070810010f1801800c90050f450f081c034001d0064610309003460056410380507002c10540c2c0f180c000d0100507510703c807030b4040c1548a90190006191814203c0401480d2260000e14413221031045142007062400c0095150069580508065224615000400420001c0041e455031600c10001580d92040c544503250707045e5002640c94816001071403501c01c1c0c0d00d01c11000710580d2451107000040c100301030308001e15088421854100440340403040340d980780110640e0903c400da00005a440528440c1010040500f80291000c0d4114a030144c07d507010442c6041406110f280d0b074401844012848 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 345002778 1250 345001528 345001583
    0x6030103020f13050f16020f0c061e0c060a05061914040f1803031a0109030b06030705030706050c210904090305160302030408010507080402060d0911040504080304200d 74
    0xf0442e04120a2030074229118103000d040d5514181050013502c0454058408114410f44102000091a5005a0b082805200d51051070086141408492034403108a514801094650140002410035007850283e5408403040942540d01c0b4203444180d07050100100a000c2080f10700041c894132213035080c017001c40c0c0034013a0942040951803924441c00513890030429010042c1d0300030795007041404a081140c64260240006950101e10310030020000504609000c81c0d0001001e801d5a81166803640485c0c586000394100c44040703000801c160003090010001034620560035040d107250b203c00075111850354820320780100c2c0115140c0c008441854012011140e030040300035800b40e0b401883e820025102e030070600444829508100100c1c5a55115048c000e01aa4000f0080d51414444003000c800a0204075800c0300c0c1e01000302c41c150080d0341c2d00c2c070809125501030200035030703240b41926140e01c181c0000303140d01282c510a4071f2240c81039155031a0000d48254001c6200204074071001c45005000341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 345004028 1250 345002778 345002809
    0x41404051e041b081f050721020706020408060a0e030316030b0d0507060c060f0501050306060d0c050d030c1b27110c160e460516050906030103020f 65
    0x60f000080d03000781c0042c04a9044903030701882d8205245165040094401c2580c10500141d0103d00c5131000000c0011254040184132000610307210156031504184d801650040c02e06400c8035041100c000450300170800212003c001440ca1131815031126541316940040c000101551005d40c1c80443d12a600d41c0003406800a04460005a42d07030300090003070001100846190382001e605400d4120140103141c1602c0d00200542100d80d5007009100e109221032206651100c504440041c06803200c1005d808054041c0d81d6000b04035000c1d0610310301c00341003404c4103008052082c0040003101c0e600b004000e40d00307190b100584910340c0d0748c01c4c40c9409462140c0300b01c80100c0c0d0018000860500010343c03108503007111000001040d56842e02100651400c8903c2d0080245059011031850003107000800e0981c054029110201d80203021a2403210381c80c401da00c021951501405455000d642d1003540d4140140790003441d01c0c9070140424801c0c001840028021401190382c68080d55424208200100707 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 345005278 1250 345004028 345004073
    0x2010801060302030a1d1b0d0f1e170a0905030a020a03020112090212010e0d0c05030316200d08100b041e080a05030901091d0417040b040b041404051e04 67
    0x1c6403604c502e9102d005624507c2d0b2890840c1e1446107090516400c40328041d42c000b01c90034001819915500e1700c0f1016019295075110000b05c8050000e103400d00081151103408840c0358540c1c25440004d0a50145030f0070191003a4861507035400141c0c0e44809442c1075a90a01c0c00c480b1142000301c4a502030030030140f00a610201040724510408015440050760782d89a0307086a4603044070110a986d20708105a019185400810000d01076516011200c038100006240c9581143c54006c3c154484140c00f06000e03070b240c0c0101108156055100340d2498010791005204001503152028907002c1c0e01c114450141c4124142c402c1c50781c0b60403a00054402041c1050544c1d01c00c058900d00340c0d85a40c80b000807140800c205c00d0021400007189401c18030118000122408039807615100c000c80c10800b0b1480c3c000350303a0204800b0802c801e600d000f134001010100d1106403594140700741c2040714850181c00a0003145802d003001007076a0b4514585900d2110f140079600d0503215800d21481c7c046807001d0741c00058 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 345006528 1250 345005278 345005321
    0x20a0c061139030c180a18020108010b0306011b080a020106090605011d030c0a0f030b01080616120b06040807180b010f0807050f040b030105013b0105070b042d02010801060302030a 79
    0x501842c0d501e5482809000b408001100c0c11041d440b41441000f2000389c0018501001400040c500b0b034000d581001050501030800c1e032210005640d00c0400700b41c121192034010414002880c2c0900404003d400e20382c000b407100d141014002403026012040350b580710350f81c012522040d80c03801d106403000490098455048192038080d5002d0844a520044812508920001a00500c003140c2c45025601584020420364045081118000007005441c54001c1c0e6803880120941c0c0e450b0000e1004184000140014074901440c00203a4852101d098119a0500c0c4012400340c1e8401c030f5003400c1144500300110640c841c0a011101e40c0282c29145084c00c03800500407d440744484080d40c100c407000da8841022003400c24007409400c0c4a4910a480c405414842402c401d82c401c501e1070000c1b0041c90014148800e03615612803107c0107807401c2d10001d80c65403500115210f4075400b83c00c0d000700080d81a8501c0b01540c002480c0c01d0b014400c1004040d40800400e01d040307015082011459601018401003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 345007778 1250 345006528 345006559
    0x30602040e0603070b071a0c09030a150e0604110904050709110409060503031204060b120115090b01020601230109080a030215060d020f0f01020a0c061139030c 70
    0x4501040c0d032910702c24807800c4400100050284202c03050254403280c0b01d20408280e040114007000c0c068091624404c0c00c1c06440441d4404100003403110b0300a800e01d120082d078cc0b18000003121519016440c51783c2000301080046031300090001b0301c4034415607586000d9562030074070608040c4c1b1600030030380c07d50418a00845000c8000043c006940c2000001c01101e540d800825a50f40f003030300c406170045120240058086581984160304103000075041500105003003807141d08503000d0070040b155a01d00c3e044144154111407140d0002d2283c280018000c40d410882c45800c4904240241c110003812114040c1c1d4a9124040800041000f0790031503ca0307030344c0c900d0080c3d1100380421425880c100340c003000036075a01c1d10070742e01d1030340302c2d0040c0030f403040c404011080c0504140110f45060543c03246080c01000140c0c92030394440284aa50303210105d01100c01c2c10941854421b4519008500b848a040c41240c0c40804011201c4510812480c0b031581c101c0300480c1c244400c02c803127142d00ca0b52800c600c3c0c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 345009028 1250 345007778 345007799
    0x4050312070207062a030e031c1d0307030510050a15030f030e040b0f1509090f1b09090601180b0d020d1803050a050d061220010c0506060d080403060204 67
    0x40c1c808075140c0701050710300c4002c2170001c4002c035020408141c46075000e41c3c0c0800e01581014038040390150a03149010059024220341201015203c00068003980c070840140005940c03000c1103101c00c0300917104940c42e40d1503403907864042d086c44454507943c5401051454410383d100800c11905807500126203592030804c6000c0b030601c0c40c0c05502083c95401c50709040d00d03091186403050500148030101e204282c0f400c0c40032901000105000e5040100302004080d030b0307a010028481d120404d11031090b0710b840b0102e0000342d5081400e29424030f205002a081c1551040f00c80c40d032045083c0f804214008910201000e420301a62190142480010b9502040c1c89281c0003020880070040301031191900600320036a0a01c680c0300c4c0500002e1042c008806640d108900402d07140c2d6481d480481d0301031300c84800312400d10b9802c10841e002c582203480c400b00380c400c0c4c0b9140802103009080c402101c01468594644a07103000b49413500c9119001d80c240c041141420680300510f03000740c011902c654903403c542c0c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 345010278 1250 345009028 345009043
    0x13020913030305060f01050f0a050f0706060807150503010302040207020f040c0504171603060b28060305070804110f0114120601080c0f0406030f06030510051801140f040503120702 79
    0x500283c28031000419138241a80510500300f410794a0074030b821030b8091800d01c00e4209414500800c030040041d22048100748010300000c900403000003c40c10b1a0107034281c80e04480b039110850718101c07140c0c5180c0301504a03041c0c0b41100c2e010350740560b4844003440007500d580e200c0c000b400d600c05c0c6002c1c0402c20031648100070b441519280f5181c6071f4042c44129200356501c0043c9000c44c1c54000d4008184001001900402d2919002070010500c2e803d4610007100c10200a044c0624040c0d4041020491140d1501800f80c1181d00c608000e100d904103031b16240c0c0016808200c01e8080c041e040b034104826440f420710505580c840940f22038443d41c4003d0001420141600c03010300060240700850000301d4041e003180d0708142e6013852903190500c2d000083d0050034101050100b490f54404000021800521801a01c0c0944400008075854443c4a4403803103403510440e101075a00d070007202d0031480d0002d98429009029040306440310b598914009103035200c0c000f402024a050142445440d54001881c80f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 345011528 1250 345010278 345010283
    0xf0a0c060c0c020f2b0c080607120b0603090d11030f07050304080f120318100f140a1b0507060f06230303070b06100c061a01030f0b031513020913 64
    0x13203544410001c122840112000b1004c82d8031210406a129044924045160b58402c10602c01d600d03a42e0940182006800c83c1d240c000319048649807600c1c814148910b0752140302c2101e1013400c50030407c0e00365988180351a01c0c402409005501c945e82003104105503466600c1c2c0c2d08486969007402d240660b100d81251091039160310030f10b44410103540000c1a10071015a0300c00c07180e400c6035140001d2840b98040d0202900642c01001d1500d08109102e0254a6488210507004500180c41c4000003603180b4005280001162501664164007580000418881c1e00e103480c00944441150400000400700c00c61230030700481c40c11000080900041d5103400c064800c0c0c5440504030841d100600d6203d100b0b40d02d0050200d400140010403520700002c4298207407445180c90008254240d03144022905c3e18084034490500d9412352201e0396030b040c0502e1070802600c403400d105000d01c210100f9510021007800246505141000640740080503c104800c15002411800d079401c1111104a0079819820207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 345012778 1250 345011528 345011539
    0xc0406180b03010203010308030627160e01020c0603010612110406020c1302070203030d050703021b060117070b0f0a210b04141003080a12060f050a0e09030f0a0c060c0c02 75
    0x72140d00d018800d9038122600085868030b542c0d00c038030030010005511017250751720080d501c0141080c0c00980510034030985010400018010700080040d0040b00c00b4110141198000c0085900d40e032545411780b4111200b50030b00085611401d041d101c003a00c1a100d00c21501c50001c9400038240342e0028962804c42070503075644589500080a40d8103070f10900304042d4040d8000c0040c801c1c003450b0b079030095070b015045240040c205800c04000480c0c43d103050260080c5544220010f0110700541c29081901940c01401064402d00d031040d100440d00400e01507010b14200401c0351441c49000b03440252051529280c059480c0c855801d688000704070f983c0c0c000e03002d1442c03c406200c0b961300384080349009040904c55000410300c4c5584c0d900745a4031102c03412003000944100068506070342d000e10000b4005120480c2d92850902e000d01004002d10307803046c030b125241c000901ca4103d10101c100e81c0c0000700a440161351b0121035038190f600d4086240010082c03850100c82025090317011102c0e02c1c0c0a44222503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 345014028 1250 345012778 345012791
    0xe090318030a0507051e0904050106030506013f0b181209092809080403171312061d010b1206060f01030902150309030a0e09010b0301060c050c040618 66
    0xc1c950307984402c000041c0142d02419041c001c0389000c81c21055000ba03810b00384007a0302401804502c55200942d0304940da03a4443d038081c801c00c001805058058203900001c1400070000140d0740c1c8555000400740c85010802d00310144a003010a2007100041d40c01609902c10340c14420898903281c0588107094103507000388460010002011400c8071854800142080d00b08e80b249200d0300004d40c086140c0d014080746d1800d20031803068050054042d0a40100c5001d6280c0f483d40c01c1c00d0000520113010044803420410542c42d220001842c40d0040d9500101d4800709022140740210003860f000703105905010a0301c19140c58800150803000c001c00b0b003074902e0705d540700c8000000790f6125815120b05a0001d40d042d0807081c1e0b94800d03445902c120740020306d541c00e0404100c414054652098030b40070025040020750702c050f01e8003c0d8031803400034410390f09003030a503140064019042c0410301a184c1001032080300364080c010108003c00313a02e000184200307d41c0d0750351200082206000d079050709615041c841c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 345015278 1250 345014028 345014077
    0xf080a0f11030906040b030a0605030f0a1104050609040807140a12020c01080f1308070b040c030c120305030c0304052416090e010329191d10050603070e0903 69
    0x109030750759024058131250400d03051503050601030300020034034107281d84c0e66440081d456408101d5a1114002d010103015000c20310f0404210071a54483c803a40980d01300404d224141d22203030412903006402078100d039258011840c14100c60324500204003403d10134080c040c418440c0325004102108200e4081300c0900c00c481e0019507013a90215074050000c0c510200144010240d459181901031062500c00d2406450742ea42d500413800954007950795010311039040c000c01c10b044004c07601500d42d04881000c0d0f06e00036500145640b000a00c0d01e1001d00e00840443d041004c03c115000c80380c90004000040303140103001100c1c04076400c80c5d544c005105030402e11100e06001e9048207007551120700d1750b058580e082d500e42e01d0070301078440c03030080c11802030101198408091140c180c0c0288501d80e60340800e40106611141903030b20800d440b007e030805c803a1203500b46000009103415080b080b090003091a51382e1100181c1030004d25403009140c08040c1c020050a4107000c00101040311103100806403568200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 345016528 1250 345015278 345015283
    0x510020c16120c03170906040b09010305011a180a03060c0809010f0612080921070311120a1b26070e040201051b01020f0c010b0f012102070f080a0f11 66
    0x280b001900d002c12442c3c0c02d001040b4000d0081d2006145841920320307091140002c100e00e94055403003600209404680c0f00c241e90717807500805006010185500d8140000c00800c299a031152410424000008c80c000701d85c10b46074484400025030300001f082285050a0303101410041081390505225407804221070791455040c800d140030350743c500070201e10010103076603544201d500218103243d014803241c8031402240306a81010802008100150000c00d14600d00407039084140c0328424400c1c0d1030b14100c52682900002c41906141e04080900010307041c50a07245000d08050704126480289000d0603040750390441030054902444400300d0328050380e5910401000c0c141070b58000d000031010000d24000d18014881c070307030010f143d030000140742c50720700c0400352510b51003480d4040059441b95100c0c012440c0034941001240804e090040714029904a00300d201484c3e2901c000d56580d0100e00c000901c111b4640001c41e0301da00160045d52010000d00261100042c42c4183c0d0024254a4075541d10700e102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 345017778 1250 345016528 345016559
    0x5030901050705031509061206070c050d050304110108040f080d14010504020406140d0b0a0e04060f140106050a03150303031b0309020d0605040203010e0601090c030e030c0a0f0510020c16 82
    0x6203545d00c02000074104044d007000070b0a45544a800e00301d1841c816a0188155070042c802c9031507a51900c420b614101d41018100e6400324180300c420b00801010801c00071000c400d1810034a001030b1166a03034039040300809114007000e440c14101003018041403030142d025101c6d0350b1000c070b0703a201c80781c2c0d0714801c10050340320318052440020203a11074441e1685100380644510520303072501040c180905800f007000e04038030342d02420b0400c0c1040c05003c18040540301c0c0c2103404420060601c03540074542001c1c501c051041c0708000800000103038000321244280e12140403c207000f0100a40e59959060040207011030611100020740b03004d041170320047c002d02c10b40007150f0340980704a40f810f07a1601d60300e00a010080060740c040d520b400d42080694024804607018019211002400091700c10f40107003181c0042e00703049070a83c000c2203d04001d007000030729942182c0d030021301c44214566902e080303402c0144940c800d0f281c1a0002c500c0082e4250081071009000d122003034404030107035075030040003000502c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 345019028 1250 345017778 345017791
    0x42d061e0b0a030915020d02211b092103030a140106021009060207150f060f0302011704030203160c150521040201090b070602120f0105010203030c130b0a0503090105070503 76
    0x7020808800014026001000550301034000d54900c0503600c000841603034031428034580a5580000e002e90145510542ca8a40030141403640c0041c1c90a81d03011600c1000b904000c80781400c012038100c95aa5a808002e8280d00e2a0340f4944038401004082590701c2c0c00c191045030300c0e0b5007010203e0804a5100c000700307041341c426a0090800340c3c0009a10002083c150030705860b0305808000f400041600080074080041510a001540080500c4008112007407500b004411003581902000981e80c010b4012060200e1102c8181c081d48441c5016495842007042200c0550f5010381040280440c5c1c001c10030844d900074150100300600100100ea40e4401c03a02c800600420101e0b4152103030b14544a0340d0f074042d01c181031641000d9102d6541c0b04030b5030002c80d009c5611030f03000100c0a03407284d08820f4983d04072241040405495060600207502e13070000500700e034203041000c6034003402d0a5a10701680d0041c00000f5042c0d54402141900070159441214a190152700304008203030034602c40c500f282d22400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 345020278 1250 345019028 345019049
    0xb010605120c071a01060e0a24080a0f0c0203030712060e010b09030703020a09020c1204060203090130050103030305370f0f050906071706042d061e 65
    0x103580250542c2c060708040360540315500074005481400d0b1040302518003900c515110311042074040e20410107800916080012032545802400c0b400c0b02c003100e140e041d814414140028182d0311000e8000082c501e62107019102e9003040c0010303145030340100046010b2901c0ba41c1d00031540c1038440143c000e5448912a0110410340d20004205c40c00c0e4040203805a003000a0944000966035000100c4100c3c0d20303001000515400101004404400c0003520034800245842500b02480c00002075207034012081950706111054407484032580d01001d807403980d541d40402d40440e01c40102da444004103030074007007280800d140c180801c41c0c80f40c102c1040c41ea03d03c1c05440c1c20080d98030081c00c0d00700c0041460411a103090b25502007032403407034450113407060200540780005540e151900b41c00c9c1c40c0070030150010007032080c103013002e01c10450390301d100703550182c025071300810442c0c42c8402a14222080b00c0241c1840803100d081c1d00b00060003034100d0011903840d14801c0520200c16a40003200300c426110300003002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 345021528 1250 345020278 345020281
    0x1d04050d110f01140a0606020c0306060103110c060a0c0806011e030c1b05010e06010f0608010e061804110a1403031c0e0a0c030308010e060f09090c0a0807030b01060512 74
    0x512405007129024050000c1c1d82e41030907000311a0b401c0d100b2141c050001506100d0420103205190710801e03008003064802800420340b02408240c07a024041d2101d810903442d04584090104050202ca0000c05031204075840762070105030000040c8510516040081d141c3c2001c07420941c0b1903034008010f41030b1110311481809108001740c0060030101d4100301407140c1450724102c007020007811724461602440001c0307004a2501380d000e0400d403051b04000c07000f03209a541403042c43d5108940e1410b4503c50720300000252540300004c0c0d0000c0000c0c0ea8a901c2211400030003040017100d15070560405410307110750620944078010140a80b008099440e0035510600c00700e403840d1843c00c20b00c4940e00c26032720f00040790088102c034281011502d800a8441c450104010010194000c0c034040c01405c0000006905080120001e500d41e61520450f600c00d0313159501040c070040c401e210040c2c0c080f41c010061000c07680d82d0358ac1640c0750f00d401d21094600a0381d40d0300000340f541c000c0c1c04030f40380781c00d409209410f80d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 345022778 1250 345021528 345021553
    0x6090a030905180604240803190329010c0f03050c0d0504050102120d060812030709060509061206012007060e040504020609010c08040f140306070c050c06070611070c1d0405 76
    0x38055211b070649001403803d800c09410400e180a071014146079405540d89042c1c80400920300180308000004262801e01c0b08d85544da040d8011008801c007031602890a14903e10040340e15101c4000b0107040c2c0188106003104050f00040100003410001003950780e800d403220b100f55024061407050601580240c0c001c211040c200714028900c2c202c6c10180040d90680b1560400d2900030a614000b140d542e000041c860310310303040084440103013030a2030018601102d0001040140c0a40318094a0410070400816610380c045c110010b58110094070132403a040c10718625a0b0341d11000d03c186070104a403003440302c0c00c9080c1400b80c14403a80e001b0f04030034a000f100704011030b480241c1c02ca06840340304c0700307000c089184041081e5220080c4000203603003000140030401c250a20001604040a005504500c0400502c02040344800d1030b608454141c0c4844041c00c25001801092502440e0700400040100030000010810000e4a110030460041412100c2c0d2103040b0f8203081d18050425400220b00200303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 345024028 1250 345022778 345022781
    0x50103080d020c031204300e060d020c10060f080c060f1c0906090204050f040b0403110c0a03080301031b0305030708160b0f041511030c0a03090506090a030905180604 73
    0x3144243d20859103040f1540b1085000200c1c1074400301c0d2011030000001541c82e01720031800308503020000714105000c0448802400c0a4003150503580207580100344169490300c11b5065459410082d01568001c1e00e0403a5901c0080c0054041d0110000e5401d1010581c0100041d6108a2036405050540b800302034a0141842d50411401b072068580d20032541607030b04d416401900000c510a00010510112500c100400d6410003410a00600d07040c80801c0701042c88028219009505030802c150459013841d07882c1d0609501c0d200340340d0800c00c207010000c1007098010007107040f41c0c01005650b07400d8a0000d203140c0a40c100384005000e43e03006000302404640c00c0d000601503e0001c0c504030032080b003517550f02c12040300c0417290042240003840c108403e01c22100d03d060300050405104000e01c840310801d07034495004c068800400d0301c00102c0e43d0040d40303001c0d605c0b8130603240c0c100e030880e401e518107252801c2e0740384024242100003480214000445007400308900004156544180075150b540a05100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 345025278 1250 345024028 345024037
    0x14160501030f0c140d09051911061611030f032205030d050403140a140d020c060310030b0402030a170a09060f120c09030b16080906060307050d06060b0a030203070e04050103080d02 79
    0x21036107a98484110002e002007003244503c40c507500c03642c1a00c002314145120031030400d003041805400e04012250112460003442c2c0d216a90100c956840f540900d4046484c04003480801c01e45c074440010008403281a1480050005001c02c418554841c3c4940503d921406a01078103804990280403e00004070008a942c0606c1d9901048808440007034550001346a902280c404043d0012200990400d0b810721000c02d00c3c1c10145c9110f0f10b541407031010320300c0e0843c5501c00540090509000b10b0304564052040004040c1c01c22080d5104804031601c1c2c1e1140d6121005410220b1030f00000010b00b503000340742d0700e44040d880c0e489100c0151300c0c009902010b006c2c041c14420030007207a6580480021050203030a0b006021500c1d00c00030700140807001404c6000d0250100d9015440001004590791300020b2a070162401518000105c1c4030601c0d028010748510381103140a83e41c04180780c0c4240764141d0155219060a41d51060030054610a1104586003804080c020740402c1103280c0d40211160000e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 345026528 1250 345025278 345025297
    0x50d05090d02030912010e1006060e1008130609021302090307170616021f0c091a040b0702030f0106080607081f05040c0e031506180115080414160501030f0c14 70
    0x10070208000704103581041038100004a07410303949c68060201650141c40f07a16004c3c1c05a900c109128041e01c8003501160008201e1903640d030691030072030308010040d00507210341503001c0c100c0989140380150040c00b039081703a60040c5c000c0c4220100080c0c01c0e4640d041c448140d0700600090081030710baa424a80040405403030400941c8140100f00b481103d41c05005448050040d000040c0c0c40303204400107010b008194040300c1a003603944900a611140740040340c1c00c48045654207559110380d0300c04a4100120759958102c254600a00007e01c03000100d600c61003411513a031400120780d00c84481c0c034107881240545100c004c400280c1031115050a80c003041031a03c035070422a80c045500400a45001446400f0511111400c030603c082800c4c405054078400c4100c4840f0076156051031034004005080b040d0a500b04201800070605014405022030f100c01c0052090301c843c0c6401411084881c00e807489042d0001f4a845810b48100c1030138820507140045070750301c580b16130110700078040054100701000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 345027778 1250 345026528 345026531
    0xf1303030b062703030c0318040b090a09020108060111150603030f0d0e010509030910050a0c0c06050901020f03041505031015120b010314040303090c15050d05090d0203091201 77
    0x510100d56407400907014900f241008070210701d0100c040b0b0b4400c0743e00e542da128040d44c4144010034030b10b4008002c1c0d51a0182d01e4880800350001d1600040183c03d00d050180d8000140c5024000d40c114a5000b07203011074000c0c0c0b160700b9281c80d50001128060201c80000d0442c0d01f08605503d528003c035025940c201c1c0d03000701101e040c035500f400c00c20515848500f80415490341c0b03101250484000303000da15440704082002d10304012a0402090106d40034050110410900088600c2c840b40030f41d5040f00103542100c041080a929150064056800031000b54054418139400c0300e4440000002c803026a03691074895605d280703107003105a032540c0000d0440c02d41c400707800002198401008005400c07554065840c4501549081d001504550345080240c1c109402e11481c0960113040648040c0c0050345480d00043d80269420b08080d035806a030000311108115501c00c011142d40070000d0a040b41000c40200059113a0320880c4e80c1c2d0301d910b0300000e000b6030000d0080c0e4002d407078020082d03c00703514407070300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 345029028 1250 345027778 345027791
    0x703020f07180e01110f18030a0209180102040b07080a0314190902031002030708040b010911090d08220504060509011202010f0504090c1e020c1f090f090f0c080f130303 74
    0x1c1c4010390442010441b810340046900c1d1203c010707100762076488000a4000c1d06100c105600171502d0040018000010070b48400c00400d1100c4096044600400582820b141c940d03203070780307498082503010b415001e00003030420110700e6000f0f02c50347c0b4143c01182600e515000c0c00702044555400340441075026030b0f16001c2e16964a5080785140001d43c407940156480d205a0f01e0a840c01c12484041038101c4041580b804c001c001c0281000781c219070030031078221840c40740444549000603040c4941041f28061806014604108010100103407080e00c104580c140040b035104c4007400119442440740c091500006880b80d005035002d00e04050f0322103000d2400343c2c9010b480e0288101501c8610044400086004c5407542122514a001204841d030b00c1c0301410040c56010002084400c915800600d9001c500b00075456142c003030780e00c13a0000e101c00d58502070441e43ea807242c84c0080041d51104c0c1483c2e42002e581ca410580304990b014403e10602c20f07040040d0300d914503560540c2160b000b003141410f95502 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 345030278 1250 345029028 345029051
    0x12020d0203010312021207080d15031401060e011401080103020d03090506070803060f010e0108070e01030608151009021303030509040603021804050d03062d15050703020f07180e01 79
    0x1c0d40a903004007034128114005000092038010300504a4603010820f1000200040c2c01c0000c862040101c004041400c3e0354400b8071015440c156400104034541150a1006810044d008602215020040b5404903a60b48000c4085440c10a1005001030582c0c80180300614008a0350030644e8000d00d080710354551200041542d5900500f81035a02c002c0100400c0290b19290304103881c542c0c400e1038202a48400b1000207004c1c02409000ea07000e0010b160b641400f143d01c80d0f4085001891040c04507980342084c0020000072080598514154160b00d407008610380c81ca03402201d0020f0310101c405201240703152011100e640004070716a502c03548a034400405a51410402407000760004000c18031400c0501e802c078541801c4036413070014541052410048441980e0584203050710408400001a201c500310180ca620310760480c0044104081154035031a61140140c402184a80c0071155a107044800443c0e4a0301107209100c012401c0c502d9441d0b100c846a00284002c01c545000421440b9008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 345031528 1250 345030278 345030281
    0x6060206010515030c071e110f06030609090a02040510030507121a09070801050a020417060f061e0411070314090d03050d022b0c03021206120f07030506010612020a09050112020d 78
    0x71f4134140808a204030b400603c05c5001c00d904c420042203903484079103182a0045001800001c080320310500c02d42c0e0000703000e840c05002e02c112056009004220343c0c50120180000e10f000c50009841c14032507441c0204103071400340c00c019249a080443c40201c40000c030802070b08160010310000c0103004001c030008a8030b400b4040c260151980c072030050b03251414017180184504981c141c5012a44c0800b05112040c000e07250340d941c00010944a05407103900e0080d500080090503007803550002c1c9404885814010507001610a0030700c01e40d04c0e80342d040c1c0707441d0061003d0301031100c5055105100000c1003000a014000510f03403044040409810000071403550301c0d03601484050760108c904241213100390700300144150b00c0920500c0c28114284005e4450080d040c080c000d01c05801202d6580c0803c0d100101001030b450328940400465a01c0c03912807420680b584001e125250204404010140000f0110300aa9420b40c2186d074403440081d18110046a180d500385030301d0f0040c02d0f400c100350302003244079 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 345032778 1250 345031528 345031553
    0x20a0305060115030c05090a061209140705011b0317070c080310050f0312040306090f1211060609010605030a0504111e030d050f0f0c150403020a0606060206010515030c07 75
    0x1045242d03c1030b000c0822000c2d058525015015040140130094071109a1320306040d8815140280b800c2c514802e4000240e5005080044d4050b16401c00c40c25451401d110000d6084207443c4203982c2c00d041c598a00c504d6001e0180c201d400100820741345000c42085481d001503550b80600c1c646002540066161200341c1d4079481035030941f00500351501e05100d14102044140e0030010117500a10a0100d807071040344060289010040036035840f9480b00f0103010204c1e0480345d405400c13884503098071080c40405055003500d441d482045001c0c0700c00060452619503001030403607520703858451640d0385a40b0303204c0c020107004004031003602461500203c580c41d20907603000f00108086d0400503a4500f10304041c41c04410810503410820100841d41050305d101d0300b601e6101b92151402d0f0b032a480340382c4202e400c00c805000300300d1050020078100000d165001441103515070182100700581034840c1012030300d0b00e10900596400c140200346400561035124003d60740604202d10302801d0640c1c1c3d607556041e02c40c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 345034028 1250 345032778 345032789
    0x60c0a0f052a01272904060503010603050a0218010318050d050a09080c150d0f02030f01030605130503030c18030d080f150f010f022409070501030513020d020a03050601 74
    0x1036074480e2050b01e580101c030364000d428400c012000c000f0801030b00180c04041038080c041c4003460415038000000d0744401d0308003407103104e08001c07a00c0300e07203030100145550801d1041c01d0021b2709110101d1001c508900c2101d50904007841d51445c142d49060040d00540048402c07072008145000705040400d20030700c182e103c242000c1e950580c0e110a80721000f88400c4443d00100c810b03800c080121081661502c03038004c55255003255803a103a00860140100030101c100445124a0000041004800d10034041a0580b4440c0000300042c0d103400e242e11034180d4071060700814030350080012800348295a00079201d84e0085222001000003048003007814420800c2090380401c103014280b01150204441c441d03800318629001100b05448040040e40983e1400d50640c14030400e00e070160146031007441005506059141101c0b00d0605145080b030b2403020450303607402140901140866150b10034001c0702e000d071031940410110407131146c007040900942076204a0b0701c00c90a42e40040011070510182e8000d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 345035278 1250 345034028 345034093
    0xa060203041a040806040f030216120309080c0906090a0603020d06050403020712050703081b01090f06051f0302090702240609010b030f04030324030b0411060c0a0f05 73
    0x9242002c2030180e619804600b1070890418001404407010000d1035a912075007014007088046030a06050381024041040a000300050800101c1c24244100c094008540311342d0b00e40c445a41c0c1c403c8025111a15481e034146c0c0201034102049961810743c9035983c004061200005d4590b03174980c00208480c016400480d412500c817010841895014003100300103103c0601ca40c030f10f4014a81d20161205010b000060007414041010100c2c06007030304003917804040032070080000f003a050800c000310019001088804508000018002080000c0140640c00b40c440400c90f49a045508029603040b00501550451049d06a14840010f40655614460315504003a52080c1852000d0080d61031050700507034030740e54080041c08082c1e0f1100741401d43c02601460005000465941a4805c50117070042068001d11364010110600c1101c283da107000d0391041c0300c00317480d604500042c000c0d903004003a9442202e07000f01c480140802d00703104610ba2828414000d0310701415000414900440c0303819440c400c1f82 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 345036528 1250 345035278 345035287
    0xe0f0114090312011806032004060f1503090503070c0b0d0b01080c09010c11280f03051924051e270c090405010e100b10080705090a060203 61
    0x4002000540121015020b903107800c802c5881c4040010041c800d049400d410b00d0b4500040c1e05083e4040d0700a50792100c010541418460a42c0d091a12500c500502c542e00c2c104000404050341c810a41c202c1d1a19124581085008141980100002c070000d40d0709020410002000580c09011b5401410034000300c981c6034a41d440300b00d03045a1000256506010003101400000380d128802c0e2008020300b483c0000314100d42e45003c40c550008081441d410070500d000c00d001d104001200c08400d0300b4a0880e850000d6502e14003824000781d2880041c0c526000000e00140c411f200101c0561014040c4005c2e0040b0038000003841081008a0248201195600144124610010040400414058480881d904000718058140c9108050000980801c3d022070412040244200814444003d00514182c0740c00d0074114040e2601015034165401a2078808502d0409440f402d80c003400050446c1c0c0d0141d0254000f500c48000151030281440005d12108000390740700070014001c1d09469001d10b444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 345037778 1250 345036528 345036551
    0x5040f09060f08010212010e22141603020603130539030d14090420070c060f0801030602090f04020d0605090a14190e030d06060207090207030f0c060e0f01 68
    0x80110b50b0800111a401042206101c080c444012030644101c0c00c0d00998540ba200758014520b5031000d1103000d1545c081c00d02100b4010804811000b002d0700b5800d0342c001081318001800078441d0b41c003000b94840350600c0840e11811050f0f0f076004125210301c0403641344007002101100c8050241d000040e15a6121348100c2c0c2d01d001c52401040c148c80150020462802038402c0900404240001c950020102081118041d65140c0255060301c40c603040c04541e0000d022488081a400282c0581c0d42040401000a10b41d1113104204446000d07640c0300c0c0d94503400e5030785d450301a41c08400d100b6805280a52503039459540c0e4030080a0000b980000024900e1404081c040405801405003030003524121028107540320328a599944604442c0c814444000ea04242c28002d2003405044d19043c48040741c2c4507228001903000c10207881158007201c884951f0740648100760f21030b500c0c00a000481c02d1900c820601d00503000428034030321682c0041801021a505545000c922402a550580d1a005c00188 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 345039028 1250 345037778 345037799
    0x201090b030906040f0204060b0f0720090f0907031e060e12120c0403060207080a02070506071e0c0503060c0a0806030304061e0e04090b010503010e0c011d0105040f0906 74
    0x10400640329504501e40844219201c0400600251542a1407100700c8115526a4455400760030510051512802c0e10b140c41400740e0040001182d10701c1c030280110f42c402c0c0a5540390804808020032a404903503400e8514510b9200180103260688544040840040e4a1f240f4072240801c42c12008042c8a0302c505041059031281c06040e1402e0b08601c840c0c10320b0b420351034100c0c4c4825000c1010061aa1201200385400e0301c0385610180a040c07012134018108040503004091060703e035030885000680354400c00400d8410b004004059016140e035882c00d00d402a000d500300039005010003a8031560710700c00b0900b056400c40780c6c0d031458100000c110603010b40041c2e5098106505800075403c0074101f02001d0702c03203040800da000d0180d1201800a015500c20900a00c0000000d0414841442146400c00b90380300c0a00415120b075082103040404010005500d203042d15050352060403003c844040400d00c0c082c1c113a040c40c1002000c00012070320b8035481070354030001e01074601e000500d18030702018482d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 345040278 1250 345039028 345039047
    0x50a080a06051f09051c02011d090f060103091b2132011a0a06051c0203090c191703030403051813050708040c1707090c2a0201 56
    0x40c940c9000c005110549034420007808040004183c0703c030201c62003078291006207596100503880301451600c0176441024070b03014917200780b00384c841002c060701c610000001c103001c0c0c10030310741c0011318240080c400c3c0700000c5240d0b8104a0605000400b61066224080b131080c1e40701490991400f250001c0003440c1a010300c4006600010103a00045546552030400d0741880f207950302c0e4800a403a21200e41038003040380e40c002c2000d0840080018010360b5600034803402070405000c1c403819245074002881c0303016604039240342107050703050450350380b48800c80b80094001512946062003020700349a2180c0300e0038000c030544402d00055901480ca041e81041e0105a42c01400b00f06810500502c4006074004046d581d6422944240305211050040851000b0785510840d003000340c100b40138401041d8005820700d000707034000d02d1440386450321951100c00c03145504120190a41c40f4030803c00c00c02165a0100e520049a0328040c481e8002c040ca900030040c3c000d0000c07001d11340b403100428045603080121034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 345041528 1250 345040278 345040291
    0x70609030c14011a0402030403030e2a10051209030417060406050916030303050603100507051306051c05130501022a0106050a05130e19060614030d050c0f0607050a08 73
    0x284061501c000c00404c0400d500010580070345c0c1c0200100b000c05009410403845114800c003140c0820740300801d44007003440042c24011a0b02001c402e14951400c0005080d8001c009036240c543c64a801440c2c038207a4032000622080f200d0000b8800414225000d460100080a0b114010542c44c03c280c104001220f50107481d2003040d5011141c1c00400b0b070450007554003100d8060400240c155103650109040c20ba00079071608a81d071402040101c901d80060190104915060500030841e48451007030b112449000d030b0700301030f01c0d01c0c04082200840041d0401c0d5402480150b0b90359002420b903582e1400cde81c010012808845e5050480799190188403041e1700c8a07610100d000380046490500403d041090301e005990040c00201031403601c1428503001105000000d100305c80305a401d900045110340750404085900390300300b40001400c0a00841001010a030050103030105075803207481541c9903400b503c500310090141006600d60f45000b070040510400c441c1d140c3c150b445c01c083d20f0081c81c490004111 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 345042778 1250 345041528 345041531
    0x21081602012c010621020d150c050301080618030d0b0604090c09082b0804050c030a0606080f120a0804031e08010f090203090d050d180f021005030708130602070609030c1401 76
    0x31030685c602084c01111090301501d10741004401814000c091000d01c100c0045aa410070420241d400e0b0f022004504035500801a03840360740758284540040311841c1200d0700668803d002c044c000b054558003031018041d000b000c113460542c0c1e4603070300410f9401558656000c50420b00301003080ea802804290310844c0303078048010180c0780348514501c00400300d0710741d40c0401c66624005410010100402c6140301c6008003100d608401a1800c000544007070b0280c1c0e03034a4041c00e400381403000c400040c58030814204040c82c500303086412004890192001388107504000b00001d100c84409038141d980e0082c0c0455541d03c004540c100040c80c92151455404002034600c10010858818008940c00800888503d40941d840c2c0d100c402c0e810241c00c0c070b5483d0032460800c00c03000800304105084640d03401da00c20f803411440140310101c00d40d010b00040707440501107408480082c2064011300c240b81e42c03481c8103030401803e142040c0c0f2030404890340540c0c103c01142c1d001d88504244158109550100c1c8640c800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 345044028 1250 345042778 345042809
    0x100204031208040f061112190e0313050d030216032a0b0d05100f0f090b010e03060f040c0b03010806040c08070b07080306031203090a21081602012c0106 67
    0xd5131003662090050290800b5030707500102580d035a59204550030a001d84c0c42c2c003a0300c1d00b8035643c0c40c88680c4030541807510052a080341c2c804078840100036a00082000081c0440e050b1415003031040c000d56050007241113005015410410303408145008000d9802000c07906005c49e942d400308000c1d03600b10301ea43e501e07035024400d082040e569030a00b1612030500790f40000c10280c407540881da0305a5415001501044040c26001c100c811101401d0800c07102d80c2c290a0000e04025001950030b500d44002c1c154042c0c018100060703926041c010f40b01c3d0403c4c4100a0111010f503210310400d003c1d08203070414200354008030140130a00151090070b01c040c1c84000040d240051904190740d4042c4a038100017450707450301100280c031641d030500c011005006074200c004e907a8982404c620382c480c1d5907014102c418010080308411600c0d0345201d10ba0000065880c0c00c03445460301111507000314100340d40325046649540650400b84502130803507101d09254a20105607034000390000e425900e50b80c1284840341344608 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 345045278 1250 345044028 345044033
    0x601050f0a1401121a0102160b0f0c10020403060515010305090606040b060405150a080906010602060402090a15080c010908031c0c090b07030c0209070e090f07020a0510020403120804 80
    0x41a600840e00300c005400040c40305140181e0b903400b07800018000d041d207092500200601d80c4072041da500d840c00d03408c0d503200c004070071115020110f0b40e0056203507130075040c4a8503c0718004c1600178550036404a045644580c60100c582e0181da015420445132141c550301030065051601180b4070204009007024441c2d45041d20200740d480c42e0080c001442141c031000200c01d2a100c038401c07034000d020050039202c14103101240c01e40b4607900095600e000500708000141c030100d004203406058a1455000e0030042d22280c0803c03161000240c034520229a0750301040d103100c0c0507610060000c1402c00c01400701400b181002514100c21079004440a0f041080380000100c0c0b0408034110000703003134800040481c2400c408403a01a80740d040865404800641c034800d05810141c51140c6901c02c0352244031580d12880d04a40c1301d603d0052094000c40813401207501c0c0310b003c0201ca0b0b400089481256038820340c6480390740c505030140340060250b41c1e0002d424410320903c0200a040746820b03042c441c680d0304060f07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 345046528 1250 345045278 345045289
    0x4050705010e181b0702130204210f0219050303190e03070e0c0a050408070f560412050f0f10020a030b040609151a0403080904020c0102070807050601050f 68
    0x4044101041d4041e4071307103550740d44000682d0b0402d9000750403158169019000000254840c4c015405804c0d04403201124480c89a80219401c80c4d1060414940761035070350900c03e0000380b850902c211199580b00c04502a1010800780801032010b0303180c008074281c201c8002c0d080040c0008906e000340c0000d0340c02e0200c2041010307455002081d0094030350303039540004012986070145400540301c6001310100041c15124200816054402d0361629003440d540e00c10480c51542c020040040c601080b5448808403050003d00e4212100d007802d6042c0c002a065110880c8580c3c410f42141c2080c5800411450074008200804041c105d1583d00504804803039031002552540016241e5244a400144143e1094402d030003100388064098030a00c1000c0c0c848106401802000910002c03c10968100048202418032040d450181c60f03e07407940b03030605517200c002e03032584130600954200740c0030410386041450034402444440c0c01442400e84840040c0303409410084181d00c207900c83c0308640403102c0e160f50759 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 345047778 1250 345046528 345046531
    0x4060b0a0503090c06040303080103110405100b0d0e0706030c171003140c1c050d140d09030306080307060b13060e070309140d1215030f0b04020d060504050705010e18 73
    0x25070900e540c49903240c030501d038641150380a40d40c4c1c001d400071500100701070f00007120b0340c162f03842141203159007000c10b0240700480e081164aa0030200100c0d00400c82d941e603100040c450740088000106649841c0d0344041e2601c2c04903442240000c0e52004054882070f4000d00d030000030380c180b0001d4600d07404d1200000910348018000a000101d00c0c07a02c22950071800c0000060841c8081c140c1c4800780c1c00f000000c03010100242050343e0b5806520308400d400d1340304a40f0f40d4580400801a281000c2c24080d411703000700007400049060580c0c2c1c08010455040400142101d00d00c502c4c0e0105101341300c0018407400000c41c40da40c1d4040c0381820320500200590900d0140e0046042c90700190244060038a03100740031600321740d00031a0095040b80951142c2c4513962501110038841d0500407640c0368032408891045901c8081c01e402c2550169030005004c2182440c1c00a0004140c102c008000f42c40c0c400844100f910111385075440200100030550704011040410f0804590500c00040b00307414441c001c030b10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 345049028 1250 345047778 345047797
    0x1111902010b300703050307020f0d020109060806060c100624211b020114090d020a201906080c0403020616060204091e1821121a090604060b 62
    0x41c50490000c600f1014003000707041241c0c401c00c65404a60300d0600a40765805000103078018130440050903660f09040044014059040e56010403003803800404607101e0b24094180d83d4444001c01603402c9030710f420000d030f0483e10b84041c000180940752412064011588122480607280c041034120803264211350f1081707403403032000c0040d01c603000610380c50f000a0030324a458802d2408003412801595605502128901005c02c40c07285498441480d819650442c01182c00011b0703000d40030200015115800071500403084844c0c0600b44010100017440300c111078419080d0303507036544400304030280c1d100884036082a05c8441e1349103443d0950b000b0421510a51003451900d00e1060707400e5041003803e178110390003030a2403c0e080084500c007028000b51003200400f1f4840860a007590241410100d00e0700c4042e03154480030040141c0e101e800702040205e204010b174000d010042d0303039005a85843c0e02070381e031040a6031082d43c0c204415110800c00080005842c45021701e240050a200046800f01202d100c5035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 345050278 1250 345049028 345049069
    0x1060c0b0f060109120b0402131107110f030601060f0215060d0f0203070801020a2f030a080a0b030307030c05010c14040b0c070f0f081212070c080c01111902010b 71
    0x540c0c02c801070740c01c0002a401a9079108040b05003205001c444c081042c003c030300c00c03600450740c000110303d4031090310301b8000416440b40d005c000707650005224041070207114002410010140c0300d5480080d0400c8000d900800101e4803580c00913241d50341c1402603c0d181507082e14811594204200803c4001504610080803080e1101c0400155a07007081114010110707200295520440128010b10034504440c015689082030881100005045110b007c8400283c200440c14014220700403100d200000d005072454903510040f003107290310240700400180d4040e0321400600d0b520381c5001421036a240c512601041004120030101002d901c08690490311045c0700b454440c04003032005403d080d4141e10a0701800003c00b40012007028126807001124030710702c2a212050415a0918803074440c0f241031080c0325400000080c0c0640c0a0254490b0446c020803040d4105580546c3e0242192401590740302c84280105004c10a036200c002000744004c01d0f44001d1200e44000b1001c6050668401c80505065 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 345051528 1250 345050278 345050281
    0x100903020706050c01020d0507020c0310050105030606061b07060513050907080103030f0207080304032a0b090910050607050a0210050a080c1b030414190b1b011b020c0901060c0b0f 79
    0x350342501903c1800424070010003850411820280d500c1714bc450740103019004654540d012003280f032040e00d0407660f014001d008140d4420f400c01c013442e070042d0004400c410390400c004141a004000c040054451501c030701e652605422a00c0c40313480c001ea804144a031041c0c00400960a82c808407a0741104e52500707040100b000003640c1a41060032a401c4030410740702c046800028801c0e07400d00001451a4455030856008480f80c400c02c2c40a1140220050b03190300300044c101a0900e651407643c4601ca5040b0040c006031210002199a8007401041d03665a006404001c10b61801e54088649402d10b0304140d0310b0207503c118003901c2408018011443c0341008a07455400b842000403149148900000307503030b0350721f44070714903500c0812400c00a036000c1d0001d026884560f261581c0108140c5601d010305605100d07400b0022200080580d030424125501c88240b0703880350004407603030303800310540381c014000550400083c00f095a00580c424010040130a0000d800301c0d5156540307035002a00c4811101e0075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 345052778 1250 345051528 345051547
    0x40f0b0c0708090904141209090c03091b0102030918040615050f01080405011104080d020c0306060d120e0604090209040b032808070213060806060118140d0c03060b0310090302070605 80
    0x8001e07010031200d0b024003c0b69010154410030400070308c001e070812608050310b511003120144c568002140c07003c13815840042105090000641c4480d8941814811a850024944007203052100750940316080384265a0602c010406107000340040c0030701c403844940d0b289240100103484030303843d0760075141806859400314080c041c082d08000c2c01e904104086981e1560345004d0a56105180e80000e00107008254104565203404611180034450050040041b12240d0312401040c00c03400c501c0c8010300c2010303050500d4545482001d04000c181112006841d5140032051100382d441c00c01000303129400031004800540301b002000302c400d40c40801c4184a046217031030b114035184143c4002035800740c10800c0b1007031022610f411000580e0840c0096901e40d80700e110054601d0360b01c1c0103e030950804100400d001001480d100704d810342500a00b911106901e5880301100142d0a4000352030241d00c2d6480a00b00c3d05040183c0b66038140000b5041145600d6510000d48402090082400f0000001082e444 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 345054028 1250 345052778 345052793
    0xd020a09090510060602160e091e0c0a030516050103051b13032a060f0f0806040b0607110301110f03010b03042d030f05040605030a180b040f0b0c0708090904 69
    0xc0280b418804110045d11010069910041d60341030850f8100030000109103036004146080c02501058001c1c4060100071095243d8280240c2405010388201e0b403140b6980d65500719004021070144000d0179520302d100060201d143d080307800c40344c14982000c05000843d60280c014200d0001440c6050f51501c4201a104a0b0210740f07074000341508018015580c00190521140d40c0c1400503081003404095607600c06541e00c3e81c0703081c10744000c5980c425400346258011000c00d940000d00900c00030340c21410400280d220b0b0000481a00ca0f04000c480c58016400c1c24400c1903e00c024015002d03041034280d03120000203200501909a0180c0e000c00410100001e0858401c00340f10581c85620780c9108007d02c4d5a80c1c00c8103240d054002030801c0301a001315038007601c11602a2000c65403000d280d9507a0500300406082c6d04102c01e000004201048004a0340010a46026512a203071020390f40180d41002c4554900c013600d07c0d0782c0808208841030001c1d040d90215203420106454524050340c4500b005c52 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 345055278 1250 345054028 345054043
    0x20d020411120f2203030b190303031506020c030703080901031d0a150b01020304030204151d0a060812044103120309070b030a0603080a05030702010b0d020a090905 72
    0xc040c51011400040c8401000d815a00c07070380260f02c05018650f0b4603c0f460000c4031244640d0412020381480c0800400d20940019542c0b11002d4921f6007564402d4030007699211065000340c0c0040d940da058541400240d00016000b41001d100911000500e403001070b441c0d481a10000704002400a0841600d9000740c118a81140c80784200c20b4603016130710303070140d00d50f00d60b40012659990342e8640c52101c2240e91080c1807152006900460520f401c5500b40401030400700b070049020344819000240001002a246242e0355540c010300300141410043e0200b03070707601c6030000c4c10107420144000310070f80301080540d000c458244142d000592850403804006000750182c1800488804c14800d8507101820100b0341c40d500181d04031828441188500c40242c0130940d0072200c10340000008010150340702000c1d50f04070600d1000040c2c40c542d41d9607084803603440440c0882c08640040100140a41c0a200e04440c0000641e14107501d201d0541c00910003210b94010a10019540e010300c1d82840401c12a20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 345056528 1250 345055278 345055301
    0x7050705100e030301232d1009050d03020312040f0209090609030d0f0b030d0e030c0d05060711250e0603160611011e0204030b012111060c0604030905040c0912020d0204 74
    0x1004a0141000d51201c0107c200003851214102c0c0510a0854104585640c2e42078885036500e041c06c80c1000100622461400810b070f0451106106140b811070340b10400c9401240b01c0c03441b0b190600c44910508c80c2400008145040c19005070b410000810404011540c03456520040000e0104c09034180074020403903204c0b800e8143c07041c00d44061111745c1100382d94102503401c0301103403001c002076420480f66207206440100180c1146010840b150b00507201104100c1802003900ca8101140d40e51800c90303840088100040105800b0400c031020400d03041c0e0390042c04c00d0300a4808508003040520784c414181c414a0104034444065002c042c00039800708800d0351100440900325682ea10350f80c0080d4000c1c0c00240c81c0d0490110001840d00c1e00302070304511100341d1801c2c42c1410700342500c0390040004001c0c62039401c45010400c0e034401440600600b407007248280c481c60403c500301001e010403101c00d80c40d840280513250787c091241c05050002e107a40d02d58100c071502c0ca4488140b010a000e0001045032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 345057778 1250 345056528 345056539
    0xc17160806130614070801030303110901020316030309080712030609020901022e020c1b0105070201022e0c08040506070302040f140a0e07091401080103151a030607050705100e03030123 81
    0x610803241d9110046c1ea049034081d54080c4280d24501040c00d200748106652680503030f0040001c0c1c107a680b1681203c10249000f81070020b090b203c541c69922035540016000c98803038031940207081ca020381612885002c0e00b035040046091a80020010799030342e600f07540d03140c030b4103808200300141e12940c42d008004030340f1480810354071000903140c805d9880d42c0110003640d00103048441407549500c16010340324070301d80590003094042000d071000e0622840303805100d06078074119002c074035001c6450301512031410003940d41c9614a00d0207041c03ca080c4140a0142c2c0d04140c010801000a0914190003100b030318035011f4640040342400c800a100e050b010351043e10305440d200100680240c010b00850b00301e905c90890141014220030044031585024040209015500060104424081c6d800b001c00481c0f55a600181044440d00107031034100121000000140d00084000810200380015808524120303824010218000e040c1500c0740414040c0b9002c1c1c100c001e00d03010700e80c60180c01211003c000a8403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 345059028 1250 345057778 345057781
    0x80a020c0705040c230306030303010b031312110615090a0b0402210601081003080d09030c06091127040605040c0f03080a0f170c0c0a0c17160806130614 67
    0x1c0180a402c0c00e405c0010904120503c1070502d400c000e41101e100c0d40b0000c028516581c00d102da1480b0a40014041488540805000d94005205c18185150030801c1e500c55811040d045103080c0e25110300100401400300b03241c040f1000c3c070344440d54040c1d0884d00380d01c6c000c00c0c070f281b40101050003402074504640c0612101250b00080a440f020b0b490701950742a610307050703284e40742d00c0400400c400e0303844000c2110108008030307260144240e1004644074820f19203107019001e90381390001a12482d41050700c0d103054901c0041281c0c941054861640b0b490f02949203002d85041c071241c03095a9000f080540a04d03118000141001110002d00000e405102d208500441d02e900b0408041c0c0c201c110000049074002d5a0301490314002e0200c008201c40759040c070080d039680c50f41e121300e181c0c0028410001901c100d005800000315075008903005000e1003a210303400d80f90608000ca2610703419070020201d40c1c0c0c440e04240080c84010640903132001000078029880700452914000510402c480260215032010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 345060278 1250 345059028 345059051
    0x31b03041209060809070303081b0c060601020d0e0f09040305090a0605071101111914010e0c04060b090a06210612030305060a05060403031202041203050a08010e07080a020c070504 79
    0x1500425008441e50b181540d280d25440c0135102c007003050340c55552551054074100b001910420015a000d04440e402d03110030490f045042003541c00c401d803544110b030440350400c40c6659040080010101c00f928207441c0121006000c02c01911175a2a640c2c080c4c03c070100010249800f40d41103901540020b0084090107568900080c8070350000d45084550107001c071000f21680d840360780c2070380740360f8019009000940c0002d001d504400d41c0042040720000010070080090b28001c0c4100201040c04001400307082c00640b0400c41200c0341c40e080f010a00c2014810442e5540300c19901005903850b074101804d15520201f04215060140300c02496010f08190022600001e05039641545c14030a490a0001c2d444100810003c04003070301686d500301ca0180010000f007032003a0600080342071030550052403c2d0300c3c3c00c2c1501d03c0000041c0e040e008540001400c50722035078099200740c010218004000c020341000d803401020070780b010340b5900a007500882c0d0302c00c1300501400440001c00d03004004000e0a060503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 345061528 1250 345060278 345060293
    0x6040303121b1101060608010b0d0c030f0f0b03120703021c0210050412081b0901120603021c0b070f0503190b21010e01020403020306040b2206050a0f180602031b0304 73
    0x280340c1c0f40540d50a015000501c0c60080d49294180c0c0c0c0c011001e0390501521800c910000d0010303142c48001c15894814103480184107104120107500c05241c00f080344d5910200b418030744540080c0001c41414104121000300f90b010a1542c0c14500034190b40744414940a012890042d15140e40d0240c01d2500080c04100807404490485c1c20340240c5600340c0507954a0b000340240800803501512510040000a0041d0b2051200c501440201000001c045460350042040c6500c40b40c3c1100270403072044100028880c00f141015400007131458014001840114014114003010300045100b411003c418100c003002c0f40c0202c0140e64014120a207039140c0040c0000d83d400120b81a01115460481850a190300c103000b00d40c01d898001d0003c05413511140d0711000c410000030008014001001d0303200803e03204004540103518040c1002041d1410201500403c8803041441450a035142010034040144400d040d00816a04903000507104c1d62409109000c144c40d0440c080c0c0260000000c110411891 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 345062778 1250 345061528 345061547
    0x40201020a0503120f0106032a051b030a080603061e040f06140a06080102070c05090c0f04120c120b13080f0f07060605040b0616020312030a0e010507020c06040303121b 74
    0x30505d04c1801170341e803580280c040f91140c42101c2d4809051000b40c0c001a0802da401d02d1051221707182180c0380c0356003040c4548010f561103100324842d03000051410707503d0758130142c9941c00c45003c40242c0003d080041e207541280d0310444c03004000f0080d80c1e0001d002d01c140080d000c24020341100b0700f030111400c0c000100c0345001084a43c05202031810030007094200b014130075980c8090340446900195410441005031440000700614090712003000f020104560760702c0a4002461000c030000400325551408031500e034081d400a5420316410108440030a000d000b00340d40041c41d010202100c2011800c4c500701620521012606043c800505000303840480801002454081d003020480c10f40ca9504220559025074200c60b03000805005440001102100c80f00c0e100b4402002c4421002c80510200000e8008072160320360b030303599540c1e1104044c1c07084c0112503100442e813002e09580d001401c0040d00c45d01580c00003400704000307581c40154000d1554000008802c0e05168960040500d14004113218030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 345064028 1250 345062778 345062791
    0xa0213050613110d02030a1d070311030607140d0e060718090c020c22051806070801030519050c032d060106090605030604020d060b130e1e040201020a050312 69
    0x4010480b90309208140f10300c030020403007900038a01c2c2c00020350399070019401c084c00544a140d83c0d9021402c80010308040a40d400c1000340182c20090b145080041e584000798140c0c82c0240c104804000113180d00071510300390b00320b111000c80d449600090040004200b1b9948406a504c600802d02004ca47c20441d69144100c1a80307002002c90303118180700c0240c2d00b0407072440c405170340500054903aa01d04105210781c030402003100c095507c41e40380011401d80304141ca002c01001c140504040780e10348280801540036220741803a01c160352469955079a5600880c4e4000c01c00d00034034100d5020407605100f01c03a07804c0001000c4900c0d44500394038070079407034440d41004407c05c07010166491441727101041082c1229400e855094142e440d01740b041d90940d000074406580300e50b003003200342c030445034070302c42c20f070250240150207034031059214244450405d135508000c802e00d21600c00c2014440c251014100030302007442402032191918030040c0d2400c1c5920b04010301501001c00c5030010803003603200181c420003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 345065278 1250 345064028 345064039
    0x209040c03020403120806190902090a050105090a1a0c010e010b011e090621091218030f020f030309090906040309050904020303030a0e07051009031109010e180a02130506 75
    0xe00420254100c1c030a074400100500c90452110380c5490069040c1c41e800714000d4411000003141741a4414408016000342e1101640428144281c0c248203d030f81c4090308081c2000d6181592041c0080d010039006c0c803414200f9940e41101d5800c04030301c030b42a240c00e413a220009000500320f000686010b0481c12038414001442c80d00c500c043c03200307a07a1040c88258002e0b11400380081c01c00341d00310b0f5107141013033400c1010070b11001e826580c045603100d00700c465402450300c0700948054020044c00c800f401702c2e41cbc2c1080b034017490052022404c04070b081c610320382c3e04a0341021a90112404039081d4068410201e42c4541d0ba03204112000c4000702d1824442c91007580d4503001d40da102c00401032658020f03a0080d405034420f000041c0507005d2a0302c80c1c10f1800130310080314181a0740310000341d0750b4240d418102c400500c14031010400c21500c4030583c810a001168041550341c10408003103203200000309107080da100304000502c0c07011f5042c0103441d50541c01030400030302141b48000d400082c180c159243c2d4001c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 345066528 1250 345065278 345065291
    0x4080c0d17090a020108220f0819030204140427030c0b090102030115050304020a030206221703070215040b0721021219120c0233040b0408090306010801020904 70
    0xb2a001c030303900b000982e058440c5071490325403020620600c054024900c07921500300175041c1c0800c20740c860f80004903204500707090342c45103c080d5840080c1c040901134400d0500521050080c0d00b80722040504081c01545d0001c2e4561000c1c2c000b0396201d01c145000d21a2120494901050550108240311b25038002c400286e22922140c1c442801c0380b20911030000c000e10a100c3c100030451040004503000f41c0014409280c0e1500c03900050066480189411020764120810291844001418034010103074070501401c0e008409101e103441c1d01c1010344c0248940f0019003030118032003480054501074204124207585a02c0360345009551200201130013800c00862140b074034441440000d04421000d140040c81c0d04000c018026140100160109070302400759041c00c1400a4500c4c0c41111032960140d401060041004100a0320300d402038504134541120820b107441d0080c4078904159001a804408a0115951820109494002e041005a0601441000044d2100150090f20325818100c13000c1281 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 345067778 1250 345066528 345066541
    0x2040f08030307080609060d050d18080109050705190801050712050f0720030702120106060e09070f1206080d09091505151819081203011d04080c0d17 66
    0x740e01040303548400040d0328000007081d03810308200d03044d04100050000d00240d5a1551090700789a045480d0a00059840c070020041c0b1101400c401c008000c031100030000030995444070303601d40c030550203070500030004442c1420003001140100c200920405d002046282060880249200c8412105035201428a00460510041c00103010701452094031841c00c41801c4040a9a8408001001e0186808244100030243c0c41e8402e0104c054040d0200010302541000c4024000700e0410501901509481007002416504000f2040c902042800d02c05401c076844ca010a010300411740041d600d0303000d00700e04038503100c2c0c000f030202c0203a5440d110b0600041e000c08025902c0404035129182e400020010310034211412080100324406111140c540c80d422180c1c049008034446103420f8a41e80b84409042001440901084100c000c0400d2582c0c1f0355403510002c503d506c1ca801008000c0011902c004c5401c0140d580202c50b0079101050940d00d60004400c00a4261001201101d521410340782c0014a03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 345069028 1250 345067778 345067783
    0x612060b030606160309050a03030e030d0e100e210a1110120b060f0f0d0f0b01050d1d12090906030307170d09050115060e012c010311040902040f08 65
    0x20514015002600741381d032070740f20f40b0294110190107a00303000c25680f0110350b50310b524200c400518026190025600e441206140c0707031a01806240c02008507410340d8515540d0b8400800c20710105515049405d140300ccd100180c40e10001c0480c0814555a49030310991142011030000240c600a811840200a80e00103206032a200100e141d00040c8902e0040007050303c07168000c258204001d4441070521641c460140304551140380f950008071404190340a03101c10502a404200030b0600d03040c8481100c080019220b4014011000c1e140b07901d8150728010700e050b0782c00b140d481c0c042c00d008440d104864140400c00640c00806000d00858072034001a01d141800022038601c294000c016050344803040f443c0c04480e4006030b12a04103541c079008043c020440074001d40030315401107080b80c081e6070b1800001621844a00b281541408035040d0940d40560100e0800c4000a0b0011050040d4221500048000301000c40100d0b41b90100440c003c41c2c1d02d80c1030360281064071480907005541c141c51b400c519a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 345070278 1250 345069028 345069031
    0x30e011d010206060d05160920070201051801020c1003050603120c070614300a0513030503270708070b0f091009090f090c05040905030315030f06010612060b03 70
    0x140503a00c0340c40030a407241001c019030248240100301f03444c803c450483c03850132400a15481000e1a40e100c1c1d4403001c076807680c40031140709100708582c514505010350340040e2a0f4080c00c06049403004075480130740102e9000744402142c948000306001c0c2910354004010b07008000c19101c40c0c0c000e1044640d41e03410041140c045985a000c0c600c010801e003460110111584681c0150761214508244040c212840180316480d20070044014040741c000034102158010b40c02c004c102c0b0310007a04210600603408401410301f10301c82c4d058500700d0794960b80c540000c0c0c80d0140500080008507904181c0c0303403680c040414910259070f42c0c078050303851031aa074100c80006801840d0110784503480c200001c24007450845040d8a400d005424034440c007a940c3c000f51001c81c0c1044503803400083d2103130703901d800700701103250b510b400781074115010007100101d91a056078a0200421511481c1c0c920740301c00d242d81d502000518003411210088460a41c0c44440c001c1c0204042c0104110103401c10b440400c501d039000042d079 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 345071528 1250 345070278 345070337
    0x12150103020705100b01020f0706080f0a020301051008040203071802030103060b12030315010c060507050c0c030d0516023c011d0d02040e07141206040302030403021516030e01 77
    0x203040c0f21901000d01c40003000505e80710390640c03240b8200c56031321800034020b4000601c51398440a840f46030041d02e01200707010042030400640d02c100014802c035520601c0d04c0a03403c1103480c04c211541c1d15480401d16241e416002203000466031a0550070700e1a980d001907059078480c0400340841c0c500c0b40305001c0c0c1e03160403c0c14030003950028000140789a42030044407440b204149051142400705881d01c0040f18000d0702c07400c001620005803000400780400a03000741000980c02840481d500d603400a0042c05290342040001c04c44030350720381c00d56071000800800300b04801c0004401090311103101e020008110b50038240e82c141c1582c42a51580641e0800703000714900003014040320707030303d0082150481704494103d034000d640301c9000715846420441400640040c105c254400f10b1602d08200342018440c641c1c0841d64085020440000d5010056508590b41070b1041700c0030326121440082c1d64010705900e0984810804800014580d04c00b502e18440035007038a8440c26a12281079104070095041544c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 345072778 1250 345071528 345071533
    0xe160308030c03041e061413080d11070218070909060503060f0718170f0a0c0b0306010923040e1b01080c1303050a03110d0c02010f0c020612150103020705 68
    0x500042d0890002c40d481032003400c0c10120701e41003082000288000c08000c4da80d440d512070348907161034444908190884141074000c0e0f00c500142c3e036080c425105141c07031f20010948549138200e84901c40415552125802004614045400030018030325080c00c40f0403800080000a000510560038400c50b400e1781d00107405000d0980d01c0d0b0f902d40c0c840b100c0c042c2260040141140c1c0e400500e0486101d444090440366006040e41c030340d03c009003032411052001000d4580c010001c04c0001034144050802210b21040c1d23996141e41ea03850050381d628107617178011303000d4150301d0380307100301604826074840a0030b00c040718100328003c100d03080c0c0c40d40e4805401c0300d103504000a80c0c20b0085580610304443d4001e8030001c5a0b0701d03041c1c6102c1da1600b0a91554001c0350300e0b80c05505800109900440d03440320154101009018007030000c1c000400c000400a400303418003441c8062280d40c580300b00c030107045040c4c020341141c1d030b20310494203d4000648100c2d80c00d0b4402500d65001c40b96980f0070b008035042240c20000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 345074028 1250 345072778 345072781
    0x5070804150903090914070206060f0307170309060406080a110f0703030906020904020d0b100503070c080a0512010b0c1e030a0806060714031803010606080f10090f0e16030803 77
    0x646500a10100a0580138002240000505021280660b15010680c094000d159042070207003e0f240403806403181c4e1140000d8142803082e81c40014603c411149818400c0d5a05c6915032446810741c41610b101a81002c00007074040784054000745010f02501513003030100301c20501560701c0c06103401400075840c010b0f5010030a100200744280c2181d001380b80100070061034040144c00060890f4802d204102d00303c2d443c2e01000d60720b40b078642c0741240d0510041c2041c5180d0704d0401c070028490f482607100104a090045022600684180d0070385d00b408010104088155071101c41d5002c8075000581e450780c1d03a01c2000344000610340c19122000d88042488020760820800240c2510b1004d4020030081e00414140280c0d801b0448a0950801804c0881c1c0a1a90b5112900a42c0105481d069020740a40c4c1401001c010b61640f0140c2c607684801c00f024000141d0b26501d10181402c07005500900300d45040c1100981e4803202c580c02010b14512074012960a14000307454600701d003505220150440c1020f10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 345075278 1250 345074028 345074063
    0x1080c010c02150309120c241b1b030424030c0527030105040b040309091802061b010501080d0201231501110d031d210901030605150304030305070804 66
    0x2940e0170040b05010f41e0f01c43d200d8100c050301580c008103940750343e5601020309085809240702e01810f5815101c0a40400e51a041e100c036000700740381740300c0c2d1070740d103c800a01c0010580c2201240030340100c10005480e5200c0c0e4450543c549025082e104100942d02c940b00c88601034042e105154044030113403070726030829640314050508499480d000000d00004802414445d5030280700c4c030b030701c0b90f407242d211030100c2c1c24641001004002c0541090301d8641c90a1030b40c02100030b10311142c0e20704950440b0303a00d0340c40814112480030340300045455034030b40d070a180012641d008041003802c00009aa4020010300380310b042c000c04030242c00900c201c007110007140402c0d84441806880080c005040c10800e1815600841c42490034030340c0513008000070340d1600b06008810803244082c1c8424407000080031803822a580950280e1411250818945000075a03448241d000303800c608001c10000b0030781c0c01007404001c96110300c1e0744102c60440010b41ba11002400310b501449410f80215005402c200e00000a80c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 345076528 1250 345075278 345075319
    0x10903081503030c03070b0f0115051c11030901050f0604061d270102040503011d0c0111120406080603010501080f120708040e0103030c170315040218030a0b01080c010c02 75
    0x1e505803501070004101300f911400301000101500d910030f0580e16805e00c1e00340480000e000040c0c000e910310680641c460715001c3d51000a4400c2442c2042d00c00002118040c016030003404400d8954400d584044108841030704194415442000c9001c0c042e0601c0c0d540e201084100d039090301a10000ca0304200e203000040031065140c47d40700240940c021a02515001150100e4004454820060390005000d12050500307000300ae144180010151031290f040b00101510f459650b020b1604101d00c41c2d214496280003003211143c6200840241340e51280c5681c0001d0240d1000c0700c0d141d00a44c241400044c407400001003402034801a02e01030042c0c0031102030685036503480418150349500b801d00c408949020801031213030086101b522000d411034824944964a8140126105002c060520130000a801d00104150200504903001a42d540c0342e500800404450040900d8240c441e000a203820840c80d1074405060b5500700f030031540d6007040f400044880c0700019500a4104d00310100d0b0b003e080c00300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 345077778 1250 345076528 345076561
    0xf0f0a03060207110d0b070e0d031202074d01020c010c05030706060b0c010e150109020a051e0318070b0a0f1e21090c050105030603250302100201090308 67
    0xc43c03039940d01031380600004203402508141030360b950100e001485095508403119010001040d01d2501090041c0e8030082e01095a1300c142203007540e0009a01d404100b490030188440c10040c0c042003a25000c0524000800e040b2684d81a0405102021601c81551808080a40307000c1c140e0050924144050044500c111803c10849240c4410300214000550361301569000c1c001e0f018005494080e50440b080c20340c0d00015003040f1540084e04202c45046d006005a03054900c0d0080250351404030300c4080301c040c8191400c92210f421a000b031300030301c0c80c51080110f00444c4030f14500c4501140034414503031642e0051141d4103400300c0400001220a010300d003c0c400c0d01e0001d00744010001103200e165105081d4100d00e66001800da9680300b484510702c6841c42042e01400d13082007108003027503600da1050000900880381480f00100015010780d904008486403094840080a141c81d9078a001903011100c9000891049001c50542803215105101319102c0540541c0d4803c0e994544050007481d0000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 345079028 1250 345077778 345077783
    0x8160506040e011e080304080604170c0604140a0605100f0b030106050409110403060509100e07060203040315181407051c0b091c0e0910050d0b070e1309020f0f0a03060207 75
    0x30441320004100400f40082d000030031140000d00f0062810740b615942c048403582c254a041003081c81a403041d003030000303074040d40198803072020b481c3c0300304150f000740c5410154580102040e05000400580c003003080d10000494506400703070a01c1c0d54907500100c606020901038000015001c1c0402c001031030842d0441b880c010b006000c05482d254030f075120032090307920440f0030283c0c0d6481004e00a80c008102d2040c41c030000c1800703018003642d030304081000f9200c1c441c92101074484814114020394010b000d034402900c20047c2e01d00200c81251a03e4030066075010362680d0740c078500075030740c1c002120708104841480c500004c07180204200078a80e40c03980207180c042c0c82d1807441e00c61034806000ba0008000b001d5910001034840c110070b040e84c601000444100100004441c1c4141101000f468440000108005910a405007040d55a0b02c1c0c08450000c440203036241d1100d044401030404482c61340c0080c030f070680240c500f0300c2207900300410f100c9100e07029803232643c00517118030702000404d4071903002e44080351 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 345080278 1250 345079028 345079079
    0x11b020a1208100515030403110f1f2301060206090d05070201050715060f030c091107031b0803010b030121021e041107050c030d0e03070e0414010608160506040e01 72
    0x944500108802009944005c000070703400106000034550040d65540428481c5402040d400e03444112103a1100202061300a014003100228442050260007541d0903d900501c1c42c00c4070500d915944805000c2880703081c015005035030224000c224080b07030082d444000ba03140c80b4542a200e5004494036840071100340e03000b4600e0100040038030460302507603000303240c000e007161829801c41c103103c04002515806050046c0c42c01d0b41039003034042d0a80c2510005074142c24020061244c0e0000c001000300031040080204030008008910105c0308000b03141030301c400c5a1601103080f2660401c0903000c001810183d445022107106500034000b81640c5802c05a0103800402d072242c902d000e1050703072f801070310041310240c01c0000d000713006040801451002c80c0c0d051406115003100e102c00700f611000c0034024081c0b0448031500107420301560300c0350011650511002042041e6482460a403030b40304048140070903440b80c58000450740b0b031030019101920320101c402c2d00140d02c1c10301d00e4078005250356031081529 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 345081528 1250 345080278 345080311
    0x103030804140d200a0203150603070b030a0c08070e03100c0e03060c0703030b01020a0f02090a0209030f15100e180a080c010b10091206050405100c02011b020a1208 72
    0x5600501084640c030030543c4490408582e00d4000031505009140c0381d03c400d50040c500b04006d0b07900015803500f41c6601c1c11403814962134400101e403d0034141d1b040381d070000070000280a8000319a42c4072841050159844902c1a1104001125208440e40d41a541544040b014022411a03680a1303010948d160030b00d2050b180342c81c1c01082c00c0c508100e41c80f8a5041c80030034140180741d0035010300008620300f403000e082c140d412a651030f10402c40181c4064014110f20001a1b0745526960440d1160800201250380004143c11000e41c0c44c8109104030700036440c0c503000300e003402c10a04a40e0003030b0340b44101549203a94400503500603074411000b5800c403c0c8900300e07801001c50940b000404003003c1c46400828810703002003c0c4080720554400d10f40411114280800035500f140b500c1c0105d15600103c00306c2d503038403103042103071a00f07520755083c52042c1d1411002d5108580c055000d0728010100c551075040805841109a13101c103800c0501504030078551222040311442040100c2d4400c030035040030b207240c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 345082778 1250 345081528 345081563
    0x105010c1101230301050301150612090507031a06040b010323040618200108010f050105180402030109230f04170f030c2214040c2c1809060103030804 66
    0x1000750f6a02c810b852040f001005101c1c3e401e0038014501e125104010100089103408401040884c0f401000f40c46503550b2a6807100f00001400500019034024023504400c08041b5440110710006a52291240b07181004c000400c0d4000d000c2c12140c400c07141d2102086c601a6401c042e0842001023007101d4169850343c0f061300488e030842001c003c5a02400840d14008500c4150846000c00f420400703040c0140702e0010004280c1041090b0141c4d482840c00c0c40e102c2c04a94120f070a000c100601c480c0e0700c18000300001c0351503000345d40828807621b036424600030001c4070551151409541680c1c0342c082c05818000140100b018a000820b208820491b11481c6c034016002d001200d801c103a07407480e15400000f070075540340302868092210002c034002190000764541b107007032030420884600c41c4d40250f0b1142509040b40b40100300900220580b0440c080c06028040090141d0f045d500341080d214458880003440d4004800d0000c40c8203d18002c000d240da6402c1d5181a80c18150041040303a072228410b10b146c14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 345084028 1250 345082778 345082817
    0x4091802030f0c1c0b13150906020a09060311070b1003060f0213080f071403030904020d1413080d0504140d17092b021c0e04140105010c1101 62
    0x1c8942c0740d0180c11030000e14400c0055030b0754081d2244508603a030305050720102d43c4684072180c001000780c1d081000f181c40752a03c81c099480b40e43c0c80f002158a0000301d00d060000e10340007032038014102d0f81c1e6981c400c0c1d221002a802c440c64601c0807003030304e8420b018000c0010300103000c2a4214400300c040402096591b41c41800765420703500b4180626401181d03080d42c1040c800800c3c40a021888007a1055013805c884965440c221842405101c100010f81a10151070901c1191051b00019009550310111501860040c1c0700d481c1d9850441c1644200180240302e160441c2032040384d000342064544180840c2c1c440c013818003e032040e5500034242c84a0b03102e0301000c0006c8142080c030307a100e252880084a00b01c0c7e840000052034171140b5004294160004a0010409016080d107481010b56680c09610200e10b070440c480d01010b000d10441c40b5007968241c02440781c0c0903041c0e08542c140300d6581000c1c0742d540860001c2c4500c0b8085014444901c00007a00d000038020341310b2062504c0402c181900c1e0b0100d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 345085278 1250 345084028 345084043
    0x30106031b03050105061516030306080709140a022109071d070809120702040504080c0d1206080d0801090c03090c0f0614090a030b100b0a0306090f050c0409180203 72
    0xc400034892407040040000038042d0039131100c1d04844244205800d40c102540307034460342c2c2400310080082e141d484101402640001d002e013552404413801d082e00c44400c0c1c001001d1503040a8070800d031110028080ea6614004c648140c40d10700c0400c1c03243d54480c00103c60b00d08001d00201c1c0540110340740800c0071001207072a01000d0382034a51645040c280034a01034421100501442e190350010010301c095a034280c4210360900e079059070001505e980310b0611820501035506224460301904111240c0603a0104140c11230310098a010090907a494505541d183d4500c404000426001c10040080b9603040d030141d1080388550802044003106540e502409a90387c0c0c0155400414100301840016401030281e00c08034808220945403168041c002003c122491200601c03803c00d2000040c040202c01000c0c5008140603095540c403030f0300c005c20203409080c5d1030040e00e204c0b500d400c054000d0240c003070141c0d9018944c40110145003d0074200d5080103091030b800710b400f24052018100005880401060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 345086528 1250 345085278 345085313
    0x609020a0f1106040b0621010f05071b0c09050a0e0d081512060a0e1005013b060103020d021b070e0112050c0d020d0f03020a03080702030412060b03010603 68
    0x42600c0e40d03101015200c145003444080c0c0c2c59102504000014120560540e00018126450020382c201d0702001e0307031080d142c060900301d40c1d400c140254030280d03d42d030052402200785449084040034410148544260740030390251080d03144007030401014405d0350045811224400e00481d1301c420142e46c4a24040e19850500d0024001a04202980075100f000900995049880020815403a03030099980c074009801c031b00205640e6010b04801020400040c918118016814041c0d0340c0e5403400c06621070b000012140220840140c0c0601d041682c0e80e0800f4000d040000108654803103100440003900400813054a5542c2007100744182501050081801c400136001444101d042516601940106034090203070701c8003940c4640001900400c2221003000203803044007030041e00303000103003a001501e83d000d030509041511400906a0105125060a0098660a49640b0356000803682c0340f00b01c4c0b03d03203244916554680c40004290307420003100002c0090000c10440e450361501300c1400c19a10b4070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 345087778 1250 345086528 345086537
    0xa05060406031b0609050a060215070c0f060f0c080402010545030f01020906070b0c04030f0302010218010f0207030f050f010608060114010302040b030103140723131503150609020a 79
    0xc2001307503888180c20b009490b050b40d240e00280d14100c8040e6036a203180d01d50032030000070480043c4445114070104040782d6044000508400d0b000d062041c000c103044020244190300300105054014000d086450040d581070359810300e8003100c0b80181120324110031b2100b1540c0c3c1e00309803c4a00f104002c000381e140318108003581030303805d034214201481c2284061130b400b401c1e4014095101039694150a44072020307001007280c117141d0390364000c0c0c8010344929040107000941409080d000e16505502900904038a104502d11a018a20041d980c000382c8040c0d420059001c41418800504e41c1d8102c202707540c3c810001c8400300300d500c5400c0f82c25201d4a4016a2540d03010310010001d11280724101560100203003811032402d4200300240d81544014040138264600c160080c6500c58001c10007880106004034040d80c0d080031356115041c1028901a880d0b100b00c190a8012031500120301c20741400c0268400c051810740c0c034555800181c0310110f410040e41561700c80e0001804402030004045500d001d039035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 345089028 1250 345087778 345087833
    0x9030f09040b030c1f180b1b011503030504140405010b0313050f03041410030203070203030f09100c030501060e0328050708120405040c0e1003020d090204022106090403080a0506040603 81
    0x10000c10291080c0b022407044d00f008101048030441e0641290301c1042318500f42c020869603030b2040c84c050015201c01c20a400d26004001050581c060017402c00d0342c040403040c0b8040d401100800054410a028140c011641000032034035103248010075040c5039120300c5c140d420007040b0014090840c2c0041e405981203400b18401030001b460300180d5448601001c0c1811820350408036002275490100422030038550800d200842c0203c50304000d121000b42d94030405014012006200078082c181c20701ca0000407403400c52000d0710625003c01d2882c3c1550050740c4076000c0301c03d000090041e00601c01c44c161100e02401a012507800ca041c005c19064041c1102071a07552880c0606010440f00507031a03010800031401c1c80d0000c4c036550b107140300c42612000c0c90090303103d1541018120040c002910000d51185c80095110200e010310068a2138144c040c07410102d0310b0351502c09000c440001150010006411080040d401400552003680c00030380181000070000e40380d03940e405031811f40c00540500c0116184 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 345090278 1250 345089028 345089089
    0x1060806011706040f11130c02060c040501080a05060a120302030306031b010e010c0314120919020d06110918040c0906050609060d201209030f09040b030c 68
    0x400c0380e00402c40480001104554510069114900036000502103038215120a06100040701e06e0840c5042c010300380e403100300d001741440c8000c2980030031481c050f0182c2c5002440d44d05800c1d0075541164010b8540d5040d07030380c428080ba0020030b0b000f00f69641c1b001072035401040c000c550004104034288280c00841c1d0b2400c0007400c05290401288480b450010b00d10031154090368400103a42c0048802e00303004c41c5450440c40e05903250b49442410881d1010080741c0342e01405041e0700d03003600480c04038003a9110140c60190401d100e10790101c001e0b4102400c600d8050000358903500800800006080302814910070400052103014400d0811440359803000030b00c02404025003040c801003400c440300b042410325000104050b8024090346602c40c040108030110520500c3c0c01219185401c4030002204a0001101c0d0b0b82c0d41d0011410003c1c858101d50004207034200c00030072540341c1c5a0100300141410358000800006e881184030b0280c05000b8030042e04801e8950b0460700c040070020341103a001014040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 345091528 1250 345090278 345090283
    0x3270a050c090c07060e0a023a0308070f0e031204090506030c281d07090807050f04020a11060703050603150105090705070203071e03170304020315070e060c010608 72
    0x800910400d00032040c82840c9283c41c0480e00c0b0145c1c05600801c2c41860f800c0814180541e42001070f403c110002060351300d8000d82e0201c0d02d031a20a0a000c4944000100e0030301140120980004003c1156072012800b0315000d042048001e4040b0328081c025000550003107030900502c03c152042c050400308040c00340c010b0030301075658040350a40040c80445014800620508018526902800c14100d50201c41c00f0410302c00303c002e80180825800029a40e0610303006803107046441500150107481c020994010100d4294116400205036040e00f44100040000a41c050201c10040c41400d03458104004400c2c80035501c504203a44000a142c9402c1e01030600707000030b0061300b0311145206001840643c0e642000c4a403c10198601180c44001031b102003442e000d000d411451000764017914035440c140c18814001c061b2442401410409140140c00038114042517400035815001024030450700e8001050081d840703102842d002020184850100c0c600e5400031205841c140d444c5c0d8024400304004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 345092778 1250 345091528 345091543
    0xc1006061409030c0906120f0a03030b0315010501200f0a0312020a090b07051612050c12030306010f03021c0e1612080906090402030a020a0e19060503270a05 69
    0x780d00125140210b4440026140c4291600c1070303110300c003007601003845070321403c28241c100d80c00d82045031284400105500c0d40d40368400c004030000390030310308552140e05011910300242400d9004110041e42058015526100501108014201080707200045074504100368011046604090405981103080013400d40400ea1404010503004002442000d5400b00c02d00d0200e401c0e440700e0a40b240780a161090400d00282c02c2903030120007410004c203c0301e920b80302401643e84603004440b07139a031036007090014444004c550b00c101d5420074070000b0210350107035080c7e4225054902c1c0041c030b041030300c1155000b400f2040c10f0948000e982c0350480d0a04000c1040305003c40410520555000d5260401107807070340c4017044e0014078801c0b022902101c9a00d440085d07480850780244190345902e4247c0301040290031504010b00024480004c4001c0d0781407001058014510700308020a040b410310381e082c1c0d2240d20141450f45400100c01811460395079200f107450890f03030b100028187c3c4090a0a116180564 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 345094028 1250 345092778 345092807
    0x71a0a020309070b030903070204020307090e0f0403080105060c100507050d05010b0f1e13030b1603050106022a030f06040b0702071805070e0901260c0a060c080c100606 74
    0x20400c00c0c0300c66002c00003401c00840d542089001d540740d44912841e800d500590300c000703401078004010301c40c106403c086110140d1b804207203c0242a95200300400802c80305a03005404189190010300250902c840104020319107081102c1240006403020001c480f003c480c500d00003034000c681d0241070b2401e4007405005080c20071406040c541c1284040341684101100403400c1c00003071940b0001880c80f41c0580f0360000c03070105080c82466503030a00d80d003d614100c9840800424600e041e1141a02074032449060711034550090034050702c6000b00090070240c0e0a01c0020251001500024942d01040021105840d050140c512400c0a142035140c2620103400c81c4d080d0340140300300340051120259011095440d000010605440c4e0350001d4400f81034020b103103030700003001e4000440c1d40e4415030030f1074201c0c001c41e8400c4010035507914240d03034541d010408a2940524880e404000315885581c07542d2040d400781d201d8619044002e9650b0b40750059900000124507203803602040190340001c10120681c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 345095278 1250 345094028 345094031
    0x6061303060f0b0f15070f051f0b1c1709120f0115080d05070c080a06140709120f082502010206010b0a210f0905030309060106030e10020a050f071a0a 66
    0x201380c4002550003d000300c031184000030040b95403428000e0f1242c0e0742c1e0b11079401c10b090320a812011842e680c1a103401034016100d2034249080c882c0e40341094803104581c00603103003100c8040102960b41e500684c4d0010b280b104103010500500f5020f54401e0881c812100303a82e0000c113001c40005415509403003007000800441c045ca1042001450800310307101c00510348901d4101c2d038504c1c4520b84070034420a075412215203031090400750410065a984860380c5480d20010040c01580d4200c0300321000300d45030040c01e102e444d014190b04c00286624003c40041c1e0302c1106410f082c02c80c0e8a108443e4221210b03201c40500d4241032041c8295601480740340d000d0800d0600b002d1a10381321581c0540101040c010446445261080080144480d0b51058026068500007032104175035030306000381d50381c000b522807031320030f001e030380c00000c1c04070b000744580c80b000ca90b08409030811a01e008003050080d000905108184107081150701d1200c40d1035001000c9562040324230104410100400110344540203250880c800d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 345096528 1250 345095278 345095299
    0x24051905010504030f021f0203071511160f050a0803010306060902090d0f0f0b090a05010e010b180406240e0f072007050301020307050408061b1206061303060f0b 71
    0x142d030300408880982e500052407080030000c1d4408a4112205108041c42810000b00920741080d804401008201e0045000c1040c40810b03100442c201c4a004145a41d40a0f003000510308807580c2005030320001c2d005480d80801c10f51503481e81410190321400c101c8107944008010700030842c580c828440601281a800c50500d0b070960007242c5401c40c01c0901906139113031a04440100480354000030801580013864640c0d6050520391555100825602200e19501300900c1c4401e441051117406e2803802c0040c000000051b103910608e81090300607000791b8145032240c1e50200e1062881598000c80c01c00e5a204905442c903000e0604c5280d0806001d00d00313004c89035814070005c035600549242030003d805000d0740c0c2d901c02d1030307580710303c1c0001d1540865015400801085801d503040000b4108442440c01590b01c0d65903186031003803d0008a1000e58115036041c00181c10b5a0400600c2e130364080c0c4064856813419950408500500302c0543c0211020b03600d542c1c1c0e0000c0042d45001c0d22000000035240440c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 345097778 1250 345096528 345096539
    0x6022a07050a0512030903250e040503070602071a0c04050411070c030b1003020418021c030212030720010e101a0402070501110c060601090b03011d0a240519 69
    0x610603e12840e44205902c0d041c15401c030030148111216160002c0c2155220f0100f40e0004c681d540104503a842e495400a500003078003004501075501c42d0b540940910310b000d00541e1503d0003900b1002042d510500200b25075196010582500c2d8003030070b1030a1503d901d03503103018104810348445001140c40110240031520001c0ca8628604043d00d511814070391043c0e4508018640c20000c941c00654840e00300405180201400313455001068020303111101142d040c00220032800c0120000200181e203d40c1580c3c4400c10315001858110105240120f080c0842110491265880240e0001c0d1030f5903c0390480d00c10391080100d440c2c011540f043c14803005100800c00038070520030198040c002c079000079103001004401c1d030041c3d50f00c0e0f20541c503107500c40da00e8510300c5a803448100d940e1804640c0001b00401d200c0049001d8070304858440ca0034805040180b1403009680038044c02c43d0800b180c03503100c0b8851007020f413000f500700521801c00800c0003a2814080081d044500c1d00c3d80780c040c400003c42840f2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 345099028 1250 345097778 345097789
    0x3050d0f120902151c0606050408060c1e0f03150405010b0f070807060e060709050915040902011101110d0b0f01020a171909030203060709060207170a06022a0705 71
    0x1c440000d500001c02040301e002080500c1e141100ea0203101c040003410146020f4000000d6009465400b001c0200075241d40f4180e5491049000300320996015000165034910440000c107600d403c4110b5014619589040600464104200c007880507007000c82004814482d840b4401d110603c2144c044c07119501d0110403d40d2841804800307090580001901003d101c007460890b00000e030301c0340c1e0812540c0280c80440da01c508080e2050750010b000d0390fa0004162801ca00c00e2402600e440c4491044030401d041084010980704608038140804600c4c04000e20000b031190415079400e804d02c0696402d00340d0b03041d4044507480c10351188607420106041c811a40c0c0000c107c071f40a079206074100d1455981001c22445070107a45840b8498000c4805000d01312a0302084020889109030125800e40e101d812040e103d00940b806498010380c8804802c00c400c00c10401610700c404a41c0b03080d1817900d44903454034016640040d20141c4020980a0b03880c002c2c03002e8009048040010300007030b10201307090000240307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 345100278 1250 345099028 345099047
    0xc07140c010e1009050d06060302090a02030613090311010c09091401030503071205040b070503120708040f15090804090e0f071d100b070f03030e030a0206060405090309030d050403050d0f 82
    0x600943e60a500a03250700d0242d610800503080003015420080364a1418101408060008a018460f800c000c9200552280285c80c01500008d00b00011451020542c1c0020492034200b0350400000100c07244c01100300b0300c255030f0b20761002d5907111030642c1001400000e885d40320440c019900000401000426408410f4a80c1a940000381810501c0001030441d0305005075001313520710351b0000880b0740801500000a101a040e03518003001c00d80d40340390040c1e0704e8500440e000780207441d09483c00c0c80000c8021036441a5204800c40003e5130112680704e4030f100b600036070401030a441e0f686e0366451420000304480020300880d100142921402c0c2200b0364481c12243d4090259500001d01081c0000b11098528000e071407440069621280740c0d040ca010b82c240d4603002030380400c0c038000310002444000700444500c081650000c091517100c01092100034800204070b0344079030105002c15681d5950900c10601d070a9560759400352594198242107060280282460007071281c240c0c0b0840c1025007020540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 345101528 1250 345100278 345100307
    0x10509060901030603120c030216060203071106130b03191b030903120504050312010f060e090406061520030310050609040906020408070906050d051e0a0b0c07140c01 73
    0x229200c074003000c0180c001d0304031504000d02c4420100302c440e06050b030091148441038081d0b821154580b200c0a90780b00a045079001e0040180c10402928000c00d0011003490410714019100c0c0c0d1502041c00107000d009003d0742c100c440070590010900c10340e903800c041e16005018107102c0404c80d0001241c802880035001011410a250b180c41419040c14080d090010b4201d0303001205000510303040c5070480d200d51104100c410021078240010034070300c0d86202c4240640d44142c0b14a40106141c0c07040101c0758600520440d04591034a102146240c03e024164002031a56142d9000e45039600e54941203203d0700e0804410540d005104010b03060b00c403400003904039401611010781e51048080800c0203400040e41c051704003400058001860340d0f0018515007103804114041000c20340361020401400d151080203065503110942c0d0310401c40c4c041c0700c1d12081c41b00050480b150304400da40ca560f09400100c604070b549000105280c41440540c01508441c4045600a04281003141c000a058152000d042e0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 345102778 1250 345101528 345101539
    0x80610120c03021e10080c0a11031e04061704021c0302030d1418070311151e03061f1d0109091802280605091305040c050307060c02010509 61
    0x910309005950540001039500588105840f00401118420300e00418403001d02a02120150103d4503101d0502d06010b02e01034031400386000e009410072a400c180500400d2042d02042240103134452103410b0204c0040030110200c0c0d129031411102803c034041031107000207006040c1040100603940d100303100f040c43c0800c20440f004510b15040c102d286000f94001e1190b102d20341342000c0300140e08000310134440c1001400c0d80030800d28a090198450296100040500300c1961802c139691034095034640c8482d4004440c11b0030005907200f542208080f051085000210010600c5154203001052054034a106000c0120314228111700034082c46203141d0341b0046140c00c407061811603100f600340c540104402c81040c08000101410740400c8140c03c3c0e801c904c640324418010540100c1c1c41000ca02e04100d01c07940021803490240203a420b80d03c40351b542d0384c1c020130120700078060305c1c1103202d850302460080039205074031410034007403500d0710501d50008001d10840c0518030f00180e80c4101207404001080d80d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 345104028 1250 345102778 345102809
    0x501090c05040b1e0702060c060405010c0c0308060409050c091005040609090b060d020a0f08010608100e0a1e08120603010b0402030c0d1109040603150510050a030b04051203090f07080610 82
    0x81c1d10313007030700030003034000c0d80710a000503400e001560001c0c3d45c174001c5001d80002c0045549417001580c2c1c00c181c028006011520010000b113481c50590f10071500343d809042920819000c000000e0309804080703030450a0000d0210062015040500c1424081c11002c501040b00341c169844050348e01d4001031841e80710340c080501081c21500c81c203410100920609523003a03001c6480f0740da90f502038181802503003100c3c4120303000c802d510081c2e800f43d01010305810015100c0004e05442d444890740c20400e140201e000205503410000d40001c4c01010042460051000c80341440c000305800d4899106543e0710690040c010300c9076007001c900c102c0c0c04400c0c2c0c006001501c03038141540700030503004110001c2c1d401482e054001060145c001c01d10344051100c3d03101080f9594131199403905022403800756903001094100244005101924482d070440d000754100d0b52203207a4031650f10364991044456024540151050b03180040c3d00700a80800340c8161400b50105240080000f602c1c0303402c074843c0401d44d841588 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 345105278 1250 345104028 345104077
    0x406080f060307170d1409060a051605070e0718030b16030e03030403090e0f010b03060411220501090b040506032206060b03040b060105090d1203060f090501090c05040b 74
    0x1000c3c0c0002c124804640d1045105440201c0c0c0b1400f040350480c0c00700b0010048a4005001d4008403407040400900c081d003485248c0204a60b141c0104240c40d101d0a408201c4e0700c04036104011550003030500c440d1042c5075241c0480c000f0132a01172241f038404a410105401e20000b4030740400c0c3c0350700210303290303030700e2101099040114082c000e445101405400000180800c4c158490450000d441e0104200c00c4141c0702d90300d40b42d041e500b09105d217490012040c4081095454030703030403180201111091150034032070b01c208600b4005a114503106000001c02d0010000d42d41c000b01680000d0040c074a0080c1010300d82004180c00d403000800380c84605591000404109d0084d400504045810004c00c21000340c8401143c46180c0c001c0e14255803030190440012001d40c854403c4521817100501510351040450b52000031924408030300b8400c0c991104808102d060100441e8030041c58020705c00b060710351403c00104200c1d48440000e00800c10200402e100694000049030710061800d40510340c4c021024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 345106528 1250 345105278 345105283
    0x10206011712030405070f060c05030301090c0c080a031b113003190b120d2010051503010506010503041b053105191802030d050703080c0406080f0603 66
    0x2c02124400d0310012040c070041c8403001650100b80d80d100340d40403010315214881070710503101301500240158001c10040c00301c6916600521080922414081800d1600b0303035030640d10f9007180c42e0a80c000ba58034a02c0d642c0f04615118550760007003490902c421083c404010043d1101d551401505075407503010f507c82d42141c4200d0b00f200d618202c444c0002d8880c1848a80280b00a0203282c0191b100782c1005c5001c0b14902e869458100c0200f41d1600504809815031019100c58030880c000d810104000100b81904076414840011980c140a400251a03c0c060b54803c1207100c0008489010f80c1c03624003005600e90308082200c0d0441e80003294440328840e09400700800a1107900a240c02000209440da03104605410742021061000c0d40800b801c402c200742c0c1800c4036421505490702c004101901c0355000d080c0d5212503841180380f4440d81504840e500800d10b85510500700310000365002580704c0038164880141600410b40403c81072805160080040034860050700c408280800c0101195007079404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 345107778 1250 345106528 345106543
    0x906131e060f080c1005040e1f0803040306060b0405061e090d11010f0e03070b07050109020301021605060123090604090b0403030c1d0315041e0f11010503060102060117 74
    0xd40c003072290580342d091442c0740340100d104841c8240701d10303401c410796440c0c0080950000d580503075039541000d280445036860040080d0041e43c075050002918500c85003105d21a0025000c91002903613210f14501d003910481d201940240400e10041c0414005955000c0c100c075031114a0740c225903040420981c08280511801d007650742d00c86820305141c2e04101a882c1900c0845e2026240c1d0361341d030003030548299600c0e009213149907410780103401d007403280741e04003005812228095400000c0d54849a408642280d22a010710306481040742c14080070098104002805000c50002030420020b00601c0e80b03000c9142d4070085445146080d0006d501a117840c0d02c40202143c101070444064100360502800902098500740e0000c1d911202c51504022981c600520001000d001840710300c1341015500c220302009002102c0281c0310201007260310074105078205040303010f07041d4004401c141e0b20700840f0100203000c47e641404130910400403039a80100f81c0034119504904041012240803903000e080040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 345109028 1250 345107778 345107831
    0x1050a060908060a090c180f0c020114360109050c061321060903110c0f0603061003020f070503040e0604060e190b130e01060b13060e01140408010e01050105090613 72
    0x3850b160350b02d40b50008e8002c42d28100070400c1c00c22080c80c401c00b00328282c030303010406101c0003810300000c501070b03801e44c0010a140c7c80c0c900306403507103d0b003c2c285845001c1c0c0d000d0300c8898181e03445a04000501805001c000d10561b0112065840c1107070400c9490790b00b100c248140740e60301d10210b82244e503203903010b96115140c50340160104102100c2c0d02d401b51242c1c52400d1420b007540310301565100b40d0304010103841410003008001600315502d50007006200002004440c0426030207220300c00d556009a4060101c0520400245464605000c0907141459000b041d02e880750313042c484100222840301c48030642002c1a9545601380000c02540301c0040e1904001c0b603034005140c81c24100c03040007180d204c195189903000007030010560b5040f01703142c103004800d983c40d0041c00d00e90042040c0c5002d0081201504c50604019170440c041c00700d40b150f160001ea100140fa40d4480306030303d1000030203100c0c81d809007108072445c0c80d29003414008150b402d0406440c0829055840301d000c4c1150b12800c061614a44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 345110278 1250 345109028 345109049
    0x70504020a02030d0506100903060e0102120f01030311012c0a0818040b041122080a140f210702060919030209010909080d0513060609020301050a060908060a090c 71
    0x901a000703540713078015046a2101407900010650501e096420889803010b59a1020300c020b00f103460b914010188000c0c0402d07199801c00245001d190705c4c2649a1040b804100d446980d98910f00b4054240e1b1204c264010480e4548403001150303205440a240e544d0a05180c0c104440c521b80850500e00700529030064445032005c80d8142c210030140b840010a4030003902c090210707802071810b00040d98502940c05843c0c01080c0010f91040710410250600f50900502d6050299600d501c914149144150156290929600300503441c100c10004a156149040000c1c005040030100d030040c8100891745107500ea03240011294259607521043e40c180d5000100f062103002c3c0c200f070040049680307920089002e0018a1300024004409100724a10b4a411001c0c1c94540724046203c2e50040000030710040700c04045101c0c940226441d840784801600034440010781d2035040c04d04002160794a80e10890820811910a008203640071030099003001e0200c1c00440d509600d460144901c0740e883d0010040c6a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 345111528 1250 345110278 345110287
    0x627150603010f060902190504030c1e090c0305060f010c0b0606030a06050301050915070c031718030c0d0915140c011d010911010302090d030e01020111070f0507120c0905060307050402 81
    0x41d85d190300400904011b07040540340e00350150002d07101c074092840041c1a4404400c000c1050f003401c0040104901102c440300c070a82e5071a000098203c82d641501540001d60361800c2040c6400c284240e4000343d0303001d0030000c00342c0c0d040c0e0741c0382300344002c004003200c2c002c03070340030001c15420911a000840540401002448945840c2040741c4e60740c02081034858816010b000400c23280360049071103c280c60b815985040c0c42c002c900c2000c8140c048041d00c44404c1c00012100909103501c14400751454a54100180124500d4500000d040706125080340031402d4a40c20580e0a0360707004070300302c0e100d1010054031944540020403001e004102c9007110709801d043c00116602e002c54198071603010070380718035249001c07038500b40011012400741032051504948100903100102c0d01071030700684103a10510002c645604107040d10b5040c0c0e040360344200d40c80000750743c8150402c50103025600c0034140b20320700754192450b00d0300c1e000c43d241b05500c5400c0f542543e95001c1000790f101844800007902000c1e1056645 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 345112778 1250 345111528 345111539
    0x40e0106080c09100612090c050d140f1f180c180f0b0114031b040f0305190c05120a0b07210c050f09010c02040501080627150603010f06 60
    0x441e101c65103440c1c800c0c10f0600c0080c002100c0c0c00002c0065407083d5688402c3c01d4400401d001c02040808401d0314180220100003445694140180b1303140c80c4104e40c1100c0303a00000140f949400c2203a02e210b40c10350007101c0c590030b55048001108440300341508010488100940303a41e4414020054080c3c03462a48040100b284128049a002c0d00d40000b4410080c9180003001d10b0b045400c50460366000904203200309a035412524050344d00540b0b5091030001c0c0f00c84034110341025522991044000e01e003003002c02c005001043c410b842d11a14545000d01c4210110399800040b41c05900501d0700c0303561030040c40d000d101410402c0d41001980620041c04900b01540c0180a0342c40702d60302e0702d04120034000d4880c1480c58500030011a01d005032034050821045507001c007690b821100710b103410898135508035005603071f1758007038180242080c0340078010504100c400c0e01600c10030801c0a24050010704034079060817000042014416002482d50700f5181c403050006409070140d000d01044090038184003054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 345114028 1250 345112778 345112783
    0x30a080c07080115150516060c030e010216061d03160210020f0703060c03090804090b0114030411061b1501240e0f03160303030507121b030b040e010608 67
    0xa1040103000c84a505070340e50350300d6007a0f440f20049242030340c000c080104009050984d184140d40142c2c2801410151000d907180f0006100b0035054800f06e071180c100c2d00d0340315010b106050140fa50328009518102c3d1400220751102d028041c001c048039034a045220b0300b800342c1c411035070316442942d094035551100010300e0b107011100c4410a80c030035101e05c03400002050000403440483c600345805008007a181d82c0781c0c080200356041c008018551034032403103c001090314004102401c0102070024001c035009000610344580020161440d00d000c0040c4804070342c688100380d111071421110250780365684440e0001e8120450304900c0c0034403901c07420132051184c45407014180d0b8401d0010740280c80802c2c894400000f41c00b09941c01150110394040d00c01e09040c03510303151014014040300c1882640c414a0401003809900940000343d84009005c0c4842d07000c98000403108400c3e409000f602c0e000c000d50100c048030001c1001c28559141d000e202142c07526046a2801d1040700001c0140d20b0303440300303201c1c7c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 345115278 1250 345114028 345114037
    0x2815030e1204032f060c03131406070b040204110316030b030303160c0f14031306031a010c0c0801020301080a02011404060e060d0204180e0d02010c0e010e0a05030a08 73
    0x980640303400741c01c00034260380c107480c112900308607a0364001d81248070200c101c124000300e450440036192140c407141d880c1e000007021181d1008004695034503d00c03001c075044d1600ca0b0003030b40e24400c40841c442120b966660903214019007003a5014a9501c451000900400c4800682c00400d4804000c01c0300b0102404104200d002082d05c00340308100700d0318105034403403104640817845041000b002c0b29440d0301c00d040c3c0304d05075031084141d440800f6858841d80c0b1100161881c4616551000540700551a40003540400412290505002c9422100c80d120f0a115203000414100000341c403950051019940c0440000e01e5aa00215600d5840e005000d071241d801c030340140e010818400840148900030380485007211515640c01d502c0c0b00d001410003040d1f0f80700e105044d03861030b02880007103a1031242042c8020481444480021080c0d881d512a07801c10b40c894084206591401d444d8007401c0b90040318a0704038200c02d1910005826035840082d03061005030304a01d0300b500c9038000d04002c03c8980c10051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 345116528 1250 345115278 345115301
    0x1b1b01020f15130524060a0608070507120c20030c06070206040b091305070215060d0312050601030f110304021f02030a0513090c020a0b15281503 64
    0xc5900c00190003005541ea480300c2d00c59040450040d0014071540c4140203250790441c442e100342c418005112070300312441042145580320038100e407402d00031246455108100200700c2403c0c025018030b0107034400f5181e400b440b980500113014558000c0c08051180740b41000c0c2c158044070307440d00340b0306500c1c4100c40b0100e883c04041c000d2058003a520060700d40306040e140c000d81d008007800d00e03050518042c2540341d000300d40c0d8035410403a0345000034480a814010705202d06007a41c0140207a01400c002d104e541030000d07200901800340340303100a01003070b4000d081c00b0a41758081c1c2c1c04222a1100e00048008001c0d041c0007003a502d1412124942d090700e5000114010b80c0211a10109000e84604036014000d200f00700d01c0160703004000f40c03d200c41c0503402410403103914841103290f41f41e0324002c89050300e070007040110042e00145901030800806644c0950001c1d00740050003480d1070303101c01003146124030882c02c804082086880900c00d2a446030201e000c2d1003111038480803400d29040103000740c80c000c44078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 345117778 1250 345116528 345116533
    0x907080a0b0a0302031c170c070213090203060615040906141f05030a09030c2306090f07330c0309080a030504030204021c11220f0501051b1b0102 64
    0x109801c40c502051010150b9030014040c0074602284902064160b0381400000c09110f40c1d22500c200845451081900c00c140c212903a981c0c036050b03441044513680d046e2074000f07156442c203c011000340c3c500080c102d40c404010b032a034240900030303500c00100c28001c0f588889103503814030781c02091a107005510046007060035980010010f242c5c1d02020184482141c0c0a0b001400520020b40c0048650700240c4c0014024203140303003410b5030b646517154000507403024a4802181806c80d141c454504110040c1d00004040180403110030140e084c50300c6902c030340309000c101c1c407201c407100c0f151200c2070301c200c040d90201602d07045420702509006061080121030960110307880c544c00244078440464401c41c11580344e5030340740c98107040d40c1c01c00c0001d400481c4503640440b905101001c0309020b074801c002d91a00c0c00075010f0f45440c12007042d03103850000490241c00710140c405040280601518481082d10800d003000c0d51a100b1843c0400240240304000c500c16114511030345d55601444030036568803441c2070b0b00707 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 345119028 1250 345117778 345117791
    0x114011203020a08030c130b2d0a0e0114160302100c08160c0506040b0a0e07081216060603031e0503160e0112060902030f010807080307110f0907080a 66
    0x10080e01100e040038003502581041d103448000401c00300056a0043e9030101e40d904110403041c2c440c05090564001000c040c500164420580042c01c00202070034038055191655040000c4014039540500d0812409000621a000980740c3c003c12031f5407003414155550a0300c0c1c3c41100220039810000d1501039000d40074211138801801894050741081400584400c0001d0303c4119503a4010300b201c5220798100f105520b4100c000403003d02ca41400359024401ca80e48070f041140c03280c800c40e00c3c000b6140340d007507102500c1040506400b02d200c4800425402c09103032510403080790402c01448820004001c0b40c9001030200815070082c04000700300300b01c0421f1050034081b44070251981d100603501400d945100d6440c070b80c945413060490680b501010315180c1c4a001d00900480207407402c903044640116004000c003d4482c90f014881401007142000400c0d00a18111035191603200da090f0107480749000d005a2042502c40d032141c0b088100f4090042076403880c0074032000700a01c405070780c0d00c4061380c140701 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 345120278 1250 345119028 345119039
    0x30408030601030c0f020c0904030527030c041a040209010507120807030c03090b0f0402061e031501020303161805060403050f0f0708120d1b200109030504030f0204060512011401 78
    0x174007044883c103440d00100018201c0e0820043c000600420442c1003042c104041e0486104502400c040610100300e003180d0302a4080405060450000c28035002d01d2900028505120011085241d03103d07095400680e03881d02440103c80c2032044400140041e0b00d0b107055201c074141e00c1004140700b0201940e040010076120b1500301d080d5141c00001910382074001002c83c0c40e9811a5002a411030301c020949441d0510700b0100405116456808810600010041007802806000500220304091001e140f5616040d8483d5001c9803d80c3d880c80100314440c2c0d2500e0880014200740c00242400608803921a503a13450025641e0080c1520300245006450090701034003c0041d1903001c1e541c1800240c00281d410b50040f818035001203101142550b12000b070404031400140340c10400a8880c1c1c1c403008008a060901c82485480701c1c01840281e25000703119010940c00310035a0107603903014034a0220b0003401d00001e009040903800c502c0d0700c0161413500440c03c1c1c40c1580180010420141c408a0981e42d54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 345121528 1250 345120278 345120287
    0x9040609022b0209060423090a150b031e04050a0b040c06121401090903051204030e190b041703211812030403050310030c120c0504090309031101030b06030408030601030c 75
    0x1000194000c0380a0006008902d503c070001031001001d1031411070087c003034170001400076405a4942070380e02d0761803012015034448042490050705076540070514604101c0e001d200400d51900140b4600d00d0014081010807070700317002151100760401000900c5080c1814841c13100000382c455840840c80108145800d803045000300b0025412000c14110316a2030100c440300902014201203041102c10010100048007410807a07010320300a582d0744500c0e400307800a0004244402410101564070610100660260300c4110b4059407140c04006016540486040c0d181d4000c5290300400210780510f45004d1701c69220f9414414840c0356268450102201a1244c8030070019541031581030040000402003030040c801160045049030841034131580e42c3c1c58100321020f058000500c04181c01e40000203212502c9405806014111010003112103aa9005000311500b840028a00c0d41e9802c28080e01d86c0c000c0e03101140892002c1c104a1740da103400c1c40c0c1100e095104881c041e001c01d14100301030b405070707108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 345122778 1250 345121528 345121537
    0x5010e0f0901030305090a0b070609170c0d12020409020c0c150406080f0414070e0601080708070816140f070606080d1b08160503070501052a09040609022b02 69
    0xa0103200050f42542c0f01151207034014101c3c04d400040300d560000c3c031452031400400c403090152000180c070f0f6006250815161001c0d003e01c11200c1c00c1401030029400000c82d60380b490000c3d5007490003041e003000c06c00784041d0143ea44283e603010300c04036604401e040c0104101c0d003906401c42d40c04c040d841c01c810006a0782d000d0f5004090000b014000018400300308054042d410030b00442d403d5455219203069a0f00c0c012360341c1c000021071003151091091a5811044507a00710056081034811483c1c80c844c02003484900505007000000881e5599480a004030a000700340441e111745255030307101c00c00c204003a60b48100c0b4115019031034242e000580580c00b10b05800d5490440d84c92400602d0704142c500d00440119009072403e1204001130003440021410f0f03d89014405c001444cac0325039040c1825821076000401c4410150158070083c001c4441c40c120340d1640c0000c1803681c40e2540908008140101881d4111040052001841c100400e16841c410a540480340341030040040c01422319800b41c1c082c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 345124028 1250 345122778 345122809
    0x312090e1501030203060a0e010803120f130308131704060206010905070813052401050306070306060f03020a0e1c0b090d0c0201050705031309050109061403100b1201090302010605010e 81
    0x8070014250700961294005641003080104000c0c0c0b500d840350390201d51040300381d1207034500327038030014035402000031464182c0c1d44500540c3c09072100d8500548101250140c0490003402c1004030b200180624010300c40ba64101600f1070454005e16074403411400300ca07845070058101610484000080c00a01401014811074490780e806205454130590403000498154044443d40602e4203091002d03a2810700e90202e05c01c4210160209526040605040c4400a400041014101002402143d401c0055041208a00d00e001a65141c00d10800c4a148010440496000e540000342440d503040c160f0801c408513000340282400c61302c501401541e2610f10b807019201082130261010050b40c0110007403c0c6032401103058034a00100d0041c00d800841050b0000d180240d618001804086401e00c2048003400d03806c03408074070480710100007940e0384041d4804400c0b415220f9110703010980300da40c065441900d014000b0301040c0c43d18a4007034044c02c668015580050b421140316001d9207802c05414440380f4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 345125278 1250 345124028 345124051
    0x60411150417100b04140105060c01021c0203180a0308010509100e2404110306041805060408070506060619030b060906070c150c020a090203070e0a0312090e 69
    0x14024810311500034420303035500002410038000020000d40904640b510304440c2c0024103240e041c0118403000b103403c91000b542c040c81c03804c1c90b038a4111800003807043c1940e104403030003900c0d111441c1c442ca0191181c0489140710492110b074800b0762810980103140240300ca1420147c5182359641d60540c1c4a0700c180c40500051100001085a402d0080fa40350f00080b0420300e4180039516503140150b40c45007031701d141462550102450090b034002055801a4000480c0c050050341450005810203000250410b4401d0755200340941c070f0480302d0746c841c1201c5c940c08000c0e01d4051400d41440d60480d08800000c1d41c131405180f0000e46130b89840d0013120700f200c551441c0f004c41c1d040204011402444880061034201004000c540c21603a108409401554450702a2007102c0c7c2c01c00074001d203208445480c0009100400801d000103a84596500c0160384504000680300c0e502c0c1041240c5910014a080380c22081c0d40c074011042c400e4041d1142c028800f180c6990810b1940c80d0039024449a041341c0c10b18092 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 345126528 1250 345125278 345125303
    0x209010b0307020a06140402030607230d09062d0207030f0e010905090a1e0504080f1e040b360d081903021e1801080703021201030c170604 61
    0x440500c0c06940c00a15034811650481c40355510601110a80c2c14220214000003007008210303d0100315559104060385003510b0f2454459144104400d040c80035107031010300c0852181c1710810760b684402019500070740103000c64804440c2000e40300350011880c42e1404100480c0b011042e2485c02210b45283d0316595211f0741042d80c2508403002c401c800b04090400416080001e882c0d5116030007030f40100c50701c48000851207404d940c010b1461480455403910749060500304408103400d030302650a5407010280250f070750b02c0d1b114031008d455942103011050f030000c0441d01141d400d910b84003403d070f005c000744e030402604c060307582a4492090006940340c0380200302c00078046503810000796141030684507900d03290400c130006180c00c090f04508603400f00047c0c0c3c0841c03280344030301c0c1501809081a4200b003400d031414041e8111421940c03820180581070140706130100e00c55620079030440c1c2c0040107408030b006103540c49141420309015144500c1101c05120309038482008000301e00340f409a684400c207c0000d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 345127778 1250 345126528 345126539
    0x50a1e020a0e1909020d20040f05090d0c03020f060108010f27020f12030d091106070b010905070c210207060504140d2d1b151110020d0501030b0112020901 68
    0x1e01344801040b82c2040200d5400800290700c05d00c040c60780d120400e41c82180030201c2c014081121142100f01140c2410003003402082caa021400b0002d40405181c841030700c2060f410282d02d001040030341c200c00c0d44216800015400c0043d8010290b102c0c02c1d84041c00072f02d102c100301c0341c0b40d44482078500314820069410a0300501d0a14404520306002408400390b00300e950141500b540c004160248031180c0f200d81034070801503142c1400c0e881000c1203c2442c1002e803030b80c440306800d86d41402543c103400e5540c400308024034000d0182d6094958007285031b403281080c20013040c14a1010350f900d180940300361440400c0c0c450090003034034155440300719402c4140d5140b00801028200c40701c02903504030310241d00d014540d4000380303900407103044061010340300d2103e501d00b0305000807141c2d400c003d00c00c200304428468040d20a01c034039070300302d00f610b804074015416800d22424011400c80501d00780340f0025104d4820032064005034101c034010740701d42c0b0080e03a072008603c042d820010310095100711041c0040c0b04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 345129028 1250 345127778 345127781
    0xa140307090204050f040c09121b0e04030c030f020a0b011e0b04051507080405061b06250806011130040b04120f050a0807050c04061a07050a1e020a0e19 67
    0x251040d60b072410018207680e0304e2059000c1480f404082c1c646e100140b1010460002b850b850f00d00a00500304040c1e01841d080d20020060300340b1034001010010003d060304041032081141036141c80e08094106e09a503541d10341000e40680380b40484060410001e1b00140891150003610308840d0060a21910840c1c500c600d0b80d02c66010500407118440c040c0300c045290b44420001d00308541002108400b00074410801924120340107001c0441100c0750900c003040084003a0f880300b00f1240310f0030715014a80311480180c4a082c02030270000b40034410070044801081e08064102883e1a08100317101c9680d034007801000701c610560003420040b000402040081c180b8074000201c46030f014820460488409546440c2072030b00c100020b41e920b50020840c4014400240f0080d80e013044211020403000d031400001d10843c0c811030803c180c0d070003400b03e0a00240074040c420401f13800c0d40540c1c45103884d4103605810455801c17080d0140d0282200ca17801150b0f017050742018038069420260f5402401104440140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 345130278 1250 345129028 345129041
    0x102010b1012240603021e0403021807020f060f180c0d08030c040305031c050a09050705040c030e0f01050106020f06071b0c0801050901050a0509030901080a020f090a140307090204050f04 82
    0x1030308001400407100d10030101d20a5007004d8a0584c1e00542d8070b603070740080d60031070303400c0d2054025003003404200410041e0342d1032070300d20a40d641da6480c3c42c1e5665960402030b8100985540c400c1203500408040010380300d034800465202d9000c0781030002c061550301c4081917503102c103040c8068200c0010303003500020810b141d001e176030700c4030030700c2e01c0b041c0350541340e5456904603088841407000825510343c110885d102240110381d0311031141c0208011620407034803a01d588100a00c1118000c0c0c0e9151070309030405110b5084454805102030031a0110158581041d0091030b091203840014026100880341c0b54201045603406140c1a50316518404865102c0707004000a181c0c08a13401520b1140006043e41d00b806400d1190a120300001080d16100e244603058582c014814607054000300200140c582c0c000c115550020442040103844039110f0402c09080d00c528601141d00c160815000a0001c0d540390000c1c00086d016410383d03404907510300240d800e03070145000d4a58060040c040d400382c281060341c802ca = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 345131528 1250 345130278 345130301
    0xd020102041d10081906050703090f030f020c0a03111002061e060f0a030818010207080d05090d0203031314060a09060c02031f020703140703021e070306060e060102010b1012 76
    0x10403d55100d05942c0741815402d0503241c42c2d0350125420007802801d109580c0e014289003400c0c07001000c00e80d540030303d29085400c002d052141900601e45a04d01c200500000400d0140a01c89690b80740d040030803142c0c4c100c50540f841050120040329840f8804510640140d49840c919020500c40b500a01d007026801803c00d50003030900340c107911242da10112044002c40c01001242e54500e62003984141c10602072040d1070540d40869810820302c0c4000540700714080407854820b440708110800030b4400065044082e5141c8804207a40c8440d02c002607480c1d084402c2003c80280d4140c00c0e0051081074042c4007003030001300d031201d001004102e0007003019114451004054610180d004100302c0d00c2815450341c8415801c2d400300c0e01d0000c05400c98540c0108604080f4507905040150358000e546940c58610f400c000c09a0200c03004808404010070f0b0099a445081844165101d500e14448a00110f451900541c2040000c0e0660f040074030524441c55030329540c84101c40b2032070400302c01800307400904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 345132778 1250 345131528 345131551
    0xb0f0313020301090c14011e1b05010c0f09060e0609040b0d14010b010f14030a09030c12050a1407020a03021002030d1407080f131101030204180e0d020102041d 70
    0x10b99080c800e444c00180700d15505042d89040a90480c0d00b00c0400a4150601102c4007684814001032454a103000005280c0114541c4e03c0360340d0140f081080d590020119824040c03000c140980040e28003020f04c4c2181c2e00c0e4612070766100740480c4d00081c0b031000241c018404002020581c00c0c5900115039020001d02030400c069200d50300e0707200c4400d00d0500e189407655680d52060030344d0b903c0903040000003600d1038402c00d4130740b8080f070391800c2e0311003d8a004085582d1b030321060704141c001e1107078220141d0010124181c0070500c06000d0a1a4031000e0100e000440a00043d40c411a1201c1540c0f81150081c00c8030f030083d400e5a0174001003810f82a40d401c00d522091080c5403480d002401185090b45811803034001e20300385400d016110b41400741c0251024441d03032042000e000174902280e1841500b000340301c2d040d81441350061380248a41d420449184d550080600c89203041e5812104042c410b2804403281030780520012400c070300560140d07035400b01040d13010b6035001207040d6a442c1c101d00406403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 345134028 1250 345132778 345132811
    0x130f020d02130b03010c0e0a090510030807030e0f061204030e04060f081f05040203060f07140f220807030204020304020312041e090902060307051c0609090b010f0b0f03 74
    0x18403018018002d821181e85416411030503003001c3c0941a2a8001070034100c0b00b50010341d001a200000c14014070b202191380364000390700d541030309104038003e54110700030035620303c000e0038004e04c03942406503500e00407103822244405608025044654103d80c803040d9107a40d8503299000c60703250503078400c010740c003070340b45e501c0840c045001c800310f0001000c1c244c0007003151010781c080307a0004044202280b44014a400b04010242c3ca0202e5a554040f400500440c2565038460094608805942c0d030410040d101050b070442800307400008041f04c1f00360302c05080406107502025083d81d6104c0c010070019400080c010001401c154018540240c401010b41d0010080300442940c0d581140e4820b8050004400c1114002021145010054a056181408032007900d801090030780c4406400c940400c040000d420100004140001c150640d6000d07080c000d01d80c0c1e0b0001312020b04980c6809544401c00c2400000390404c800001d80d00f2919410038030740c03d11000c040c412b2426003004060750f4403c8503100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 345135278 1250 345134028 345134033
    0xa03150807060e040b0a0e041401110d0606020c030607020715020106080303270d020a03050903010e010c02030301150809120a0c06060f0e15011e140c03040e090303130f020d 76
    0x46002d040155a00045036161508102c10f59510741c00160080a014000b408128003840380c56a0164000b4040348050008440c100d0040c403000c0300c1c001064030f01013840e21080d2400d8010b04201c8140c0c0d400c48442071241700425071220016078420000d61b024510030402d00c559000281f03e601c3c898000003952603600c110b4541144c2c803c6442c605001d500350748010390307148140721240800c054000140300031b40101002030f59801041c40d02900b4400042280c00c01d80c0d5094000c201403440311002484582c6000202035540d03042070041c0255200c01c1403041c0b00140c07284402c3d070303c0f50500400a000c0c030fa1406070308441c00e07408440d50a0401c070050032608040381c1540984d1009107a460002c440c01843e151000e98852009031541440b0101c50790b604a01d40c2e0321588401031030352103080c240a01107a000e41615504100c10310740e00c400c413011406041a000c00300180c0100c81049051140503680c006036240c60303210403a00720449520703141c0d648020401441d032003840144003a160390b82c4640c281c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 345136528 1250 345135278 345135283
    0x20a1e02090c13060912060908090409061a030a030206010e0702010204081e0c040b030c0f03010209180406151212020106090216050c09131b090e0f0601080604080a031508 75
    0x8940302c940010340002d00b541036154409042c2d0041c038061504504140c01d0a01404100c800d0b071101501d0140c44000d12011300110b00c0847d0340350700c0d00404c1085450007074a824405010b0580c0342511038452101c0b082100d04000c180d850030203034540e01900d241e03030034a040400146400343c0f0304c504540d0b0900000c100300000308900402104000c01c8203115228219016241c0b030f024000480c0650705107501603c150724001b4043c481e0f44000c070341190880c030481020038024017801c0c40c190717481450994000041d402035424103014a01480e42031019421050440c3d00c81800e81c4181c510600e554221880483c0c0b9001024541480c1c0b8030012840c203544880c0c401c2a6040f02c4841c402140b071880c3d4040c20020200214107144d002a1082916450000f110b100350145400016204802e072290300c1c5964244500c5002c0034110850080141080200f4604e95840540c44450400d1007080004101d030000020020301ca6a400b0040600c0c00340c08100484c06410349a500391011040c85601040c5c0c004c00303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 345137778 1250 345136528 345136531
    0xa0b0c030f0703020714060717070201020c030d1d04090c03081809041505090705030303150307030501060306090209100806061c020901030303051b07020f0609010903080c0102121501020a1e0209 85
    0x1c2e8002c1615a05146d01040d031600400c00144c498407003040305071b00040d5011015178901c0341c1003824035251a070030300040c1d0508103107410023a41809038920350510709400c12200001c92888105540b01c8615140c203100c1260030224000c1e00602400300f00b00000303400e10004102140280443c5640a102840400c8002000765404c42c0c0081340500c10043c0b0324524458141e1001840d001056038525000c0441d440c0d02c0080c0c441c0c0312a04d0360814140751920308110880055502c18000c010240d620f0501800501d410390b022840398103600d000c00c2c0d40782c02107003601090710000300240c20691560b07010040b044041004080748010800705820140e550a100b0750300a43c040d4402180601e8074180c0c0784007180059071010b0360050700740131a6026850700044511040c01c00c2d40c034507607640003040c010390704000983e01c01840b4080c00a6404c40403001074018100e102d80c80c0300c02c005c85e0b1b03e40c0340304030080e80305640d11203005a003c2c00d880310100d5800c2c0707507001c5c2403607503200400c80d0211684c0210318000c20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 345139028 1250 345137778 345137783
    0xf11030f0705042411060f0105150408030c0a03030e071d100302030604030305060907030e030f030702010e06040f06060f030827030a03030b09010b0403030801090b03100615020c040b0a0b0c030f07 86
    0x3000c91a8640c98012030718860500009024014505d04090005048041801094000cac0000480780410400d80011100917001e104220b80d111018414807070b5031403104203012000207060050340340041c0c5000500707a045e20403115140901c01448980c401d18204024500d03064032021150010250b102440035070b000d24041c1c0c1e004900d80c60904240114001c010b0010406c1500c0c12030014003d51000c0b05503115051290180c2d0348ea51035901080b4017508810703007008028042c5009000401c03144024000303420748101e406100055484205415882c1944406403c10fa410800001007800800700005601c101c82e1030b042c00d46a04101080c503080e02450700310003003992036982120034071f010840c0030b006102d1081c5035490a402c642d401005c0070018420306030120303120b00c80c40300150360038003d500d40f01c43d100358100a0309644090181c009034403002c681000d0700420b0310f00440d070305250080443d03c45018001d03014240c41e204201415a201e6199941140001d000b8100070b40d5401004000d810b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 345140278 1250 345139028 345139079
    0x301090f0312050f010602070302090a090b0903030f071d040b12010c11010b0f010f050a0212070b0109050603010e03180a050d0813060c0c03060b030f0609060a0f11030f070504 77
    0x142c11411140440781c01911414a03550748900400050f1350000301303201525410759034442c03142c41d4031459002905980c0f0008190f046014100800701000001440c8903101d0180e401c62140c031000b0080c0c8011090340100805c0400d1519a02000d0403d030f08034606245001c0c04402c15102402c0d18642142c004800d624001044482e140351007550034040d0704e42c00242211200e54002203000064015030069032002c06202c80881c048860500912003c001e255010070080d507500401c2c90041450082400b5010a00d498032001c5079031414144200c0d010081540021460401031010180f09a168030a13400d9100c840c02c940891341d43c482d05c510300c45080c864140c0039100c0000d0b0b80f04c07840202c03040c1c00013000c102101803010301180298403203004490300102d0005401c2c4444010a05000c101e440030701c013502c541010700c014150300280c0c18ac0b10f01c00c0c03843d00300081b44100d5954010b4a40901748510842f200b840403600300b10381200310030342080590400c43d18241c1d6801141c1643d00c4401c0d50041c00c0c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 345141528 1250 345140278 345140297
    0x213050a0510081501030f1704060e01032307032d02190f0504180603020d0f020102070807050105030a0f021303060209090708040f03081b27010302190305060301090f03 74
    0x1039400c105598040c0100002402448080d100c4c1540f0000c4144005483e05400307640071303024000f201d07560a01018030403d085944a0b140d03080945620416592203002031321b400c644da4425482015040102d55020140340360780e03150002c04401505400d034014080c1d101c070300c01d42d04403981a070041010922083c140562100032410107140840c0d03624044200380801440c5038904036512504440503280bc0e400c4404608000401c140c3c001e11180e080203400001d0300f020034051140d030b108003500081c1b0036422182038170740701d6005945030b0003980f0480f8007180307050001c202101281e40203682031003240500181089101110002c50800e01e40c0161206640000d0a507030504120300c00541c85522806c10780e01604183d43c0f4400101000d85000d010000600003050214074002d05002460700900005511611400401540c41d40c002c00a00100e031603039022403c0a5001c1e0080d01c040c0401d0304e01916010703070484029000307448028100c031390656a07090107200141c0c980754002d0f02e26000ba55403107a034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 345142778 1250 345141528 345141541
    0x5030106060207080709060501090915030602120a111c02030612070320012606150c070f050405060931080405030c0a0b04260102030727030f08070213050a05 69
    0x201405c0350800d90415060030000c0c013050360022141c2d01160340140001510300030181c10600310703d559420080c045400050f4a00d0440100c011840c01080480b03400c10800518000c048060310551600c80300d10b041c4815084a07566191b4081e50b03000001a000702e40100705500e190703080552a0300f04440d203030b000340701e00c00403207100c4200d51400500030308140c9143c0840d440310100f07070101c8064a022100b400000180a902c50706103244002c1d658080305a240d84aa5900701d1329034146000b011690300311600c0014480c03419000b030034001e10014010100c6c588030754800001c040c0740c070a01441d440e410784402c000300d1603c0d030703010084281c050050b258a0b01e0801041600303094181e030038144a8030110005220b0191441d04a4040300c0910902440c910f41d02440c400101e50001c0a8030200e503c04030400c520a900200c50940d000000c658045000c0c0b6210000f4100803d01d00002e88250b00e9480410001242d860040c040702d40010118206811264011001d4800886a6550558440c400c0c00b80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 345143884 1106 345142778 345142783
    0x604050a0f060b040501031a06120403020a1707020405010806040c1404090206042301090b120a090212070e070201020a12050703020f03090303070e0913060c02070503010606020708 79
    0x110941e0fa410022660b0018417070103012034105070043d800384440b0782003801042401001d0341c0c107042c009070710020701c580020802c80540c80792a814801060b040030340f00c810448a030002a646480700d01c103000603a54180c3c0201040d13070102d4244000104120383e40000d0303444100888408408100000d0041c100001000c1d41000000170003090400a40c00384480c510f460204110040300741d1801143c0c0c04280e8460708104403010b22130507211400c4030901d42d400c20300721040800c001c960b58002803003401c103103120700c1340d07543c02441c040001002118080e54040c040d8002141000741d07503480505140e401103100f0941a507164000b0f812207000342e0565030706e00719480703410751a89000e440b2217590307038019108800802e503840d94110701c034502403142510a000c60403026402c04681d50301c80c40500281e0364010154081c0407404505505d0920842c0014040e0f070f8000e103500d5251121860 = true := by decide +kernel

theorem cover : BRFrame.Cov 344964028 345143884 := by
  have h0 := BRFrame.cov_init 344964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 344964028 ≤ n) (h2 : n < 345143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
