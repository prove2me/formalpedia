-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3881
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:55.543784+00:00
-- url     : https://prove2.me/submissions/3f4907e3-c130-49d4-9630-a6fb51d31e5a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 697841726 ≤ n < 698021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 697842976 1250 697841726 697841737
    0xa05010e0d21090305090418051608060c07051c030c1805060a1407140f060106020c1c06150b0c010b040b011b03030902181f060212130320030f03 64
    0x140400d030716620060b1180001029490700c11414003605000d0442c0c95903603440340c4a911121032408540030007a40c6030450500240b43c22881c01c0d01e807800001c2c4500500005e036103034010144600b050380d82c102801c0443c601840381e02d06001c400301301030210025070b60580088040903819110120f502001c0500c001104003140107258110b101407000103c0c1c07500c0b600784403000f0f03140705034817034984442503c80000203158019405e00b60351114184140070f8108208282c01054648042c3c84150301110001e1203002d900400d50344082d03600704d20b18080c030840390f10090494501008008031569222100ca51581000c0c0900c0c50725440e2100855640c1468044e00d40c0b40001603403103022041a995070031440c4038050009504055443d03036203d0040c1c985042241141036503020448240c50320f062015a100401c01d1401d01030610b00e2010802203070001400051444015086074483c464140000030020513948060130501c1400035120340300d071440601501ca40c80542c241e8161800c1300040903607d01c6403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 697844226 1250 697842976 697843007
    0x30304032a12030c090f0b0405090907050a03080708130905061c02030c0607052107020901061b12020f03180f030a0f0605130605070e1e010c0b0c09030a05010e0d 71
    0x3020100800700c1c46036010f620030f2911070911170303041030b12125950038a5506030090121301e48001030a110074a8480345456000000303100170301500b814a070100e44402c0b1540300040c0300d040e0100d110000c0000550503605e4082c2182d510140080c0c0e94000b00e40901410b80d1070702d004905070312050305860480381031081c0007500507009110303400329001403004591040f502070352140501150544000582c0608540400d014541c00f41c0303c070520f004110040078182d219000384209010000303079410807d0b1715100e000c5c1e005000844955403102c0203038180b201c03c002c503005502000407481c480103141c0c1a50300c50490107503840c4440e44040c01c10325030380320404000070780442141980640041c42d55008a6444030003c00154500070780c0d81d0360300040c0c40c0162036100114085107129926070505c08205100c5508080c441711511043c4c50019041c0004e044000d4405920003001840c044614400c441c44d152001c2d00320f482c280720a0406500814034582800001e000e07001d00c48108910615103000403141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 697845476 1250 697844226 697844243
    0x30309080d02070b160c170a0c080a020303061e010c060903112d210a121e0b1507060b0f09011d0106080106050f0d0f050c07060509011107020108041103030304032a 72
    0x100c2c0d602c0401c87d508100c4808042040c110750104c00541c0c1d41d000341c01210005d400554590600300200701182142c1c0442440e110000306040140340e900003601020603410400024105074141021600c08080580d001402c0c0311310b051211312090040c0c024030000b42c68410445242c445400059155100561407201e072604040914404480c00e200801041407582800751450344c01c0c00741a4180d9920b64403403c00e0301507107114183c9410580c05000c0120303604890003c1060a1208a14403501400402424181d13940c405490240c444650100d80321a0082c801c1859603941d01d1001901c00c44503200c040140740441c00029100e01070501203042c1c1e503650f16420301700ba0780308540c25119004101c40e42c54540d11411001c5a8540500c1480d0144081040140e80c0303264505100d0180c0314083c1c10420268988010901350610712401d4940403942403804118607140da0070840400d84a0040541d80b500001040c00304050f0444441d00b60001c592608004400309a842210302c0b69488802400c4e266 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 697846726 1250 697845476 697845503
    0x3140115050108190c210507140c030c1b0321040302280603020d0c05091e061c0902010e090609010312020307080c0102030f0c070807030309080d02070b160c 69
    0x180101a019880300d400000071013642e03e00c2480300c06603190807041e0000306004c004030b03c510400d0300c0c80c04c1d110700109030010f01607801c0c803040082400d2100d540f41c01d1542c05c003180907a03038030b0320a104580700c41c00c40608039000b5030140d0174080703100b06111440520a200e013071805881c4620f84600d0a5506682d59401818a45140c007840000031244c0a181000000100d20f1300c1c3c28108110824003400c00c80e40c1c01130311390484030480d004807104141040d003440001c1c8030f40070700e581d80e410700307c0480d015074051450803d41754008201f06000e5201070458140040f0400441c01c036041d80103080c8075000740d0b50700d1f151040d048240b1a001500ba5030700b5070460807210050000c10900c502141070300040e88116850585982c503040007641013103408101c141d4000060101c0010080700f042d40241c4960807052500c0035642d594032040c4078804004040c03503281c00c00ca80920039444183d400c90144c00d04155550b248925181d414900f08032024240001151003141420703115034607041102e68072805054129 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 697847976 1250 697846726 697846729
    0xf080f07030312060e0702060106090609080a060b04060b0301180b060a0807081b040608010311030309030a030f020a020405040b040218070516050c0a1d0610090b0702010e0312040314011505 83
    0x80741da640d54802a183c942c503000582e0b01c0c07160081c905c540455800b6103449c2d410488010f0011405c3d50005040201501c003e005000002c90525412a401480010070410303450100e005400b4550003110181404000003400001244040003425540c0008001041c0c0203010803100b4040c000d2894001101d05002a00f000c1c003030030308c00c0e40001e0b4000c030900c24411031103039001c1182c0c8203070085000150500c2c0104100402803440537404881103000e0750411902801080d42d810300707650051700f0402c0382c0781d0300c3c80e03118001d0041d04140d1350090002d00c014a13081c204412901015901240030b61112a0a44045148058654003032246540d03070900e0718082c0703028458907074001d0b00256964001c05200522507a28a1020001458901050b03400310004185c26042c20310b00600d440c0c066120000142003560740308058030155000c140d0029211015400102c8900803601da1054061140300f030495507044180c0c0203441100e118101407200f05400c99001400ea42e52500300781a43c3c2004241031055 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 697849226 1250 697847976 697847987
    0x1605030402131d190b07050d0b150903300a051c0c09120201020618010b0a1410030b060a0c0f3807090b0c070807080105010f080f070303 60
    0x580000c1281440600001c0303060b040b0f0707045110908620b08a141030921110050101001280c03903050710003507090264981401003480141008100b140000b00c1c01a0550b856104560580b006003002c0c5020b010301110303000c543c2c03103004035610900c1007246101c0700c1d1074850741e44910361640d039620b2a12622640b03040d01c6d140c2c04c0b4250040500006001886104038020020700700a0381145010070390007950f075805412004580c001110408914403400d000d40d80024030340c0e401c8001c00e030b030320500d0125440c0a0382c0100511070380310780d1214000c000021105201d00c000304000d034045801301c0520740703140c01c1903086410300d42e18581c0240c0140016490580a4120b03c80e03c03a0081c103c82100b14410b81e542130944403111a211441031070401c401028261850001c9400342005074007480c9400c0450015114064610620305410400502200c241c0f070140540f10040890f1400c5500060f00e40c052540a81024003810303024010040340020300020000302920005004405084140d045032411a003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 697850476 1250 697849226 697849231
    0x3809030c060a110a2a030317040f05030d050709150c0b042402030a0f0b0315060f04060303020709050604020a05071502040f0902090108060118050d1401050f041208160503 75
    0x207010303110f00301c0794058406110f443c0741c1510030003080e00030040140b07000301c9142c142c24060281802c210010f000007500131a52030b20310b944600c0c44580030354a51030804174800310850000c0040c00301140b8001c3e203070b40d81d81105000f036040e81c8800c020a900c4160201410444900450000e0380c0050100f0224045952294005000d40360350340100003c02e60014018142c1128103850642c0081004000354107440780c0c0c2000c2001020038040d06201ca00042d43d60000042464143c016040104545a81d0055030350403004001d082401520b6403828003a48441c150704c50700c2542824080000d82e680340038400c4070200c20041d2121420500c0319201c040c6111804625000b201c0e60810001c5070100d00c061420009010610026968100e48000180020300181002c0d040c80080051689145801d4800b682500c0003035581c00480c4116040880410301030a40c2d00c00e955103003405001280700100d441c40d00c1940035120301b0304500c1403400100e81d001402c0b581c0b201124100d0000032210391241e401180c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 697851726 1250 697850476 697850497
    0xc051605011103090a0605100b1911060a090203071205120a020c0406090b03011a09010b0a020102091804120f09140315070306090f0e070501183809030c06 68
    0x280100400c00300b060310b5000341d030b004545034003801c45031041200500070603a10002d8010541c041c0c0703290800a040c00d004001d6118004071000c0e617800e00e0148140500c000076000b0004580b000d06110000c200200596603099000b401342c520040342010901105003822540f00c00101024040c01c003a5820540080104001714050010900e030f0301ea803540500e4018082190001400080d418101821145c840b4402e48074042903040300c80055a500b20b140341120070110750307030744d0ba01d8210004074020300c105041c8543c020a8080d503813003011001c0705818421032043e50707a502c203001c1e90300059541c0c100344d008610024403015010700003c0c90208400888420150440d050020034000b240c051980844080d80025903c01c0204074002c6203001e941c101c9807001c241001031100b01d006064681c4100c1c0205414421040a51400120303c424660003e103040c6403c80202c00c000140740b40f8000100c5070070001c06101071002451340c84032000f01c1d440850010010012468030b0414402107403c00d01840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 697852976 1250 697851726 697851731
    0x270b19112a060405010f18020a06050f0d020d02040515030f0103230d030c09141f180e150604060e0d03200c04150305030304030e0a03240501090c05160501 68
    0x900100c0d00b007080394080c40c41240085020503410040e40111118940b00711103040d03003181c0c030300c0150312034040a601352401444c000b40c0e0780107400303100900c6106000082d80748034800200c09011010940c09001901c1d000c40783c030f49200900c9102070b04540015070f1800c540c105001c00400000b09010307040180030b81b140b11002131410a041c075a80c00d225240c190480400d031030b60300500a1541c800782d001c010340100c5c1c00d0400c280c200200820460b888406071544407141444103111601c1c010580b0b42c401481c0d10410040315602c2d1010400304580596900c081800088441c4005141c500242c1d41a1160b07950b0f02040d05105204001000880720015014010070030f020040000c000703158103c4d1210320a00801d08841100140300458401030f280e02d850300f40c2e03203d06000162020040743c0e007254061800002a07000340700001c07846a45540010603c2054202075000401c0d82031034400418203c142c200a00d80c0c3c0e82406000361184092004000350b0100b00007282c940d803051324101e810b030080000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 697854226 1250 697852976 697853047
    0x6010e040c0e0f0a080a0b0a0207050109141501030812130c060e0a0f0e01061107090c08010e090c0303090105070f06090b06030d030209060706270b1911 67
    0x304003101c444031920707070024a81500c45102403d2524406031024030a46410040d1480d08914684805030040001d2801408030b0200b080044203405854401d50020001c014608142c5030050609101d40180107140c0a05080c000f0110500b4404604a0390030a04032442c1007d0b800351500054070080821812001480100703022542844000d00075002503140c55000c0d2501908000346000194041450298000c4050051402d01c0800a044a446081905941c038645100c0e504007103064100d4101c0a280542d01d2042030b49c0250303000e040351203500100300180c0750402070945031180c4841e81c0303030954401c01400103594458402426070fa130181170001100601a560030b4155100240e058440000e10b4050003100d14040c06252244802410110300d40900200410001e002c0d4243c040c041580c2e91140091980c104e0002c000f62800c02e000d0840ca031925482c0c690300126050792051081d403444007440818120f180320340401d0b4407110408504101b890700d266840b884c0e2054090b500203d07001e50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 697855476 1250 697854226 697854229
    0xd020301090c0b0301090e0a020a05010e0a080340051e0303030a02030924070e040f1803031a091302031504030f0806010c081606180c0f08010203040213020306010e 72
    0x461202510307006102c143e40e5494950510240c0395180e1301c2d0241f50300120001401640c4142040c1e0840e5000c0c203010502c9652840012240341a0364801c1e8140d01001a940ca40d2601e0860a03105400032031179181c2d840704450030360350f405200640c001101c40d0701141081c001450700b2081d0814183e0002151030050396000c0c0031904580081e2187c021481e000300c14041078a030b080c480d04450005004607241508030425155100aa0103051002403180380d0302a90517a403165000070403c2c20701c20382c0c244000210a0301b2940740541d1108280c0000b4074000701c074040106e10f20052510b03540003c0415481e83c48050403091400b8508034101e0f0b00d0312844508201c801403007a40b039445240662038040c100341e1042c001038681074004181c0d40c1042070402280000417180000d0790841016000c0c1190805070b28034151000702140c80403070459041c0020703050200150300d00a01c0a483c1d40e52411500c1c2c9035280d070250b00b40d01007a10000e600c4860000c08900c041e030294042d65010405140c00d46c00c403803d020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 697856726 1250 697855476 697855493
    0x4060f02040b12041a090a030309110d0f1505010f260a1b080706050307080403020c03062a041413060e0a0e1b100f090b12070206090304030f020d02030109 68
    0x1400d820f0100f04280c10881030001c004101007089030040203107042c0d45849070120391501c9011714024140341d602d1883d502404940700c42c4c202c40c07500107800100e0080c020309103032103041c407100c00803500d10300380400c1080b9410413030150030b0403031340500d62660641d0f04102c4040b000a070302040440680020902000d0058000c2100c410322a008500629654500384152207a141040d001010305500842c0c00308002070740002100c0d8000310f54604010151201d140c128101080070741c510794540f0424047c0301102008002c408808200702c03480c41e070348080601c003d80e240d010740e103e801020340040f107500f605d5041c2480f41c2c12034008081000100b06468810328007000354191039450110366036910080e00140100b180c2d4002d0f203404001c01c2d6a59011000080b1000780d103011080820402c0303643d54132103d00408995000d4094880d02c04c1d182d1104490402c840d00c02110000e00501c600030209442c0301003c0100c80907281c00043c50090000b05070284003111003104400c0342c05640c0d4000000214481d003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 697857976 1250 697856726 697856737
    0x50a12050306010f03090302120f090a06050c151506070212060108070303030b040b0906011b050106240f0f08041e0f06110a080f0921030f010b07030804060f02040b 72
    0xd80340c003501d80c1421070004207040040e49128044c145070405210202c1d0300007403500c80b0400d0404501d076540c0c80d68052b000850040c9141c46810103050316012413410b41142c060309004226408603003000501da2607001044c13000ba240507169032000104207941d400c1580051000e24005840012880e0300384141321324261003607001420681003520103008060b8540130b0311004d03032070844050102c07c0a030030000b0310034070001e86503506018107a5101c804621038009a000c1c40c03a0000001c110071951000038124003580031403240c1b0540c0b0068090604280183d0642800c25030076079401d008035208a00075150181c002c2c20942c0d540c000400c8890b20802c5c00c12003420118810b0704490203450042c40c0035000c2e50000700020410230302c248440c515066001802542c003240307040800e02c40391130f0300328001d0400c180c2003403041e805403100c0301905c43c9441240003540130319084900c00000b80ea8680038402d0900a024004001135440c1d4003140210301290808000d4407170100c0300620f4196100726900c0c055001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 697859226 1250 697857976 697858013
    0x150d02070b01080c0f0a060f03050a0e12041418040f0507090c051309020f070609020406080307081201090209150901030e1603050c09071e02070f1701050603010b0307050d050a 77
    0x14805103040c10311040d1000174050794002e040c6401d005005c2c100c086192116010550b444001410117040e503000850003040c1d590030f8440c001c41083c103580041d4854001c520403820b84001d080d5490400d1214010f8981680c0828000b94075070b82d460030502181800c09071407512526001103011025880307030450203003268841c0d5550301d014003900c04800c6a03640c40a12828418062403000708600f00c202c0d110a60302610008180f00103200260080c00180c110b0520344c131009c501c80302007011540040c60344a03d4040905160381e030300c80302601640308540801d40c22194903d03910035031b00b9080024140c481030504001c10941483c848880c40d103c1c170000c03010042c2d64252410410b1000070720803001e822400307039200d07001460000d40c060010104c40c4400c1e40c410b03060450b00b0031602c2c400d0203014081c02c440940f40c00b40c3c9640e036200d09048500d03046030b181c8c40d51071304011404038541441011445440500900b40882c80c2008011045110410949031340c065200040001407c0c203c401172840d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 697860476 1250 697859226 697859233
    0x6090614070803070c0204050907030308071209060e0106060915020712060b030d020318010c020604031209180c0318030c0206090f060c010e01061205060103081b0a061a040902150d02070b0108 84
    0x1c5e40108801c0e50301c09001c0d4030164200c0e010600100344e00103a050791203d228100301000340c3c15100b4960051450b0354020740101e292030141ca140f510103402040848a1954a540803162203032503040212032002113040160348020010000a43e6a12203c0d0b140c0c1d014410000305100c1810210303040141d00d00b01680107070000501250007001c003c504002040c4e0078a8441c07007501003a40854424801c5002c080d10303401a80e003207403481c1842801c40c50058200c85036106042000684c0d5100640081d486803c08a030030606002405040030898604498140c0c0c0d9061120126409205c4154481c0248a801c01030307040c95100d0303e444100080844a405d10000039165401100175803c540d165040a800001c01c0c410310404500000b03031050640760402d4045546800b1745140d90814519187d07151a24055580242d041c080c84d40c1c006600501e603002e03c8074803017810b0b8003000704450000500031750150b010b058800c02d145220b0003800d20800000e0380149001c0d80f50302c6000a40700700340d200e11450f92 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 697861726 1250 697860476 697860497
    0x3041509081b090a11030103060905010b21060f0601020a06110c1b09070c2d0c090c1d1005090d060e0a06200a1b0c08071703040609061407080307 64
    0xb0503201031507000c2c8040c0800c101c0c4940c05c0c41c054140348010300c4040c3c000c6031074500b80717818850290b0000c1203007240240100c2e440c2d4910703401100c00e00c00d030b110118251300503507000404036020022030900c50320b4140d01500307001d0940d599403402811505070100c44910706025100c002071007004803111499201a44030903900e01041001880b00c4002c1464040280b04408040081d00c0021504201d102e051200c03074521000091000007a0a9910301a04d10181c0e0000058240b1256000061003840c9940b43c910029000f5843c0b0034210502c0e040380d8101c21041404038085100d04040d11001c10010581e442207901a143d10f801d56991850040e41600008144002c04c0058403030030030400d101c1d01c04a214440c2802d02c240c2c1e00e014181060090002a241c84045107d600c3d058040c501d500ca028460000c1c1c6030b4500558a0320140922495855440714401b001030001054504450300340d035800b5030b0f450804d1422a52000f010041c0d0245803003d2100c0303070015002c840614800c203001d40c2c4519249 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 697862976 1250 697861726 697861729
    0x30c0703061104050f130b04181101140f07110d350301090b01110f0601060f0503060916020703210305010e191d011a0102150903041509081b 62
    0x4030451248062900e804010400c45505d0755029000d2400040301c00c04a5114021007910103090301c00c032480d40c05840e00c208036803000002ca00100c0214054403415098080795001900d02d011a203c2c07188443c00188220408a00020010140d045c800c0740550313403421080c0b000c10120003040c04201d0300204180c20840d5841c05903502039a18102c0d203540314000001049a030105440103018280300580c86d0031581d003550740100703116a45d021030364084500311044000b40c1d41d04c40300e0a019020001d00007000020809220708240d03030042034020250302c1192039041d40050039079012100d071400e50107882c0000000c9080446a001c8400b0342c203125840821200350020308440d8141c00c0080c0e0f4100703c0040c0042203800f0319100c1c420700503800000940b6400e4221481c1540c5026040e6080396081c80400c440c50000040550110703402a0201c6e81c031199010b80300c09203001c084400c891554018001040107981c800c00066041c4850b0520028441c2c0b44e24806082406806000d035032441421142c000a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 697864226 1250 697862976 697862981
    0x150909040515101a180d0b0406060801020711061b1501060801061119110d080d05060909030a0e1302070302010213060201020a020a150f02040321030b1c03030905030c070306 76
    0x104403c106940c80741410140c010300900900c1c5035200c810000880c501550103582080b2034120341e001804050b80f00c40a00c0d1911a40e401150110b44403030a0400024002905009580c54154000020b0345040a280d051229079040901440c034101c1c5c210a0301301111a00344001401000d030f40c588020b0f11760500d0f00c09409201d060307214000300085445c400c040c005011500e816440001110b44941300c45904008142d0001c0ba0710303803513001200c0420f01080140c04001048403180300700b001d00003aa204010400c84031422100e1324020b410801140890030710a50616200b1200245012195209404054126046890114090703036000820091404042011000403c06031000758680010718100940b120010341c00200b186a03401c480308003000c0d96400c5080490400760085440326502c1c2802e081861003980301c0c04143c8140c040a0416078801d01402114100180c440521400c14480c2c0380c000e908441c50070703070070503659088000024100380001d00b40400d440300100b0741d850950400c2000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 697865476 1250 697864226 697864231
    0x207031707261005090a09020109080d08190e031234030b270601090f050a03121206030b0106020c030325020d050f01020a120e0c150909040515 63
    0x14003030700880ca00b140d01e48426203a0440350110746554020b49500c00303441200145134100950003442c03402001142c040d80c0d071040c034115000740c0e26818140d40e41c188061f110030a80c2c000b6000113024800141102c40c140034840205150484005010f200c14401503017950440ca0361407521126050a010001d01c0c8004240e000a41908402c9606000500c01c0c0c82130109100343c3c4000c1c10b03160441000039589503020000200e031400c2083c0461401d2245005540700115500c60200e000005c002c00c200c0303103c0300018181c501c060280d02c0300310705580b00e55120a0907241c0103001c0000100002003a0303100341c000c42c8019886101c1e05aa194108071000c2e00300341c520500d45000390710501c01c075403080501e040012224100c02c514281c1c0301055001140100c00c0e1048060a184507d0006a00a800c15401131144411072b03602e90784403107845004401581c4c0f21415030380907035000074101c20681c03504500450282c002c0014a5140100c1c031004111480c03400c4809982d6504444000c19252000d4001d090713 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 697866726 1250 697865476 697865491
    0x141305070e1e030a1e050303040605010f0b0715020f0d1b020105180309040e120705030a030b010906081b0d060f080d08160e0d06051501030e0c0a0b1c02070317 70
    0x100b451106601013596100c0a40025043c81c1d914049001744682a0400014480e0000f05881e82d030319181c10164040d200078818a825600e10400000e0702842110588030040d920000c143d00762103000031500b02a4001400c1a10807610030000140e0144140c410035071101c2c010300a6a2000810300006070031510001c083d12a0b40020b041e000da002240402140c0740b907070040b98006240c00e0321010b03c1c0c0c50120380346001100104005010400e104000024000d02c16640d0b506200c4c54034114011240014140300e05004240f0b40f1020800401c40504100102c0600d00844c9050416a0700c1009c1610020350011401381c0310001c06014400c402d10102c3c2c101606402c0255203400d100c1c3d03e83c055102c101100204101c0005965441e039503c010309644c055401610611060818211203803404c450020074a01007032900402d400c02c040d001c181021a1400104884002490b041800003c2d81c00710b5950002c806440c0041c141030b41040c40034104650184c0c0e5060510207103002007601e03c45001e0402c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 697867976 1250 697866726 697866769
    0x30503073b040c0206011206020f041d0114101409150a0c050c0a03050616110703140c03010917090a1508010513020903060c0c01020c0d0216170304141305070e 70
    0x1402100c04000900c1f0080da8030820051341c1c3c1c00700d5800c10800f40207541000140f55801140e150210321140030301e506880389000c0c842a81001241040b9218a08126880208041420100c03000082001420f01c0410181004c1c1c5860300360305a0320642ea110248443c04035621003828001e003e401c102e02c0d110200d0584050700c9007820f640b03d403a5501da0003000039042012014054003d54130800c1c000864611500440d120180c80c0d03e0440070341e203441c0302e50000c14070441d0f0b03c0d076003146414041c4034070b01c54211340080c5400c08003101e001c0d081e030301880b55103422890031600000c203020802000c8c06064010740e10b034400355043c8030801c90003e01d140c007106002d500602407420181c2e80420503e4000280c15501c03a5101705203101e0714003900600900d0016130044003502c100c9142c01003190302038140d900c4251094a0b44400314154826030301100c0d8040d550090000f40b0042240c0004e5030400f000c01072946622601203214001510000c07209000001c6694121a200b810f000d070070b44c0e00c81c0c000755904 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 697869226 1250 697867976 697867979
    0x30207050d0e0d240c180e091e0106090b04020a1706010203130e07020d0c0b130303110304030c050607110a0b0a0204320105031e06060903010e01050f010f03030503073b040c020601 79
    0x1a0781031b02c078160098580d034081c2240801c0550304100304408112040300d9000410000741020303070303000700154031480c0003060400212144500c1c140c421282c03811095200c00311041c59280b9400456000244100c0c1075100030058812410308007050725000309291003031006140b8202d01300070300b8403080340e007084180320000240800150110a04d10303440800500b214840074460f0401720080d2007000e80da00742c843e42c00802e03c02419404820910320b42d00a030202c41841e2182401180d084104802c40701c0c464000130308410000303100c2c40c1e00e6604404000d034091b0401c0d031101d254441da040c0c038501c2865401018680300542c10716801a292203060242040d41c214038114011000780c01206644992001cae00800007891540c455095620080018008000001103564400c8c0244030075610708200448510000170b03141c61248905c02526031550383c003410b5443e401030a40341040d2811902002460f03001d003544000d20681e039440c01c00115915540c0103c80f0901c2800304681092100c80b0454008000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 697870476 1250 697869226 697869257
    0xd0b04110301060207060807140c060f061203160f0c151404060e04050901061509090e060c22030501090c0314012a140307050705060106030207050d0e0d240c 69
    0xc0d85c03000c035840f6042c10031051356500703c1114201c091240801c50349070041400c0d4481d460000307980e0310600c2415951100c0b83c40d020108003905941e591142c105a004010f501400810300008004070b074442c80750345882040c1c40d0750b20040d040244c0c011006240300c02a0038a815540082c1c401c94207404500385900d0701d410301c0c00051100c0c100e4102e441c041c0e0b440b540800c6600500754001c80081070600c6c4034040c1c06060741002042c4a103070307120f030800840c1402e00c003034504400410403d0048402c078807000d18000d003481d5018203202d141c200b42d034035404040c41d001000c00d000703025030313894035100c1e20f45441c0e00da05529240901407100303520052940e1401d8030118002c245801c900351241d0030850201c2e00c403190f51008498072003403601161040c0303c0c04000c1c440020740010140694030710450a83d40c0d00c2e1389401c0100c0490040c080043c1103a804030b01055401400341035548031208018014120004058a41c1420244865840100c0400c0c1110040e4103200502c128040e0b41060700c6c4c28107841e501c804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 697871726 1250 697870476 697870483
    0xc0c061421071704150905031c06090e0f030304030c1a0108060f090102070317060d060e010e0c030d0c0825030f180e0402040c0207081b190b030f070e03030d0b041103010602 76
    0x50584007558481c0b06e5800e0050810548050650b15048a14001c8100c0c0d00079015240d42e2065450490409460300c1c02d004000c1540300700d4035a004015400d40d40c40381c034112030802e5090b1080c0c68030400404885030191041844602821105004080c1800c1401c55406213440040050149900c14842a80000c0d803040030110724851304184402c440e00c0705000603c400200f10001410740d841c121804045003019040303507500d512581c056444100a520505480300e47d500100d200066022416400241400c0082e0402c00711400c003030a403450340c2c041c0c00d0050741140001580414500152040f100d1342c007921902c1c00307111040003e1030961a1159008030004043c2009100d19100c1a198000e00d20801c0650010526001180d07a5004c0000c07401744400201d49140380280c04498081004c0c0c2803c03401031080b0341034031900c0d510310360ba201d40c0b5003116000640460100034041e510506c407a039080015001010201100054102d040c070700308001c8901190411300c0f185420300041103260f4011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 697872976 1250 697871726 697871753
    0xf04030c05040b061608160f0203060a0203010e0a0510210b0c040f060507082803050a0216030c0302010b0306190b0901080a03050d060819060b010c0c061421071704 72
    0x4036005505d0b819241401c01806586980c203074107600131100005000e011480d1000c000c0c000d505858854480000c000d099220034054501264035001c0840d00c8c20205030310043d40160507111242805441e14050085048511141c0403441501c2840034180480088020782181c1c9510165280c40e03d40704451910160f10f2290380280803000c070303d000501112008486000d0b1041d2003070000e04151000300c81a1042004140000a23380300000d06030010b10300c2190300940004080c1e0f01e04408568007140c51001d500c200701c0440d500c44e074003002107480c1080f02078041c80007110340013080740110640c1400c655500106901c100b0001004100d440e50128048101e140c051500a6032200b20103104005029154080c031020b100d101c034401c0312130524000d84209140b050340244818454080115115910301c8000341004030814000c01034a809641034400c1b00d5003c0701418106001c0c03200349461031280c04200c0d0340d0300140b88200a4055405201519520070000401c1c1c031a090a441e01405150700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 697874226 1250 697872976 697872997
    0x80f0c0313031106040b091b090c0708090303040303350103020d0f15050910020304170304170a02012a09090f060b13080f03210a0605060c010603020108070e1f140f04030c05040b06 79
    0x2942c8413301640a08070b54125070064204d958842d542e10303008100c04402046c8880e2515a10311541d01c0c500007000050b03086099a07104200c030390840e0204286c40d0400c0108880e11509140c00400048580b20000c02640c41304d240080c0c51720340104001c1c1409031230704402c807a05204108000002c0c4819070381f03181e00e4803081d400c15102e0351240b90881401400d05094009640046443c200050741508990440e40381d0852006c0200c00c0034441504041c0d12412040c041041c1703810601c0b00c0c41240d0300c02060a0800c4c80c0201e00f00340d0303030100350103141d01602c5890074941c6010700a101e06c4200b000304800320300164008600d0b054a00159400400784003203c4000b101002c4042040c03110540c1000014080041040e680c515140b00c0c4c0c40d0080c030305440100e0105240304c000074810350240308001507440000c0c243c152484680300b03441100b0002d82140405006034980d50701a901c08600140c58522041c3c1c1c0002d65135811070412100e0901e850b03210074810380c14031001000a895600075180f11081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 697875476 1250 697874226 697874251
    0x20d0206150103110705160509010b120705300c0406050d0b010504030b250801060e062107050309010608010b0607030e03070306051501080f0c0313031106040b091b09 73
    0x21100120f010340b8140c4501c122a00d000300d00b40c0140305003c100c00c2c41244040401030030041c0d0f141c2c248001c01d602441041c030007200c04d01404e84418040005180e0040e407614009103804654156203c05a0400c03443e418080b060300c0c0c840900d03203180031200e6000b231080c42805040030300c0c08900030800d10800c441c008441b07072200f04118459008800750b40c09143d2008980c400b030302d081e5401d007151904000b51180c81c90000035200b0845070140c2d03a000c1c180e980da0754030480007100c20b1046c0242c83d401480c0b001184522100095031228410b0940e0707001c0d112594845170f40b0704103207031003500307407055134000c0305041e40350124100d510b68962003107582c2d44c2c0c0c0c5030402a00c2c003528440024181103460740064040d504160402000d08091010005410400d80702d4100ca5101c20082d100d00c10001c443c00403000d4020408140122008035440390418403a181005104c0e80c41261181000000e071011600c040c640710500084020520410405004c041c0140340025441c60000c1c0c4d620101605070b058405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 697876726 1250 697875476 697875511
    0x906061e0708043308160c02060f0c031b240a0b09010f0f0806060a171c030c03062c0c070618300e0609120a02090106020d0206 56
    0x1607100309a0b00248407002607209142042e128000d014882040070407162004c844404814a001d00740fa07a0140310710f41c1080340c102d900d0360019502d862414100303031380c0100705114500c40119410000c01a410f0382d100a141c480701d03100d0750070901c0450411400d8603030b000390b200038000b03a8041c4101400507161407803280301c6494080a0500a0a900d9466600221108008a6840310604401e4201c61601d014104541e0b0390b00407980d151072040d101d0fa540626030076010407440340824407003201030502c141956105030000e2184a040c0d0341003030007000403d46503451414650741500c145401404c1031145c000082c161a591040402e2002c03082030181250000864107012490041c2d1710307070701e500c84e00422040c03040071a1002c51100c00c0c42d00b07c40c0070b02e02c0480750041e0411890700c5070302c2c8041050910070b80110707403800307581560405940640001c2d007409207040640d0344200d00385804440101501c5c43c010705005004c00c1d400c058026105540c071082c01541c40c9a80010519802400d46620f0030590 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 697877976 1250 697876726 697876733
    0x30c030909050f040c062d0509030a060609060e06060702010f02190311010614030304180f02040b0705070602030c070504180209010e0a0b0d0b0a05100314010b0906061e07 75
    0x1a05140c1000c0107203442c040c104202c42c81d44001241c06240a0680462850baa8180480b181840301000d800c045004840f05440b1400501c0c1400b020340485c140141401090004a46440302c40302c0244c5240c0c3c3c603850200410151841040045d01c40306102d204685003d50120395580300e040802410050280e06d00c8600510a002b03100c040c0e08080d4000030910503030f08000f0b0072130003110100c001a501c0c080d030004603c10840d5025500c4400580a1801d00d4a084e00ea034503034400304100007400399180d0b4840d0062080c6440180b016041003d401d6480f081c20b428168540303041074200704259401044043c01d410700000740f003022180102d5002c10700008046090396018548600203401600c05000414420b03410320f1418407a04c0c1044041106c94101c00801202031081a4040d02e40c4e95480b011170411045600070540c00300c0074000703d01c183c0c2d60f203983c2c00c904164803042c50b0a0a0b551420030324100e1901b518403640002e030031150f06082205840c0c20034038000e804c4c82c500b002c0300b40014552040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 697879226 1250 697877976 697877987
    0xb1b010b030f010c02010b0306160c0602090306070309030e100516060207080705070303021204060807030b120a080408240106050705101404020a060c0302100c11070807140306070c030c03 82
    0x34400090700355280d00016005180c0641820a41c84015509000b882421403d00058491050101005124680c0c0240700c055442642c00702d4141c40f40b80e020004115607403010010f01b805450681e80000703411302c0d14140204448001d100c02d0f441419000782d02980a5801429600941503980440303c1000e0b041c40c142000340f02c2d0a00003880c103007010440034280003000c669903080f41c0c0070303400342d4500c0300d8064840000c0340718070300444010070545000702c3c1c0c82d03900c01d44c050504050054440d40240341100d410520349a48000b04031090310001400740f10061f07040c030102400e1352200c1b4501c3c0380c61240401c440c20400c8140581c1040280100c0c2e10801d1203010003c0080c0e003041c50800b0040d5001740e4041c6140c022089805034001c0029540000307002c2e124400c080d0005070580c0c0507040d4240310031880f40240003001007100c00c00261603d00141c440c410301c94240109030f0080205106803801240c0180640140340d610311039046002045601600030300c51a240f264185082502c101c55444c007680c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 697880476 1250 697879226 697879241
    0xe010302160b0c220819030e0612040627020d050c120607021b090f09100c09080f1207260408060414061b070c09050f1608010b1b01 58
    0x8040d02c60051001400c0b9000080070001001d1030201c8802c2e001c52032051009401c0d20030410705e90f02030031003644140070644210ba4454440e1800f280d1a1700c2940014100341c01220130b004c1158016014002080010712580c824080c02010405508800c0000100100360480004c0c0c01032400c07022a50800c2000d01c10000c0c20f51000303140440c424141181d481e5076800c1160310b0400b5104882e58800c003807124070f04111182d0001400c0d464207681c0e0410020f40c640015254000358410110318414a00490045072607042d0950b41d00c0c0380300762500340071505d040451840d0030400d170040041150326458080c02c58241f5038001c0c0c9000c0d0030346802e151050403040302d0705c01400f1880012070003094802010810900450140c07000b144965070482e001a2030b03207425203407101e03001e1411040021850101c401b61170000e006406c0d070f07050150f4890100c41501d80c2201c20000558940f0108024204090001084071003c2e1810800c0c40d810b02c0c121040d181724032890802481d000c4c2c0c1007940300c20b03825081541c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 697881726 1250 697880476 697880483
    0x20c2808030406051209070f0506070c1703071109070512190606210501080c010f020c03010501080d0210090302190f0609120909090b0703150e04051f0c0e01030216 72
    0x90b0395642d12003006200313420841e0380002880380f602c0030496803140082c0c5103094806140032018154544010042941c0c0050304c1160490890721000410010116200e084004010065980c69095185c42c1c50240e2040c0d9030244604c540b0310a00003180d500105a5414160302805003145481d0040e100f08604c0f080804006064100300b00400d40c50342c00034903c0544410a4a05825200c1c0e020280702519401d00481049038440c100d00d0072039612a4405240c0010940152414100310341d0119082d9130090300400c003140d00a40019804a504000340d64078042e0b651404c100c4401c06030b4000f902c50b103c00c56a0b8141e0505000e000301800b5900412610146e40700d542000840c40510300141760041c4004a0300c0807d042442c002081401030080c4002c0d15070200751032040e50b8801e81b05500802d441903a03620a85034200001c103020200c400070728001da006400034412214003e0030034900604502041107041e00707026480407850b130410a07401c02c1c603030242009600c0d901500504040b080003444042d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 697882976 1250 697881726 697881733
    0xf0102071802041a09010e10050409020403290702100b21070f050a180f060807060c1209030b0628060905030c0301020901141c02031e0601020c2808 65
    0x11840281e940e00600440b2020400007903500c40700209602180150b04105003c50848002c103102e078a00402d055801026504026007010f480398040b4040740c006400c1160450b542a440503030f924154020242c00e00032243c021545460018402074599000780c81b5040050346a050780002d03543c6105910400052503040e0080140303010940d07070b0361003200c0d109000749510341c0440821300d0300b0400c061a003038601804030b210ba03c2c8100c1d0707080001000c02075070701002c0503a20103010602c51024446880113199669900990b0500ca04210742540500e15106e014008900000c0000401880040d58400d0089900d44044400b545489182142010184043c8a800f0308046691034002104605035031040c0c08417140c3d4141c3c8000d0500300e1081c49001d5011602c075031050400d6851181c010400802030b181040c488400e0a0344241c10307600155900700c07100707aa49245000c4c81d441280e44135070100c1e0901c003c1080c903240d440420161009038441441030850619076448481054514500901c502c004070b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 697884226 1250 697882976 697883009
    0x31707020c0406060e030a0b093d0605090118240e09010507051903090b07050304030e0d0b070c020a03052b080105010207090b2d0315090c0f010207 65
    0xd4486001c480c03070781e00c038500d80000403c010384100100d684205018008014903c0e07192a01c0702c024500a003e846640700310031000d0600200004d01c080e040000703070003a241d14486080c0418907034450040e8040103602c1d04404000666820150904440c0b8954a00310210040c03129003014180081c114107500606218a80507040078a1059085940b081b00c065410f440d50003c903400c0e58070580f0701c0d5000403801d2018200000c6a54900d240d0310380305080c001102205030baa11150f0810450306070010450103c04c001c18580c011103142d1070204110351071180800c0558601c0d00c0ca4201800b42c2c0708002022100342c0c00c64413804a07001c09190450100ca0106c84c03400016492082d040e51061725440040400c0700925004001d02c0d8181d0380c1c160081c1020740e0400b91000300403c0004009984140075492402c0c495001d5104040c0c3c502c000c400500c0c55520090906140810401003001042e0100c01001101d032004540070700d80203c1107410305600f81c20712004034508a0345800c00f210b061400f208 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 697885476 1250 697884226 697884241
    0x250c05031314040b040212070f2c12010b0904080918090a020312070b0114010c060e161401050301030b0a09050d02150601080402010507260a0504050f04091e0317 71
    0x9000c01031080845081c0002c001e1132003480145e0045e101c0344049400780c1130100355602c0c064085549603c0c01450030824400e040d011020f90029027001461203901840390780e00b0641400c809200050241600a0111000e00c04c08170710300e0140140040c1c9040404132b1410550741d40c04c46400200c0e02d000750700040a0615a40b202d48489940100b01d10900c1400f8000f05410315076401c0c0d85061b0f80285169816a180c407420b103507402d00708801241040354603508000060860300c6006445010039005080581e100d440160190701c00785c1212001c0c03044410005410303a8020203e0381500d50108001d0016100e0b20740c510007611641030000c001d4080c4030056603005500090302c10f80c2442400e2003100302c1d200d500064407080d40c16140a03000a00401080000c211a4202407069104042500c1600303216000c0ca0300241c0c0104a11400080f40010108000d15144090013094581140c081000b602c20f503407510700746288240d0043d200d1b00070300004010706004018032400483c1c0c8104c400c183e0301d0240c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 697886726 1250 697885476 697885499
    0x160501050105031015144015050402070602040b070b0f0609040c12020f030d260105090631050105040c0f120213050a030302010203010e250c050313 65
    0x2601d029108003e202c0c0c01e890074034013600e9403034000084104d00d01820803015003c00e8825016064120707550801038610313500740f030ba5013880c400100c440051880030494011b0070340b507c4d06c080c80e0428504100c4000761622100c080401140c1c01110700507941c05a40c5000c04c040c2c02580d001d003030401d41c08a01c1034148200051313500e00c12084208121404d1b954001004404141910081e01220307414106000c0e40512282100038580001c003200390244541000a1808548003012400540c80008040c0700303002d58242c89440c4151404103043e150306240c04074010360320044c1903a12030040b89010200c484c0d401c101b5220035a010a4084d0152012407004c24041c18080c401c0d107000d40d203042048000e0038480c0c400c00d0001d10003540d4100c03000c81c11036803d0020b5001165000040c80c050b100029842d03441240c05401103210b5000503840e580341c041c4c04000080b00614183c90800c0961080103c100c10703c0c0544006070703250405e8072801d449401c0c59440e5004e200056620320307107030000100748111b014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 697887976 1250 697886726 697886729
    0x111203010611210d0b0a06020c040b0a080d050703053f070f050904020409050109050f0f01060e010305191e05130b04060e010b060706060602011d0a14031605010501 72
    0x40d20707602030312540301551a58551005540800f0807400c00c5452048000b10b4005080c0f5901400c004254100d102d00004d540403242d84c4083c001d030f03100b5882091203040900914105507012103080c901d480c41c040354161108180064a010850001120020540940203030b41220428031000703512210000b41c0c0080c00380801c000c0d84e00d20b5000240c1d03000c161030b003101c01c0ae00c142d0300380d039500b944010b07070250517034407604500d0065600580902010840840da489818000d09942074041450700f01018031440200002d4104070b0000310140050007180d0700b21601e071041c00400e00e800207143c0c1d03601c0c1082c2c4151054000d03100c0f41c0c600f031401401902c1020b205800d41e48007008810085500c0341815a210b0704000c03070000f0700806410700051b01007405136003c3e00c0c000302503400124002c2c0c807101c0020030990014400721811680d6400070300005074244206a80d0f01485038000c2801c4c00d00107411543e0b0403094100408054034003120705481c040038029203013101080c190554500550b4a42140600401d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 697889226 1250 697887976 697887989
    0x100c050601031a0a050118090512070507050a09020910050c0703060c080609070914010c020a0b0a080906011203080f040c080304090f050f01030f030c05011503110108061012090311120301 82
    0x4a0001c513440261503c100ca0480360003044291401d50141c10080180461907001d0b900b50003500683c000c5070340360b40d00a00301684110060a80da50402d801c00203c41c0c6c1710b40000d1100c1e4414048100d054441840303280241c032071030900c0c584404109030b440d8a429025080108284c0c00c04c000448515049008240500d20454440b0000d0307031546007c50b00801c1510a42c01a0030b05031481d40540d5000e1100360001e00e0000c0c100e80c2e00c0a880b0082c0c2c01c01e6074807003405540014201010441d8030302040c40058054403160404464004840c0c50042031000d002d0b00f1021071465803008a4100842c844440004003482e90680b070f2940d581e0b100c4070b4001c1c02da140e840100c240c245000501005021200d10303050f20b03408200d000c064085038404480c4680584011a001e650b0b030100c0440018820500100030340c41080902400c0361b110f00010425440508550300506c40c01c42c0c0d020f991500314206042d4142149000a02c101540c10100d80c050000d158800d5207008018081c2104001c3d240154180c0b0007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 697890476 1250 697889226 697889273
    0x80903010b18071202070506010807060207060203131716060305072015090304180b040b0907080406020319110a0201150f0b1b010c0f02250302100c05060103 69
    0x78018144582840c207192040c080802c01c500281c29603000301815000341900030401420401d42e40d5444d80380c0442a08a07048507444004200f0100343c2c100000c6018000b1480514107104050681440104150284842203541940c1e00081d140e000c20a001c0c82081a01d11514080d070b4606020380106000d4034102d002900500d00524054111502000300e201010700920035005002c000124110000d0709111090008210000391508400180c060f225104840000c0001e4150104801c50b407800c100103001d0181d0700200020203401c80d1400d68000c3d0003110141c2e60380c4e9100c1a401402403565007a407902c40ca0114100075084c0e40002424040f641d40d002000900c0d0307095840860703000c0d01d1107100a0420200c40510443d946440a009826020043d02802e03203e244a2142961a000c1030400010700d0a0340028074140d0420401c0c2e0041c2024242450700881c0c0c140348003c8040314000a4000c410140900107a58441c0200003842c130342000c213079140340d40c50740343c858100600108125030541 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 697891726 1250 697890476 697890491
    0x60b1e0a090e03030a09030c1205040504060e07050901120b03031c0509060405332a09030a02011b0c15081f14030a020415180b0a03080d1808090301 65
    0x10182c8107228040741c00310010340c11aa070791100100549160358040b810003090043d558001001240c800480070804c1d15402e40303e5090800f404102d60003a8881203070200d18505102040d40c0280860f2200642840c0001c007840700d150803680a006d051001640500c000200a075442131108003066060103c808140603d0700c070164003560701e0b0400d46010b0184c1d00b18948000f9006803007424102c48072a0f6840e11a0301106840e64011032238001c940d880305c040b661000250101c0241070a070700009603002100f0341842c0103400426900c442c480c0009051042c1109203c078451a004401e114241d441541190090340320200c0d1441341d5065144d1002198a00c00801d8011a10304400400d03c2140c50310301d502140340c110700e01640c1c8100c440b61509401000c400401503207680c014241020910340001502c02c1c03078a0803045034103074102c03000003401e468140a4100c07030b030340c41380798200b200d1f0014401d40c0c5032414240706000822072021f55056030310030082c2c400c040240c903501610081030210001c02884 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 697892976 1250 697891726 697891739
    0x9150307180909050f030a0e31020a0f0201090305030613060e01090204050a09200d140406150f08060a0506060d1815050f07030203281512050c0d060b1e0a 68
    0x2405074035001c07008100741d03111101127420071050950001341c141c8801c40c1006454002220350181840c040b503800307074000034100509504600140864800ca02c020000d01c8403586004041d07000203894a4403804103031540352001e0710305421040203000c560441c6109540c1d60391416000b58021320070140601c1042d00c0007d9061198407500c0000443c0c458942840d48540031410310030f13800101e0030698240d40c0d106040c20300320b00d031100b588034606c02c00c4000f854075034290400042c484c8981c848203103040240c8043c8842e010100da900d800c0704c0107410111b900c2d12080e00054650145c2c000c1140c00300d01d009031181c030100c541181c0b5a1628090825000502d007000362001c00c0c1c0c0d00c200d40002d012200c4a01082c000351180d40290b41c0643e4480f45407803403032a000c0400e072051401003e0340c581a0b03180c40c07a03d1024441c00c00d060000b400e030401c2e20303400c8070305954886403a212080c080340c0c4202d02d8400c004007803083e5508030350307038060340180748520309103070a004400400500480c1d88e010310800c1c400403410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 697894226 1250 697892976 697892983
    0x31216020f060c03011202010302041814010503010b01140a0e130f060e042105130e01182a0528020705030d0c062007081c0209150307180909050f 64
    0x500e04000c00b03c0e107568201500c40c009400459001c0741056070807c80004c600c54003482203c090910079002040c0074034110b040500064041e0032142c0300e0b074176191750301400340c1c1c10614400001404e1040180c81705035a2000b0703544180d02e00350064210347d0310083c0c40407142c41c562042c2001007851030200941c0380c44060a01c0600001c440060070100e10420410110111901040341c1e21020701d455450a40c0b01250a181052240d201c80b408800c3c0300010301c24151443d50386041c03021160410403d0514840282a03228000300a42810401c49090354144c1480b82c005c458000c4481801c1d401101c0481400980a03100d440b517000c014001e851000c50702d407a0100d11201c80c00c1c6641d64545034900140c07112001072046c4125070342503000c408a0382400c1502440038007a02409114178645a00e00074040b80c501c00b403101d0004204500c1042240002e540721070b400c8840c0100c40c0c43e499143e544801050b1140c20852a101c4030114900d040050220203d4220b522100d201340f0641b0005210022403641c3e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 697895476 1250 697894226 697894231
    0x1050a05070906050c101a0f060901140d0e1504050c0109050303030a023f070c02030a03050307020109050105040b1008150c070507180203010e010510120e031216020f06 74
    0x307041c80300204442482100030b04000d10900d415071b4101d20000040760200c40c1d924070f4401b40103466081e208450300c0c00e04072960000f20107690140c500130302140002c0c60209200035000c084000420700680c0b80c030f071651042c0c0807011030004640703155074506483d400020040707504442c1445140c0c82e010702c5511850110048400280065055803502c045540c0690088916021a0421040c0803e204d041201c1e500042c540464074654540c841c1e0300000c007151800501300300c14041e600480100580b4001a040d15080d018901103469807103110f0224003401564101a1a940c208010702050210600c2a41e0140b58940c07107080d034441d5a0000a41c9402e0481d68222a0640100000d040c03100c080005101042c4201c0c1036800c00d0340c03502106400c02c03044142665140703501000600910003217170300b014090981140e1001603072a440d00b00030725001701c0c1030306c82d1610313a03c0d1404082005404c00a58443d01940c0d0508240c41c0f41c071aa1503401400e81e580480014401e580c810104420080340303250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 697896726 1250 697895476 697895491
    0x1201020711090601030e1606090f080705060906091201270305160f02060a020c090c07111003060b0c0c1e030a030521090c03071a0a1404052101050a05 66
    0x810007105401c120485200030003150503d0340314454101e0b4080248045a83d400c040d03821010103500b0700000034140380503a0002c01c440811800706016083c1c00007031a4080318021221a40e40350065004110740d8042c0444007078102200080c50011907506410070007034061204010f0210211044100c0902d00100d0ba020380412402c012002d480d802c602403092155000d5408200c108045078040b5015134041c011620042c0c022401050701c4c1c0c0380c0710300c80f02d802c5514808000d08103000398a50690900d0010344242c410040c200207469241e000ea0080300080c10a8010b42d602c07803071007c5101d511126035a012921410b4045100d403400048451010181c2c4c1020340204280c83c400d582c161640da02010548035021508200d0b82c400b10307142454544502502d50242000a2648050600c1c00160b60040200c5000c16840000c21410000545820340c8051030080d007240c03480f40c03052019100d61f421583d00010441c2e03004181da08000c250111050010000f00503030380d1240c40701c20403160241c1351103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 697897976 1250 697896726 697896743
    0x609020c280b0603010212040807061107150203070210020a09090605060c030f0a050f16020f090f15011e030501030b090c06071104020928080309030601090c0216031112010207 77
    0x400850108948583e108401900051500c0009070450401078001c4030103c0b400b000c000756000401c03089000e803003ca40c140b520040c0c103000d210750b220030341c0c41d01c142d104069943e400b00c0080e101c5c9108100c00594500040401c650321301100d82d0003440c207000f40c0141c40300541001d40010b03140c00d144086407010204040a03500f4000e00042c80c2c43c150780440d9a07042000414040d0502c0031030301070000d0040340c40600544116502920500848a48401015200b244418100310442180080b825805600744900e641c0718103034030380181c0d5070710081d900003540e07561a403402d0078280d074043d0b100d603058078040c0c03150044c256150a0402e03a01d01910903150b81140060003103100240c20001002d00b1070400030005030800b041c80000c2149a902da0010010141d02451100406e01c0b00380c0e4100c01412100703010758503000200003c02d90b0ba40d818440e0440e1b240c2d40300c5090400510a229034400e01e1044503890300e0303140c0c0d00d003031510302d00920000e010710400c41d07440420002c420510032103025035440303240f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 697899226 1250 697897976 697898053
    0x70f0e0c07020121060801051605180f0a090203180c1005090904020f060313140706021509150903040302030c010507030c020d1b030b04060c030b01021f0605040609020c 74
    0x1100c0c1340d03540d000540c4103070400412400142c60640a080c2c080d1a910000040c45e10b03120300f04407024440e584411003808020400040c012a00105400e0320141c1a5082c14905010b0800304038074008951100c00307094804014042d203d0169110710028500100c212840040c0c00e40405ca4041b0740d8000002c0411801c1041140500b840c5d40300907400390009003030b0111150341c0800305441d64001c071443c46419074410040d80030016000f00d0450f400d0309000041c000d148c00d000f0081c1d90707000c2214070203c0c6072180f600080c00300007040203150240000390113518020706040c918140d6035002404201d1182c040d82e2060312843d4450b00035030350403c1d0075588094032004c2c241c09101e0312400f01c94099660074940b0186003800182c6040260095200d2030099420b0314107428804210340c0c601401404050809a69030302ca60b078001180c4101d00d80d540f0007440450b000c5400007005281941c03205400500f00070f000140c16249501400050703003080140c0c3c200340c02107000c14040c414440003440420114009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 697900476 1250 697899226 697899229
    0x807030b0303090604180501140612061207030318050102010911040c020c030d020703060e010207020918160e0403083409180603140706050a0806010e1002070f0e0c0702 74
    0x3402000e07058038038060001011929560158102040c0c81c4101140031140c0c0c50380348602c5004140c0d0780c000100e44981c40001030710318842d407440403102088407008520590b48407120900b10724110f004590b56656a072401420309940004448041a221000040c5550060044290702075114464050714031002d01044000c1c58000361040841c030480040c401c00d030301c0800c00108072820030340040c1380c001d1462520005503010342c00c8054190740140701c10740c010b03140c2d009041e800110300c44040a0180d150701d50245048801c40c1c0810011107001c0f00040d800343d2076150b03940218040d60380c5840300e55650f10b0003000341c881100c68104040d2000c04d20080e080312303580b91001302107152900788099a45d903043c01c2d41c10118041d9407003c507036030f910b0b040080081e40030030140d5940603100540085481d2003000740290196010000602c00c41000254542e0310549407204150b80082c5000001045944000d6540001d8003034144110800070000c0340c641c00e20030381148a40c0c0310341c071010b11b082051703070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 697901726 1250 697900476 697900481
    0xa03060c0509031006080f03040e0610120504061e020306030c0f04020705060a020a090e2802071e02040b011d061b070b0a030f0603081210081b090c0a080703 69
    0x140d0300c20810009000c440c409550500003441101180d110200d445420311003a541130880b0307011040c503e40e00401c400c0100541104003a03030b22490403514a44004c46101d800e07035440d0100c03d03d0f045600e18060130041082210340c88a201c14211183e0207c4d010f4511074440100d100950305298564404080b0700443c0c0f070702940d80c06034604040c1000d810503145c0d40e40d081c501101565202502900801c4602d80c066010090500602420b01545402d040c2080d41e01650028000d101d41d681c5d001c440e4402c0f05590301c1e011070f59082c4c2e01c0940444021004180c911030101101400c80c400e509114009050798810094100b12030100c510640b8018480f40400410781d21061500104082805c10440f00010522400c002010600714480c0d548003440b0703005017190300c2c422848c181c00e0300e0100c0074404114080e042d00d2901102e10440441901c0e010072102c0c1c5004190b0080000d07200d000300000a09484400c2c0709840002661411299226019041402e000f18032003080062520400142118840d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 697902976 1250 697901726 697901741
    0x6010303080a06030203300729040803010909030203070807030806210c120712051f06060509101814130902060f0307030b102c010210020901140d0902011d0a0306 71
    0x5145d41d22107c50180c40103100b58000100984d100d1508228080641c201490118100340305402810003601c0c1554600034140010300944405644d50591a01014000c00484a000d904828002d480710058030b0f00520200c1c040752850b0081d9185601c0d0007035000b00d68051401d1150390806800c0c80354100d801c2c401d80c03641d15903541b038a5200d80180010094088503110040e103001d40040d0503094440d50048420584c5031611060091400b03100700034640c0d1010546542e40307401c40d41c42e2400c0c0c0706000b0884581440289812a203074070000006480c280d101e54007101c03800305a401030680e0640c90031140440b594a0b6010350000010000c0c1526070000e080290f9219886080001ea81119007010a40c0d0b05008800325000c00d03078a082003040e100d496440c42410b643c1045401041c4c40700100000c2d03c806101c00382c040c2c0c1580100d5013039540e0380544101002d24148040e02a1201c004000c40c401030a0705000c1a40403030100701e00050b540304902411800c170351025010584c07442c0780d50360381c0000f041c82 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 697904226 1250 697902976 697903033
    0x80a1b0305180411030a090b09030a020601030233091206042d291303021507021509030d0c0207230402120405010e0609030c0a060f0603080c06010303080a06030203 72
    0x6860720b482c1402d000101031740c02a981d10400080c032058a01e006000c0f2417014085103182d51090054105590340010703c0c90540e1390558904101ca85c20b501c420040140300300d40004103a817080c0380c45651050382400313821050002c4440c070354806003050741d0a03110300c02910064001d252512801e9a2150429170300c564a03101c5034003030a0f00c1030311500d803081c809003014074440860306610218000d489581148a0b004146804401d2004a15582c041e42c0e494052181c0c02103c048140000c800d03500a1102034968408112000558600882442d4a03580110407203107407545407908094001c0d00c0000c4c200241c0d0241000c40280d507520007a200d0800c00704903c11035216030200120340c04582c07241c83d814001c40c8928000302c5c256074046c0019080920007021103c80b5881401a100f91100c0020760060b0a80c1094002542c101c00351400f80207014140c0015214110001d00210f40e0748001032018100c1e4041c2d0b1380e0300f5654880d01d00d42010746c0d285200c0654076500268070b401e41c010740030b18864a0303d0705c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 697905476 1250 697904226 697904231
    0x20309041a0303160201030b060a0e0103151a0c1005010e0106140403150e060123060c01270308010b0307120209190f0303170403090e040f060603080a1b03051804 71
    0x80c5000040d1450380f0290a00d02400703080300c001c13811940c25004044c440c3d4401c0720050306010011038010051181d88140d94101511110043c030210358180020002d40310811080c600d610300c183c0311043c29031294002402e0351090209004000c1464403d080c180e0b075102201d500e850b40fa2501c102d1b00c569458100d2800e80c4010080080051120030400c0d00d010629000440e018900c0030410f800c0c013905a00404031010a0070501410850081a501c8201811031746141c0703c410340d015041c010f14203a00340c40300004100c940501e0b2107440c504c104e03007041e22a0303950031482c0c0e8031390421074100d01086c1c6481c408103a1061403680e142d1201d40107010354100c0607100c00081c4240f403203241c5205000d83e014084080e0701c14001d00516034454603c0481c06a901c0e01000301e82440d0754001d02c110b01d80d116081d20310341c9000c003160030032007600a5a01d00c00d4000100f0b0080580702c1c28050a207070310a03860000031409440040101c011280120007080341c00d03803030b003d00300000a86201289103000d51882c0d40035a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 697906726 1250 697905476 697905521
    0x50a0501113d0e0607120b03010e06090709060303121e06180608060c0f07171c1404170f070204060f1401090b0f0a11061e061002030904 60
    0x180548405602c88201c180b100e42c080540101c0c1c00b00d802d00c1a921400100d003003100e03040c000d140000c0c001c1e400a9031494030100821000315200c0003002c044005c6a4154245080000c1100700001d441e4084d103a070b0f10583d29800d60703c0402c07400b1900d03184001008500d00c0d8015001071511a402094807807100406034201240c5d40c6e620104a908581003d01200c44000d80c0d00450110351140070050500c0c0c100901d01809c01d00e07003518190207010345600a000c400a0f003d02005003c03400400000110011551200c03c10380c100ca40c00000c4c036203058041c0703140c062140d51810301c6040080c02984c218003e00c031180c11913045038500c1d038000c4a1207035030300c20704100080050319544130f04802814400c0000d01900d04180c0100c00e08015031030118100b01d41220b0074042002030400305c034503241701c80000d19a078002c849025a10800c0c54040f40c9224054241000a40e18034041d6095800801882a05140d9150410009010561949800141d005108110040c1441d90006551108416501e6043d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 697907976 1250 697906726 697906753
    0x414070e01180302091806010618051005091804021008060d0b06011b03170a0203010605040b0901020132010504110403060e030403060510090b0d080d05130803240307050a050111 78
    0x81c40240c030808005c010040302060045003d207c00c602401807441c0038881c44000c1c0c121924500c0b100e004d072511806d1120303c01c1609502500841c1d442d00e201414500d02007040c140c1609444a04880a0340a400d00410a00c401c5101b508140e224400003048245088120344460388201001042c29050080407480c800b25141e01140601c2003d1007980c80d181000040350014503000300180045000600600040c803039160400c05480580d68444451900c902603100100d02402c44007090350400c00401e5034040c000c1802080215500d001c88481040e03c0e665941400103c401544c55220b040e5000c0c041400050f8298101000000340941181c0c1084d80381c0d02e50504503803007910302c0c071068000c0c0740c0100320b64049405071a41c02d040c101c0b20340017012101e4031524440c2c4100c05445a01c244d4680c00101a498840b800a000a400550064403454003680b0a0403c07103041407030340e0000e004001d40f01c50741c0c034000450f0f0090301c01c0601503800d03076403910005549a682c0e59400c0c104070b0082d04414240c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 697909226 1250 697907976 697907989
    0xa0f0608030c0c1e030d08040809060301090c030c1404090c090e090a0c0b120a050901021b0c01090b03010807030b0402031c02010b0901081531050106050414070e01180302 75
    0x480051802502c1d0141c045410081680d20400030303d04007410201c84c43d5903030340d004140340742034000f04d00700103090b40c0e9140340c030319210710445900c9c6600890100000c644c1e04002d601c58030042456403070402107510800da0680d160600481d80e4065504d003004140640101c0d600308030016880c03400c103c1c0e001600e40055481e900400c841c600c10691040ca070300c000380b02c0c40c4030002c8000c16444e20000d160072051000705004581c02400d0100c02920f0b070b404038104801c2541213804413220b8040902800c2c4080c60555103074100e0f21040342c00100310590103c1c6001c1c059084074100c0d503000d0003d10748246980c0d01c480c0450310050050368503009410b00245a2a44030b401c85032005034075400018020185000c1118511041c5c0081c0120f81c40038a041e0f03290035445200d16088110b00b4680809280c00d4180040c80303e943c0ca01450940021103420b00030450150824010f44c1da0449051111003481e9252843c2088102c60a00016200001380780295000d0740c84409180c2c0440032924489840790049901b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 697910476 1250 697909226 697909237
    0x204090f0203060c040305030a08061203030405061005010e0d0b090a0c030b01180203041115192d0212070f1202150a0506030703020f0612130606060305040b0a0f060803 74
    0x19030600840c41a01180380a22856610100301c0940508260441e2501903a07401303680010800d000c3c0d10808950255905440061048560001c807a5285880c4c07030456110740d030545540c0503100c03500301d0205441d13010300c04d0310001c020094036a18541c240c54807055840724003e040b030703811401459003200c0824484000d0201542c0940343c001580d52601310020340307045052840703480d40c0d0300c103006002c00110480003001ca0b841013110800d03100d035200044200a07100f110300e041d503164540c0041c4004550880118036003103507a000d9001010156140f003800c004c4400d0055001a0000d02d254030486a042000e00080d6025140403007000c01c140d13484240c604410700410025034084007802d90070300c103211036403a400020100140300600f08440829a22150f81c0402480b8030603035a0603a40544400e000d40e8411700103082d9410880c14251030110204441c4c0304107683d0305051400c081011802800b030503028603884070b61480c140e0b0710340020720018014034104074009620b401c00000d4500f0304201a08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 697911726 1250 697910476 697910483
    0x503060907030b0f070509061e0307030605010306171e0c03031204021e030723030d0e310515030a05030a11160b0a05120f010312021621020409 63
    0x41d00d2421410940349085009000d60000036810b0104880c0c1507004065409201c000e60b1f10781c0e02e81407082d0007840800030003940600303040804000c0100c0c655058000000320341c02a00c04001454403043c00908810701804c07100c6c616800245d02d10702401c210040c0410700810b00d8187ca801609400010707095038005105420311b0328106040c03000758600041610880034081c0710350030401008a001c25100d010340d1003820000e94082203804000c1c1410340d0f1160403110010241c980a002c0703a03001602e5403002e640201e0140340c0b241c004442c00a400110000d003100c040b41540041240c103548100500001030540c44100c000c070180299070385041140103035a83c8148065038442e050850f000702121944400440d1940c0040d41d0009401c1040854500f9200311000c190f94600d5000300a80d410b01c0ba620b8680da0070f143c08420058104a44072196059a10078141a20105241c0301c0032607562100c01500015400c45500403c001d5000b000c50915107407a0b0300704586c00c421075400107022030355248005c3c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 697912976 1250 697911726 697911733
    0x310020306121239070f080109020312030705090a3b1b0904090c050111070b031302040b0a061d060c0606010e01021f06140402120406090c030b0403050a021b130203040c05030609 78
    0x40c804c0b032948001b5030000c2c1c07000704000c00840c401d6400090788d034000003003000296040040440e410130710800c01c58002e510081c1002040c030f81c0d108002078900c2080903200080065034004203441404184a000420560000040e41c60311b6003030f01c452a4035190003034a81c200004002008240d00c0d54010610060f0051440ea15101c0c5031000250144191402d0310f00e564022030001d014030390b24481a20f400c084c6900c0358544c13400b03551020a00800840e442607a03c034000a00014025512000312000c0307000384280007241070071310b2060050754000d814044045801080c00074641e944a40f001010b00103051040303400c649200005606442c2c04030012070900e5458000620600305c0c400314024841c042035808505e0031002c0340c5e00072112000604002c20150b258505107043c0060700c81c14601540c1c1040d000c054508052601901c0c0394401c80000015008001c04600d0003548012400c00703240000e8400038000b07000c24048030080d80010011101c00350040c02c0400c00d80c5040100741c0c42495440000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 697914226 1250 697912976 697912979
    0xb251706010203030c120a0b0d051006050618010302090d2102071205060f07180905010e100807090b19030305041706070516020d02031002030612123907 67
    0x1810284002091141554030420510a00781000d000311841d086048000c0b4901d51904d0700500041e10203001007603408090034071294180400441c1001840e4001181004815902c0050012030300401000441e8413200014005995010b40c00405d02490300402c6400019550341d5003090800710050207040caa9101e0001040d80c0307404000c044c000c0c01c03d655864101001c15501e5030b644200050036024403a603840301050101c0e000b94035003406900320740400f10101d51a0142440188400d101d00e100f240d01350804960002440c601060540f21000081c0c00401c0c00c007860400030b0300d81c00c0c803401c5e000318007200d07039a01408810119902545c401e81d121940c4500d402c82c40712041207411110005c075004403060006281d009811204104500001040010842d000040701e00b02182c401a42500400109110f8210311313900462103042d046500920200e050501c2030758070409a05031420b400da04001384c400c415044000c02c00c00d403246460010300f03c20251424500f501e24161583c001c0d9100600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 697915476 1250 697914226 697914257
    0x4080d050a0f11030c160816150513020a0902030c040b04031401050f090d1202040b0a030606090b04050a030609020303130e06010201061a03060d0302011d0708010f05130b25 76
    0x43c0111405030303800101e0542c00e101d241c4103d280300c0c1c802e092045150141c0b080701008064816101c0c0800490503156403801c2c0c03414034080401c45600d84210103454400001e0a112a0300002c000d071303d4024000110090074460240c000754400b0b0081c090060041c400050148e41c58801440a14400d40400103200c9900c8001c5080d91401f91a041041c0b4542d400c1000794072001885c200d0200c4d052234403e8001070702000e41c4000348202c2c0c20020310100700003a070510454241d00202c0c1250303000d82c0d0340903180d41e5800400045004034050298400206003081000c10240c0e0071144d0a01d000509503440d001c0520444000e40d03102e54410b00c800e4210004010240d80c0a00c592402024140e94890300118404210122440300a2600c2e01c200c1820211409046c801d502c01c0036002c800d032081e5011140421111a581c1c0b01d1446960782d158286413500100f102c4034055103000f81051000c0c030a101c0001d90781d803d2440390082810701d8201d0882008011010b044131100400c0c00c6175100c4644207203220320b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 697916726 1250 697915476 697915481
    0xe1b0310090f060b0d060204080a0c06021209040213050319061505130518071214030414010c110907030501090c0e1e0d050d03020c06070801120204020304080d050a0f 73
    0xd9a4644461500c0d8a100202d030041615030441640114005442070034040080c42c3d8044d01500900313101d02c0844c001c200c1c484001a210344903070103200d9807400365980c1c9004903030320204940580389071801030226011900b403a8000d0301d000c04126039000d8260b074136080420301d0f091900c08038141c000c407004e10399400d0105170721400c86241030a4210511031070034a40850070108000d44040c0728a40d4501c00507082d03100c0341c45a0b400c0380c0300d554155100036642d0003460304000c81d21982902c00c90030010b13181000c00f800108075011074180d140030b51082c1010314015034402202000a0750980650403c16200b552100344052194001c5c1e00d00250f40e5050000440032625001c03401810f10184204556031580c4100110000d20403c84840d0240c09460021464200300c3c89002046071061903803051200342c058000d0007102c85c0410860b0042d580b400b604850750f09080c4034240c100110401000702504080e0025a4440d00a148883c40e0000807014081181c20403149070610b190f884e06120181d60302030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 697917976 1250 697916726 697916743
    0x15050f1e040b0d02030a1b1d01060c140618150609041407090f020a0e031b040f1503060209010806032b031113050310020f180a080a0510050115170702010e1b03 70
    0x100305811100d46000074a907234888103014203418003070000d0b00f003420000464240303034514900758140e8420342001e400d0407040120214070382c405c5000359000754100c0200c40c03811078842c94004007201f8094440d074070380c000012000000003c3c54019030380041504591402110107810f124800181c1d50201030500074401c40d11407540030300c0b07504070015210814440c011401d415803800c030350000b00820210020340003080d2029142e100054141030001c10b0010307a6001e080030300002c1e241e0100581d01c40381090b4a405100c941c84121400c040080a060440c0d030300c441e10b00d404241400218290842c011011a0300001d01a100580c2071401c01c2c0000d050610601e40c1c203603481c081c158280f60101d1340352a2180190200c0745508580300c80a1907155850314410001021003005443e500742e03103030a2494440c0c9811081c2d0100b41d0a040c00098054412004c2c200d2882056503403829072084400300c0c40f09244050300b010115920341582c8451a01300344024004200c1d0b540041c616103156100b03040c100340c0302 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 697919226 1250 697917976 697917989
    0x3080603122107030b0d0312050a0509030301090c1b2102060c090607051c05070c05030309010f030b040b03030c01150e0709030206071515050f1e040b0d02030a1b 71
    0x280004103071500c00d203000180b24000c40004420b140d079030040841c010142c0303110301c41e41304040d21802420301d0781007114181007200903002444980e50b0321881c0401c0d1030040c2c454032b80c40e900c10001004003100a50141c400f220391481e20142213911020703105410f40100c01e064510412115007020400c3c20b80302241c0110100d4000b501e000d1600d00c4d6031084a00640404034021000058140c04114040c404810f82010280307080384d03a20007141004007035404c03203081210510145400811245000002c4d40e00c1c0540c1655101c03218000307240b044014003511500d594101e41c4556014a02d0343e802c0c0040e1454010300000002c1c03201d12040c0c1603034418066445441d080041c40c0c240300030298401c9500066907010760b81e0329940c80c103914150703078903c5e14a04000620b51030510001042c04024800d50308541c8111299000b40c0040c10801610304040000c4460354106a410b5000c14101600803036446080100720800c000d2980c0c0110f03060154450003180d5080c20703a1941c0307511812080089000d03110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 697920476 1250 697919226 697919263
    0x40614040c1e030228030503030a0e0d02010b06030112020f04050c09040617060106080403020721030f0516060c02071a030106110f0a080f07061401080c1206270a03080603 75
    0x38513004640c0045081043d4a503000d210300e212624103030012952002036503c00101ca6a074940b00000178001c3c044074810050b6409041c848607462441400750803506840100101e14591030040c00d207056040c1d0800c02c980209000215081c2e0703917140c2c481c0b03c1c03081c884a6001c0b65503036001030800044901c0b81d080101c40403500c01c070480c40c00c000010705038159203190400da0700a0310380b030400782c5ca00060b940c02000100190080325500035072040c103840c540d0344240c40d0038040507a54101030311140510030015455000140925020843e00e4212825442081c0195807072183c031a0007104810024200c1001880000001000303019072000030074280d104400060000603126125080c0c0314004120090584400800c42c0708100c1f04240880b503e1544c000010492001c509810458a1000b48122111760140011040c030340d0a0400150200c900c070903001c1d10300c59940500d900140c0707000da00200341c842c0f05075207100c18002041105044090007a229034190345412004c0620b401e822400000540f41d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 697921726 1250 697920476 697920479
    0xc0509060a0e010b07020613060203040302181603150801090305070b09030f16060b090405011b02210d02120f191a2206060e04110708070b040614040c1e 67
    0x241402c841e90f05440d40c1d400466581d070000d0001500318001d4040c90311071800502400540690000300800480c1c2c800d59a241c8402c403032404078081c2c0c1c0c2c0b088500303280d42611900f08850f00d0b4820740c000b03000410003c031110300075a102c0038100c0c01c46071030360b02c01c6010440000d8010280444090019400304c01140118589100c00700311000c24081e2081c00107441c3c0e020007540c6c003044aa900491222440079108550300c1c989401c02501a2554803206502e4841d2540c2d600308451010480610f10340c1d50020b844860280c507000e21704180c2c410408080b05507401c6c05600080c0304015440742c002c2601441030b1110b2304105d050b0580c800a0a11400706403880c0c07156111521034920500300160908032420003443c00300200c100b84800400d4409080186001004507a40b038018150144000041d40c040240c01941d2514000d0f502c154000980a00c2062000000041040b4401e0307900078402d0f034010400340001081001c0d500825034044403800a1007005012190340003800741c0b5290000c0442c0036109 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 697922976 1250 697921726 697921739
    0x1151206080d11071809120c080415030204080d020c120c01091202031e07140904020604090b06040b0703050405101b06051503070905060307050904030210020d090501090c0509060a 79
    0x150b0029011400344100850f001403000300600001000300b4080d64520070750700b13012100e00002c2038006000c807201da45400c2c483c1c00e464800e003806030300d040c1d0001007a80340c075080101142c001213a6210801c1056001c01c07002c0b031228020b10000141e0315160f0000c0c2003044200c41009282580c501403c6502d42c058031520009a0780f00c2c40301d0003222035003d141106c00040d400402d0030412101006c031400003250050031a84000001d00004075031381b10500ca00c0002c01c0070100520401d042d90041e61255040c042805030310b03000d501c581030210005242d00e05e416552044090706400a0b103056000c02d0000c1410815414513041d880d442c07000034a07000c880e0084002d00000128030446c0b01800d007698030070014094408010401002400c02021180c1107030391601c14001508080780d100b030003806204000241402c0051100d0300540d49600a041f0b20b5840c01e0044000f9040121910856030312040c1800c00300d8801c0c49100751031406404203481d15130800c028009014809800239014060742041000070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 697924226 1250 697922976 697922983
    0x120a0c0e15010f0e0301020307181502150702070e040b0405010c14120c040f0b090307050f01020628110309010c0504061d060c0f0303010e0f04020f01260115120608 72
    0x51403000d0030b201c4070005000c0c0003281c41c201c131018080d0f01907100005008545421082d4496807500404003110349030707106c18100407852001001100940e0050440d5106003010140c041c1c0c0c4031880b841105d500030750b100d076080c200b0700d016101510b609a0450501080c81400c0c020008210300c40d05014101d0103100101c2503561050400b061200c01011011070405100c02e007c60b0004d022101c0c4241c18107890312543c4515910000c2e4181c480d2241050010309407d01c0101c2c8040c041058014200c55a6107001c504c0b19101004498024200b08002018514149101b0200e0003a0305c1180b031780d241d240811440703003140d00b100c0307445080c003000340410000759070301098000c5000110140d4120002c3e803500820701c24012200600701306d0143c0c0007002c031a0600040030754100e40c4215003000490320362640b04032a0410984000c0d4101d040d42c1d6480042e0f5010b40c20403001651098030090121450740c0780e58105100030b0300103c00c000104201c0116595000340d01c6d440d807040c4000c040000918001c0c01d25039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 697925476 1250 697924226 697924261
    0x114010801030326090d08090d09150c05120408012d0c0507051902100905061605150103061b05040b03010608061306060201050402090a05090c0f060405120a0c0e 71
    0x204140d036500100340f0f0302e1402084c02c603c50301000800e402c0c14102c0d8815201c26090810710001000a400140e03041e0001500c03c2d6284420780b2a095603c3c10301106481c030000d4801c0c60000c0c08a40e2440300001038041010451402100c803450752110f01307000f905404d4a10140856000300030130001c0109806d04000c1c5481e44c4040d8900008505800c1d0000703459601a220010780b19000300341c3d100704044c00707000320102814400c654605c003030012410292001b00b460f001d8180c10010078440c411418148800744102c41c1e000e03c0c00c80d142d25444150710811041d09800440d21181ca40a91804020848032560301030700c5142061030034181040504010341c08140f02c1c000c1044201d0303000c9243e0b901c071440350804000006d401400220340303941c006400f0b401c0580b0300324014244400060f0301c0b50344070b00c24140224282405040709030031350740c20004c3c0d10b00c6a00c08194400c41c208400030b890f541d844042d48108002101031f0482c454142004104541d5580c444a2505821010007801d005c0485800c032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 697926726 1250 697925476 697925483
    0x31a01050904051e250303020f03031e040303060e18072102040b0a031709010806040b010206045a0506070804032c120c0109090506031002120906011401080103 70
    0x30384213503051012441c000f250081c40075040e1400191a8890b00040180b0040e24000c0e0200e950810f440c01e0119030343e04c8112440001c003140319160b00d0045d66861171164000303000f4940452415261a9a05a44802503038086040b0b0001c07005505803142c00e02c4680001d1144501e19012654001c126140e20041e0560003481695a2207001710a0740d265021a80515004141e5040d050500d0010400395030156081c1408203a110000486500d490b0080742880101a4003a140c207031216a200d4402c881c800c4200c0f102c0d801f03405691310707294203a540340032641c6030b8540280030000f040c0c150000c20580340030784204000c4044034428001c9100002c0700d0307801200500d000f2019940da1300b001c490310600105105120048040001002c401c181c440d4040b0420032501e19000c2e04080041030351305e09040c29407030f004c218000300c03c203d10314544d03100a1b40940040d0517660500701c41d0040c001261f0204081c802e10000d07020031b00400005c2008031a0141501c0010806080c0d403803000a84103031014417008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 697927976 1250 697926726 697926763
    0x70e04021e030414070b04030807080c0106050411040f0e040b1311040f050f0a090b1504090204090320030a050f18030d02070602010e0606091602070f031a0105090405 73
    0x2003260840703140100349409070303180115031a402d16141c403415040c2030400c003081c203100702d15020402442950880741140da002e0369052a000343c031745c2c48000750741012801d070013503540e24000021291664022804030109244610799141c4c207000904251244640140c03036040031403c1000001448030a40710741142ea10320489080c00c416242140c0034400c074515a5820600303004c100018406c2c55040140181080b1541c40d422380e49020041c0d046a4011501400c03054041d4042504c0c0080e4117451020040043e0011508007400e03008038059401c01c10003180020317007903144200b580c080711000c9491240d02c0b6001d1407a100e4640c000402c3d50061310400765010305d00040c0c610030703002100223055500380d01409584020400c018003940750400b42c42040095424283d1112001d213000c9010b503c01c0c5402007440c40d076900c44034100040483c4c07410340d503000e62040001c042090706080400c00010751041100203401c500c1304140885801c0c0603800107003d050401c0a003c005880032030482c01c540c2e1040c424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 697929226 1250 697927976 697927987
    0x7080313030f08041703090a0e0f0f091510050a330504090903030507020c010201090c0b0304020d05060108010606020c0603010302060306090405030d0e0109140a0c090c03020f04081b09070e0402 85
    0xc400d05110b03550003c0700003800c1700705100d8800d20110140c07041c060119003d045080e03075641e0203900360b0300c112048070841141000103158135030703985d217016009121881200d0304040d116240e2030788800b0544d071100c1d8405400301c0030000e0389403c0b030388100503040e0045900b090302c81006240036801c000060310706072204072500340250544504107983c0203100c0130794240841c1c1c10030700f00a4001c04003620010b005002d80c20210700b455005000f00401d090307008803403006c000e1401c481c4151980010780104e074040303038540710800803600812085000e000707040d00015000d40341440203840d02143c24209030140c0d44c10310040025079a00020743c1e500c03e00558203200240e8032840c081d4154807403c0000c0c0b60183c07805284620606056204122161140d0422040e501689800301c0c0d032290312038002002542c0c6d90704140311001700c582250008040c0c034140907003044c1c207400c00c103c115041908400c0c0b0071f0780403d1031000907540c03420703005981d03210580e034001040c10140d0000f040c0a01240b0110300039500000c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 697930476 1250 697929226 697929233
    0x9210a080d0f09080d14090c0d06090803100f05010c080d0b0420040905060f030a021e0d03110114061516020603270d0816110a1407080313030f 63
    0x54080c2c0081c0a040290a0311450084080d800c10200100c50b603180241c0390700303400550f132000d5005885001c0184a241d801c2800c1104162400200f15403447e11000c4ca01c000480d240302a50054042261590381c442c14680b4100300507140707500c03103410000d4a400a102044021044a17050072a03268007268020b504400b20f0003801c078a002c04048551b44802c001101180d0402510030f840d01d01c1028070058a0788400c10429040209026605400240b500001031410807030703907100102c03c980f408081070031030740c00900000c0c80d0079000c0d4045810b448041d01840310070f210715448114003c00060031420710b800451440c55100c8a00b14000e28000b4540f01d8403000c0455010755142e00400003540c81c41c202e0603007a080c440e850011a0742407a10703001ca00c000000800c0c0f11310050010303982c0781030b10303514036089444005554a5a009000108448560b41035090098680481c0034034180c04d00406210070241c84c161040c2e10010442d007041c070850300da089010503c1c40490f5089600000c00112909 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 697931726 1250 697930476 697930481
    0xa110a021807170c0903100b15070201120c08061f0c020118090e03132306031005090a14070c030504290301150e1512090304050d030509210a080d 64
    0xc88070f143c900540c400304100d1610020081c12601d0050f41960341d401c00c220405010780304c0c0460950b0307100007134203140715001354094090300398a401407600c1e6007426404031000d01125118000c940000303992100300465820154001d90602c0d0480310311443d050881d03c4003e01d0100928402410043d5094541c51143e1707040048401070314000740c0c1005507441c00d40740030340c4c0e9900c03c180021a4441c81040080c0014601d80c2d0285410540d651540c15003045c042007007120351005112a43c0395810a5020440c0d841b0201000e11940c2000800218101302030391184207a00c00030580750400840c4400707032000a503c07101b80e4040354102c1d103000122042c030364003d0107159008460740b0841389d00840001201135003144050454042c503103602d03000300142c106011a00074018180828000104550b041000b1000740481d803000d41c1f9800e680c01d098607000061341010190000340c00140c1c02182c03015291034601c0d552040344591014070502c10200d150a00d03100c03551401c02806484000ca80303411065801d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 697932976 1250 697931726 697931747
    0x15030102130e100f2301021c03020a030b1912080c061006090f1203230a050909090106240e1003060303110105060303090411040f0b0a110a021807 64
    0x101c400196103500c403002c1e82e1003044100c4401441c114100760014440b1041e0340c6110030b80d0070583c524070044079103002104009446440c8541140726a5800d1080d00b440707101100300c03154043c0c0d000750b0740300c0101000138155842d0300000340c4250036005004044500071550b090071038244007a0036911001c0f60400f02c0f85400341045d592071a0180c50f08008080b1001d601c86426100e41b52500604030b602c4107e802483c400350702031301584030220121a400710380108410141101d541d451a00c0e5003141c90240825508540c0c4040c010442c0030800011a20340384c41c0719030344416201c1c000c0010a00d025205010203800503154007081200b011070151407445028018200302028006848999039168001e000300702621060b0000740303280c00108070100042c0102e90040800500843c140002c1000700002050125003000b41c2d141308000018035280c4540c0c00100070101d9036520350b15003090000c054003c00040340c0020841c1c100340c0d408401aa56400f294410280380484080c0550fa07603201aa80b11015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 697934226 1250 697932976 697932997
    0x105010309210509100302090f330a11010203040b130503040f0b03150f1819050a0b04051b0d0f2910020d0503010e151002010f1406030615030102 64
    0x490000b000c0355002402481c03c90f806403040f9440030603200c0202d0481c000c40310314540c01240111180a07902d030070443c03e050001c038040701d034910000e0741c05d0325110820a50042900100c02042a202c8640c000b48045981940c4900275459413400c1c1d030b00d40304a44002461201c0943c0902804014070004200b56030181c03941444e8001c110b911501034000d507810403581c2d0101845d100d49181d00d1400c11842600450303e0145c28994900e04860110f114420010980a0300c0300e0380c0b2080300390074030207401590b000c0c4060314070014040c043c2030305100075904000d00310140e5a100c0620b107610320062808444501d41700500005003009404420701c05860002d5090f80c2c190055201c1c2040300071000126024040e00711030b9003008142c008402e80c0c5480f10510380d440030510910040103100040c0d80c103654044459000d0742c2d40703030750140f00086690046075421f10050390341c0c480d82c0140343c0d498403402100b040500440e03250792a01e5400650340d0100180801e101d0781002076080c10341e40f8250191041d0284 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 697935476 1250 697934226 697934273
    0x1b190308031e06060406080f060105130f05030d030e0a14030d0203040b0610030e0a0201030513050a080c120304020a06110115080109030e062503090302130203150a0e0105010309 78
    0x1d01007a030825940d564882140142d10140109040f0b107084800c64045403d5a180d4604c03075501d50302807034001040181440d051200030004d10100204030465000580b02004000b156941040103140c5001801030f45141490b242180d610b251810000322034020552068000d0351030540111070f0740c00c602034240e40c00a0113001000b88020080446501442540c05841e032081c0400343d010b04505580d03044410343c045811004501c409540304e504034640c0700803440c09160307041c0349550710b05203402003021060303801c100301043c001011030b0184410a0050340e00b40c00b190075410540c000030100c046a100f18000d2010810304a041d0712002e420160704040104040c414140e61540e0482c0a0417100c0e0003100000d040305840d001d1483c009060340c0e12440041a100507800070222088071240788035100303038140b024905002005070345030320700050450707041a03015803203050200d442c00381040701c094140e01c920403240c814050120343d085070a0441d0000d19001c90f510146c3d042c40300300040e8091000c3e11104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 697936726 1250 697935476 697935481
    0x40c1e0c05073b01050103020706140103030c0b0702010903021e1504051006050607110d03050c0303090106031403070f033204030b180c0634030f021b19030803 70
    0x1800c9074002c0c003d488007a0588014100002503842e101105281c2c80c115100100050156502c26405880c507a8800c000000c0c600440081e01c0840d240c09a0007200007806180ca4542001076002c48180c0004860000b40f049802603900030f5101c4500306030a4182103451200386c2412070f030811028000c0c0d0380c1800349803142e050a04205444280211000303003000d082c01f40008081c104803040701c001c40d40100c58401c0c007040540070031051b500e100c201601001030078001c070060700f5014030040d405051058000260703180303103151001720214907204101d0036800a0000d03501140180100511050b850304c0c00b084110300c80706030350058480070710300c1a03025411900100b401da5903d600400030390b0b01803e100c2c01c156036400f426021481500c0c4407140c264024151202c1a414180080c00c8400980b121f282e807200b80c9001c81c0003103181120040007140c0c05501c1300005040e0005001d00b1410f0441c40a0102c0c60b1440080c8007050154181d154050003c044103100000103100c85c00001d554002d000b5070356030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 697937976 1250 697936726 697936739
    0x80d0c0905041a04060b0406140703091a0409140903030a0924050a0b060403080f0d062c01080105100509130b1e07030b0907050304060b030f030a0e040c1e0c0507 71
    0x10000c491103075004d545821008103010780410240d8003241d41668880c00300d04040b200f0109280c0007240d048052081c2c8000120342c074001d20035042201151003c040392143d24106440c010389004190001d00c0030006c1c0188150078101000300c82d8442c0c408100803d1202440ca8418000c44030080344c5800b0340d14800ea142d040b41e0b0f06810043c087c1c91148403e2080e0580f040c100082ca05c81c9200003816400f0800401c421015400080c0c103201d01040400615565104043d00a581a03210300d06c1701048030001240c1d43e14440e1b00344030301410600c3d00804c614500000303900340c1c08801d40503061242008000164000c1107111130192203d520584045075070404005810300c41e5a44210750130b91108110016090612034407030701402e0b030002800602c1e00c0c2c40340b050944050740050800e81ea1152114042c01c1036480c1001005e12825516000756941c0804020041c11150b4582e44035100d41d051000b420403184d1b02402c040c0403482d0211003010560012041038440e400410402030203801089000a2107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 697939226 1250 697937976 697938011
    0x118090e010915110a110309090a0c12090b31030206040b0f060d03051602041a04060e061e01170a140c070506011701090501020c030d0b030a080d0c090504 68
    0x100c51082200c0300840c440d0049800030b8400245031104c101c90300380540284584904002c80000f4071030740c01e9a19080245d40801c1408008a0303260311499281c5c006410720950021104095101d40e180070070103810141c1d06c0040c5100054000c9011981ea2200d00e014000c121100c00710303d07002260070000161041c038000e501c1d440c1c1180c064941b1415000050040e0710704e5511103100b0742000f0600029200c0d04c0d90b050b9401d030018251004809008050580161114400c20007803451100c07100d40c2480c4500300300301c2990159042070200c0038071a810301c0700c0f0f0303150540702d504240e0700728038000501c07910080101c07250043d800b01010b00c1100e107818050400441d500094260789110340f4005555900d5804803428400d681c030003041c0c0c2d48003900400500003902400c0c845504620000b081c17034026500d8190a9801c51221110503400c0080c4c6070036198041e03c036404101d2015005441c0c0000280c40304820342c040c10442500c166102c510410301540302d0010100a42002001000844400c2d40c4000d513 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 697940476 1250 697939226 697939241
    0x1803011805060601110d0302070c4106070b070e13090b07110a1b052701050d020d080f0702060c030a12061a070c17390118090e01 57
    0x10341d0300502020402da540315203135000ea0b220401000b001490b400700c2c0110002e51000c80d0654072180e2115000c91265409400c3d00d04611411996202d50401900740d80101c0441e03a480c040f2080b5080881d10050300c03a1001d0f603280c55041414409a80d07a0a04141c0b80d290f14420500d500800e990702c0c903c100b41072644500b84541c02000445003560f901c4805540c45090040010780d940d0007200301400280c00c802c0040300301a461031104609698a101085041c0000030500503032a0040c100741c40220348045046006103412102810f0140141e000b00e0700c41543c032900500701d0100014141601d440200852b00c219a000d4106a5103100800a141d129002140c0c0f050000b0321140d5003001c5440035018182c15220356201c00440003048040e03808131507101e0f080c2110003440d282000141d5000e010419503124989e01e0203012040d03600e80d41034040c000c00564001c081203a103114820f8900c04588990390504c828241103603640105110340710003c040e90700142c480f50602c0504880082d06401c01c21 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 697941726 1250 697940476 697940483
    0xe0319020606010e010c0f03090503120a021b0105030c13080304030b010612050f060d030e090906040b010902040f14010c060609200405181305150403110c0f010518030118 75
    0x81ca5516094011541c8214001d07925000408103241c5001060b61244c0d540c28061081c144035503501d5890000c2420b100b40c15900c450442004a204900d00da014000344022511540080e07070088403220001e016400041c00501d0f5100010690034034038404048180094600541281d44032507032450051068a424040c0700c0c00181e4030581d090464204e4060320340103640350354010312650755200500c420041c1e112015020810403150b40951521240b40c114043e04503a00a00360600e4941454280c1c600c06a00134502203204100421101d110b003003554081e115104040f4510400510040b248a6266103010340814030b00310001a0340e20440d8000e043d441e52041403126411414041d02089000391b00c1002d0b00700d03e12004001c05400b81a500d60f611001910301d000c170800b05511680d1030311030003042c03125030070b8070380ca0511080c1600a0140382015103c0d40007041602d803480042a4035120070142513060100c04280307900322501e4842c0c10322000902400821624001c08041002c02002d00da058 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 697942976 1250 697941726 697941733
    0xc12060c020318040509191a06030a110d02060912061006020d0903061d0a05060702060f04020f0f0102030f0a0819060501170c040302060d05060406060e010c020d05010e031902 77
    0x2503450303400401601c01030008103070b06825810031070090001400c801001c00e40c0c14010000d5074002505d900c1c001c207903a10300400c141c900b001d842c032144009a9802802c00c501c00c0e0300c148030b541d001692035881c41d10010b03c02e450a00d411415840402c0e814000c3d226510f61050100f035255482240c005403c911802441840d010041d607100070070b1b40c0b1140300c1a85400007400318581231001c01e28a400590714020f00080c00d0f2000780400d2502410201c4030b10088516400450a00c884203134104042c507088007030101030703841d581020703070008004110503a03040c1c2c0249800c400c0341c4c0d0103030300920a444400150369504ca41e6103424034002481d8640886021100b03d03804100d11500340c20602c19001a40d4041c0c44264403142c6400640c0b6041c00c00074014080690100404001a240c117030203070045189040300452141001e0003080190344542c0c2120382004044003040b0400d80c2d201e8580ca6400d038042e03e9485040c000c908241e405089040c40070032045c84000307000010f508200b000100c8003030f1643d00740d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 697944226 1250 697942976 697942991
    0x20d0902040506090907290a050703030c090b120a0e1608060c0f1605071814060d021003020d021603020f0d020f060103020f030f0d0306050406050a030215160c1206 72
    0x1040b2011301c1c261403400d480d038000101407191030740104c1100085005e404190741031a0314204c2c075034402c2e4040000c0000103800801c09208161305400754000400041c204000b5160409a640c2000d016050082880340007040109400c80d4a5a01c24400480740720300303603007450036030414140c6441c80500c2440c589115520004d4a00c00c44202a94039403c040e1001519108e002d25140e03c020319084030035141c9024024000a0361403440716443d00724240c0c01030100d508036110303448503002c0400410702070144162070780320750040e90754000d94029110b460500688915a01040c0d4000307001c0d414150080301c4944091034281500020f540381c0e00c54010301103070400d401c60b000c102e03100d84003184c2032901507121170014401460003078009510000003404486c6213010041b1f4507850042896a25000b0a55401062100c0d00381805a100901000c1da50192651300d1079003c1002e41d0300c4200b580302c000902080c0e407454102c0405041da10a80c00c03807618421a0788580503041c10740d8503010221802460f0048 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 697945476 1250 697944226 697944229
    0x10f17030906091908030309010f0c1107090c12051512070602070e0415051005101103030f10080a05010c08060d02060a030c02030c2409070b04031410020d0902040506 73
    0x2201d044000c080d180d541400036020500c410103090120000c61480c48404c045004407080000d98070580c0391400100c1c40340d8149800808440114017840d0400a038042c0241e05600001940c1c6d044036441c003c00984c004d480c42d81210300c031000d0040d1401c1e260604040c050075598225034011404002c0700d070390390310440400101d50b5480a0340324940243e04000c030104000c03c0c04402e03440e8000d0045420084002e0b40c890603000b00d850071510607068155501d0140700d0fa0810108001e0000880c4c10300d03008011710700350320aa0306d00008049060000201e0006002070f141c9035802d00044c00307210100c80904d0b50500d0b1030382c0a044407103d48000180301c0c070006001c61410f00c49524015801600003490311003c10802c40140c07920801004c154030080000e031a5404040142c14603240d690700c520803140081c0c541c462520700e005040040319500240050046144540c21202200d0380300e07c8201c11070045500c0d060420003004002680c0c148003155840c810f01c06034100a040a00c200c6003005155503190 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 697946726 1250 697945476 697945483
    0xf06090e061f030818040609051602030418183e010f030203040f120203090a08010e0616020a0606230904152a0c1a06030a0b060612010f17 61
    0x60b400450811204010004200220002c040412a07182c2003060031500c5c00204007030342d40b2a44281c1460381d0780e50030440741d85050300d240200c0c10b90503c080d500d01482c0200c4180300030740042105540580d41c100c100d040c2c44800c4c0c00e4540c55980300b1000201d0300b100606000e0491016400c14400c050500c5c0c090300c42d00180c030300074610b00703d05864803107814000180850003500001c10456040c00d40c0451000480c030300c0000e584008203154011a902c1e40d044041c00310310a440c0c3e01001071a81090700d00e01d100703140442d0750f6602950310102e80341008685c0304100e00c3c1c24600c071400b524044c40c0440100c0c401410404140707000d460445880741c62020742041c00300080c01258081e083c494901540802d000c0160095004030f80e400b81c130761080114210040b04c40100025005010030021540c1c001000342c0d181c00c0000d00764940c403444600b072401d00003094a5104035840140400010310001c0d40560b18441510f4105440c2902226150f0f11540e02c000c0e8000f40d405030f2100d00c00c07041140341030b007232000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 697947976 1250 697946726 697946761
    0x100201061a0c0a030c1e08030717011d040203120d060f05031c05030606070b13060c020d080c0703031113030b280506011407030c0b180d080603010f06090e06 69
    0x202c02086481c00d66101110341c2c50307918101b2607120038070403100740074005110203030314007540510704499903400c024802a0503801f61075064486241c4c2d2100400c10310b080034031010b0f5040404c04414003140d86520000c0e04150084280810320440811440942140e540c045415558003030b20400989481e5001c060703513140070030001c1d804551302c1c003251040c1d28172800240d904840080d0105040c07981c6e42d925039110310401c484214006040c41802024040e507401800704a40450010304449002d9010040120400070a2500c1c1080001503072000c0622940c4040903480c0152102901c03485080c0c0c686920324024441a40c1c45d03c145800704030800c0c69510355070031011450000003824804501190040c0c200104028140441c0c1c645441c5000c01d0341000741a0741e44655101e00041000d07281051071520050505134034829101d001004242d00041d0036000f01503d824061032554401001a014003c019548207503581801800107000e03036581c00034116101c00d038040d205035544050480e0804a0b92 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 697949226 1250 697947976 697947997
    0xc210a030e211b220f1409060f07200307020901090e1b06070c260a11060706062408060d050a0215091c061404050d0e060702100201061a 60
    0x38183c0084003c0e903509003400d4884003801018281202c819101308001603204c0c107080340b81d103410409424a0161003545a0308036580c4c0480031509105071450f036983e00081c09410500000c1e404161094000d1034030280721240d8136100a07400e00c4100c7c8040d00ea40003188228000c6202000101d01080240203814040341001c00034143d0400d50461a8600300600c840f0b940c000c042044100c0104034102d01c043d0260941206000000c44104160b00d0061084800403106400094004000903000340311045502800c84882e516903129081c807500800c0140e1002800c4503015131030804050801400003485015921903040559580c000e2054050750490b00900c541c00c003009140c01886c01c0d000d440114000500c04508005048010807845a05200d440b650307209113000701c408000083c0911013003d00a400c0030100b03130038035550301c540d108801c2314000c0c14400255441c4800352107034415203184540003880d040ca00c07506d081c00a4000c00c441e005040021a0900142d40a41c9074001200c422004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 697950476 1250 697949226 697949233
    0x60a1b09060f0c0201030f020309030307021002030601081305100c11010b040e06010504093f0201020a0c060f020d051e070f050a0f050f070b0601200c210a030e21 71
    0x9400101e410300f281c050103d040c190f0382c0c06401041d241c684040c51083c05c4003801540e407810610b0000c0d00d40280c00c0351012406004004120991360700c50803550300410f010300c1c00107c0040c0c85c50710030708242c070743c0715281440c03440c00c3c0c60300c0a03040e40900260403449190340200400d200484c1800103841c003104100710f050f80420010061402c0980c090301c20b0034094142007101b107001c1d05400c119810840c0d8000b0600c0380b0303207401c10800030b4010503215241c48180000c5280c582038100140c15031045078030103440e103941d5041c03000c0c4c1244280c0498402c50944601001079141c600481e001c5040c54400402c406c00c51040040d0200c1c4c004c1c01050070b82800380d1070b0035041c81c100300c00403280050144001010485c0600100b02d00140540c0640342e558030a82003403401d491300c24001889400c1841880000c104e006110701100500440e600d001c002040d91412100061140c0c03241c3c416040551488043c450702e01d091052540c0329000901c0003100300c50395810603c2c0c1d20141590340e150700c012200c0301e41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 697951726 1250 697950476 697950497
    0x3030506061e0901020c1f02060a05010503060414010b040c050301031704031a070c02060a02150901050105100e030309120f06071e030c020f06010609090e0a0c061d03060a1b0906 78
    0x1c07070b04405031080c0c003014811114002680c4000c04c1c04144048210781d034548148480104241c1c0501056511042c940c001300255071501001980d1a00043c0000d45a076400c0000e01d44490007c0d040031129400242c401e11840500c1100104194403d200070b6964800050b50001242d00410890342285e4010030040640e904285042c02d070ba51010b0408400e00855a0b81200140c4500e006050004040d801501030142040e4010200100080c10400700e40d25120060290780d036120100310f00742e8030928103840210130100100740740d403044c494015403080040c610f1340c1c101e90340041c0741003041c0c20401c280d036150f03160301d5019030300c111400c101d0800321240d1940104140e44641e20800944100b84110f64008840030320f018101802a00300400080c3c400704103204105050080e00a07030741d01c401c010010f80416450b01c10900c68103004900400000f0b0380401c07001c00704403c0c8840c1e400401010b540d054141810a14000e06198490a00e00f5580321510300d6040c0c01403401c2d004585060700d920b207506 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 697952976 1250 697951726 697951777
    0x21020607081503010906020d0507231309051f06020105040b0438091203010f27020408012c060a050a020705070e041434080610030303050606 62
    0x3441c0145400c880640001034030101e99402d000d14021140110300c01a540c210b0303018210309640009102d102404001d60040b501060320b8645e40721a040c8508001d0b07141c90304070f1240c04111005500ca0403045040c00b0502410030040003032000307a07805400708602d100d59500000ea0994504880c041d004d000d0100028007c500b00700e4800c4100c41440c41036102d0b448009211012002e09a5182c036000903143e000c02004440c200010001150941e480906561403c2c81d0f91401d04850301880440c420b484c1c20800d501500300092000b000742040f000e40d01e503510303050928007c282c805145010150f4411404020311441c020b280012130540d4003030710b80b035a6244c1005000c2d2001404040860303500308494408903a06001e08ca0107403c0900f516080c50409080500c082c21942000440d141c2040005015005611040402d8103c40301e100d902d0100d110310b41100322030195070201c206070107020308102001143d42030850a0742c0c0710303450820850b19550144000da01929040e0030f04180c0707140104044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 697954226 1250 697952976 697952987
    0xe0f07083405121306152114070b0a12020a0c1202071a04050901060302120f06060403140f060903090a05011d1804061820041b0c21020607 61
    0x1400103042c0b140c030341071006010300c0004000700c5100b40402c00d4000d5210411086004409000e0094480985030703a080c07911078920410102500c0962180c0d024128040184441c2c10f4807080030715070300341c81c804c50340e0b11406000740d4812001a00050442a440001e040f014429500e12642075a0303080c3c2d4925040d601d80028090f111501802d610407008006151600900c026625000900c442515113140c1002c0c807104c010180c100d0300038140140000007000c9000172980e944844e00c2908504151070340c0010807100d01c00c07038102802c81001c0013905442d00c08006007425480c040542210596542c03c80d20388c0d00e038014001c00135401002680100300c650700c110f0590921440e280070385250864030000054101e10a4003900c0c6581591000b0802801414800da4001e2400f005040c040340b0910f90311202d6003412080078115403131401e4007200c00d640300c59104000c01300300c0c034202012080000350b014249003240c81c41282c901400c0785031850008aa405042d401041c150000c1000d1340b5180421341d82c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 697955476 1250 697954226 697954321
    0x50307090f080102091207030f0f11030303071d030705031e030d020c0f060705090603070c051c031a0a0e0703020903031314181005190e0f0708 63
    0x30400800404038501800807105070040240000050b62281000140112844604502d5550781c201110402c0803482c07481e4404400c0740d04c055006403090075843c101c020b00d4001c915058162001000304600307103800114141204c90000600c0030740014070800c06d035540f00c15002c0e490301a0000140d0001e0781c0e480750144070707040c480341c01034a060025110340e02c0220b0700160f00d401d0f1981d101982c03004075110f0a2012540000e01403502c01d10300407020001c65610300c00a00b9905c200601481d03044140041400100c0080103615000040411070341c0004000d03008020038410340b0000b00c0c0b1248004d10b40300188204940c1d0034030030000295225002134000750011000a40c0600040105100340c40000f40004041c1400e040070300a030840b2001070083c2d015a41980801c035450400900c105000b148074041c0485100729590402d10011551030400740e0381c2c0341c1c0041c1303003400d080041c01641400308104610032421940c440480780d8507140982c404c4019074411040d252034141d4410b149407030312211200d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 697956726 1250 697955476 697955491
    0xc040506030f06041208071e0f0c020d0b0f060402120f0408130b13092d0f0e0307060b061201150306031a06040c0503150d14060106170106021209010503 67
    0x50302c1007800c42009082180841d03017250342c8408415210750750307a080300c2040e400100703030301e0285494489559080580c0e210f6070b14182c10300001031800d10000c0d03c1a80e84500880e4040c1401d8600d05076031610360905c510542c1c1244c0c105044200142850030548240c0d900012402c01804058840e021300440700c0a000c1d00555002504004440e040d0701c18000c041e0041a0000e0007036520307210031100c25411140750304a174003d94103016100468aa507180800c9160001030300580c080c0591011100040c0f400d45092070800d030400064540800c004405012201e014a105001c010f00380360400c5103070300c5070011814000c60160014091141c110000da402481e09090006803d500ca40f03603081110314080081c10107040d03140c200700076410940104800c0a90034103116086041510352903280000d003482050090381098140002e0000c11819050345400100546041c0c1d6115035000f00301044240042600400310f500001d055840018000c0f0700c866070080030760814240d000115000e60002d44504c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 697957976 1250 697956726 697956733
    0x20304080f120717010f03081315050406030510030f140c0303030a0605010e040c0504050d0312020d0b120307050309150d0e06071d0604120f06090b0a06120201020c04050603 76
    0x4080c0e0000c980c001c240390050b000b5000420315164a004120004a000c4603400742c0c0c44400401911030128001c078140c1c5e81c048041e60b183c07141c0310000780f4503070495130212842c0d882c48000450040c0d04800248140c41c51540d050106640b0801441417081c03051100800102c410030200010561081d056a02c42d941c0070b040d15003036000100083d145420a4030340b0000700e030303840c0c03410003070307580c003d00080e641d00c074182c905100e020040d01c005801402140718650084140c42c580f101054801c036100715220038562070441d00d4102d69000100148004c64881e40200d440c1280031110640000c1500c8056a20000451902c642c0c030003403004c80204604e07016481e074424030030100708804a0080c07080303118011000f808649441c903c020300151814240e10808000b042c9001801d0b11905e086070240e59800a84a807103582030315145481f8003400602404207440d203c000c4003000404415540500d103190000e00446031240e0f10b40c20442c0a1004c024056444180c180c4903500f0306411595016000a056 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 697959226 1250 697957976 697957987
    0x32c0c011427040501061128080301090b010f0c0b0103080a0c050607020105160f02070509040302031b06090c15090d2301020c0105010905070c0605040c0f1203090b031902030408 78
    0x3102c0400d842c0307070803071403920700300c1c02d02d0146040611a2030700400c030914241d01d09503840444141c86022002c003250050601880e2100380c0300f101c0d41c07405601c3e5484002e2a03034940e56003c03d04010440014054006081c1d001c5480f080c51080900c407031103e802684c1403000da40380d5543c2c050760740d0180403204280000860000d000c1403080c840c0c031f44200c1d05600003142d140343c0803500c1902030150448860600403484c2c0c021982550004903d8207480b000d507000000f644650070180c2c9140541d58050818030f010900c2200f204402103016405441c00808039a030303030102078080091b00d200d00910302c03000074030510407880e4528200c00d00d1140300780105132244a91100f8602c0c00f608001800121200340e40001312280401c1092003128010031121000300720138245420b00901e40240b81c5006000c03980c42d80013080030300c29982508401030030b018060a0000f036440c0714120b041a110003080d40465908000080d0b12a50901103e03c207040c41d815010707181d20070700354000003508058800c9e1b8084006120 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 697960476 1250 697959226 697959247
    0x6030316030e100806011413180e060127050c0c0d020a110d0b06090a0b0603010f030b060a080a020d060e0601030b06100e0f0607050a0b011202030609120304080702011b03032c0c0114 80
    0x1c1014080120310808100944ad444d51107141c40d9060784030740318032441503e0400c445a0201102030488510340804101398550101c0f0210f280a1441960818003c050843d100141c000030780890081c880c0741d08a02404902c020002400f901b40c102501d800d510b80001280c038170b40018800d6000d03590307180016201404401289050700709801540600241d10750a000744624a54820391108080ba07060703590a040003141e80c2c650107017200080c016483d1a503540d0410416411100762146030108582c020340e50303802d00454001050f1200ca01540035080c3c00504c440c071404003180e543c100500b00040d0040d0200910980340e102d14019038040c000c00c101e07200040c0d45200d000e8003c0030680004484401140105070405d0740c058411039040d0320001400300d0382c18084081c1c90703102d0b8001c044030b601c0b5926800143d603494070104840f07071141e1420002000301740d01a44001c440301803503030700311aa031080c86003489503030030a00c002105185d12800c002070701980304e40742003d03000d400c091089007810300140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 697961726 1250 697960476 697960499
    0x21501031112010e121e0703030605010806030105070f11010e1e0c06130504090204141e090a150c030e2a0d1a06030316030e100806011413 61
    0x30011914215104401d10451504210078004000c82e0780c0200226125080b802d0398604541c6842e2078404000b017035500449400154503084401388103409540c0e85884c7c58024010311a601800703003c034207600080341e11030605114492090400780c6500140c2c0d131110f90180c0f400c00c68081050403e6480f41500d045080c0b080c044d401007081400c2400883c00c2c0318016560030540c034052158001d02c400e01c6021541c0146e1400d400481c5c90a640c001041411400400c0140059102e428031000c070304070600405c00c1c40440e4000316641e101114400a44441c3c800c80e03280c400000000d0441c08580c0e100909806d0158405410901641000200c980354841000c1c180a00c1e007000070450380f80403041184032016001c6042c04024100d0340919144101c2d541d45004e81d13000344000440300c1030000020f005441c00c0045030401040e001201e545c490b91407a000707105144080c1c0b8180541d0440c0100c1c0c25013070050742c0d1035001d050161503100d05500c88040c030104d990041140440c036000e5803100010310b4420003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 697962976 1250 697961726 697961729
    0x305040510272402030f0f0705040b0a051b030405030c010318050106080304030c080712030f020f1204081002070302191a070f021605060405040c140d060503100b13050403021501 78
    0x880b01c280c00c00f0704007101040c0d9420000c42c8450914010401c00c824220380a51196102a4882d100301c078039240c0c2c1c541140c00b4080c541041c0d542c03000002d85201803503000000b40600450028250b0742c038082d0b08004136140d004601c00c7d50781660003201844201d6029030401d80010920441c24108c048480c2c6038242590b005a0050b0314039080018148203010740802100081c00c4803c000306011440d10b07140f02e142d0001d4010140070000302c038440300281403081c030401c954401007004548200d00c119080041d140d005100340ca015200310343d04e14401050900a8a24030b5802d034020717015a10221303008141444001408880800305100c3c44481d9aa0010513a1300500341c95545140e017071508440a441c02c20021600d8810360210f00c010440e6980c1c040c2100c0c15260251800f00d501450349005944140b603071400b1540341800401d4441007491190722000c100c0740d084040750300c120440070b81202250311038081180c0000302d0600c402ea41030306036001950014828030444001202c030130341083c4820300a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 697964226 1250 697962976 697962983
    0xa03060902090705091c210e0a0801060e0103060e0f10020316031a2427150304081c0c0207060201060605040f17010b131506030504051027 61
    0x100c400c40015801c024182c40c0d0b201042e400d0061030100424000303005010681940681c0d561210344040400c03800c0b2503c1d4000700200003031a0b0350005404005400b912005403144d00406603a080011043c905000f844102d803614400c21b040780c0d007541c450901a03d01030003441d0b003c0c410000042c2203004100030741001911050401a10fa04207400d00c400303030b00c0002810200701810560380b04000c0300c5a04500b8515141160980505580c0010144c210094502d05211100001c00c2464040c201c05030920000744d200380d40310450500c00c0d42000300380700390070003d00f40754041407001800103411000188544004001038902040c2103800b88000d80c0c070241011001604100420080c075902402400090089820041d05050400c040d400c5201128802d01100b1015000c400044031800c3d0700041074900054092900040c546896402802c900308503250400013411000400603c0380c42102e0095510074041c0c4160340f03460789100e010700b00003c01f0b5030719641d8226012800521059010f010300b4070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 697965476 1250 697964226 697964231
    0x160c05060a02010902040b040b01052a0f060f01080f030a0f0c0606030807050f07120305130b04030b010f051f0f021005090d09080a080306100c0602270d03020712110a0306 75
    0x41303803041c0000e681c081140240510f061150701a05a82c00400783c81c12243c0304010b000159031686c411040c0c3c01c0b45000c05c1d4082c0d000f9120340015a00c00810903621601640e81c0f0115180d81e9106108c0d034401484400407000d0f0014040c04008034404c2d88078144410603440e1004013240c0c0d0b03445034000c44110340e00031940d0390400160002006000e200078a80e22800d80042d1892600d01608c03685210340090006040240009000200c202c6441400018290324140a83c44076124681170340c408a017801020425040c07020300103460319204603a0f056101d8031846408100c545258262880c038440618070040d4000d10700195080a075512402c0d2080312034038020b01800c49150000340a88019403c001c0070f03130308490804804544502d08a0740c01207421f0b40c4200e42200700c0c0d1002c6a40c0c080021f001000300d0300004d240c00c2000e090f41c0200f9080c0450b0000c43d00304030084000c00140c011807100080150308255410020600c100e4a00d0800600550190480b440c1140010b81407400301d401c202c2c0d41c05d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 697966726 1250 697965476 697965491
    0x180f0102031915031e020418050607023c0f01050c130f0506070b040510150509010b0304030915050702060d020307020622060506010e060d0504030f0c08160c05060a0201 74
    0x60b641d0003848064482e1282d4450082e045494100d0840400304044131080c0e0341d10703000c004644450741703d0940d0304100400c2200365a01450b0040c0c80e2201591900010302c60521081301040d0f40390304202c10001f0403440d0102002072a1140400f5010000d10052203025490030b24515200130700904d0700c22038034060016a60602e4440013074901d46182c22844c03150f1401c40041c0040d840784011030701010303000501c0c0c00b1705950740e10745140340407078821074514101d08200c00c400d990304214400720b0a079a01101e1383e44107a030f00e40365060918041140c014000982003035040156020f21500c00c01c03d203e0501d1301030719092050300403072403a612449010006c1a40003040001443d03040c0001e1b5009a01003610a000e0009444100304102d900c0744c002c1c2c0410f541e64045815a0b005c5e03c100c620402014120b240c80c3d80d1090040030082004490550100d10040d450681c07407442900c50703098190f8051030440c10081a0b1031001d80d0f03151411030480e2041c10300d03100440c0c19501c1101800318841c40760700204001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 697967976 1250 697966726 697966771
    0x405061f020c0112020a0903140304180207020306061c020409111504092d230408090a1a1818040c0f060f09090209010905270c04030308180f010203 65
    0x130000c00c070035041d807441403050144840d400111042103e410142c448409064600454114801c680c400c290341e5142651403904414150003031b00d034050084081d034080350380d0070090180f1050400c0d01d60004400c140c43d0800149842e9201d03020260041110070550081c280105981410004c00307040003400c0801d080000c81564080c10241d02c0d0700f0b005d4068007428000c03112225078a03d582d01100207031100603070312211900100350b0582144d611078231669403c045c20003140b1540b00700c41c0c05010b0b4070380c0000407402901e00040c0d000d403000944101460281007290300c0184238010598a03078400c042d00b5028030601c030903800460040e4040d0040081d007a1034101c0703020940656601c01d600f401408440e280380c040e0001c841504880002101690340d000781c0c80101d40819070307600001d0380440c0405400c19240101b4503400703504809a02030b10800e440d0790034100f4840c00303940f200400144080c1d00045403400b01d07540d9241449004022501070101d2046e040703003644c0044a0300c90176540c0d90758132003800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 697969226 1250 697967976 697967987
    0x307030f0b041104051e0a06090623041202040612050d020715020304061b170901121806020c120703030b280509270106030b010e070e0405061f020c01 66
    0x207070002c950820594000b4500100c1a000700e00c01d0521544161000400a40403903141110030600181110701c0350303440f01d030060070b103021501800700000c141c0c00d00c000b08002143d01c0c03a05080c03c0c50b1061800c152800c0f0058001c892120422a0841d03141c40c8005201d5028241056402d0705c0b80c00580303c0d0307103600c0400030310f003260b59806500086400c903811010240c0110444094a4451410b46655450080210f1101ca114070004045030007046040c000241c0440207400c070071809a03990130120800d0b81202c0140d0351070201d02c41c0490428959440005c04990040c03000003a004142ca19901e00002c803d50550032a01d025804243c64441e0300c1c1242ca041e0035541882440a100c50000c0c20034011220060003c901846005400c1103000c030341c40401c901581754a1001100207140700c01d45031350206020f00a94841103952007808000411000d0905e5030710340c030540e40c3b035403800d084d00d41c14001c00001e4480608080e0300315980946800342c00042c10300d10150f4540f01e80050000610b40c000041c40d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 697970476 1250 697969226 697969241
    0x21218010c090b0306010c0204061508100501090602150a110313020411030c220503010e070807051008040b0604091e0215160f140f0604110f01051606110307030f 71
    0xc1200703204003404043c1110064070b030440001e1030a030300e40f031403184045402880e9a4101c8a81c0944010084440b154000c00c1e01e44680e5042d043d861103d60b0300c1c401980c50280d280540710140c5c01c00c01d50364442a00900c1d4890780601c0c50300011640c9100303840303c41c074541d0050b00d401c076417094805030b00300075400c0c54007903400b441030460034145c03940c5443c040341c0d08540200141c810100484851a80542200c10001c00207003100030300800103030764000b45c02a5035544510a08a150241d542c0004951402c1c28142498440948603a9111350f1140d807072500012008040036441942c4114180118004a0002c2288052110401d0328950180100101d2011000a0031851242044241c11000c1209166600700741e1220f4420316000461600c03440301c24035614500024406d022070b00c00c1a4000040090145000f00c0032203e032400110240581e0300c4914a00c2130100300104110704200c5840b078000003219000e100001030110380e03810b441c4c100d40d20035a048800242c8440054074894038900c103461 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 697971726 1250 697970476 697970501
    0x905042a03200a090518030c0c120f06040b071b060c0210111b0a020603130c0b0f0915070f20090103050d0507030c06060e100e06030705060d02121801 66
    0x100751128103400903070f800d0054016240510b0f191000308070b030100075035201030481c200d0005482d144d0700d2920896a49203043c91184d44a101510b020400c40e00d800314070101d02d1441600540690390765904ea900309a2005881c034400c006820103000160343c50035001c500c00b00c0c4101004604501c4680000340781108103a074840360303c0d242c41c01d0070184200200898030b040d96000c00e50240090404021424107404201c0690400400810002a0070702c0110078000c151250305180880d41d16900f800700c40d8090208555110704d8108038400b00e03440c2c2a04044d2180a00f02038103482c2490070b075100c422141144008031044440240f440c1a0074001032428403024034240c82034295036146445155641c890301d40710205002d00001c3c0c1d4424107200f100696071045e0042828080300c1d0b940e151203000c01800700c0c0d10b4030040c400f1480c040303885080000c902c0c0c001d6800074010b150507410301c1c0c01c018030b03540070960040300658204400307c2c4101c00b220390a44a203503280c0500c000741002140c49400d40341c040b100c11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 697972976 1250 697971726 697971773
    0x70f09081204062a060c052107031d210702040e011a010201140a020306010c021e0f0103090506041103010f11071208010b0d0e030f31050a0905042a03 66
    0x590003504d9404950400b80e412201c00310b8580030484050345c4901c101c443c00c0c5003c0851180d05000c941c0c05656050244600e86c1d070400402080c0c030150f050700368601c20000b01d103800031202100407225021840d00700d02c0d1001107141c6801107950000d0202c0c0c0e030082c002005079443d121110884008844060144603080c00248400c020302c800240c60848010050280c3d0b95020000c6155640300d1003a40007001c4e030140006940030b810400c010003c12001040390b1048640600503100d03548039000b0704049070b51007801820181c980e0b903242d40800755010030307481d00f40d9600d00ca41d20fa141140d00913001d40c40980c10031903654410f039061200c0313108080c041c2c01d410f001a88004001c0311020404951a0b209450000920010f089544504500c00e65041904124011a80034200035801a0b208000c864031b000910380c001500158160090340c0b0701c0b500f0740c080403100c030410140e0300c190026503000e8428801a04034882071403078030308080c1c040c0c400380c0703094410b23001e0038000c0021401110310170725452810f1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 697974226 1250 697972976 697973027
    0x41505010c08131502070e07090b0f1c0f0b090f01030c1a04080a080a110a050607200114010e010f05030d03020c01021201180b0405040209070f0908120406 68
    0x6050a00300d518000c11540b0001059055000c141403000e0183c014503510380454841c0b0040290746442c40e000d04413144a1410200b20304600900c800f5080b59100d070304181c24840c40b00c0d42030460b81c0191010104074a480707040307040c01101e607101702d0411010b04040040d40e907500c0303418841b500d400144042610041e040040c0701050500c4d084008039004149452401c2c805461002041c0c040e950010042e0310551840b0b10800c0984800340a142800740c0d101c00e00300030b21241603030380d5001c030010260454000fa000f04082912076084070040542007030000b40940680300c10030342120001480001c09408140052001c46444540385004102008010702a1170400b000292140131007083c41c8241980001d5080c045031003074054034011404001409801d41c0d40b0441408200c0704040c2928145251003044400703443c0c544140c9010755000f0b00010880c5c0c2d20b0b4141650310003504039501c024880348000c000303030002040142d5190001103400d400e84483c507208001d40450050000040b8008101d1407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 697975476 1250 697974226 697974229
    0x80307032301060e0d0b1b13031208221203020f040f090b06040f05010e1f0f120e06060f06070b090307060501060c03020c010f2c0f01140304141c0806041505 69
    0x800a400c50380c041500030440c0070008000d070282c810b4000d074005a622340704000080c0316840800601c503644e036850710b084698030b01d00c0046444642040d10706900f000000603401141e6074a00c0001c0070091401d00500c0c1402007078118a080d000f6a10400109018402c14059409103008100b40d00c01c1c107a550f5400c060602c1801a60301c2c41174000c07e41000030800d80b000099039032203082488009488600a80d0015180c0002c0c510f012005003480416480d0040d0b1000d400b16200301c01c0d0848a240c003070b0506450315400c10026480b03140344154031032001e1004201080c090000b0b0fa00808801c0007c580d81d2107207160140c26644140c1c403070400d1000202580d408240c012980c401c00307007001d181203940305511401c00c1d103264000f210b00320140750481ca00c40b602c0c220301e1100d5200c242c0080b248024458400300044610854071040000b44030005d2007c20001001c0902d20000c800d952400c2d1076400030101044088214802c24800018018000b482114203192003005101c5200c6480460760608010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 697976726 1250 697975476 697975493
    0x303060418080a03091505011502062401120e010e0a0c0f0f0e1003060608101103060307120f050303072a0b0c07050f0d050310061b080307032301060e0d 67
    0x603d54820306841e00300f80c008000a4180a070300318030781c0d020304016558640d01b1020425048040b20710140c450800424030821144412054404000030304000e00c1500800444511050311842e01800e5110f54007200602001c1c0a214141e4441c1d600034146083e103803c111080c4e161640c4a41b00c0b1101880c418000502800010410f035100104150020346031112242d40070b085ca40c1c0058441850b000000c02c880f0030100d8034115a001100e420b021000d03850082c0031903807001b5926030398076502420301000511000e03148459880e005040740c0c055102c07941c8030301e400c3d5401201c0315000909070f00f00384190104211400480c02901002c1800550341640d1802c42d59080a40354540300400070864004115082045040445580f4241e03421403480b10b801426039001515500010014034402089030341c4134190030955460308840380c008182640d182d464185e4401b5002100b00b58a0704903142c03610448010305941d103c0152050802507141c0701c40201840800f82c04140b041c107006070107001044601 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 697977976 1250 697976726 697976737
    0x6070204020a0c02191814010521060a0c090b0a08180a080c03030403200a0221010207050a02030c0607020a1a04050d0503040302030d08010602150a060504020408030306041808 77
    0x596005a07208116034054400740c0d4007400080d4801caa840305060324000305c0c1d8000c1704446114030036500901c804080c0d00240d550303807240103540c00c0041004004915081094514071480400e450750b100039601031080c108001142d00803281522101c80d10301182d4850103c80041040d074541c00d00380344030300e01c00509001c0007401001007043c1c403c810100c2c460051202561080e40041c0b869600c060003420b01c4e4803600115019004511703200220074140c0c2170b10083d400440e049501802c85840c1ca6070030000160b040405101486405104903841c410702403000b08513241c050310003802c0101c0c0e03510400d8640000d044c1d069000340d6083c0f10f800c005865101600f0281c910f0217001d00001400000000c2f0721b405254082644943c0310360071002402000300007030054074000d5042e1500305a594000781d4107041e00b0311038030005900c8820b10880e4040704098440d0890900100412019950300004082e60420b40109850707400c00001d00199140500c0782201d01c021400024600080e15103995180b800b61 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 697979226 1250 697977976 697977979
    0xf03070806240a0e040204050d030c0c1413020a050d050702060a050a0612021e0301021c06080a030804030305071116090e0d14070f08030412080a0905030a0e150304030206061e060702 80
    0x4905004c0d4243d612074060b20013511000d8403801c0030340d6a40c2801014940c1c0c000782a904070b01000800310308800c610701d0484641001600402d441a81d01c1e42e82d90007540148540000c0100a00c80100060380501809008640c2d99004150138240035202c4421110050a9641640d02d000310030030a002e45c440c420f08000e50100c82e800f01d204aa903510246030b0001ca18034560551001801945180300b1841021145108a2041020740d03264880b040d03492200f080c028010804980c0003400003880790f0481c5a1000e01c03450300414442c440c0007820302d06441c082000702c001c0345602041c8200d00c02441415954004440140b203143c1119070054020610980000143c0000050007418400800c0c07115010540c0b1101c800d98a10b41420151403450141c040c0d41c0000c1c1800c0007050b8807003581d0203041c003c950010051b40c6000e494050a41c0c010304101c0c61290011428014400003440c4840075601c41e42c040e40140c011890b102003044844644c54640045003000b2141001a40e00c0b513001b0b56400550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 697980476 1250 697979226 697979237
    0xf2303012309010c0e1201020d050109090c0b030106021905010905060124032c03280f0e090a2013060806090c1210080d0306060806040e060f04080f03070806240a 71
    0x6d0f100e540a4130a400701c01903013a05201c00000c0c005016032000002502400d010741e0400d84800c0d5140c881d100a100d003d0040c0e1119140c0e1800010010003401c41900c00c000000302880b10b980d90303d040680c00d03071000b203080508400021a080c90120807842c0d0100600e81000341025400e803515003058800c40300171035540030903104072409500b00304480b000c0f600c007010364101d200c1304580442c00041c500420400075018000c06c6401d140102001d5650903c02092040b540e941e0307000c801d00400f1403940c000308244540089460b01500503004282941118100c0c40c28581001405012080042c00c9180102c094074100403c100c2d0460684596650580049000791074001d000d45040801d46c10254a80c01007010031130b8801d0b01588000c0c111080340e168107c2594542017004110303003154640d46140e0b042a00081d28007154154004d131b00c01c0c0724001d00703401d04031795400050a075002190041c022071a044244211031601e200d51404e145030243d49045000b00c2d041c01c4008502952682205005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 697981726 1250 697980476 697980499
    0x207030809030118240e061b0f0f0d230a09031403010602010c03110c070e040f0f0b0f1b04050409021201020c0c190f2303012309010c0e 60
    0x3507081d04404102a22840320711500744181c05c24220203448080214200c502c107917801440c0c120240641c010a0b68038402401041d41c0312504d031880341c540d40706e0060041900b00809800000818090800803454503400b60321140300c01d82e4282110385140d1100034074414404106c000d00701c2a25415403106003008003041ca0343c0a842e0580b40300000200f0304142c2c1002000218442e50305600031010300750a5507050100c41c000800d5502c80703215003010b02007241c00c18802481380e0190003031166046441000307071410240b1103440d1034001d2a2001411075022140e9018099082440340b41103400c460044002d41e07101140740d041406d10300c00e030312805000d503440d644c482040d0341d43c1445007a484200a0700a40d940c481b4908420b440b000083d1041d0310941c0c00c0d490315207042815100c0314040e10310310b04c100c1100380d041c00200c8280290744c042240000c440d81d82c150480d07403020700580006e110f9080c1c8038041d140e02d900a43d10440c00040c0310880c02d038503140c01c00481c15400f02680b01e030407509461188145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 697982976 1250 697981726 697981729
    0xd030b031009241b0c030305060111070510120504031106370b0306090102030603010e03031e100803180f060c0d0807110f06061c03121116060b0a0b09010207030809 72
    0x140754044d121301c182c20004441da02c020341c2101522500c14420313641080180c0d280c83c01503402d01090440702c1e56640c41084140040c1c10303d44030b464140340300d0b8200f07071350310031400039203401a56001c981c100d0000390810001d022120f420480950458807800482c0380c0b4003002c0d07a05030085404600c18841c01c201002c8040180300b03156029101d110000350994105241020740c05000c0c0d4000d6640301d01035071811000502040d03020060301c0c0500c6004000102c0d0901e80c12280941200160000841c02c00030000000c0d0448200010950004008043d9107a00460810081d02e0450314a038580542d03000c12665415180206040541034024244042d203034071625001c031000c81941c80d40c1e000b43c0c0300f00f80840440320800504248a000100c4403203161014000240507000d0211100401140e000118550a202190070000762103050641c02424814000300204488404560903120070390743e0101c19100d41006441c40b0050001669040c2c0303031028000000b580d5850500c805032000102180c0e90155 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 697984226 1250 697982976 697982981
    0x60c0913021204110a090908030402100e06040e0f07030e190303060b0d0f0b04090203030304030c03124b0b040605040518280f0f050d030b03100924 65
    0x4004080d2002d1a0a2809290002c910521001070503c01c0500c000f0028032041d0a02506d0369981e44a188282503881c3c070340c00c3c0254001010354490a2201c020007001d0b8a8075141c0c080c000801c5803a03090a81c40c2444c0345050512103026009204140c10204025103403080080e01001030f100084045607e000103040403002401a40c000318000c08000403c503c5c07035607881e0082e2940014458007048280980010081110b0103464025016007080c800680464018902c1c00c000c1402030a00e107090381d184c110103030102c0310407110000200d03442220110948170b40521000c0c500d046200c040034400c00c90f6141c6104102407540481c001900c0b51a050b500f9245c641100000700800b0700184407509141552192182c409071859105216000002c1405ca900e440c003400b01c10016100101c03038000c81d45500221055541c02511204140e18030f48001a404104204407150259000a003d10000c000c06060910038103100710214109151000440c089070550314002900004e24184000940c404801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 697985476 1250 697984226 697984237
    0x908030f040c181406031915021905030103030815012307120c0b0c0301050a0b0c0a05100c0f03140f07020708060c0304020109080102032a04090504051e060c091302 72
    0xc3d0014803040300b21444080e0800a60001d01d01c0780c24400780d60382414580c1d601a4003103182c8a91890940500110b01c48120400101700410000740c504494808a600449003180404000501c0000100103060b40058a03903081200f514041e000c003e15040000c00c081d11003c941c0b1407900644441d960075550b40000c4580c80c4cc1c0c001038000001102100c040c5c007840681c481921001e2a240008036800c40340030407039060345c5004207034180700c40c00c2c110a80303544d40118a803400135103e08450342c0003094040000c1e400c0c6582240021500b54242140200343c822001c800809150174090250f0405801682c4184c1c0000c030307901005015581da40c000c920306822584162440c0c0a62014050384410450046105600070b0700e031030034000e9894604500300c0c0301c121a240c06489220521a10341280e202d43d8954420090286038142511062481d00b00d83d803d0300c04540313a0748a071000708640e00300b42400c003a035070b075201c400383c0001e207080c0720340b10614852902c10a00c40c0050041c41210014140d042e0f41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 697986726 1250 697985476 697985489
    0x2040c170708130f12030507080709090203060d08030f0103021002030a0507022403040302010501081b180a020c121b0106031a0a1515110601080723090c0304060507030908030f040c 79
    0x4984d8030003030604244c0081d1428501c00040d0900001078040e41c000c0c040d8030700030991503840c86011450092480b00a42028010b40c0e40301c2c00300d262020104002c074004d580209020840c1080c2d9515501c1008094452100460705540052100005940e0420191201160151a40b1030141d09500c501000381c100c040d006051084040f061000b815415070040b03050b0b40e108401c07921450200510481c800038507400d0780c0d0b40050401c14203400351440001c110380001e4140c07400341c10544103054480c00c060740c0c000101000400480c241622443c035101d5103104415400080100c1410740d200c920f12013001041c14541c200c407ca0104003071081311741c008200c0e0200d000b01c8003103680c0c41d0280c41d082c26110349503e0340010300a038400035192401142d0141260342c0240140030b03891500c1e0300c809903c03245000d5180c01c58070b8041001800d485002c0040c1c0720303130191001540d40f850705282103421180c3c007400580c101450301d10b011002825400c2101d410510030040400c4940e52480c0c141c607001c11940082c0f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 697987976 1250 697986726 697986743
    0x1141b0427151a04050603010902130b1821060c03040302030702090a05071701081c1809060e100e2809080310090e120a020a0803011202040c17070813 66
    0x11070008500d03550b103a0a030b40b04101c4802c9500c065a0361007036240104d01803198491010401004492a50b500901101c580403440e419015079804401c0210f0b04440c80d03441d400c003400306c0c00003c14584280303079594016150403010078411404000e04d588400c01424900b0a200000204040c98000c01c1910b40d21503008144502a16105101c00060070b401d40c0c06a0102e40f14003007980001d544049038038182e071107000081c0004503c0b07101c00030f10348c1c40f00100350081c480940c0d2800c81107501c481803103000d46035003203022840704c1c9130612084541d600103200700541c0e040180c0912900005962590b00038201100c9048560341d000c2d42411250000150303556500e26090380f000400841402551050b0313000d28000b02c50554034040e4400741d8840401001d050707044070110955200c1d13054050283d00c0e145104650342c00e822944c4091503079100383c010b0082c10620580c60300843c60503026021010819241504004c01784202c400320303010024001c28140305900d40024290b0190300e1100d8409500400d18 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 697989226 1250 697987976 697987991
    0x100504060603110103020a0806150409020f04061b05060a02250609140a0b0c2a0c040b010504050105030a0b060904020d0509071205031611090103030201141b0427 71
    0x10304014101d5220441d60b104a11040c040c45601a00c02d41d400744409071503030441d9903240ca04004140e64070301c110b14405036080c04080741c11000d0340f018100c603c91100c10103a131203013000350140c02310005484c000e4031401e00f80613400000300003155130fc1d00880803c0c4050380340c05503075040301e01c85008070300010510b8001740c00d880709025280e0001001035001e03510009d07071480c103251020b4580c06a104040e0503102424042084100f00c0340c010a0103100d04c040c0c00c5003222a01401c1d2529000402c0c1520496110754001c12080c9810301c51081d0900c0e090070f011745401e141c84000380050100425504600b80e5038003101c01681c894a04955450000510465852801e80700b00001802c0546842d206132107201000328202c03c601400e0950f0580080066040c0500b889001a1224620308212144040c118010b00d564442080c1039001e51b200b80c0000c10100c00c0c040300d281d0118030040004a0342c907110b00000040f50343d0340c4220ba0555418501c543e00a8051420b805003c07a0f01403132100d035079231a000c003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 697990476 1250 697989226 697989233
    0x909050903162402070f0c06110d0e03010b060712090605130909030c0b10090510030507030b04150c050409050718121103070b070203070b0702060f0702030c03070e0106030b12070504020c100504 85
    0x6d400c00940310340c5c0313040d01450701c491040745d200003503009003c0a03900c008c4480001f1030003507818421881c0014004601020b03130001240483c0c0040c401190301c16a15990700c2101f41c2c0054400e00503001038a011410000a05c080380c01607005803084504069440d584541414854141d428a00e50400e80800e41030402c1d84040188483e28824a0203480c948000300b180030903012a18803c49801070014401903086440e40d8070082c1018000f284c1c1044088610290740301e884c0950310fa000c1701c80c0c5945403602d00c2c0a010006032200284004100028103203c1358203084940f002000303503a00d4800c40001d10310907103080c260221704008880e51600c039a19000840c0300444000345043e510a90a82e41265901c1456008600038568020350020050050140d448490070180100c11b0000302202c1704042408040790601c1c43c183c00030a02d10741e901c0010301100c0d8140c01178540300081540c41c003010500c40b19540d9110340160160368480c94000641072050300c4208000414503030540d0003008241400d01c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 697991726 1250 697990476 697990493
    0xf050c090106110f01020403020a1e0f0902030411030a0b162318030708060403230c160f060e100302040f1206050f06090604050c041203090905090316240207 69
    0xd0f80001d8800d181d0050a01481030090341c0450768090124040340c0c3c10081d90b80700c1c4042e681c01100b42e2428002c0c0008112441c241c89000034241c508006030f0f242000c2c148030640e0802c02a659002e540080003010000350880c0c02c1c035a22001464140c1512410500102e81120f511404801c01c0e5080c0106210310f903445500904103102d0702e6240180e18541a002d06840d8070852080c5285500880005030100e401000c1c220b144891448078103c1060301342d150741200ea0000054403801d5800400014100c140380e80b61040680010482c500c0028030f44500200f5680e01000407901881c0746101038020b0501a40584018210b042c001160440d1654000000c0281456040d030b1400e0900010405281c03580000034050000540001001c1d56031000380809004041d1000400e45d208110004c3d200b0034004180c8541d520998170361030140e18003160703030055440140c0444015082042400282e000d4030b0446081c4981c88094480041211400b1101100c108220100c43d030340000b412004010601 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 697992976 1250 697991726 697991747
    0x6040303090e01060309030512060a09050412031d07140d0605040311061e0a0e0708030414120d0f200703080403050d031104060e0f06040e1605090901030f050c090106 73
    0x3002c0700c900d07a681c040480684888000c00380200d1020010124181160031050741c0c000d01c0540010f40d016910081c00c000c446040b41c058450311a02c0f41c4418006074140228200c1000e070100c040a50510b400d040c0352106070510400c042d07500021003001c1680c039100310403400160001d40800c0305240c641400340000d032401c0c5400d001c0c7e0082c0c8002034808800a001c01d502c0d1041e4181080c929070320541c6640c0240401c10035007110f4810310000280d4104c082000380042c00f6004609480007d840040c8480201c04040055403030704500e2444030700300d88c418105140f0800c0ca10303065400c4075200c40c121003102000b03001803450303002c3c8000200600060f10000c1045034451012a041d034140d41504404a40c1c502700080d0801d2020001004a50b100b202840d5910000400a00a80c11110005406079105501204203000d400c02002021503218909200760360850a25078686070035600010454901404000c0190109040c02070030300004001c440c50210000d00101c40c20b586134500030744002242d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 697994226 1250 697992976 697992989
    0x304050303061804050c0d0303380604230a1715071e080a150906050901050901121209090504150e07030c03060218130b0307050402120f040305090604030309 69
    0x34803e92298411041c1c1c0740903c52134000c809456000800f404221903481e24030000c2c2e04140e12048002105040d801c00e0456030340314502d4444da08112003003c1d2a005608003ea5840b5040500013008803044801e500540d0064840c001c0707007611244000104008030a402624081c40618091541c0d41000500802ea1315800314500e2403070340d5030b40ca00300c1d24142c111074403d02d400c0150006100107809103203100c0d0007414120000c607101d080c100746140c000c0794580c8441892601e40b03c0030041e40c02c02100c1c03103024140660744542d0310360500d00c0d022884080c4601c0140810300c0400b8002c0d6040c41105044083c210600d8107121909281c01c1c40304d40302e00c002000002e000e1034898480c807a03900009040045951002c411242c00c0d03d0341d11440001c1d001030102d003000d00764921084c070160b500d50051782c0b403010005000050013810305041c18a800394a420582c001c602c1004094070382e40311440c2007031340704404d400c10500a03a03881c9021910b9009041442d50003480102d1302008041c3c00c100441e061b13500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 697995476 1250 697994226 697994239
    0x50609030327030a2a0506040605090102030c04180f020f03040c0801051501030509010b0916020f03040612050603010b04060f060e10080126031201091d030d0c0e06030405030306 78
    0x1810a0310807001600b000400000c0c3d4410481d0503280da005d140c480902c1c0c00302c12078a005d5107011100c0c6882c11968143c049846400c000c04110411006115040e0091000344c0214250b00c3d0128151040d07200758052196200d0b4031460050784411a50072550003203680000540d21101183c2607501640c2082e20119a2800e0300c00b130200d8070f00414400c03039101d10500343d200c0080301e44410054006280140c2045419500d031128000030b600d408688a00480c042c2071807100000c41100f000f8141003842e03080448170340082200f007202c10b6200f10901e1180d440f00c0e0001586403100700019005111043c4206e07082410080c1c0003950591208540e8200c48442e128034540301110000c00c05008650b000c40004188030344018418200421424410103915000c2c802e001e80340e4510031461070700f00745503545804044200510140c2c03280e021b16007030701c950341c6842c4000495000c1c1c0c1d0354880c0180307030481c0c1f4215607035901d20003400d1161809149203e000742c0207641e01c1c1842d0070520380341d50048914600890 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 697996726 1250 697995476 697995511
    0xc0f120a02101b030207050708120909090a0b040204051e0a0614060319020c03070609080403030f0c02310905010c090e1603050a0902031e0d05071113090506090303 72
    0x3142400740c908560014840030f58030400040c000c2c1c000b5048035909884a2003404c5021444080070494404115110400c9607201c920300c0c0d081000300301004000030f403103420445240000401c10b4000781d4019030b046030045250703503428131a0340c2c80e131000744240f5401840d0356040c041c0301c81007a0b00000554000c508441c0010321042d00740896840240e50002d4030750184c00c607016a05105d580038204501c152415207203821490b881c2c000036119958010790b03520100290410405070400c02c023012046142c00c10b44940d0440d5000900c1181c40910030201c3e01c0142d00489014141c140c00011507a40c00403020022400d013420404d008000d000350312400300b02040c0700840c8186554121610502d03c4103008011104840d0013100034000182c81d5092044d00e0b0000d81006a070203008460359140d2840e07100c0c10a54110581c1071400c503141c483c600c140601000f1300e40114038856141048014160b8142e06180305520310301c40140040b800180040c05070000303000f4452000720041d80205942c510442191 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 697997976 1250 697996726 697996753
    0x503151807080a0e030a0801121113061d04050d1101060f091a041107060b031e0c210a24051006031b300e032109070b0c0f120a02 57
    0x31b02c1001610400b041d1450010040795000c24034060502d0303c00e80038084c10848860100c0d62821003480c100520688a04041c81141000a1000180b281b4079100005a0816450f03140d00d07000d0000b240000c00c454007903c0c2c00700321001d402c20700c014020410245880c1d41e4508950008008418840006016040052080d403406000c2e00b40350801102c42c852601300240d440030014005016040d400d401010300e55080e000c0c0781110164049040005000c0174200c41c41040074581c503803d011001c650103a003008451a00001e0354412403984005140501c5409190303001c0b400e0a00c4103015600d41c00e00d410040043c11640708407045403c90388040c42100751040d100d926040200300315070000303448810080748100c030200050040c003800035180980c0705030386840c0c401919041101c40c081a4070019440f489003404074401d07568034180903400340542c01c155001540764011440717034261004000c0352001501d402404a610100c003500100c44006845103c0444940c100c6035641003d40203007100380e01362 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 697999226 1250 697997976 697997983
    0x90d0804090207050c120607121503032a0c0510020709020a032a0c080a1206030804080705121203190c020a0210230c07050316091b0503151807080a0e 66
    0x5c1010440070700441c1d50f40c0c1c4009c0b00e042d20f40c8201008900d071150000c40e10502060001806180039980c0c080d00460846829604240c0c3c01031011011024801940049024103055100341e8500711103920b40b11a01882c22450702107180c02c405945440003c1e40201c0340c1c1c059012000340d840c0000a9056560841070300c556240a03400c0d42401314510ba00c10400140d410b84c01011134202034104041025009044a4112415900100c0d8140c07030008040c4080382c01007201e0401040200c9940d0568220422015256100702034840000d18000c0040f5182e01c11100b18080c100f405400700b000614800d55000303694551021007a0701078043c4121248049224055004c064610f1200e01410446112403046456101d070825060b28040c0312008101d80e903052120040749800718a003412404e05210400d011614640710b05880310074948801c00d0080d800500303803503105d0003809a1103031080c045000309030f50b40c000c0c48240103d00080c9080103150394104082600480083d0001c00610203600c00303807a078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 698000476 1250 697999226 697999249
    0x9011217040e130624060206060303071e0f1403090a150e120c030a20030a02010206010e0a02160305030a0b030106120209090a14030c10060b0304020402090d0804090207050c 76
    0x242d18100c1c00035582400e016002180c4621616000030191241c10001100403000701010f4803424244008100c072582c10480c0903000201140510301d07100083d0340da030003003900c124440c40e1007031841104241480160380e8a041240c2d0070030b81861940242120042d225440501001e12030403a8000c0419000740c0105100f1504000b501c5030280c0741e1100c0d081110310029503010101c503102d04840c07420991402d10080ca5410320031a0302d200740c2e030900c4661050158034104041e0203548016203000150382e000840d1811100406c541c40b50030b0f03c1309000300001e0b100c0d05850a214240883c081c230200741c0d00c400103601c150322076401002410119001c046c01d8444910420032100d445003e0400980380134075103950031a180d441100c45c40600c3e99154080d0394002e095100098002142900c000c0506114102509465140400919007405d5076030465000c00b90000c1d01860b808241040d0039195003440d003c0d81d64000d20b520ba121662a04410040d5100300002c036000c1c007179003c008040d0f05084a40b00c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 698001726 1250 698000476 698000489
    0xf180a1526070e0402043308060c0331060c050921030405040b0415081507050316050f070c090606120207020f0409080d11030105040c0e030d18050901121704 69
    0x651511340d40c003044080d2445500c0303403462400c00c4503205085031a8080d090810803184001c81c110516000100d428018003c040c042c03941001c0040013040c000020a084214281160a1020320080c48800d010b4840905004040c03030310781140c0c2c3c05000c2e080030192100190443d042e0070b13221040405a202d01a8400c41400c06600a00041c09546402e80200b140301c80301070800a6404078040d81c107034220500340d210801c40d81210240200d80300289040395072250703503410700e00d00d507042550112180b45141c0110b1010041c000c41c54801051608c021181610b410000078511039403180b503480010004c1e807143c40040f030100410058070000324001c0c1c035042c6130010442c20314425441c0c14070000e0010000100e40800c2b0801644170a40010711555403ea43c10700e203039540760360400c0f040c0400c032a0410500c034144604c3c0020006196030000304001811011324061183c100d408081451502480d00015130110081001082c3c128102e0703900301b100c900400803074850305140310b80c0c08050b1140f0b00480c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 698002976 1250 698001726 698001749
    0x601021c05090f0604030b04020916120b0a050d0506101508060f0103090206030f060f09060d020d0201090b1804111e03310c050f180a152607 62
    0x4601035400340014100030900686a0f481c2805140e001610990060308100c5a8415100602040d400d01e2208150f02500e002031881010a03200340c00780960001c21403c0c5241d60302c58001c18031546940c1c104500810010305000c12218603454040e441c2c480c115425290725002e00d100040603403048513a40c001d81000d07125402c80340c48010034890390706000b003880b17814581c444102000507100d62005600c1001c110303042e600d03142845030421403508184800c0c18410f01c00f2906002566070381c00807414180354111020308114040d071005030b0b00f41d80640d001c3c0c0c1031201c0100e280f42085100f14104092291304075410464400b06072a05075081c00341e85400d800c9040341d01002000c01214500464001c1059412401868141b8001c0303240d20a051140d003004912a211000c200700c0e0540d10540030b80b1003120710380b103500400c502040c000341805040507509400500881d020484603405550b0b90b0a032001c08000c070f15120b200703140c0d078120840c0c80f41200181041e10054070100c0415117405030b42400a00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 698004226 1250 698002976 698003023
    0x70807080f07090b0903070503031612050324030a0203060115120203010b0f0a050403020307030303020409200313020109150521010e13020415170709090f140703080f12060102 77
    0x1130280301e07005400d00e160140320b503800110ba590780820140c40c00c0030380c1050790500400546025a00726411640e210113000d014824084040421403030010103101a160035589107403450006446c2607144100039415004020010605d05154002500c24000640705d0201c403450746003464040348824807070080104010700c10598840e1410000300340d0700a091400b2400c1c15282d80000303081c845190310480100e6400a000c10000906000b40300306528841501c404030550001c1c1c0c04054480107000040f54806084071008682c002e10b101c001601c0301703925071003000341d50705009882540041803c1180c0020350310300400e0348140b000c0003410b8071015010a0455100c0c42c031103d4420f82d001c0d9040f03034443c3c0c1b9180303004541d2801d10381050040845040782a403614031000d1003030400e025070b0031032041e8500b42145040480e44540b418070380c0c01c1e440103002c3c0c44002d0042d41e160a2a42c25000144010b10002d503941d00421110060b04014102a00c07000b03045d1209030059039103504041d4040e0b03100d5154100e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 698005476 1250 698004226 698004239
    0x4140105070f02042c0c18040804030803010e0f0606132607121e030e0f0a0e1609090225020a030c140306060a180e0c0307030302010e0d02010c0504030809010215070807080f0709 78
    0x499030411b100c9c40c41c40342000c0c2c43e6075881c01e691300246c00c01c003880d051a030708112268250f40f030040e4000c00c0545d003c51030200c07484808050b28650340101d01e4409545100b0349408587c106050450080c408241c850080e00d03041640082d90000c00103464071003c0c0502c04405076400c2e0310141034254942c5030b440c0c0401c0c0501c1031110124503c80f10b07960081c18080006040403500e0751080c840e094a26000c080c0d10507902c00030700f840d040713a00304060991050000b4042ea030403045000e0251000c004280b0f440f284c5620001c4c0483d411a000100310240c0c005000804422000d51548420740803420344440e59500e5081c008200100d1140f6800b4044540e03410903a140e00758805103541c1c0700384086d070383c01102c1503001c139180046940c003c80040c1e540300c844000e03404042c4449020556140b00900007240d01b0a4002c086001c0c030700025000ba180004d859405030b000300001600500341c21400c20051800d2000641454811503504000c00c040000080d01c82c010004400e220b032090b0345900c0b00c3c6070b050a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 698006726 1250 698005476 698005519
    0x6080f0717010e0c07060914060f0702030d020f0405031f0b04020306090402040e010902090c040501120513030f03090f0f05010f06030305030c09220e07090204140105070f02042c0c 79
    0x810004105000b000f200c0085880c44c01509003890142d01003600b0b23a41400b000701d10300030005001c542d00a10900622401c0c0d58080116445100ca0680241c1c460402001c14090b0744195401258107105030000030b903400108050420304204042810400742480c5000d02040c0d00c07080312072662081d501c40c009801803409038001e2903410090000010002042d40c0451030000050302c8141c0d02200100b0100030540e0f2003e14a0b518040c1c9520034021400c0c043c001c2000300013003000007010300c80300d10901241e45205c5c0d88411a815003152844800540341e090281403030440300010398180d420060010150000c1e4042d02c011654035949507855a5a07d284a20300c07034001c1211540c2c4608030b29000540303080000303004030082030078441c0003035a07c80500c03d1a10b40003142c4d000b007003100c1c014801040341c5581c1c100c5000310b840d021700f403581da20303441490075140d44030304090007e52103494052800420700718211a5592a40d0880000f115000d8044034942c2da2480c07040c1607a44004000600c0c000300d407440c0d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 698007976 1250 698006726 698006731
    0xa0801050405041b060e04180f020d140d05070c17070302090c0702150909010e0f0a050415020a120507030207170a050c101406060f0d0506130606080f0717010e 70
    0x11004c9014001c8452200c9090343c46550104000610700c1d504032440d8901407040150083c40354904520700c44403969824541c0c110540040d12840c450100c00e0f042c000710700701c000a03102ca501d0903a5001c03501c03100c1c060b1994100300c07416601c40c0d8981402007440303083c01d1041c0424504250003040054174503400c100c16000e0003000c1d08010001070001c1c00040e200d140906a0501c801405207460f13615000902c044488140e02001d1018000c20610078601a01500b490704141002004120740e960f500780003041d0011084140315840c40001c05074880c2d075010280c0b124803c84e0560a000c1902c07040340071000e80c0035010003e401d01680340280d00e12052820b00030710010886041a500349401d003400a424100b251411100e40e6484a8885640c1c92403070089680c402811076015080694082404100707005612950b00340b240c0e540c1c0410f5150740c4000840c800e030085910140032880c0c403440001c140090039a80b80e403085001c0800300d40c45c1800342d0945003107907010445100460386010b50112040901 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 698009226 1250 698007976 698007983
    0x32309120106050307030317160f0f181409070201020a0509010309020d0209011e06020d0509040e01320109050c0f070812010f05030d030b010207120c0b070c08060109020a080105040504 81
    0x254100003803e5202070060000460003911880a0342c121001490b00298000305189541004410130b603a50b070340c0041c03000c488001300d03103480144010364000981d0b8540c03900c4100e204808910b0800901032a032101840c2d5141d9064410409585510320241e080c2d010b06200c11000c82c0c010301c2080703020f52107540281a200d00007060f46405d001c10740c003c07c51000017078004045c0a004003641d02006802c24130110000d000520007010000d00c1408010018026001554031803502c0310b284400c41e60094100c0d0703405281016074410071950795a000e5a2a983c0140e0011000082900002d443c601e2440394921417101c001340a0f1400510003524100c951040c1c9003110750890038441d0b02c0c000340c0a02c20f00d602908041a040b0401410201018a03082c080d501c50700416003003140000c0c0c50b0740d0114891044844104208101080d1441c08044941c0182c104031200c0d4070100383e0f0340138490307242c00300d8048941c2d0006580d00c03a42c84034109000e9104001d04000450f00b00e00040216003810303806203071b02600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 698010476 1250 698009226 698009231
    0xb0a032d080a0302030105010f090608180a051c18051003150b03040f0c0509060a090b030a05100212130f080d0f0218100e0913080f070c030323091201 66
    0x300c80c0e031911840e401140094002aa000c00140032075604078412425104041c1003880341c041c43c00100408401008005000701100d2200d250010a03041150f41036603940711094509080c01220740c50001e041004c80000056500300d0310022051205102a051300d0001c4c1a0713010b200c2920009401916003802c80804481c40420f00180b001c0302580a0f41c001d901c00e008000340b5003050700b1b1881d03c048040c0c00c61485441c0c602d0130b01c0015a905132024003102c1d0300010200304200d000300000e0408020500c00340048c080c0c84030200480c5c00303a900030405e80ca00c0c800c42c01501c1c1c40303151805100354450440149852480049040881ca00c040500200c04183d000422080c001e01040e80aa80088500c07400c800d0241c1150071a070302d02426641e514512600d0b10a8054800800045c203810300a00304207500d400819494081c860340340700721141504120100b60340c91039146840c07400d449191005400003418078010050701c0460020501c3c01e803403403c030725078100f24102040041342d564a004182d425036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 698011726 1250 698010476 698010563
    0x1031709030a14010501140d060f0e0304060c020a080705060a0c05010605060d021b0303070c0b04020d0c030b150609010e0f0d06151403070602060106080711150108010b0a03 76
    0x1a81007080045241c4900c6120003c441c00c20140e0b0b09482d01a00300c0500d80c814490b0344000c0303440340c001d904072041c0c00c0000440c12450340304d000c070000c2800d034942d2010781c000040e010a00380d41003070440707007514401d80b1000d19140d0360b036094980f00d418a015841d40075034104020394040781b03d11084a40386014000004419903100c0c0010138179442214107035407460f0040703454869140700101c10509100308401841c614648414002c01c0344500c0a802407401e01040301160a545800f503551003001d030b00c41140c01c031517610307400c180c48040c00c1182d00050100c1e074440e00003000e041003804e4446241040e1100c1085442000c10000d0041e002800290000700504030300c800310301c080c0958100705881c041c0c2250000e09080c02c00242004c0f40e8081e600960260004000d0b1540c00100503044030300701d280502c1360b900d40e000700312032642080864031001c2c454540d0b451310080207880f1450480382a9070007000450034560a008000540744800342818582c10015450811702c134400101400d018680c0c1c80300c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 698012976 1250 698011726 698011729
    0x218150904090b060102011a10140c071202120a151e050a0b040606021f020901050c010c0801060f0804020a050f1206090f0c0607080412031e030b091e01031709 70
    0x480c2c0a000643c0c3c2c50b280c04060003540e5030284070780440f40e160b0b03401d107400703001e24200800c02c850b14500307450040062540ba00d00841c010841035078407980c00e500c20740e401180d9403c9152401032540009030f00c80c0b1002405011a07400c0040d24581c142c2d4454070015004080100200080000c40b40e44d8002c2c02c201a8510140000c600c1154880e209503440040d03c880594180000c41d0074540007203042d54010321140140d0030404c502c40244014441e0007581e20031400004840d5800fa90765809210360074550780c194925009644913058a50b195644101211030030411030700c01105032400b0b50032115011043c0050700700005407010f00000a4a0600300310903182c1c106291001c1103403d02003035080580d0000001406103c0e80b00101c80803501c203400c2110a8131034032140d201d00d00c1381801000000b020702007018098440707009010403071101030f000316541080c007502400c100303031080d88141c0900000495100328050341d607800c10f40f2050300c1c10144c0c1c00c5070b80740d58541071580000c025905082c000058035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 698014226 1250 698012976 698012981
    0x1802250b0a1802060714071a07030828050702120d05180604210c021314060a0b0d05040c03020a080f01050a0b0904020f0103110c010b03100218150904 66
    0x4520600c0811401e16001119104842c80000005002c100030a24040940c1d180029101000e802a00086407030440c01c4a0914040c140d40c000c490f420321400001540d10a640301400645003e601c902c9410758420000060458101807030644002c0780003e00c103080a4030354040c1c2d40c40302040c0103c681e02c81c2903903200400e903006100105c1c0d8141d159001c1021007100080c541464805403801000039041907514402d143d0000000c051065080340d440d844150f2003a00f0746c0c2c202d07a802620005800303600076410000750403800903c0d01c408045102107002824840401d108941c911202f0710300303015000124034081c02001d40280d89151610300701002607944c0c3d40040c002883c05034014030300c00c0b00d0b0492103829500010980192286031103407501613929001d01c6d056001e81d040300d03284100040600181d00903c06142207217802c280100e0184800d140543c46042d0800c01101122900418a01c0d20f0059200c0d041e1011901518460700e6026404c22241d060103012818003e64144141400410304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 698015476 1250 698014226 698014297
    0x30b030105191b0c2907030e010b0306040309061202040503150915040f030809031303051e07031a0606190c1119030b0703020c0a0f17041802 62
    0x400c00c01440d052000900144500c42004006403002203051124000c040c0c000544400c0103000310201040b10600110340d002411900c0d4070010400031345e1705000d00018010400d88603856419840c0c009905c0c080d140c0002d81c035200e143e0550f00d171f41c201400d00400b160404a0300854003c81e070380a00c00803910ba601070104406035032085110540701d28020b50468a0046501d00350328182301c80070140700218403d441c030246a5074040c20410465140c078070a051451040c00307405940c01103884400300806c1404500421000d031624000045a20446d00c0180ca0340584d21006103900ca10441038824009110303041c40e44814000d003540d09120545188400031054200e841d4002070490041504120900d5034610580b02d080e282500c1c0060048a042000c501034000030308040003842c000703184103109804907041946400c09460ba00d694600e0070040f01d044514003221412907400d00700c00c04019940544003165983e0342c0048084186d02d8910000794884121004002900c0790129103072880d0301500034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 698016726 1250 698015476 698015491
    0x50d05030c010b0a06020709020f040e25142a03040305070609380c121207020303090d111c08070f02032d1b1f0b100c03030b030105 58
    0x40d03407801c4240ca11402c450000c5101d0b849030044c00800d100a5600040c040c040d103204a8006aa42c0d0010400201078001c66015001007486901008030b940c3d20124031b0105613070181d1100e00c290406510030780e02c01c02000381c10b8000c0c00060080042c1d000250314607604c48a80282140c80d0790029604c00c0342141e100750000d40e2160701c1003408101850384500d580c3c00030501d502c4081b000c070b01644010b12aa85114640d03001c0c03000c10b150b800441e0b9401c8070881c0c041d001107108803071545420402c04002a00280624090380c003041000444081c00881200c0c442d40d00c000240206500b10481030381d020030b942204210612646056413160040390308044020241602c50b10384502c0c007440d004007101c480201030f0046400922000507000c1d01644144200c8607401c2c402c000907a5040c2c042003d5014440e1031003421280d1110310000d000300401d40b00d03030038a012004940142e000c0c000940c1038440e41c61031507400004004002e101103206444032480a4440d19000c41c1e99401200041e007501c4c400d44115 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 698017976 1250 698016726 698016733
    0xd02160b0108030319020a0e120c090606070c0308072919090b160c06050112020a0e01030f061d1b101103030406090c18050105100806030c011107050d05 67
    0x44248480340362514014071080c4002d51551504107580c54010604504083c2c8150300440c109490078000e50401c000c1200c0540b008481010104815661700300031640d00b80186403840206045003040c0c0300304c0311229041383c050a40685181c0c0c60400c1a0300003041622100c0a1540c3d40740c14042d03440700710030340b04201140c0c14254202001071030b4a2f03480040040d00a507162410300400214581400c6500090f40900c140c01d07500d41c02800c0e03035031140089004112a00d070200105101c07031400c41b100700ca82c1c02640c503400f00c40c4e00c1e083c3ea41860b80c000e0102410056810030160002009600461400d45400441c194054003c1c540e4910b0131503050101001407074140c001c6a05030401d1130000b00e00070300c5e41c5410107001e90074501c2c3e9622444054809800f86442d80c000300140802e940e81980206042424407038011840f0f040c06d40100790a0213010701c80e490001c29004914850306402d4000d16008020700100c40340c0c0401034070b00c80e603240c0c81011580a90310f0b000030783c1da42d03000a5012281c0600d028 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 698019226 1250 698017976 698018017
    0x339070317130302121005011701060602031606022b0e10090201090b0c1f02030702010c0e0f013203041103071a0304050c040903030c080105041a060d020d02 69
    0x40c00c0345910142000741907007800c0c4502024151510466402c0ba038059a00b060b104240500301400d10a4500071458040d003000000988288452484e07000f20861100800240b038907a802280c5900c00c00d807070200d82c01d00314520030020951550042000704507020000c54400500d0315070a440c035900703d460318009955044001403800c030901500b807280182000400c03c0001c0d541c0041c0c80c1018074080e030f03558018003164400902c0c5c2d00b00302d00b8001c0d4055840d0750784140e852900d0f10029500c11075204005500742030034640d0150040c0c2c0350ac0c1a01074000c1188644907220801100c03061a00b100284440200c24802001c41480f030f21000420f49110000342d80d2494203040c09806140450170090080d8000c0380d04204c621403510f41201c1c2900483d0f03010303583c4d80f102d050003480e04601000c1141d02c549441c00650800d03805da4405151010551182c44441ea694410030088902600c0346420b00f824a0340115005e07d0300302e00601c0b900b2018000181442a00410142241c11925004205082d68000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 698020476 1250 698019226 698019233
    0x706090614010911162306071b0b0c070c05060c07031406010b030f15030712060507020d140c03070b0a02031918120e09090303010617060303390703 65
    0x44034003412118509110449210301c048559209038071402c900c00b0001741c1500200107401d900f05402036100720a503040040c3c0c0004254940303c1c20799410010450f10401c0001c4145c940460b45412500301500c075400c0c4d62103401c0307503142e6844044204c2d08085010008552541c4d860050b10b400b070f03070140041c400c4c18214540508a421400d2400542d64003c500410a51a1407406c0382d13070020760040110303140d440340c3c1d00302c051081c01082d540d94140240300001c82d184029809030482d850188806101c02c0d01c1c0c0140c01e0340c1350014070340d0503000251000040a0328040000041460602c010100da05d801690b8076a00200c230070907140804200d03000030501c804580f507200e0141100e4280e90040203a005615048040b40c1d1403250000c2c00c810600814040180c0903030311807100018090300d07140d1135150001c8034544a40c001d001e0100030544814040103425042014144681c401030011440e0490710940401c81148464140300400140004401040d421070340c106601d42042008021040c21840c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 698021582 1106 698020476 698020511
    0x60b161b1a07061409070611070905010b1b0d020c19090c0206040c06030902090402190f030f021008071205090118050303090c0604030c091107060906 66
    0x10341c501c00101c4940050080611840d010032041c044030040701038101058607041c066500415090055500450030306003480a8201243c45007a550f01c5441e0a58800341c12010751443c0100700d403c200a072019030f03000d401c00508082c1c1620115841c00a683d10a0508114454004500000000d050200c0c90724080c02800006101c940c113401c1c00a5581e940a880c100e0b5a0340d408040001c0c1d0314401d129816005a005041a01a448503020000e61404c00d015864407043d80820000d40d69003030b8103400c1d00952080d4201078044001d03004102c0000c09410b03551040c050000204800300b5480b40804c00702c04194400010300f030b114000201d0062030050007140b03081c8034000f400e43c2800b5000002d10320490301c03c011a2a000701180a00ca10b6000c1c603c80205010700c007003000d00185030150440c09c2c042d00d04002543c00c144188e103440c016502c0c105416170b556566011030082803510324 = true := by decide +kernel

theorem cover : BRFrame.Cov 697841726 698021582 := by
  have h0 := BRFrame.cov_init 697841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 697841726 ≤ n) (h2 : n < 698021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
