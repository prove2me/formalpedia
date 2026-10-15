-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4282
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:07:01.046008+00:00
-- url     : https://prove2.me/submissions/d609aef4-b95f-4b4f-bab3-a8f5bb513998

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 769964028 ≤ n < 770143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 769965278 1250 769964028 769964053
    0x40f0803010f090509010b0901030f050a230709020a0504030818031203070806040c020c010f03020f03040311280f03051c0b1507080f0c21070204050a021603080702 72
    0x46000740402c108440c4598100210b120403210041c1a0880b940e01d81040d841170760b200c0c0c0d00703000d044a4004c0c528158040a604095040c032490080051400502c0301188200c1000941d00c20340c0d02d80320008907104161110009022803040070455004227005102c20000207101000802002a84000e8180900a204042460840155a60740c0001004000c00000503800300c01194043d104940c21f021801e04c006001e515811124800750400c00c01c26004184540030f5011660820000f905155a07407800e824010505034000300c18412034003c00d17a491503048007502c41c00d5080f20303c44111b00342451696a4441c00381200002c2181440018450400b450f04100703000001c0203400383d030100b951841c1740c040000113000300c803242c05014024442103010401480681c0c002004440d02c20b60344000d010205484d0503a001000b014192081342182e0340c800841020305090b0780700380c07028061a00d803815410140c3c0a40780180692404001940700441c0c1b02c0d4104030b4105a40e801a80c3c2d10f2400035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 769966528 1250 769965278 769965293
    0xc100201061a180636011413030221070b07170f0409090311010216060605040c05030a0902010e03030c030a0e0d11010e0a0914091506030a061e020d0507120b0a050603040f 75
    0xc13042172031501050400400c03540c0088046040402c0c8051040c43c0007a50704c031f062002c44141c000a401000c000480c42031090b02c464403206e1034001c0104803403032f541e0b4401c02d50f61554446803081320084034203900c20309503110350420740e4245921800880d00702814030201000034007011009908020116001001c5c0c24000c3c4001c01500842400408508600d03040ca88255002c40c1c0c40700b401070707180071001a592540312041d240c12440148004c1802c40841c00120764415402c114a5814000041e0025503880000001c000070031154850391807041c1400200000d507140d60780041c002040c001c1011803158401e4000402c601002402a401c880c9c650f414a000c55034069000f03c0c1c040c480506102e40008100416040004483e015460f90f01d402c2c004241c4401c459040140000e0f00d4200701819485102c102c20300c6290828070840d16044160402c401805007a03404801040d40c01166030440322460040448040d006810000d52500d0081440503651000b0007c1c1c5183d501c02440e200021080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 769967778 1250 769966528 769966597
    0x21b0c0a06050d15240503070c030c080d06061d01180306051b04060201020a08092d1507030912020f1b030106150903020312040f0302060703020c100201061a1806 71
    0x18843d917400400c40c00081e080a00301066110051000c02d00c10004400d51244180d40780c0da81c185885034611038585070600441c010f28800c40c80301820724601240307043c1c1c050481400d4489030f1b1564111840750340e00550307160307151020070820380c0617401d070038400f03e04950001d5030001042801c04041031103054a00007650000c0d005080141d40004541c40c103a036100f1400b0382c0081d07529028201540d4490503003a003842484890041d000b00034401c0030701140003446442580c4c2007030f1900c00321628000c0e01c000e000b8101d1a0048070940c81c409030003401d1510000c0c202c100210f00700e00900c220051540c407202452115400706601d0340d00c5260100b51120200520350840c2840e0311040916800c510406050001034442c84c201e55406000c100306410b01052050110303501601e46035a100d41906003281404900d035a903a8008900c81c129515144d415440102100e800100c0d0420042c0e030f00c40105a2445031a024035460f4800c031170f901c00b007803a0500087c64a404040103080070b0054410711402400e48 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 769969028 1250 769967778 769967789
    0x6160c02030a14120301050901172104230108040605150a0f03050114100302012118050d020c18070e03060403120c09050d0b220501021b0c0a06050d15 66
    0x307141d04040c0f0220204070f641007655680b1034160442d07042c400403d048500501c9009440000d40104080c040130520540035214181c13203807400d000990007a80e02041d8454410f80056a441021140c1e170404d00c03540442003100160340d0002180c07610f40706c41010300b9015000c4008841020b400034a141e41e030741520001010480c40103c4000e141d410481d0031207203c05400b000c0007420798200001031080700940b02c15640e0900b0541521031a0706c400c0c000c2c682c01307207050810451805941010000ca00340003000c0b19485442121940309030384d20201d07103540c072071100700b40c010040e0f201407a0b086d00104c41e4158055514902020120384080000380b4120041ea41070340401d81d81d03040c00548050b58000c07507414100034202041940e01e010041803440455800c0504441c81c000c020910038058008070880102d00182090245c030050304105000f540213500d410081d039034000340000d1030b040c04100041052002841002181d10b040c0742510642e0210010086140c0c2e02d0300305208488030420604042d10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 769970278 1250 769969028 769969043
    0xb0a0b0c150114060304120201061206020c0c0a0f030605060d061404121403010b0d1d03040e06091512120d0506210c060a0c0210032c06160c02030a 65
    0x1518550110071110043c2c218900d140d0074600003039401e44400003240c1e001039103d0300c1780c00c00846945d0101d004020640007000c805242d06040070074004240c014111100000b401e9691070b8520404002d40e005282c400c0c2c0e0320b03804801604201003269540140e902c070710040c05800d1007241350780d1218221030100000a8012080c40c06001c02d00541d1500c0508a0f191424024004c0034a01ca4203500c90005100d0340b4016280001d81c40a9480140c00400601070f128100d1101034000003940c40e01d9410600500340c05840450009045281c4203d07810f00a83e9100b00d81ca4644444405000c2403012820780040070344031318101014441301e45002403100401074000020581400340800440d035403081d405298404080c1200503c0e14404212401c07004803c464007075417042c0c0e05a09176103061400710003075480442c00100850517505508401444c43e4000a0f4550002c103d00b130b4180c4100080300c40007120790003040011801c000190300401000200c8c20a0565440c2c0d560000f0b2030003089400407100304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 769971528 1250 769970278 769970293
    0x302070f0b1803030106081626150901030c170a1e020108060f09060f0a0e040605060109060c030801061b05030705010e0d0f1d0d050601060305010311061c0b0a0b0c 72
    0x12030606412220340740c030b0480a14619454008010150321010f0601f01d0300400001e0100e0003640551004494000c240d81002d490382c1d1b40d0b41050501c01c004850b800301200c1c0051000c52680b8041544a050b0380d4881619101e02d41050f8070b44420051419141d1030038441c00c5500c40c0440c12900e658520549400d0f00320204070b4483c40010800480036201034020300c0340708010280f41d940d00e02901d40c03149040e140d4030000c41c10200040c80d44070b441d60200c0841a9200107100c07e10545d500414454003007078907284030840c1d8488080700d03000b41c12207000c3d0000741e2000040c8403c91062120302c0414140c0c100c0b800e9503e00c25120700b03045a01110302201c0e02c0e95038160122035280c05200d00e000780d00d81c5040400032450400005050b084007001b50015403000d104143c80d165448044450026400c04110f510968480c01e001d0000c180032300040e0740060b031100c2c050f4101c0c174014007261b100140c00321103003042c1c43c60760300203d01820403941c00316444014684c000c0b03940c0319072401034901d90040000a1104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 769972778 1250 769971528 769971541
    0x406030b010302090d0b04030e0d0302010905070f03020907030e0a02280524030c121315270614071d03120901050c030c0604030f18081c0302070f0b 65
    0x121011030114506250060005084560382c181ca180c1400e40c00501512456440d458111ba0040a90683c0340d845214012003405040d070550061046078420021200010346600040d00692450700c0003d5012000d10000394040344a9000f00002d011244203d5041545660010303d0000c5e00b01075100321005880c0d40302c40c0302075059101100801c03040d41c1000101c0301aa6030000e100300d0018a40d030810800202080c001100c600032500e00c403104c4a2000300d582000600c4c40e803d0303200c0d80000e546104061028000c07a407803038403034002d00c840d400c039044c01152400b10840304a01d015030000d4900e107a90f6012a0741120000c9101c0e407040811355070300300ba129a030a5104402e0b58404210301d02a502038117461601a08850880f000d617035090911a407560421100f440c0b85201e0180130b584140034090034401099000701260742c941e1026226010003c6a071400c002d80c1103c607105070401030380448071900328610108a82e241a103003601d40949401c20544415465041d2503000701c07070b612416400c0000c5d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 769974028 1250 769972778 769972781
    0x604030503090c01090f0b0703020c060c01020c10020c0601051216061e020c0a0b09060c072303030702010207061823041b051812010504050c09010504061206021b03030c040603 77
    0x3d0088003400c08040441c188840c15441a4050244d0161404002000c0003414000c101c02030500c00c0c028400da554038200c4100c01d01035044181c4d900e203144913074500040398521500a1390b0741c0710351a03001404a80c0c0ba00c420807800160040c0140d007140200002030b42c110890841420203003a841d02c0e12222846500e0f02c0505515820440d901107402c9105030300c440e60350301107011044500003a055602c9142e50780000d0205d01c540b03a034400051240311710009007407104000c00224005040300c407030b900d00d08220a0603200d2103500b034000c2c01a00000340c2845014042c0080f9860fa42054910b480c030a41c580c41c2c07003031000500001104002d080064001c0c2c003841c0501402e0304191703001558510120a0746400780c00d40c0100034510b00310880c3c80c0400308083d00c800682a181c040c02e08028401810a4145581c0b110b440e41d5825000d82c100100215290500d0301443d8120354841c5c036902070600341c1b42c030780e8030094014400c08900c917018500003030720b442001c00103075004626031320303c0c2690340745020800360 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 769975278 1250 769974028 769974043
    0x1204060b01090501020a2102010e15191404030807020115060c0b072606030c0d0b1b3a0603051c021b0f150a0512060f210c03060403050309 61
    0x2411507100340076207000203078200e00c41e080300b1f607880c000320b400b031100b9030816800340151b442407103101c3c801c16030071240e181d9100c500300307009440020310101c074264101044d4055645c01e5115520961140005c0b9000a1140000e01d6000103140300008240c100f03030011040c040c87c03a80c05400003408418507902031007030710340f11113410001c5801c20490428180702c0c1c2001c051031904541c40b0a01c014000159951014000201032600007085501755071b2207840c00050b6410260307800358032409000740d8a005c00103400100c41d6014008150308500c2c030314011107400d4103200c2c203403407400c4209503041d5a501c00c130450060702d014521172800b5054800c4141d03042c24650745c030551303a8070031980407070304107030350403041c0ca40c00c1901050680360200c90b1000640459094148402d444616100001c1c01e0381441c0e900c5000f078443c4512020804400b030300c510b002c00c01580424250140c0c07105d4282c0038988800018004030070820792031810381d1103c24802c0e00203410940101c5040e400f1500c004100000c0385014000365 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 769976528 1250 769975278 769975289
    0xc270b1606050a2f0d060b030f180322090c08060108130f122c030f120f160f150b0108090a0201230d02090411030c0d0504081204060b0109 61
    0xc0203100f40303c09150000803a510140302e11000008004d4410903000c0b07044640480c2c0840042c00031942c0c601c829142580300b190b82e048032510003408105003038844480101140c820400840c1454240c0240c1c2105825410041c0b400310602c8200140041c0700d4002e541c0503524544910303640703240c0f20b0005040303141e00528a0122604007448880041d41c210800c202e0580c2000030300b40c800c030508005840c071010500004201c000d4440c50301802280405070700c0c0940d8030980a5a2003400c00e038032096560710b084c25190b43d1458043c08004901a2210082c100d00e620307050a540600c0c2103500e40007001e480d4003505480000006040030311280c4030b806400201c44081c40c001000f45001401c1c1510741c00c0d1503900a0401c1020b0205082060280e100c20020451001541d6a075140500a24009600c0901514016801c5c0104c51403201e080d041580d101e200e80081c0c040ca444050407880c0d0003003070020000c80b0b45d402c00384281c185405010907278038440c51142c18000752081e2807030000f6080d50881d5000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 769977778 1250 769976528 769976531
    0x3200a0f1a04050a12050c0312060f100816020c0a03050105010518040b040f2111100c0c1e06050a0506210c12010b09091b01030c270b1606050a 63
    0x30b100004500040d810501c1350860303086050195070032811160b40c840c001c1714500b148000320b040c501903e190041d803801104121784401c495000c840500c5a9180524008408240b0100019041185c00c01400022038414410391b040444004001600440290010341d1030740e548400603c009c0c14000302007050200d1000320260203290690300e6141d103140052008207031820228480c820800c03240d82c0b42c600016400340c0207018010001004150100d0410303201001e10900c01c0a401082c0e00b4440c4580d80c03e400d42e20000c0081c0d240c3c84400074110521680f010036070030038503450041041403040600030b84c40a1400305442c142241000301242803650318601301160325041804190000130480c0484000352180344281d0041842280184407003101039070070007160f80c100107900401103404040070001da02c0c01396111550500440c1244e41a00911010882c00e50218500e05050404900315410a249143d07030a80c80e0003020f403da4010821142c00d90721046401003c019050203000da00c440f101c1e00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 769979028 1250 769977778 769977781
    0x1f09021201021309061a30160305100e070c1b060306180c0f030b03030405030a060902030609011803080c0c0d120e0606130207170c0c15090a0303200a0f1a 68
    0x5202107184511101075031505401e480007c0540101e80d103544c0c0130021800058603903c0c040403c0c0624000011040340000d00d00710024000b00504c40562060f1903000403a141140c0e038001c826901030400039009c1d81d000750f0000003c5401e9a554130702030040c1200ea54045400b902c0d103040d90300e5641c1301c816002c05140c106500d8400d0550300181c504d580e44141e140115010203040301003415480b076500055014060b00d8064401d100468110020951003070b002c403981a070340d20f0440c80c00c80310001100c5410001c240310003000300703101e815801d030440f5080e03501c681780044444001346070403e1f0722803410101d80011b960003052070203845455444541c14019180070f142c0f03540098800c04102030b00e012265404120301042c41319884009002691400000b43d417107480b20403c540da0b1f105095001e11a5415040d140d6100e500502a90803600c00030304450910b6086072b034141c1e1903130418200d00c03242c1544900840c0c4011010451254107a00400740a040c0c500d040c1001d030b5502414811496400e4900e50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 769980278 1250 769979028 769979069
    0x10060905180609060f0306041a010f0e160e090f0f01081603061515052203020603190b060d0218030105060105040303051e030a1d1f0902120102130906 66
    0x1410380d07002000302c4240c943c5540f6140080d44070020000695050700c2000b0800041169040c03840a06000514100400e030b80e81e1403001c038070b00995018081c6907104c4074020901500c1c07001c14030300d80100f5509180c0740591280c40483e500c05403c9030842d07007408400050000c4041072409440c003500c2078101038003071a4260543d0403030100341c3d80301c014005560342d407101e0407596140c260391014000040038180b4800c1c080400600c0c40d000505c01850400c600440a90300c1c0c0c1010180c2422a40c0c00791046003960b0743c0707030541c00210381c0c00c404004000391100201c9409035034450082005042d01e98005854040c7d01c1701040142d40644100b0340240c1c508424050662b8002e8282c400300c9a240c500603696103000344c419101c01c1e0003e007000d61900d6003c0300b032000351066504100328ac401000200314601c540ea00c01603503a40c08184044c8003100c1400701c1c2011500c1030303030002598075001a0130300004090b240e1095089074822280c075407e0540012007800010b045028240080c084c4034852880c1003000c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 769981528 1250 769980278 769980319
    0x3140a15151e03140d0e030105060112090f020301050106050d06050901030209130809030727090c050d0c0503060c190e01082206060e073903020a0b10060905 69
    0x40c01080d080040700b800400d00d9050800d042800745920042c191240e0205503a1580d54224203d5140041800300400c40c0e65404c052203002c1c4a03d005a49160f20009440070075002081461825a1905400c00744080035890902486008103072503514240c1d0b481c2102261812500c203a000284200d0001c801000507035a001d690a070010103400317411541c1c120600d0045041c3c800c6001c401d8260007480380006040c009504148060104010300c030030314000c0802c005080700c50045c00108100c000040620a900301004103030f105a202d84550001d298403070000034986402200e07010701200c000121040c110400401042c00c101c1541002c0c6441c5414100207400d42c02e0050401d02182d0340c030030b503881e000b6a51190a04410f500020104045a02e4a00b000c14021040383e0600c0402c0c00c0c0c60190310200c891601c1d1212000300030344020f040c03400d42e03990403966101040c1b040d01148280c161110104003c08241401130042d0070402c90000e1070304c100901041e00780c0c3c5c0003074400d02341c48500e02c0b501c1a46 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 769982778 1250 769981528 769981571
    0x5030901050f04030b0f010302130b01090315140a0617061306020a20070806090c011403070509150306100f020a020904021210050a15060507030e040603140a15 70
    0x2401c0c442d8a90020311070a4120340180d1388064800c0e001c48050103002d1480403242e6040e2030090f103c000c0100182d40205065a2840d421700380015541d0300204085400710708807083c2d0460001000c0303070b0303440800c405c06e19101d400c2d40c3c44a40250748403070070041550b40f0326005000c40c444c400501058500b400c1015007400c00803a014002507000641031b002d0301c0c800c00802c04e1040d00e038401c8a90500e0000b0446941c0c1005029891841c820300700030820003c0005140890450141c6d50410701a6034203017000104d400207400e441c244001402802469503803042604694508110959240d2500718200841200c122510009001e00000e0b00501d482e400728070341c4034064040e1000e0340b450f00d542c0302044500481c140700e102c840c042c40248603c0948607400c05070194010308404c0c0816008410600c01c0b5040510410b00401c81c10403000340042e006012001d03034200c0091000420035541d031110b041c904d07083e1740d0811b00b03504241c0c4108100300140c900810400c01518007044980060310f52100f64901 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 769984028 1250 769982778 769982797
    0x7050a0507060b09160e03070b09151b0d0f05040605070237030c0806061008151e10030e06060f0f04020c010902010f02010e030f070503071b1805040503 67
    0x5000940c07005100154000120080020b4140c400700c1c40c2c900102c22a000b171000c0c05000107950450302c080240b4002072801c00303586031000b4052400701d000c02004494094101d6648400c002071040d5a5815a2109080c0c3c1c0b540d51031018090740074a6200081079040345080903010711605100902c0805d40c08800e955190303a0603208540040032940d82055148140c2c641204141f02800c000c800400c080e050140c2100d100d0a40114455200d43d212070300c4405c1140c10320f4014550154400d15075210b00861750b0070002c803039800038502c00020702007204040100c010300280c0260080c01011800e05082c8142c0360303c41c6280411140007190545501c800300a40060312071410340301c0e001d0300c5594081007188142d100038404c56440c3d08000e8600c1c0607041c900d8003640418003422542107460f0040c0a00c50000d813502c1d02540c0703031030040041070b005034008180c15038180c4811301040300021001d845481c034510f6411200707020b02c1e04c1c003c0c0c044551600079202440303050515050100280c40001903c0380c0c1c90 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 769985278 1250 769984028 769984037
    0xe0111071202040b13090602090301060b040312050307090305061006090905071d040f0218030622030305040c03060507020106050310020703021b0d15091b2d091a120607050a 76
    0xc180400560b1034244120f2075507040d450802e06c00708100e2207034010f1103004002d600a00003103035154440c01190059110140440d8140c10074404d0080c45180151382c01021750800e00711480d1242c45032464182c01302c90f00c54244038006800d100ea17a030011079060081140d800140306600d48564000d08040300006481582c00038010280001e07516a00207808030b2910340303c11520b444590401d9030f038001c034920000b8041d010b01030114030041c909001010000c08010711070481004a40e90032401004020800c0d12411100400440002c40030301420340502c20303560010894900745402c241c1031181c0d1151408040d803041204000094001c285402020f91021041c10030100c90f102043e00380c3c4041400500000010540c814540c0066004c1c2e03102c41d00944800a10242d00d582c00081e5500d90f0043d0302c0000015403040141e2514075590320602841005074101055513140d0444c19500b1a0034a03600b203075110704450642e0b084c103980040b40d034221207008110604000101504502c00c2034240030412 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 769986528 1250 769985278 769985291
    0x90e0307030f14070309051509060313020307030605180c0316031b1a07060606080f0c03060117070e1804030f0f090b040608010501030513080d1a040c0e011107120204 73
    0x2e0f405209098809256880c80701d56400841ca0002d08115150240030f01c54509850b800b41042d52480c244c0d800368601814036807440c0c5910b0301010640030100022637142c818240003100003029401220300a85198102c04000802c41c40a41d0800102d0104503010394084a440460000030390704001c101c82c1c1103c2184031030207600c10800d1222031583c1000f10f41403c514a02c80107003100d40001c10119001d4907040296036140c140450b840f10303060b21907021010010010850729044040119004103050405081e501c490103024026041c0c104c1d440e4021410366a200c04180c240101100c18082a9000485051406a4014240d0000005401d007000341d2006c0d28003503075001e002c00300007800c48855820744890780c51100504400e030901505000a051002060380600d86c1c20040c80c0c0c89500140c0142071034517030000703000200304140d41e03c4903090400c40101d120380c1f04c0340302c1d107010706078603a9400b600900ca07840054410307400c00141104591141c103042010090500a502107540e0484011618 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 769987778 1250 769986528 769986557
    0x608070b490e120a1e020c01110109020d1203060806090d14070b040803010f0803070f0303020f04051c0506062d0d12020105070906020111030105090606040f0602010213090e030703 79
    0x1c0040c6070b111407030340c418034124188044402c4054000b019055440c0e51094030701d0b01c60402c4403010f8080030341c050391040c0d0484100d98003a03c0f8041c2d07111041d03400022030201a8000030052448520f0036104000d0b9060125503040e40341c084d4201802985005000b642002003c25658100c0e80e000b0004106128941340c100c4041001110400d035041601920b2a0500741003480c1503510038402c01600084556000881c0000401556102600103d4242c0b141c3c0098130160702a6104c40c1c0300c0c0050304030810006c0b0702e03544c400c00b4220040702246090f5600c02568588140f4101c409000705106250105411000c0041a8165581c03005003035407034405500b0300b0010a02035032050320010418400100381ca000d0650551207644959040c0c0d0740c4500003136465609900301e80880c502004c00c030b02d0800060103e400c1a4141130341064015242c11302c2c0c00e6581d040e81000020b1500b0510043c3d4000800900100c8003800e500003501001c1010440440c000300712a40e2841058802410711420400300d02c00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 769989028 1250 769987778 769987781
    0x501060c1e0305040e040305040501032a0e1302070614060402090a0b09010309080a02011b08092808070b040b0c04061707032901030e0c220608070b49 66
    0x20490f9005c8000c03203003410700d0050015002030041500203450b0075071080d841840300e440500c04001030101c04025611b00c3c9030071034040161113000e641004030152003942c582d07198070041c03403145d008500c00240c00441c00702c2c85003c40c00c080d0046115600500c00c3d90b4aa49d24042c14504a4811400541e82c4010700c82c01a005041020400b8200c1d110224080003481c5d01900704a29016a2206050072181c0c0d20f401599139800503a0100d00b190301151040b00300455403007201e400790030400c3c00b200001509a0384d012199200720340848010a07054140030401691282d99608660b04071003107810039043c03040060403000703001d6000300300703080801c0480c6101e802580803c3c80e00550080d982489145000d103048200040e80c21540024034100008030078030380c08115420310340b170300420400d41c04900003079080c0c20b03104840240400c0d595070100040c0a55003080144010710320b80f40031a4640124a00f9015158181c9e0100030083d20030050484170004008a0341198200d0074483d94840c07000c9250180 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 769990278 1250 769989028 769989037
    0x30f0d0e1f3c0f17151804030207170114070c020117101419050d03090e0106090620060a0f0f02042d0e01050904061b0c0302010501060c1e0305 63
    0xd902e04000c2e4158010a58008038000e096940c0340c807144010030440c0003c030f034028120301d2107803210800040030031005912075010100c103040c01480f0b0701001d401d401040c8a00c400c10340f01280907904c203030010040c1c19006845040c01c0443d81000300400642d44080d55035060b4001e200344d0400c40301c0b11302c001c11a80207015882120881c0d8202c14900e00e03101541c5101041c542c05000204c0c03d03a200c00024501d00715440f4a0a010a0b4000f400e010b86404140801c50154800032030501081860108000428800903402040f032507448003189803610b08080c00b10070402482c80f0102c008040000d82242c4009456a040554140002180c9031314104d8000200064019002c00300d00020f000110481c42001071a40901c242c0150f01700030101c500703800e13684030840c49040da5001130030004219500d4a811040d600c680110307070214003808802c9090409a01001c5804c000c81d214455050034594244259805003506d42855405210702e500d40003031424140308a0b00da00000780c0b10400070544607800f900d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 769991528 1250 769990278 769990337
    0xe0f06151210090b0c090a05130207021201240308030609090309100503010e01092a0c0237140609040219110f01020306101805030f0d0e1f 61
    0x140c002e4408401141c0140c40c118000369980b900860200d1289061082112100e0000078000d07c0f000780f50400707010114403201017000481d5824840c850140e22101c140c802c84091300d200028010040c0c02c40e0000e80320030344c00c0c148600c1d8a005000d2000440050850360400d808807800f40300d965603842c00f94990712403003094503042650110016000b0741c02c1070265050b00d8941e107180c04a40e132900e00800850300c41644178a441f140ea98401304140601900304155520ba42ca480000c4e03920303a0300460380c0c0200b000a00b40034a500c01c40390004400200f40600600e110300850108030389d203071070761503440041c440d44001d110f104002042e214507605c55048a042c48021440a0503a001e5440d001d4000b400313190784154603001c0d5140c1c90080500604c01c80303208803c014004400324604810407100128004002e01c0f901c0400d03803010036544d904114920085402600400402d0b5000c4801089103d513450788074003901e0160b551101c5150ba081204407051070600d06030ba400c85005450544590190214 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 769992778 1250 769991528 769991533
    0x61207170102040503060105031507050304031b030809010507080f18030d060e010303020d0927020d0f020a2606060708161a0114090a0e010915020408010e0f061512 72
    0xc80960601034018100f01c81c2d00f02c0030381c1d91a81ea140107041d02e400c1403018024008ca07002c0d00046000f070148015540090080c5001c2210880f40d08803000865625541540840c50503802c0210341c407003d004043e401556450110300c982040c05003480881005041a80b2018048000204016080056802d4011018030502c1010b540f817588071b42c0c2480a01003030f0f0050166000c1c036004580100740810407501500d1141204a4610f50f0348143c1e1102100c8821915400b0000c4901ca0001400384202c85028084c005980324141c0c00041e081002d403101d54500000f032524071208140c07804000c0c9030b02c00c10556960b5610401454440d00703a00c900043d117402900d0030351640b4203000090300e10780004070042c081c00e0001c2c0d80751602003d02020524419030301c180100002045030b00250840d110707034110032001240f2a0340554500341e07030052942c608a00d90303a022400b04000c4009004840111324043c02603d810503126541c42d4031003c0050070f40a015140320590b002548650092145505c211000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 769994028 1250 769992778 769992809
    0x61106242d031203010905040618050706030f0e0613020628090b09130906021c15060504150503060f060f13061b060911150c0f15061207 60
    0x8901c001000d5002a071045441c500c0c101151400d002a9414210402c0da01450960303107407200c440050400103004403811a100c2d0003640c2c0c0c41100e40180200144070b80c0280c41070604000000b8201d5142110b007004031801e02c8401e85280501003a2560000e41d80620b0b050b08070560700215080e40300700000101106c180140c06002c8102140405d03d64091541d03481d2501541d072004503141e400350704100e0780d10400b41c0703444d0101400550f000782e0003588148005030902d0407030440c1c2030289001001c400401511247d101051a000700000070103080d03241800f504040c03c00324003078101903900c4c0541c800e200c0000007290055589100d1030085410051000366a102051840c2885d80c01260003103202000d05d89012440794080d0150a07125810b04900e4440c0752443d407140c002400c030219040d41d100381c600c9501c41060b1560003104500c00d4004940c140e039050b010390081e180c80611034103011140c1104c40c2c4a0150383c1d1240600da00100d08a4a48150a80c10411141032a40582c401074a020f804807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 769995278 1250 769994028 769994059
    0x110901081509190c020703020a050910030503160614091203040f20011b051917210f0127020d1a010f0908210c030d051006110624 57
    0xca0400020105101204c074640042e40d0b5100c4a000007940400003036001d0049080403440d1651020000010f15000303a82e9460715400c1d039114015100d0741081500000007800303040c1c05801e50821801c0c2c1202c0192414501503900c2d02c45800184484032000000319060023280914407425079003103c181034410741c0c24034441e07520301190031400d40802c40b2079242036124121a00401a81d07900300c0d02504404080c00d895106030540d1440c115181030070080c15070011140c50001d05018090394001015200318210140307400c1e9001400e006d5480c40390001031000e040040120490010484040000c8200c7ca5078100040c1c0541c0d201071074090b15004203520401a42c0f02c90345a403034000e803145015189a00c108581030480e90280d04240c0e4440300204140d44c040d07821074111642c0051000c0d0a00852801e01d6045900800c10f10900716140e006001c0f0203c0b42100744801048541010300312421010312003503e4640040c0548501400300c4010a42070f100000c840c00c00d00700c0209407030201072900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 769996528 1250 769995278 769995301
    0x1808010b0108011e0b0307020a0f05070e09030a050d090c030609060516050f030606070f1202011505040207020d1106040f1d0f09060a05041b1409060103110901081509 73
    0x3151481d00082c40c00c400098020b480071100d001d0031089041c160042818005032241070361000e0080d10840c4506004a03001c503000c64400e258452180e00507002940c0740030304480090310042d048400b0380c0c00c100b040d186030741e0b003040407280310000040001c0391403a0075050001c0007070901c3c0c0c07000e0082d9050410713403002c000700359022910440b60602d40003458006800100d07102e004007041d40d149400200080380c55441c100c000b030216144501428a490130b020365624800e4422889a030740980e44a11149070b1021407000144058001a24110b0404019800148199140800c00303442c4035030380f002e0582c00da1210011900900103210030815941d65071180c44074405031040c0e028244840c02008590403842e04151603014001c800000d02c07088d00d40d8903e06005150242003203418000300006004041310014941c4014003000e8070900421050301d042c00340452006028034101840e01d916140044c214005170754072010203207080c2606035100ea455404108454101035030284062041054440e01c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 769997778 1250 769996528 769996541
    0x31110020a020307150605010909200a02031918050d060e1e0601050301060608041401141501020c0306040b0127060f0303120501030c060507080918010510081006080403180801 77
    0x1701c0d00740d072170405c20741c9098044170024000c04d400900551404c11148009400035041c41144c1c86c0d200420b0440c2d030750040e8040d4403102c1d41c1005a00041041c0d413004070238030f5001001c1042800c1840310072241601d81c1c45400c0c1c8c1c45c060207110342c21600c0390000307120440d4031640641030b00408807001141102e104618848036698010130a02c14400041000d04040c01454112640760303c4030702541e1078030b555050315607040c4241d006556586d501204040c6c22050540d5004400116503080107400300b1000a00b4031900144083c0a03a02000901c8002512542d034141101e01e0380ca600b0505121094210b06401100120394482505040300850002d1192090030f048a20940790000c91842d964680c0042d19802d1001a04141d01e80702c0404ca46409a0000c1003002d04c5840c0c03061a00c940d0400040348030410504400030000600f005021a0510700000070601c651414001c07004d29042605c6e01c80b20101d402420100182c010125040500424005112801540380300b42216295900280245234 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 769999028 1250 769997778 769997783
    0x91b07120e0907120c031a04020a1202180406151d0a030f140c03160510050f030a060303110a1509050a02030319031a0904020405070509041e0b100c031110020a020307 73
    0x90600421031086c02480786d10028000d41c2c80c5005040000340410009420505200d401d1101456501e102c40b5103500c014402d80709801a402c0740000d810040c08210740ca25009010301450180c6c009890a4020541005460451182005101803c00490072176035241d40010320b01c40d80300e04080d04010002c0b840030b550154000440790092545c03020156120702051511110101450040c001800c0c00e000200c00c540441c02c0051814a4409003c061540111890b0049580c2c50200f03004241c0e0000300c208855400c24020203060025856440708000746800e80340607550f407850102e0821070140b009410702c640003816241c230360f8428802005000300a41940d00040e00d016000d002e004614440c903079040501a2007410240c0d102e50070b0200501f409050041400350a12116000d613036107018500030808003e1513a1000e035044641001a52a2000d2583c401d095400310300241c203074043c903030525254061038003051826100486c0c40c1880013080030642c41a0000504070711107a000001044a1032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 770000278 1250 769999028 769999031
    0xc03070b091906200c0a27110417071a0c120307141602030709060911030f1315020703030504020f180703021b0f0c091b07120e090712 59
    0x18904104007042045004070000314a000c0200c2100b0304d00d520802030b000101e2012128090150313000140c8400c500d51000384070014002c402900b8801407c002c0c803800c1180c48060100c40e030081625900c50143d80980604120030a0004100420401003100103112140208240d03010107a010466a1b1002c60300410500c10103102c2c0c001040d40b4401c8a100d0f080039500c0b42c03100c00d58070384050304c02d51002203140c20b40340441c2031810240e0703020b200240003804140b400084281c031300341c100000c0d103200c0b510b0010301c2d04050081110310711885450507032115501005004801c0c01c0c0c54a07000720f1540c21034400341c1d9407005c0341380010160964000d0b03020f07900888403503200c90203400401c1040d002d40e0700582c207000e02c0c1c030001c100510702a40140c201029501501e041101c01080310320310341040002c000600d94420311700e00070242008084140c0109403e0040c20b2500c2e0030440c00300d2175204040004003580e00055000559611600840d4440d090003403000303030b00d401e040c10f000f806e060701802680e5265 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 770001528 1250 770000278 770000299
    0x70f080318060402010e0f0f10021f09051507050f030406050703050f040c14010e191a0a020a11060418050114010f0206060d0804030803010e010303020d030c120e0c03070b09 76
    0x15000090541e11660b416503a000d204410441413045c42d4812004c890742200b1303c01a12380d11070b900d00d001400c010320340b6401000f40507243c00000780300c006c41021040c01f0900d040c1c2a0008502c0100310095107843c05000c640781c640f101c1c0d00031901881001034100c0c6010303003c820310003084070f03030b07003080f402140d440c0e4080c4407681350840d4601c1c1c10f120036500184038205072074080000501d06603a401c0e035200705050903060b100c40140454085800c0c81c0c1010a84a40d50301e0501140c42e900200307050040344d22049506205014602a55800a044020703004071184505a10030b0303510002150082d084214803602d945407000c4403000540004e0003404551292620010240d502c16500c03071481c407206a006082c15220308061000018540ca01030314151420000440800d6080d030081d4020b00d4186200d42c0c1e15072450030000d0408034070081080030941010302025a275071348141098091503c0c2c010014032003250124141c900f0540e1001e040d090300580301d0007d050341c0e01c1c10107048401d00589412258 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 770002778 1250 770001528 770001571
    0x7031208070815150f1e030915090102040b04080c130b0a0b030406090204051602070501090303082d090a03031a060f250b042916020102070f0803 64
    0x3490000c0301c1d8000040da28500058607140144410044408060092514420320107101900e036400a5100c0404110000d000044403164842612042000704600342c15401e003480b41a44988444640200343d02000c1e001c9501c07400294126402011510b800c1c075603030b40c2d0302d0180075215002d40110511803100c4401c100f61650060240c0110710f580100884605420014803a5107a000500141d41c655a205101c40040e215482554001c1e241d09041051b04161180001d25100442e00103904109451780c0420000350030a0f180340c0c001c003450454400901038994092001090b00300245501207000c41070002106d00450040780311800f0f40c0d03040c40354030b40c2900c0d070301070000303551445039004441045000711152800700030705485000c110444001700c540c0780034011045000e03601560007807400c4040c0820004503101d240441d0051041d0080c040c0928010848511401024901001c0c0543c00c80d4490f01d100394121001664008200a80715969041c0b03000e0713540048139103002000722400302261 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 770004028 1250 770002778 770002787
    0x1c080414070308090d030332010602030a0206180c03010f0e0111070b072109031d010c0b0f0c0c1002030a1422150203070216050a0506071712040302070312 68
    0x156a0420309803880c015240085c0040c0b107000c2c00301a810950384134a110000b40e20840c20742140c841000c551021401e041e8081c3c004e00c581131340804199401040700381c500c0303034004c074100e94441c080e0601700d03503118144c402d84c50074280601c00300c550551030040c5c414014001940b0031520400030000800c106c03003040d94142e82610844034040c003e41c400e100028022032154040500d02604881c5a0400c00720302c2103da810350301100340480c00316408003518030580320705541029100e0400d18003a4480c0d542602c2d00000e100b4081c0c0041305a0050703500007404100a24112855030300c01808480f0b20b4101c442c444002034000f81e805040309414003c01d40084a091201d8901a1201d8504150300d480140713408491101c1f03421044840c40c00d564819030481410b403024500c10625074016114400545603030104414454100500c1040071101c10310140d12258245e4003842e504c0103e491b0744800740341100009014801500464080745000c110030150302140304400c49218419814030f14803900420368 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 770005278 1250 770004028 770004043
    0x50109081b010203090a090f0c03060b1e0c030a03051e0702030315010201060b0a030c090905090a0b0a02160c170c060a0e01181d13081603021c080414 66
    0x8100d41c880a4140c40d101d4950900c0090306105004480c900a08080072681c2d03141140d00c5100c03840c0e52036841808032441e90046620100d89440c0800c6401c1c08d2a034100c016000d105c0c503076110741043c4d03a071562070480b41200310b42ca0640030f482145d444550030400140034100442d80d0740458040c610703130031400c605040c440e107014000350b0b0050344c115a1221881c0810b805009a8181150340ba003030006520981d03c4001c4c03003207200c2c940d000f041c600303050310000d04078540d107901200c0000c1c500001c00262071004100c5026a5500295040440d11500c00040123401800160344424543d05440c0c0100241120194116050307a032203005101c3c0b44011098071a4101c0c800640c1114041001c861160310803541802124014149254414008059191303035a000303401035624038400009907804030401594466102181c5601d543c0c111081d0360380e0540a00038039102030212191340c2d20b1201054001d00203141d0855202081040100c945100200402800d0341c00703031010030610000180e011000708444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 770006528 1250 770005278 770005289
    0x30d0b0d120810090207030e010e1e040f0209090c03040b0f0105030703030806060d050c0d061418100e070309060b010c0506041b08030309030d0e0307030905060d020c0d1107050109 79
    0x34440303150507040684900d10010160f81d1564100c240110b0341c0c40b807030300c080c00c51140284d5aa01d6505003c1c2e0000d00f0b940d600b124194030860344811160064000111a0002d1400030f50300452030307c4640990300c000c2e0088092903580a030055082080745244d000140d44150301601d9000e96940300c1c01e010007180903003802200d4041e00030120a10210b8003a03181c5940101e07015080a1609c43d0a003602c00845034141c034051103860000481500e4901d0342e000302c401800444095040c8801748000180d810707241c5901103a42c200310140060f0481070401d4510008040350544140a403401100040c010700d4140c100b11b44031850482000c1e0203521070b210350201c541d440307001072900d600e4640f03071703812191a0300e0314105a001d144c07440454003c2081c00698000c161002c011070f125460030b03400c42c055940502c04209654010300c0340f0707070120741c3c090010301c2100c0d0259009a92031030a060b8a10180c0b00d02801682248124a04440b010f40d1240c0b06402d0f006205d0242ca18080e00d039001162100014032a5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 770007778 1250 770006528 770006543
    0xb0a09121a070507080a14190309021f0905040f1b05120c09010c15230109050c09100c05070b1b010f18110d1a0702010c031b050702040605040608030d0b0d 68
    0x1404109004040342c910324008001f20504144291290049610f170b103104c0c8500094407a05d4107001c60030300e032040c076039100401948550803801142c001480e0102c0d0380b0926106a888903440304a55040fa40401060640d013110218810115200035080c2e6116581500700c841d02c10300010001c1c502ca0080e50904603059586000a01d140c0d1a02d41c000d04a280314440403a5807008400d08082e03820310841001d0b5101914542d4942c90718030b0316811660014507002119000700404070f45a03a0f88d0b01c1d188460800c90428030011015424824a0905190080d0180c40d00c00030b48001c20303a8088001c2d0380020040c000074000c04c4049880071082c2c420b1080c491030540b4180c446140018241e500c501c0c556400078050141d40c4005449950300f0080120403811081400d201b441034032a828081d5203400d10007400d050048078920a0802c5019202c00c1c2400100b20011a0800840d52150000c00040c030004100380203aa4440020580726440004603440f01486c04599a4250820611841c4080d802580 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 770009028 1250 770007778 770007787
    0x1d011b0908010207150213150c060b0301060321090812032707210206031e180705040c03020c1f0c02010603020a1e030b0a0f050708100b0a09121a07050708 68
    0x1750030107500400144083c0350307461403020840300710519516038096030650303540074100e805c1c5c100301080320100f07002d403406a4106a428404152034140000d200006144c1d495480050490100c0766800d00f6004a13020b03014000d41c500d900000c1802841c06101c16030140808d03e21541100c02d50380445a2403405a9048440c04200c02010079840d240c0200346090900b4121f1030f16400240300354002c0b00d10b81c54040c44a50402140e41e62036414a9000401561942440074280400d5541e03510500c9030900c01e640700d071034004015100c1d80554001040b54400ca411b002e8001c541804140020ba0041070094070b810790407070155105028450071250050301c19484175003060605070f00da400220a08011a607203003000000180344407101c5214081e0ba1000045817040c104180e01510806425013040002c4003041c0312814850351540c2c41201c0c3c59408070380d40c0b5410700303605481500041d8481c9090b40040b10303060080c1300c40c1d0115000b0040380ca042da0b04940d55100700c01e039404c0c05070400203000d0090034031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 770010278 1250 770009028 770009063
    0xf061f0f11030909090106090b0a080703110418050a0302100c050403140109020306041406060105040b03060f03070803070c0e1006020a0b070c140102190f121d011b0908010207 77
    0x4452000c04075280540c0e2070101039001040c1804400e4801d030203660b42d90714080050303400910400d803208100f25070120200e07140000051340e551545c04050018641950301050035510ba80c400545507101000380154017030b4074148552200e4075110150058002c0c040c240c56080910710409200880d80e4580c5428981991281140c0040f0101a58495035a414580d0f001d80d0341044454421441613069040482c400410b060520b10045c0c2018107219041c841404034541c81020380350f00050030b032340419540000d64000fa15101950740417113114007000a0300030500600c0751b050000d0318100000750104c2d4455250400000902d80300b07590068024911000020768084451504044585007198054890340c03a26500e1400a4505032a96135000414000c16502038007800b042c10f1560400034808004400c01134070361902c0d9030110407256586c2c0c2d00722850328000081c1e0000d58980c6002002260007114421080034400d4801c0070202c0c070b8844e00000d00d2101402250011580401160f842e0076880 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 770011528 1250 770010278 770010287
    0x303100e04051e0601031101080f0c2d07030219050d080c040e01150e030c21010207061d0f1606140d0905060115050f0906160b0f061f0f 60
    0x250040780c850060f211810000b440c00a1400c410901c0c18001c1c241c0c5500d149014110761410401e02414004401f08110704840c2c1c0b40350080d44100030400c0c8950382d522102c41c480c10a00188140b03000240e288047c490402c0c1000041d0006610903021104c0310400043c001e1032809502600034075940c000150a25401d215903c20740c0c20074040c0840900301604c40d003d144244009812500b0501e0702c0e80141c11540c1c3d0700828121108070142e02400100791420089203002584180c0e0b15440c41c6500c0d01a101d201007541150341803070b001841003200442070200300b20000d2040020341c480c0d1242c447c030300301c51000100303410800c400343d00c0010313001d01c1c80c2c1041529030030104106070300070342c8042c002c5030b950718228010f114080d80305502529456060007060f030000c5a03803200400801c2070034481001d0f54806001221049403007100c503913031140c800c040c1d450b000c0c095201004140c0303070540060020403480d200c103440c001c074012030380c04520041449110303e03518025440540003070390900101007a0f031f026 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 770012778 1250 770011528 770011531
    0x506061917040807060c030219031802041406190602100506270a1104050105090f0a03020a0b031e04081605030405031219140a03020f0d06260303100e 66
    0x20381491148441c248202141010003120300340c2e079000e800280d040400950380b1610200748441c2c2011410103031080c2d04440000221076042d81803641e204420420b40c8032881807458480d40c000c0090107200f1914010000c40c80054900302c0c0103040c0c01440703090041c2020098001d60b0b51981c002e001010412030150080d001c0906002e40106203101064003219040710421038030342d01b004144940b030424020020445520742408400000107010512050f82d000c421211a0141128010380c1301c030040000661400c09984025400640058005032021061028501c9001c800c1000350300b04850040d072040c4044200c1c1c0083c0f807094108000c4c2c0401041e010240010b03030181080f20309058582c2c1c0400d14141d90314501104148020488500c1c800d00c0c00680c2c541d500c0303146031407150510742d5500442640502d102d21401d050300860b070400031050200c1601c0070480302040901c03031180c0d40e00c0848001e1501807081c4004010f0140b01d4600050000201e90141c040a060000b00910304007560070742920 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 770014028 1250 770012778 770012827
    0x10b160f021005070210090803070b040c09150905150d080d0905060c1201140d0b07020a0f08031504150501030c18090b0102070f0602031207021504030f12050606 71
    0x10204258000d40c5440d0b052599203116602c5595071029a40104840c55401c00381c2c0c2d004000302c40100340041c0a01000f9121001c1d80003420711441c0d00d451401c1c44c0740303070b50303903081508028540b0210200c10b00c601042c1d0800c84404150070003081d21281280340405848400d050382240ca04444040080c110341e00408584100d454001041019a0344540c01c080083d02d28410440000c1440c015441141c00c046004100700f181d1001c0700d903500c0340403c0c22010800000707050304400400003010140240030004403ea8403511541000003030303160140075500700b0307100382180c031011620504071400c1510500e90310302c4085411421031450400114090144070f070101080103401c3c1e20821340402c8603d51a405001c80940100f224980300b0002441c2111a40c40b194685113122001c0100c16000300403035400742030303601020a00b503495100c240d00d4104840c3d0310603407141311502003209140d40b040d07200f25260010380d104448044400103e009807201500d240da40315004104541c00055581c184507900741 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 770015278 1250 770014028 770014043
    0x1014090618030a080d060b0306030d0e030a0b10090507020a0312022101030b01080c271509090c03010614030723090709091803080402010e0a08071e060206010b16 71
    0x60251021a0a02c0146442144e0841d00844c50f44070200150040704082c20303d1800b506d085141c1a40005e40d00c101c80381144040c44202c40500e56030347c405000508207160010900320040c10688030010005200380310b40c401031480d050106900510100b03a081d412500341d66000c90b80c00c0d241c0ca83d40000c0d4419512809580b04403600c0221240b036103036180c0e00844c0100680d003a19850110303a6400d0040700c19445125034441240c280311a28601c1ca5428250054041058242d40314495600300c030010f03500c2c41340c1c000382e4202000301c0103400054899058105070000e001c0c6640c0d511150107450b0305100515815000340c0703418404203800c0844045400f91100c3d184032590301d40c501003003075000d090300c001c0c001034041c00041c0054011806a04540001d036200c00b40d140d034480c0c40c001c101e0302d0042c00083c1048a14003012045540d2000300c000600307085000e403480b0903962950781c2523041c0381070321200c4a181d03202e800080d001d002107105412140046985403403c0319041c0003940c0c05c05003000885d81c2c034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 770016528 1250 770015278 770015317
    0x102070e040f0b2802070218040c1e050402030a0902040c0509061b010b1c03080709050d06050615030123240708040e01230922020301092010140906 65
    0x2919880c00f40d2403184d11501005030f1352601130042c481d41442c0c00e000f414800c19401e003030000281da281c00000c11118846900c6826440d2503001d004c4404441e13216030f074440c1c00402031140080f00340d405004aa4801c45040104103400700c6c054600c1d000c0d1840180e800340c414800b001c0c000c0c2c10b29082d420051112400040c41d5290740002540000380315410701840000e000e14001090342000030207030007605034101695030314a45000644000502d2200900c040e4440000c64590f85400902c11418111442000c0c0c0b251303120709140f480b607000721034005282c1040c20044c04c002d00b00700001100d1402d5001d03a540e24114800c1c4410541c0d488801c013116048400c20001641095030000c06018101c9030b14018060200071f99901540c1c43c0100f191441285103c080c403c6480b441c8120b020300310034482c454122a51180006401032100c194050903042c0903070184074104c1c0d5403804900d1403401c03c580070420441c4640c011035221040b0009400003641c10480040d4515000c00503042c3c91a0325920700354030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 770017778 1250 770016528 770016571
    0x8160c0203030703090305120c0c220e0606040f0b0306060405090a06060e0a061e061b0b010e0402120a050d180b1201030501061a0417030910020c0102070e040f0b 71
    0x2154020b100540014449460900070400140410b4481c40c231303201405424040c0c0003410301c2d12920542c0b809032291000c0c0044020002950f803903d100c0c241819801c00c41442c0d035150698881c0c400301c030428412450a00c100d078407200c8501c07910b4146803001d4001c2c9801c2e91010240320040034041d005000380d01c244104a80020100e00814024040d001c030b1690300c60901c9d040000a85800b600001848400742c0c90300c100c3c0c4803950420b034044945510380718243c034440e012041d05620f400700001c0c3c010710130880086441d007408090580074902c01e032003040680700707030420312615140c500400810340e4220100c2c100115103d401c86801e0341c0c106484400c0510f5980070040c01c2541700758007200911508a00400c2401030130b1290314000e21a11350194002450803607483c0b01486a0700440c00c890807008904c1150800820940384000740240c01e80b0401e880302c0d030300a90f039414070b260491700520a41001040c0c440755241001d001e0790380b180c00041f403440b1a44c0d800440700300060104030402c2455403003214 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 770019028 1250 770017778 770017783
    0x30b060402071b03020f0909060a0506011e090305060601260601031b030902030f12040e0907080313172109040f151e15140903011406041a0108160c0203 67
    0x2404141c0f205900b0801d19510511900d0680e0b03052445c45105018100054203a001c50b40039803100d180c4070000780d01d5444000583c1c042c0c1c0d072000899020405000603050281d04440d103117043d24081c0046504965a46004540c0b040c1c000e568480040e001124250700d001048005a03000b5805060100c0c1e21150301c030f2441d100b00500702c400340009843d64850f50a50505100801c108030f0030001824400a0365a10310b403a5102d5132180708101d078011400507001031030a11201000d000c016040e070355034514411132401c498000d40154141d205141c54401000c01002079490104003e00c62450010b40801803d86101e400003150640c000b41c403600c100d000e441d05440b582200010002d0080c0d1050f05280b81180840001150108102046141400282e2082807194131152040c5401006034011210040e101e0040d811410f400d50301300440c1c003200c02c20a4038494400c150a070303010000d642c8007401c0580352962281c055404584201d003c03c245096005801040110701c0c2081c00c000c0255601091 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 770020278 1250 770019028 770019053
    0x933060f0513020f1201060f03090b070f0e18060111010b0901180b0a151d0a051507050316060b01031407110307050708030304030905030d0f0c0c05130903020105060102070e01030b06040207 83
    0x891707065000300610001da007102111610500f1403404100e130407100d035281c0c3c4503288060564000c1c82030050503040d0840c826403c0c0c0046480c041c00c00c055007408a040145071001c1503440501203031003d101d000d18002c0500c03402a4520340107180078802d07441c0c8412002500c414803951052941c85500394201502c9084880c0010b00f504014846110b01c0d01000414900b0454207001040d00c4210740c0151507590001c070f001c140c490441c7d042d80c5c81581a560b1144900c030364080103081e80408242804078000560060441c9401400240440c001000044046404100d6980d101203000340114403071921481880101342c199404a929103072542d190300d444c05a46500a00c2580e000104003c105984490504d0080c14150014070083e440480080c0443d0302c1500c6400c00c01048420b540107000e428200d80b00104005001a2010480141594050840f90806034099030816000c034946520000d2024100c0b0844072852200d40d00710f0f510090a19030281075035034095020300a802c08036640a5604 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 770021528 1250 770020278 770020297
    0x2409110c011404022b0602030601030b0d050106050901060801180b010e0319150618020f0d05010b1e040501020a06240618060e01140d0933060f0513020f 67
    0x2c019441e26204005080014540f0341c0c801010329a216041c1c0c0203001000200c480d44040d02585235524000100d0003444409961036002c01c4000356407060102c198880340540d0010307a00c09685a885030000d44401d24288070742c0c02411011460306039100304503031191504d102c0525203800d2415080c0c0009103090042da4030710004000b003081c08020801c075040d51400ca91070050091040614064540c0c84512400940f00c1d54560009002c1d500c40251a00302e400c0141080010803195868290104194111401010815074550340e800042d440503000d43d0221401680104040d02580e5a0b51020384611180c90700f51100c030515403000c0b442003040c2140600720598a48138203002110450000404903800031003804000c070074103162643d10801c0d091111880c0c801065032140c1130f0340780c0002020168006807402044001d1000d60300120303904030500c0a08002020860b40942c10010100e41c003d00c42c0804070401c00d5420440c40c20043c0e804006404808001424a203003070407126440d13445004070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 770022778 1250 770021528 770021561
    0x13050c0405072109030804020d1e140d020c030d111e0c030d030506060703050306190306150e09100915090819020c0d230a05060a2409110c01 62
    0x1c07040e00f0100f2448800040d07200e40014011369003d42c9000e42845c00180020b4080d000b0ba000e11002d0044100d0100c400d0341d000c2d4025414111942000e822a052400304a125030007405c4950001030320001d41c035508202e006020305540440e0040686d10b20f071502a02103580e006a4802d0080230f290104094040c0b0044805031aa20303510344101800c214054080d0fa040c50314040a01160741c884406998049902d401d1096032070b1119000210689040740e0003d206c0c428039070002c003c105051300840441e00c00707030240206030794441305074145c0c240040720515010b0b84179606450102c0d9030350f0412050a4000c000002480b00072003c10019103c140d14103880042000503180350010030040c514920a01d24030161524200d02c0b800683d02100c2a0809014030a40031007041301490000b40082411640b2000c5032810055032801ca138983d1803ca5404807001c0ca40182614004489042d00c008000c07840a049141400d2402e40b40003403c0700402c000c0641002c1c0410a61004240300795034245c41c02002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 770024028 1250 770022778 770022797
    0x10b030601150f03090303110c1f0c02060f040f02090114031506010203030a0906110d05011404050402130213120807050d0e0d080309101506080f0f13050c040507 71
    0x241850050182e00c080000d200b0740104090a65000d119645010510303d07010950032083d08040340500030b901809000c40038005110905403600290000e9102046401c6014941400c50040304403601d501e88000507802190010300800ca100b00c00320b038413904c60400a00f1003503003500803d583c02800d0700030041007440800d40ea07c1702d00d020010400c08100003c1d03125110724044000035281d001c00380144d5102c80c0c541c2401c000700005900400340c84c8a0392900d440e203848140e007900b00035003000c1c450b40e036000c02203000c07800140c181030140612a40c1c0243c4284030012010100b070340203600011500e02d0bd441d0300074000c501d0204031028000064040c6504070745440d09401d000741001c032540c1c5540e0a10000d0110718102c0d4954000c084000c41d00400b06540f256203060105042c44640c000d50300029242044c00801900d1000b44201950156520304d000c0340d0721040a81e6492205a6440450b1032529001441200c1c2c440000b0100d1803050081d5910505d01802240c1920400d0307500901040003081c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 770025278 1250 770024028 770024051
    0x309010b0303040302150903101e0b030111040303230f030f0a2a021005070c140105040c030204091a04050102042102060307050906160606030c051f0e0315040501 71
    0x35040340544218055880c003881c42c0c0c0081c0154071915054075031000d0214440c59603a0f0244038a1842149500c010300004150744400c0b40f00b14811101c2c1002d451410b6400d40e45ca08052050702c0c450301c1e82d4501581f0b820f055880c16601c2e40c80b0310020200c45c0e940da0011a10f02d00c021005001209a19801a5140d04202002900d80035005061942e56481c0081d151011001200c4c0050448103181300c5140341c4101c2c0c0000c0f42400c03000b443d201d60301b40c14002448101680070070361510b074600400c2c4039400300070500100e9090301c205550250107006041c03c1400580741c25440000251305c9110f00504941c00b55440070203801003142c055036283d6010800300000c0c0380f05401c48084070001c1450a55103400b550000d02180800b6201804006000c5403481058032028103c45541184100c0b1200e401c0710303864494003415290004032480440a1b50006050910619211a100200d1040c80305000940407c1703403414074030800550315100c2d0000503d00d211540d143d1500450048e400802c580c0581c0d07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 770026528 1250 770025278 770025281
    0x305190c05031b01030b030f161a13151b0c03050d02070b1b0705221401060225170f0c010c02031b06040308040b220b09040207020a090908030901 64
    0x9a000c01d010350000300f607440c841040914038014049007420000f40c40500000440d2070500b014030718445a10951240d0f000300d0b422001404200c131601f1254400340809101403074040e000b160a01627070708590369030038070201181490303039100390580d0302e0050406050402c070b100c9100f200b1034060701d150b07074410418024440c060002d11480036140c00186800e80c6040700e4000184104a00c4440c40c500e15082900864000e00000000300002440010a034042c90750a00300b41c441d40c1d003488400d907d03240d041a147d1207106103060480d15550050070110140d4968a90041d080420a202c15403400c40c02083d060f1000d80044140c002c1d80c0c0051a52600f071200e00d41c0703080600c1e4542e0303051090081c1c0c0d9000680e0000750080308044040ca6903046104d814000c01d0f0503014582000780150030100e00450f86034000000b13004142080c011003030862070440d204401001143c001c105804808008018040c1041c1d00108100b600c09446280c643daa07920840d41124041c1800301d82012000052001c0740509 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 770027778 1250 770026528 770026553
    0x100509032a1008010f090203060d0204050106110d0801140405041b0801140f060604031203060312111b13021b07150210271b3b0c0f04030519 62
    0xd40c10f1081d0305505148602040b41072901c2111000c0d0f8002000855549601301d60310740d80c2d58041e00912079543c441102400041d201e9030441050b03c104000c03580304500c5150b03083c4c12101d2400d9511084605041804080c010040040c0c40410808902c407074018102d0110030000c1180100001b40382099100f009140007000d0f04801002d00804144501980d402040341c00312648580c0030940c2884240f01900902455400a000125030401070300d0b1003904101c2c0b060b000104203007550012025075401d0094100c0041207682c2080c0f02c40a50880300310346a00811546014030700040740007203600ca0007803505005801c80552100120850034400342c04107c2d01e91444406041403091120088110f061070381454210510251000321702012310001c4a01c0f0940c020b08107101d0403001d5103444210001145880310002e0310036013030030891072411015100c580c0100441d0303104070440d12045c2d0503401c1908001e0440701c06030001c000c000000f40c0300300001c5811604000c1d00014110550800c171040010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 770029028 1250 770027778 770027809
    0x909010b0d150f060f17010b1305090f0403030c02010e06010807240f0302030c041e05100507030203190e0d0b0105100306031a150a14100c02100509032a 67
    0x180000340900c0001007180c4055801c40e2603c00c034030034440c5d10111890301c910000901300a1410001080c050061170040070343c0d00c81038691111282d560b1080c015112402c40344603040344900b81c04100024880c0d00101c183c0a40c47c8000725060740c1b06e81c8400d080c10300a03032020006034800c850411590300621356007042c400240d05401103c903c54080602421b00201d2940c00b0940d0000000c1c1d215240841691302074021380030001c902e03202411940300c03900c006014291007210304030389140345544100c0c1121241e9038981c0c0518100520000c0c45524124411501400d0001c0c2c031070003680c6904e60846140c2458020303180d140d6136514000a12001601640d90001010300704801400400d0b1034001d9455124000210f01c41d1554988114100301402030045541c4140c1805c00081d5052880300d86103008007003241c62090f5409512402d485443d000c070b4009402003400b00104100070300903000b50941500c05825550a42c1c09460700650011903c0e01100d40c11142c010408240e0a211951008444 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 770030278 1250 770029028 770029061
    0xa0c06150b0d0519020d0c1d0a03060e010912020d090b04050108041101030905190318030b19140709030b07090b040b090a0308040f0509130f08030c0909010b0d 70
    0x1e051014181d0188a5044600c2c0c00d40c0d01d40740442c039600044e928052624042000c1103450328141c80495003d40078001924002862150074903021038545110884211001080d0030381491440e03562502a0407501c0403803205551380d0038042c000ca0700030144201d003082c460717000c0e0448d1041c1c1000070340003017100d400c92500e60105110a11043e41c1096070705030040d810554555281c054200102d01401c03130690000c210780187c140d080c4180c02160041e0800500c40d8541384411840c0c040304c403000010300e201c0076045030503000205500c028201748903907100d07101c0b00c0045101e11402a402c071012105030f07040740025424007020001c0c0812443c8081e0806403d1038921103403464a01c4d17802d000d0095000d02502d461000400941d40e90360310440600039680850b07085c0d01c039170380c0310346142c08602c441c4101c60080e003884000a1150245041c1801803d902046242c044540341c3c89501080e000140b40480710081007007803200544d9100d214a00030300c20800c020360b0701e0030180300ca5025282e5808d21a600368 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 770031528 1250 770030278 770030321
    0x1407030204030203060703330f090506150f040b0f192d051209030d0518030a050a120e060403031b02120d1e050402100806060a110f01020a0c06 63
    0x680d800b1441c5c0342c0020301032801280c040e01c2d1b5140050044030703103041c08150042c0c010351b52104050014103442191811540c3e04034240e521900c04064410807684d266004100c0007659a0859a034009003540d512000034450a0a0311202d80c6070756a0700540c521020104003182400c3d04440780e800c1b80c0c4501000703141082c62500f00b034440c54031880520401d41c0141d03140c40070902a5a01c2901510002c40c45100000b05608101152584903403020710303822103590a12000906c0200b0049060210403203150007140380c020040c02c21a41d0f07400c000ca0000c20007614401900d0b502909008020082c02c00c0703000380c01d060600d0324015040b50040c0c0714014a505c1c1400c41404142d40100c1c88aaa0400226009a8543c58007818200038a0043c2600e003e44102c040c00d0101038840c1e60140b80706510076600306804401ca4181900d00b994201c070083e510500400454160900c10b1200b1401204850304862042e40245407150980c1c01c0751038180009410a00f602013400b04d2800750315850141159454400d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 770032778 1250 770031528 770031533
    0xe0a0207110f01021212010302031e0d0f050405040204060314010e1605030901020f0c0d1b110402070c0312030c03060e0c040308131a0903060907080c121002030703140703020403 78
    0x103102003961020b2003007034507103070b5016541d00a2003550340d0740b041112aa035943d40c3e90312050005203800c0c04240c2c00f9215201800c03071004100743e68103103100400c4009110044c111785086990a4940706024100001404002115181ea00141029000c035840c00702d02440241401001e200c4168003500c0c030081d010091020f02a01e0081d2104400c40074030f407440d030f42e55403200b00302e01911900301c1034200d400000510041d900380100e41e015a1900c01e40d15841c40141c4101e02c1e01035250f411a024000302d02e00c0c840344079289025070080440c28411400a0349895030391310707455042d100030b40b140c1010035107440350f041d0300c103601d840b849000e802d00c0800002903007408101c003c15400385010040010100141a018641e40c0308150710090040018003071620b075080d88600400c0d049004031038064400c8401203000d8603404101601030381c04a20041040c40200340030040d03001e0034142a50381c2ca0080b44402025210680025407140e4004c0c0c801080d03040140006111a83c07000306414200b52052205000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 770034028 1250 770032778 770032793
    0xf021908090d0302030417031b1c080415050f010501031805030a0f050706020f04090c030212193e04080a0206070c080a110406050f03070306020f0c160e0a0207 70
    0x82148003600e05814400907440d060346140301d9034000400c520a11681f00d500c480000004007881600d051300580c0e03400d156180a9940c811680f01590b80d00306941c04d55442138440c400995000c1d0084044140096a0071a0f8004031981610741900c8549500014001541c050149542a00c0e2070311282489039180d03114151640110785880e002c00042c90f80c4020300f42d1089050303c3c0181d070400c104650f01d0f070480c2107810481c2d0041c07040350485820640d00c0103805000348280d80641407519500484c82c0c0d03c1e020000310f0802250901079903a039494403e10a038044000030189000070004940d051200a81400d283d541d10f14456107806031010030040c0907581001c40e402e0501170b41690780d01c0d1210f40b40c1c54200201c40ca81d07003041d0b5083c82a219444140046001840c80c010410384040041d40d444805120000d003d4585e01e58250344400401c10000e0200e90050070382c51000c0303002d542450740392624142000c450800b08104200c8552007440040381d41c160542d003050206204502e04440c0c0d0f9a40c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 770035278 1250 770034028 770034037
    0x120d031b0203220521060109020711102105060901080109080a030f0902120c041b020c0d0203030d0c0809010e03040f0303051804020406030e1209030303160e030d0f021908 75
    0x40e50750b544000d4100e1684035454030f10002d8000140320214000c1e195840b41320105104401c0509440b07460b0001806000d103100b00d0b0003031900016407050028141082c0210122004540010403051070018070b05100398100c1540140340b05000800c550801804000d5010b0060704042c1003a45408000e20000321003800f11200c40c0b08500780481e14403648901344004000d2544060b400c401c12402c15031043c0380204800e00443c100b141c080050120705500300900c0e1500c0c3d40c903640507912019540106142c580000b2281a10080c211303490000b20f0420710041d02d50100c1d4000220741240b0a21082c40d200380034003221402d40c10000c5040c1450440498002050f5102c05001d2040000c1c04140c5580b003e8451100390402500641d0b072183d6900c0c004004101091940400e401020303552041c20000c1030072540101d10041c010b500310348a60b45180e90b82507000d0700610600100c407001451a8405000541e290b90300394403503842c50074007254042e0800d24004d4114103010b03194076041001a4500042c0e9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 770036528 1250 770035278 770035297
    0x908010203060607200604060806040c0c030e190504090f03080c0712140d060b03070306050d0c1a2502090604140403050d02040b0408070602070501080708150f120d031b0203 76
    0x1411007140c24940f400c815a5118105c541258000802042d0190070015550051105880810105285030800c0f26900e60f114401400540c000724500d040b8a0060b2900400d8a0500f40742c01107903a64500240c11034100781d0f41140c1050380b100c1204107058221000035032000e100120b20345000155680c0b65a58444081400140005000e01c0c01c034440f81c102c10381d0319181c03000600b0030203c3d4880d140312905400444600d40042d04050001c14207052201c60300242a41c85030041003164105100d24020751702c0b41d980360f0701c5500c060207154000041c0048407070301c0da4580f01010032100e1407401071000c04500105004d00403410014601559005402c83c59801605440e1040e26034a144102d04064480d0394846d01c0c0703440011801045c01800401c2c0d170400ca42036a0200c40005640d000196110403084440002142c06140043c5040140180030011071034010003450707084242e40000713481c42110450f4000300b540040307982142c2c55094420118507140a00e00416620481d080c002d60728450b80404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 770037778 1250 770036528 770036543
    0x5060c030d271b05040c050d02030c070f080702132901030f090507170c030a0809010315090e0c010305092503050f0307030e091501051819060908010203060607 70
    0x400c003050380e04852a040c20707a00070300c1040b11800b1410080e501502c0410041c1283c064520001518a00b0303229410b00744200e84c07200d034281051b03084040000d40004010715030340a41004900c1c00217284608c83d108452203000c550b51200b100e4010300951003c6001c00007201840c1c002d0008141c1c1034940d0151007440d0f000c54075444880340350012005041381914820000c0e0610705044104030b0049035280981b0004403040c507001c0300240d1030700e81e280d000000c40c81e0140c001140d10800714117942c0c002c0c1031540040c100425419017244d480c0ca02c102044d80704182c4555204000c800c1003c00b409000c003049000d10302400745041c100d00403525418038032803000c01c2114007210504040c4050340294011604031054030402502e409a0944941c00031004800080c40c5007441200c82c07500c42c51003401000c41324114070001c0140030054a80c0c0c0e11501b2034003420030b40c0814034201030390b6110501c150f0098100800081d01d1415801420030a1035400400c0329900620400020b51107074801c5c2c42115402004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 770039028 1250 770037778 770037791
    0x71d1501111c0206090705090612150a020a021e0304171c170f01030c06050d15081b01050405090408070314030405060f090d140c010e010608011505060c030d 69
    0x140e401d40201c4078000401d0080104256182610724203003100d01c00d0390307025076007036076180009607445643c24000c5d030f58061000408542c1d03600b8a0300c045e88406070303540210782030702444400081c96448202d0340441103035000100180b03680d6044c04540c90859900075612400074807800308603182e0107103000c0c0b440c0c0c4111a0070145a104030402481c0544c400314000540b07020078103807005001c581c0c0c1c1c4a2050410742c007003001c1105030380307007800c00da04032908515400c00460400100f101c0303e41c401c2040c1d402e070036103031041410048a004418801090503900030082050344000e0f1226090400024505000d010f100403c0f054440c0f2044039801540b180c449a81c50701c1070714082d1420120300c80300d00392101c004400c000400100240c40c5014801c1c041d0300d000240d5403180c0c42da940c0ea8040a69000090b40c40f0824801042075101404034403c070a0000328101c42c07060021030848009620013295a911000410091043c0070030b5000170342020f0b1501d0740b9000494003075943e203206030481014600c1d034400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 770040278 1250 770039028 770039071
    0x616120f05030f06060a090e01090f110a02070e0402040b12100c02030a0903062307080907050d03020d0c11061c060b03011215020702090f07090b09012703021011071d 73
    0x51400088c00c5840950900795071112103000003040c0003076030718510718a80f00c1c0200d1180e0185068a030721422550040003280d040c0710010406803400740c41242c126844185a00c2d80c0d9460a00300041070030008004c1104040d02c1c400101901c0c0118003203070940d0000c00c00c00c0c56481e4403803164011759030400c50101d00103846195116025a1016600342d1954004d82844129a800000d29010750291422200990b0310341003007203039510000708010701583c014141c0d201a54011070348088042d01454074060342035040004103d0991104031004416a2034801c2d50003441d0740341c803a00028045d202c0034a411581054280c5441c8540d50744058007208104011807500742d003640450345502e6001e40341407d5420880c242d800c03a44010349805002c43c800c24008228000c0c12429510b5540050391180e420741d2a1b030032540001d02d0f100b04a081c012000001c080b0250322603501040d90030328140e4480480340da0003940503051851541260548007495050201520081514190002c100c0200fa240400041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 770041528 1250 770040278 770040287
    0x703060f050111070f0602060a0b030105071d0a03021026010509010e09010608190b070e130903140f07021e0a061116080708070b1204060b0616120f05030f06060a 71
    0x117030300801c3c40c0d0411080c085070550740407034414052040c1d81410b00020018104142c05c0e00c1007200c030940050109002740040100d081d040a40d0148003070280b154154a030703004101c4d0344d0f501800d01d1010540e8884010105c525540f24003001c58010b20020403913504140020340c05c220103114143c44410110040b500c040820740c4058010700340d10080b12240128441c1240d10f03030300080310948411200500041d0414001ca044003400d50000303240021810042070701c00000c00b030146050301040042d4078401e000034a08402405e8001c1c00b502c603a80c807070290740304100da089548800d000a00c829440d100d10780751602402c400c2690a14203100d06207000d9420840d01d070403000681c2c0034028050000016081401041c50000c0e502c9060035180100c0d111480040702d40700c0c114601c0011019017001a0100e8010751100606820040c40700e0b00d00000114841d00c1d0b0001d084080e110805545205000d02d500b04500ca00c0c50f00c03a6041081c03c5103400c9802034041c0300000c14160055400091132160750f0b228 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 770042778 1250 770041528 770041543
    0x3020708041508040b010b0a200309030114060306090d0f1b0b0403030e010b0d111c08040320100210150510110c01110a060b0a1208030702060703060f050111 69
    0x404039140000815240000c180083c143c1d41a00c02e8898440049428124213044541040b615100e114036080f40c0c24203024103116203071501c04940018408048566401c0c054010915100c0032440b88a080400c2014100f0b64050130a419a0b4480c21030182c034503402c900d105042e450107081c4108a46032030f000d40d07018036400c1c0000800c000400030401c010036130981e00820703400e03c001008002d052400414000202c02c0504094400b8000c5d00e220445450221000e4605402d92441c26011070126600e004003a04242c0003224a80c11524104040210001401500440485040c41580b00c0c2d8038002c1c0d21195041072007807006840315400d0300c40782c0c00006d0400003010040d000303d02d505029100200104034080c200040d070300507410482c04541c03103804082d27405880e44000c2c20130000d0b20350f19000100035040156800090b030540000b050b96030140b2039801d0368000d407040b84e943d21781120002e0408000401010506240400521070a8441d000d020300350b50081c00c0020000c1c0c03515400b2842e1104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 770044028 1250 770042778 770042789
    0x406120e030904110a03050105010912060e1905030406020c0a06080a051506030a0903031a01052b060605030a0b0a0b090d2f011b2012010f1a0301090807030302070804 73
    0x801c2c0e041850130256500800b022090b9980070081e59883d0300044aa00034180700d41d440c501d0807040d0200100e5039541c0700d615648440c0c02110320b1100c2100c6000107003d40864140d441d500301007010000c480d018407075810401c0c1300b200c10488250074110003400f40d04000e000070006980e90000038000c0f038182c10f0b240c6a46100148056100c1ca0003800304d0b00540a00354085000030300340800f043c000104080c07040d4114505849050403d07031018000401407122190301180c101a2189441e0012a14400e40c0081c0840c0e568959480c58807101110694018205aa0141980d184104410f21102d000d4903508031046a00c1c06480080b401d00103a101688030840c04160100702008401c1085139030402000002038a0b44a5429141c44410754100d900510161080c104d4688407213041546480015640348010040381408504c58003041c21030344034403079840c50350f0350710040030402c503d491440c80d5000908400902802803140e503640308070702940000405154011843e00200b00c1414141d401510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 770045278 1250 770044028 770044031
    0x102030324150c0f07051c0f1203050f01080a03090b030618090a020a530d0822080f0f030901020d0f0501050913060e0304170c03030406120e030904 65
    0xb0480900250903480303030fa005211407040215521030702c3d0011814000302c88000740900c4e080703807001d60030210542c4000e4040350b03035204400050300040c8500e100300404e4000c039a400a0103103001e504031400300030181c102801d01d0784040010390020390b104510303e0654909003081034681e105c21020413610766005000041142d1f0300003c20841c0d0800017030180364203000319040c0d001d01c2d6840c4003013803a100e82140c0400154001c0340d0070346585102c13002c03002141398080c0d95001d00c20042500c545007210020481b4209600107010340382003039500c20b88a030303004416200b0301031800c0000200b080040c1e01898004041d4540450b140c442d0000b00015075203800050a000c0796030745001d02946000303600140b8109251850710080034021074992090328160b50018040108a0f10340c01d40701c0c00d141450b50000c403092501c0c0d41e000707200c140c0c1c140041c200400700c416030240d645410354001400d126403a09080d0003607005100422005501c80c942c850400d14416000401c200308020b51815841020500768019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 770046528 1250 770045278 770045299
    0xb2e03060906050c07150507090909030f020f0f030a1805041112070503040b07030902030a021002010614030318010f020f0616120c081b0408060c04050a0e060102030324 74
    0x4001500319540c100d01c60b40d800c0100d40e450203200407503802584406042e11a038101d1040c1e0341e441b603a10680e003009850070106409503076400c6c40e02c166140c20100b1000682d140003e448115010040f8841d281a110080d001c01400800500d50324002c00c0c400f1810440085644c00395030300d45c62003900107401b0180080c00746404920441d02c05503c080c44080081100d5400200394500c6402070780d000c0c91b4031440003051605d460100710050314070702d0b000b42e0741070080203059030040c0c0d1100c4d0b060000f40c40320340010036040d1601018000740800328003564025002040b240c1c00007150240ca0702c03140d00c02404c00c0e048140027203100b02d02e031943c91001800340d44644402d00c00003100d40038004842c001699210b9900300440d0a981050341c1d03060011402081c1800041078a16641106151070400710304540b40c103103075540d004103241c071801fa07030710b1140c8440000e414046820202e11142c00f03480d140d1070b40119800c0000000350b42e884020005015245100390306c51003050b003480b4200f40c00700c0081248000307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 770047778 1250 770046528 770046533
    0x21303080316120204030203070e0606160507090c0309020d030c0503070b1005100e0a03061a030715080702031206090604060306050a0c09060c0f08031518040b0708040b2e03 76
    0x1d50340c03035080342e03010540c0100d0300424841c69000b1101540c0c0c2c00380291100e02c0c500b004010901c5005410030b035221100b440140200c0c00d031150410f4449003e00c005007401440c0c17003103c40840303001c81220390415040860100150301d43c20070814150f40d00d4075001550b03026030304182e401d501a0020082c0f041d140407007404107888490301500244e480131103008211904242d0b05648009009030701c9a08484030792070070004032f4140d5000e00540c00e008110500440d1030440000e0800d1103a8101001e260841d032170300588039600a06403944480c0a00085150007580b04803020014070042001d881403181000082a40e00d580e00044011948603070b090100d400e1104800f03015003010075030140020030030751000032424810075141c40b03119007203c045d40240202d0b440e0401542c1c07006286400d42e600251510800d81c44149140799140150718001586041516080e07203142c2e00604910104200f403802c0c00081078205500c6030b000302e14401e005007810102034034004031700c1c400d8501414106000100000303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 770049028 1250 770047778 770047801
    0xc030f0c010b09240f030f03031915170111070320010c2708030a020a0309090912050c212a190303150308090f04110307030213030803 59
    0x1a51400244000710410003445101c040458002501c00b544c0c03a05022103001961111104240c05084400e481502c00003181c0b030404800e0100c4203980c0f00104208541b551540780f5072103a4003d00040c001241507105031400c039159400380d1140820f010080040d000340951001c110014180811602c1d4582800e001d0500c2104c03555004480d810700e074049000305410711440c1a22a003d44843e5000c40500b201222048039100c0c0d46004142c460801188407801007001d000e03046a0780d0b0050024600e14a002010340e100396004030f003114101548240000c80107082510190326618005498006480c0308500c0c00038040705c8080100f03048070041080f15145001171034031000502a40003e521000711101d0074036207078441c00300b650700f100032100001820054600035040c0a8a0b000c181140020b440e0340d0040c002c0d0b88110703881400000c3c0340d042401c15012141e44d900088604200807500c0040e079110f0b0b403100502c80000c050f80081c12000602c3c040064a01460708045080e440c5c0c50034008602 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 770050278 1250 770049028 770049037
    0x9060303020d020a02030d0f05070209040503031014090c0901030b1f0e19061b150b0f040203060a030b0a0f02070b0723040b0f0f0703030c08092b03020c030f 69
    0x20014010210780002c00d03400010b29078403141c2d02030001d0100c18214a401ca81d0000b0400014042010421610016903100b080890082e8041c40c00786580f800e101d91700c00005040c0b80d002c07a44500303000100c90640d0390f500c50b1003680b0242c4154400c2c1c0d50300716000120018411a482c1035408000d00c03c407402c10227002200d5031400307c416180c440155a0030410000901040f41410300c2503070b1140e03018010180b2616405400900c480e9031606031490590350081e040000f40a03109003159642c03006041490580400030111005640461850400101041d542c0c0414000070b0102c030b0079040480c031981410341c80100290340c1200215101c3c441850503201d0100140c400b1800100340c907050349582c466500504000c02111052180b41c6494043d15801c0340d0410195035050310000c1c05146c48401040c2c0003065181d1207035030000380300ca40480001d408000050074524155100d04103083c220f0b5403d140103801d0203061045c0c065140c20741ca03000c03806445030001c11003a601000c100c4449070040c0c2000740 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 770051528 1250 770050278 770050283
    0x41503060b0a030b01050418020307060c1e052a180a0b04110a031104150509130c0c060e01110714011b05071e08031009060e0903220f090603 62
    0x6000c0e40700c49108002040c225804050b0422080f04010046442c107540140d000c01411312040003000d45940020741408515808080402c0340c00c080e520130444101c982030808549806851840800e0340c440c944e46885a00e00c69690881c1c20340100c882503041c9a422041010052044070302260b944001c21148400303589a14041d0304040e0042e005103424091681c0c22400300c200075003800c008090440243c44003002c00b100361102040041000210281200003180c050748507c0d0707a480e0f4071018002e03450090798001079440d05d0500201103d075400040321300055000440800d0ba5050701c441e0a0040c100c00551b0350004500181e05000c021848003112540d905d040020041e1903540060091420b0140c0790b100005034003040b540c0002030000500300b4141c0660303c86200d0342022640e80300c48039441602c4100d0501e980003410000f04016000f050054448070b2030204080c140800c10544e00e0141040d013554495585035402c000662001c41140141708030080755041d9652100c2c0b0b50010036460001307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 770052778 1250 770051528 770051531
    0x1502161101110d0e0a080a080307050a030605060729040c06180b0a030c0f020601030b0601081302031e01060504091104090317070f09080607140c0c041d06070908060a050604090204150306 82
    0x920280c0c0441c5200e2241d230403000031403444c0e965190880ea1680b058054200789a943c03513000c21291604005054800e01c901925042c1c400311003031032004840c103041c1c8402e440b8100000c00001179000381c0140225501070500c4d0b400f8001d804c0a44000400a070810144e8020205102c000d15925401c406040300a0f6126000720244c0604100d8840509010251800003040041821540700e6000a42c1c80700341c20107400f0509140f42c0c0002d08050940e40c2e618503102400508505040081c400c110090800b1101044004040d036a5500034a8000c80e001c0e2041e6a101006020b0600a81d1000b0b04000380c0801541e0310b00c0e181ca005070000403000781010008030f14180c0402d03440d100086050094103540c4940c88a80c18000c0e2004695021040c0c0901c20300440031000e109407918010b5030b00010039810582c02405280c0016440d06100a00704020000c40311004c110070074000c80d0007600594405000310f950f544d0040031130040d004580000b504146040881051242c040300001c003580c0c4103980 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 770054028 1250 770052778 770052799
    0x1a01050a08031611040c02011527020c0c09040c0906090216020409080d09031e0203030717040f020a0303080f0a0606120509070f0f031502161101110d0e 67
    0x34040d0140c0c640c0204031240c1d01c10840c22107154070307203444000541c3c0b0803104074094201d110f01060036030344240d2800717000d81e458000b0581d40010000e4800068050a8030580040d0007103040d00c01c43d034241501c640a2a5030003e40c21284078024024904281c201a2800302d0b01d00f803515190b0710b12145403040c1c00c209031410034081601c051a0084950500110b50a60481002902004018650a24110762404040000d0070520300c59004d92030485010341c079800c06c1d000641040807283c0d41d0104034102150810010045510b40010402a500300b120785001107070740c2d40d843e1408400ba001d03400650301c22810381c400010582c0c032a40a0b80301e400007041090454840f13001c91015500c080c0280d001045118161104180d01548001c0e4800d540c1d0044400040d901c2d641a50388000039080f490215044820034802c0c003416556092102540c101c04600e44060522000003507400c0c800c00801d8400741c8030840c00141c3c07081c5107201203903000300c0950746c100314811405804c0181c4241c2c5c0a000c0c0c0401036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 770055278 1250 770054028 770054039
    0x20030c06010e06010f0f30020405041a0604061107050310020a110d021009060f0912080924040302031902010e070e090d0f0513030b010303030b0405091c030207050a1a01 74
    0x5004140c0d6280c1c0d10f41b074042c01c1c10366409441c00c40d0484d00d1180714003860110072444804141c4042490360001c0001642e41d81040140400d4031200388401011020058040819840300300c2150b080340e050b0703c0e003500f2038030110498604107501a8032590380341c480c03030141b000c200b60b03141c1c02840c0694154465880d0070305607498440d01d90400c5200c00001d0303008890b841e80c0d9070345160800c0100601c501c07030020b44140780d44d00a404a441200058401804150660175282c0d00080c1e0590441c1620b0020888040020741c100b042d0301d22100011441107001000c5000c05008009980340140003812041c4a0720130002c00034000d1520402a241504c6240750010344011550780745805040078001074030210260300b90941d400c2040001b40d004020381000340c128071210704143c030341c00f0b10311070420400c565240d03040050544008800e07140c8140d00c0d01b02400b20803480012800306030b40c42510721045240780c82c501a0001c1c000c1d5013019080340241c0400100700420203404000d04401c41c440786080d66200c9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 770056528 1250 770055278 770055287
    0x20f0306010801051e1c0c15020622080906070f060902031606020c06030919030f030c0504231323010812180a0b0408030a020f030f090120030c06010e0601 68
    0x40101403000b01e260010028100281c284410341b440041d4150342140640d11900750424070781c04089002c0b0700b8645210403540c1401031681000111000900310104d49034518181c807078842c8007d180d550700041740c0030305864450940d0b6581380c02050482015a0310304003040500f10141049110340612450900304070348940703546d0141c407080d03401094600354001c14000954000b424124aa205100e407000304c0c4081001c0d04041603101c0d9071800031a0039107800c081c01344c8100c0780100040c4041400240100070b10328451180518855205000d011410f402003011603210b00e00500c140f5080050136059a5000107210145099200022140da1380e11407440d51030b4a00302d48400f2484401708114200ca86890b1160000d03410000c150600311580c900b040740c9907612036480340d1001e800c0801d041a000e50107200d90003000180c000035503d84440e40c05c900e200f40c803911511606000500d91100f407500160902070b50b02c24582800c81e80d072440910440ba940784403d210381c400c5040c510001583c1ca5115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 770057778 1250 770056528 770056549
    0xc010813140715050d0612030f120f0518070f2402011b0305180a03080106030e030c2509230601110601030c06020c0a031e15020f030601080105 63
    0x84091002940815901c10044400a0200e5401e0307202c0c9103404503410b002ea011054160740710351151a80c4601004181e401d0320070f0ba510955030344803028641d4020030740140600c90300003a540351410500805001000042c5944e160980f0000c0c42c0104002040440141480700c510450b022107284564603800c1d80c010841070b000b040d601010106180c003c50348000410381b003d01c80c9000105000005118418007003140303114010000c0d440d80184071480d0022504411444a035a0140c4805421038801810500c03040c4140d2040683e41d041d0f443c2980070520944000a41020070f4610444010454a602c241c010614803000d100280d000113562403e0700c5505103041c82d12a204c19500010149424401c1000746090306111020115481001051003018080c5100c0c0240401c16410100024600b10810b182d06c4d014028190702030000c1000c2c9011482c42e0004010000510071603850300a4420b4030346204010000e0001c41d1a64590150201035841420b082c2d9540005030303651001c0002200300b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 770059028 1250 770057778 770057791
    0x616110f101508060c03040c08060714090d0c0902030f010609030c0303180905090a05010b010f051209030f1219140f060111070b07050c030c01020601120317090109050c0108 76
    0x1560400c2421040e00914901d1180601d00e000c0a541d6180c004d00345081281c0b849400c0c3c0001081204020002e0000c0000d4141c10001308090310301090058070020701d00c0d03041e5152443c0400c851202d5a0b03440c3c00004980e07170000405580554032500e00c400307034005030f4044044044640010a1040c40340100604498001c0b008150981ca1070301e09650011102528110040d001d2070b01003100c42c0c00307002d200e0250802c07000510b2150b8180c01c0090840b1840401c550400543c41c00c81800180e1100549020021a10423462103455200403e4618031840d08900030381d103004104032030340041d8604100e02c00c040410308002c4844507100f04408440b02007a42150604102d0b000c20840010900016840130041c10f042d0403240740c0000461400303009a2240541c89000100042081010b10240c601024180c0040c400e60803003a0002c2d40f00c4005000702440c400c80b548010342414401c0c03000c2e80b1000c6103441141080c3c00d212039218040c0884600c25280d5110b0143c000106500c10b07800e9503c01c09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 770060278 1250 770059028 770059033
    0x1409150702120a0f170f040b0a02100b01090e09070e070519091208031305100603171617090a1401020610030302061503011b0305190c0c020d030507050616110f 70
    0x100e280c1d4901c0c00c145920b10040d1100e0100703000d10109a810781b80200090860707000c0b0301c1d03152109182c00a2400c0092706c0e041000504225940c132169030808801415207511220743c0c501d955801c00e06500c2c02d032041d8425001d080d1079100748940d894221005100306450140580b000d169400025511029544603080d050050300503001e0128a100c0061508911070003100303d54240300340c072564502004c2101d58501c141d900c00e020010800010400b1224800032481a41028105207403422459800c3c5005429100192140004082000200c4078000c0700140710342400e580341c80003c4850302c0240300315405442240c000c0b40308070100c3d5801000b141d42c543d006241a40d55000b42069a0380740502280d010364032080501414200388030b070314905807031550303002a041c9000c5501882c1c4031710609064600034030303003103185001d681d2010040c98101d806036113003500456549822541441080c10140040c020340c030603c9a1094032a5018412100554904001303079104903c0d01d40701ca283c104c0a10256 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 770061528 1250 770060278 770060303
    0xa110304060203091c110f0f030f0901020a0812010e0901050411190b0f2a0d0c0f0506071101290f15040906090f0207080a1409150702120a 61
    0x26500c0d0021940181d0002c117403521030404a01c0384203800d14011010300811078101c040d0f43c2440f020030101410003c104c00801c824416084c0303040d240e1180c142151140400050400102e9000f0444040910b91004460365514001c03044469803600170f00070b9500818064020450310641401940d0141e50006503540c040c481f0b0b0701c20420b10742c0a9960351403c0000c0c3d203000003802c40b41c00c2c000d80034580e1a849556074a0416a100e2220190004404211440e14144490f06000f0000744180c05000c5820710600480807824400801c80d10241c000380b07184a0f040c00c04c213460758010510703560190003c0c000c0c45458208100140c1101020310b4030211243d2035001c40c04245400503124401e140d000d01032005c00109490320f04404e0307005811082901d52114010044200d01744201c500d81040350703004508080650740c44441c039100d040328810030451400001d12002c0e0030081210801c8800404000303030344078040c400103c16005114281e2103030059403103240008601090201500b0780c40345500001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 770062778 1250 770061528 770061533
    0x5010e0d0303061a070c0506070c06080712020c0c0307060302030615160f0f14120406030c0324030611030702031b030403061103190608071403120a050408060a110304 73
    0x6281014003a0101512000c0000b03000c1307580da900c500b04a5040c040d156a40710642000c0400e0748141d4003460090808110301c0c40840c9014813900305891007898614201d446006d0b08551400c2200c00c0544400d00c009000c20209100286182c1500015019a518150398000a404901080343c0b00d58001c123100c1e14a002603d1180004c010340503217850100a5078180d51504c41d40303207a5103a000c40300710100003d2001400b20310080d481007080310b000249148601c1d8503910009009c1c074841c40040c075807294003011155000e500600c2000d40c01c0a10380c21a514500c1500c184d5401d5844151400740c6407000e2402c4039000c6000b1a4400c0f0034a400842c80c2c0032440010743c0244520050400c00350109003c00300000e282d0340101d851f410325280c03000d0380346d00342031503c56020f244e003012002c1e0540c40c0c01b1041000c100c000c036585080f81c1ca03002c6031031302d032a0140000c17070b0a1400220600c0904003001a400100c2d40e00400039200b981d0302041125040c1d03a41288240444850003176486042da81880000c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 770064028 1250 770062778 770062789
    0x101a04020708070b09010e15130f020d021801062a0314040905070207061205090601030b07021f020315010903030c290702010f0e0106050d02060a0905060d0902180105010e 75
    0x1c416124500c4907140c0521522605102d010668170403c0a0351500c9050704032403010401c110390006040e0a004403400d0805800180c442e06010003000c0e14840f407054802d55440031500e400ca103070094002c0070321406000c00c512034a00c090044c200461241c45030066059412085c100070400781844070960b0004544058504000315141d040114030100004070705c1217000d0185030b002c2c11943d0018a0480c1c14236a028004103941603890503035600e00350401c0941600003401c0c0e0704503600501444450389605208030b003070119102d0702c0390403480391122540448100340d00661040410142000344c0ca41d100d0b0044034030007007034440034000032821402c4601240b1906d060500c021415118402104140241500c82c40310803548040580d5482c20400702c801c42c5409070400e0b220100008000c02030805000800040343c43d031010340140c0d00803079100d4100e0700840c0300701d010344402407041d5100c10700039059001920048800701c1c0604481c46004840c61044107009069680507114035042c21703862010f100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 770065278 1250 770064028 770064037
    0x32502160b090d0c1401030501090209030d030903050c160e060102030c0303070e010504030f030c0b010503011104120c0906030c090e2109010309021c021c03050a05031302030304120302101a0402 85
    0x15070042d100f40e043c20000381da0b950711400a00e182c4148000441c01c04001408a0318141e100c0400940100107402c0d4941c1d002c40d0414481100d405c00007000891030034110340070b003d0364414100341d200d1174080703840200307810b81000c048505940b01e91150395280d01c01240c81e800790785e2909185034403e00110364014012551441034400624041d03052564076100c1c0303882011103e60580107e070502407284288008402c4050140c6025002440112011000c2c09118440e501c03501103524103a400c2c89080000300c08240d0000c2640540034090140c8030305001c0800c50b241d20074111624500150341000038070206545a00c100c401c4850241d04c082002c407105107510440034581010740d21418403006a50707012484481c800440c00042d40d0708903620610070121580040c401d2094a50200d840000ea400011561074925a251158076500c03a4095a015425500c030004e5060201040100f004113146029080b918000d608503289d00b05108071090498a800e002e401008480700e94403006c904180e002031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 770066528 1250 770065278 770065297
    0x303040f1103120306100e0a0b090d02040213180902030601050105030903071b090e0f030304030513090501030516090b01020d0513050603091605011d1003020f032502160b 75
    0x505046007400207402c094a003d00380880a00200c140011810001410303035040349207081c00120f0803200b4000400103045071203502c6100700d0002d044d5517503845412000d500d9543c0076205540b41d64055041d60b1002ca143c0c011a1801c6401e0601c1001040c61809031907900c54024010780201c0c1d0800004550702d03800140f07105100c2c4010006c50001a40c08516981030008142011803801d0600304c4800564107441c1ca0a91a0340c403c0c0c0003121400404002c0300d400c281d16042181c0c3c2e5080c880309400b25203007613501020440340382070000418813101080c0c0f440382c0d0b070403070b0001180507454a84007021a508000020700680c00403103110b1003240104010248100c0d21241c0d12021035982c4d00040c100d600840d84444180c002d03550050f482c403140041c000207420b00342001405202e02c60281c20681c80789401c02c51103070743c09504c1900224000d50441d00e00100c40041c60f03a403407410038540b001d19004403120201040503106c42484487c40420301c441030205490003900c110b443c024141c1410f411450b0b04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 770067778 1250 770066528 770066543
    0x150301030f0f0807030e090603010c0503270a03020304030b0c0c0a0627080d0509010b06220e0109090b07030b06070b040623040c060e01140d1d0709110a020303040f 72
    0x300340202d03c400c40034020a5129030390b0300301484000300600c8250030029024034081ea04000250b001c881e007040549500c5040c029200600c1c0b0040000e40000c44400901540580140030030b0030b0a06501200500c1501e0050b500340820b510703190403041c410300c2030a0074061540c109281150010740143c0041040c442d0100c00300038000705400e00380d4800014240c08544209002803494041140c50051030703400551000204440c80401c0b010490700d10a5095a03043c000f9619400d0701030441f0030060b079010b0b2051100c01c1300030350303100c1000311300030b120043e400e96010704114001040740b8440d000344844d110001d0b08290510389180e481c0741120101502c1202c50039250540580d50743c8600c12202c10381e5140780d02510440c00d060800e003440d0701c0b2a40020040003501c441c1e6202d16600501d810546030019480705039202a59040c1d04010001d040041107005850602c1c44041c0800280b4441070780c503d40710420840d2002c0d04111120700c140c10050b400b61f00300380b00107004210440007405c0c0c51030040c0d07074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 770069028 1250 770067778 770067803
    0xb1804050604090510090201020606030604020d080c0a320606031f29120f12071533050a050603040c09051303030c020a21111209030c150301030f 64
    0x4132103050107141002030086641e03d681c00c60070356904010440c1c00c444d0a070050401d0f8201b07034000c03541c48010004007400c109000515007407545010014100c6840e0055440b42070341c80000c041e40310104048403524060b00c0500c102c4428030380f0203d48140200b100a00801d07080a201602540c016010071515440a5030342c0e2001400350005550b0880c258a00140c0c1c11711060900c0070046a0004190b40000690014074501800c007000900c000004802c0d21a80b601c4050524100d17500c036031154100700103642040031506040c000f2a10307482c2c0420790300000c41c1c40080c0c030811500d108603841c400d00d50b0019407030f8000c0200c1d0901c0b00046800c6405a0700c1ca5088a0b15044e804080d2442551480b4102581e00c00f02414580d142c85503c04400c040e1002c0d1001800c0c544446c0d0300f055001c0b0080982d40c400b1010225500c2c0184050701803c204482500d0084101a1000140f43c000341003090003805198030400b21494000d81081e0000848404141188d0071030325042c1c5803c003014803c880040c0f1030741 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 770070278 1250 770069028 770069033
    0x1060504050a06060314011d04021309210f081b0403170403051c0206071206080a050615040e0307060203100902071506080c280b1902070b180405060409 67
    0x31540305101d40c007000b0540e0744ca8094020210b170820203684400e00c000c4401440800c03803504030180c4400d4580e0000110b5141da000040900c00c2401000c003d02d490310305160104010703c04200c20214032001f4541c080140d4190944411104281400000c0c400c400042e00b14009a695034030300f04c41000c1d8540c107154890741c0c0c5d4070004100994010000801003010420000100800d949030b4000500e00f03030803544d050102954502c406030040081c00034003020300c0c900071501d81c0700d440200b0409044988a250604080f9140d40043d640c0003856000c43e01c43d0416030a0500588c04a01004401107141848a0311b1341d50003508003a01d584070251603540300265070285030002d0491705005000c1031a84044004405040b618958005802908021064445542c484904c0d220480400e203141040d2045101c8280f20001180c2090001d2580070503084000e40480350b400e0700c0607500d0f8086484940e100e891259207030046400740c1f0900000c4141e041030500741900f2841c6c01c1203001e00040307110f4140c1d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 770071528 1250 770070278 770070281
    0x9011d2d25080709020403110d151b11010e06040f05030c100e060601080c0d020f0d0e0601030209071403070e011b050105100e01030b07111c031416021b010201060504 73
    0x900411180340c019090902142c1c009000580042c10028011481c0501e150340b105000318044003003030305c41c03402d04910307006000d0307940714200202807141420018006804003d004081c01e038041c2d20b00152074001100c440000502c120143c500c0d0f074000422640d56190382d00181d80344501da04495a00091200101c0b480c41000f0102c124451031201041f4120302c42066450040001c100d241040440c80500c80c2008003d402c40316480c24a01015030364802c040303800d01d9148182c0441042d000d140c00c0c4003881c2110042045070603207208441d2003501c0c0c0c803a107a0440d0ac0e15003c1418035941c120030030110355024010002044c0c5044103041203805a0185044510307018422071096030035075150003c01c03aa08401101c030001514849040f104254110b458440720150020004002d10085000100310003000304000c8408814100c034500d840915140010068029100c040d101e40358070402042c03590604808070f0950107103540c002c040180e0341200e004810140c123070880781503544e41c0c80041883d8403903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 770072778 1250 770071528 770071573
    0x304030b070206010e09011407180b0d0e0d050304170310081f1d0a0b0901020906030907060e0f1003050c2709010b0403172109011d2d 59
    0x1c1da0094041e641c5003109640711000000c0010301103034940341c80c60141c401010350b95030f00702c001e619000c0440090010484034400080d00900040e4030082440ac6181450390004007e07021010b00361103a0b02d0103a0300951b811300095400400303990354034891110800c119005560310054a4503151441d651710001c6600b80000300d5944840c2d150100c4031180840300a0082c100e402c0c20340381900d164000c0321a1115204c002400008001d032088030041010320200350180c8078030810003070075180e49081100c01c140e0f03070740c215215000200e0742071484a0500e1501107412141c284000d0700c00d40c80300602407402c4005102c01000645c406905003c00310044282c00008990301c0000e00940c002c08407118104000d4030b40507031190712071610402c003e2001500070030528030384019a2600c5a241e80d00b000001030486001602010000300d1201045950201500710704042081214140c5001d5800c00304a41c64034201403c2503032030302680c05011100c0109070100c0c0e03400d80304201079841e62a898101c401041c0301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 770074028 1250 770072778 770072791
    0x203060a091d151005040923160f06050318010603151a0607050718020c011a01030b0d0809100c1b05180411040207020301180606090b0f0307090e0304030b 68
    0x103008244003242c0100000300d10f0070000089070b009482e1402d03144010b00c001d8010a80200d4480b083c1c1e10402507884401d41003043c500c4d098820f074055488805554020f0840d03420041c03007403070fa8001080629954510283c03211640d0b03140c41c0d5521000c19480180060f91090001c0d941c511001001c90404810750030a690180d001260500601070340200c1c204001d02c3c1d480c4104170800560000400c00182e00040b0b030351004030740028040d001242d00081c007544086040130350030302000301d42c010706104076170500007401d0300c0030440d009101051140312070383c051000703212940820001c03a81c0e1a00085120070183c05150449001103d0b50312000c046040d800c3c490745507503160340180218030304131000048044840000f1829840c280c1c03a01c11850501c600100c1c040c99000070b0140039500c00307400003003500398101141148451945411001008140b2400c4100f502e0030301003213920b1403c191104131650000b4001c011460503e6a100300400c5c0c1c103402c0082c544030400c00080080c441840440c821003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 770075278 1250 770074028 770074061
    0xc061a10030510080309131d06010303020709060806160503060310020d02070201020106050904121404030614090c24090f0d080d0f18170d141f05010903060203060a09 73
    0x60442c002a500800e513002400315810910005103030340c075100000071200c61a080d021540c070b042074030303400c8008041307603054892405048000b109040c0c00048031011903801c07140030081941d84040154032110b050750010700b56039001d1001884544584091f5401c480020b007074803070402142010000305d0b03001c28506541070380c0100d090170941d0780a00c5042c009002c1a82c80d5207462800e0340c0e840e0a80e5120760040401e0084400a007028030b94900c090b40c1c082c42d4041010040c5550394907200c10400002c440c508030710f10030030b039110507141800606001c503400f00d9010124600b100f0340c8411060b4001d4250a0340045001c02054590341d9920340300044d56000d0401c00303640b07920015560b030079561a501c0403a48181004408041400d103803c0541c6030300d4002d1020303100410300780c41c00c44d820300c0f84403100f01d405424414903015032800c40440c41e000d082e50402a28981c000b080148030594154455180131a2640b1403c10126800760015648014001c140011064072443c4080444041401450120 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 770076528 1250 770075278 770075281
    0x40201230403150c1b06110f0f0309070b090d060f020702061902071e0e04110909151b0a05160218010303080f0408040b0702031c0e0a0e070c061a100305 67
    0x403856208004d800e49692404030202180782a00380c0c104110008010302059a83c6e181500750070118003910700c2031002da929a59540d0444068261940058818103d14003a040e8002000070312103040303032010078019140c407481c00c80315100e800090100403009401207800b005040010382d980030007040d2200ba150401120340c01c414000a180c03c3c03a1b9003060701991340308801b0100c00031602c50180112050001d9150013a030b00d0b45045032a0a0f2640b413100d8103d2011003d1100d00c0102248150300c0d04941207113091299100300400311403600f510082d038140305082044140c0e0620800050003526400c521000c0c4400d1607a02044000c81e0a010180031000c0c000010300405270710000060f04003080b46241c004504041d11001280d200f01d00c9008202000020b4080841d103060201c450080340c2c2403102ca040c11000b9a000c0c003803508107100203200e014142000300d042d01007190014016031841d640c40d1100410795540c03100404452003080301c0c80e0008460606542d071800940c04455003250780100c3c05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 770077778 1250 770076528 770076563
    0xe0601080a0c0807050303040e040327150e0f010e210d1209020312091203070b460603050118060c210504140304150e1503040201230403 60
    0x144902e50704200b889402c601c034108020790700001900d040d59100c140d0880b071a16585403d07155407003100c160001e40e562610340e40070103406842a01c0c00329101100804130440361903004076003141024000641c4414a0200507945500c10f4116540640d806000c01030001c1e0610802203041d400c01c810740c29a64403001102c8511584000051110317995144c00780070b45002503000a072200c01c0100b1025600d60040780114156076103540a40c002042142641d036a40b0031402e04030201c0324101c0307010a070000303501002d12015a5031841c10480803d07240d4880b03007051003401c4140145c03844040c00f580c1d06807542c1d00030001c0b903801c2c170483c0b43c1541d200520340201a801c0c0b80000c25100e1400b0081d00303201c5d01c070040a91201406d0800c40744090707001400101a515442d090320b444016800305026403101280c042019541c4074804801e014903078858070f400202c2e607000c00040e010600c121100001c0305001140055016015081104e10008007128034081614204006504503500640c0d00e0140c41681000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 770079028 1250 770077778 770077793
    0x4081506041109130f06051002070905130f060c0507080313050601050415060c06020c03070f0b0a0203160f020736020a020604021207030204020a03053301050a02010e0601080a 77
    0x59071510311101800c10b03403d034000550200410444051843d200c030b55001c1a0409540144c02815004180714010040c01000035a6605035020740440e071460b14020825111040d0151201c0a9015608465142d120354444024046640c034480c184401400f502c00000d8481019510070b8030805001da40707255550505901d4180180c0c40039005500d0803182c449180011880700c8250f80841c1003210340c0520902c3d01c44024030842103008a14040810f02c4010401c51150321480f450040e94a020a80c44032a0590201d1000b965a45110001042694031150242104086440940c0143d55a480d135581c810a940500c01c4203481c4911b211000100e0012150070b003030f10b0741c0204a4000c50400001c1107029545040181c0060b01c80c100c030107014810000300f0440c0034065603001d4025034480104c541e0180107810180d950070718200049021850004031401404d4500c40486801590710550200669041e40524902c0341155200c12490f14818001c03c0b255000709203813002803400c40c800341070416 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 770080278 1250 770079028 770079041
    0x602031503210307030e07080303250504050303180d05010609020c280b09033c1614030409060b07021f08040308430c1e080408150604 59
    0x5808511204070b00d121010520540f0381c40741d2542000100c2e00d828600711442c0404d1603110844500c00002049141c081c104000401900c00c0340d14850903091505c2c4c180e03214003d5000301601640207026084580544a171000845503010301410507503e8191165801e6902c5078111020351900000e402407243d41c2003000200d001c0124500d005400459403a521807d07a00170000b500401c0442d021549083c020b200b20b80070b810341c00103404a11503a0440103075018544040d15584500c8418401340c103403511030b0850b0b42e4000c248004202100d0b45a50f010984005025500141d11060102140000c4c1c0741c132418002d445403c80c001e454010781e10400043c1b103c0d5818030000320940e2084080050b420a80c4c0baa04a94541440303000d944c1d0fa203100e0480007038110050080d0000078039001c0c803000d4400c040320245036141d520a01c01302f12109000c0e9100a4922401440642c0446407440000d03007507000c2c0400d01d845000c403646030507604d03060705141c207003010105101d0f00d907c1802d0001902d010300c60f25 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 770081528 1250 770080278 770080303
    0x1f020106050907030207050303040227150a0906060e10020f0102040801060f050d0b0411190b0d0e0609070b0c070510050d060e040b04060906060e01080307150e0c0d030c0602031503 79
    0x179842c008140d50340d192039000c0548000c2c000e0410702a1500e691821260003030503034060301440d481604d0151300d414104c00c44203505600070002d542c808501c00b0384074041e08003580e0b103a0300c1e1441d41c109520140320303610044c0c0e5440e0086007d8540007014100080c00108000c08444002080040c107000040b5180d50165000300c0c442d142d10009400020301241031540d0003034122882c02215212880428010b91b214104114085000f182c041041c58800c006016440400d850400045a854038016500c010a90394040207504c01c10081140071843c01c001d004074031205058803992540c84003c121600214004440820070125404984034003510650004112001c514442801d0940300e11300da062001c1c10203440340c1d890318842000e01031260048030061601d0b0440d50410341c6d454046130384940082c03000311140347c3c82021b081c5020340709004161031002007002a0446140c0001044080d546001d000c074107010314031514402184451020794816080c1c1803121a0308810802054105011801c01303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 770082778 1250 770081528 770081531
    0x90a06140d0b1603020405040606050d0c0315050d0204150801020702150a0c0b1e041101021006030c06081f0914060117011a040306090606032603040305091f02010605090703 76
    0x40c4021542c007201564100350320800c01425200002001c80c080e02c07954011907002428810002201c07944440103005c8074003200030410101070160012010b60700a0b48885c20041003118003030140e13141c1443c07005202480244000789004000e142030942000350b500c040d01e03a940c082036035015410440e10980e00c43c0002503040e8a8010741c41c0700070f03002014050f405803450b07041600148000c01600580b089029002c80d100840740340c02d10348880c4010458981d240103001c2e800707443c08640503501171a81a694001c00440e0030b2410003000b111040b03c0203154009200310505410803002201320b996014019484c0080380100c50600420908d60300a0324150402c044080c845000d511100007007070640e40311035460711a510311190008503e001d41e4001502841ca800c0f191000c125460380240e0440c0d103d60390a00280740c0f9000d0302070882c40d1a908000b6554000c00006000900c40e500904121000920038141000d03040f04200c2c041d0440300c060f10150f992540c09001525100c41c0d4990f000c01c240c0340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 770084028 1250 770082778 770082799
    0x15021c0c020c102109050a0506060a0b09010c06090204060f0b0306010906080115031a03011107050d050a08070c1e03210b180c07143007120e090a0614 66
    0x601c130b41c19070b00394441c8000e1440540c0c03401a4554000481c0c40c0c0e0040101c0c0c88020707460410540b550000c0e11007030f200b000b003204005861440f2400b924106071050b1180e1101c0051a12a4000780002d01c9089030b116a5518020078103022044650001c1c150f02088540c03640707460000588000700d0760b08100309020558004005000c0700c0720380080c41124a2401050780340050708006c2c54a49038640555055007070603149059090307000301034070313409009104554500500460543c2c540c815012060001690080083e4200d401001030851440c4103543c07124407807034108000d4030a00000315045000442d10304050110503503489003100c3d18000d1a03001c00649003507000090601c801040306000312441072001500c04002c1c4c1098407122904000982007501422141c0d42e243c001e0061003150302d100d1900012281c50002417100d6a8030b04a548040ca80781040e111000e40c46050440c18040144c840500c41184c0c40c0c04070110f00030455002e020500d5400c2c8495004c24140100642e402142c4661 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 770085278 1250 770084028 770084059
    0x305070305040c050d0c091d070b0406020d08100308030a0c1d01020723040213050a0b1201051203090d080307031d060c1605150f07050c060415021c0c020c 68
    0x307662048890440f040920302c602c0c1c2c50448180002548030b03a03072245c41c0082988146001023220720201901c0400d0318482d0ba2209517007021401280103940041c1d100914000c04240101d004e00d40103a81107980000c180d540b84c0e47e50007594000c8a82d04040780d00c4a940c03004075608400000000400b0151051500c5034000000351b440145101e031249512021404000c02d181c0c8041c034a1100002804c19540c039a0210912408169140310b2140190008070000845440d65001d5803040f00c801c25001c40e00340d1a11040005e00c050307041c03510310030b800100640c07501941d0b413001140c0c200d44684041c1f0345a1030302580140465000261f0007080500c82e0034210780e09039000c00d40355401080099141d84a4a00d80a602018040c618008187c0d1080d5520085010194007032284104040c407110391032903540c200c089400740102d1406082c150b000001040010320001500c2c0c4400d0585140107003012044400300c5009074418011810885d03a0388030b64120158140018100441c00b81c440010400404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 770086528 1250 770085278 770085293
    0x3120604020a1707031805061803030c040504020a0509030a150c0201020703170901110c01050a0501230909122b152907030e010e040c0903030e0a030b07080106030507030504 76
    0x90b562800740030408400070346154000d500c011801065038921b1495140e00c2e180095580c11700b90307490404501d04220b540300014000007182d100e0842c9224040c1020710b00010b02c400f9410540c52103040c400280081061600c0c1000307151a040c1c0614001b104442045084e20100d400d410702c200c045900400015000c2070b0040000030102c1100301c8250b04030b9581c00072890040c10190a101070102000812140d1079205421650140c80d281d003003009241d0341c9401b8041c900e0001e51140d000e40c0c0480c481c8a1480c90140d80c42903100d0103900550b035104a43c00d0701e8200c00d038000024200c05880c541205900048040341e584141e81d03ca600030024103401e00100c48001e0001d114418103143d10b913050405201c80c0c1101401341a442c610f02030344031140c514001d0f00001c40d0100b0240040c001e031031064520b140070700844450041a80311004d01c05c0c11600e040364448540c00c9850f8004c4912440040050300c454035503071041c0785c2035494030415414800010300341c1c0c3d80680311404060801c17081c800801c044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 770087778 1250 770086528 770086547
    0x406061416060903050a090501090e0c31090e0c180901020f07060501090c14040b0a02070f0803040e01120c060807031b021605040515090714040803120604020a 70
    0x1142030498449805514484440302500c4004260600300340d9224101038100019014181c07490701e6202e012600c1d2001164140c0407441010204202e0101084045015600402149040309000d09003030082d1030031118500200900035480705505c002c03c12248013903210b064103040c401c0300540940b8214a000a5800c2000c2c0043c98448103640007141d0509401d6048484040d8021207007078548005003044001080c09108240156007005441c640480c840d841c0e000e20940200c000905107810000d85041c2d680000c4008025441a50000f00d0810b15803c004c2c001442508015a511400c15019250201b0180e002000c11020f0320b131345800040042548070240d814502d0640b0255440a004401801d00c90b0b2050744581c0f1100500035880394003103400c034080104111001d0720141c0e11000d1004441c000c40c0c03000c075a0008182d00f8041460001c0c0c0e2681c00009500c0c00321003000c0034645490081d44164400b840980c0001070304c07103805007049413aa030b0049048400714201684a600500307404c50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 770089028 1250 770087778 770087807
    0x106091e050f0109030b0103030903060e0c090c031e04060204080c030a08040510031e0b01020615030307061a120114071b0605190f0b1201020c1b04140c0702010e040606 74
    0x70b445501003243d02c1001c0120040da00038a0003a410b5131359007400b40107070116010a94913a420551170910968001841480b0740d18082c0c0040c00d5640d42c071300202c3c003c1e0405031002031848040020510001c0000c02c07494001d9008840c0160366a103011040c52400301c0380c002c2c20780a0740000050ba0b01003840e80e8184c1d4200d4005440e0040c0e180000c000403801482c601e50100503072042e079480d10f0b2414105500800f001c40e02030f000c540342ea44803400300590185a102034182e0561007000780c0e00c00181e07141c011400f4410030740480010501a00e000a00c9690b0304100010141c1d0341d5807034160601e5034020080d410407503500707103d503901c80000c003d0302c2400403034a409861151900003041140b81c1521b550311403031817903010800001d60384800c2140a0548081d40e607108068480d904640b5010601c01c4030034404041c1c008028505001d02080440381c82d0558840d0f120303603181095000c00380c45040b010312a888035180969034107800e05c00504008201070b01c41d0300692070a0070500c4080e801c498900750441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 770090278 1250 770089028 770089039
    0xa061205030403120203090405010602010c0f02190f0c0e090624090f07120612050705091608091002030f090d17190f09050705120109030806040e0313030302060106091e05 75
    0x400704d000c3e469403041e844076940140c50032000080143c0e042d400a804003465694000c107000310514200da5565440c1d1841d08810420240480051101d0300308601a511401c040e10740340360385600403d6122011180038429070040d000300400c2290704529515060b007001085007400d15201d000c104480b01c0104032441c07801c0c2c64408240c4160143c030044240c001c44d003d00380403c0340c841c1403004603a00e00c040119020b200307017207001ca494941140458820a0483c0304020917500c2e5040031911310001625103e100c0c09016100224055039000031417107a2240150070f191800c051142d207103072248420120040000c40a00700d0303222801d1003050303900311042d143d0484500b2008140e6800405101050425540c03600038650108a00800d000040300c10844059100d440603800e21400e80da5908001000202c0c006d00050162800c1c1c2c1c0301c08180303400b081c200c0381400a01d088001c42412603400c29405030780f202c001040801e601144100c0502000500c044aa500d030205403100c04086010341446030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 770091528 1250 770090278 770090303
    0x602010e060c070f050d180909050a1e06022b0c02150c09031507020609030f160f020405130b0a062121050706061a07140102160602030a061205030403 66
    0x40072110034101c05030018161401e241c4881009040c4507c0818a0340c1c2e010040a00081c030380a06100341c0e48150741040262003c42d400e60703110203244c0345020800ca040c5441c4113190000c5016440a408840340301d0088204400c00801c7d06a103e6100030052180281041900880d50303078089040540710812a4109095031280700708441c480c00b42840041d0148034008948410040e101c3d84140a44c0c1d8513020b8468603100c45180c1074a82c031844100042120b03003081a003046003100658003030310714010400c10031415483d0380050b003a140c007514455111004c81c4c14100600075590b038015003183e510f10f003c00c40d5510b4565145000c00c400f264110296080c9124001440805000c60300e00300c0120480c40100e0380e44600c09000e50700260340541d4000e182c07650106900300f4001b40c0c1c4c80b926070052405070404805a68071403400082d601d2003c195502441015040d951800d490960b90f4410030001d61207103401940c0c0d00484030154018502d030304200301450081030004c000c8070b003660b0b080746812491 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 770092778 1250 770091528 770091533
    0x6270e0304090e0c09010b0436060e040b07030b030c0f0f04061e0603140a0c20030702092a13050306010303210507050412030e0301090b100602010e060c07 68
    0x640c02103038000c1d03065034180f001c0f802040f403001c035450302d050710102d8603c5500d989680500b00c4a00890040301d910400c210b038000e69400c01c5c1000841109402c504a00b405a145145030095804aa1001807480081c0b0284420403075018296640055a4078007001049001c0d400aa41d454100c5050380c0110003020921403251184090300040c0e85000d41709000c282e07070381c40c00f00d01060940100003030005514180483c18521038010040c0083d10700a0003601c0341c0b41d10382100000c0480ca503203403081c800d90b00c0c071244125100044a603140303e0548003071a00d450b13460051020340403004114480c603100d0744085414410b0342d03852050443d8070100310680c0350204480603070000030a54001e40e13410b220b00000042016400540d844c40012502e1681401d039501148080695105840340c001162003840148070034841519040581c90003403a10790010401203002c40d00310349c4000c00584620180ba0104801602c031805804018031103440204580301e000c400d5161681805043c403000e0300310000c0c3c0c80c001d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 770094028 1250 770092778 770092783
    0xc09220204270302060f090d030e03070516170106051521093301030b060a090501150e01080c0412020609040c02060703050907080703121e0f0306270e 66
    0x10400c14009524542c580302e88000e100460059508070014801c140001d44050f05141e4218011201d41004011065412005038041d200086040c030081c07105121960110f00100708420b850a4504d9080070002c0c2091003280c0b80407070206080901c0e0781801d104010503141c3d01d0742086940c10111100f512548501c404070310031013008200d0345203005403106110100b440400d0074140c0307030070403618280e540c012220700310340030030070319080901880f09207004001148000410030340c0b010004050a02c2d154032002908210303402a00007030900c9102002c6110b41d60b4100072003403440c1000f4244020740385031801030340c5441c5c0b01c2c0f40522141708c0c0b02c4410728070454540105071500d62000807c2070140e00380c0d47c24000c0d61001c04580400c0043c3c00c110114100300070101d000415030b11218007030b02141d400c548403101a945249041c8007040b089a043c486040c403e005510141c40c015914482e000324079601c001c0c241d445541050241d1400c82800307ca10009111f407200010a0080021840e4100b0a401e0303070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 770095278 1250 770094028 770094041
    0x180a2f03031209013213050307140f0d02150108060c0f0706091a060f090915100e010e0a050106030216110d05070923040203030f16150603050c09220204 67
    0x1700a07101c05900000b04100c1000440c0c00c88481c04140d07441a9554808211589007580020b03100d5001000b08901045d0f0091007812805009070403a0300000403a24200e280424900c070010058108501055012580070f0041740105004401000b140c207000040080f40d106214000d1045c51001414000300541600000e000b5030300310242e24000e1803100c201c41c42000003100c00300d114848640000c0d88603d0f0158001d8000e00c045e90040c02076801c3d880c401e80c50000023031b1180150000c89600002c201d65072404243c064641d170496103125040103540203094400c1030b00500c0a040c01840381c3c015148090312180c41454220907900705410b02540400c01c80c110490000c2c0140c080e044020800c0380c105e405c4270102980100400d181c0084107e01111898001d0b80c0007949500108094201004400090b011411580608121844003980e0b148140c0c460b105100714400c1d22444108180b05052000b519030079402d4400210354070380f1030f01c1514040303580319070106255000717003000040d07403282c0c1d002d030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 770096528 1250 770095278 770095301
    0x2211e090a0531060603180b070e0d02030703060c0f03090f03051c2d1a0f03031b0a110117060103050c0f03040c1e0e0f180a2f0303120901 61
    0x50300c0b050b0f2145509009015940540400301e418403860306502c940052281031840c0d00030401823050317142e10b1f008641105c1c03aa01c210380e022107000319450160750144882c40c003c41c03060f40300240032421903002070500702d0540045c80c2413620b003002d20030224900060070042198076103401950341b1150001203001ca9201382c00640458503000c050000c440351000c0142a0238800f03281100302c1106201c00200391010081e2128030115034442d841c0071401c1c0030070b200d105400300a09a03424402610200c001c00c2c01c40ba0150856036202d440b94405001d22000c191b41c1955003031900000950360104d046a4074940138200c141003660300e10028040802060039605a14211868180d072401c150a141e00c070110503010f41080e1a01c01300e04a499010010b00040c11a15102c424845076034401750030540019004020641c406020310401154040c00d008020040d4447c00307003c0c0740c180e81d00040c0100300c3c101001040d4612001d1032035107074070b0341c0000541c1ea01500c115202200380d5905400301c2d01410042581c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 770097778 1250 770096528 770096599
    0x52a1e0309070314070b2703030307030902150301050303122502160828021c0b0a05091f020c0c0a15020d0905100305060102211e090a05 60
    0x140400803102281010480c4d00038048180c44440544000e40c4540c1c6910600711121410010205021440c400410100c450a41c142491400c0707070011908540c17049078000002070f5241e21a00c214a00140150100c607032000500c0c0c1190b041c10f000c81e42e070744904034007240e4030740d100000900004183c80b41a402c5240d20350030090301284403030f80a9911020304c1c00030140112415004180004002401790b0305042d114001d0000078550020300d0f10514103160140e8001c2d9903401c05100b140048a40e81616503c2281d00610307a14080c4210b000f11540a01910900e820122080c415190042c20411480d07940e180010b039100c5c040e5090a251140c64008642c200309000320001d80d001c3c100341f80c000000318640a0303a517071400c030000032602c203800344c02030340e43c4000050014600c0d1882980990382c4580c06004952141000680d42e10701022803824032040b45000150f0314281101750300f00c000000d40f01030529410071958600180c3e14a6a5000c1c1034014443e60581c0c20f01c084034050029903a0380001e46 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 770099028 1250 770097778 770097781
    0x1a1308070b07020906180105010503040f20011b0809010e040906110306100201060803122a0405040e0a21050f1207030b010215041e0206040b0409052a1e03 68
    0x19148100d80003001c003a1301c90481603001450b5400c0032081c60818454100d05550f0b560b09060065078a5080504251221110002c404000854007111940c4400090352106042c0c00101d0004007410700b074090441c03c1d007140d000f0050004030248280c4d0280d01c02401d00c4007040390404045001803540704005810242010038092800c0d807114029030191905035091007500c50b15031001e90070b0301c03041c0c0b103122401d91040049641c040940b882071904661243e564180c403d050f8003803140f03100c06900d90020321a00c001030420803881c080c4104a071008582014044c0c40c16a900d4031070440d07824880c061030560355821511122403099085900c0c60400d803c8498980d00c0202090086c2d96048604d8400303e450214410255800014080500d440100c10424147d0392580c030705840c00c80200c0050700e051300c01001100140c0d03500014001030114001205c0d150341c6404010301c2641c102420350400c40c0d0080710400c50030034200081c50a17400e81c14000c55514a24880070792041d400c0703070814290800b400f00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 770100278 1250 770099028 770099039
    0x203070e03070e041b060f0c02060c01050405061812030c0a09050d1b0b04030f0609020f3106030201171302041b020616094a07091a130807 61
    0x240d0742c02035010b031140020383d2a0000d55201801c1946c05a40c01080c0341c1e02541d0b80842c40f0303d00c40c60303c0c180301400482c1400800780c40ca90a66a00b070310200c03201d030017072030070483c44202013141012044078040c0285503451b90b800c20810702d0301c8068011444c0c1c0e031001510000950059100b5401010042c1c01c00c0a400864104640400c00521001903042c10716000010780e05100030995041e01d405c15607200d0007040c1556180d0080c0142041240c00516405545001d41c1d1206081c60a914942440d4415030340b0400b214909044040542c840492804606002507640050351103040ca00c200007060040d140da18101200c0f42c0000c80c025402800e00c0c20107454009031440b04803005049408448581d1140c0396650b2000a550848000081e0108020054984140c240d1040208403402c9013090700c02c101212401001e000e9060034801c591a140d4800442200200d681d00503c7c80c500110070350304040410b500c070200312408040015000c0b13803049100f4000452500204484000c9480c0b00366100e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 770101528 1250 770100278 770100299
    0x7020f01180f2a090b040203160309150c1101050f040f1506050301090303021207080103110f0d08030c07051608060c0a0e030d02060613020f04170f0102030a0902130e07090203070e0307 81
    0x9004e03070410baa040100c40d51403400d203402503a01450307080102d90b90794100141e0440003400d55260948a90070b8005484840004034410203101218541d9281c00014100b09900e080d100c003d4940e01a00411104010105e10340303103141070f031890f4882c00705502c900c9070081840c0a845103421640d415482d0408440402d0f805900501c5c20041c8410381c699030b41d0714a2000d8a40701024440500b00805081c3d200c201480d081c1000e40c5130502c020611500b1808039100c00d0f031140c004880065500e074000483c04107001e810041c401c492810400d00ca0007240c10300c0320b0700741c446101078210030030143c020403403050301e5001307000380000181c0140c100c1d4410030021900950b108404d40704140241c0c2a42a506c3c01c0300128000c0711038000c0c075030703203100d01d8503262030341001361030078800840a4a0f0064403a005030450003030001314080c5c1a042008982d140450041103a4a074100c02891855071405400600450000c6180d00803282800c20040c0c8981e40c100c0107645600d01c40e0308840d41400b800c076020840c002d52 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 770102778 1250 770101528 770101613
    0xa032106080d08010e070e040c02190602040e060a080a11040608060f1b21071b050109020315060d0219050301020d02040816051f0c0209010e07020f01180f 68
    0x46030355002099030394416403501c240061b1407203800506000350418180c109078010070b054030781c10b1048a4403208520720450580c0c070016021a08150002400c003d20050940b220b5080138007212540345443c5031520f415520345000c54014180d410003e0100420365030355000800408080041d035086141c407100012074000c0890b220502410741c0c211000703905280c6419100c5040b8024a8084821030040e2940601d10000700700200300942c4181400b20700014201080000e0711640011480380490b10400d03080a0360b020b051922030a40300c04001d11952944d100000e015010359148030350007801e02e81540e416003550403154040d0300015811615054580c001d01c2116036403025a01a040d078958104480c0c0034501c1400e9003d480080c441500f005c000380c3e841c010740940c0c1400d0742000e2aa038040f0309444000da001a4400200400300070140e0b0b01440703000711201d2184000c00c002d00c11140b5800204803d81005411103000c040040200561481c100b15020310b0a1810310803600d14a1924040010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 770104028 1250 770102778 770102803
    0x109020a020607110c01031a0409050d090e0415050723090117070503010618090606270f06110a020307031113050f0105010518100806210a03210608 65
    0xc0b100080e1a0511821544440c00504805401070041c2100110040c0000444400441071032100d00a20b0313a0342c520845103e28401d5002c1c196040011101030300c030700c44940c001c0a4601d10001084000303042007800c0f64116001080000f42c94481901c129001c030080800f0b40b21f607107829a0807080820342c40f8080d000d5030200360b1750501d80d0601d548810300712100039104030f000301d5020f100500c0464000c15245003c00c0c48804c6841c034113561842020b040d141c40d81d009502040f45111046040210343c40182c001801c81400d20100310b10b040c040c04504055441420b04005841242c1e01f2000402d00807810740d1074008080b039804176103074141010300c82408502c1505c100c101d034041600c4543d080c0a40c500c26448201c105000d41e2038180155166440441501000500710a4030302c0b46555400c9a0100204169514070f0903107040801e00c4418205040420602c002e00e00c81c0d5205501c000405aa0b0541d26160a05601c0e640e0944214441682800141c41034104000415610000101901a0503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 770105278 1250 770104028 770104033
    0xe070c061506180506070203060a091e1a0a0207020102120c01092406051008010905130b15040513020a03021e0607060207031d181b04060c02040c030c08040b04060b090109020a02 78
    0x250b0380c1d0201720345842060002505500020001212114558005040719008044061041454444080005600b02c0c4111000b125002c40460b10aa9030080c8990105895804618088480e00080e540b41034040500c2c001407400624601354540170340000e0340003644041404101310035041c44085000c80c2402100c5000d01d0300000003824580554401900c15264445030450b034241000034000c1d02d002411500242c2c09080380400041c1040821441250b610000c071000d290840100016a0313405043c040c0d480072140c01c40005685c4080fa80000ca990444002c028103124040d06080d074286124121340c024008501c000a0003140d40080c0490361190340c0d59540f202c05000b0807107004105030210703500180421402000d0303407090b4a0302c0380c01c548810083d02d04c01000155001ea00c0d070203a00080700003984400701e501142071a00035041c000e901402c09001e02515160002d22110b001071000d05500800001308007800754990024003004000f0b0148002507840b00c044070b000c1d600040c403960061 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 770106528 1250 770105278 770105327
    0x90d150603080403060e0a1a060103021b0606090714041e0f291c0b010212130602070807030b0708181902131406040207020a05030607180605040e070c061506 69
    0x3e002c00b144a1f40d00540c0b200d410500074400a0010340d00100042140d4103146d800c02030044a140004030320104442d044000748920700c0d000d4144802281e01609a4052116001c15280100e031004266403c4e0b803100c64040003401c00000c034210039082c1c25808414000c052003030104584ca034804a5a203600c1d000003a5040d1054012800c100b24410b030480c0c09084c0c2c00d00140c07a0200f6a003034120070035401e814070403965451600c400d002c19070351009070140704001071480208030541d0144904c0340182201800b50180e285191101070403503400421403020040504006411541d045444400500000701181c10105421410242d40b002062050344200c00728400350042010600404004408207030044081d0388610040c403010750000c5404a901200300f40c00880d15880401c0041e12078180d039510025408801c120240803050160000343c1041000c010500a040714101da07540c00c010580351944041d141410510010040000c88071000154202d000668039449070030480038a92100102e000b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 770107778 1250 770106528 770106551
    0x3062c0106140f07020103140a051801051311031903030213051e091803031911040e0606070305040b1606180506040206030903040e16081b090d15060308040306 70
    0x40b48510ba0340b5191070104000b10b03001514008040e111413441030502050321000c801241041c407108840c00451a56100108959008880903524201e26904020061810010030107460900d07c0000a00000000b80f046007842d03d0800c21483c100201c3c0d00d4160003101e8902e030040281d40b0941884841c8114080081041c0c5410b1984230b0b031b00e240803005440d442c0141d400344022141c0003044850750b41c803111010080c84d08144003d500c580d60000c24020480c040d040c1d02d40071190300000c00c1040240c1440244089403a070703000560401c50454603241c0b0b0f00c10740c0c0360884e8107114903040703406030030008a003940003400c0c00700c10078070480c3c405c91042c0241402035160758040c0441c91409410340d8800740200300542042c600960b000400441500c0c03405450b480c00016500d02036500d031030301c040a4a200303030b10070398049601c42c2c200440000071142045060b1215505009800740107100c0e620b03a0701c40c17070200310010b144600591101c0d0002d0141550740d0900c2051034100348402d46500c1c1c2041e004169 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 770109028 1250 770107778 770107787
    0x6070506150907080712020f160c06030608031206130f140a0c050a03020d020d0c02060f0906060609040506010c061107020a0812030103200303070606030510200a03062c0106 76
    0x1003480b855680d9130841c0c0c1e65103001c80d00c0b01043c11802e01071079400c101e21440503807c03800400035100348010740c0042c0c883c0f500d0030407480d0889038002d9040600d4480c0038400e101d00403003128004603200c809811345495038000900401c82181d900300ca41450b02402c00c540c20362542008444040c0c03102d405660b55103100f40c481c152908200d1417800a00100945c1072014060b078003502c08000c3c9110014100140201c00000702c1c1d0301e0141e841c0142c1d0080040100f00da5200c4681640600118050255414281b000c00d04601450b08803620031034941c00004e1240e441112413a081580100060003407100702c440c4291079901c04801030740103200c10720300422601400a10040a0000084040d265070300c2d50f22002800d59401c414020004624a40c0032401d540030030142c01014065440020303403600c0c518165141c0b052080402203924203080c2e10005c7c00289030700c824080c0401006035540c6a0410350203d0042c88103421800d000d58070f1400704100410810310310070042a0103400c07071284c0c0e62111426036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 770110278 1250 770109028 770109031
    0x10506040b0307090e150708010503160b040b0d02130303030219021b06090102030c0d0203030a0c21180204050a0e0115080d0507060e011d060a02090105090d11060705061509 76
    0x58269103c2c0d01c04000d00c8080d13a02c02294484031300280ca903400b13250f00784064030040640701400003da0000042c0030a00c3d0034401089000061080c8100c09032900c0e0395450039002c0c44c80343c01c081440110b02010710700601e40455401500540403d00e5654580c4ad001d002500036160011601069078010781e840740c000110842164018400405e01c0f1440f43e081101507480743c219a81140010321a440c41802d041100144a082e59006543c0740d00e800031028003280c0c1d14007180f008020440300c03582c81141046070b26407141e8070034100200d1b481581d998550b0052143d90300083d0000d00d007104202c0d0300399480d80f00ca02c200106400a21220090840000d090708050080e00c1c031540000203d018214024030003002020f20404001c80c0311018401e01d40d086a40c000091a943c0700203c80b81030310384506002c9c2551280c0e005500b1820918403c00003044e50013424200b81c02403214035004418010710700703040c03c07000a000348000d5a854181c40e00d16110300056070306150007500300600302ca1741d107484051075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 770111528 1250 770110278 770110301
    0x60612022703010b0a0801141b120a020c0a060605040b03060c1204050c0a030305090102070f080d03020d091e0519021309020a0b0406090e060a06090510090e011701050604 75
    0x30080d4a0341c0c015806030288442520b585990f031101c51030055101c1c201140c0041244500001304010841d040c83c001010041c0b140c0f12044034241c0a8400118510039921049015280c15849541d8410640c00070311620149442078440d40180c6010014990405d000341c640a0703605120b140510424540e5030681603a004150351402d2020440325000d126a60780d00c24010812500440c4000c0701243c0301c007205420942c00110001800c8c2c100d940c040201c0e03401018401141c0e51410700d440d80342612203220009060030941c0000b12002209225040095855041421418195400414207181000c2e440c82181c1c03a004d108460741140c03400202a251054008d41102040c80c03080001c640285010202242d1102c4050030108a218054001d040500b503652a586c2d2000e0400131004141c1c90010085445545484002c0c04002d80c40851030f42290020b0742c2150044d8214003066034025030903003160b450810304500024240300d08101d030500c0c48140000030091601e402085c0001d640c14100c21 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 770112778 1250 770111528 770111557
    0x1d1603030c170d0501180e060402010906050a03020c0f03040315091109061306260606060d020a0909110a030605042f0c010f1506170f0703060b070606061202 69
    0x4500822402c5449a503003040005256292000c02410f26080701c1d820f07004000d81407210111050703100c4c40c03071052006805c3c02000a109601c0c069000070b116200f68015001040804201d040c0518000c7d0140c442c80301540d010755103007008040030941d40c0d801621058074500c0102c100000c1c03d1300b45208401c1c1054201e18980400c9041c2e1040c002907401c003801440d0406003507041a40088034174481c01010300240c01b034840c40741102c03003001080a10283c08018144d000141400800c2d0303104c07812207002088200c400b50300c4400115003659400d00380d80c003821040d4101280e0000c4c81a14200030821881c0780e88041040a0b1550140801c960201a1802c0912403800c0001030540003141440000d16070b003190b003071078100c04481690a4441405009050540f40c14001128901d690140800350150b031402144a5084210710072365084040d001c03e503008141400b2801240c03003608450054400e0032022541c601042c0703003002c000c140f180320303140014143c0b9203400a442e0140c000c8642952903001e1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 770114028 1250 770112778 770112797
    0x3020424080105160f141803060a0507080c1204150b0d0302030418020901020604020415080111070c06030504050a060c140304031d010f14031009060b030907080319211d160303 77
    0x3c04c0280c031f91040290001c0c10304860450383c01070703a0070802140700342441e980110305410300344030240140001401001c00d40d6014002000c036038200781d098585c040c1d0818100c2e440b9180100750700008088024001c1e802191800302201407580020081044071042041403602d28018100e200807402441c000034016005200031a015141c150400351a03091605408946141d035015494212030001d807142d5003c2601040c0c40c024071991028480040505050a2080340303865a03070991030f03008104000342601c1c2d44401d44110315200304501901c5d0055a0390580c0c0d07a08003410702400d1012100301a1748156a851980040c0354462200580d441c030a03511170400e8809042140304043d000200718010f144101800003c00880c64055100140803c4413101d0b41c1c0c1c00c2c01c90405091400542105442d07a00802c1a004034012401d032003004c283e0145414111142c146a00302d074100f049024695016040c40070b485d10307145500b0745800302908803d0407224600403101c1006005840703480050b001c10751010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 770115278 1250 770114028 770114057
    0x30903121b0f15020315010e0604050a0b070606230924010f02031c140907060e042d1506020712170d020c0a02090a09020a03020424080105160f 63
    0x14901034450b02c183e0700841d280141c504008101d810031160b000041c0d109841000d645c1d600884040302e0264182c2e02985014140030100300d000310340d0310407002e0288000450406021499020b0400f41c0404100c1d2481e820540c01109080200c40c01520302c9070340c021011a051001c80c09050300503c0c0c8407204180c60385070700c0d401520b200c10355071038010542c04100091045c0c00c0d40c0c400014600c03e429140003403014400e41c0441c03050708004190402542c400201070150580080c0b107880380c0c10081341c0106554100e842150107440d05c0c07450405540310180041008441780c3c3c1c0018044289030070f603062155a482c50100e0703903501d076071140700301e900f910405440108441a51901031152912542403500340781c045903404981c4109903001464000f0440c02e411072410107120351308910080d01c1400f111201e42c00003540b240c540d100091080b6034136100860707403a10f036460040c42c11034101091154a9949c480c420b000e0101265048184a01045a40440c80c040d02c21088032070b201e569103601241258 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 770116528 1250 770115278 770115293
    0x20307080c0307211503050a0302120a0206011401090803310302131d0601170c040905190c0f1215020a0906111005281118060d09030903121b 62
    0x1007008003840f6072038200717a07901c5404400742c50000b14444c00c01065156002d04000303003003406c40c0c0141050100d003040314110f00c0d40d002400f5815035111140c40c0c8825000000162803203200c1c1e5100d4410ba000102d040c20070715656415203000d04c40009030943e00b440c91070080110010180c00700a502c2540001800e50030a500e90102c1d842c5803200c0605400b40c6909200c161500d08268401300048003081c051a000c45002d0007611102c4509450600070030342030f0390307805031206401102c044015506608440901454150200c005e2012610000d826a01e4022920001d0804a02070310314903566014000402c1c514030880300c69480f150f54042510341030a408413060212049602800c3c4195044101c840c140d910855019500143d503900728011fa00282020f954000202000f5a921705500d4058800325002181e103040b40d05020040e05044200001d0311900030400c44a01161130517125004240d04940c2981c04d607402160750205554034090b0488900f5624840d40b100303005019100300000740e00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 770117778 1250 770116528 770116577
    0x80a1406150d0f050906070e090106050f1602031c0f031802060a02070e090c010e0910170321041101020a320a030305060901140f010507050c0315010f0b031b030903040b030a020307080c0307 83
    0x101a0041aa115075000a0300c1c100d10047128592040080c0c900e8200e082e0401101040809a41400d10242110320617501c09d0040d480c101a004160004404919034400d0240c0b20151209109074605130134115149942c44089982c1a4045120700f040900f1030300c1d2840340c2c0da10407103403200100c80c0107090090084a008030031200302180e2009100000e09a000d070200300004144210b80800503240034140200d078400b50f500c2540c155048080c07204081400c44000f808095881c03102d440b502d01c031460140b0309907401e0b443e01a0250154680c904101a4990001400b8a90881300103000717036210415541040c8a041c1703800c1e404003075002402c030154000c0740076041c264021020744e01148020004a4103021003806032040104010005000100a085826015009444440381145040c0303652242016a141c007900e082d4101000246d0030b954208115000340102c00d29036600ca0802040b0318010303410544110740847c1e588030029605a0307040083e64030030900e5960341c440c219400c1c2c55180d0100351 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 770119028 1250 770117778 770117797
    0x906170316050a050d12060b070203061627080601060f051e07200a0603022706040b1c0612080a12020405040c080a1406150d0f050906070e090106050f 66
    0x220b00f800f038082001440306644085140e00c6440060034000064012100740d034101c101e40749414051040540c800188069001e507442c041c4a03d001100c481c195242c2511421201d01c3d21004049130f160701c907012521900303d4001904980c040e0b42c039803106403460601405007a0009000b407128505001503c810b83e41c4442e4549601898607019480e407807a034131600c918408040301c022015000600b02402d0308402003010b17240842c2050640400042e402c140c8034070010f480301c907a00220758a56126800c4900404000461aa562022680781d20300414180c0b8100302c3c10341f0780f510015480c4588000d9101041e40500620700d01500150f080d6808242288540300c5c00303600344000308194640340710b01c0049480903101e50301e2520f00192a030082d24010b452808070000e0130b20601c9503a445e04950104070788031454215403640302e0313505048002e001441407848450708020900041080200c0c440e8054210f5645046030014054140038101800703100303500020354204011080f242e100c0015121540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 770120278 1250 770119028 770119033
    0x503031617070e130c0c020607021c14010c0c0206120a0608070909152304050313031a060901082503020a150801120b1303030902030105070207090617031605 69
    0x41241c00000c00010485058000c03e035584501041440d090340c042c0e248010800d8103200320700703804074000d003141c1c20104000d002e03c4010458008543e559020760307064214403980c00031001188e0500c4280d903408075440c00c00651030101e401403102c0c42030980b41800703900070b4003c030710303107203600e80d035900e03840700090149040079554180070980340d900307011850090616070000724419009040007080c00003100c2031600001c0c50440300c100c1c02c0418003003154840300a607070b8900c0341d9a2541000350443c030400c40700302d09003605440c0101c10010b84170303001e411480404a0b080844c1e81ca031000c0c45000442801010300951003031415503103a841c3c007000c0ca0b00c0d071000341c0740040942d592a4089282c0304070a41000890b04400710689820503407101d0301c01d004100c1485c5803600f01d40c03a900e072000b004002818030035820102110b030805160282d0072000c0c410f603026008005c28074000600a4840c0510b004401129051210020752075060714464000170702e41d034028500d0844d00d600404020912564100e4850 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 770121528 1250 770120278 770120297
    0xa020607080901181b23010e03120c1b040e0604020f01120e0309101707030209040615080a0507030902010212090109170619110d0b120307050102070210080405030316 73
    0x21544d60301c001a29610540201c1000985c41020340b110340d10316085400c20300d8100c3d965031404c0100000781410041e0a0902c1203d43d5184000300307007805540f0303112256510000650070b00c40308000074284a1459030682c4000c10200c41c1c0d00700004d42d054150301810f141d011401240251800c14444151020141454040c3c58001c118401c1600c105a45510303450b0804684e4075034505144e41a400c007022145004c1c059900e05542d084022500036088004150f400704142d00c194541360301c400003500005110712000010804000d1a08108584003910a81002d000c50510f038000d000c1d524107154140c02400c40c5100b042400c40498104d500110f041210250000410740843d4800d0043c50711054044c080c0c40c0b030400c030460b040044a140c04105145480806401384550105a4100e19160f00020401c03030038100000301080d8820f0031414460100050600c10450154001c0490500c240d4850b818804400800d5524000450740540250400c20020f258040d24030880da84109407401c000c4540b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 770122778 1250 770121528 770121551
    0xf040210020c1005120f0702100b0607060e010b01120501080d051608070c14060406050d0b030a0506071d0301090b060907020a0507030c032105160203030d020a05030117030a020607080901 82
    0x102c3e02490018011950000b2040107500002c0c59140d0300a10640318a0304a0034200402580c1d040307a00c0b5048480c683d03c0c2c0408205030f840b41c0c103c80e80c1c660409002d10540da400d02005000340b5a8180d5540442d00a0380c40364809017180c01203d041315403003c05444d0146501030151440e92000c50080800e841d00e403290000140e08402070b1001c203003d0a001a001410600c14a005091010700c0714480c100c1884100082907000c0304840384000c00500c003080700302400d8007080c0f030032601e20002006805040104138500b40d0150809111101240f43c44559280311401c2c0740c01c07200d20b01782c0600f42c8001440026400c0c10b105000503000740c45841210607c0e2180c0d1280e0381440301a0304100c6900340c0359802002400321040001c03150002c101011007942c542010301a01c00e00c50440b02d0034a02e200e001228042d99807c0c81540c815041c00c84055558000680008003103500901460440b8a40c110540300d0384840042074840c007003074980052129444065042e20324583c000c0c1291990740d200e2880515 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 770124028 1250 770122778 770122789
    0xc0102071a0405120c07050411070f03080702010c05040f0510090e13140f06011802040306020426061909150c0e1c03080a0906060503060103080913050f040210020c 72
    0x4003000c0074142000303141800d241607400c10383c04418241c4440d009000c10780c440800441e001c411206c00701da00144840c180315030040c05004240d00505031000400300300c018141c12411030b6200b8181070b4000c1001d03e0f0001c0c4c054840b40600d002e80b41d042101b0b090240124201180c0018140c511070804103c4a075a90f00c140000a40c12103c3c81a1407100c0806c10042050512080e03101410080207407541c401248a516900c481c14460f05401c440030040481e220602581154080c0d030300324031709543e81d6031550381e130100d940a48503071000c9480100c2c102000c1c541010075124051080c00940300c21261403c030103600504800c220582d0a84c102c083c4074006c2003e103116212503807005032215411441040c0800840140803111070012804410030400000c0d07100307007865405010007800141c807880e2400d04100816081d009031f909485540300210511131034001034003800078125100144000c01e01c68200035101c1c20ba038030801568118000c02c0052801c000b0f41440c20407a8070441c2d0440c2c00d484000740 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 770125278 1250 770124028 770124053
    0x70b0901050427050f22060f0e060f0c0301031527030309020a0806090d03020c0a0c0602060f1005011d040f0606050c060108010c27030812220201090603020c010207 72
    0x207143c040102601c4001440c090f20b54841c01e0b07900d46620b1842c06404201390202518440c1041114641d00001041402d900120003408110802c000407011403c001b562840c0c1580c101600c0c0e84150000f5110941c0007003140c2c141ca6100b0000354600c1c82e03402028001c1c00d1043c200c0c00e0740d2071000e0340140c0d00306400034044400714000e5401240024590061104140d0b003a004106e050300080c08000c400000000e10700040c0030075103001666203c00c2106907050800407940200210020a00050b2490b40013030840e01446c0e038458681215120003502e08640350040c031403180400c4541c0c105185009070040c1d800b45040006e000462180c07500c2000c10300310349117030b04500c011800110320845442000c10081e80941b0401000300300c0c00c0782d42000500940d504600c40400d0740180201c203195440000311080085600007002c9403203c1040b0002c46070b490b01200d003459490301d80c83c5401003071700e200c00e0109140343d0181c490f0058035003040c030b0407406135001c15011200c80d074023005058001440f42c520714 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 770126528 1250 770125278 770125319
    0x915040f0605010806040911010c020402040305030408010615050405010e091806091c02010204080703062007120809060f0115091e1409151c0b0406050a0518070b09010504 75
    0x148090400b00007406464018101034001d41c60b00007180e00060401e64444075100b024200449850001d20000300030788210380004049000104000403c3c610540007031043d102011b02d091540c0f078a020046601340100e106183c00a280002c0c1c00d01207041100180341c1042c1006401600c2d540e51083d05858403c00383e0301960079600041d089540f80320341440c02138403205c80384025481c0510380b02c0203907541d111a00002c0d08450f5103400c803a284c02c00085111f0701700c040d0811325680310b0f10181402d0f0764900c50517412402103030383c9900086076080041201803040240ca942079030700d64206100b0541001000205806010300700c1004200c040c2100e0103408181c08079101c10b60047d0400e041528554850800540542c01c04001d0201c0120184989003140d0410b5522141c2070b0101402440c2195150a000e8190181401808280207264002510540b2000001d00c41a19464400c40980e02204044c0240c0e8204030024848400402d00516802c281454110b0619440b0f20403555007100c0031504 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 770127778 1250 770126528 770126531
    0xf04090f03080f091b06032206090b0a0b01020a03111e030408011508060412030f0c05071101050c0c0d1b060207090b010e0a060f090e0c07020418110915040f 69
    0x1000f64088040300b103607070311003801005061040e000e4801c0e1034a060904403c144552070110005c0c4001e034400104141d403108020f919800d1220300c2c02c01e04010b143c42e0fa41541c00d414648002410704510b80540402e880c010390042000083c107031811500001da00300c00d101c15000b40360042d1140006484251340024946018503a00e500d400704041c02c403204041d05c00b0040d007021204220303010000c503050307034426009200a4a55058444203c004000c907a8220707580740d280c003000401d07503070b880340c0a416012312400d1030b244805034200042d0703032901480d241c3c65066031180c6511201418000400c8030b2586c8141c0824000003034528031107001c2c14650304170382e0059106007402c1120443c80d0040b180b2204081c01c08502000782da501140042c5c005000703440c14082000c104400c10341c40759800c0801031242084011441c204081c400130300307500c0310324180d105e281000114242c0e40b406070414107842d64015400c0390025241801d01c0100103004000d0000400c0748080140d6644690003020031508ac240e00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 770129028 1250 770127778 770127781
    0x32010e1c02060a09180c02070312110715020f162106020c03120121031d030d02010b040b04180204050402010c050a0602030402040e061b030a09170a081803090f04090f0308 75
    0x41280214604170307841d07041402c1060703003c1300c04d402061100035a41c010007003440300c44000000790b6001131400c1032000d140c424140001802142c101004030350700b038940d082d00c0e8800e60b0340c4401981c0f044401e08020650660340c10403c07040c40019010b02080074080b40b9691071602c1d68458200302d8002c1c00304410660000104d68052001030300c002c50142c04030b11031207103c10300182d41c0003500c0c52192000a0602446c0c503080c540407085a01d0f504c2103403c0041c1100c6041201c458000d02038541c104c40d4034019400c0c44010507203417038030340140d84003c00c400c1800d90010007103408000140c00094001c3c0d05000c0309a18072008188140180306c07549001381c1001d42d980c00e09205010803605a11034541e00358010f102808440c04802400144601c01350383c0c002c0d1241c8803a0505070040619000040c500101510002004100c02003d80700f0400d45440e03221603544d030f0500340580815544040e0600341c20800a405183c58000c11005908202800c00205502c29a5a4000c0703041e14580a90203e0b00200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 770130278 1250 770129028 770129039
    0x180f020403050c040b24030a0e1605010f0504140d11100c110d080307081b120103110303090a031e02041109030d141b030705030432010e1c02060a09 65
    0x1e45504031000e0306c01c0714842c001c08040c50041c8005d4006080c48060000200e115400d40f030f04034880a520141c181c50140c880610f0380c1d00c02244034460035001c10800e00c0c8202d0803e00545c29030713085440c2e4041c41c003030349001e0004105090001513003c81c2d882010082d001d403543ca0720b240d04588100e6903180c0b104200c1c09428610011003270300c02c4492040c05a5480e40001a01c1e0310306990f00400281001011521101203010880300c004070b640c1c050040100300d07108074025010030907048078003442148030410b80c214141a00c9100e6050307100c2d04111203840410000340b00784483c4200040714004400340d002c85a0014080e100c01010006030100f000c1111030161900307100081d1402c4803803d1081c142c100c1010842018041d0048a80c008944107001e690f9030384062085480c2c15a014054030fa031140c40d100301644150701c03c222000c8400c012001d02d0450004c4101c0400405c405071900348103071042c0c804001c09621101c40c0d145092040682110041c1c591101a01b07940506449500651307080c00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 770131528 1250 770130278 770130281
    0x6090612031b11040e07150c0c091814030c19060b01030b150a14030c040f06020303060d0b07120e030d0c1b020f06070b0a0c090902030f01180f020403050c04 69
    0x1c0036548502d4030800242c0020780340e4241c4060108056034003140410f10104400d091401c2ca5200c40c91101c022180d00702e00d0b90344059448041403107030502501e641c0c0c0303814998080300c800281110358690100d111002148541c000011400c8111045a281ca105090814107140301150352651700c481c191115410091140030752111408280b07800c001007181c6000265504850b04020903235210000b680e01c02440c0f050b0141c504500394042495a6410025042190740d4400e00c100621181c4554001c21402d2020040301e000b480b0060003a805c80006480b50400310202900c00420303c05801c0c0080d07481c1030107020701206103140401464903908a42644000d681c15011008208840700001c0d1030b58825102c0144074054050302e8002c0c801d00440c000c00d0b0188607440f40a0102d12582d810408110f400342c1040c20b0240895441481242e03441003258203a0000380c0d0094105460000180b29000b425076000700c2c8401034440100b00e4049095058049074080c0e0001d0b1143d03080302d0005200350602c0e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 770132778 1250 770131528 770131547
    0xf140406140907050c0a050111090301060506031312030b0d050607021c0c0f02150309011514130b1c061a0d120f090f06031d210903010609061203 64
    0x401d806039500d41c140400280503100082c01241031000104214152690802c070681c000c0e68450020844c03000543c082c02450341150030098030035820000b010404c0e0030142c040e45d0044006100c503007000d03903541c2c0e40c0d41005440c1c2d81c01241050f030f0b036541c50011556070038403078440c40e40100090040d44c100860004c0c100110001e0744000c0e10325403214060700991102c13040d1091500700198240300700d224400201e5400031500e454090850100130b0000d03550042d8003d40d24040c0440d050040150f0351958000c51051054220342c0c04000800c0020210242d42c015520319107000b041600545c403003103210300510034140c805031030301556000d01e16628603c0c0c0d0728141010350201c0d10b086440a403a6500c1c21a00c51102502c000c000320012214001400340c02e180c40545070420f003203250f00d034950358020028059540c4186a611b040ba60f00000f500000c1001c0800c00740d480340e003140942c2e45800183c0103070301c00d81c1e02d11340544d03036084002000d104c90300c260005054550500103402815080041c400b100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 770134028 1250 770132778 770132789
    0x42108040e04110a060f11070504050c0c010501051e09071103030a0b0a081903180b121509090d0c0f0b040c051302122403120406031112010306020c070f140406 70
    0x201303041c0c00d00609400802110300307116076180520100071110741e141c1c10a0340982c81a90480e042c0b0062100030314401010700724640c1e100d4000c0090740e036543c0400680c10100d40c4840440c50022070000c000381488426145d1003c41824110b2068154030750951940d4412a182c20110366105160709881c80e0545001006142007401001c45448031117403980c404400480c0102030142c00c2154901e090740e4000090000c1100c0600c1c2620b460040c0c401a10604d0220f80e2095051175140112407280b8140c003820b80500306103c000c007891800207005a83d44003000e0402c2d90203101000446001820b020545031041c0e104d0300324281e000d807414090200c80c40700240c4076607000d40148851688184402c0c4141e40c0680702c011125034821035078048581100072000195014050200c40042c3c3c0900b103401081151801c1c3d40401c00c003074810385052040c1c001c001c0b00b1000000303014010004240d07160041e110801c8618140c03000540c2e900c90014804050394043e400543c1d010203d00c58901d40b61141500809 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 770135278 1250 770134028 770134039
    0x1c030b0411211e040602070b180a0b09030f0f0a0f110a020d140105101412150c09090403030e01050f01060f1809020c01020903071505042108040e0411 66
    0x10341076011510a006511030a81c1c400841c41d000414594908088100c08103140e10b0b020740f1410300f810803030003a43c090751040e510300c80c03002c2c00324541d10710f103000c0d004104800c0310160500913030030354440c444264044c0084c94184010300240c040c800b00d8270024092042910025540d5041c03221014080c0f0a100603140b0520550203d1910340b0080410720012003941150301c3c000c2c00c1c07900c1c5092100d140000c104c41c2555841e10041098100b6002000303000d41c0e80142d40300c1c001000c241304211000b0b085003c0c0000c3c6400500e800184081511202c680100703501c3e1070705052007541004145800400c660543c0000d458000d0001c0c1d5000038412160896010241c801056042c14400361601200510400030003103984602117507443ca810138403000d88120f03042959101507818515000c0d4020004580c0300b1b001c0e4000000d000c00600200c00001c8906071242801c1905d44021b0300e8420826105141c560042c0d6a02040080d01020060014102042c940080c1d4100781c240704408000141c80e050142 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 770136528 1250 770135278 770135287
    0x30f15010506030f0c0d1119020111130b03061f0804121d0d14010e010905060105060a0206060108190908030a140402150a110f0705011413171c030b0411 67
    0x10713030a4040350301420305502240d03641d58070102c040c0201416803415090200100d18200100c2c1d085c1e80710024200c46500034050b07125035009440c110310803510342e181203400b040300401550303942c80065030307108900820400c0c182e03850b145545240c0490008810010380481f00304800c000c04410310942c0c802c0e15251000b520712041c9146400030746035404480c420100f0300599800c02a50903a01000c4002c480002d02006044c0c18195018016045084640b402050004512410a40183c036600040d80e8000c05050312010f0055800f440302608014400540c0c072800c042003000d81c0525103415100700307010f0b5901c1c07600c0d1803030f0307403c503520b0794421812400020180000350b9150070318418829043c41c003295688003888800d4621030034800701a02940a42c0034600c2034100085468822107000380c8680d4281c00c007202d1000010f02c208040d006540403040c1c41803040c400c03c40c03440346001000c01300300e0304609840040704824000189441001a481e03000018042c181402109100b41440c00c0b45400e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 770137778 1250 770136528 770136541
    0x6040308010e01050f06161a01080c010e060a110f06071206090915050a0608150105010807051204171c0e0c03070303120506031507080406060501090e0a09030e030f1501050603 77
    0x15800c80c40110746c45010040b60020408034016000c220280d80440d66030592904c00407000c3c0c5031071007441542454020b00803502510350003110300100d0380c0f400070720300e5180c00c05000d0140c83d07a010f8000340040c03502c602920141c03190000c000e0700d80683c810340c8a41c0460b134098902c220940b03e00d500080402401c0840f400000b9a0415282000000950000c15035a4941c02c0c054000d00080e4081000b07803060140d80b40f612a00c0a0200341030318400e903102040b030703905c00c1d07400e4800c1e12801c0b5440b0064801000001d002c01c0050031010a12202c3d40c0704e95103001c08003d0806442c0080c101004160340d40d544120b91704402c1000b4041804209070058641240b864601811182d80c00e28400031107619078001400660302030002403e00034407114a10203904200c0310003061181c0031101201e0321071030b01101060130743c054100c02c01203030b40e000382c2e500c0c85a90b444224005032503405411014042162080d44540d60305000c201b900e494800010701200350402000c2c0260700042e03008600510081050160 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 770139028 1250 770137778 770137789
    0x60e0139050c10051503160302030606010e06030f06040207141509120a03200a09030c090921030902040e0a050106140a03021002100c030617010606080711011503030206040308010e0105 81
    0x50000310b00400a07090b030785c2064000180d81203001e02541801040e0400b29442e0a030851403090301d00940480340150303589001502c02c0500c40060b03c0e4482011300005404500207030000c0c0d48107401610140c00c008007aa0b0f02c800403c80c402900030640c200400082c242c500c41180c0d0390303026200800070b000ca1111103011520701d2085104460406440383c4010700119140700b6030804030103012070059034460750840c5c01071150701e16000c02c460404080200140911150049500ba41c2e00110f140d03811106003942c005898900e10710780c1c006c1c5a100d00c04580543c2d143c2c41411024040d04c030107010039170702524081382143d419400c030f031100c842d4451162002d600c41c3c8001d02d00381c990540c0c222038102c0c58124140d1416000c0c04018611905003290150045c0d40364000c0c1044800e40c1c0690302c0401d0883c4c10b56800c0c0c4401d0700945c0002030b220300000f940c0c107108805001503611024000650301105040c1103082c40e64507003041c0c0240c2d121105000030143d00000752401072003000071200302541040002030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 770140278 1250 770139028 770139043
    0x518060f0409021504030c0e010609300b04050106060e0613060c08041a090f0d02220e03040b09120f0c0607060222090506040216060e0139050c 63
    0x24000c1d03554a45038400c640b10104032110400e1311030301494075070703a480c588441210f09500440c1c00031041e00000181d03003801034030141c055400750b4406d44c00d4a0721f80158451105142c140001c400302c0d21148900c0450411001180124003a40c004141982480405000d2288040210303004100c1000038846903c0d503a11b144041e207a2500d044410f0b00518207040c1018040d9400180450460840c00700c40510154010210b4080644041c155900b00800700550551010406504a5420810b03050b4400b5501c210040e200584580003425400748604e01c0e180d0b401075005200041000a5a1f00c0e2b02d14110107003c00b010040d80007007242c05a140f804585610040c64401d0107543d010a0f01d808110050b01a2141c00070106a60304d0541c45071180724440201d0352142800b804c4c80d09010618500b000d00071511040104c0e00808049a246d5640f070000b0810024074520a560341d0414007015207130907581540383c192045024038021500782c0c640308402101c6105205126003040f449848943c0443c050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 770141528 1250 770140278 770140309
    0x21070f090803040e06010311160210092715060804021e03100908190e0111030901391a0a1806020a020c0613060e04060303090302130209130204051806 66
    0x1306040d203032200142c0142090059030042c15002240308e03003079000003a021700b91040c02158a103803a5070030303c00140c03a421141c0c020130b2101803401c40700365550001c11a0001c4441c50702d24000680700101004083d011645802c800000740c0c01a003031100354a8441c2d16660a808031031640403038401100d0020750303511110300319540380503281e4681c0302c1405800020703117110b44003078074602088098180004115003d901c0d1030302e0116540314007064016900105507a100d04040c0c407104400030140d0040803840303229200c402c2446504a02c1b84540800f0a899080c040d4421680c92010300f44450070300c0f0202200034504100e080c540103d83c05a0f00046203105403681e080040142d5400303034500c040381804591014543c00450001351203040d008c03001d08803400c454080d0340c3c0520581c41c01081205485035444040c0c0084c14484003030002d49003070086c2c2d13840400340060040c80c200840000c43c1c600c109034222841c80e90790101e4104064240024510059500061621036a25251000030b010000e0070416 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 770142778 1250 770141528 770141549
    0xc081006080102161b03060f050a0e0d02120c07090c02030924090d1e140c0307030c0e0907080118120810170307150e1219080c21070f09080304 63
    0x120170840c1d203c1c4071094090754204005001480b451003140001d08020355401038100d1911032036000b91403001c20b80c03000c00c041e640c1c05464503100a400d4540740f50000e0003010894001e03100c002444036030314420090303400b5458001d5a21038402208000d01901c0c1d60351401c520801d0703007101c2c1d01d012074040c04441103503804683c010040c40031410300003145070040c0000301203200d101920009118400074024214510309041b581c92102d1402410f40f65007103407000902c2a81c1000c418001041092605039000303a24404440b02d05a6412303405095980300f1181c8201c01c002100001c0c14010003020412051101d4240010b190900d18688d101d80c00040c0b0518003c850a25960940b084050040700d04907600403256614010318442880010001107440d01c00a11410340143c16540c5014141d503100343c00c0100b0054030b141c2103202510034a10091100082d10070410052490a0700d801c0101c5c007102001c4909501c5142c54540a0400c072403540910082c00510034040005810000c111426585100b02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 770143884 1106 770142778 770142803
    0x1a09060d0c090207050a0507120614070c0f02010915080108071d07050702030115090906060803130302010c05011413290601030c0c0c08100608010216 66
    0x10a1072864240411400c07110358040c0400d1070140d01500e070522442c1d5203880c02c101c0d15400c100d081840010b80f90302840706501c10000e5a03080c2801089080c2018040030b011800410801841c40408484001c11a48607250700801813605800c520742881060b08003416404090041280901c200040002c0c0b100140100c5030710825480039040c42501e80c1402111580d100e2001a0380541d00d0b11100c0d01041044110b04005140d024000985c4404510b0900240d400c0b9a10a40084d8000d1091201311203003091010101e0b54242000000b80d03082e45041070140100c1e4508402c031400c04400c0288401c501d40115078154450b070300a004404002c0d600050a030003004043c425600d52100042a6500a600c140044042d5081080307885590b43c2d910114480640c0000325070f40c010700c0460300106424041d15020f080400c0082d03050202d5080d584240310004a0050700a585085 = true := by decide +kernel

theorem cover : BRFrame.Cov 769964028 770143884 := by
  have h0 := BRFrame.cov_init 769964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 769964028 ≤ n) (h2 : n < 770143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
