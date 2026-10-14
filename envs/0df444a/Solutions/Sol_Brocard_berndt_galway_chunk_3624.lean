-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3624
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:12:03.109869+00:00
-- url     : https://prove2.me/submissions/d8b817f6-a693-4b8f-9aa6-efecdf290097

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 651618705 ≤ n < 651798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 651619955 1250 651618705 651618757
    0x307021905030c0a12060c180b070506070f023316020c04020c07050d08072406210803151002010f2f0708070b1608150105041406 57
    0xc034015600220140d41c440040f2404021480090340243c040001048801c400042c2c0203a000b04030050302c0781094811007a00f400c41140d0111598486600b07064000740003810441c0c14002260701c2000c900700654405100320000755540380044a01d403104042d02c1340115140c0005030716002c8809042c040d000c89140c5651100081040b040048026100d00324186203070380380a0081c4c550318110b20b001030140520b03107010800c0761030302c51206640d02c00c0700304050790102c0c00010281040800c20a040d8227001c0d6454002403c0302d0090744030808003240c00c1c030031845000000d540c079071000350000b03005030712511071803201c401403064140c042c0d134000c1e14503625000c401e406400c20544254250410401300150311840000040c460a080300101e0301c8400300c00207100410084d00e030490003008201d09000700344d981e200034907600b510801d101002d540041d41c100b6500604c0c050740281c0148d040413284000c0c8002900034050381c054248800c1c0c00300b00100c91134560710241c40380c400d038281500d000d0880380c9403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 651621205 1250 651619955 651619999
    0x7051e0a0e1f02032a120306010908030708030f1e0103050c0301142214012307170a0e0c0a0306020d0b010906050922051f1403030904050405030702 65
    0x18601400700d9400740081560300c0403a03030082c004a500a10f1400740c91001141081450003204038030b20040b6000800c0010080245600c81c0300028406581c90074600005071075188164000180c69004016040004001c0010380c3d8001c0d2203c05941d4050300ca078500103848204286030b14200303003240c000001c10300c80000340c40b10160a056000f0000d0840308445c40710002400c07120314a281c4140e46120902c5110501030400082c0039140e0b9880c1041c4481c0100e080d01c1c0101c00e5a01d000c801c1d940a403441c0c1d003a05a94a81182076030134091100e4042003079003840940d00604103102560380b00740329462008107101551841c980240401c1d107054591800d0310082d00020700c089151890308140100650044056005640141d16031505002000040001c4d0840700c010387d4500c1c0708861a0b40062551301e025841c003449501c19000c0300400301c08818120741504d5070105820040380c03e00c00e10140c078040121140418180e0b07011a09907240e06000c2d00e036125100c4000d401c190706889528248203519 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 651622455 1250 651621205 651621227
    0x819060e16080c12030a0e0906040b09090a03140901080f06012007060f110c041e0903080a05060901290d0603120201050601051e1b060c03040b060d031e0201061a070501061d07051e0a 80
    0x42c40381ca0f04070343400840e148041d000c0c0c0043d01c1d0203d80540c0110340d450b8410001b055018105140007003110a00f058264040c90032640415501e0780400701c207000e00ca40090364100300d8070b041d00d485840241006a541da54a4003480024052a43c8080e88a00d2070022130001c0c1582181c4001804202c000b4a401080a03d00b00c42000300d492818000c02c22614105407424102c40d25811080c66242d05d18080310880c8a500181c02070314841046403003583c0b08180900001540500118040511490300103801e55000410b00c504000c410040c20750000500d071a460003000c1c40780d241076101d140e510187d000f040541400c41c07040b031294000300080040300308021031103a4802c41151139991504801c1c030801411011005000c54800307040018803140000c0303d60001d44480c8008603c41e95900e0401c3d108024180d4400b0b252a0001202d10500c1070034000c8100a1039844005030012440c2c480480c41e11401415007800c000c03000403010400321188010b0a519030086080c030790340d4990044094400c0401c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 651623705 1250 651622455 651622457
    0x81b16080a1b0518100509040f020112052415030a150602010b010f050a180602010614010c080703031806051905010819060e16080c12030a0e0906040b09090a03 70
    0x15002082c403900c4841100030844201500352042c000e484c0b50781003614180201002881080c40900003681e549110200c0d021b035000700c446403490a4a07000041a0206201948070b10604200030320200800c3c0358480815a8848141d03407a4900550740003403032500603c000c01031070980101c20302c0050070307982d40000c02d40e420020070075818580c3c5041c240d003603406000080380420b100c500780c48003843c083c80041c03860b00203e242c81a2003200141441889c001290041c3e00182e65840c0103203c0d8241c0e90301d4080304240c09003040c0000c03003c0c542d030b08000792040e00d1000b020585c45401c9008603081071030030301000c10f520050600c8039140c10b40705081200d0400b0a0704d17103102e040100001e00440c0201d00c00c2c042c500d0004480b120403042d511288013808a5441c4000c552083c0403030f0b2050764105181100240141c1d1001e09040c400f4801000b8082c1108a641c6c08a40c108104548440ea00400988034100c1c0a40d03000f03409949080000d4014514800d10a030040300305030400415040c04241071610360f01c0303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 651624955 1250 651623705 651623723
    0x1050d0e0106051c030203030106180320040c090b031306110a1706090408160c05041104091a10140708120601120b06071707020d120807020109081b16080a 68
    0x800d280701c131141c0288100250158104100600a1600c2413a1800303c14110700c140c0f203111640e070b0b80c840d03101c491018202034144140703102c209020324190082000c0b8800b1480c02c4082c10b400c214101c8140c3c0300181901608840041801d41040119002207903454a0090481c0d114642e95401800107091640c0d40054072100314001486894003941c124080c0743c11060250030500c14201003c601708003044140c5090007120b0001070356668a010b02130002d640e07940d149484070302d0404010700741c4031109504541ca01124148949588802078034500346507951400d1469a0045034542807076118030b00001d00456400140e14010405030b8405d14020002030b618840255200c0d00c81c40b04407100103030100e9102404003c0b00300412942c2f944440d1020000700710b10b180c038156600003509a2440901240c3e11a41e1580d21441290050000d962058050000340000c0b0895a0341c22003c1c80703408102034800c25030410144008404008020403c24465017021005403500107442d9591001c1d41c0840b84400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 651626205 1250 651624955 651624979
    0xb0c15011508010e1b0702030f01020406051308011815060515040312020109080409091a0103060b180709030609240e010f020c0703080906070512030403080a09020a060e01050d0e010605 81
    0x11304944840c0c0300d141c156181d41001701071041c01030600d501880046c0c3e8144207107118420700c00802e00c010710080030b19450b415500c1c07081110b00c034584040c560010443e81d00d020540c0c00000c0b1804160032440c0d03400a9049110b40300003a1040c01450941c00840d081003075803101540c0349217028010000c1c1d80c054198084c2e041204c1100b2820707240b103500b0043c0490810300c81048000440e4000240700e51140400070b41002040c0c060054a0400740c0c825594140c442e5052113041c10004042d90328184080380e080800d240c09640608000c00510000345102e0f80c0301d00742002e0000300707100704140b400151600d02000564412007800780c40900007210155182442044010300140708030b50345445407002400081d45140c4a01c0fa40e0740100351230340c1c1c12800070820100020001c0c0b1025155404405990b40c81c0e081504000389100001000b440b542444c0098420169840b8a86501110381919010340c091a04000481d03450007043c00039014a41016a000300307144040d0070210503101c01740c5012407091 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 651627455 1250 651626205 651626219
    0x30305060904050d0f0e1504030b06030604110f010522031b030b010e07020109050a0819110a2a032003060705030c03070201060510170604050108070b0c1501150801 72
    0x5006460040441c4e001a044070585800b9041d103914118143c140110b441407400007160011b03e00c001c6038110040d00003014800c120183c82c906400140c01d80003030000d440c059581e5100d0036007000c11070340706a02d124100541603100d041102c8940c2a0204080c06410084240013401c000e076000455683c2d0803c07042c0343e09888030203c048100c80d00020180c0107031b40707003040084c10100060075a0b421075481c2c40c08440855010003070a1040c51044500c02e61b40e1b40710300c44680c050f4079050040010001c141045a014035400104400070325085245440c3c69410600782c5004815a94000f42070059254130000c20700100980c2100340030110b80803441c2c8594840e007010f0300d441c03048804901150040c030109841000e09005103500c01c0041c0000038080d0b07113039000208500c0f044541e44c0001030034465211100c42384103c1054002d04160790034403082d41007400c0303541c48107a14005d48202c0d503004650311a07208010002c105d60307084403280c408000d503100c0811100c41d656401115001c900014000984d070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 651628705 1250 651627455 651627469
    0x180504151e0504020d08120405070902030c09042d020d0e0109230f060a1d0703030e04091b03050604121806050307031d030a0e040915050c041701020703030506 70
    0x44544801d00740340c48250000014000c02d8050000d076000000268650001801c4e200240400d490f944819201c0b49005d25005e4035180e0b903500080710740e50041c418060020787c03003002c0d1748035214119008158403400102102c402c11f207042d091600384282004131040007400760300030310080d80c0c201020310001c0c3c100e40a041c02d981d80448002d0031080d5036400150381004450311030200da0710b51020754454041409103285071036025036480c11a5a40d82036140156401e000803400d4040c000e802600002c0d02d940c5001d020500400e800c03600a40d1109403880401c003812040301121400441d8504aa82d200c0c28069664281103404454098400303c41440e000d0003080103414980940035411542030402c0d0040312190000744c04c0038245511121a0070004d118224a48043c550070030003540c4840718814001c00006a540301c1a024518100088000c80c000d4038005808050803000031031140c980c03840b005040c0c80f6943c07240c0311000d83e141d008141c1b04070640040c014a80255000e10207078403050200244 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 651629955 1250 651628705 651628721
    0x1902070302130b0a18050f011502100203280e0c06041406071e12080106030e25030506040c0317090d030c0203031e070615060206071818050415 63
    0x4080005200000c0303605580c0c001400c03e1802925a0561035581c07103031903000c40c0c40300000b01503040d280c200308854803600780710342801009007000c07614003d529400080d44a00038000140300781a0000f0000c0c10f0403885503d41c6c8507408804641140b207190307131600c000c01171060f0003a03662280a2030160701e41034641041034605480c00c4d5001e40501311070000400010340d00c03c0c602104d0820079008510203074814003622a101a000b29045c81a420046c1001800b840050700898145490610002d05469000902c0c0411440e40d800041402c1c082070451510000c50387d000030403c1c41000208410062091998001c40c0d01c26242980b00480103550b400040c02030090320b50308501c10101100c082881003d04529050000e020349240002414040040355090312480d40c541c04c0019403401044058402c2041880c41134500c030309041e080c0240251128800f62903141003005103044050102c0c400348a80001340340ca01c2148004605111142000c2c03d01254141e41741403042c900e20000c40114011000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 651631205 1250 651629955 651629959
    0x5030f0907063221060108070e010e150c250308030a0902010e06180f0307080a02060a0314070c061d120c011b020a0203060106030b01080105040911151902070302 71
    0x50207014141036542c1c0d8060700800c1a00e240381c00204840e40180c81c00140000150520880f0308154070300130803442030801a040c00d0400019008020040d944080d035503900c400d0918050140881c40800140880070138030824840100015101c01c1c0841d0015100744003400921078405a000d40c0542d6208002030f0b488094100c900070000555010b50543c05014a540705040c10640548800003149003501300503c0c0d08969101c0f51032220052401846045102500b10014101c2e6802c0480c141c1d200c1c584058028020b12011070a8419140a500122000148030881003582d00c2d01d00d41c0145110301d01c000a595551404100800409540d03d0103c00111590020001e1448108907842198014045151103551b41d081c070342c1134049650340e8403800761000d038014584c1c400e03180109400c044041e0b002e075041c9460101984076503600082d07040e04448040b540040c042400b0704090b1030800e0b108040d03590044c0c00150464441c5400d0015000001d101d030281d140054180d4030590f907031241400069 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 651632455 1250 651631205 651631217
    0x1204020a080f102a03060609170a020409050f01092004050708010e0901150b040509130b2202040c020a05011505060702040f0603021e150307360605030f090706 70
    0x9a2034a10768000e84c40310783c1c060401c000c1e0700c0142c2c42c281012181c0c03030b0082c600003a2601010000c0715400202c02001e450f151070070342d00f00c11403020990780e038240024009004588691040082c0b1406004000c00e00703403c81c00030b2041e082c1901d00b002071300c40c1501e060015001d40d100100340328140b900c900ca1003084540c072414030321390802000381c48190303009060707441c1e030346d20340c80c5d000c06003603011021400400da036090290700c0c3c038100010030243e088002d14029000c080b64662001240035128441c0c0c21038000c07141e68406000a0b10017940c50b49401380069041420040c1e90781c601c1c0e500289440b14203000d11300811102c50707100b0421407199078a1044c1a4004400c0c070241d400361406500100c545821540001042941c0e640032985043c2030050b900341151850302800400d003400e409000c1e14a20b8030061078603601d0079440151240d01c200711180501c0400f090010f201590b0005004000301240034141c010700e0792030760000e00640c4106e500400c017900500c0800c2035410000f039000144c1e4100c2c0c50301c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 651633705 1250 651632455 651632473
    0x602070617042303040609210f030c03030204150c051209032e06080f070b04050108070302130308040b0c011805030307081e180d08060901050402070c0306021204020a080f 75
    0x840152040c10510402c03420f240180003040401c00c10045c402807605498010005207440c22100a0300004120b100c00c40080020740c00015060060f410b01c0d0030f0745401c1c110013842080c02d04800070300954014070424080310308400300071504030281d5180701348114100c030300300c6059400818060007103055282c1c0580c0200c0003c5a140510801203070080cad0140b0300e021204502844280c11748065500c0b0181c1500030700981003210000303100b0340010781006c2c03000c0c070b1400f85010300003070521b0b900402c100300b0142cac0450302289840d01914554015900b1568040e1142c0c0c54200e0301d40c3c1a405840d07815500d6180416040788a40d5412403440e078150010040c40c19581d85c1c00701615080340007402c645900620503414a1041d000c8038219018070303003640188005201c03904401c0d142c001144403500c288000c002c00c1105943d60f9102e17403410740d8025200540c1b241903d103460540301c8626000240b0355400400d080303227100e684c81d0345584a40c1c001c644801d4016038800c150703a150000440b0010241d0403103514 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 651634955 1250 651633705 651633713
    0x90c03050402210706050f19090f0602030408031b01090203010f0222050a05041508060c271012060308070b060f060c0a0b07111614040c1d030c1306060207061704 71
    0x50884070001c0d03805c1f01c0c502002d4080d001c021442c5c0040c1c2c6804144501c1c0203004a1000b0709200020741224002140303844d060a0380306661b03018150202060071520024200d562401703400010b02e0540c007400030311950401088141c042d40281261003030180036000d840d500801154495811144042c00d200c04030350a220600c800303004200f4603445420050140060b400504006d038a01c1224031410180c0c9034042c000400403065198a078003207440c0071100f01402d255407041706e402c481c111541014032080c40d40c080644050880f560002e0201903000c03031035505111005020324400c1208640d02e280c03910a1b0b20800c64140241052030311540d00c0030710901d00141b400c2a0203030304500710341041a4501405c02c0c8240c41d040c10f00011403a0159101c6040100c401400303040c0304540c00c00c07507041c06150031000c00184044480d9107403540d00c01d00c04054620903102071001c6020440c010345000d144a004401e02000f80c1058072171800188141040000c480340b1446800e00c10107480c0c0000c08444e1100d840b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 651636205 1250 651634955 651634957
    0x307020f0906060906040603020a030b121c03060f0b1801110d0302032809200102120d141e090d090302060d0e030307121104081f0204090c0305040221070605 69
    0xc11034000c1c00400c0313010640d81c0c03660041d100a1a042c2e80169039411231500c001c090301c41c3d01c1d08050060410620072000c01d007020502803000314040c110300400b0f2001c0f5408a015101991044014094058011a89441c100020a45828a000340c2c82504c044d45004582d040505040c0d0701c400e400c800355520310300c1e200340c0003075401103103a90b042c0c40000c038158800002004076082c1c14038400e80e28454035040240c1c080c00d40d182d04403007031907005c1006000300c0007030344800550004c40004030f00050320600060341580012000300c00260038060300e14103560408003900d010001e076041d2004450000d00c02510000700031302c40351856560844024919800e0005903040380030714040301c0340c40300400448140100301551040c0856070368001d10484101003642102ca00300503210701c6440c00c0009000460000651450080f000f03000c02014881c5802e030136009018070780000403070904000145a03201d82c036810407030081c0d0003111540d01250100b400035940e400d08041085103500014010412580684 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 651637455 1250 651636205 651636211
    0x80d0c03110316020f0301050606033c060108010e070509060702130f0b0f0a150509030a0b010e0709080102030601170a06030219150c050304032409150507020307020f09 74
    0x208210340c00e0001460700c1c0742140c205100d0144030402c0745074404103601d09282d41d400040d0041d8000c028a080140100745180320040990451601413842c088010b03407100a10f089014144442c0d080c00516840f40c0345122206440b0640044e030145c00105440300000c044501809007030700d403a45001c1c10794090240039008440c040c4d902028080d016440700b001c030301510301c008012441c0011000d03150800c1003103155000002a0040e6606081400300191050300e00808400d40c2c10959140d0207140f0000f40340c6081c0740402000403444900000c1e00854205805008410984800c10001d0700c87c15594201d00084a4450004280421400c0e1004034807200e550400c07071002c80417840e5501ca40114554441e001040003500c609600200700318000c858a81ca1f490000e4a0903908025040d1200c994034080c500010b040190900c0e90a4071702c010042e801c841c02c900203407090220340c031141000300422004100c034100c01d50414002802c07a9101108075180194000e1a105000f500c41d0144088082c0003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 651638705 1250 651637455 651637457
    0x10509040c090e0a0302010e010e031204060605030d02060a0501050108040308071101060f0f09060501090b030109020d06242d030e0111070c081605060406050306010215101a04080d0c03 81
    0x7030706000c58100b5190050301e021101140003000c0015041c80c00074210383d8901d440d0301d002c1e4904078420200c04c0001c0200e440b04290899a404c45480f6400c002c40105801c2d4007982c1c1c14030030050743c0790145030042541442440040c40030000e40c2c0c0d81d81c0044d03038007101c12078005000130321080029140700d0003038043e0780040591a0001032507039140c440d41c00c2000702d650841e8009907840b140c100140701c2c1d98064540070742020300c4d1000146142c1040d07640e4a0206010310009240c000c03805085001c1c0640c030080040134521100100f12080511000301a00c0d89403d03000050800d810507040003500702d840e11002180754030364081704480408114010420b2161941381952a854001c040c52401d202030701c03400e40906006241c0c0e07854500d00511740703e82c03d018943d07940700e41c1004000310b07a0780c60152011070311182441944e995071000100c1c02c0c0044021102d81240700c090511184c0558904050241c9802d010000a290301e407045c070300064043c910410f8400d07841614001d06103031080500f14245886 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 651639955 1250 651638705 651638723
    0x100b090103170c0f160810021206060c030d0c0e2d040b030703080a020d020f0d09030b07020102070c0f21120f1101091a0705160305090a09020c010c11030a0801050904 73
    0x130012080c1807031800c1103034401524504c2010720240c0000d1007840d4200681600461130306860740100c1040080003002e55102c0e10012514102da48024011518210b4080f4010805a4071881c0e001e00300210ba222114007482b58030880040440710b41c18401c2000748002c40c40c01c044908802000003400480740c00d10380600071007100100040541c3c02a1000601c503030044c0c207180c0c5103030100a15000040410224507403000c003242403072035042111001500c0e08440e054110381c0d1001ca003a07000e031081c0c105c020120106c2c418001150032502280d402030380d510407801048048404240c140c0304031a0301019004041c1214400c1c1000d01411641c5c040c11514101050000186424076007156045038007030b40d0b0340c110b50f010b9180100450300540c3d0f103c0010b05200e8205804020b10b540c00310300c104402010300c0000102c071602640c401d8507810043c2098801590740300601141c2c540a040500350100103c5d41103022040c01400c007001707903240c000482d5540c9521780e203030004000346142c024005890b8006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 651641205 1250 651639955 651639973
    0x90c090604090906270318120c031205090609040e0a150e060c030103031d060c030c0726060c0723010905060603011b0320070302100b090103170c 64
    0x540402600081507600c0c00003d440202d03040483c26100344540701e020344602c2c045854401e5800007154042c094252a01200860fa007903540d98a80034280c00826a265a11034044100194034150005a92090301c003050540d6042d042527405009454580d40d11031030612003442c003030074681d0219001c00d082000319a941280364644c1091922801da980c042542c965030040d90009080080640102c4100c101a103158950345000340034491070000030704e20801b940c503c0402d9070340c0d490a48002041d41000e80e940c444260304c0aa0382d60009204007a41900103480307844d2440700307051040584440e2000035042c01e5980114204e02e42c0c1c000c075022a40d002c00e00d41460740d014604a24104044603071000020000c00b01e0070454505038004050502c0ba83c14000d81c0c3d4284480e54140000081160030003187d81d80111045a012200c0b00c800c201e402d0101085480038141d0000710358080203e40d5400300450340c0c017241400010802400302900f8000c964003504681402c2c8401420101c1280d010307521084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 651642455 1250 651641205 651641209
    0x150a0609063c063509070e04110607440906040b070f23150601230904020d05061c0201050f1b16140612130503040902030a020d11031005090c09 63
    0x250b52100340401022030f10081005c2a030b0100726601c050030a481c20a4018900b0380e41c0d049030f19490700310a5000d207102169a0080100e02c1c00c4d542c02255058000c204490070b034010401c10640141d154500e2480c06881d881d001182c620203c902410028100b18074150400005940507805000d00300e80603a01c208084020039003691800c40410b01c0c02d440b02c4110000b549459160080c0e00d0502111309642d4000d01c8242e80e0411010304074198cc00d0440c0940f600b01d82104d1600340201540d0303607081400000d182d40c40944650206106102c116021108140003c007035145003250608000d0124000b001550301c8420302c00e02030165907042c0c1c8004060804020038450414252242004000c03200110500048111100c000101441590a9401c0c020000404440c00c07134003038a8144405248400001400800c3c001c0b640540303245e0106643da0304200004400a40c443e030300402000d450914500a00705038201120300036844103d4150449003090104070b4000006410340c0c0e041d00b03040100258036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 651643705 1250 651642455 651642527
    0xb04120c080f100e241306050901050108120304050a0803060a090903080615090604030213180b01140a08032a0d09210302150a0609063c06 61
    0x40c900c150090880002004020740c2030740e10030543c21304250030405440003409060400ca8440c45610444516146c42e200d1059071007281c82c8102034116070801081080c00c400c1504120304a607501401c80d407212901c0104d00300d0f40c1c00180c500503c180c0060091001090180c03025682000000b080d41482c241d581217030504440b00d2941c201c003c41c20350020010381d443c0080d40910709802c040d018a140c500c00c980050803d10550000a104a0140041d0801c400d4035038041130810b0901e81d04100034252505241010410900c2164001040d10800780000e09100d400d010440fa1040f0045050a0801d81945500c5201000419012a10341e51101c20f581c0b0810044602101d191612103031141481801c51440360820315842044842c1440200003030342c0095009070a030380c110b4600710151190400d46010340381d2540a030072002c1c100b078800300e0403580c500c903ca05071900240000903041c1c0e1082280c40440e01105080b0000c01c1c08480410009000c2d1031200001c210003003d42c2d0034a40048180313800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 651644955 1250 651643705 651643723
    0xa0c021804060e01060504150506030c04090914010507023c1b010813020f19030506070e090708091b060d05010b031803030f0105130b091612060b04120c08 68
    0x11464543c0c000301d0410100380318640c0a0181603c080c86158410040f0003014045449424028030700040016a9031f1800000d036006044074030814400c0742143d007004000c040086210301d19951030135010030002800000c0006409081032414041070511303d030543d1000000c140d206a03c2ca0054a654041c041c09001250411131310104080341510a40001460114000c00702450100300e0032031030015a8503120028448a0700307c41d10700da0103003964100b80c51501150b100a045208880601c0655600400c84010380312065450380000c1c0e881d82c404903051513040e6103a10958110070515a1107900e40c410f00810640042d02c00c529020501d0001421a01d0984c410b080091000c81440480502c0903614004000d010b401517095040031b141100d40600c06124161265120302c118041048003504030140515000f0580d100919000002c0c801d01c031407512880c00052501c243c0142c0350f0f5101e00c030b00d034282d0365001107990406040c851550700c01d107610301d400d407010440c080b000204031508101d680c2c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 651646205 1250 651644955 651644963
    0x1b021f05041a03060915030a0f050120030609240604120309080703030212250b060108060d08030a0e07080f0a0308010b09010f030c090801060905040512040b0a0c021804 74
    0x1e6114500010030b9400c440c1c16040e1000c41c0010002d012641e500c01c00943c3d0440742c0706149080c541b000030002840c00300d4001c40144642e81958080741440340c1075014400710464105107030804902c0c0d0006d10b005210844402c0c0e800784c0c8043c007080e4010040041c003030600c5400b140e01aa003001120020384180c1065008048200302100d6400815600c540040002c080c03036801440d12a041d9070300a92566000e405420380c0d004003240041c0c0c5280403085201c5501102c105d042c080c00c0090030a48074901c000c42e07155000c200c000000c2031060805401445a0540001e40c540c21621044c2605019002000b0301c3d40081c030440c4000b050300e00062003001c8102010900a24040d1014030300a48030960581c041000143d042c0560016644c1180c49880011880d2074002041c2503209015a404405034020b400c00390b2804501144125850344590702481c020f4040301c182250b6a02002002e200b0303400303482d0542d030081c0005601eaa020389001c51201d80300500044c40d840041c4010080c401046a05031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 651647455 1250 651646205 651646207
    0x4060305012703050a0c020a03021002030c0d140d05060f032a04060302150304061b02010603050f0c0a0501110a080a0804140c0102032706070302030c0706090302011b021f05 76
    0x24480e28524498580d039002d501207021040c0c41030740300600b19001d400c12101c180140ca4a0040456907074054103006154003c203103031008109000000e5483d0440c18280a072407041c0c411f4688201e000340042c49801003035840d010b240c0080c0c03024010107490f000d0001500403400c0c281d822403568040c0003c9403041000c5080c4170300003400304504200c00c41c030019000d010b50b18240003880513031940701078142c01550201080b9500c1d200c5181600080c900020140110442d404001034460760641000c000c90303010b0011126400c0f03000e04170580340e540c405082640a00d90490400c2039501514415208684500c195000c40b0669240c1d0040c03940028520000103000d00e0801c0f0400c4900d10b54284000005001008031058200002c1e61f284100c030b010703500c0f03c0b036000c007206034155080410300b120000c050000c7c0c0e140c1640b4034020f50b603a00000801c800f28001e841d004580948595100710440c0c1e0142c0d200700400d00401c0303c000341c5039440041a40c0002c0c1901640d900740c43c068211800a0525603641 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 651648705 1250 651647455 651647471
    0x50126071d130c0f0804020d0b2220040204230607050a0501022809091a03070f0f060f05031f150c0506070201020715020d150603060806060108060d0f020f0406030501 73
    0x4c0203540c585485a050200c00020301000d40c803628407030f680c00c2d030f4091a01c0b102d0f0340300d07540180f0101094640d014849036916921008100101010781d42141711000e07000002c495180412069001354010910001b8888000c0803100301001c200d41e004c2040a0300c814038180b441c0e100d540c18036038081d2040c1d9140e900015841e484440149202c03001d959405407100840d003041000808040052089010079616214605104590038039550042d9400408580c2c0b00d81d9105c0d8a4054051144218150400c8040c80001d40d00d024102d200f0b4020840d60780c040c0356554941c5200045401c40702e440081c0a0580000718a14041389100d10000200ea1101e80e0002c1c22f5113441850008020300b10b50031640140130790f000194034203006c41c50b82c07075170100007580710711300c2c0c0d10324000400c80546106050200350130001451505680301100b605c0803041903ca40c1d541d20001915070203025900a40c0101001100c0408100c4440b00b00d0136051004103014110b0f04034034002410340f85c03690001e84259540313441c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 651649955 1250 651648705 651648707
    0x4030c17120105060702090a0c03061d0105100504030f0b07090b0a0e0a090b0102100b0f030a12020c0d020f010c0606081b12071d10080a0606050126071d130c 69
    0x766801071000b200c0203440c19806074041081440e01400345d824903601c440300040c03030302e0282d04820050129640452181081c02c0011007005600303205550058001a1584020300d105204480c281e03070b080380802c03031008519920294000c500500b20310800c19a4400829550300d400d00415000321035030740b415214050101008005c01650340b100c440d052030701700d803103942e66008134800068103210303180000e00d0070010010030311560324102c000d503144c0104080c0030f040202c0d02c0e040b160751141940c00c584a1098400a11803062801c3c0c502944c041400201050385610800e0140090340c42004042442603130390000519291805001c0c0550490300718809803103051031502c0e12002d0000704018040300d0b18020300d8101d801a01c0f000c0c0507031000710078005038885041d0401c8100401055085468400040c2454030052a8501480c0d00181c5419210b200601e036a00c440318001c2d8100d40c8251309078035540c4081c0d600100c14011321a4018202198000340d0f95100000340c04040044c0012810035100342c1c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 651651205 1250 651649955 651649987
    0x1303140d092904050c060c011e060e0f070c0f05030c07060207060201150e01060e03070807120204110a0f080a0b090c0c191101211b0806010e030a020904030c17 70
    0x70910b000c000800b0840400c20005030480d0302e0000f03890050b0394045040d80203014044101d40440c60008240d07132482c0999a582c800c0040701e00c1d03000b0440d581e841e070040100d00c03c0b0301a10280f0000760b0b20740951002c10803d15035040208d10401c200da207031400800310281481099403100c000340e04198400c114240d020301640d0b82124020035a0302e5401c1c00c11501c0ca644420600070f81c0c0c01c00000f0030749442580c40400070708001c0c0c103641007252680c0e6075a20b942104401044400ca0007030f4104424a102d0017449000c0c1c40700951b858959210901c0e11500803a507080005200707030082602d480c20400540c58258296015a903408150740d0b468007070f1350555140800030000e030900c0407654070384c880100300710040014001409203050114015680443d07065200c0da20f17416603032240340c0034841005a800300b4080d604640e1680ba540c1d40c59031804010740e40a101c0c41c440c95099000302e000d6000510344600880e91140c400e041000c6d1003411a190500c0180c19a4a0002d0b070901c005001c20754040c9041c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 651652455 1250 651651205 651651263
    0x604020f0307080721170705070918060506040f0f02120f0c0a1103091c050705040203010b0d050604230403020705100c032d05071a1303140d09 63
    0x16000b040a03600d008107683da521800e114940107050000015100002509400d08000b60800580c4209266a0003c030809a101d584200c0e0303e48904280010300f21201c1c0510030380102c50301410101001c00781c50358400380ca0003c000340d51180d92130f428228800103078416116260720140c130068585800c06505802d00002030a00a20401c1402c108042e481b84181114100b01c8213103407021260001d04074482c95805802031440e071141c450100d504000b03484581c5011034500171001c88113229079641c1030008034030080c02021035811041007007070040c40b00c0e070304016004a405440000d04000c0940010213070b04004000e2860100345400b0710040c590304100703120181500b20b07400b400300c5400020241c00401c00340d01c0182448030303908517003511b440030080f0a4180ca070015220081c804441e003004125a000880031102c03d18910540b108e03401d1140381142c4210814002c110010425403001d0b14803440c10341d09034218170b504110700480014540180c0b80c582c0d00c28204510000c505040c1018284000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 651653705 1250 651652455 651652459
    0x1050c090109050f03030412030e0a2c0106020d180b030f0f0703050c03070f0c050a0302010518070b090402030c0f0408010603110102030703201e1606050f070618020d050604020f 78
    0x3c001003131103e50300072040301c0440e6110300980b03512044500c0c0568480c84c44000c000d0b48002c01d07010016100c0f4039032012a088400c3c0e1040456000a401c0c3d09000e00340c8207002c1c200050344a0511401603d018284800b003003425950826003d035a58061049607520460b01c212104a020b001d12079070b50a00031049420200a05041c01103140c000171040050000130400c17410008401c22400329540500229690560040140c034040780383c505029001c1d0200b541d15081d000d22002d001500f801c0007141c190103640d410a16035203845000d400b040301940002c3d01008404508101c00401120500000c0000341010000443c0d098514241055088540c40d41c0c10b065410801030040001d13800001d407845001c01001d600484d51400d100d0500e445520b0869120041c0601e03004c01b400c00f000551903c0261203980014242a25003404640364002c42100828080d4240000310000340284c000a4080c1c2816155255420b299000030755084d840e03400544540e085001807105509248290f202c4003101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 651654955 1250 651653705 651653719
    0xa03091506150906170a060b120f10030f061a09090a0203070b120a09030210020703170612030d1e060e150f03030f07020d021914030a200d0501050c09010905 69
    0x307404030203040c0d02c20380821150b040405c800040d210007016481078016042407806162140c52483d5100740610307090303462601e101c91000009540001c0306d6400d206407503004100300078011040d524030b0302600ea103503464252440b504c4d2904800e81c03184900d9078895243d030b034014130700200c00c3d006140c180b02a5030004100d25504120a0b400d428240c03001a0b00f00134a2480040c0c85003040c14200c0c141100c40f640d00b52110300006c0c103502459480600f910039011001c62200c02511000104034041c2c004099aa035a42c009016120912025520800d000805100300d034440307130845010300c412682140c105180400d11841881101d1200d0504038403a100d055440968041c2240e000940c5d80c003441d00701000c003000002e41c82046480d00b0101400c0d60707901400a28404550390010b05150206008822101c00b940d08100c03110718002034510041034000d14158402c5040c1c48229403080f00b8042e40c20f4000050051660010703c0034441e062042020340b410070b8407448821f00042c4131081ea40d2020b0701c6a10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 651656205 1250 651654955 651654959
    0x41e0f0e070e0d050f011a1302160807051f05040308060904052107080c060402010215191a0a060f030b01090807060c030908061003210906050a030915061509 69
    0x70300500c00000602d41107444036124001c42c940346280000782148401c06509081842d05607482c40017001c031004ca0201e501c094540c4580c6080380880c020a2140600d0407000150000801e40c01c00003080b50f20300800c1030b90301e41d100000e07861500c0121450515451940e800811061591005203580c21000c11520507109051584840d40e0b00c603040a0600030a112411a40b0b1004c40c6c1101158089035021030364585034580008542c0e200c020842d400da0260041c044030f04081101c2c006010300c100c0038801c400b060700c4584c0b84410018861044506080e03004e0900d074251583d039202c0148001c0c400d658602c3e188454007903005041c0c0301984526818032420b030406005107200880d0060555000345089504420a030408449100b1140d01440c003601603a800d002040e07101e0b41030b880a42c1c1c001d90b02c5009004803041c4092201015094080019129403003d010451080c0002c00441d04c1030720300400d48461903100c4000b803041d02d02c0f070030801c555180c9003040b000d40ca100d0200202010b508001076094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 651657455 1250 651656205 651656207
    0x216021c02090412030e01051024051c061706010302030712080301031502160c05012c10031508160506280314010303020a1112030a0311041e0f0e07 65
    0x401a00081552801c4aa206a001d209900c08805006c0703a400074810340c00d1940400030f025145004580700500031521080c07110501c0c0d0071001e98802e140d9035192a080d0030030032109403003c50074680f1000b5a1204000600d403910442000a0088800b01400e15945584100362600400358009442c0400345144080410341c07540035281180c0d003114070341c881c0e0010003068500a22400d0000e01080703400401e4103080c05414110402038480a1302d99144800d10101405400c0081d0300481110941088000025090283c0e550707100c8070060901040c0490121107101e00340d0915000704065900c00096420784c0034140907240d00500c0203a94003840c04401c0000948107901c22804a41000b80e80104240e00c02c0c42903010160450642c02c1380c520315612450001d490751390005007076428068102070302580340703007500703580c2d10201c419030096240c0180800260301600000100c0703020740c4818000001d0340c0030100c265001170744274030a07003070390362424040d41d22200017040c0c000b0240300b00d10204100d105 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 651658705 1250 651657455 651657469
    0x20901240e010e2403040b0702070b031311041121010b070b060907110d05044713090228140306030a120305011502060906011205030403060216021c02 66
    0x510a64410010640c40002540c001132010480740c45800000300300014480b00d4042c56018607103950a4a14103550341160340440e02040c1d03002c2c3c821030b800c5001d50f000605140c000c40700340300000c1d00c08681d0018042041c1c0b5280c0141c090020135060508280c1e0400e2890301c401c6014000c4000503d090800c02e8940b220580401400d0901900c2802d0126100502a101e04205846600100c03078070050128070003045900700f4403071030601581664684003000340d10701c483c0079200060040b01d2907030b038404211030f02c0f959070320f04003961070b054100400460030001c485010098820b100707000d80d661012188800d0113013610780d040b0b40307188507a40001d401944d02549001c0c190410007030b080c0d01c07a02d076800001d0801500d040014031103092030608900c1290943c224038101d03927501c51010640c21601da826a19603400f01d03040072242d000840140000240da0003040103050049040382c0c2030544960b40e900490780240c00c01c0d01e003206013100100843c64084aa600c400031140e52407900d400e030613400b01e510 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 651659955 1250 651658705 651658727
    0xe1f0f05040e062703040e070e120619050c070c0e040201080708010312030b01120203070f0e10051e0c03030405010209190503100f020c0106060c020909070b040b0a0201020403020901240e01 83
    0x1d401401084da070031403082040c2e5018001e0f000480a45050911024220040802c00c075409244039450b40070706d003030000c41e45501c41d2a0506a42809441000d40e6000501c0d0040c841e40303c0110034040580410b210303540020103441c0030b0003032601c1d030704190002501c40c0200414201c2002891001400050328124000380000b0180c00d011410142c00340058520740c3d640301c00c0c16001d610210400004030341c0601003c42070001e0b0b0300d903100700c0a2008240300304120150b140c84045201040307040304201d0041110509100305d0140c183c00e00c03c550702c026003554001e44059401d6900454138081e81d19111100c807075050340e14111f6400c1540390001003600c60840c44040440c5580c0c035000c0280400d4190103c41c000c0070804020481552944409401411081d009070b005e240800000389070311800003000c40940d4442c07260541010b19108001c1c100e0340c0106041011950240400030041c2c64250829000e02400e00c3c514285146010200c03807031600100f600300411801c0c0c45a028540d07005005d41071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 651661205 1250 651659955 651660001
    0x705030d050406020702090411010f0e01051b0a17120601032a0e0901180513021c06020c06070806031009020a12020d020a08030c1006030206040e1f0f05040e06 70
    0xd207641e00d03420284024003c0202c069044140ca0741000200b081140b0a103500c0c50003602c600350540d409800482da1503a460010324042441005a040703843e0200400d440d00c480c286040b54842c61035940c0b031604041803541552403550300403039501480e8440071700555120300c0c207137010059110914a0062480d00c18003030042c41c641c0c0c0a03000f914840c4600084120701101400c441e549580d60b004542081020000903081c007032400000c01c1c89103000f2000c0f4800c4680023080000b641c0c03880441180e01ca02003e004403401c55080000300074001081c403031180f040d400754591514925022082c1414001d403155090385051506148000503a02c580001040d61486101c00700c1d08800d501c04619084050319020354413208102d8002038044000001301754000c0e2803400d540d119040300d200801030b6204d6010081d80b028061106005505c01c2c50245a03001074103c41c000860140207a040780b00c41d229404ca44d02182080100b88042e0a1600078443c076820803c001b418985801c07505000c441e04c1e1907116074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 651662455 1250 651661205 651661211
    0x171603030516050d02060a0f29030307052b02031c0509033f090712030521042006180a05030706091818020d03091502071a0705030d 58
    0x440ba001981000782200d542c010125800042e8a810280d91071004a510102c1203040101145842e141c0303001303800141c03100c88084038481d250484102e10b00007141c10b03015050312040c000400459070070401144185000340080c4044081da550000c1904c403251003607015580200714800016091540074554443c044900140c01d0b11040700150852040c17038000345200d11100307000d84141182c60350300810302c03243c0d0890800c1d05010140d400c0035140c1c102c94007502500700c602e041291600a02104c03402c28802e00d010303440c100d004440e02c8628555140303081d044400d03000400c42004940c01000d060000d11400754542180031000107183d45c811003880c40e1000c0ca60f80034841c06620780104031005440010150b0f9082500c0e0b082c001c2c070f09500d0b481440580b84011150911030502880b03042c8103502c207444c03a0522400300360244201c1401660048040088074000040c550f40d42c90310074000c15089a011b46095032400008001500c000c418601000a0403c5017400240000007110b8520303c01075408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 651663705 1250 651662455 651662467
    0x140c0a17090a11240c070621020a0c0c15080703050115180b280f0c020418021201090510050f0f07030b06070f0b0f040b0604020705030409020703091716030305 70
    0x4640001e50000c0f0070415112061240980c1e01d460304003802d01c5040c03440845541c20b0b030b507d0f400c460b1152080744a040c00d4481d8080c08020f40403e40081510441600f00711040880c2a595006103017410b070f21501c0919101c0300c0b8041219803050001e0b400980e1840e040c45a941020082458018006640020300260260036886884003404100040003020f6080c1c0d01d031100329284511400600c50340015242601c2e400d080c00c1d40c021207201420080340e5480c1103841c0c105a0031300000b000c5210350600d003d941c61b0100380050f5202c40080700c03403041020001c40c0c494014641280f604940103101c02e0201d080504200e90508001c00c8198040740c0501d1042c2c194541e03142c20740c001c0c608000b41e01d4025400040301410301220203502c4e20f400744030302c1d0072425903512a442ca41031202d0a4500505003161503000c90700b18031f410b0300a0058a40100c1c29070349030030756031000c000880e801040f08038046400c1840422010701c58544100207081c00c43c02a04100c8050740351076014461038007001703081c001c001c988 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 651664955 1250 651663705 651663709
    0x1030207021804050c03060c0a080c0708120a0c030e1504241104050a090c02071a0c0109060e070617070318080c07090f0209030c13140c0a17090a11 65
    0x18940d55200c6900b14030040c1001c0c103180303407144810140d080c040e11524020540324034100e01121120481d0b551500c00907100e580300011254058082904d071b50000703120030065500301c5c000c207174000e504610002030b0380c900400020741900c0c401d508201003504a0682071900b0600c0d4020198010b0340407290028040350704140e180c5d290400e02108240616040000f14054912070050050340c1d81191107041883c0c1d2559104c090f42c0580c001c134001600000420007a40001c5400701d01415008488203080200c1c14002d00d007112041c20054038015114480340c0d280302003e100c4a0044c02c02ea207041d0401840d901c0c2c0c0b4450824024100d1010140da03440348890a10190300401c10b503d40c031241e069505c0342c00d1034603140c0e1a01540180c00b811480d00c102c454140700c840c42220300980c2c014001d0840001040100002d442c40703403403000c541984031114241d030481400d20103441554030004068980c5ca82520092924040407481000c91000301c040c807521304000074418600ca948002059082132036100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 651666205 1250 651664955 651664969
    0x10c021f091a0403061d150a0227120f0a0807050115030812090c0d0308091903020d02070e10050609040b060c1b0910030803100302060a0903051501030c050103020702 73
    0xc011442000d449401c2c2c1c501d05201d10080089a000f08028061000c02010700320240d000c500940e030f010791022141d2105801010105540306190420050030200c9210059002c00303480a500043e0140f000d09056082c40d000000300e041440ca03034010024100380307030002d694405030620f014045030008521441004001d41000d10314907100c60b10200681c0e541e1400da21242c001001041001c4540c4000a04007400003e4807030740e81b04020481000209561003e540030032002d444080c40e8000c0789062203202c003459004800e103d10030341c01442c0c20203428000a0400003d134220094050b030310800d0040c800b16020f001030551b01304444a944d100e4003540014011301400b4880d98004d039011480300241a808075500030b00c0030035007d00c2c41c40b0134654000c00c030b289a0100c0340303001070921102e405e0004c070780c081c8090750317000e00341c11002103099850303800094464016448140008196010a0040000034041b40680340b81481c2c2100c140e50450f554149800c0442c0a05410598003113002019561005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 651667455 1250 651666205 651666209
    0x6060d060917070311060c040b1810081006090b0a1101090c260609060c1b0a0807210e121e01020703020c01211805060708090606010c021f09 62
    0x42d0021140482c40b4126a000d60490401580815090301260740580000700380c01d0f02c107461052000b40307002d00303122800d54181c0200c60890300020002c07035807515070b84443d003201941c0d00341c80d1500c445616200e180306404015075085070741081045c18041008a0180007518420103e60426400c4403070510a01801010040c001030a041981000004c41e20b0141444c0c004110091020240200c00c80c983c1b140e4070201034440c1d4490341d2044c0001070301c0c2250b83c8054a001012410003269804200d00706900d0705079044000d5401d40310010780e0341d0410800d101c07504100a402c1007074104100d10301101502c64142040c9103401415404284c01000400303100004440702d601d08280f82d000e0802c3d1a5038000d4000d80401c8016126815100c07608d1360054400018010b030010710004015403d001c1031001e0400030703491614100700410f00800150042c020769100d2800c580c5c9011a40c40c054403907600d0400f0142913103040c8250341640c0405622075403941c00501038070408641203020008822600c52110f9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 651668705 1250 651667455 651667463
    0x51002181804110d0308012105100b04150605070618020907030b090a0605010e0108190e030403050c030a020a090c0309150203070e011110110403050717060615070b04020301110a2007060206060d0609 87
    0xc2c10035060030ac1d0b00c1e03210315500300c015603040048501482c21b502c0c00340128003501c808075030300384411400580c0d40d4205415000f505a84590008181d502203080804207642d1640460b848400488403428089480e0b0380c05140c040040c08124600b07030010f811a9980d0301c50034104a0402c00040b1052030113082c8200e642660f8904001060308801c500b901c0790054001101d09002d2240941402d10f00001c184540640080014240d5403034000703800000d00004c40c488040c107490f0341c4010302150b040082509940440700d40035a41c2d10345904001c0528501d02802d605104002e0b013100c1280e4400a02c4001040040c42e00050800d055502500c1500481d400104148034105001c01c3c14584809010020500380048550307e4482c3d50801101e43c20b4054850702d680414001d010200c1e00c0150f846400c036002078000904070300090380c000001c1d84140c41c0400820307122141301000d2404103a018001c10b0b00c0038090306d0000d00346013009440d02c0f00604094803981031050312000740440c40e03010360222944 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 651669955 1250 651668705 651668713
    0x180f031501061d0306253f061412070e010f1403120d02070512031018050903310b030106120209030304050409080f1c0612051002181804110d0308012105 67
    0xc4c0c48203d000729040c40440d0301c003020781d601c290300003280b6000700c1007582d4400c2c01004049c41c0d070009000302d01c1480750100d4050302c248000003592150a040050103440405008080039050041b00c03460403c850442a0090b4042e841800b0f2201030341d010b44145514282c1d015942c1e000508085251101c800c1105038051000401d200d108504e42c1c8400d411200c180d04003101c0701402028400440d107048402c000d4a41082146d6210520301c2204011101460031404480040030000c1e000c01c1c00303460b04614030010f0b0001c018065150070a044808008055105502c0d041a50010a403a4007451056500581e1901003400c104040b040c161011541d816075015100e01d0346012000d5600848103000c0756503413500d40046190091201b40d1031f0b600703070060018100d214007080030300000c2d40090084040054035000c100016941c5140300556aa070005055400b81001e061246d5485203041c0c00500c138142d0880c010f00080d0300308074010304582d220303d2542c0c100c02d20641e0710000120b00140040035401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 651671205 1250 651669955 651670007
    0x1b0503030309010212070f091e3f1106070204020702030a03021b0d031e0909152c0a18150c08010902180f031501061d030625 55
    0x4158090103803178070010400b500326201c00707405984401e280400c07040012003651050002681c40015007001003200c80ca9412501c0e581c1e03141034103507542d02400034130410144494041c13003810801000e1501c3c41900c0b0704611001d9035a03600603844060146140103030000706a800035980e490781a5030055401606031a0805007902d0300a4580141202c2c1340070010481c0d2040d000f60418580c0b0118070f07079254072584041c1851030b005c1c18441f000f40e0649010002005004514220301c1c0c09800341041c4031030f00d580200750518900d07800750b000815916018800040d903844800c1110b980964011003a640c001031700400c21504580328000400b0042c09a205000c07444a180c08158800030314802c1ca542c03210032590704c0d4082d45050b40b09600341c2007103c105075614071040b46060b0f4444c4441c00d00041c01c490200c4654074400da01c0c500241c2c000780210342c01e031012141081c000420418280801c40143c25a4980100011850403a60100b04151040d41510b020380138001e503c000480b200420074641019 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 651672455 1250 651671205 651671221
    0x50a051302090d031809020304030e01050702030c2206150917030d14061206060a1e0e040b0612030405150a111c1b02030606150f030f060f060703020a1b05030303 71
    0x116045c6804c4202a4907580001145900d5100b03586c0155415504c011040100000441e1103070004031040c1d900d401844452a803d0f80c5d038a00014101007100c1c2022500106c60414104a40072a4040c00030400b4a80c81c134802d43c0e40c02024141503072a00115001003820000860b07245010745082c08150034941820520940380b040e4101d4407800084820140c00b0f003a01010030b032504407e90700640c00c079001084c01d00c9040320242c8543c154019060600880503560b111078410380e8002d640c25664034542130180110790800500392280b41d4070040096280615040c00704861404c006407a8a042c007002c6084040d03a072003100842d1031401d02208540d1040303100851540c00070701e13061408000c110302400070cc1c0d9610108200460580d0001c000e0b00d89561444241704040012112400040100300b0406a40b142071030042c42c0100d0404003d40c14500d0610700b40103024406030031301072080c4814420040020340c0050b080049580c030248000c00754180064036000d815454211682c54040401000300407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 651673705 1250 651672455 651672467
    0x2031905040e010506130e22080705070b0304170d0b220501050414132108040b01060309080a1404180f0b15040905041b120302060907050a051302090d03 67
    0x142d4002c10700118075981c0c82d01001241d00c02d90040c1c4240e0700700041d08001d4842c4560042d64095203140740201400c03420f402c5004001c1181004450b4072402007451001d006081191038050056648402d00c1c41c01c1940303406216501000032580c03d0300d000500c01e0b28205140d08544012400a0500c80e07824011141c5840c0603113001c208056207900c0c1c1800051980741902450300844614000480b658a60001138020075840440070750304464111f8030390170340402001181c1600c00c45a5224161400c0c549424220003906074030005c00c250404281d440490980012076000d08918200820129020f079003101b4240542ea01000491600c594102d182c003410350000003620b8403080c010418409048108a50700703a0340440704900e40340a10051000107183c3c0c0c40070b0b80007406940750400310701066190246a140d10f40080d034610b011111004101758042010303d420504000181c00c20b142440045502c0703100c148a0b45110b0060040d50500b107800503412680d0811014143d036112544a080c05016 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 651674955 1250 651673705 651673709
    0x11070c2421110c0114062205041b0f1d2203090312030c02011b020a02061810030207020f040b1f030212070203071704050310020711030a0b1e04050a06020a0203190504 73
    0xc1e2641d500002103c40c68910009000014000484110142060805002824002c00403506120000307848212600e0310742b80380c0300824664800d501250f080606d20100c840103c0303018072608a89038280001e0b5221043d060056082c0141c824900d0b1000d41030485020556620140c1154007440e0300701400d9515030070400005a03660001e02801c4002501144e010300009200001038000f40d095800500e04a0010721200e1596a218075500032a0b00000e801d00003402888004a80e00065000842c201450038103005c081c01c0310200403401240000c00d01040304000b54881003440480d1910a141c06a0705966100104603045201440c008201031345e00d80c000801520f1300100c2140e070340d62550122003200c1c22f450000d005820347c1d00c210300782c00c80a50401c810442d03001174807451031021900c040201c803690324042c4504c0300140c10320120645181c0c2c0d0480047c08101d081c0301c01c1001007880001d460380b02540c08400140e5554441904905501400b40100200e8840080007024660300c1005403007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 651676205 1250 651674955 651674981
    0x15040504061505010507150c0507170a080a15030b0c16050d110a1a0601050403150518010b01020c0f180108070602070b1206120111070c2421110c01 65
    0xc110b61900300644086c01801d4006101d07442c1c07110351208010642d085501500e00f117082c282c0c2050403640c2e48000742040c0801040740c6410201c0d140d52020350101c08103410584130a01040102003000d0b0103035034541240006040b032190a0003107407841d0184400c90b8051501400b00c40b0040a0914180e501e64034103151400009103090501c032244040828034002035035205c00402e060400d8510909218400140181e043c800180000008641240e0702c0091480c542d80b80042c9915010040340e807140705003003602410742e2401c4181d800c140d0f000603e104070288200d074990340c2c4801c9500041c00e10800c1300081c0010b481020b0000030505400580c0c403050b600d03543c0a0b0344030251211128038680c09030014113000a50320f0408162039040414107030341c0894260001165108400701d80d103440d9440030310102e034290ba00c400c7c100002d400c0e649008106503a4072202e05c01c1005403e82c0106000700d8104410009840d006c1034105550303056000c00800700c0d401501e1600e840403c41a54000c02c80b400703010b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 651677455 1250 651676205 651676241
    0xa0506160605010510020a03180905190e030a050d0f09050a0c090c050702210f12041701020406091a0c1f0c0f0f030c05121003120503010b04030b1504050406 69
    0x41150f02d0704400601c4120170590040000304e44a460448082088041014510441000106400c28903000d200d01c90081c0001d4881082c049221a40450b125400d501440390802c0c025902019400f104a805440c0300c0000880d9403c024042c8000130445058000c10510400c00e0704000c10106608450482d003001d5820401c200f5410400da03154403803034000941c424180c050b440c03003200c4031b040d0341c00f52100c01c1400c80340191b000488103854013003941600340b0b01c52030101e4204800d50b10441602700204400e0001d6085ca481c080001d000c00b800703805030810441c0c038030f8034041c10552030805a4090003c0c0d0021908100c2d075010b5900d1000d0014106501018105081c0c1c8099500606d051025400b07603030f5a031001c10304001d404600401072541c0d450100b003400c110041008020402c0c650040020281c01c11030b0901d1031034a04802c030109144a001e010050004228600050b001d540403a0f421601c19200f643d65108468001c00b0701209241d440b510f0202800140315140e403100c2030041e2032410360 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 651678705 1250 651677455 651677459
    0xc0f1014011a0a0c0303150602011a18070809120f030106170402280801140a0509060705090f0105070210120c030603020f040903110a0f0303050a0608030d0b0a050616060501 76
    0x5020700180440c5600c1e40000c00c1480383c564415441c08100d2030182c03400150005643c40b160900300100c1c0c1c0301d2001070f91240e000ca03588072414102c09140060482d11201002c0d0100030304140d01e04010070440910030504e00244000b50305000d1030040380c4a80c2d5505030b4884008a4900ca103800a006210000300341d43c50094444920010036405143c0091094880503203030911050a10f1b4040012203100110f4800090304160034041e520072116040407401040c584503221404407000140301d6a02c030750000c400d02182c55045130441e651880d007540d00b5500d01e8440401a02c891003100340007034100740142c0c45103042e190f200e04410b1200944000c2402060340f40340d012000d490160002960044102c402c00040d0714155000d071b000c0c14400c3c10300f0701143e051020042c1c01c22000720015155944a000c1e100c08255040c414280d000825040801c03015003070444195803130160303688107807030603a483c0c2d10306100f60b98030b16100300100301c000c3c143e5650307400700609203164820204c02110360600b00000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 651679955 1250 651678705 651678719
    0x10c020a09050a0510030f060911030a030302030a051f06080705070b150406050f18040606210b06010206041101050703090e0a090203010524060f0904150302030c030a0b0a020c0f101401 81
    0x305c40c1125001240101c0124141d280c41c0c000782103c01003201c1c020f8480b0880b603141d403010700601c00f0142c041e8400586a07c5e02503406825140020b00d54400791019000c4440c0e403201c0000038809484003850700229540e40c00505403800d2149400160080082c21b0803c181390f20081c1c0071085100096400703000307107952101400394075103924035000c0d0701880307140800d02c0000500303020170f60117801402e000c1002d540d190f0214001ca0100061085019850504241400b03503a045203030700010b081c4000d02291074140c840580d42111031051034100a000602d04007031520510b07031500645410700e117000d0142030501032003004011084040340254203110000d4440c0501c10141d10030902c0d6204c007040450a02010044298085000718039200803e109252558486c4d1050828101c0041c4410000f20b007107004042c90700ca551540144a540007080520000d18600507550300880b00460158880c28000705040c1068800f070849030b0303648504c07165100d008242d508507003d6040c00c01d100040c141d0b29080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 651681205 1250 651679955 651679981
    0x1512120c0503030606180d060c090f030b0105010e030a0506010e19110301061803120521160e0f090a150503070b0a05070204091b09050c1201090b010c020a09050a05 72
    0x800341c140d40060001403180d080c910700034a020300ca081c43d10b2081c60301c0800003804290740000144e50f207039a80e1000c4884136411001030406802c0c2c40e41a005241d1850313443c003480310814020541000058000c030308090301c1c108410000141d019054074a10742e110301e85600070403030490304000c0c0c00340541c2082d0140c1403184542d905111004811516583c01c04805840418196141001c4130f1001a0000301207120b03010f03c04100d50403561100c0d683d040c0310107040100190140c000030940d400f4001e00510400b1003410300090b00d01d0341001c0501c101d8150004a92500d40300155400c0490001001503801d1658441c00465081c4070070f22000649030f00505a4a442501030402c900a0810050a9080c01040a482010710007800420010345642c1c49000c108092440070b00740d4501c825003400500010300400b0741c0700002050b01030a016054064800000b810b200ba2400c0715034075051408a6482640d01c2c0382102d40240402895994800b100c4008000031103d0000092500020a01001c3d07800b0f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 651682455 1250 651681205 651681227
    0x120910060806010b03361005270f0f1606030506030601090509031918060203030618041103150405010e030901300c02210f1c151212 58
    0x40c020b0815a08086183c1c2c01c0d0f0744040c00e1482003c0c100c0f900c180c030421510303543d0295100701c001c2c01d02c45425008815480d00300004a1101c80d141040d0401c03480220444007240100802c15100b00523003d102501c1b400c0644402100d5050300814829140a0000084c680c413502c48910340080f840781d41e0717501101110400d481c0780340d00da000341c1d004100070985a00459048a41c0905580c030b828407a01c806403800c0c440c41d21880101c0c07801280010320740440140c0d10001d22582c0040c1d4554641080061030741d200c02201d4500b4080c40c10003080a005d24a003800c00202c0001e8125000c50701c5003900080344000468040302d50390300f000f892421602004c8240c80102d201a1281802030401c02c034240c0d4409080d150003403252140a42140080c1031070300030000e0741040c580141000d843c00b04019041e006600140c0c128401042014038050800d1404449840c0d01d0144020b429050203143c110182c02c1a032108240800c0011001c07450003064001c5c0680940b00c0c8a083c901520b02c1442a03d003c0505 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 651683705 1250 651682455 651682469
    0x727030b091606050706060e1e150102120f09060301060507050f0a11010804021212040f080a080703031e230901050f160507061b0e010908030d0f09060212091006 71
    0xc80400c01186019002030400c07175100389400b0900759211400f50010600407a0f40214207010988903e03071500420000503080303100e100070801c204540400103551412200780101100b4000510002a1100c0e81c058070302c03820700180750303540e0303540d40d603c00900300d4104090560309030080d280350034000600003c510202c198400c2107072244000340001903881e4240280140d80000140d4600581114240200ba600309002c02e10f054030b45041205220404250b5000b41c0d010f584502d4006001c00c1c0c01078152ba4a00b541450013046110b500319540900c00020700090480310b003481005036031316007408400400100303a10048200c0341d5031b05020714243c80003991340080c2d9101020104400e00601300900c0301d04155800c003140f80c0b1407603603911011181c400b603200344145802d000d49440076a100740385044405003440c0c1a000117080c009034a440380320380c040408240f99100035890800100c0c0d000140c441d60041c20454448010701841c1e0504007045580ca08a401581601231402c042032240005031415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 651684955 1250 651683705 651683743
    0x6010602060a020d1d0a03090807031109040303060f03050c010f0305010b090d081e0403140d05030f190e10050a1506081e012304050c0a080727030b09 66
    0x141540303620095200c0c403100c03040661101080d800300002980e41709440d480c044000d202d50020ba0400030400800d40d081074010b604100b00400210f0149074441455100031501070000751610316040d0300030040c0354040c21060401002c00014054041074580c07072080207032220700020302c1c007003002c508071002400f80c1e0441d000103110b01c00d12802d001080d01855442a00450300d00302c0c00400c111541a0f000410805041c0000f80c107008110344212003003440031484000f0013103511085c002900d6408010f0164015050300c02c006000c200500101200000d05002c041016000d05080d03181c0726031092a0040c006400c00010804fc000c0c03d20030018120481510000d4050912404585034100540304811005410a4501100829215450003041c03454a122010060949000721403080a80c045200724604401c00410344c03545002c9601d140a83e203400700407960380c00001d584812603a04400f1741c1c0601760000034164403c1051030820f40740180380380700090742c641d4001c0748d030b60414002c078600d2600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 651686205 1250 651684955 651684961
    0x3091507051c0606050f07150203010f08010e010905030304080307020a0f2a0f05010309030c080333090a0e0f0a03080105030708010e0c010c03210b090601020c0a05060f13090506120601060206 84
    0x102500174000c1c951161880540303901e030231084241030740c2080c1c0000c140d001c401001000410024402c034503100b81c40000a2003100720507141c0f00e490707020091014040c0080000011304252080c80052005a80560f40f0900420300341070070b8003520f03000041101e0000e0088946040c4088500344681122811002702c40340b507044c07200450140080f074104505204861500d00c0000d145c010156200f07180088618055a540038403c403100102481c51a1125405110095664a507000380300d910001c810000328100c4030701400545440301d2400301705001c3c014482d0b89002c03d139002811604a4500310308456200f500d6401c841d080300c0f202030030041c050388251f0f542e44155000341c5030068040d02070304210744c6d0283c84410b008800c0120000ca001110340e21480304110f80303030074040160010400c1c401003842451010114a0080c20360007054410300c000b00c2c0306100c0031404c0048641c1e110404c103007100955030b24150000a0403069846500ca0079034800a0b6624020004100d4100c030450350092065031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 651687455 1250 651686205 651686227
    0x4060222090b0405011d360c030613080f0310080303040609120e031b0a1205010516111005090c0301020d09052e0b130e0309012a02010503091507051c060605 69
    0xa90701c0224450783c110700d100c0d0001041f00e40c900704007090101350080e00e00d0b42d2001c801c050801d50b00400a000180d500380c0c0708008a4440030590704e008061078400b9560351034042216540c5102a4030140c1944400070400007000349a4004024803407140080d02c0b1441900c02c3d0544540c058030000a0701540300ca280910318400c0d5041807055050050010b2000580300c08407166405501030094420760b440700140200a51847c21f081041280d0386490320701d0040c050b810b07a032603103494209402c590307490380007107800840c040c4402c0d000140004c0c0215900c0c03182c0013039000a42281340003a90540908600e0100301403406001c0580080088a9618145100600b0780002e005043c0c1d00d42e00404d0301c0c000030300001c600b40715110401808800464a900c2c58500041c6006042585034070100e0b01c100e50309441400c08680c07c40c0c80c0b542401c0c090b80740c1d900d1130101d600c3c1020544000c4000f81c041c2c0d080c0100b50f9000740c02045240c0031841d0030110761046c001002c2c2600d42078070500c000200d040048040030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 651688705 1250 651687455 651687481
    0xa0c1b0606030f0302030315010c030f0f02070e0112030206010e070203030f0903070510021c0b0922060203011d0903030709181e051602010506030604060222090b0405011d 75
    0x554440c540020321161241c849005071181c040003100503920000902040101207490070788116803d191000c00000d0303a81d4010080411641400d0a0213000c2401440040c02404040c010b000354480d125200e607510368143c0d1076500510426400342c0194800451041c0040c61034505c100071315001036107161604a80350700841001803427407642c0d0005001e000c0018006002c401440720b2007070700140c2c4640c07081c18020792540012511a0081e45403100da0b035040d44035011142d910420031002c0d0001e105c102d02c9a00c04038140020014030591000001042c0f03e40d01c00c0c500100102558044401e0340d84403c820341e5030b84401d80e814400b00b9a804070070881c41420f49448464007240000100310359840e202c0b1100c0d044140312503000102e49810411203104e41e00069001001c100c0d01c001e104506040011030b80324038010f4409004180c0010351880140103100c50345121400c03e4050200a07551141d8210051941401882c801c9081400000c1c8015480a0280c0c0c1792007003081d40070041e01e46081d85959 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 651689955 1250 651688705 651688757
    0x1302031003020603131b140306072102040b04030804030605100308181305040b010302131e0b0103020c0d1713050318040b0a06080a0c0504081b0a05061b01050a0c 71
    0x140806802905c4005402c151084a0901010168040250a03c0d041c40b03d002482d110090281e03201100300310241781e00072a405c43c144000b01e20940c0e044003400c00a00a881030390011080350000080007c1081005c10040003120b00844080165440b6005001d030411002d100c09400e0744411b21100022000f003105044038850000c00d0710b09016002000c190a5070402c60301611103045081c010030079801d0400240441c502c20b42400c10440c00c1c015181080223003580d100d13102e6241e0740d48400c4450390080c1d040750048003250040782c0110300203d400a003076400701719807030200c80c1180d4013092119080e5031303404407030f141d111010314200f04d02010368806006000102660164859001e0215912408200ca0141c1411740e603015442ca082c004410690303151804a1003001801c000030000b40d00007140441c00d50044c1c0c580b441e10f8110740800241d84c0481d44c1c005c076500c00d900245d1030313001e20021500342c1070b8403182a000744500e1b500c40302d29108850708010b1a0000c960300b03d07600d15030300f0403000301000c2e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 651691205 1250 651689955 651689971
    0x30c280b28030605131d12180f09180d0c0804030f02130c12050c040602070308130801050a09031e02192102010b03160b0d11271302031003020603 64
    0x43c483e69100006042d401c140684681459a00d00515810a0442c50300b00c0042d840304c00207004014070a86ca5030070310303c2494a441c40ca20781550700c5901903034032001c4208a5100003817820025040400150704a0443c15400228034400c14543d4100903010f40000e0b580309070030880e881d090a2441e121106428600c0344201d80c801c0900b8400d4001d01d10700d1040389105500c959496680c0d0004e1075081003245c80103840398241d403000313000c02c1102a50000c0c6510549500840e01c0341c031007542e801c05207103800c01c40d040842c0c1035003001d04000d01a00720340d0000c0b42e40342c000c2d0b0316203614078000a540741048105400100040e085030084016075200c075041026800e1045404c1d00c00c544c817040405460240446e0ba80c40183d4650126013441c2c03804212800074848810320070400b061034084521264405c0c22241c4003906e8a6030317804680041c40d80142c60009400043ca10144e00007032007002007255079078030391620407615110403001502c002c0c4290f0384582d01030420041614110340801006400040c1055 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 651692455 1250 651691205 651691211
    0x50711040b1503100f0e010306020715050432060f13020d0b1506040b0304061107020d0507090f02180d05031c1e1118030c280b2803 58
    0x490700d4907109055001c6841d60444140c483c18800304100d1100d80a621040c0041c1c5444000e00c02e000700504043d045075842540103984034524a06555401003081d5480741701460101001b0611103865040e1810031070029981090740d0203e0003004543c2c40c01c1c0d1290f809030344660000380b001c1206009058100003440450081c000312a0f00041c0d1581d822482214010521000d210741c1004c42441020001c100b02c429070301301400d0080358001400002c0c4050005501c0c0d407403512600d400281280d42403500039024402c0300300c2d80d00300580e80d09524419015114504442c0c040f0611242c07003601d0720070b6220307038016103108544410840740c00c16000d8280c45901041007015a00090320406078411001c03c58082090741151500d0001c0303920a541011005040090a80f2141c03650801c4407124042002400501002400401c0c60002200042500f10401031820840b0003100c0c20b850b0070205940482c4580b60340c40303141ca9615401200c1d0703080401400d44403612a41e55110002c030500c0307443c520b400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 651693705 1250 651692455 651692471
    0x203030d0c09050909011e05130204060909140c0f22050f1006050906030c0d06030b070203090306010906030302150a020c0316060c090b0313020f030f0f160605071104 73
    0x10204550101c1c00100110b20701e410204900d00309a0816640300007240c0082007651040480103020541d90301901c90000d1303981c8002a90540040800500c1c1034001c3c0c010480240c44101200080c201110b041d00c42800c901e090a851380c1c400219030580a07006402d1000c030150304418883c45000c981d0705005205034003031509600312040d2140611811031303020303035420900302403202c0307508068203400040802000300a00c140944030401207d8200742c007403607600d580c0c441d6406002c0040000e908001e0104440380d06003c0840d900001401d40d4944c02c03401d9600c5a681c82c00036504590540c4001000340c2c0024082c100300d07081c54294991310485510002d0b26048020340f40c43e0030b5034000c0300200c181c0341e0790b52040c40a0001c68850030b04100e01324203201d00c442e0304180b40480c0a0000909400c40343d01050303c14411074441c01d440055850024044590044a00103919282c810354001480d99126040403900d4030302911958208942081c3c60b264039001d00c1d6118000c00c404070803035464010b81c80d0440c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 651694955 1250 651693705 651693727
    0xa0b031b0301020702060c0c090c03100501051c0f0f1104121218030506180607140d09050a200105040b0d0c11160e060607020112050601020a020618041116060504020303 74
    0x30a1f00522070009403884813a00410419a010041c08510040800b4801c2000c0301d505500c101e01500c109080c15a240c1104108035110b01c040d150b403250106003844c0000e030b24058070742c1098000c511a10700c01e000c1d8614044c4154814061803040034019510585070001056039504c4c000180466490000250410800300404120441c1e008a443d54000c3c5c08220014404800900351901c0c540041c2c00c050910040007060f10442c0c400a000000c2e0002d4078500c03040b0242d00010f02d0f035510000361610804070b0f0419510396074071720042110038600c1d0224880558800c90440382a10399400e500340c00c02d0345681045005004c210300003000d00c13103a5010494000703020070100034003c58164402600605061380050400030107010240148410f00c10400180c1c0c0041c1001c142c501000c031300050555500380100e15005103980060b41003180042c468904040d0074801444440040d10180040320102d446801c0d24821040c4000e01c05c200c80408600142d02508665000360001301203d082c101c043d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 651696205 1250 651694955 651694957
    0x2040e010612050f01081f0e0d02100b0406030209040b130804081b030601080d12021b0304060f0801030b1513050c040e130b0c0f1c02120a0b031b030102070206 70
    0x40080460015840741003940907600503290f204e0b0b43c03580101000e501d80040390355101c1c0848403109040c48604000e80b203400380e40e40011000c005580440e94240076000001c4d441c9c4108a042001142c208103030b000d05410b0034000c800450354040d010030207503904d64841518040d4041c0540301400190f907030b03010229603240d004c0c0014006842c080c2c004485a01802605c40e500d65003514000e41003400104000100032406e0740760361403681803848000722510104002403040586404521403c0200d50914000000c050025a402515079428064500708242c0c0c907a0024480280a0f181c001d00160840255600040d00ca0f40c0140040c001550507100fa842030350411103004841107404181000404130041207039402200084145402c40903944441d41550001000c4010503400080c2d022400e81031f500c103d0b04081074506020580720801000d081c0a9404240c1816440000c080428031150300da00c100c41d07e1410060003001440701a002c45110581000315040d0325550a01c03c803000f60301c03450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 651697455 1250 651696205 651696209
    0xc0c04020304030504143102040503010c050901120213050114070f0303200f030c091503010905040b070f0f030b131a0901060f08150a09090501290604051302040e01 72
    0x34944c81c4c2c485090000f8004114000382c2414400c0189142d40c4180d409502c0c0d9243c2024007130014050110068505038000e071143d68441d0f40c01d50300e40f01c922031189070300201504401000b6604c3e40310028451601c3c0d0f05900862440032501103420300e04200ca5805050350442090040e94503c0c28117115448081c4100040c007800d40119444601c551008211304d0070f14620402800784407400c1c111551044102800020000f02203100001220500c41d500e0303c28140f20b940c2c00c64846a60f030341c2c5500200010f09400d03241140c00344084400302e20628080d4240548158440d503682c1e04092550000300d0107050621401500412a01010f441704203480c003515207201d09600300c5400445815013400f0b901e1505900c44410413150482808c5680d602800d2950820800c801c0c40b402c110210000800105042d8045000300b4074007c40b10341000010740190340300502d1f0001500d940380d407040001c08440b08501d1569880142000140460303d8840300c1400c08000d030950050400d621440e009410480030303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 651698705 1250 651697455 651697457
    0x70b060d021f0f030c090303020327120f01140f07080709210510020a08010902090103140f09060114011710030602131a130608040311010f0b03070b030f07050c0c0402030403 76
    0x164243e10151a018007522884034910300d0040388891458500a40341d020700d22a01120082c903203024008010110351000c3c0c0c7c14401484841400e540d000c3d16551b07801400f45280c215420320003860520401c89884c3c0c0d210364910440d0740c06958030f0b40412a480c2c3c03401041e10b003d20440c02008281d200404030881c0139a002e80c1c0b40c140e0b0910684c2401460010b00700d82c07104c002c3d07004100302d41a01e940012680d04441c140c10015894403d06030041e00904050701440680024500801c140d502c41880703036038003a200440507210f41c1d98039100040035000701ca14495000c40d05c0690880c8a002d00c0d190002da2111a110f04003026035100d98544050764425039008200c030040c071109000441c0441d613200d00700400c81e0b281c9458001290f00d140a1143c482c41401c0500c10410005400d05010748412401080601c00070001002003050040040c07814484890280c4582e80001c100c1c1c042900880b4012454903040e421580c6e00d0f00320031a110380c03100c0714616042c01078410300c00c1151914005103000341d2207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 651699955 1250 651698705 651698717
    0x518070c1e0606140d020118080d0305010e07080603030a0f090305071205060708070e0f010e0d0b0901060605071a100b12060f0d0f1214030a1406010203070b060d021f 73
    0x807074180350702035030181e404c40060700025000c0448a69104004541550390a003803004800b000140507070b80002c61648115450700896400e0b00e0b015a25900450684040c2c44403040b6644680740c088079071010445446070143d20410009114a00580d140c0e5210390303251801d000c8840e00c0b0741d1894140060b0384d11200845400c6458070007000010b106446e841700951400074410301e000c800c0103000380e01c0c900216015a44512010080364810801a00e01d044040d010940c0c4102c24a818105204101c0c0c480c5400e500e0541c0100d62280b040f001c0750a034a8001e030340c2a1003480c0c0c00d204e0031484e0fa006484481c0e02800c0038400152151070f01c7c040c20304445018000c0c1403070305d401403d0050050035580340b00d1142d00000e120b0000528006089682c030b0b42c00544100c001414900c09549030b082006003410200400f0081110011a80e00a115103d5001e070204902d61285001a40c0d01e014654000300700349400400100c0e00d04090b000c60f5a2240014404d001081034445000c048103850304984002800d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 651701205 1250 651699955 651700013
    0xc07050312092b0609110904050d0206010f060c02060d0204030212030703180b12091e100c0302030609130204140403200304060e19090e0a0b010806010518070c 70
    0xf400b0b9207891110b80d0ba1010101d11002c220b0540c9103044480d000041c40140c3e501000800d00c03000c146001000310b8007500c6141d450509007846580c800d01242003000510403080082082e09000101c64111001c0b0384564424a009c0c0d801c01ca0260050b031001c41c0841e83c00e020000141e91030240b885000e900e85005141d07145800d0400a08105592454125002d1520020080c041c01e180889908480140d210100b41d11015030050620507025106403903840c0300e100128001e040840c8210b1403948960b0200318040c01d128040c5c0903800101d81c00ba03480020b02c80092441a0445880c88036144000d20008440c803495074885004801a01c00740c2c00549902184690350070f40c1500090b01e610380300019030405144c030b04024560051182e00d01d0091400240204131450121100409040d81070414014003080c1c04100d9917602d107558069562003d91070000421041c04107000303050f900080d0030407183c4584a1006041020040d00c2e860412907290304000c007103a1040d08090000e40680d0141078518 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 651702455 1250 651701205 651701209
    0x50903070f140d0905010c081b070e1603020412060903030905030f040801050f010803040623030f0105030613020f10140a020c090a06080601030807111e010e191202030f010c08040303060902160201050c0705031209 93
    0x308030708cd060418148100310a002c1792340c2d010340b01c00d500c0381d2040e00420014620316080740a0800410010f000d4403002c1a25413030142010043c1c13060300d00d010000c01141c1d491503180c5410b60000c0c8511025604100300900c401032107050307121081850250500c060116080b103000e500ea104032144210441000e00603c038600e002e1202c550410680d0300d0b41290f0840c01d40028040e10024280c06218bc1c0c0b00828a0000ca40241c000c00c003001c5c000501244c4802984002035150020a0111445507000c5400240080fa15104a03001d6404201c000d1100343c0c00d507a80c07407000740c0c00240191102c8c0d04040b98074180e90303102c12054490101c0c2c3c26400480c80a0b0700000360402265204a5110b510406051a48482aa24903078120307007138842c88802082c46400400c0c2843e8045464a08a5080111503200300c0d0308003880c540500d10940d8100300c0c550307032441000201e0007078200c450400309101c801c4102542c801c0006d44ac41e500c803207041d21910b5541c1c0c00000c0ca41190040e22040c0c00c280070a1002d414 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 651703705 1250 651702455 651702481
    0x8030c0c0609150109230a06050915030114090307120c0f03110706030204120b06011806030e0d03020f09041505030a031d031609050903070f140d0905010c081b070e 72
    0x1040f203c142401b52071403058003000300c28510010000310180784c0c0c0000d1104410340e00814010003014003202031900b044541c000034583c1c41c0388454004d6007011100c2e43e05019054a041c8250501b02c00f8600f01601c07640e032100c00b0301c1050700840410100c8601000407540e22030005103003500c82d440c0c40070004016034a003801c10405500030703014980706000400c1046004188081c807039034420403110550740d40c0c100690b210201041d03044083c41d0100400301c0c229070194420107000ca4a04116a03054003400d02c11416440344000e0350800040a101079a4241095000880601240540c0c5005207032180b011130701d4a00402c40944c009a2040e00080c801081002003019844058021f401c0c1c41c090003002e4000f00f542449190700555480d000140d5025042c4140d51400780e0001d814040d80e1214244010049039900f0449424005d000c0c1070310380383d401070404104544068441100843d0f080d2242106500b055482a80260310030040801c130407014003c1c0f101821881181c203203281030170104040300c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 651704955 1250 651703705 651703709
    0x3060b0316031a010e010c051912030501050316151707021b0a0f0612062105061807060e030f07060504180204050303270909250b040308030c0c06091501 67
    0x242903d4085034606070390b881110301d0000d100078281070030b500415180262401024141da20103000d5032103081c004100352409002c035220b20a0340c2c00c0c00617988030303010980c4070007289500140185089404109c3c0c515120000070b9050780038101812144c00421400c001450100c07110401600841c1c10010181c00d100e103410110340d8161607001506e42400a08000745100d405180107001c001c00c451800c0e142140c0006025101061210b951140c0e0711282c00d00d4000c01c40006c840340c0c01a07400050b01d10325080600f24001c0d14070001070401a142200c1510080c1524078007070b80602404800b442e210904006c41e50060040c0c0d520166101d05c0e01000e10102c03140c45030030001c803d004102c2045255400401d0b2411005e07201540241d19003804001c17000310100703000c99500400c800c400c1100c2d03c04d0114203c00e400082c40802070311001c1801c1fa40032620b54038012011041000e00092000c01c2121000d10b03030184800c01002e01c0c3c04000548a41390606c00c07142c8020903440000d0030f040d10b40c0a05490342c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 651706205 1250 651704955 651704981
    0x909110d21080c032e0803120f100308090301020d0e15100f060318060c03060906050f030601030b130f0c1a09130e03160f12020d08070e0103060b031603 67
    0xb0140c2058845800741e0310000d0071168445099142c04074a80d0411170081c0c1c0d4586100d101400c8440c0c0d034201280c0c031398103d0752340135150805490000c2d031a0200b101c5840d00ca10700080044103040e003195100d0706150801150b89405640c05d029108118242e845040a041c2241b4014004500c1e030031f0049003485001450300309d58100d09001040707981802e02c240829901141404600d82001121101d2100c6444030081d01031401c0c02d62200169400d640040c0a64000e40d0060045540b0340082c0141078900b4a21560154450300041000c141c100300c0705900302c900fa5206801c84411078a82442494602e08241d84240c49440d0400094402c1d02c20129401c0b88e18811508040c40d00000034a02401c2c1184002119120021a0842202030086a80c070000c4d6000b0740e00405150709020b0110175042e1812505520700440c02a00103000043c1b54100003c25641c200c126a1102d8049503251004203206042c5604d88002050050407240611f10410002185500f00070214100800f44c64540744028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 651707455 1250 651706205 651706217
    0x10210e01060e1308030a0c0513141219020f040b100801090f1a06090409080c010c14040305120d09020603040803040506070c0809040c051308031b0105060a0909110d21 73
    0x4000650a13a0503a98030541c140b400040552042e80280d649109414044c00761880401000c54100120031400503243c1085d240720080044403518103540d0450284d0407000c503409404030724014030341600c0c3c400c45010013400103e0100c0340b260108003078000034011580400c00d500018072807006181b19069003000b8420b418082d20140d400712000c01112010303006d0082400240c60306c03198030303a500103154680d4030442c031759a552002d03004640205000152340700001c4803070524044181010b4256019030742c010018012040702d4180c0c0c505298090700910591540b02c0504102580d941c40146104a0107008601c1d03a0b45072503e05542071080040a81081c0a2407001d00d44c0071800764815544508010b0b40c001506a500817402c1d03842e03002e20b4841e0192810010004120b600c0040042e004030310640ca880700004114a01d11400da44046804a4100002490400002000c3c0e040401d90764001e003800c2c8210070b500004100c83c0e00d284a0117840d0042c0068203141c07160050b40a02e0f0a0204a142c19 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 651708705 1250 651707455 651707491
    0x20a051902010206150f040c020a0f2001020102040b0901050a0216060207050913050c09130605150a0e0f13030e06070c030c1a0708071e03020604060506090610210e01060e 75
    0x101c20000d0b40708950f010b17543d188e90b5444414001c0003e2105150020040401c2142e60f18094503d0520525601d07541030001640301c1880d4014002e40d811b80b400307803c0d0307541440e52900044030307035410a00f28002144107004200c542d211079484108050040b0360301401010707081100307003c0c1511002e08181c00183c440d40044010980c04100c2c00480d400458042565888039102c0d012207940b8008042c00e45440c100500035002c81804204465803c196203088910f90f0300d00221288040c11100c5441c01d4074070200090010940d2402e00000d05d03c02d0a121010601c130340045541900424000c48140721905418000e02005e1040c09000701800b0713144040b1041c0712480b00010380038284000340b0b180008203121040121150b50310000f00011030051480c0c0717a807410000d41c0d42000352400d80701070b4507100101f0b10301c0c20203203070300c0e44a45c02c00346c49905205010301c011118060210400181442c000304a001c1c0d44409014079017441901030300124100781090851003040382d0250282c00341c070307801d4580 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 651709955 1250 651708705 651708709
    0xe010e060306130b100206250c0305031f120c05090c071e170703120501060801030f170a03020c01050112020f060d090609210206070519020a05190201020615 69
    0x1101d5110005a4495250710703a0f20003480c0c094500800711550000032000741d40031496001600905c98080c1401c00c0c415000d40201d044082a0f1642034100000c03031301258080400e00807402180c21288015101c200084020201c11000805805c044102c1100320412428050f180f4150b40240c141202d0541c86400d117038903c91018420858000d03c00300c62410b01110040b240c48204a4039904030503080c01a2110494421659010300000ca022a8144040c0c00340c0c003000388102e40c145ca1050712075025036400c545034070203076200c600000c03241c000340044800f582c00d050340003404d03001c520350b01c026823100700b400f5901d801d544058203c2c09403103103200800e10150756003001d5041c103524280c605640c0c03200c072648034001414507050054021800c1075078400c1048241c0440039202044041c2c804144500c8900032611a00190b840c1400514140b003801204d50b4083da002000b0700c007034011101e03142c101d80d82d40c80c00c0031041840b040f02003000755011410355806001d110f034441c20000c0c1d5200302c0502440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 651711205 1250 651709955 651709957
    0x52a10090806091b010c0f0602030a06170304030f0b220c080d1b0210020a050604030503012112050d0b0310050702070f06020a0f0303060b03150f1203031f0b0c06070e010e06 76
    0x4d045040005000c1401e0501010051400d100f44d04208159032303925007581c0b0180500302500c10500c84141c013501c480c00c0c1940c00710a44003529070004100c0c01030150794568001ca0040502407030000b00320b40c481100081900d0b100018400c0c440c4400f00c100074034250000d82081c81d50b0590380b05001a40301c405d114081281c1c0c2042c030f6168110f4880340404a202c10491905400d55001026446080144824190041c01941c125224000c01c0c141c00d510000d484003c154400c540107010f246000a8901c4c801d010380040e1404240301800003612410b060006413800c0a111001e450f80f80d5100d050024499040c00030102070005100e080340e00c41d00c0c0c4800259682c400f500f02a100045a1001c042010310176084032000381401c1d103004e0b490781002c020070b8078801c400b0f0385030710b00c66120307040780c0c41a03420700c40481d024296011003d1811607a4411320264110600701c40b0035409001440042129881c840c0985040c2003100001c0c1a50300e080e1401a110300182d01c0a141402260b44c1444c41c5680c81d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 651712455 1250 651711205 651711253
    0x5060102010b1f09030b0906250c02090a020c03040b090405010e0702070e1b03091506030606010903020913080c0d2318031f02070302010b0d052a1009080609 69
    0x2030b071100f44200e10040304554610564100500b40c0300703604103000c00300900150f090300501c1d143c0304000301d14448690070900500c1a060190101d5a0041501b015180c0581410350145482001600d4082c0c038444582c1554400c0d000300581c0380011905018604051107610702500740300c0c512003850309108002a45e40c010502c01d420f40c0003800d500003074018800c48034812510300e403513400036200d090183d2040c0c0c617915a10031b100495104103000400503e00056094040c80068480c032070703450f0550f000d10802100c000c00e044400d0100e210740e240000c0d0500c004005030b01501000e030581d1703035000308010220b01c0c09111440c0030001c2485040c2e000684d003011541101c622035888042d490000c004a400c2680c81c2d42161200500303800c540170341519139002465060301c254000c00c030451030340c0c04225941c03510400c05801580008090003090a407411258042d0f10b820102e00607a00388100010403101000701c8400000744585001c22032031a0800c03490b50005070490260480c0c05006500b03c3c407680c410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 651713705 1250 651712455 651712489
    0x306010e0a0e07182d02070305070b070504050306010b071101030222031b06050c120a090b030c0406030e0303063001020f040e1e07031d0604030309020405060102010b 73
    0x2000800c0d2180040d038441c1c01d03851845019100c03843d07900c02c040030801244111116a80b8240304801014681c0d05d042d03203082191800001c400402d0410011000f90805102142400010030684005c9004184824881e003d07960b0b44541d104e0800303080c141410300603800315560a506124080000c2c0203524918140f01c0d0a1a0058987c00707052044040c0516210145035000c03180b03840441880b200001c400f800480e100c1042136480e5940310221031502c580e000441c8280c002d12180b2001700c0c0588000d0440c01000c5c40c0031320046495007924483e0340d100340da0032044460300040403c5101e40501403403d444080c00040c50461801d80c2c0410f0149461802122009440d444070b2250111064040800720003004000c6403039002400e20640c165000313010b60410050705000041d0a1302180045120841555040880d5525501002d4020308039200030540c56180841c404091880c04000c0c091085000703540100348510706005000407514051700751811a410071000103490786414201c0c000460b01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 651714955 1250 651713705 651713729
    0x10b010c11043801020d0216120c1809030905062d040909050604021212040e063c01110309010c0f12080708070801061b1103012c010b030601 62
    0x42d02d503d911036001101552081c03e10103040c07a820b89004a120b4000e44542078080b14000c4880300c074107036076841a4140e94104401c03110000d00c14010925007611804c1e20418a000c0526100da405039400da810083c1c18500c1555400f5110605500c504110f0040c281035541a180c45c9025501550401800da030b564408440c1500c1001d1100301102258000e0101c070408000c400003a10301907840e0b080c240ea090307115030741410603040c80510119089041e0403480842e1850a45800102490b002c4014025a4040b1440003595080d0402100c10303002490011905214000501160185412011101410000765501022a0010000480342c45660900b0700001201107403410020741c81e4006401400da0380881c0401e120943c201000030b004022036142d07003505540700324007121120707824400c60b80082c0c89100c04076891001200340c80800d6000c0c0d030181c8410b2180344042401c4d20760032030390000c65040ea621840d40c62020307500314240600c590380080c401c09405400080c1d0310344042c040c0b0110142 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 651716205 1250 651714955 651714971
    0x4020912030f04051503060117040f0813060f0c03050906130b0f040e0c03060f010305070519020f19050d030522050618030a17060607150e010b010c1104 67
    0xd24520101509032249046039542c4544050100042c1c11a200d064050808840200007000d00e0390b007641e205090680d92840030783c1c101c80c130102503c003005d00240c8810a89402c240080355108008103188040705030207012030380c0740c823000500024441491f00100b01000c2c0c800c41c0001c0d4404200c69607a0f504803111503d0310f00c0081c4542c844440e650091003883d41c005040314452100c4400b500450b488045d54100a0340d40c2414111140700c03c0315030b2a40007542c0143c0980c1036009034040c5801c0400c0d454331908150500d034445981c85c00010002e40075900a0040354a840010070010040e00094071102210400565540342ea0304c8604044800349500c5a0022b8510303010f503100691062501e0081d01079100d01420400d0300d03590252000792410070b25040041104400000310b038000086039441168064813100781413158000544010750100c4108010000f01d485000c00c00c00d4042c1420000808107041c0b4440c40c21213691400c2d603410710840200c098040745003c610700e0f88240c0c064078045942a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 651717455 1250 651716205 651716209
    0x9060620150c1809040609020913030905040c120509011a12060c0a052a06010f120609080d140115300f0f0f05060405012d050d14060a0203060906040209 67
    0x80f81c528034850f00003901a04120500c403154102c072007868000c0c0e40076080c5440d92001880c88001030072025010411040b02000706041c40c0d800495484518500001d407016102380807015500182c0354800c19039143ca14080300392841116810007494200c1d03011500d4505580b040d42c0b1800000c01c009548c0c5000306002d5445805501124541a06a1905210041c080c201000c4050b242d0070f242c1068860800003080d51080d04080c00c003681e140c5c4401c60200c1000b96100c10203811144022540d01000f031082d442c03010580e00540100406005c0008515070414996403001d400d10711178001000446900224618608003984840c01d50310795001d00b681c03008882445c05000308084240c007652901240c0101010507620510000403564400e10a54566804202c26a2800e0054001c40d0303403514460041c41d0f0340180b06e0301e032402184001c13400c20380da41d90004290620f01182625032507000c0d0101c840b01d400600c000c42d80200d00043c11411420401d02241c0301240041c0414000c96000400380810303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 651718705 1250 651717455 651717487
    0x2181b16020405270715020d0c0b060102160f05010e092e031b0e1e01060e0103060f0324060e040b0702010905010e0106150504050f0103051009060620150c 68
    0x1314a0780c10189641d121040c803035a40d40110b0705c42d002d400000b60300c2003400c20f440428015000e04403a076a54007013220940b140b5060308030142c022030540c4601c00103640042c244100020050101c06820042d2a10701030016060011106200344541c00210402c041c8a0003c2c40d00304005601e41c918000402008003140d44a40c50350b00040c081c400f0382c1c1c000748480340e034445284003501d0440541c12201c0e1600c0d021080001000c05614510100030dc0060000604c149650003020405142c0419150b580c1c80c0680c00c034483c15003003075410360f5030145440e00071052040042c4044480d000308200c0107241903a0541c8844010340001c181105920104200d14400d400485c40e03207401000802800d40c0f28100a030091080d88a20303410304902e50340c0d2400b21030064040d20110344014060800304200c85004500520780200b100c40e61340380380000402c00c1d54030b030320442c005401103032038580380111500c401641d0b240b09500a00902d034050304040c80c4031001e1081d03503034010850f071440303a0703c4000d40d200100072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 651719955 1250 651718705 651718741
    0x10510120215070507030c0605090a0603020a050f0d0204060f180b0f09060c0a150e1002030403020a081903110c03070308101502070f080712110d02181b16020405 71
    0x740030782c0498000b052002c04904102142e10580e02a00304580d98201500c40c1d01030071101c05e5110081030810050b50380aa0003c00c01ea82c1300d0b02d400303071501240328140e6040c4e4006a070b00951540d80402c00b07000450300b0118002c3c48404600380707044001190341c4405525851802403054402c2d0126882c0200e503100801e585011000511454840e0051000981d03200c464650079620700400314005100c00b821840341c540480d0014000c4d100050105003824007a600142045045100d821490b00119500d00003070501041a419802030300701070024024203540b440700c0706c503220150800509003c050700002315001150305040a103e141c1d50341400b1840b40c41c4c1d0f5031080c1041d03030491504c9040241c3c0032440c4030581381e0070381e0005903072500c4210980d50f490345801080c8410740b44401c0280401d801da4103210500000030601c82030703100349074041030459440c801001c180c0080002807000308030b94004205410300710403044504005440e0249600d401c40e018000c0d0040d99a080840c5601d00f502c254550 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 651721205 1250 651719955 651719989
    0x90f0f01150f080712060f020d02031e07020703111305010e0f070528091701090318050918010f060b0306010e010201050610230414010909050603030405131b050406030605030105101202 81
    0x342710022220075001030b500c02c5a41580700c18035007840d44000401c0200c0240141c6c05136004001803400e580c0c540d500170b900b40f101103600003e03100d0b1140305583c8900419018002d40c0c9060382d40d1341002008050b41d01d200ac0c03c040203100051080a00a880082c020b41444d0b01c1c0e01c880c2c5281d0303142100b007a24040341e00e03088121483c20b540d1100030300400540215140c688250303158030aa490a105891904081c0e0007803d91001d41000465090003081c22040c502c8008003000050703205102e0004002c4400d194081840c106000c41000340941c0c0000c08d11107400820f00003031141e85032040001c0c9800c030401455500703100607500030000c120b419412001ca000505280a81d0b1a6110141c40783c101052000d03507800030b0154200424517103154000c0c180100e402500441c00d0a08040c1000201c41a80c49221340260b03a03036042e41c103c84e4031725489041c00926512455078903070038413a0040943e407a80d04a24020703030420f0240b044052580024a0454141012984020203113100050741d401e84806014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 651722455 1250 651721205 651721207
    0x1c140307030e0715090504050610110f01090c03110603091c0c050123061801050f040b0d030801090608191e17031909020315090f0f01150f080712060f02 67
    0x104803990b400001813000c0600707848065079242d03540100019100c7c100e68468000566115101c82140101d0b00341117050300d50303000d89914285803485c00e0300316181990192000880c03d10108140810181604150502505e04619514100300341301da0b42c9185103202d00142c17030412040038101d4414050000a15440030007486807285c000d11000d10b1714509e51a03441e900e0a80d80c00300e141e51424801c84005040005150b4403da880c2400b041041d40004081c55001a26030310b0212160f555074105020b0988a42c035400c103079505025240b030031580980c01c910103a03400b40c1d807013402184240071100495035000f050815200d61505c0d011061198403803005160301030100c811982d0314001e8019510404910360781504044a07604800e06444910b10085d4040d0000d2400360b01c009528071a8030f900c00780110454208420440a0303e203082e034540440c8986035034130000100d442550202e40c0e4014480c020041e018982440201a25642c040c802e0003480c141c042041000c000369a0013251038014906821 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 651723705 1250 651722455 651722459
    0x20c060a080114191802070210200106140d02060d02030106051b060c03041e1211010513080a08190f0f15240519030c021c140307030e07 60
    0x34101c1c903002c0c0103414030b100e4101900001400c01c100060091040440920141c515106042041c0c4001011503005150204240d07405604c540100076160711f419036829080b20010101d10001072650360924202c0d0341041c2c0200a40d0011482418030703110b04490b415103100da640300082c098419603480304411030000c40000380305a0448040c02411455001c5e190a0180c0f03034085a489000881e080140c0e96424004140400c079060800b040900502c0c00c0c00f00c1103070304c544907004c1c0b00c01e40c01c003c070b8006000c2c500d8401c1a0070003070188135000042c0340d0484072541070640d6240b0003801402c80d00400c000c881c030005a860840f075080c10300d82c406082c408108007400c0f480c1c010017802d02102100913407030601a001c0084c00016440070115920b0680820b140d0030025420400c00900d460312000700f10080c41001c0e03000500c05a0304c0f02206440e01c00090f0010368200107420959400e40c0c03020101840c5da5105e0340d481c1c10541a00701e466505003101c0d901c0d070360410140c1c0107002894200d81d99200c1c680c80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 651724955 1250 651723705 651723707
    0x603100c0315060c17071502071112101a03070e060a120302031908070804020f04020906041707060906020c0904062a03060b0f0d0509190b0123010c030f020c060a 71
    0x98141a41c01821444405d030b40445d00c0c40c005204980c40100340d9104402c0107206040740360701a0410a1003010356184240314200090003000510103510781c1900984040340c400c81007803240d58040d2901911010301e6403a0000040d881340107038412841c550030100006103075540e030040c000c0c1c043c0c5101120304881250031300b0000d580b80c0100b40341c004420300707001010510038000c002d0729115200e107a03a840c04903502c5509101c80b500c070011110740c01c41e07003d2083c41510796890024101030841000740718400344001021524003030481e4444024801c580303600340107040e400700d039180f01502c081d90140320945952070300800402072994006d200c10aa6060b182c1a240c00852010074440791365002d100d002d80f56581400d45105a8410801203001000340300c4082c03410b504840c1c1d00c01003000545185000c52928080321041c1844111000544000103000c2000c0000b41c103409225000c42402c8841c1c44070b070018081008011006d03041c0400d41c0b442203140f6208001c21090804e002d413002e5101c041d2688 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 651726205 1250 651724955 651724967
    0x2d0703020c040506010c0b060d0203010f111809101a07020a0320030607092c011502010c0f0804110d081903051602030f0a02030409020f0309150603100c031506 70
    0x1d0400d00c0b0300e00306404070b0b20541c4502c01c01080c285c0c0000044081da00d8038002c110782c500c00080c04a070555218516041c3d034011520501811140d000b1079599104180500844000041c0c508203118032049d101380100c0100d4034042505844d400000074800180f0365840d0703551b80c09680f00003540010482c40102c2000420b1440d04103c6c101415940e640300e0130300c810940c94040480c1c06200043e0340030020040c007540c00c03403e00c4a4664010414034040d0440e8040341d002c01013600000c00c0b1a250390550300e502582407244c14103034412403410f11400120144014038254001c0d00144c4404650754124543e607a8400204054a42c81445c4aa40e441184003038903030603008030102400b027841c1100107001c1d90b050840e01801e41d0b100c2da010714a045a40843d81c0300e550858082d0100310301c000e0101103294000d03440203122804208071a640c0300d14100d81c00303926091428000d0949075041c1000d000c01030714002603424458109001c0420892100da000303c0041ca41a200e1403400350100e80b00140300b039000b00d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 651727455 1250 651726205 651726223
    0xf0909030305150f060702010c290f01060203031b0d050403120b0342010909170a02071802070f0b09060606071203050402010905090f1602070b2d070302 67
    0x107141401103030740e58828a0100b90110600b940c00101d101d06a60203840e10b41c0040844601c1410b049d0091a100d4481148035a21080c0d51a6906018000c030840c00c000c007000e040d8420b121074069449581001c2d4020740740d00020302000310144c2a000015481d060f80300960710305c0140000f08020300e20b05824001d000800c07c0a407144880e03d89072200f1181d050104483d80c082c10502681c2000c00180f52408130040c01c1c000e451f00180c1042c010f040217000880a90354024000c02401160b19002030a0151710504801c5000000c075504000303800302e05401042502c1106c9009144214004903000b84002034428010028140c8032128415020461548507003401000c401003120746543e500c1c0288422441500409440c0c000000c40e072581c21071190700420f0b800352061400400c2c01d42e8460104440030f00c1610324a86070f0b01030030108407004680c160301a036850090701c014480c5519004004900d40f1803441a40c552090502942c0d80b802e43c1c1d010f0468040300e24600503680c450712410029260283c04d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 651728705 1250 651727455 651727457
    0x830010519030b0f0411030a080d0b010e1309060204090f1d0a020d081e0d0e120301052b0c060801030c0b0301050a050418021f110601080c0d0c0f090903 67
    0x450040420703200349490400580b640105820400d03101c1003e204581c101c001d004582039403100703040021a490901c0b62a02c007920035200a0349070840110070500b03070750304c052419040254402c6001000e40e00c5048901c1d8020a008000851844505141010348103541040d0005410100e0852483c81541d2010045e071404211308182c420403512129198451100060b40c09090721200c3c4010807010001444450740c0c03140c2c02d851030300480700620996005500e506142c15600c8446542600040c001303124081c0148091a14560400d0001900d901d81c01240704141400040f6039080d00c4c0181d8002c2c0c940d03030f40124640500c9076031200000c0482c10309000c112218010071400042040c40c031400d50b41a148001d00034003600e0701300818480201041c0b0860414040c50b00410405600e86c504286a424418080f880301c01030510000f500240786500d4454081c2d0002d0010003004001003155111143e0850701900c1e49842c40c01e04034503402c842c7d080009211200440003c44401e10b9019101007442 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 651729955 1250 651728705 651728719
    0x608010c0e0a0801020f0417072c060102060403140c0f15190501061b030e0a080c21030702040b061e040e060303070507050f040204170c04151208300105 67
    0x356034640d405c0c4e00404650290854046c0000d10003200c1c00e01c000c0c49049400c4080390901c40d59202040141810300c0d89468521101e0464008484140035405610401c01e00003850981800d58001b081d21040c48450100d01c0030210307680c0e80040081c8403402c090120703c02160a01142003c0204160300180d070088025911220a00600748190007030604a83e5517440c2c2520050440008180910300b1b48030450400140c0203070380083d6a150556070b40504400002002d80e112004107116019101d221015a0f00000405503507c0380340001c1240c104590590303021501d2413102c00803d540d401204003121815035500d905801c03959814025101302d4000603074a90fa81d40300d51042c56143d1007107800c0134201d5008001d06015508090201d4810003030b01910040c5065640c0c0d23001c1c9038070700640e000308000b500401080f240b40d01e400e0048501140d8640120005540340030120685031100c400000e00c0020003182e42920603220960110a0080b42c5100c40e20030401100841e0142409026462140f55 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 651731205 1250 651729955 651729959
    0x10060312090e090d080703060e1302120703170c0f06090105090c0f10031d1e2404140c04050405010c090801050907060503060f1906090902090916030608010c0e0a 71
    0x402c01d0720940150b494101a060940031603400700c40d154002004101450303111100000e400c4018003240d480303803092a13070000c04002a481002410681810004101d0b40000e90500c0030450031014060409820701d04603942d00c07041c00545040c004071100900c06400740c0f40c10170000d51010f4114a05c616030302d80c1501c414118000c200203002d41d00410b402c2e0490300f600129150b00d0301a1740b00701d107060b0490454000300000c4400301e40c9080c90000e5203541e90482c010000c855042c081100021407550800301c07a50804010500f10090200180054182d403261407091030940703002c2c01441110000680280502d01d03003801c0c903d002c0d1210200e01800182081c81c0017900c01c4045c803540340a40f00a00240c0300f2246066021900b41d04003400d0254440c0c0b400c034407681169140708241400300c551181c05180c2528050001c0d0020580f540801c0600740104184d840a07981d284e0b04943c4085400209802c1c0307000448210000d1016401174a4150b10701001703041c205030400503003d01c0120440703150131865 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 651732455 1250 651731205 651731219
    0x7021323220b060301090b0705041d15010c0f020405100503100c0504170f0d02160602030a020304031509020a141e180c0d110301030c0e041104020c1006031209 70
    0x2181c44009850010001072038800070b128485030542000004002080a640b01d0b1107009880c0002d17650100032036000142004220088001c0b0001846101d4501c4951303e0f1041d102214204c860b07102a041203d41c100c03c02c02c0150010203140300d150080d000f0003040c81e101965543c509691700541d80300b8441c1880b8426011414041c05102c80740c107942e000c3c14545800802d020094030002e085403103004420150080080411040f8506019a401031106500040c1001c0345c1d800c4580003d03045400800c03505d400749030000304a6048a41c000c00c60f00000740e0000a020003411141002580405e0810340010350748403190034840040f03401c403401100d1111061002102d50049590540c0201c3c0316803152001c0030700000032a50001e20324446915091414500400701d0b10341c18441403040c80d02000601c24001e956803008080c1c5041c007494041030810b034545004c2003540f0f54404ac8103907000250091031003024407640840811641e414400c0f10b84030b103410043c000003901c0d488005030303908100050784 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 651733705 1250 651732455 651732481
    0xc0f1014040f0602160503180405070f020a0318090e06040c0f0302090123060d1509021219060f0306021c1103041403070f11010f0e01050a0507021323 66
    0x74580c04004000322440030750b01c80019401c00e02249240741d43c92020540414828802040c1c60007244001802d411040c40401040350000b804c440d04019980d00b5512109800003500c40d102d5815003803040d00b4025203040300c0310040850300131514003402c0402e084082c050000b400303400703148503241c807041d13550311030805076116a26840040d51000244004202c076440310000c41064501c07005105c03900118101c0460341c0345d48a00703811200e040d900d5101c0a05002082c03808009405904403e61400440403005003414101504401c2c0c0500301c01d44000c6c240846901c0a0018420f4507124a00140c1e40d0034042d000350050a01c0d104101a195070441c120010b511034016507560040026046443d2510b03440383c03119252100110611041120f800400e2414484020b400c0c491444540f1200452000401180c403404c0c0b07600502038011001c10060ba04a425144000210302e0200d07160b401c2400059984c0b100050301400c80e0745894003d2210001070303419824041c10301c02e07083d0542d4440c441c1e44042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 651734955 1250 651733705 651733711
    0xa081f020a020d12020d050108101a060d0e0c040608070e010b040e010303050d0f0f021c0501050906191508011e0b0702010e030319020d0f02150f0c0c0f1014 69
    0x580215031032860309805400007500500d09004c1c014109040803843e4030842c0c3c400e8102c03842e00c3e8441e1900b522a18070341c1c01201101d103000601b20307180f0380e10300003c550307140210024910510344544c880054440108698400b25a005205006e00d1383da880203942c550480d401014503c0400c1000421a007400804540c2102c03d180324009a40c1c0c0780d07480484a0703822040f41e843c000d545440c5070b0724141081e07000d07102d03249071040401a50f4072603803502d1000c9a840d5140942c0e800c0d050000401aa6981e4252260b02c03040981d58040d4812000c09003580d08a0346400c0541c0403842a0281c08000d07a2007410141643e06501d5003d15608a511076031142e003481d4440e590034a441001000c0040d44210050402160060100c03800c00d10391200311007100042101c0c9000591058140d0010560310514054240c50340d4006011003506220401d11095070003440b90a030b8280c10008500e040300401d003150a0265450142c541f0a952848250b803614920440e100e106400c002070703d00741e40c00140d44240 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 651736205 1250 651734955 651734957
    0x30e041103070e060403050709111903020a09120b06010f030e010504050d090608040c09020a0504050d030210060b0c060a0923030901021006080318010318031809020423040b0a081f020a 81
    0xc0c8ca40b408040360080c080c0714012210701c0400380300c40c0c03800641a14074200303a207059841c050384034003502000400f800c501da40819501061503480e10f0100381d6100c0728581022081c68001c9159056010a90152101e031b80c0c0b5864540c608400c000a004c800300c0c03003902e00c2d2559074034401151340d501c400b2504170009840107001c1d40442c03001003044948960080034442d00b2818401d0a05070384100043d003000344610240d0141c4c0007851400500b00241c86503c0180c007000d0b2086040c00c108600599481100510092400d90b503649541c0034061242d00c882944d1607400651481490500360154983e0041c40c00c0c40e02610a0040b101c84500d01405560b05441403140254102054400140c10410003c41201d041c1903480c0482d9140f2425114034201150003134407131f1402c2e8264504415015010f9030300c5410810310501003841403000c0381c2c205c8600d411070046200344400300c100000d401805802061075029003800c00000d4080380c00306680d01e10346034006003480d01100001103a401e034451000040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 651737455 1250 651736205 651736213
    0x1060e0c030703051003081b1e030409020d0b0a061d060711010f03061701091b1202010804060e0118020f0d030e010f02010e190b0106020304030816030e041103070e06040305 76
    0x1030090743c400d602c0183e00540c0c0c1040c0b05082503503901c03880441e50000302d80101c40f0103540c0102c84a600d003002640741d68100201e003009070a0010003003640b0b9000c3d0303015200d0601d4000850f06c40f0708bd440d4210440b00e407002016800d01c00e41d56170f80034200710b51108007c5040c40c00380000300c0c141d1404c03d0640c2d1030036421880c80100024401c0046912150028040060581c0ca00380802e0144a402e602d400d0902c406000056807422414107401c54031303881c00d1500c40b03000038200c240100c42009000310b2196a0a00b8882c210752114178105000e02500c00f40c1000c250305c2c1c01c56030a0b4900c0a091502003060080c1c418030352903070714241405030040315003601a0104442c0701c3d940415510030018a400300c480780c8000070300441d0206407a41058401c00400c003504c40c0c1a080c0c00309101c6a03140060041440f0b000070351070175155031b45280990054407402c2615a2480c81081c0074140110009441200000c00411509506501c8450150001d03514900092180203a1081a0501000700c405698100000b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 651738705 1250 651737455 651737461
    0xa03080306010c050106090501060905030a120305070c05030f0711030123191a01271a04030b2a0f16030c0203160e1513050603010225020301060e0c03 66
    0x181405500140615041003002d00c00140829400e00c5181c01604a80c400490036500d4035400410b04911604494401d810441d48400051411414000e02d00c0d601d0a002c11940d03102d40e4251950b0030084009481400300003060310010301700710010004548151a040c09540381d0105140c201c0d640304800b0342c003421050300803003a1110390741c05c05036000707a15070504c40c03080641c6900c4000b51401da004090f40c2191116080c000b56070860b070ac845102c07100380c00c58012007001c0081c0003403a9005200303101090b04075000c1000c0c65041c00c412940a1600303c03041054a060483c13018150b0014500c0c5410440102c8185180e8048107404448a000201a03110b0810501c40c0400103440f411510071418450450359400058506202c10030441e900d0b62a103c01443c50070030200080c20004103031142410b122811500d1581c1c0300049500d4007001004005080d541d48008207009210704203640108006c0d642880e512000400c400440319842a0000d0000c0c9a640344256442c40e01a43e001d210a03900b4000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 651739955 1250 651738705 651738713
    0x61e040609140f010506090606030708040305070501110f0c0c060414212b0c02010c12091e0305070911030f0c12191d1b0a080123070c020a03 62
    0x28800c240a4141008501d0765000700600c0e000003102c0f0b0303205994680d02002194504a11000d5000c54181c901034a03514001d50010300404000704001d003802404506441401000d40c4001d40c2c16030041640c0f075494044010400d5150400c07005410180704d410418829400c00300c05460440707007200803c008101401c420416071800f605000b4030344c0300307282c046500030780001c010343e2900300700460242c0501c0d041c105000070091108140a0b00b88561608000010b0741d11442058480c0c1c0c000507050040c1c00614422101102d01d81e000f48202400301d64039040c1006070840c21402c03640700314111154030303685180c100b06803040f0b50305111000400f8000200201044121a80c1c1302c620207100505d058030070651075000000548040e840f100390781d5500300790340d600c500c65030300b8000030740314206090072528410b50307601c09c0c68a070346040003002d406500015843d06198200035000d140000e100c4030610f2403507000d01d5000c4c4000f151316030540d81c6c003213400103002d011542c05042e006483c4541c80d034110340b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 651741205 1250 651739955 651739961
    0xc030f03052505100e0309040c050d0903030209131401060e1c030207081b0927100b0f22150e04060e33150d0c060e041112151201020a02061e0406 64
    0x4c810090000c2080344604400c480d02c33880d0040340c4240c60043c0c031001000c040c04080184002d014450710301d4108402e01000103000d0300c60440740146445903105002c07402003024a200c0c5008400066209040f045c101500421200705485000c02140c0035882c4001a40130f0240a8141e625001100032001c22400c00300c8220800010582900c00ca0346142c91000282c80c0c0321448a80e2640070307030b65128038032080c9808111484011000c40e40c040202e20b42040381c410f8802070041504500d643e890f600000d142d11030742d4107030080450081c081e03440d02c0c147c1001d801500008a003e50b42d4052001c20414080c038082140141c0654100070310741c3d500d4600c80d4200784110141201c00f0b021b103c07041140c45540d51182c03a0a2a500c0343d20303140da0592070309502503c0d84242a40d910711a43c244034500003980030350016107421006441000e07146407074040e039201071080c00040c01c4e5001501d9500c013171300d007607415001058190703c00c0d0308550265a030000500289052120442ea5000600c0d0129000c41c003160 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 651742455 1250 651741205 651741221
    0x1704050111030115020c1030020a0201020c01061205060a020a09090905030d0606020c0f0d080c12130501020d21112b090c030f03052505100e030904 65
    0x242081d0411942003182c10990112038400c80800300c040000b41e05205203444400c082d51402080c0c81c0000d0701078104403e03590500301c4542c1d148982550a071403650140c203000030460f4210341e13459262000078040c1d8030194024580350300b48040040c2d850507010140c0d607a140c0003005816151035a00c052006588040e842d58104502503e02013102c81c024445d04121520410003584e9070810300d41201c00342c030003d520020a40d00280640e144545412141d10180c010459419001c225039140c041e040740180c5440040904c104104808001c100800904000e01410071242880da1758800480c0c1c2e41c0c44000b2103000150844194420111071078035000c4141c1d1100401140400c41c60141041c55000b54400b02c8041c0c2e00381c0d803c0c0b5841022560400d0300700c400c4140c2031000d00000d0f03d03191003081051000600c40200c2c1406413041c5032058040e18010f4045481e61810720303c1c84c00c2101d00c00042c05c80142c0703080c02550344840c41185c0e01e100702c0c07244800c0704001c0c508141c422010400100010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 651743705 1250 651742455 651742463
    0x110d1b050106080706171008060105040908221707030201020a020402181206150604081e03041a07140c030a1101090f030b161b0609020402040902030906090d0c031704 73
    0x2d0400802e4010050000c8000351030141d9038861079040112880741580c2024020068107000ba40c03040c0222180031a03d641510020b80d008940040c042c5050b0b0018419134a40c1000c2d00c5500c15041c0340c07200303a028983d0444600c94804403040f0580e858403030f10380c00140300081c00740e4449209038005007031540241442250000745a0803201011001c60940300b00d0280d080403d8000504002054501540060301380d03800f601c200742042e081131300c1241e44d8000718420802840c444950040711000400c12903019000180030549000c8ca0321010000340d8002840031038601c1103e460800c042600014811088a002402041c41c1a1300d03454500b00c50201f5210b003410082ca141011400d801410400002148980c540f035229141020410500500d19003004c000c00525202d4441940071580145421030b0f04020001620b008520008000384101da0104c07a01c10300100070000e081e0404a2a24414540030040d80d8442140304400c0f1001000b9800080208010702284070342180110071050f071152003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 651744955 1250 651743705 651743711
    0xc0904060e0105090a0233070611040816270e1c02100b030c01090608060a050a0308030610030506030304060809010e010504142a010e0d02040615110d1b0501 69
    0x40081c85003074490844442c0b949503c140320804c00c40c1400404000c4203c418800300000d207001030b1204044a0340174582101410300820100140300f8194800942030010340742060303449540d10742d01c54880b050607030341c00500010004000342115400d40003440194149800401c600d9003410b55100034001e00c0743c0da0710207104d0291410924560101100e440d400150002c0001002c10302c0750b1025181403019960003034002441c07072981644c00941c540e041c0c400a0602c0c0c1d1903541c40d0070108044544a41c04140c0c002c40f040301c000709114406c0c0086000325420368a20303c0300d0850030720550a80d4816600b00d41c16610811042150a1080038425001042e24001140101207001507a0941d030080d01c042ea00101c0c0c0554000085808001108071004080fa8a080d4000d510a441d940d44030320680f0366041c410300f043d1494159a444904054440e8014020800280c4400600e00d840e400180c00101040c03210000840407000040d030340701000a00c0e59000351804411003040005e1040710b1080b03d8640d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 651746205 1250 651744955 651744971
    0x150509011b03140a090e0a060e1303020a0c120b0703060605041404020702040f0506102a0503070605010b04180216030318060203191a0307170f33090c090406 69
    0x110300e80040c00c450700140d0740c1c04c09050800500140d5030b580500040d50040c40c02004014400700049027030b5106400081e5a5070f0206103060613402c00200c458020401208644003003001d003d400813821019000e000080002d41c1c5502c000d90841340c0301d000345004180e090000f0002850750b42c0c0a003c501c140900b01600f4065203501050a440e801c02c800c031003180e207807810046207090038002148007030344078a0724807171122000b52144220720b0300304500340b02c81004018200c2403050420031a000070f0361140c0200425039446820340c00c43d07002806030994050802c4000c0c402c440d840e00070b4480c09002d45d110704095600320f80c1d040d0028100032105460503040381031040c000c2070091000d184607584001014041c20024000242107620201c049164100709111490b4107840004070042581d5403a844a0400305c103945184e864441d9401034141d5034810509040c02d014030690080022410401c00c011101c145010000c491140c12100305205501000010b000ca180860782d01d6041130143c07500140100d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 651747455 1250 651746205 651746237
    0x180302120c031605030f060f06040504020103091203050103030905030d02122a071e0305030706050c0d06090605030d0320090402040306020c0123010b040302011d040e07150509011b03 80
    0x2a0f16008003050900c26858200414141448001c182c8903411020344400d1502c08c580b010104c0d03024150a005981c4e540009046902941c40414940d821a11864141126400c01005414240401c40000720780000c00982400c00040801400e0000d03006045503c4100c40007540540003040380140690307030240e0b40e4145018605c251101c0b58032442c003824200e8244000a03a003452250307400307442c107803161000700003049021098550859100c04080b4042d220511803944502840c4c3e1555201e504c3c19400180c410044c1e808001200c20590542c2d04003401d28030190211200d0821441514052407001c440458a10000b0410343c0e4004200500700b03522521000103e070804034011203560f54840780407070a505c828602c0c0c844001080380700c40381581400c00e072203004d0181d4403000707041c40140c40d84030b4000b91810302d80f522187c101400401c03039548150602c0b5500e10342c0e485075030119940258541403180c441e0045170000c0c0300c182c42e00c5c0303008440040c0030b889011103040141c2c00c01480414115400b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 651748705 1250 651747455 651747463
    0x3050702190b0a09060c0c09051509160905040504020f091306060b180f15070f05030a021e1527011a040c030501080a03080c300106180302120c03 64
    0xb42c0308401c206611000c10503409410500140c0008050204000d4400c002407060010101a203c0201e80410582c50f91103003881520b030306100c040da1007400c0d0000c224801c19843c40c3d00c2c1d9001d0b402c0c0d0300c580d0000c1d0348005000031141e0036500650006285811250941080b8414580021200e00794170010300b041c0c0c0300d0400b01d5546030071260340284005200701c02504045500c10f1200c07000c40c4c290701c00d8a4607600281000c0419031840340100e20204d2150240296a85114803c1e5001021f0343d1361152245c4001303403503005034401c0d0084207003015014005079200085259141091034000403003500c410001400341520b03d0f1001e031003111540d0715030b04003640c20300558400c2c5030603400c45402803148a0070042a00c010070140000c052800c801006036071800582d80d40e20b0303601400c08e0358080d252070320607007210b1090040151241402001c01d2408034890000c2401080441c400c0101076600c80c51304441c045c442414000c242110740d2010300140c070f0603c1c28039401d415500304851030041503c1c082814 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 651749955 1250 651748705 651748709
    0x50c03040620160b0f19150915081216080d09050a030305041e0b0a0c140708211501030f021324030b0916030b0405251b0305070219 58
    0x1e040f004034184040054107100540c1041035400f08540a02c0d201c00c140a05e00c21864001d811076803145440c82c0c40495000c820703070203480210420f203c84031b000c4548441c030000d43c1c07181201900c50005004480f2544000341d500080f5040d4805107034803510b444c2c140c0b85811001003001000c5d640d18007100083d030100030319640240303c0d40340892a880c06052907034410380b1841d00c82c1341070300b02c0c41019400500981156507010680e90000611000383b0f0604559a203641e500f00310280c8000901c150500001340c018000c0c0e29241c0e4120700703422049900c40300c1c190b8003d9600c8411075405500901c81580203402c0000141c0c0a1800141070080103002016100d030a81c1c4002010488220401e01e150b0a91003046000c0c14581010712840440101041c1400300040440004000194413a000c4500c01e030044005041c00800900043c103050a40d00701e40352103522440d040b0445603c80700002409685200010039000d46810700c03041d40e50318180c0c0c0c41d0380b05034022a4072441c02c804018040600d8548440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 651751205 1250 651749955 651749977
    0xa0b0c06070801052b050c030a08031524090f04020a030b090f0702060402060a0c0b0109270b0712020d060305030307020f012c0f01050412020709050c03040620 70
    0x9504000301d02421040d8180c0200340030341800b0013108070001c40380d030760940c1c204400110780114034250304083e800c14a400503219814001d00407440103014400d0050341c0242110703441015440f4008041064001100401102c0041d11154030401100c500b0043c0c100b0120282072140e101c0102000207049a00107604000825594070746401136040ca82003055000d80c0c58400c1508030308210301c6c065a40c2c2c200510080c411000080d81c41061803140d5a10090345601401000701d40d6100c0f105400500001071110860301255110001c86642c0d4003003840c42d860b00204005d0303158690001c100c46030010408140502c540801008003865924400c3e503000310b0141c00611344900b440d6500034100f001c03080d00201e07980c7c14106000301032a03451840448846903000a44006101c0100b41da06042c525003a41005510b00010002406203414090010a082d60301f510806a02d40c902c02044a005594503500000e0510000c1c00064040e8007020602040d03823265040d42d02c0c0c69041002c140d12040d01c2c58 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 651752455 1250 651751205 651751213
    0x10e03070e16050708030103120c0c06030c0f08101a040806040615080601030506160e1c0b10060503042306010303030e060703140411010e03120705070623090a0b0c 72
    0x4200b1818429505001d5030035803600300e1811000791501c81680c0011300020789024030025461004901841c1540f03d0564403c4503108429030780c1c6805002030015410043c00710741c00c00f80400074940701d0383d13405204602c1c0f901c0e0a50b4590078441c0314080403140c86801452000104408111b5107c1009501d101d01d01c22031020940c034030071007002404a805980807001903030020005000254010810f01da000360f070000c0074160741c040607404540d03000e088103200d0b07002048101310103400c09850182079000c07030041109010b01d071a12450b034000c12030786201d5280000c1082c008100012100c4805642166040c0c0c2056003414280c032119041c80c3e0700703a000700e0229544103429084000188141507115200c0e00b0200030060582c06484a0008000c00061164a02201e5001540c0c01a003010080b0780380a01102d0140b80407614142859001241c155034920541000084191143c0c0010a070360112145c20b0607030903400010005280c10111489920815021001c218095801e0241076510204c00c010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 651753705 1250 651752455 651752461
    0x4060b1612050c030c0304170d020d03051f06032a0f0c05070f0f1706070806010c0204060e011d061023040b0f0405010318020a0506071106190f0215070806010e03070e 73
    0x48c5c0260701c011076110629008a440e42200603008120340303083c105141008100c40c1e480301c52448810009006107150072842900120303c90f50f0540c09941c5c3c1a00c501001120b444200c00300c203c00d403120789240c00000e00c01c039984900c8039200d056030f680c05038441c404880b100394035050003001d83c2d0b203180c00004154501480400450a400410502407200407020305100d0601035001407a4010080509060148802d03000742117440e40da122000030710315018403482c0d5503181d80031303502c40640740c9040c0007040c6203820102c6d00500e44030003c100021401d480d004400344103408000c00c81d00901c00d5581c6001d40c180b100003858603000b001451110100403081b0794490900001400b100c8680710b01b48400c40941c40a400180c075511200c40540d4822101291900760a242a03032500800d410f0b200e4018030b0228248010343c0b105500d081c048140754413101e030307003000f07a2008030b0b918450303070410601c1d203048000440c1d81e141c06981019040034040c507049410510000100380750458585c000070850a01e5010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 651754955 1250 651753705 651753719
    0x608060604050f15190e0f1b090402030711010509060a14060901120201120606090e090c0108180307060f0506030c09070e010815030d080403031505011709160b0904060b1612050c030c0304 82
    0x642340d0000048040f43d881e00e580a00101c3e1500900103142d02690340003001c01c81d1140103c8500c8050701901d0000d000f1483c00058040d140d8070243d40c44080325040000e9003a05017031041d422417003050302500c4104a6840c10b22140300e404034040099040c40900060004007071000d018050107000d00c0c0e110080d180c0d140058440c50503600030929842070b0440c0d000b012260381d101003403540003a84000301d040c141000451440c194032688000404071864121011a42d0100e41c1103513100d1300c800c40903a4403030380180003440040f9004540190000e010b59010401660103040241e40001091060007506a04031010900e4140c00d5082d51020412010400c000c03d9894011091241106841004894a030800123001c04141084c5409140700000003c1d04118040100018201401c00d0880c001560385400400c1c0d03520000c08079010358201480815240480400c0703840c89c031001800c1412400391511031704921070300c1000b01c0c01044820091203034500401c0018200f010180d0b809580c0d1103140482c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 651756205 1250 651754955 651754981
    0x12030903051207050a030c0203100e0a02040c02010204031221020a21060b040e09210c0c040b090117010603081305010305011406070b100312030608060604050f15190e 73
    0x100342e8004408221250000f00c010600c00d440d01e5150505203017054040c03000a0928140c107000c1c92400e4500038003110381231400902d114600c1d000340e9040000101c0c601c0224242d100714003014240c20320951110741203520031000803013600c201083d070b6400000c03d44080000e0303070301401010f4002158004072885610000074180703408030380c5540800c800ea1800440300d9580c05648181d030b4101c01d001e0002010783d41d0a00811034448003607030019900c522801c51140d0107800c0111000010b21403585000d038681014860a0300d1054000c000b03c031580e10784007403180480f2a900b140009552a4500000051100c4014081410714440300b4540e1a003440001400c481c416404540a907002090384002a101c090843d8807980d00081d52001d256104a14001a21400d51000b841400e415154148041e85a07001c3c5045e10b0b0f80f003054400a44038101040251002520007a80405e008004684010f0364140d0540c51500e000d0081c1c2940b0064a480000140c40d5034800420b000b205020480f58903c59a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 651757455 1250 651756205 651756223
    0xc0c0612010e1e1503240403020f06070801090b13091511030408090f0d150212070201050603150901090c08030703110f03042c07020c010e060711090a061203090305 72
    0x6085034016821030060b64202c07020180104941c2c405081c002e820903141440b0422003003109103055900740700981b0b040040224103d41c1540180100038014403050004a1001e01a0145079503031790003070342080e0390348004041d0145520780c00040172480c900125043d000b500301250183c42c10003840303896a0140030036910700302140702141c0001c204110008030003005981040c04141c030781d0400d600860010031080d03c001000a001e0140340c5110645502c0144c00828140030283c22180240c1c44564081e0b00344d600c1500c0f19076041e0001c03c00051084c69000740a940605440004661002c8540760111840516000034480fa04002514428036800c5010304a0246003c0300500e030a40c140c003440e40d00d900440c0603100300d161501504824a001401c0003030300d0440c84a10850803410140406503840c901e0307205c803c1c04034046070403030517041c0341020031b5480c501c0c0c0000805040350300d054104011071a004040100030b56940c4004030305c800012011101840c400d44846102a00b03600704170346042004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 651758705 1250 651757455 651757471
    0x50607020a030e01030e0303010905090705130c1d06190302041203050c0111030f2404050a05070212040b040303030b0607080a020a0605010504061206020703020a050d0e150a080c0c0c0612010e 84
    0x6c1c5034480707000d42c0002182d044480d00070b00007c0c2600d91100c41400e04c2c1e07984d8411584643c50800e5040790000c2c6521140c00c801032500da81101c0307180481e041c001d526882c1d07045070b408030007070041c02308029a81d42c1c03024201031140b8005251a450700f000240038540290103038001000421103078024a000d10908811b901062803c90079490007002c0c84087c0c40c00142681408640e01da404000c00180001140c09450014000c0c0018074162a10a0081000b1540d00380144660398000e000c003c0c1d44002c69050701c06102c8600d240070b06548041d005400d90104480d00420101700060104d41403502a0074100d030a17901a02c1440e1141c180030003610410780065101c2e92401108000c441d01c09505802c0240c2d008001680750802e904040c3c0c100f42c0070a801600501404144403207041c0c0c4045203a0030f8141c101d0315a00c040d0100c20304c60066015944081012600c9000426185040b000c040c018410140048400c040541d20110745503412401c00c01c8120b503c41401403080c0d049840d0055446254 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 651759955 1250 651758705 651758711
    0x2b0203070906150c03020a0611031f03050d030207050a08040801060f0b03010503030403170904150f09090503120615071101080a0e071a0705030403050322121707050607020a030e0103 80
    0x100b5050f1400d501507500c850060061034803440f4101030017801068143d94101100700103075200c1c80c442030119402141c2243ca000c4200024120048440c0e10400540740c000d0010078110750100c400743d00039804050b0a881511840032a4030001d803071a401000905804030003c00c00c103103445a810301c010400c1d004400d403e01c05200500c015200082070320116600540c80d62207100211401e8039044c884d102c08140c04c6404c00520304508460b103400c00044603045040c0d003030f0150303540044400703ca80084009005810030880c0443c0c12103581c8074a6000b01d40107001d04040d00e180c04030404582d03c1b10b801150440140c40b0120000e41e0050f40d81e80d40040d2152003440f42c00205001c0355207a014900403604940001c603590414481050160348903a0362081c04c0343d90319a240c0c10a06c0c1d813500004400310441d00201714522000051400c8282121818072a4021a02140e41c40145c03900c200c00c1e881c00076080034040b201c003007081000320500541c0c250300600084000c03410300410016210844a041c541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 651761205 1250 651759955 651759959
    0x50d08221416060c06090c05120f0601090b061c0617011407080622110414040f020702130c0c0c06080601080a0203240a0305010207031701050d1106092b0203070906 72
    0x3030001c4c101c010f03503a480f410000f90403a042c50300f9012910140c01054000e05a01900746152200140003035845643c10215241683d03101c003140142c0703041e22203564011070306014051100300c8031020250505a4940081843c94490450400c41a0407098900442c1c2d1542c00000d1004080c14120f40c000030306282601c0b00b8948a408140d5084413181282c0e06d00c00304a02c072418001c65a4030140801452070041c607034031991142056154061606141c0c0b0480ca803852040b0140502d1080300c4102d507001d00b424004178644007200c40240201c009440a0280040da03000001e0f03584128140584580d44402c0002d0821000050001c040244101d840500c10814040c1410552118803626810581410302456294001c116054110b40c0300134031560002c542041050707000708142d000e4403104082c8070761981e80c40d002c1112404420304040d020008416070701026083c49001440c441e040a0046100800424480d00068550070911030168441cbc485140851405000322001410440010b00c8418 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 651762455 1250 651761205 651761207
    0x80f0f180303120c0a030e1609060b03070c03050c0c09190f0b01231204031e0f0806040506221d03130e1f09050103031407050d0822141606 61
    0x10f10241003016008004268080300c14840e4100441c04801003068804001c0c414401c04440c01180c0074001c0c51500f02031021070007020100c20380340300c2e004503600c407111481952030030b480715441207543e003070540500e0350050748548840403424001d500080001c201e55003d08025411501803003401c001c402c0c01c0001c2c100380d50380d00803c40640c4500013003072a0302d18400c40300300101a105070340c0100b2003140c10f0020072003456084004000e959050350750420600c1010b000c200c0d0410300740c020b50004101284d003c190a41000c1d401140d0100010380340008080c0c1010745d0030400c0080d041c68202c50361f101c4046581c100c5200c80039454401c6110b00650600c05005100012005140604030002090b40b0006040c9041e0000200542900d000f5010b4140d4442c40c0d1200981002d00080c1e010a1505078a200148101c00c1100c0742580c0000140c0010200a8001c840455000c0c0c21020000c540780410001003064084040955101d054904008071610401e903040808008005800e003160b000108481 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 651763705 1250 651762455 651762487
    0x403120e0109030c0b0c16060902040e030301270609140403120605030c090403261b0f160503310e0103150b0102011b020a060e010e0c010507080f0f180303 68
    0x2880e1301601d116016500e45074528014054003030707c48030344950155800144840c503842034005900940b01800001c3c141d80240e6030301c1c0300a200755408800c40480360600c0c11802016140c0f50301c4250340102e6031541d03c942c41020341380f603c07862851221048040c4401c00d50072800710b52041010410511000d803401000035162000c0041141c041c108040c0040c003050303c180700c00c40d9000381c03002c3c3c003140400c5800c1013801c0d0390000310345040700b00f00203200716400c0300f44007426600c000d064800103602e8031a070f608241940c0c280401048038a0700c400c1c86411003c10800c6070302c81401080444410150490130a078910606151388035004650050006101266a05590304020b42d540c620100c0c0c1124200d004038010025071800451030803000e0303034440e409035000c0f42d00c20050740940000d000c01002c10558900721013900480d907015610400c40c3c04881d502504c0586801c42c0a198814100100d45241034019805484c201580240005030380c9484000078299020b01e0303000f6030082d814541100060303010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 651764955 1250 651763705 651763727
    0x903040501051815030103032a02010e0a0f080c0108060a030201080c280e010f020610120606030602030703290a030303051801060303050a090603410403120e010903 72
    0x100300b400502c4080703050391a84081c56540c0c003c1c0034607207103071603004000c0050382007804100c0001c0d4940c3c1c079525580010080410b10042d0020303410084082c3d42e0b0042d2480000700000580104000400050202d004080580101300341d4018005803c4000c0004004400003458148030341d00c007110500c0540d1b07004a0b640d5200020340603250360382e0342420f07242c100c807005000e0100091003031200100b00070364030180e072074440e140a80b5622441c11205034213a0300c8600c103c0e2180c0040c280000c040244d12030b141c25075111b89001e150000b1b00c0030f84a844400580c2e004849a0010944032150b01070025282a110b00e035040c08251540444400c0ca40015004076140c80003404140c1c585010403a140003051002c0d80074624032008000e0b075503480c0380c0608039802036049100440c1c07042000244440c000c0c011038141d40c1d100c1e5a8a614600d40b19515004080702009032600700c04032044071096a415400001e0089002e40c940600e440d9403508500d040d180d04c903109400d540d04011103800040d07041115418 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 651766205 1250 651764955 651764957
    0x2010c23031003050a05030d0c05030f0a18080c07031e0503040b0304080c0a0c0f0504020705070e07050c0601030f05070b160f1e030c020a12030f0509030705130e010501060201050903040501 83
    0x241d291951000d50310044015003000e003003030003072100c0c1c038081100000041141c14410481030105075000c400944103804129034030501004c0c11400203003803240341d41c05803120780c4042c85d0400780e04521f51103241c11604907941c1c1040e21352000e0780501c1404800701c0f01e1110051a400701c5030410645a03140350b240c0c0240c4c07003544262040031020404009a000c00d441502c0d0005040b5580d5244608240d00c8000e900c0c0300c0c030b0051582d00c02e00480d103820300e03000b02da5266805c0402803090743c2c50000c06520048000b40150200a014442000c08640c1444418000d501030402004201c00710b05007541003050075840702c81d03404c2d001c2091181500404008040858000c4188041a05241000d40c40014030940c200903502c145c002740010540c10515907103090f80259000d410391500c420344040208011000a0302003a040fa0342c5203000c0b403186000744546203001d03040d101120b035610081002c2100110942c4c038240d4552070040e400c003400b4407400d0700401e081e10003844030341000c1c41019244d01c29801864 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 651767455 1250 651766205 651766207
    0x3090307030c1109150406231c0209160f02031305060a030608010509030c0f032d120103152a0309170409060e010b030105061902010902040f050702010c23 68
    0x40070701c03811001503003a00754042c050507910705c1e12030880044001405500c912841c5401000304945842055405100c401a10500c49400c0702d441088414020780200086c088040d040c1c10006032903429000e030040c152140c107002c600b005403202070b0060002a09003411940148041070852a8801c0080c0c11a0415203c01c0d9039000c0c06903003200a040d01d40c00090a5600306411701105450010080c54591105402e603201440d124500c82d8413441401c46202e50010150070b031605050740c0c000551101060038001d03a142801c80080741050b0b220076401541e0405074480844880507150141c95003d000200005010501001c1300b4189400060003010426645100c1c6104120003180d00166421420708003945031582c9130602009013025004844040c6601d000008074400c1c3c0c001502c2c183c4000400c5c0c40e091030500c0e01070141551005940400b15074031640c0d90400358989100b140545a80350101040c43c0c17800c514081d003500c9070109640100206150000d01b46a0501a403140c801d04820045d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 651768705 1250 651767455 651767477
    0x403030506190f14060c031b0a0b09060609060616080d0207020d110307170c01051608180a150c0b0a090b07080a1802030c042408060901060b0309030703 67
    0x4900e54200c500d454400603000400c01044441c2c1d4140d643c0104d0b840002c02540c4500120184080c6019541001d6020361061241d2466009000442c044000b401811100c680c0d00c0e9448290380307413a06691083c9181c000b0310510106080944c101b540c01001900e04510704020840e585181c40390302000034094443c042101440b280b080c2c0c0403242c13016002414420500700038181785181400714003c0c10720030b125001001800006452035100803120f2680a0701d01034400c0303c0191031a0b0303c4034902806400030401e060000078240390107069a04204002c0100720f4000505109010202c0d80003e80c0b291969141d4038411507020350700700d00080e0300c4108012180c8803410580d02a05115400070559400c0f9401c0080080e84006010b100d00c0403070b9401d102811890150101e52081e003e0041d426030450916a50241019007001c40100040c1d03902d044510403214412000070202d41085a2a81001d401d00039580024014080684415010305156040508403240d4a208041c80241400716800c0e003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 651769955 1250 651768705 651768709
    0x3030a0f141206091027050a05060d110a0b04150e042708041511070510080112030e091611010c0e0d03230301090507080f07050d02090607060603020a09050c030403030506 75
    0x174a02c020031108454500300158030360804074050380e0300540200d440c40c1500140c180406030080501416010b0030308485080d481d00d130119504014101290001c034041c00000e148852540100000c005401c0081704920011200608044502074007910560a00e6102c011400d0700d00300d180e0f1500c02e44240c0186a03507140c90411980d00859120351440c24400120050007038000070150702d580d2800040e500c145e40c440d005c20880407400810b140000340c1120040c48a800c031000407801050003820120401600303280012002841114007030104800c22a4561000d90400c0880c544582c441c0d000740607104000400509140d0390039295807140d0100680da1050500a1000c4000740340c01d00d60317006c03042902d0980104030303030700030301c150314455180c800050280c3d4803038150180600c012406984954491103021a083d03040200c03207241c00c0c0c7c6c1c2000005004d035503810051040c2e620030507002c2049440c40c01080040d64542d80014405420a82000807042105084035031240d418100055683c4403600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 651771205 1250 651769955 651769981
    0x5010603020a0f170105090309010e041407020c03010e0303010b0d020a1806031b030509150702160f0f0f0311011431080d0c110f03030a0f14120609 65
    0x100c00794101c124280041a09442d0700d05541c00da41d4200d07201210140e62101e280d01300c48003166600801e0b0801d1202207810341c410668005c003150014404a13000041040c00304201809a40c00c0e00540d1040c0c4126040d03040c00c0c010002840c842c42c0140d81075600d0b20303080b203d07284a858001c1c80001e42c00900310040c5070241c00f00c10241c0340b050004e105e010780c48840140080c003010401042c540e031a0203500d5240d612034000e441c031030001d0101400707010b4040248080c0d4044040d16003810741c051000d4203c00160a025000010410000400b4581e0310342005103203140345036004598030070807004003800420120300410f440d000023860070003d00000c070f081d951028000c14011f0521080c00e120b01e000204040300c50704025820090410701466900c030481d9680310707102e40c2607102085011030030002194040c2480c407072028010b009441d14900c00c01c0003a0445d4002c1070b01c1c0c808680070b54081c608080d84940c0d6040703034045030604685050010424555a17040c01400940720344061800207041c1e20705c40c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 651772455 1250 651771205 651771209
    0x10507022e290307050a060c030309050c060c0303041a0103030c080309070f26030a0c0b0405010209040507170601020c06030a052a040608060a030c060f05070c0f051c051207050106 79
    0x100454041c0100030760b40c04655008044940300e80b040e80b0004c1075900d048074920048803925141c1c0000700da065a416405000e408009072110b00500f1640102d13500d500008000a19110014555030f00d000c1c5403000c0b0070203085510108031070400d0b00510000e500304010000d103980100340c42d610f958401c80d0f801e03d4100b050f001401308100721400000d0142c80d0b0b21461303064625503514011708000303113908180e590246250080c00924100001d802141410700c040fa0800e01410001d0300d0b00d01ca4002181c191402901c221000460000362030700038203824109941c100030b0074809001a100017400203850b40c000600241681559000400c001a0044241141501e01e41041840c44c000403003051a140c0c0162207644003040c400000102c0a2521301948010751358421440a090f1381425003c80d09014507200c42000c0c820104050004182c0b10a50380000f007043c1000e1241d40d40c101400e01c0441819101c160b041084000040b40c006500800c0d18580c40464040e01c07a200e00003800c210707014083d65 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 651773705 1250 651772455 651772481
    0x714010209031501090c021b0103180807030801050907090b0316200106061202090d08070317040f02130212240618041521020112020c0c0102010507022e 67
    0x4050043c103448a1911450480c0c88081d010082c05460f44070a9880b001040401c0007806031240095007658001d52016081c5250103524880700c071100d54500040e944411015408140f001c0010000c86c03500700304d02c50b8000710b640f911113241850901661194000134050310b001c242a4500140c0f400d203d0061000811010401c0c40d2554111520b007500038070342c0c0d018500006ea030030800f41420701e502e07000300c07204108080c0c070074038036880f140c0c88926064201c0001202000350703020f4010204e0350140291030045000302d00d04a02212a80304104c0d513104070002413803a0a00602c0094040b200c0c540140e907110030315140322401c18115140d51800040c5401080da030240e000705001e00443d100404280110b8000c0d0b6040000b038001c11419244c0303080b0f0744103016070702c000245030714550020010b820300300c140f060522007100d515009130407082e42c2000300944410341c4a608494125a070900403650001c0090001d41a40ac0d1240d66044003030801015400c51182d042d080c0144161940c0e00600e505014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 651774955 1250 651773705 651773713
    0x1f020f03040605100501030e1e030c0307150f090818120d020a0507050105130b0901230306040f0e0c220e1605010302031608040510150f090908071401020903 69
    0x5203015402450240c0d0f942500d03944040e00451a94040d01c42c10f0210b8400c41c0c010100500b90008944000380000008092743c0401e0000c08040e0000700040c0c42a2842400d11a0403c5441100401140c0310314004210351800c080d0600c0104111740100c9075094a800384d04108400580c0215041301c42d0700c2d2881003544101d008201000e54082201003090703106a00b074030300c95030751000110740d140a1280c1140340030280400400880a00c4c0e0000c1c5a0f080042c103000240840f07500d81d141c2c9080b4003002e00345020304000200070251070302d0321840c0040b482c070300420021001030508040c2c0d030300005200d2a01a81d600584c0c003124050180741850041c030f00041c28001000e1101190b521002d46e240807035034a400d07d43c4e02280c558068000d9a1091008148144240800c010b048a2148003e070054030310b402114526810803005000b868200070307210f99004060303403811101c600c500403c0e9002600007490506a0b40c0059001d0301140c1d010f94120750401c140c0b8401035000c078028441d81034607e51508ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 651776205 1250 651774955 651774961
    0x30a050903060c07120c060b0603040812060901151b021c120201020f160f140303090c0307141917011b1d01080a0207080c0a11121f020f03 61
    0x940040100881641601075410035142c2061503403250040440040000580914182c080c61040c2d0500c2009030190402141b07203034146011480641c002d441c240c401480004079518000a55500f494000005580c4002c2661505146258440421a20394204010a0301c0044c904642e01c09030700c0c0c82a00201400000c5401d50b8501c02039070706400c01210490b996090307403032046006100f81c400f00e80d00d2600032440d008017201c000b002c103140c003541222103401c2015030002068429406141914410005664a0400000712031a0001c0188054420f501c0f05100380410204c0144074100f0200588140002244140c3ca940048109030041000880708150769401181d054000820000300c900c000c1c20000241e000445610310682d1005822640d0602c00a0107540b180c00069400282c88000500b080c040307a5400a26501c95802c40010b6844404202d040c0480d005e003140300104200d81c2d06425900c0280c0854581031042c00c003645814498810a50210581d0101c68684d081404816036900e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 651777455 1250 651776205 651776207
    0x19031d0405011805060a2d03080a030c02190f11120a080310051c030e010e0a080109050708010627020f030109050a062705090109060507050703020607020c10051b030a 73
    0xf40032091020002820000131880a003000d00e0448207a071008002d0300c040310700996445c030181980019046002001110001c0440d8589014241e402d01c156004185220f080c0c00003454182c003031048459801d00f0324142d90000382440300c0319500c00e5200b0030b480ea11003507401c0003034440c19150300b05a215004810080c03042017070000040d8883d0100c8490242446c2c0c0340d80511125400d0000d4045401c4140c00603c808a4002d44a5103000d020501d01031500014203000306100001c0ea80c450002c681d102c5804004001d8148440009880e000000b044601d1601520710310041c90b00c032428207060300800b04003200c01040d804691786d81d40c05903e465502d59441a402c030080c90226041c0489a283c980041441d4118030345031031401c4030040c460703420f00580a03c0f2030000c0c1000ba1480300199a940d0103407001070a140500e1f84070b10030f2915840c0c0c5421a50a000c1d0500300c005251004540050012200c1d66681c200b04a041d40300710f00d002c0780c030750a12142d2402100324501d0048950300c00410084051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 651778705 1250 651777455 651777479
    0xe0a14070f0f3303051b0c0a1e0b0619030803010308040510030e1b042717120c0f0c120a02010627091506141219031d040501 55
    0x40340e54014100b1100500510316003803102c5190f20318030080d070b100c088810380f0384a6000150014a40e5a490b49610400010558594042e420b07080d00340c0c1020700d550080c441c0c441641e006046c0a40070f100441007040e9a842000b010081c15a80b0170911840c5401d0041c034003400d03030030255038450f000c2940c03540c5904000046820334412248201c2c81c2207510b42c011f5200c3c0c003404000030300500080c2007a00c0303c40903c80743c0918840c001600b0a0b9078411403c100b030f0640417540c490b50481040703040d9212050802d810000340c2d803031100d107580f00100410900c00550380300e031540c0017945060803030321000c40a04290b454403400c1c20481c1c1500c503035031041901d0640305004151070fa0a5030000c00085548460b00003100845c03400030022a2842501440052040d800c403000c55449030b00400210311080c074101044480c20f0300110781382890089240071034107110402d0010001110001c2110011010454081005130507006042000303140c41e184858800c3c07001ea42a10303100a101f07120f550b84482c010100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 651779955 1250 651778705 651778709
    0x314031210031202031c0b0102010b0303130f0e01080c01081b03150a12230109120201020403110a030f030e0109050d05030d050f0c03070c110d150501090e0a14070f0f 73
    0x341c14489802c0441e6980000102e42044280701b454001446110010100512100290740d055540307034400100076039024001440750b40d6100726092901c27800c241d0704011140c850340112280c801c1c03040050020200005100c10004ac0901c0c0203006a50703a4269030300c540b190054808040b802c080140502080715004901c3c1c0042c055440c4480940d60310348000f030b001180640606202c0302c01c0e200c8401514100c0108038003110100c00851601c1166580c5203449000d09a03e00050750b0209040c000c0065600c1c01090204003281c41c0c007201421500c4240f5090f12a83c00101845034401d40092917900802c100300c02060006c10034244003615041040d20b0742d0240100d1003c107840c01d4001201c079103145000c0c0740605595400c1a082d80d03102ca40a07101c44015250507101c400c641d00450601b03a440750301d07500c8954401e4071120350141404440300d00343c51041c1c01201480341091134a48440c0c000149101446821880d1003101f2407000359101d09105c001d42050700b00d502e9203c1c010824105e15018201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 651781205 1250 651779955 651779963
    0x6080d1106150d05070e10170a1203091a0a021c0501060e090703020c160303030b010c2406090507030e060106090609060c060b1216060e0a031403121003 67
    0x40051006200c544901044501c80740508400c29004680d08241802c0303100584030710211070b80c003901c45501c400b8030001100c4070901600710000130701c9030316085810008178140d170200410f400d8104e9900d40c0340045084044204055603100303840c042c0a881044c03005502d45000a02c11581070004141d00654440d049000c0c4459a1000e030903000d000718070925040750301643c0d80c044a60030032003c004402e84050a00010990284012800d0310028421016040d1010042c040e50516510b0041c055800040c1d4040c140034116103020003080405c2040c0c080003001c2c4000400308145a64250000d0003a44c006581c418607050070805410303010b900181c0416000401c0780c3c1160380c0e816084640b04c0c0603005450001d4049a01086401d004030280500310744284001f054150448010440790850030644140c680d00980054901c41070920340310010300b06918204d039004040002041400405120007804100d0325045c100d1501c0041c810341c1c40030b441c4401c1104003030500c02d084030300c0351f80d0f00d0009071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 651782455 1250 651781205 651781217
    0x130c020d0504080303061002100c03051503150c0a0212030a05100b040f060507021206100603200412020a082b0912020907030e0a081b07051c080d06080d 67
    0x3540399008109460440301d0410056295590380403c0c030008030314416080b0150300c1400f090205030f480b07500846038600c0d556500000c5628141302c01100500c0031141e42030090700a8601c48100180320700d40d01340c0c0400c0e05015665650540503080345880516590301c1d04070300001c000d001d80c0346c1040d00710030300600b07050a00e000142c3c0c48005c071a4407407180e03220b40f24501643c0c0303030200301c4079000d2400b80a590340001d144892005400043c60708084040b200c1140324291035600303002c41c0c0c1e01849012991a500d400030307a4500d82030450030900d0f04c554007460f0116150101070170115070343c56840c1c50190a200d016034404902140c6200001c03c0305050f03e14004600e8820907a00313030320130300380070081b6800041086c403081011380a00c40a8100600a081019180e00e980001414100704a4005612454581e6a2801d811080c14101c4c1d010a0000c0b0399600700c87d0042159540b410f200140707950b600007010749152024903100107148a000da1f80220181050b400207065000420891088034081d01e0300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 651783705 1250 651782455 651782473
    0x2060c07091407050f040306050403090308160203011a1507020307240306061b030305040f06051810060b030708100503010c0e091b041e0306090b0403170f010e0a020702130c02 77
    0x5131510b005d19007a00302d4403141400100042a00d41e0840c3d9005402802d219003000c4d01d039111101e86130b101121b40100300e044440748008500b000d200340c07101d240703809804c071140001020004d06800d10100281c0c0c544140071617040255a824002c900080a1508960203900441007010b1010404035280e040480e21b08240010118010746000f61888003e440078401005103a905800500c400b40080e285020030300e500c040016128400d131030182144995a5030031442114440c0e01d13114407072894404490811031708108007000c010640e904042d0740c1c24292060381e00e500710400848803036441180d040d030030019034454054121012400c001d5098900702100d6455a19221040f13124601414200b40c04000030400100000307100001c000035030100b101c4207a620b40f2201d05035a40d144003130b1200d480000a201c00c040c1c02a026040100d0781c1c1480050524000c0352402c69000140b1420f10900c000b038001900905a59040740c00d8540d00801d0041e1010404150314024a201c040c410090300c0f0b40300d44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 651784955 1250 651783705 651783707
    0xa1e021b1e07120b070305070c050a0c050a08010e0c041d060c040e01080c0a090c0c0203150a060e041515170a030807020c0a0308090d0209180111090d03030902060c07091407 76
    0x83d819031960060039121a40c0c80781c0800300d0080070014074030b03030401080c0c02c14580040c8091008040c035074004c00c41c2404641c1044108400c240e0315134811200c81e85428800d22a000002c00c2e08031054008070f03800108001d40e1508202000441c000218082c0102d000300704646601d00040c10507110801d11502003682c880c0c000c0390b500c402071801240c2c08641284100000d181c16081400c0c402a240b03400c1c81b034a0015400320b480c101d002d1112024014449042040040d40c502c1140d0092450010030a0340d8103054460a030300118001c08110085d4684040c9150100480c481d013004211402da40800f60400307080240d1a01d00442e02100050a094003089556200050103244000001d0240726046d2640d603d44900381d010849560b001850301075490096590015083e21401c100f1007104908410001040e0031629901c1110492034014001d85450341ca90054403025154103050002e50341c3c1103800056420701920340c1c24038040c0305042e00440c107407410f9082008020b4170701032145095191414 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 651786205 1250 651784955 651784979
    0x908070303050a17070e0f0a0b1c0b01030603150b0303041d060f0f03030d0203090106051504090c0302180d0501060302090a0b010215010e042a090509060a1e021b1e07 73
    0x2ca040015548403c8406e452070a04a0012000d10080900c51026035a42203008140c000050082a03070641d1441503c0086090055035100e4009103020080700d4195512440051946202c0d60602d0360380d47d81a020300d031404c20031a005800c582940514810203201488d000d20412107105000303440d5181e4000050411003680796905000401460801e12022407903c02074000401c980303403940d25110000752a40340c00c0c2501980c940c017002c0e915641d03414802850160340112000c01c1c20075204100c20500360003400324007a1016000c403500002000c00b070601c5400340103240c00195100c01039405111940107141c0c0b0040040d20300382c0035901c2d18114000c500d22050400d10504084030380c2c1500040c0080c2921442030b00000c648071080f1520300d9001080d152841007178100e8134000d5034600900c40748440070000154000400e0702d050080e104900c4002c12100d03645941040c0f6250046004020328140042c1c940c0303020307200021100541c082901100402c00340e42c0c0c05410307a004605001c508407503004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 651787455 1250 651786205 651786211
    0x601050a06050c15010e18060702030307051818060f03010911010e12030f030f010b0703021c0c0b09060f0606070b0402010f0915021606210c0908070303050a17 70
    0x410048000e841d241c0c080d1020b500800c1581200e00440c0740e95602c44c5065079075039000c1c1584400c000c05516000c0c2c00c80000703152591240c0256070141c3e081203105c035400012a80d00545900d0a640c45403003a0342140910201050100da1002480641c00300c065030480305140701c0c120850b05100903045500915007220b980700000340050044a0188955502511107203483d40c030054040350500d100c15201c20709541001000394481280041802400002c006150b4090700040b1801032601c0516900a5929408905920804903105da0301002d0180036030303501251290000c100c05c005151012915498080031110548844280300100390f050801c802a10030a5078030190007469601c0355001980c8074410a031300c4204100300c0900c040f031b440030300d509043c2d1000301580061065005914848211a81da60032200070070050401c01a510380848080ca8001100c070720000030282072641003241e602000b9001400c3d0b610517000c00004140d40180100307440c112660b91403040340011100c003401e002d419 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 651788705 1250 651787455 651787459
    0x3060605070f0206130503030f03100603060503100e030c0d0c02090a0204030327120501020307140306280b130e0106050403111002280b181504110901030c050111060105 74
    0x1a44001801c4c00c0008200c503080c1c0c2e01c42614619502c1e000a860b650000851003800b0390f01005001500304150040d6000d01803e05060000c0ba00b8000425918074052503031142850303d804454043e0842402187c0d00c8081160503900000b0403000058100004420700703d014002c0d0b9070020f004981c00b032094a00352941683c0e1080141a03420b0031084040302c218000d89000b0724085d0005642c480350b440907800a10500016817280361002c00900f1711580001c1e00441c0481c20802c0210907594035260030005850540f450b039941c1024134085d05e500005401040c10458000b68203840e07110700c1d65a030801c07200c94440060160f81c0300d1200719054081c922005182c1207150b083c0c07034620701c1c1920444030244c0070b0744101c841a4036800c9002103c002800030704904441c054100009200c061804540d1105ca0075213110b400c14050003010341e03145001200d03008003010700d80109080002404000380c0c00170340100f503030406585034101440b600b4928824540031500e800c0f401c00c0c0700100030079110304071240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 651789955 1250 651788705 651788723
    0x11040e1e071119030809010b2209170403081e0c0a110d0b011517160c03120f151d01091113090c082401050702011202190306060507 58
    0x41c204003510004030324003081010303024425030764607031158400919003001d00a965602043c20460411802c4a2141048a008180c10f05500d904603030100c5c0705c8100240c4801c000200c80c483c60078030304040f0106150f803500c10100001d0020031321199101504c1d10100140602a81c5034401407100b5042c030072022000040e030401140341000c56810320f01c040d0030b180301402c120004101c903600c007080403801340c00806000707120b40c071000e41e40365003c003141d4085852a40100071504003070090030440401410b2000c01c1000560f850002c140c414400070040400c6160140684020020320102908981800361448203240b907000904601005c840004070720b000d240c000300e903400c1024100213092800d03164200c481c1c041080700940134140050f03a0080861600004521040e03400003004510b020b004c122003103644982004880c0710005200d0321440e402d0030815a0342c2d10740c1c030068031000801001d012860340b0104000c7c0083d00c0205111115620300ea600304210350b114041503449001c0c10501a11881c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 651791205 1250 651789955 651789961
    0x50906181f090317180105011e140301020c15040215030412030c02160303030b030c010816050d0b04020d1d030307120506030f010203090307031d220b030111040e1e 72
    0x4056000215181c06454940e140d030f4041030110134012404c0d121443c44440c4141c4a41700d2070381c00c2c403035140500203c034022200d00303000c00d908600360000c9003d10640c01d1743da007546420701c0e0340950443d03c12103201f2094403003403266000c0241d01010100c4081e40591441e1980a08511040080300e20469002691008203603010720708600030705440f014001548610682e080d2803a510020710402135101c1d90703003c5006500c81d01814104500c0c90700c054180031106041c0001e24601e1181980000c02624146446425160f01e01019200502c4030301d0b0020700c001a200b1841145420040b8118903001355902d400441d407010650324442102d91030b0000300303800c00d542c202c0071894101d6078120000804407410324605010313241c2268029035440b02654000121101010b400c003114a84406c5001007802100311290041010421507282e400c0e000c03044400c03000e0f5840540d41c0300c403100d10005002005466000b2620081170b50060156512000d01c481c0000e600150a00044801d61080214010130351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 651792455 1250 651791205 651791263
    0x4141c1d0103090c1514160f03030b06030a02180f010801051c050102180307210201030b1206090601060e120d0c0804150305220c03111305090618 64
    0xc900e5000d90704042d203030710a00000c904550418000390200103100c95000d07800c3d20001c0c2110040a42c108100300c0c00f80b1400800e065114003008801d0740100782212140c10fa07280407001450a004c11a074011004003d00000040a13030192114019000221114490b03082c108142a0000384c2e8080c00a40008018410b5080032003c40c0d070050b500c01610707030022045984540c26a0480c1c9080410303282c80b09051081ca140c108080c00090280c50070340381c0f1801d040c031913113a140f030040c00b80a4141030b2620000c90041d151081107410100020b4103480840c10418501d6807280070a10484000034030030310002d0b080d8603000c00c1a1001d51002c400904031f40002490540307008900600550704810203120008400b581c1c152014160142a03130001000d00d006890219401e0080b9048103e60344c0c054007040006078814402c60a0744e8000c0001342100300a58005041c0c0c442441035602d0080c1800284960a4000501a030081d461128000451521003040d1682e03125030814500724055002c4003c1509 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 651793705 1250 651792455 651792497
    0x50d0f1a040218040e030a301d01090b16030b0a030b0606070f0b10320301060b0a18120206040902220303020a0b071d040e0a060504141c 60
    0x2d0146000c4150b0071544000c00541117591103500c0341c00a80000540301402e940c00801c40145800b080f15030692400314085840b004400c1190206142e236540f1158195503030014484541001a42d0092040010310700d009940030005403a80107240d07180034a06007200e4040d016003007030210081d100350003040ca1031b1214249007030050206070300220208540c10100e1558207030440c545000e016031014509080000c190420300c0c41e4402d400b01c91440c4120818100748003021240000b498800c2c540c140101c0380085c0c0145200c0c1d005032140100001c82ea40c445402000ca04504030407244d070503c00c039070354030045e00c10145120402940503604000a00c1041841e50141c89582e04240400a001e80c030410414013040064005a016034810403a04041080c41e044450f03119880e0700d00039599000c0100c1d41c0040c1d01441c0700003885191034000419130460200070410780a034000c24144890b0400742032400d0340f19091200b005690240d004002c0d01c0d03840c441d0401004585a642d2031400c9100c00d004c0300340d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 651794955 1250 651793705 651793717
    0x301120f02060d05130b1b1b07090e100b12071505040308070b04231b01020a120c050d0807020c010309050f12030703061706040f08120403050d0f1a0402 67
    0x21158083c40012074120480c4201403080c0000c414280c3c0b01851810000e071061b000410b112407101008a003140404040020f6900c0c0381a48410329500e003c4d03004000d4240794440e00310000052030518a01040140040d10748429440f03000b04021045808060145482e1081e00004540d40000170400c00d02c440901000c0701c400b01792401c241080d0f100e90b142070255104007015103040c0c80c072005000612603654420307000c0840c030700c102c921621540303e80b0903180ca030349070031000004c2c00070302c03500200b40d00a000d030310980c69018150034a40c4103040380140502ea4000300c15200d612035140703200d508900500c03000740500f00c240c0081540c1000382004501404001070100c2e02402007000300c0810380c4081000e03d200c0010300180c00d0326031403d0100102154181d40c440040c03504040307801015032101181c1d8641058202144003c42c3c2141d0800049a118801041403038441d504d0801051503800750251003a910400c1c4103204000f10132400009944c1ca60b404055003400e00301e1003800c03614155009040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 651796205 1250 651794955 651794959
    0x1f0b0f03090f0708011b2c03010f0e0a030e0a08060105040b2806030e120f0a030b18011508010b0d090302010609020d0506040b0301050f071d091305120301120f02 71
    0x2008618406039142020041d13404121a070f911082c40100c0c42c84142034442c92100203250101801481c00340f0800c1b100e408003c442c4a04500000c2c0c0c00711910207400444894522060a0000884482030345949600c0c130380050f00018180440d24105251039007440007203411840040030b050b42083c08200050001a600f1039000c42c80700082e14074402c0c0c900c1140300c0640c80348a10080c192a002c8042d00750790010502c0411504064814610035007080c1c2500d9011080d00400b41d21004400410741c0200700c040c40ca00c5d400f815076140000c15a0b00039449605031484012102000540d020060b41c90b19828013030611581400e00009040c801c6075072100c4070a900910003ca2425510144481268402885600c1554031070b01000340508181c003030645281c81c160000c000c24500b0351003a40a41c00c0150000f000c209590318403041584c1080c1c580d00254100501c030b07100e113080078082150003810b204412a5540121030141110707221400c1520304a031004240810404d13070a030f85400c070005281030226 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 651797455 1250 651796205 651796213
    0x20a0221030706050c0a0908030906122a03041509030804080a0915031d0a0b01050603100b1b1e06070f030e010f02250c12020f090a051f0b0f0309 64
    0x700100302e0324050743d40640c0c2040301e10340d40d038040110000e0001c1208e8001c188207a00412401200d0b4071804103c401a40c840e42c0c0a03803494a461510710b8880c103240e1500c1d030520b45045515103040c051000258003031845068004040c8a10607151820341d124850080c0100342d01e1000200402c1d8a1320003407248520ba0724201d480b0390303100d0703d21103d150000d0403404002580d840134a4807411030111411040c00c0c2c168000c0c1460a025911002d215605006031800b6400100104140001099a001c0940541c0039920b4482c00c5081044106d00e0b0300d03544e0400d007403003201514600340805d68a22010280ca2401401183e610351000351220440300e03240c481056550301e2080701d00701c2c00b0b11901c0500074a51302c0c05641d0740c0c4400c1c00d03410085200d062412031105a1101c40d00003030b0340050000200c541e03810901c3c81101d424000aa600004140001d400214901c10482c0c0c4000690000f84141c004464454110080408403030001c2c129002d0f511020710100480482c0c0302c900d0010b142c1c4000c4a01c100d17 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 651798561 1106 651797455 651797467
    0x240d0b01120c0b07120e0f030d1d0d1203140708160309020306040303090213021e0309070f060f02060c0307050d050601020c15040e0106020a022103 65
    0x403441c01c600074101c9200b00001030400c140200085401e584d1505180d0504d001e810561503182000220800b40720060352400014800c40400c014004002d29078141d001a0344030803180c002c401c1011040800541140d80d55044100102d114482c03110700145407000203401e0310120f400208401580c2810009450380c00300100d42e2021f5817030040082e6a217080c030250024249200040c1d0036014840c100801e064054001c5a10b035071003135608441613041c001a100c12030043d41d0400c9642e002400c04000503250306405940c1000ea40c2040e1000c5503a10608840038103650742c4080007003501074103050200c3d60113100f61a480000600e65a02d54505400f0041c0280319a480110381c0036528000f00350750b64400c0000202083c0701401210304c4404001d50340140350001c1c445c80d02d030181100008541e59201240c0100400d03409046d03030403200c000da80811a180b02d401c5807122548814403034 = true := by decide +kernel

theorem cover : BRFrame.Cov 651618705 651798561 := by
  have h0 := BRFrame.cov_init 651618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 651618705 ≤ n) (h2 : n < 651798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
