-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5138
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:52:31.463493+00:00
-- url     : https://prove2.me/submissions/1f0458ff-1252-441b-a67b-6403f1db195a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 923920863 ≤ n < 924100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 923922113 1250 923920863 923920873
    0xc0b070c090204272723070314010209030d090504050f04080307030207111203070b090c061602042426190203071203080a06060c030c1112010e 63
    0x1500d0020800081035209030032041c410b10040007502070038580c00400300c41d04424000c08550f20f15080b0010074140e4420f84e520030301003002004114444d01481555805403001e2441500e61030f4010000788081103401005030080b000400001d191800302209800d0b14400150501c10300b00042403400d0701c6540004005641c0400811142c00c00c2c0c4620740c0c00086191618006241548420b086848040c04550070144c1c0050440705115401d4019840d41d10003c0c00051007054200316660b0740d070004402030391500da402e030109608010005080d07400e140080d01050803da004003048005031603098050b604252070b5400300620106d006852603080c5890100d8041e02c41c1031140c04210050f184018001071841190301622a080c000768890040c00c0c035010043c001ca080f44046814000755074882814203e407510801e0400d600410100c0c0301e404590340400c0f1040c0d992034111031600c03090740081c01040417150b0360004603212100107040070401030003c0c0100603000346030b1030071582c014086010503000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 923923363 1250 923922113 923922127
    0x50f012313170c09360c03070e07090909030e030313081015050d0309080d030f1a450412030b060f0a030b0409050c030c090c0f030406090c0b 62
    0x4403081d000b140158402861810071441c0071034001c64002e007881d0b05203800304a00b200a2142180c40403840e00b80307079012009003207220400c0c99a814810030018804c1c014135501151301e0940801c110300c0750b500d07540e41c00d40585c90320340c0034801000190000d0b010009031b642e0703400e01a11300300024a581001000100704031880c05000500300400146030015590416640c03c83d280c200401c1c500540b00304580400d40c2911301d18040d40d500d02e050b80442003d0140e00c01190310240c01d41d00041e0038141c95001400307000d9144040d0324802e4006080160b001100750440c4178065a85030344030b100100b010004140d08104075850400e038a00c8484162032004110041104000e1045c2c044460039805050502c01440044000741c00d5010310401c0c80150940414160300c0c0c54442d8210910200f8082c004002d5100c1d68204952190701c0c1c034079900c3c003034440c9146055090800802440c801c081c550310030303400c000c0250070035115a80080c0080c2d90a54071020b0301c0020030110702d2104c0041c03411003159582c800c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 923924613 1250 923923363 923923379
    0xf06121406070201060b091201060f0f030c06020a230f0f010e0f071a0c0c041e14040816030c060606020607080c0f030406050619060e01110304050f012313 68
    0x10082c801411641001301c2005400715110549100c3c0c1001c8554842c1c100c68511300b00d004140c1980040034040010740c000466100d035150300c4094034010410b140540c1e8403032030140e07a40d45803440014000c0305660b450030034a010039020381034922152815507194000f01d03003216240007103010a5184036559695248803d08040041e02c2040080d00080e01000f4505146c0e904031524422038451044400203028101b104148901c00c0440c1b0000e00400c940c5120814404000120f05074101050385014045110940d210303000900c15070b440408185040c0c0420f80c400e034101c0d5050b4048007404180041140001c0450081c400500400d40c010415840c040400030034411002d404069440d1040000d4262540c0040072030b603001d03803c81c202003883d844100104150b941303034071101c03000300311030500102d151940a1424484400241c1c0c810040b0300d07035038802540b60b02c510311910b9804030000702d00c0d54040d4086c03140030307801e00d08654940005601020586505601c00f9031a80c401e00007c100500c4020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 923925863 1250 923924613 923924623
    0xa1202090d14070e0c0306040905120415080a181e140303090606011b06200d0c082d0a15031a0711300a030f05010b07150f061214 57
    0x32460310400300031341c180311030a84007034400904a00d00a94442c8440000c0c4207081010081c60f100101046036216070701c0c41c8040003070085400b408005213050b8041401400c0c0d80c01001b104541900003041c541940b0b541c0c0c440e80300c0c0e6117222011038140ea441900045401180400b4100c3c90301e0000d15074070700d45104070f1818014000d002074148803511400200c3c1c44050300512740c40541c03210000515640d446841601c2199468101144400020b2410082d05881d0040310400e08a82c0b01c0385a19150ba0321140140700705401e1480025100c0040c1c9002d10190880c95600b01e9011900018402c0c0e14240e44908a80d0031b07001a103040940840811200c039a11003580d91241991900e030300640e442001c595124020103141020120014400700050703020f032600324555090380780c0455964850240094040d0482e0286001241d02d004000140e55040070200c600130f43d40855904c00c4d408030070100a0081000b421041d5100307546076000319540385d0781010700c00558001d03421381d4040c03045030300494901 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 923927113 1250 923925863 923925869
    0x712060e01110c0607181a0c0d020d0e0904060f060f211e1a0a1d03040503031c060306110306041b09120311100b240a1202090d1407 58
    0x3101005109900c1c100800c0703140e00442c00745803092038142c1008207100b0245654000c1009031f10001c1501c29481503640c0100408607580741a03400c110381000d016070b1186964584040820f504040003992440c00c10709060b84a44200f03c009031098a03640030b081141c1c002d03001800c415280b00380034401485441c4081140301b000305d4440b00405400d5481c0552030b0b041400301c00307401200078aa07000704140c126950750800c0064480880c5450448116805030280340869450b243d00720404034940c8201008039000c0d1034004d401113240c8840c00403010568203940030444030304c0e9540d4030048001006070180321481d40354008015200e040810801040700e0600c40407030358850a9004c1407001a0300030444504503203480810090325121170900b40c4503078054100c1043c4501800410b2204100c03554481800c0c008280d92200007443c0404019020314801c1c03180c81e180c5802407001807026803150100c40c40504130100f0150625602d4004104200b20017041100c646280c803180b009862001c01c564002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 923928363 1250 923927113 923927141
    0x1508010803070c0b03090f0604110a050102030f12100819171204030e010311031e060a180507110a0605060411040f030206030411090f060316060518030712060e01 71
    0x2800360ba903034803000e103640e207442020040200800001c40154041c090700f80ca1030340003400c3d11010b24042c941140741c14030020015204404580021076a13520000641e10710341c0da442e0600b0702d400e141440504060340002c00104501240c4440802d19107800d00005107054040e04150000701518a4400b0300b00058101c05d18040d402032004800301002942c64031381203901030900c0c8000103844c1c0c00480280045000200700f0480010501806001c4201d50001c00000300c40480495101c010402c15860804e00c03640040b082c8240b6201416125030303000f540c0000460030101202c0200e0030089041c0702450364251881c5a81ea000c000c410b0409015100e00c8401902c02540340070b040250040c0660500c1c000030780103a101100050400c00a03460f00010070741c00408680d01880c195034031051200302224500c0c080d009410902a08501140b1a801910016100c0724103000025921075161951400c82075810700c01c0d00740000d040000c11240303880c07413030040394013180c100203502d45c0c9030968049440e0a04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 923929613 1250 923928363 923928367
    0xc1b01030506060d0510170709050601030902060a0305130b1f080106150c080706050f04030f26040213050703290a171f0c03050f010b04092003011508010803 69
    0x60503920f1100b1183c011449000c00122600da0000d403003010181e0ba041890080444840c0c800c0c0100005131100846641c4c500602c40d81d03650b00011000c0d140c042c54000d421120500c80d04040034003d0308000d034071884101c41c00c103c00260361112580c0380c4050301c010710b40076500e41000d80b00c80c1c402c0820b0030203041000020311071103141c414200032000c0e6101201040050203494441000000c00494048a8029400f0301c642e007403008903005150130680b412400319100990034641640112041c000098001074400c5c4104055000036402c210000c2040741e1242e02d0041100700d146441c820703a4001d40c150303600042c45541f04002c6050640002c90800038400d0881801455945d800400c80c00b51444141e10100c070640c2101040e2614200c014142c2d080f100d817544103185001180e00961003042d5681c1c06100703075105d120041a07980d03002c0c0540706860000304814481410150000c011800742004100b680b90605980d26035250001e81001115032b034841c4a201c000b6500c5205a07025158030b4020398 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 923930863 1250 923929613 923929621
    0x1008311a1305030406030f09020402181306050f04050603030c1c0906020f0709020708070f0506040b0c0901172d090d1704020f0d120c0501050a1a1c080c1b010305 71
    0x5980e4004c601c40c200800d03489591401c6014144e81101c802180d000d4400d54544403584003030b8218001155074140140b05c0b0b00d40078400350350540201c404403003018040c0b04545410707038103000161000804290301448108030707500d940c0700100702040d034010414040c1507403102c0650303000f000105a544907004560240340b850301481b10101709801214440540140e84600c10300e04407109010f0100f028124029502c2d04009002c0040b1b00e16125620540c00145103590300c411100f006c1c05010201c0e8000f501c1c0031140b40740c4c000090400c0340c102c80c48450b00b020350441b070804540b40204032162045d1b110038030014403600e801d04010030340d21040d16040c000a9100c9119402403010f84c0108081d101e003213180944007858803448100c8081d15000810b0a19000d8130100103024000302c408c0488040d80713048009404c006162242c02642d5581d1218045c0700044d05080052140c011100490b5400f020320520001505c1c080003403142d459000050300e1280100c0c81e0750b14260104c69542ca05043c1490104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 923932113 1250 923930863 923930873
    0xf02040f02090603160c051006050114070b04021011010c0509031c14090103020409060e150a08070302040b18040f051525180602031201051008311a13 66
    0x20301c0d845491141900100c0c84040c5003222403420b8540054001e0090952230001c203a815044030050380e0013038981c951400c6488448080d02d104809000d040488180e011400605d0114605260b55945140008481c2c03007038420306084079040590030004c100c002032002c00b203007400d205410300d002d108003a0f014001981c40d0081c180c0c0110303416078407840b480040d08500c10f0707000742d0540f4060008000100462a2140c5c070070312085038117039a510007140d0748481103a4649002856031081c0c40414024200d690720b59400e100150045403071031075111070f41c0300c1480da2550070062154801d60150340c00511244150070120b05010180d4840104407841d11b0400840248401038100ca41858211440d102c000000084815004034860510341c0c1d00000d800069103580000a01300c4065421401e910300d90b42d510401280d102c81d0b001c1e85d404150750000107048000c11b032003503031040340304139504050603440712004041c41888003808a9440700007005109016840d0080b466002100c040b50350744422050310760b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 923933363 1250 923932113 923932117
    0xe01020606120604150e06010e0105190305030a11010b040509210a020a030f0e04090c050a320102071503050109050c070218090c0607050a0302060702120403020f0a0506070f02040f020906 82
    0x40c110008a4080f04c1c210602d5a01009a846c2c5540c1544c00030350b1a45289003850b90280710340780c4908142c00740681e081400a0003901141d034440020741c640700c10840700703403000c4802a8045201d5580d0b000340c0039081e00c40e8002c040c030500704040a003000d0000c00c00d080c420403940310070a000c6900c09200010b040d5070001500030a036501400c10081402000308210381c4510700620b0141c1181c1409118010030651007010402d43c0c10442c1c00160030b648038654550030b0301e10440380c00e0038001d9140c2407501311a0340c84140301c2ca030007061054030744d03407611b90000700c1d03000d0301103185000086d45d01c0004000280b0f2030700c101d0360402a00650a454a070b03c0b60000b6041c001c0030810031011414482c08641030400030400032000c0c501c06051141c84e0070041c1003050701e07040c81610079405802981d0015206510119013030710070303243d0098038500f054115001e01083c40540d43c0070a400c107020b107501082680e140c501810001e4840d944d480c038000c18604c10b01c02a118200c0f040c010043c014420512260340c0c00003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 923934613 1250 923933363 923933371
    0x70203070c050f0f1e0102010b190e06031617010c1b0b0a02041706090607090302100309081318201606020706090b100e0402010c1203090c060e010206061206 69
    0x7400f00602c62000d0008054001900150341e1120000030304404042c00d80c450307402c501130240c008020442515062110321114044225203506c0540c4050000000001c40240c0024003e000c81d11004114104d80c440070541d500100d5400103814844a0361a00c240561102d01010f464001310310740313000c04085148511080001c090706c6001c0d000808080c2c10743e05903001849400202c454041c0140c000030b4440c4c0b01a02e428183d4001d110024525034000d072010700c00c0320340c06041c600414041d88400c03030081a4060b412121030034100701c05008101c40c692180080c1903200130100d04903450303810a0b01143c1443e11212100408444041e1002a000040e00d480000c01e90009404043d5450000002d03c90b00c94010b241a11742030303c100074410800550341c42400700c0c2c8204031410b0b440b84071090b01c0d9001254024001102d00000c00300240046041d580b045440e8100440c40440d56560084003400c0c5030816400550261070103642503034101b041a410644c00d40340e00811442d00d15840c2d480b400014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 923935863 1250 923934613 923934619
    0x161406120a02280e0103050c0909040b090c031b10030c0e21030304060203041205091003020703020f0708030a1706030d0302070524010e150904060b131b0305070203070c05 75
    0x8030b5410300b02004020f507994070180c6151015403082d20305030043c2206220380b020a000a1900d000a00a11742c45c2088401c45600101084040d03503541e504c55280070001402d500301c9005540c100000c41c1c8080003031030004010301843c03280c081581d000303000b1b41c3c049050f221400c26040041c01d50b08541c0085c0b108a04c01004c1d64590020a2588502c0181e0b4410200b141468800002003206000701c59024501842c032443c01243c141040700c0080b665401f40d5000d8a90181e400e03a20880740310700070f90007001100d02c68016104002e070108070300f5003040d03220342c4050540c1d0000600705a0039030740445122101020324511050506150010070b581d124454603000a05070b0000741d01013070040408c00f4108100c101c0d140c0c4c002030180f403400341522070400e105071483c2c40800d002240312001c1400c0100c0c04010050f02d17481e2983d5840e00c07250040c05000d0510341d044252a040500c50f20300c1e0f405140000e0341c005a4490007024400d10060403075000501010440d0010700403900000c6404d6603100440d0300231 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 923937113 1250 923935863 923935867
    0x804030f2003070303060b070b011202040b040e0606040b01030c090b03070e090106020d031b1b0206040801020708070b0c0301060807141306020607020111040f0302011b05161406120a02 81
    0x1400302516496102803580414100702018081d440030008000d016481c40395805002041d41d500c054a510701448400400d61800b580c014803604142c205042ca010340024004105544d0b8140030408840360725520300c10b00e401203010014141024010020105805e103401c1001041c03c8200508080c060b000f604c07603100001010415585c80b6441c140b0354044001d00c2d03004513596510019544501134044600420f0801c0746107440008151204000400395403101303000c2c03211f00e48000c040030800c0070007240d111409000228000400b480601116482900216615845420705039400d140c01009034503284406c10040c016940d00a5802e0f03044152801d102000c9020760446200500591400c000c0c98003242030005511035000481ca80a0381c10358008003da0198646a00f0880c4900e00a00752071082074031b420001544a00e012410b58414034030100e24407400c50703440350b08100b10201000c214a20040b130034049400911028a5500c004680725407030100c0300d00302201c0d02080200400c01850340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 923938363 1250 923937113 923937137
    0x309151902450909070305010606021011120406090c030b070c02090a0605010e09220c091503051f0f110306012c010813050610140109050f220c05030a05070f080403 72
    0x40004901451f4003000900180f5112103000b50b584080140310001c260410000c11002d510f054115141c02005070746c0c40344140c0c1c072511581e000c2c00b00090201d4205a401c1e10006c0801c451031405030040784a540d41510710b180500400c070185a01500b85400c00703150000800c0035030707001003280c00c0e41c03141070745d22240755503032241001d5251280301603891213080c02e1040b5a08001c105401d910075074603915002c01003c07200c90403407444210355001c0145075074001841d9581140c41d9118002d003085051340c0110740b0084510304402550001d509010b54410044107108156800444d1003103101c292103401408155148903580b019003202c601135052200c0040460f42c000f180c540300d404103542180072980241414000d89803812014480c02400b244401c031501038541c807401c1130808039a00200140400e40d48542003220141070607a20010315042c1c0044d010380049a8022480c14201c3c0303403503454407440c0240c1c601c0140da0005050400700600c40b2850703200943c004030b04030f8019401d842c1401f280c800e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 923939613 1250 923938363 923938381
    0x80f0c060c07031b170c0a080c0312031008010207080a08010b03130602091804030909110c060415150e0915041e1704080a0507060503091519024509 65
    0x2c2c031030304458a0140021712141c940880040c0c18040110f081d11224000c507940c24042e500c038001c0c20351b8290b25802003440c45000100c01e0001d035070481c40455603c010340e6501c0180908990045004488030540440d280c203100d0b42115880340105031524256140d441c2c0701d184046403861144d00105010350101e00780030613403a02d209200360740c5034a0a083d06503007414140940248864401c82450a0800108440402e0381005484080080320010800d6031225a40c4210081c03200a1605030145d6a01800904211145c103040040c43d5914a00610f03080020038181011000300240f0444490501400002500c003c8100356103041d8034403a04034048945440b5150144024910b403281c0400700c0c3c0400e055102007049501c8510900c00c4034280e959038075054401c0d000c00c8507140720640003840301107072041c0d90411056000310010100c085c03002990504104980007075210075124192105080e6007180001004180c0c00414010114001d03964501e8507000c60001c0c0303625004540b800c012440200f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 923940863 1250 923939613 923939663
    0x906010b070507091d011b02120c0f03070f1e020604031b050a090e150705120c0712080a0c0908060a202b0e280507080f0c060c0703 58
    0x2032181c02400602c05000c44555910b1081c100120039520341504180c1d4450079600ca801c87c5030007a0054410309080b42c811040301d410200f02031030345005d5000484d90307607103040c0020544984140e40e11040c035056801c0042e0b103604030a82001d264014030032000050b03a500c0c0144d40c201c80c0c2c0300e2822002e00c0c40c0c0703030301c544c40c40801c0c3d5004680262803d203000c42c00032800c0d04006224141d0904480c00820301000150406106880900201e10704020b61050102400401948400c4a0140c5880c00c003640e5552a90a0000d8030300f01c00040f03111041c4440b20004e030050003004010384c50316544035410002e0464407008094026911555184845014640810700c00c50b42c41c100380c48450b03160308043c494212136070030300d60540c00104107420f10341710300107400d20a032054906490000c081c007446a00c1c881998140c0b84000d1403c2c54840340c3c0d801c0004100b004920701520400d00641844520003240f1881c1015071109140308400910001401c4200020301c80103c81d04100350050103c07107520410003807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 923942113 1250 923940863 923940869
    0x1809030201020c2e060b090f06041a09120d02100507020f012a050f0901120207290106090e0604051314010222031a0613062c0906010b070507 62
    0x980681c0100400d0784c9100c0d00341140d580c0e00c101c4005080c55244903c80e0071611140034490726a917042c4500b01751801c5c040c03000a148140600480d00d456184d0040d243d01c243d02008004904d0700009102c496070400500d0b090000c0c41f0280109550801414003035145c11490100603076050352080001e4000b8820405c41c01c415403084000c1001c003416003401c100400a4480365288804850800513643c1e01c50070032542842d0700c0008050405200b034004480051540003180c1d0242d07024084440801c0003071640400490b01d9059a0740340c040c010008a001740b00c16032004062091450081022144d1507815651101040710700080a135038245040c0246204408040c1695991413071030312884105500030311741e1209585a00400144c07010034074000c0119400010b007000e0110703040900003800c844005800200061803003804c40c0710b01d07484100f107401c02e0b03022003000d0a00c110815141c16000900141302101c2c03440d44003a618010110346d60340e000c180310381660054001201030a010042c0148805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 923943363 1250 923942113 923942137
    0xf0f1a0f0a0f0b250804030303180b0f0a0b0f0a060c140706171501120507090b0d060905130b01061101060e010f05100c051f0b03121909180903020102 66
    0xb80743e86a08980050b0740080007010b040e2107011010303504c0c3c0078014900708013031644200d12916090070b69030124090704e88a44450021400184810000791261b42040c2c45084036240c001c0c21803606041b407205030b03146005241e014800403240c0203e251a07450742802910317400c0c01e10004003030803880c1c07200080500c04160b4440c1e00480743d007c00c8a5a01c030305003041805078a1035154490b1182c03990300d0036850f984c02c0c000780400e082440c100b4108038107801260384490207041503032806170780b050080103644c050b900c8100003036a140b80c1401200140d00c00e007608402104100d011081d8155208501102d040c018041072250b685041c0440302c01c00d40001d80a8031281c01138443c2565924042d0300b0a4031180070b098480c81c0404a01251326100d020740100058002c00105429050703150b41540c0041e001c0802e040680d210810740c001600d00b04850090151100c107842e80c1c07000086070031081c208500015208024820b4001c200e03044070400704540d00145040300240481c91454140d00901c604444202 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 923944613 1250 923943363 923943389
    0xf040b0a05120a0506100305060f06100e03031605010e010606090f0b0306120102071112060709050f0a05062205221d0a030c061d0a150e030d0f0f1a0f0a 67
    0x240100c03000c071038101108d21030401c680d1541c0703c50008007c1110101c40303c2ea001a948900001d12511400d030f011071800340139060740e1402c4911940000004010503090307455a44402d890790f43c4482c244100d8000f00842c1c42c100d8002d9007070103c04000b400e610312420010080100c08950541e55101c44ea2450401d4030f4005c5540c0c01c410b00e05142a142031580c15407180d010392007203442100011480b20b01c1448299502c0000314182820452701e22506100079401000c205004183e64540e04010300300c1d07103c55494a1440071100c401c010390030950360882c4c0d010b0b80070f030a24288441030a0446106694800401003102d2a00380071000c8402c05030981c410140c03150f1202402816042001013848038007491003442000704174801802100040d4040c850301e948118090404625035000e10440034844d001c0110311140e000c0603a038070b15044884408000c50b554019080c5a00c40b42c454001e0950081c4030600103940c9255401d84010380540c2168040c41021080d00700310781d00d60441c80040e0081c060055 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 923945863 1250 923944613 923944621
    0x302030d05060a17070510051216050d092609010503040b0c1c0203090d020f0a0314040801140106030b010c080a1b0c090903020c0d0819120603030c020f040b0a05120a0506 75
    0x2564821709131103854082d02c0c00c40003001070345116408640b10b903088038001ca1029122101c0d00c04039503400761124010400c0034010b100b001d559900828a119001c1c0f50451010381c0302003003011070301c4111615031600380010400041240d8000b019a80c0c07203500a4907101c46c642c4e519210030700c54852102072480580142248a440d1100e950165025070560000c5031784c02c51707001c18180c3c0d030740b00006482c0c2440e90005400c3c200092040c02d1080c003603034030540c106003000d035102c0149083d03500403000413103d00107083c014000654507118542031002c0910b464269201c01e500d44010a11071f12815004214004507502403030b0401d002030055459020746034034a0307030707079140e20900040450f0102200140220784840d01d1b03500d030034040d0261854112822900d07184461410481c1310013104200b00621600c03044072288080d5600c950340095000341c407441640292441040501c00f154050b06100b5442e21103820340c0c98641900540c00d4640030740e214500b242d0142c01d864509100054003c0482c440c00c4200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 923947113 1250 923945863 923945909
    0x612051c2706170118020903100c0809151e040f050d020c0a1205100504030215041a160906050901030603020918010b10120b0117100303020c0d0302030d05060a 70
    0x78011a440b65451203010704200c441c1d03c011900c213120b41c13154400140c1c5041000f810380d50003003110742001011500d464103503049440a6414030f00300310380400c524000300000600180801080e00401960202d0681b414000f81c400e00d03074004070b01601c04842c0f50006010020f030040b58920180d0804115014000c034882c00940d2880b0020101d03002e0303100c6110003d8150801c0e50b80c0301c05503038000090650000d0a002800007413000501c19811440303200c00c800c0d078110380000880c2c0564040c000002440034010030b6160140c42c0941001e40c0c118101900c04074a5500c5003040b01581c040b0301d44990343e484c0380c4d80103c01400b0a508040c3d03108813080c09200c8880e001481c0f80340788001120003400000f459004120300044410019008140c007000540c3c00101190311005a07203105050034426017104045d00410400200c035444110440d00d03030f0510500d03804105080000e02d0450341170458032410b030b0b0300139101e006143d80801e9071034585000c603100e076960303520b140040c051494550905601c09405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 923948363 1250 923947113 923947187
    0xd17280504211809020a0512010b0d5a0f1802061803070e0f07030e06010b1623160b09011b0309080610050102010612051c 54
    0x404040068809032180040d020f03a180c484400030f03c807007008040c0e203458010006940a08440e408008080120444541e000c0290764043c00610b20000d440d825503442c0d88048031703249659a4841100c640030340701d643e8281c40f00321201040e92082c603044200017695881c10b0b41501b20b07074007030790806601d19083c3c191411341c000500c003007449005002805121140410b1010b010b58080d403c4402082144220080341c0760742c0c0f91078031001e0100e400042e074401c410f03000c2c8441500d91440b015034040c103001c440399244c06000c0d480311061001e0a4207524000c82c03541d03144220036014000703140d4000400144041c42c12820070b03032201c450100c0449401c209440d0703104c03000c8058020300c2d20040b40001c20003525001c01d0319040101a1518181020034031035420402d42c500c00704600300814107801003100d407000d120307031400340c1384003508004000d050400290035240304c0d0f0071a00b0245124010303140810800103c1e00c109452040c24007241002140c170072150491054141150210031f1044030a1403100070013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 923949613 1250 923948363 923948393
    0x11010c080a21091101051803030f0306010e090f16030b030f030406093008090a030605160201140705030405070312050d0c030504050c061c06090507020d17280504 71
    0x801115020b1442c103040480f42103401c060654150400e81038a5540035070000c0141c2240c000d2180c40c042046030001e86154011014420307003600200c24000c040d40c01059402100108450140c00c80c03811030010125404001d1010b150f540484c0412940070340240d10802d0b120310040c3c2566090121074510503038952161181e0350010b41c11181c00902080001e1141c03c1800960758a040c00340e030030f485000d15007000c1020940d1450410448407031140e9680c484040154411480071601c2d181c0160191890320b103013480b140542e414102403070b4549030100c0070580d0216460411a88030348881c10082c0c0703847c0c1503400c01451003542e0f0161610081d04040a0003d071908950203015a00390103004600740c5600307980003051584030381c0d000c040303a1820b0005407403855240014415203070091050203045c2d510b1580306117501941c5005200303500e80c1c14405040c0e59449400e221440f2061091680102100140b1004881c403a880c0d282c0948004482050304c01001c08005225500f06820b0020b887c0303050030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 923950863 1250 923949613 923949647
    0x807051e030408040305280305070303020d051906090903020c04150e011205010b0a0506090103050403020c030d0e0a06020c060d0515041a180603120c031303030c060606030203060603010311010c080a 87
    0x4000500380040d0400e44000c84001f01c1a0310034021110380c0c0545040d00950380413000d0607021b00007504002c1031403144074410460a4940741c1001010340c0d9504c11141c0d40c0c0c10000251303040040c0e803000b003034001446190ba80c5050300d0020b41b00316900c00ba031a07200425003184142c031580c100005100c2c07903101d0041d04458042c00003007000e08034400801a10500c98410315400000c01e100c1c202e140e60007984180d6000d40680181e81404882c2800030b420f003e0166101d1380440c4080c0141c0841d8182441340768080c00c0280014800e070011500000d00318061007680483c1c060320348000548620201025004484018109220128a030b0b401c0402c85000e6001050242102922441540258140c403a0107440068083c2a66242000361001c140d44400b640b03036250302c01000078021602d0300c415000c0045003c0e95a90018000038a002801d07079a0310340c0624205070060050000b1917a1b00c00441341100d90001d0f9002d5030140210059407509100a0050a403400110304c0b4003245411110300c4980080038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 923952113 1250 923950863 923950873
    0x4020904021c0e01180303050603010f0e0d200712060609050117011b05180406030203160f0605030108070608062e1103030c041419060e040e0c010807051e030408040305 74
    0x40e0711403078200d031701c00316013184201d40c0c211582010034041e07403080350091809000850700380e17451a1040700796022a045145254420703010f8400c01c3d035001c3e2030007900d00d03c8110114801501030641568402d8280541c1c44802c80a00c45d14040060035030011005140e03221040c0324070b40e515001c203482d0f2601c003061128203500700325480140324000e407044c0300d05214030340350385060600d14260618007000c442c0e8216003043e40c0d0f407004400740e5010862905940e00040d841554581492480040d007030301580000d080c0f0070180300500c2945400b040400640700a403038008101da640100080040281541c40304045611094122150380c86001284015006803904850603540d502d85030791b00e2204641503500c4080510051003284501c150707a070342034400148a03800312586071071b0f8602c0d00304440d40054041040d5408410706230801c1d0095001300301c0c01c00080c2076030101c1d0400103002c0c128000c1244042140c0059005150410421708070320322010802d11645910b0103242c6108a5400703130006503410b10030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 923953363 1250 923952113 923952131
    0xc080a0c0603090f0602090613121e08070f0624030203010c02160509060102011d060615040b12190e01051b03040f0f051509061515040b0904020904021c 67
    0x1a00408200b2a0304c0382e0b0401d100c0e038a0740c440100035084082e00c182d2214003007007041100c0300c192501c0c00c058a100d0120081074412854490081194030318000001c0c1c003580e1807100412a40000c1d04c040d1900680401c1c43c014103072404800501c0d606001c0030031208440300d480162040d5000e8041502e20a034020042d1100783c10050f650340701c04014894140000790024449800e0803d210b0342c100106000120b941050140303c4012554108020031007030f03001108020192425400d1211140e124110f50362901e42000d201140790300c15500425000424480854410041001001c0041140301010440c0d002c1d026142c602030102502d1a91204040c1c140504282c10400220b9010380d5009540800d030002c84e41d40e080606441c1c100945980c01445078a04c29031b06000d052900c1100381c1c2020f03101a140450f02c00d1b5140b041048014011411122241075801000049505a5140c00f580300c0c0ca4140f400f0010300a40700380b142c031581050012801e0400f01c4107169406121420070803040c404010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 923954613 1250 923953363 923953367
    0x50705100501080d03091115030f100e180a0203060112030e030607091707030209180d0201110d090819021e011415060702030703030f0e01080105150a0203070c080a0c06 74
    0x201c2805080020340000d00959105030080d4071010140e48141580c0c10288801c0000416020840c840618074030400010001210690342009500201040e4400d8076541001001c02c1c064500608a504c0e54440124071114004200074914075240d0003000c580b031641e12444965104185030404401050070310030215030700d10300490410300c60403495440681181c90961240100310140c000109140a01d44001c0007689074040c06500c104040300402028040c6007940e11310b0200b0300a501821039152001c0c40b8a040e28070340407a81c6203903100c0c030081102c101a0400e21407901c075000705103801d0b045003500e050b0403a402051500c034040c1030204010554411103209800e032150310035105004842840084d4002004201151071740001030401030611502e80d02107032403c421500181c01141040c8000941c0f04d500c00f400f66550042071a003405294908000309900c1c009051102007003980220303108a001d8420010b403000301e0340050030f0303902c981e0703440321201d44443c120381c0d050740c0410252401285543c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 923955863 1250 923954613 923954621
    0xe060702120a1110030e0c040915090503040e060d030e041d0a06060602070e0712050a06150e090a020405030a0b04020f03061006020709020a0f0c05070f0303020c091f090c0e090705070510 82
    0xa034695019001501c400e008108c001c0108103000c071410703012500750000e40f0320a0320030103070f6043c4141d005541e124104021050300e440000c08061081945d0040440000d03404812345842e90410b40d030114558607402e0b46101d0460440000049078820034218034180b202c10781061049800540a40d2651510348072807010007281101c0c56008643e171186001451081d03544181c2e40320680400000351681c59800080d540e928952610307001036442d02280340c1a15060b11890b40088452100310306d07182c03610740801d85410305003c0107010381c0075000004040d901e4801640c00e88260040c141c80091509502c00805400980160740040c0304e5000c02050604451080b03420384a215221507107450040c210840350300011110490345030252480004d078044545000802941c401e0f0040c04c1044510300900c00d6031300000341101c203c40780c5440e5002100005040440680d0300442e000705107241603401c2601d80c424132b101c0040e00400315408200f40694050b015140e4075110b64140c4650a1a003224103040d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 923957113 1250 923955863 923955881
    0x30608010c120c0e010206071d120d020601050105360402040b0d050106020c06180a090614030f0304120f080915040e060a031707020a0803041212050a0e060702120a111003 75
    0xd6400403020502880c024240c800500c100c1b590300210141601c1e000c286048401c8940f110070354031061500040b2338061007403901404080ca401c0c0d00780006d0380d004101c41700510b2000d158a01e00440c00d00103201c0320325900c4080e0100500250b655943ea1640601507600880341400da082c17030180003042c41d610105c0c0b5181d64010080c101810000c00c1c038002100312540c0d1020a80c031a800250000c3c10305058081c9000800680840d83c4500c3d140c0310603d8103210407011080c42c1a007040000340708120f50302d02c15030450b9810000d460290100c0d85003401d428400e14032203580c02031181401d891380780710080003042039451900031110135803582002d201103510f60380001414208109000710528401902511580380000c1041700b803a561080250300350f034441c0d04401c41a8a044a12005000c2c600200c1045a440341c070f0312601c0d002d020307480140044110003181b4820080010b246095685d61115046010044425a0404504c6150031122070b110080380c1c2c2d016005a074034040403e4004d02c622451 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 923958363 1250 923957113 923957117
    0x70e0c121006080f06040905010905010e010c1806111612030e0f0d0204020f1b010b01170c0d0c0c06140f0109110d0509071703030109110c031603030608010c120c0e01 73
    0x203944c031008a9100c0c4a035008003503603089a50b402c032200201c0c100f4000c41c11950300650000031070544842c2018296080303c0119014881d9841000c10500d01c040d504408a400c0d619044118040d1440d00f10300304035140b0342c0380f01030708000e080c086000c1d403410050320466442511001d4041f0043c1e418084141d0041083c0f0780e1004d81079100c400542055001002400d0700340c031140741703040b6645080000e2a15180146446a0755414400980703507000030310841100f9a0340021032040c40c00d0b0402261351301c5200c01078a015070311550104c480a006425440d01c4562002c000c2c232921240d00c81e07110610b0400ca41c030501d0700c8d4805000180b43d268500c900b460403845c2402c0d482c90000d01d240e034103025040142034a205842030b20790024075001d524003014581c8c040480590b41d2545011014016240d005030103e004100802500700b02d610000101d13050724409181311031101c0d0003800d080d80100b582e51f101ca2000e5080441c0d18400e01d0340258055061040b08004200490305007404440e032684080314640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 923959613 1250 923958363 923958377
    0x513050103060b091020030408010e0c0a090b060d0c08071d0102070303030b1302040602150a06060905130e16030c170a03121b03020909071107060f02070e0c121006 72
    0x81c990500400300c00300c0340d5880c01e08000c40700000311b1030209414031590360b83c00b603040440d080c01340384002c1c0030790894400140000d203020740701b0400040403407802d40f0554440729540e00400f02d4a403102026100c54103010fa1080040701c046a8005e401c80c002125118001144001c004444402002c1449181a07060340108655030560780c060300100001c1d81a81d5002942804091141078240000d00192407941c0c050452184100207021543c58003815022096060070014002c0030740c4100624110781044071a081d4024080311000d0081800060000e800e006241440114089070083c0c14200d80c40394200415044d50740d04034403041d460043c0b400183d0340144035150042407191750100c0c45809421310000e9064042141c40314039400c03200c010f4001c07940100f420201460812402540034055060200141071036001081c1c69142030f006440c24440104900074240b40300300036110142412000c80042820501c20140c01c50b009400003914215000002440154031150104c1c205d45040d26208 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 923960863 1250 923959613 923959627
    0x2010b0d06090639030b031209130615050306120601060806030c01050304080405040e10050f0a050f070c2307030f0606240309022b0b01090903051c06150513050103060b 74
    0x260748041c100b4164003c054580301040c210342c0d4181f00c881c0052310041c55040c0e4900208051000000102c1d154420703503864158204002040030154011020b00e6242007566541c5810000d42e210006024900d424411100040341964122148502a0000710112409062010300445e10b07072004a400900c043c03000c1c0001c0019003095040346201003c1182920700320303000080b1050854504449200429008030306026080b0190f2180b5500200d00c0301c580d109d180340405028290902c44040200107448000082c95000c442d0100348881241000c10350344c00554031b00384039050b00082402a1896840d2810004018040100e440001110116030441c00500248103400610000c40d059811030b0f50101c8031a01000010502c070050900303126000d0342c529090518100c0014140c1016080030302d01544540403a4020b8191a980c40c43c800c2c0c1c40100044811044015060b15449034890000843d0254207540c1c10038040e000704582100c5103030740c6690b83c0004405503200c82c03040e0490030b6002c00c454 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 923962113 1250 923960863 923960951
    0x20031c0509101b1a010611150a02090d03030e011505011e030f020f07060b0406050d060504050a0c080a030f08061c060e0607051804060e061002010b0d060906 69
    0x42c81030000d10341084150b100e07020125030203c4814580884240980043c2c80580e409070b00725260142180d4a0802e0800006042c6c40f0f40d6609007039080350b8208400e00c0058140c040d41c0d01103444a80001d003c980c03403a08680b802401802c45010341507100c0d420607010b00614412070b0000c600703e0b030341651140300402005004c064031009850030b010416841d540c500b901c03040e081c001415505d806404041c2e488429040000c21039200f03105062003a81000b008200035501c002e0100c16058011000107001d0b107940c80c040d49808101100103060042001000481d2000410324250150103521401a10011104200d0704403000322001c0341d100c0d4400003000700b103410941c000913001e44141070014003410200c018601d00041120820001900001d0705034415100956807004404241da041c03100710b08082c902030031014010080f500130041503a84400f828400d41020030182c0024141103620151350400d54090a078000080d81c40701c2c14250a00440407200c0e0010240300391a48251511902603280 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 923963363 1250 923962113 923962129
    0xb0f061e0c0a051515030a03051e040e01121a0c030a0f0b0d050709200d020f070b13021c020d0803101703040e180309150720031c0509 59
    0x11040c418402d00d8240340004004104018800300350346024074880c641100c80d030005010501d40c030b130301a4008000550000b0340210645505445910150072194004480c001c00741c0543d61200070706401d0700e00009401c0409406a50f030450184580d103801ca0502a4410914a825a44010010390400006956007001d51190764040c400010101e520b80141c4005200c1d03c01a0b1000c0d140e98120001c03c019051203882040a48070741002c07262030040805016034545d0040c030700c45110540d00003a007400081d80a804840082c0c2d4810fa2400141c1407200c42000820a4844203c0c01500320039442c18081d02c4a00828144030b03030082020b10800c2c0e203070759820701540000d4007101620b902910017040c5488050f1400009000110056440700e2038091151a102406041104c139440c1500d001124000c020040b10301150b4103480815140c0040900840244106100507003d07032860768404219400a020104010b41d044040707540010b02c1503445a12409219507110108000300701005150400c004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 923964613 1250 923963363 923963377
    0xd0b1c020108060d0203061008061e0c03040221011a1206150301060f0e0a0c0305071403250507020a0f0b040306090c08030309070e07090303120506030f030c010b0f061e 74
    0xb00c540701022617000c68501041944c0c0140300c41000c40741884000070801c09280c5c81042206000a460178403030b03c0c04030906020303010f0000b0321800400901075403954021542c204180301c14460411001440fa540204030b524415038082c02c110741500003616010300342e01d0800c05103401404140d02c58101340704250311070300704540d095501d65400281101c1c0c0d040d440c400510a108086009203002100003045070098400b220a0529260501c480c5951100349103019001410066035280c495000d2200154141c00c9001d450b8442000c02e501010303481409091264070986103048100c0d10b03610407503401001c5005d150f0303010380d06010800105295402101c0040d0144807d03054868882040711304541c400c40315500181d000d000b00300a0090070034101030f03021040d842c081c43c503682540d500600d11868100c80c2e00803980c8605c0030a000da9003e100c056405281e240c12240c0d80e01810540034046c01d810210319126115101002009082000460b100303101d070303502442902030745800030140c150440e103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 923965863 1250 923964613 923964619
    0x120807080121051b0a0e070c0b040318120b0f0f0a020a031103040303150b0408030306060a1e020714150a081f241b030e180c0d0b1c02010806 62
    0x10600c200407440a0040d5064101c08a0444519821903005c2c002052131560110b10921a0744041081075548a0240e50000d41e101c8680c1019454500301115052a40300c0b24121070480f20000090b181041001c044140c0c1c40fa10910384d2031f0741c64150030b0f498064110b43c1100c441c070000c000142d254069600400303500486060009252241f107a102003d600211000c40100c1d60300d07803040030b42c001e075620048010070b545444c8505d0a0f0030159220303201d0001528031801141e01090001d0f1707840c01400e401c03060140034000d80003204440c4000a54595051265108124044850f44d41a05160002c900c04030320540000b40f0f00702c82c1c000c048406800c010f0445040207111100d1900050071003149100a205030340300c070310740a07480401904050300030207590000d00c10181c100550070384500340011310f865058140740d000c1150441c00306032100e040310390341d4a040c003c5100b00031101240e40098002e40d44109420082114480144200d0106030840c0d1212901151181d03801503100e11f070107075806003002d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 923967113 1250 923965863 923965919
    0x70314030c0f1602030f030f04120c0914271207110307080a021512060910171c0c030504091806060603091506050d03030504020d020d03020601031208070801 69
    0xb00001e40700d2a080440000754070724040d50310a0540c54100502c010075200341c4051071403c0d924440d55802d600c1a4429042c580c0764406561082c8001c1403689001001c00b80c0d401d12424100c1102d01038040740844010100d4148405040101502800e6450b006034a0800800c0d82400354a4188200d4201300300845030f00041000d000c01caa1030a102200051100d8002000020300c9403042200710b200380d04c0840785a80f030a02140e520740c805050084d42120064602440b151560400c1480c04d5400390050143c400941d00410744002c400100c0d42049000226807900fa038045100403031340d4201000e00034002a0003440f01740000c10841e4008a0420448690366141404036502c11041e10004d51000d0040790b6112103881c18844d8403200c99034500c05a400c10001a401d04002031b203203241c0342c44003600b00350317854001170b00319143c801407040c5031a002007072080c040c00f0313500e4009e5450109000032500300c0032030710302e190030030317005c0d40fa20f43c052201c2d51075034207143c0e09002c10001c00800000c0c0140b007030702d58 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 923968363 1250 923967113 923967127
    0x1603110708030405060f13060503180d0903060b010c1e0510021e0c0a0b0703060905060109060504060c031b0b1e040b0a0b270109060f080a0b040c09050a020301060e0105070314030c 79
    0xa054401c0d004122645130941c503441c0041c401c81c6100d590712030150460704403407010340d49143d004003013700b520b50200340000c0441070312004942c51048010000c2c2a84680c0046403032078409141000c41c050720640868107500461035244060f406120400c1c00302c000c0790784070200300c00c0d60b00c0c01074406501c3c42000c40300d01c4c0d903540c0c031703801412141a00d0640119968103424050400140141d85d070101086c20024541454114010054841c0c1d02c224420044c2d40b244401c02c02d0b00c07919000380c28106808800c1d80581d01820070b20401c142c1642d03441d81000210603c20440c0d0b8004502c58801c80d00088a800250340310085000509141c03054a07a002417a565080360212a020503001c0e05040f110fa5510f8945c182a11a0200c590f180c119407010058281c0402040000084144615501080b1000c00e0b4840b4038081c9041d02c410381181c040b4a00708800c0000d481e209901950403582650380302d10141c80f0000043d103080c031503800044e0000e030b000101507201100c80340046810a18404100b85060a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 923969613 1250 923968363 923968387
    0xf0f06070b19090b0406061d06040c020c0613050108010f0e060f0d02131406030c130213030c030605273007110a0902190809010609021603110708030405060f 69
    0x4400b04200e4413040b00800b800107005051054001a0510200200042404860000e021840200400e10450300c4440d2080e00ca4801d00c0b0404052034041d141036180c114500000003085100d01415000525100001902032141c0c0d01340f804503240100c41841c0c9448080a0006048101a100303411001d0002c0030f00050b21440019000a0a90400040d440b03c0318410361601900c05022244a948041110155541c5040f00040000d440050050340d0741d25485c6102d0019015034030107070103440040000010301655400c591b01c00d10085c03000d50120000c400d10302311300c101d903400e1704001d652149010744001d4212564500e00b000d07222510a61104082400f1407440c0c4c0f1200040300d25250000f050203003400c020051a02400032600c080d818205201c070091000c81d01030f92500301f0420701001103100c0d01000c8d8007200140544002c299a03443c1041d03c0d150700b440340300e00304500042c1e03094840c40303158101240e52002da607102c4002c2e51910346803400b0080c140c3c000400076545144104240034503c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 923970863 1250 923969613 923969621
    0xf090903020118140106060843050307031506090905310212030a020c0d0309050a0b0306090702010b060a032007050a2d0b1e0a0b0f0f06070b19 63
    0x1601c134119004100c60081201c609440e080d5020006001c1e1010500c00d0002c1c0700d02c0d483e1041c01c4260003e490300c0c5a40e101103002e04401035086a03404000702d490a00a41e4080c0007148030740070949090140552042070030021510314842c100024107845c100388800789551f002180c000300c4403582164102c0c1a500c0342c03810101d081440d003542000c000d1048045082441091300362441410285040c03102c0b1000c0a5100c2c825503060500c1842441110300c00c150288440c01c0260401916504116440d004d100c1e180d540183c03502c0788151440300000788400d1050280142290f806400541048200001500036001d4014023600502c4000700003c60440780e030011307000d40d42c0940014248144c182c144820f450240c0b0700d001c15444201c0321650007007604910301e000540d0344030b407040c419652100001a80c01c200511510810700c0c11005128030411150040b500c1c44000321030641140703210710704202104200b0021550002001d101020108580c224210f500001000c10003507414036400c2c0c00740803a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 923972113 1250 923970863 923970911
    0x81003122609011d01020301140d0f05030d0203041707030903030e01020304080f06010603050117070e0604022808100602060c13080313060305130503070f0c1e031406010f0909030201 80
    0x2680d518041400c0307034060b04135032151400040300214515414800d403040e0303000d40003900c140600300380c18800781045001000c5010054005042d41d0700c0e140c1c00c00c9408060360017a10140c0303480703214041d84030800c2002001c84005680c16114000c4d47d619599050300c280d0302d18861181940414003002407403c4040c0400144262180050300d499130520802504880040c0c225110703403d040c180340d12030300d9400903040003690300070440d4101039918100000c001e4030624010380e0001400107946007080003041e5400b0011241612851801c1d61010840e005101c81c0380300f042c0050340000041034801c803166005000d03490200d5528540076450781c003803500c2c50b0310840e01204401605081004899418801c29030001542464552201a00d07101d2660301d025400000d071048540300c140d0020800c00885030b100500c56400c21030032400d2000400520244d46110a44100002c041602c5807000d02280c500e06842c080c13003074004824200034505005006a01e41241550360702c034180303080c400008195200d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 923973363 1250 923972113 923972131
    0x1032a110d020105061507020f060c100b040b060d0917030708090712031d01030e0f0c040b06070317191b030c09050102030306011209020d0f030810031226 68
    0x1400d0035103485a858101c1d149400011645000309100e481e0f0398654044802c44281d80605850710103a00005004844203005298841c0d0001000c25a4040220703000702c40180040d070420584000d58203000958940c40d00e030359032000c400c03c58112010342d541d21140a290050f0a00e003075040c6088121560b55005441080100b09010100080c0c19001c2020780064101d100880103a011a5640600791070b4501c0c14680a0f410408407003841e5900c240d22420b64810002c0489a4602ca420440c0e40c44a80c10a12a400391303082100d45c1801d82032038400c0742d56466040c1c0c0c5030b0005131401c200341415240007801c40d42880200b910040704402043c015040d100c81c2c1c250380c2a400464001c0003404540c2c01e88100800d00003000c50030402c5070307000b2040c0c1e40e0060081c01c1c00300440702c900041070300900324039100030342c0900240304040a100100c184803840f14402c2d101c3e98070585a01c80c4417466075480c0d1200400b00a0502100e02046e071188146d41d0003414511400c1d82040405102c080702c4180496900c5a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 923974613 1250 923973363 923973377
    0x7110c060417062809080d1802030609070305030a0311132306120a110d1b08240103020d0e0a0c0e09071505090a03020405090a2009040f11060a051c1a01032a 69
    0x40d031a007070040c8ce0b0001038140c000e164007403a580d51584c59014081a04061590f83c81c21482c0c18002c05080b69070a40000141c14151360721502207181800204a048030083c1103a0301d0040355003405000c0f540b000094502c8411683c0d50301107000e002d403217203c40c440f164420601c00451074162601030606442d40710b040c8420301e1240c19900800c0c0c010b000740b22030300c010803140e0310203200d041145a20014000030f00c1d0141e0f89191808c0814054002c211400c0c1e5503109180c1c500091010920501c029500c0001c40031440b500d0310501141d4400240c020150500010f030034192010340a0001408000381c044c0030783d0710b916a00c2c0c0000d01112000c5411060640140102104105181e56404032940307031358090155501c440004280c0e00c00004100038840f540c42e200e00000d2094a40d01c048981034000e110a90701d42c0c19130b10041c5190080c441c0441406c820110070012030416006031881c2c200700d031904801104070b03000110040c0c00704515405d154245000798214030b41c0d00025203940810983c50ba22 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 923975863 1250 923974613 923974661
    0x405070504050f06010503041103120c1e030705030f0d06051003051e010609031103031e0a11030405100818010203010801020a080114030607110c060417062809080d 72
    0x1009a842c0100101c01d44440f0400b002603603a0850705490300300c3c1d0040030404e0310742c845201091400900c00c030041e200300000f20700c00c0c40b0710a00050700005030044c0070040c0361185003c12034507580d000d01c00004096420034841e96074008007000141c07000550108010640c513940d14080b4036480015998540000d40320400c00c5a00c82d48840144542c0b488003601c40090741c9010802008102d2a00000f44066400784045041c2d80e4104140c41000c40b00030304410b0180b0100e001c6c440325901114841020405141000c0c0c0095404400d440c110b56001c0d000011951040c02d0444039480300402230707400d8150148607071591510920107107002e8a101800140c0e6201050300c041c0c9030100c16480050000b2a14900034559100400c84079000745060070240c40c03e607240140541407058003070f41c481e084000401c000501d00401c20343d080c2c24039001015902d1a03150f42201d030754842521201907000310450811070a50382c1c120f501000000d40640301c02da00b0700c550804d04500b40c94101d0b101d0107102496811389 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 923977113 1250 923975863 923975869
    0x40e0105100e090c0a031401060e0a170c060a03020c0106060819050603100c1e02070603050705090a03021c051f0501170a0204020d0e06090105071d130e070e04050705 73
    0x1120400e5400c05042e8800e00c4000154100d00c0200f00d0350076800081140001c2174001e801c906900241311951a45075a100c0340c0050038000e4096050307218120701100004c030700c2a24021780c41040030000152a8082261041c08020b0340204286810035608100166004030280b282c1406800c0c2036880c04000d08080100fa0084403582102c01d1566180c0700501c2100d81d000140480703124083c44010445001d0b800d070603a80010704984d00e40b06940300c3d48200d1341c6144d002c00c400701902d99580302040703d929007040448150250340029a000b00900100780301500d071180d414240e034202c08891400000041d03a07214100782c0010b100707142d058040d0a100c0040c901501907107014200c0c106001064010881d0b003240d60350303131401010740142c3c0d0018101749a001a40c00525403c4101c0d000c8445900780110814020101140d1503000240c40100c60240100c09804103044001d0041c40c05040e1600c42c03815000a00006281c0740c2c40307120303007100004c0f041c240060b52441180600080e000355407a05041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 923978363 1250 923977113 923977129
    0x3090c090114030318040204030b151306050d021210110403050c030607090b0f0f040b0c1006050123280905030d0804120207081009050f0613080d060b040e0105 70
    0x1c5908160b1028048403075071000001e813030704030741021913040351304440320041070007849160409000d584501042045060085040b12001d90080c3d0711401041004a803980440e0520b015541d0300000140381c20015141618540881d41ca1042c2524200c0c901e240d0508101c0e011282c0030000240c0c0813078100b0900600707002d0625408810343c05800b071450403110003854582103001d5040c4014020440e070f080d800807801031340c00164002c2c5406030340f240c6940aa610f20f401603441445a441a104044121607142c09103008940043c0c455082ca031400e043c66000c18039688280c04007603002403100c5204540300903801d03113400b05038802040c4110304209008052100913000326009500c00404500400d40c480c091950103500003038140c010b141411022400c00c00c17154010241031203a41c0e0341100b140715030f0740800207992007075007100d0a05a90001d441e0722000101c81c4020540807500d02034003c0365252004203441d500c502d100043c140d4507070751204a15001900001c0c0001e0b04040140a14141320318 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 923979613 1250 923978363 923978369
    0x30621071406031005090c0d0c12051008101a0315180c09040809060706290913030309020a0b1603030501050607020307181d030a091509060f09080303090c0901 70
    0x9000b81c518980603958600c03180c29845018060054103000440b9032085006403801e001404005004589110740001c001c400341c0c0880003442d80c90300c4082170911243c0d92400d0202c844103800382214580750000000140840c820b0301001e02080d110100c07090707900340076036803200802d60800401c2d800c0c0383e103115051126100e002401688400c00c1c1c0700d0a651038005044d4000d078000e4a1558442c420310114083c1e0164100041001e810400c10310076002115001441f10a084596401550090701c2000112441580c17500c46411a404910000c070303100f03401450303420740050850000c05075680282d801c5030303022200d1010314100b105420340c20141d05d400395500501003120110b0400c0540d40001782c40b48100c0c413880f40c92144c1d130601c0c030301d1154860300a2440b0030a8002c0c1c00101d01413003100c8075140d9110010b00c00c0001c0c0c8455001c03034080710440c5000400d0b10365540d5204c42d6810b054040e100c49800b200154140302d454400018240e504000942c850422031000d0b010014a41042c802c0c90401a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 923980863 1250 923979613 923979619
    0x3230604052d07270b07060f050703050405010b060715180803040605091504031707200f0c0901210206041221020304050612060a05030d0203070309120807080306210714 74
    0x41c4d000c44016101001c00c03c15500d0800803580d41c1c4902c0c1ca000d400810994001c4200c9600b48030820a00326050b82c0418480e07030141d0020b12141a80d0410071002d44074600c00244002941c2640071042c0740c0c1c9601041d00801d000c007109002e4103440d11a0000c0350000c6070106c46603030300d90301041440403003403102038080c2001c808060b400c0d0502c0e6802400000f4244180c5041c83c59281c00102018400c00440c45100c00c01060b015200351031203072441e1181c0f500c0350200d10602c07400c0e4003d41c3e5403c10f1115141210080441035107070b0b00d42d4400c0d032400d6284c960016030340b000040c840807462a2440c00c00c980014800d2022001c003080d540c050074030030050b8180ca1015900248810011a200c60701252086040d10b03144460a545007000103189200c02c1c1c0040da0180308030300c080002c0c1a00000204980c60003511000d505039035500320b4503803004c0c0d0904c0c024507070b120a01603c400148804090340c0c00c400000c100030b40459404400c103040300c140d0354010340d455102180801140e00000d0164004032429 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 923982113 1250 923980863 923980907
    0x1f0504050717040203070f063501050d080c011a03010b101e02011e14010b07021005070602160b100e0609040311070b0a02070603230604052d07 63
    0x10304016190000b100b5a04008445030b400040455030306000300c8001d070000d01a54109561580f0340240844604112206000c107400c041401080503000f4044003650320381041c0e03c4980c2040b09100c0540e94400d401c4603407900900450b40c2420080c05086440400b20a800400011103010103003500c43c0c030007045000e20005d194003501c0c15400028012624180c1c03418030740c0580300d00307012401400e520f402c0c0482c000083c60b00c00041c07174086c2c2103224500d00e100f40d01c4003180d0300e86400c21201d12a4200013580190600074041c5c1c00f50003640a005100d000b2080141807400314910b45901c9041d5000444450300800200115002c04d154501c2c09010f00507014030722407400308086000c05202410140502c144903403003205d52340e002c0000344050001a010242c842200c0b8a01942e1032000c1c0c06140c001c46e041c8446d001884079410b0007040703103100c140145203880e1101c00c10700c00145006032941882120007685603504074400003130b800c052104041d40c50400d241205d0300070810302c1d06181d885409100c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 923983363 1250 923982113 923982121
    0x609031e1f0903120b0d061107110108390a0903020301050a09030e1320070618020303030403031a12031c02070b01030b071b050105060f150a2001051f050405 69
    0x84103144c0c0c102c11a030f0400c0002c1c4900d4000000e04504034440005200300d04045001d4159400c501c080c000e40e40c40756250f01e40501081005440c0da0408031200c12450122000c1b4079401c0d610b2400100000721303003089150701e070403e840f003d980940c803140d00f10001c1a8124000c0085013024485d16030701800c040410070090b0010b5400501ca1620346103120b00c140c0190ae078640e21502c03264881e031000706448510114540302d580421005410442c2d095030080e107440d0307205000000c40c003908040030758002e02841c03131a82e80d070b50f00341d0007041e1154004142c0c203401b07e6007035495182c40002ca20520305810045840c0c4000c02425a43c0c400340e00000000180140103450000302c200b401d207410340e03a010607070404a980b180d000f00e0b2000c2082c02c000300044001074114040c05410b502090141c5000d440d030b001c40301100c000b4858019080601d408618000300210643c1034440c5c0700804458007095844036580780074400150942d04207555800b070342c40da5a02d207002854480150b9000414040d03609102502d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 923984613 1250 923983363 923983367
    0x30f090d0f0302180405010e01170303040b040602030405070b0a230708040e07140412020f030c060a20060c0c1c090b220b0409110301050f0609031e1f0903 68
    0x1c40c269100081c1600801e4040042c41081d285458400001d0810022907035034a08020300f0420a00c94034510441042c50701001e141c0100849120719005450005551515030fa204001d606c014000d59041c0568200400c0058900c8001c2014100e1031703445e6500c00d28400000b07619402c2e05909155140c80030401d00e40000c40c01010343c0c0031201070f501014281d0390b445000f0307113a0300200301c48181c1101002901040d8528201707461001e05000b030301c004100040d541e05250b521904401460f034880c074140140c180312072195402c2c0ca04410b5006200c40324040f81c910301440c258051301e4034403d10802254844440c40308001003a20600701030054103a07440b6040f8094682e0480d805180b1920f80d000400640c0c102c070002016003030768000e80c3e02c0407480d551004a444550840d00420316042c2c1002da80c2514101e0f10b8080e40d0685900030060040c08007440e042140540c094099190140104941100004402c00185007882c0107a00600408280c1707005c003100c1e0304640c2100d08030561510104901103a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 923985863 1250 923984613 923984627
    0x5030a090e0907031412030408040311300a050a15052505180d060605011202091507030216090b0307271a040c02160b0a0804031805040c0203030f090d 66
    0x242c11081003291080d203402c08600703006d4408405042c552001060004020701903004200f101e0183d200e00c02d014010004001c048849441c11a0520f0380d94141000c804009004058240c9280c4080320300b9040d49980d8141820074403007094a00900243ca550b04d1800c03580547c0b5400107620040c9000500c208a2080c1c0311f5050110110070810041400058070804c0a51008040401400702203420450300e00100a020903001d914006915510040d0140303c1c28020398140c800010301c0c11f9414000c00101d02141d4101c004150114030a6100c4000c02c04040c90440c2c01034840400040f4a032802001494507204a0b58006030810085065403260150f034180074040c8400082c10124080000042d400c00350030005900d00c1d4003c5c609001d45000940014010103401a50115503a02c40c1da694054203050241c0c41c04400031a004130000f0300000e00c41d030210786a2034000c403c1405803503120340c040b4044071480c04c0350030050b84c400001d0041030325801c000b0f0740d0700c042450028001180f0500004001d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 923987113 1250 923985863 923985869
    0x1308010204050306220b01150201060803041206112101140d0b390d0609140412090902030a0203060f0a050102070b090102010603140303071119020904080d0905030a090e0907 76
    0x5c17030704a00c0300c0a003826172051040301c942000e5503800e15619049220052600581c2000c0590310f0620006103440c800b10658045544201203425807004a444002c09882c001c1c51407110f425042040901e0011407480170803107e008043d140e071541d070400c210400340c1003996138124815540a85042c00203a800b410f002e6110301c210801000000140801e59503684401410803020403046154110503500400500400a0024000e01080369100d00c42c01c210b450082c8091b080140c4000080e010517102810301112080314a4170059841c0ea55031158201e03001580c00c131034102e40020910200380b4080350401d03181d010031500c05e400a0b00d032800203036a54103248602c0703060000100381701445a000790310000041d90400c0c0d65a05121203444465180d6104540c0d150100d2a40324074801c515400040d99801d408500780d003203032040365a0b0200203480320028000c42d0503000812140e10309045a00821700d80d2407203440250707211040510090841601da800041014078100100007403540001103140031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 923988363 1250 923987113 923987131
    0xa0209100f09020f0d1d070e130b091e0102041401030516030506150c0a020307151d060f0a08010321020a110303041a0d0f140610050c0109081308010204050306 70
    0x354001c0c4c1c00b40c0001502074040102c540e00d140c081e0b00085807a0540c0310940d0464a1015107041d60344501111014481c2900c2482840403929190000103480d000180c0d080365541c0c2c1200e0802036507043c9121201801c0c2140c54160b5000b150420216485c106081c00c2040c007400d050141c0d240c10000d501032000c402c0a120101a100c0020820645801e1024804d8402e01214565141041645103603900c0c125141280a0310600d03c00040603094000c0604803104184e5a0541080700d10148803000303107091250550040d0704000458582e81c410004002c5201641c0b0344400c0b40d031441c10071840c1910071084003270912040b030039410507455010421002541e8450000c485841c180c0011070f01d10b001d03a8011700e83c11680701e08182516505100640007100d61a4428031003003210450520940c0c869117480503e2507402c4011600030b00c0c212380413003680307241031821343e0403c0381021003903080d9108440182d0b1200800240e401c681c0207180c14a1000d82003002c001d605c1c10780b40a012030340e035407070080c1000b070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 923989613 1250 923988363 923988367
    0xf0e070f0f05090d06020301030c09020f07140c0901180506011b03120b03061003060c0219020f030a060203011401110f0c150f0703030e0f060702210c0f0a0209100f0902 74
    0x2407810300503801d492889802030200f00701c6600c1c41c42c1950080d4020f02080e201402c3c4140c0000d02000c0d01e0080710f0b8030304007849031075040c40c0380c41c3c0e55895083c52024690400d4010810701d28155250400e246000300485817400f40801007154185003113400c0a01000d04104400e440305900800c10383c901903079a60302d80381852451581c140e80c0001801142103c03075150060405214603445901200c8003581c3c000c2c40204400701c440301c400daa6a4203138456980b060000724505501514042094180da040094181d40707441542c2e035a00412603100340c0001010041c9400c41098659100c0c045614541130784004103090281565403903601c03e00718072000e1040443c4507002074094100700607500c0b6000040700c0c0c103441e103c03180f801070007034100c49850403280d01c60142e140000e54000a02c0500402181d009481f02e40d42446102052070402414424410b01c10403200318401c82c108860780070422443d01404441c50548100032161102429502d88290300c6e41d0b05000c1005074207500c500712109050010303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 923990863 1250 923989613 923989637
    0x906050d060f06050c1213031e02040f0507140715050402010c14071a180112090b0405030703022119121a0901060c030518120303010f0f0e070f 63
    0x2001500c110b4200c980701c1c140303055000903800c3e0440040c00f04c9075009401e0360851040a08280751500405000740030407802d10400b080440d498135000b61050300d5040d100003a042260b004141907400040390f41454030b50300e904001c0210303440241c10750480f00740944c00f0702d0b100f11911007203125004400d00d40c2c20356603500049000c43e8020012819003075400010030400c20700134800c02d511804a4420701c1001c000f4100052a213242d03503030480302000c0814008900c00e562003c0110f03005121030040c0c00c4860b035160403a00c0402c00c2c14542d64403c500c01c800031699540c1524000741807005464041c4010034102c941d21310000d40000998507131a204044070442c5040940702110f00040c001504140c00d4584003014074400140140104502002d440b03520003640e07502d2084501d0009250b010780044d405110400070151450108441600002d0041d1200d01c400214a41564000c0e070002d19100c018500400c401070508031400c0052940d611400700904d880c05003d03007070118042c011820004003103500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 923992113 1250 923990863 923990887
    0x5090d061119020304050321120a0b0316051305010e150d170306180c090628020d02012a0f140a030902030708060403093804030b100303090605 63
    0x10303a210b101c1003440c82c625503a00e444065181ea00501805001c1d001b0028a10340e210707480d5a00c0e070028101080c080e403414130003a1003100030307210140c4032150032a1203200c0407003a954200801c07014410b40000140045103003004014480d0b504a261203102c608100040001ca021403200030791018403051529030f0b10910350001440340c14140d0004080c05802103011003001440000703540310301c40940b001c02c4140348200b0441c01a160468054004000401c0481158107191001d807070308160031158100c6218001c82104182001e04560000603844443e07001021582409800c404002c038040403592a8990151020030724440940350342070006407a03a040312548207002e07840c40d07464032580302500c48860520003809421a81010382c440d101e8180c02140d9034502243c2c080c080c56150311180721b90740c600005403007554250222170340010446480b00e07803480890f05004034030110341c0d01120759442c1140f40030000e0341d40107030a191811480e00c20600000c1d03045803169040d120070341406030300e52494540e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 923993363 1250 923992113 923992117
    0x30c07050a05100606080612060610030905030c010207020910050315040203030d05070f0f2a03050403050307150c020d0c0209060a12120e1c020d030302090d050d030b0105090d0611 79
    0x1004015219410303443c010002c01d0341c001c0e8184c0b4541e03075404101c0d488003010030208118400300150243c01070340109251749091152405034a40034200480c4800c241d40b242ca055420003001c0c1815030b500090b00c4021403516528251b4808804108003500038241804a41c1d100d40009082a503040303204081000e56138204103031014003510010a00083c9000310000b042d084500032401c0201303e502d03110504442c060302852101c0160220101481403401d0204010120040e006034103000e010080400030230014001080c1c882d0048c1000c2e01074130040c0ea020422903103c1c100100440d000491042e04055011100c0159640c040701d0030000d584034075000801c500459403098820040d00007400040001d6101c5201e290140d5031900551161100f061002080c030841c0951040007500d01e036180185040d442c0070721024000e190040c01c0030410008140c04e5007007030b036081e92a580701078218801d80341c1c14014510000004e203402400c0c0b4440b40d012613040c11440b40c004028a840e0301402c0c984c0040101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 923994613 1250 923993363 923993383
    0x11205071a070f1515210303020c120c07091413051c0e0913020a0e070e060c011508071809050102070615030b090c06032404061424030c0705 62
    0xb5a0f0082d200c0c0d1458402610040000e11240043c2090742c140300381002040c00e03400311269a0101c101441c001012501d0f64114404110140b690902480d4507001040000000c2e0b0088025510b594418040c40145410456809140e940741455807031030500140c000b06a400039090000000740d04003c1c0341c52420840c0424034074255101d045070304c3d080303140d001c0d20846880006440c2c09803180c560901070310400d00c078140041d40001740341c00c0400c040b00e09040c126911018914164030500007420029a031070f4440e41100125a440b4582171141e40034020865008150040003090090300e030407007400b07a00d0743e94982101c5460742d07074601780d0500c80b081d01192030166200000300024000307616401c0c04e2030541d0006491451041000403200000003074500040b0b5001000c6030b003160b6452400291068040003000d8522419403000702c06511103000710000b070043c021000b5850720341a001d001920810401900c0b101026800201030018070104582e00280902035403607a5400e241401860321003401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 923995863 1250 923994613 923994623
    0xf04060804050c040e0102070b060616021003150b0301231c021203040303170c0c06040605091c03061502011506080402190906050405160f0e150d0c08011205071a07 72
    0x3038240391300070419801001689d200d81044441a00e403035080c440c0c00d00035078421003000c24003420b100c00907180411101003518007038600402d148071003a8845020380e41aa10025050300040010b01031105c40c1c404500c0410000394181407251500d400150607400ca16074450f184a252150980c19900c5071000d0f1540c001400085170780d102c0e502d2400501010755083c191440001c04030105901881d41030444007085107074802400b544c0c40d251203039801001c010304a40308600c1000d6116800b041d018104ca2600e103c152400079007640703001d4049640018040324182164035003a002c001810800c12040181e03907041c074003800e09584900c080350300c13035016034500d5240315201c40000500c0d4481d50810320556400b0b039000d010584505010401001c5a0000d03403010a050000404045100c0c02070320700d2240700204940b0b4072188180301400990f01000303d10134501d4a42c8403501140b600a060780d0b004150304403480d00d03103c0c81c6807a41c5454801b640204041c42e1b40300483c4100c03480c40401a28036594000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 923997113 1250 923995863 923995871
    0x61501030f110403110904121404150f02061308041a12040807020a0905011410091203021506061306030f2a170c04050114070b040b1b0f04060804050c04 67
    0x114141c0307411510085605c0032051a42c1c02d060309180070610300444d400120b580d00100c01507000e40e0b5204892400038800070040c0302c00501c2612140030a0b190b4000f40d214100010041d900007070411070001c0044080400c0d0f1110040000c2d1400e0480e000c4641b005414500d0011f04440144a4812200d859410340031107000e110910940c040240021032080315110340c5c0658404940042c0d030400d1180a01f490406902d8880c2c0d410031024014003d5054500b6110483d1544c00302220030300c8500f41940182c1c05400064001e01c5a02d9007103412800880e00b06080c241160403801e0040e100340540300c200b603100d1001c2404901d083e08002c8000e55150038810b00d14445105003130034400803003400320000c0c050040360818011624483c3c1c1c0502080d54185103040d04040054801c1540100304542c0c0c008100842000300349441502d80c015481384200c1d4010b410814404088403c081001a10114003000f0001000c0441812035003120614182103d56640b00d0900c40d06064030003903055005420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 923998363 1250 923997113 923997131
    0xa1401060306110a080a0c09090e0721020a0f121b05030303070f081f0b090a0315091416050f01050d050702060a0c2124080303041101050903061501030f 67
    0x20100140484134220b82d00c6140d00d03030700c04c500707001030314004118400400d0f43c442091281c840c0ca0340107407894040e5076040f65405c6980341d111200f1812041078030201c03d020307540301000b1454000d19080003080e50b90440010035083c554200d0f0184d1324030000030048840c14030b000200c1105403410707000418000b010b8a07128600014040c0880040001c1d050006000100140f000b15540122103040702080e0310200845043c480d410016034410301100307500c4400442c001001440311381022012914075200468511514500034101c0400258a1000c60308003181405080c2841c100b218101c40c4121190742c01000d0101c0141c400740301d00302c0b4000201c0e0800c01001700c02a0001402400b60409600c100548001481c00b2503d86046058206240d48100c1108040b4003017034200c0305188090559000060320300d403620041059440e4032155a68201008000a200e1301d0304004c1c0a600003030078904e142c0340201d400662a1240102085207200c1001d01c5885c05074800da102c401941e002940402c51100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 923999613 1250 923998363 923998391
    0x3120403030c0c050909070905090c031f0608070e0a1a06030a150b090105121803040303020a0209130f02010f0e04180212030a05030c030402040908070602030414030406020a1401060306 81
    0x10b1003042d0741d160510701c0005914200580d9052041c1c60040141c03903c1401d00450f41c010f0b14010f80040d0880c800d140014400c0c0e80e00303100e004080c85400003071440d4003140e0303181441030314043d0f805407007030390468401008240e1072000726a500c2030303120200040888210503000c0b034403401d1240c001d400060100c10400300003410351142d0000501041c0d48080195200c3c150b80c071900c2117203050f50016a0600101107441040c5074620341001c0c0841c0094a203059101c042c41c42c503001a4815001a40300070b240e2820742c149000259000b890310141c0c1d00300c0d60f4840c1c54030b03d0381111910340241000070103406404400c1c8580c121281c0c3d000000c00038828106081031750480303400010790591244a0385040c03600c2c0041700004542c218103540d2111401d5603507125464185400044c800c2e42c00c82d4480a02000090f40400141080c80c41101c00580380d0819003050a148000e42c004a03440380c6c0b08200071301c0f0b0541c0004100ca0000d13403010051944050f1084003074050603069100829003400e180820784120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 924000863 1250 923999613 923999627
    0xc09220e062a2508071505160e0112060302091f0503070b0a1d040216170c0712030c020405041223030a180221120a08010e06010c05061609060c0209060904020312040303 74
    0x4000744c6e001d0105460306418070414030000151030001c221761040001c41540904030004803140c070a407001800300c0d9a9000b00e6040002211072030f0f851002c60002a19001c252508100509010b400401c40d0710b0a040d0106258425101d40c03800b0300c88a00d84035140410b4080d000490148003900a640f240340c030100c4c03a000a00300640403100901085101054208034105491800c031001004021040c40c01c40307800d2418150101c01e6081100b01040c0e0005600c0d240100760165104214401c1c02510b443c20003000448240051030b070310100e4100c5900441003107001d40750004101c0000059100c0c407040340d00002610014001e42000c208242c04144c44a00c0695020300c40005041d0f81c0701551702400005584102ca484001154030b0700c00500c0094026004282d01c400103051154021020751261403500004031440350fa2081d000d00d94515181d401460180203200d01c1c10701c024413030066400114400802419075006a840c000080c05655042040f8181c00c0a0b01966036501c0b5203a09000380a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 924002113 1250 924000863 924000893
    0xc0d29031207020f0405090312041b0501020a1a090708010e2107050304030605060d0212071a040806060607030917060a050c030c09220e062a250807 65
    0x901070301c00c0c00d80740c0700490011100081d0b40200b0890f43d0b120441c04100041002801c036034014882400400100c40c1c290341c145024500444507110410340d520800d68510819410103070464200441c001c0c0020000c89107941c0803000714003c17115569070085200d18000da02ea129140641c01d0200c1000805804a85003e05441031643d050030b40b81d50741c482c0c5c2c03201e100300e0100620700c0d03200b00400c001094013644810340019005154180b1200c942c2c0009411991102400c41070747c20040c0108068054451418003164404940f1424945030410107500c40c40d0041c0882d010760000540203040512800c0c01e040078050034020054044807040c04907540380780807a1010030052609000c505140401350a032886038910455952600c0d44060a02203c10440480644602030180b25498038440c2c0e4050074002640c14030042c150b03440c0c402c03035034442c0884580c0a01e402c118000340c40255003081008a84900030301c03004030a20605a01c0055002150560000e8030448004c03c0d800d040220381c0741c0000c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 924003363 1250 924002113 924002119
    0xc03110a090e09010902030703030809070e0f07020705040e070611150108100e1b06090f061b100216020d03050705030406050d152114010f02030f070c08030c0d29 71
    0x640d83c2d000310321400c8803400034020b945584008010000a031041d502e007984a030f060415103041564a42070040d25500a41d070124031403a00f6010001c0d141c3d81000494000c1104079410b01a0040b05d1420302d0722948203000341c3c0f00300702e15149000c0d4802c108105214088401c0d840000a6680d1019645e48484000c62140310b814203014059041640000b000000c0c080031528049071000ca000403c0b00961250b02d0290b005002da10008940d983d1300d5001d41008000e68001c8035946400011050502000748410070030365105102c48044a400d14000110b240c0d03040c3c2d40410709020504081e105401a0718000744036210002e004140190f000c80909040ba244410900c070620800e480c03408001918052031000340254412007140d64011240c003012180203030040800075040e41105d41c04c2d43c007404003900380340790008280681400c21005143d0301520750318009001d49490398a984503888040c0071804056400f05920751000710a174000b070880c03441c1c01c80142c801c20b511110034031001c4d00360100d548 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 924004613 1250 924003363 924003389
    0x90c1115040b1b040b0a32250606080d020d05040b160828080115140f1c150f0b0306040b1f080603240105060a090f0611070b0c100c03110a09 62
    0x41d000147c42e40304044051200740d060620307914402d59940d07044481540303524079043c3c681790404074003d0f1103020040c040100140c00e400c0342980010340340140c400d0041080040802081020b80f182c1c0c020350301c0314211624290144003060519a141c0d02512070a8181038000c1d401508601850144000c26a01161115204c681c2ea5840b801c1091403081d401e0404206084142403a030b01346400148103407044c1c0840503050500040399099454810713142e80c914180e64032014140703a145c030804c10b07000b0071072035100c40780e4141040d0803404507000280c141c0c3d0040342c6030a60b00306603542d1109003940b42202c00600c07104d03800c280b200080c06c8132016207030b40d0300078040d80c400c0040c020380a0355114242040c09044401691074030742400b01030703070018a10804000c0090408110285070b03501c014010b0032240e440980c2c507010009000d0420450f030380000f040700010081a11600c00100719002080c5200c6400120019008001d9001c1d007486030410740704010006462003640c1d0000108400d4440c0b51400c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 924005863 1250 924004613 924004667
    0x50c091e0f04020306040b06130204030501020912011b0819090305280c02060c01020c0f030304050c0105180613052716020c0603040c090c1115040b1b040b0a 69
    0x5114507400d49020390150889000a404a042184d0082d048000a000c40c203c13031800515080c121f0f00700e03410884461750009000c40c2d4500d041c0505d801e0500c030350030007040201e0203a041034210010002e0a0414001c00c4400104c20b000404100900d0110b2400184283d10321444d008026600082c2454100c251001c20f15018140d04200030b08a01030039103400d006011980c0802c1100d820200080026640800c050740ca501c1003403000c041c5606130640119207a080c10701d4034904080031a4521030400505005402441c01c050952000d60481940c0c013954031020172a08403d0700348550007068024024224509000300001c0d082000f105030880c4449481e00d5618170154040c20400003080141e011a15a039a03628040c4000c0d41c10600c25031940c3d0010303030707600c188200341e9507500b200c0340206140700800c0303540e19410b0010f02a044140c10007864245040d907200301e801d60f006800000750346610140c045000f001d10048a000d08001249613460342c841031001002c4064002d0041c0700c000201c4086 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 924007113 1250 924005863 924005881
    0xe010f060509070c020f10020706080c0712120213060807030608160302061b0706390305090609030106030804050f0a1d070c1a07020721080304050c091e 67
    0x4681074900081c040040c40e1600c00d0216128a00381e9030a90340030b406289811919030350f0706002260880603030040d01d1014600b4101900050004006021241040000e040010000c1840b800740e0022030901445021020050740002d000301c0a003030003000d15a03000450803a422114041c4920700351ba5040c00410b8403552441d8079810000707000c0841c4d8503031142c244010f140c03000103040f0100c1081e0310056586404880207140c104180e2003103010408060582c408a1045a20a082c060480d0800e035407001308804c101006c54040c10000c0c0c2000404103076000c0c60f82d69a821141c0b101c0c07009000f400015140e04021581d5409885110720804c0e00c11020300c00c0d804c1850200303040351244a034030f038941d91030600c04406d8404010500420070020f02030002c0061800d18051039070000511801c0300c14502810042d18004060300218403c8070600300307100b012541000007500c41540260b8407501e0362201c4c170b806403521101e56101035200314410100a0725040a0f107481c0321036844070800301401d0300c41c9104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 924008363 1250 924007113 924007121
    0x1a0312030606030c07020603040b04290f040c0b180f010207120305180429010e031e010e0319092705090a02060c030903011d070e0a020405060a030e010f 67
    0x202101600051002428515200014550002514160502d001032030790024040d90300440f030441782660444140400d100601d803407076030708010f855640d00c3c010034580050300c08208024602c10400f9881400502048030024242e0000c0240600d140d45580082090080341c03815204a0b40c0281c0c00301038009859071000440c401102c41b2405616942c6140b610215020f40c4802d01c240f60410b84098801030b03907242c511400a0703581c1103184c07046140c403082d1403900280c840a40d4042c100907031091140c030280e5000c00c0d080208880c03081c0d4801c201c40b008924502400d10b580c8110701c5404041041c00480030380c83c0400e802d260090395580e400940340d21004848054403243c02c601d01110b05491040c87d092a4001a0072030141c9003260241d40e0b0b04d0340041d145520a090501b035507000030034020b1090809009403002086d06085505c02e1000d4415a80e40d1500d051103011480811000400c0c83d001540c0c0c110b0300500b9020b0045517030b80854601c0075020b45070701c0f02a0040c640c41c4c104289401c52603882 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 924009613 1250 924008363 924008383
    0x1104051015022e0f0506030d0c0c0f0807060906030212160c060c09140a0506090f01140705030301030b0f040f2009090105091504050319090503101a03 66
    0x354a0495a0030300390405441500c0e442aa42903204240c49092880740381201c080c42c0124401040400058401500d030648800103090030f1428100414420795540124425070807015925001c451010740d800e210048d5101c80d803215000f81c40f404004070381d1410109240007603070180d07250f1100b52130f51010110104c0c802c58145451440c0e1038000706440c1803c6105950843c0038601c1e0486680f00310b901c44204507080c084882c0d0214440d20343c101300c3c0307008034a802c1440c1c600032141081c08500d0603010030402e10441c400c6074428020000c00b095582c0c098210307821640c03050490f8903200c80311031070110f035207a1003800305a9040384058000342100d02a656400e104550125100104000994a040541e08441401c2542c1080b400d0749549a4031111000340c492401e54001040c3c038101381110744e041044c010400c4880518007030411010810001c100c0341a0501520303281401100c1c150200d030f02801940055606000b00745400c04042c4207078000d040e0381d40003000c01f202c24140c0c0307d0030140d80346103d01f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 924010863 1250 924009613 924009631
    0x110307080c10090b0a0c15020a0c0b0606040e0106030c02011d03120a20040905010510050f0c0727060605032802070516030b01090209060405060c16080703110405 71
    0x1c0c5008105050440005207000c0e0039007441d00c041c84c2c0340c0c4c2c06400c094000081c540c00082c0c010703400800748561402480303603c000c1190b0071490314038900d500a00700b100303012010303120fa14441c000c00c0e034548400c802c0350000d042040360f05070700d543c4564004015001d01c1c80024015800d0013088046400c1c81c0c0290700000c6020070041d8500580b08940102c12807005103160021550350004004001f240420640409800c01020ba0f4a50030500103104880060700000d01400398005941c1015400c42c00308c2c0c50781842401ca860300c622001c44007130710b012815040404600340350304404880000c2c0ba210f1100805a0031020b000d0103403510421121800200d808c803098a40ca503448413540b403440e0702e480c0e04808081c200035103403107103648616282c0340400384c006400050f40304041041c8843c0f13582035400340030745003010352400c9449000035141707000e14098144140d030001500c00740907608001ca0f030100b050000c4580350142d40d40c0400c03610b5810901c825284949802107070142d0b450948945440b1788451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 924012113 1250 924010863 924010873
    0x30a1d0f100c0b090f1605030a1509080d02090f010c02091824180106060509090a091709010909140103120513090c0e030a03171518010311030708 64
    0x50300700400341d6211090002805184000e120100d5048241c080c400c0c001c0308014088140d40b20300d041d01d4500d10f402c030319482a81500040c81769035400320300d8080c5c0a40000c4102114101045140010b10341c0c0e06004150400014500034400c809401420100404403181d50014210100641d0f5241017948001c0d0b00400540008a40300d1500256030cc02c5c0104600325080404030101d455804403541072200701c620003060030007100901e480a81c01111002000034050f240c40c0c901c0142082c01803c4005d880b9803418000221003070180d40c000304c001500809181d4030000308016030f802e03d0713001a02c0c05002980030f400200d10b03000307203004412001503005a00d00d142c0e840c580310041d075611107900c10307420001c0410000b0001032a411009001c4c2c80502000541c0b0400b04d1301c0039001d0000d1007480f5019400002e407840200c1c0e0004010907a0758852088001036940f403041107902301e164911038584c080503000c607016500000080c114145c80c0304004074000d140d0b040c0201682c80009104801055200d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 924013363 1250 924012113 924012139
    0xe060a06080a0b0a1814011b020715260a0f0c140714070e0a020307030c09080d08072003121003210302070204020307031b032f0c060702030a1d 63
    0x42e5200d403840305c19000e140e0003d90040d54401d92a00d030500c0481006a464290f404c11512101d2405081d00300d59000a2400c103113042409007000205a16201c240583d011110b03007078640e2003209072104004030744110814070704040144018450050280300680c54130402c40e880300d0003038014050742c411b50b0011505007442551117410701000018464800e000e550340020710250070380c4001c0d0050012400140e02d0381342801c4003c007250700081650007000b103d84000c04c001d41c400f040103030400d405840c0441540e0380b120016521030200b003c5c54031594a001039140bc0d0040040b020780840c9850380703c901440e44524512082000c2c403404081e01c0243ca0200b414400e00040203500440c824900b005814160345800081c100d8004a80440200361200302d02074003911800b9912804100307070b040030400395450456100581d10880180d1468503194801c0c1440304019005030760021600c0c40841e811881c104200039200c0d003000f12404040b8103c2031181ea004c95040f05092000b440107010807540b490 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 924014613 1250 924013363 924013381
    0x1509061b0f060209060a1106130807020d0201020111030c0a030e070b0a081e01090519090b0601110c0a0603061a160204051f080c030c0109030b0412050d0e060a06080a0b 74
    0x980c840701120354607401c00940e896034440e403002c0d14080e03010b901c6202c40b06d00001000e50520782d00916000410355012400d20003d990030059031881ca4040d074454a00d6121440180d00400340d40c1900652500c0101c200105010440011b140c0d4500d00d9030140701c81d8400d461410703511000e41c064452452000d104100303885204215803544200c00d002041405011460440700f011401e80212024035241c9080000c04010f0301e8680700f814a41c0e003020054560183c40d0400101005400c4a0407c904643d8660b91030000b000024007001d0018190f40695a032501c000d001045140f04403240305149000c0305684d0702c0800d0a444103e02d400b0125004200301e9400c010040400a01505a0704141c0380042c0d40d81051f42510740c042d004070700050400b55803402c10540750003a11604a81044072004003400041c1d00001039a8101e81c1c4a052600103400b842421740300c0307010701a04144030601c1c002c0101c00c285400140140942040b080820106031680f03041501c80000c0350014001234842d00204602c21 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 924015863 1250 924014613 924014633
    0x19090b0415122412021e030a140f070506071a070c0f030801090f0b0f10030b030312040b130818011206090617011407271509061b 57
    0x108a916120681014000708001100c5140c003644401c0d20300d01c0700b40740400c0c1c1c403070f0100c0e40500325290000c8081c5100c0d43c000b404481d03641d03405840703e100b50320070915507450820224907810741c08081d80a0100940d406a0342c0d0f1900011411418440d071000090300341480b1044582c2580c102c12401000603a02e541c0664204002c1d10680c100408036a6003000f00301050401040b1034800e641d031030050b52401110500380ea00c554000d42c002840c0a001c44201d5a8000c0101c490340c80560750000388805004042c1c005241842c0071541600000941e2107400c41c1e1141ca03035100381d01c22005503c041e15541c8503010741c08586440104480781c20811580280301501c24030700314400516240004000c041300303203000d0741d05580c403008045403120010b1101740030f56091082a00c00d450002c1108040d80d4140ca43c0010000d4543c60034460f8130000e900008018a4458043e18070000300341104903a540c403442c0c0c0942520441d000090f1907070102250345440346900e0f0038510364481c5e01002c2034140c0d0700c80d82c6843e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 924017113 1250 924015863 924015899
    0x15010801080607030b011701061116060e09061c0c1a0f07020d050c040e34210204020a090801180c0b0904020715051608060102030a0c05010e060c19090b04 68
    0x48907a40900c01c01c007d03004882580a000d4685e00c0002c0054041941440c00348854100f02c004200f030a424001142d1004c15181d000c54111800b841580712030340411b207201c4603a4821201b1032000350748001071151100709007080355100001d0b40c83c407203c003225040d541c1c040c404503812448000c0042201502d8503042820030b490240701503410640c2d00100140844254144220980d0480301241c0301a1000c8544030b620300709424840c4401100e903150031800c3c0c1d8198080e8443c030080b00d0504502059429000800403035028204558580301860003601c0102148503160140d0300301440c82881d02b94002100742c01780e50015000b68864280356110000d9000030030281c2d003040d0309000c1c203804074101c100b02c1051780600c40c40000d02c5080c0b54101683d1405410030481c14071401005114550f40d00004840c0040c100e40703004c4400d030060746002800b514a000c2024100d1054005105103840f12800900f00c42100c0c88002513040c094000913103a0714014811a401072005000070414000300712421042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 924018363 1250 924017113 924017117
    0xe040902040e0f07090614031011160f020405150f150d150311190603091106030405010c0809010b01020303162a0221101512060515010801080607030b01 67
    0x1101002c045080d142c54004007040e031039903020b15401c01401070240f00d54406420000c0807484880070311400305e941c1d22015851180c0c2c1d80e40d100304181041501d041542c000f01c1c550203610714143c41c54100792000011400040c1d203d20303e4074000c80c41c24106c014404814850190500350301c07401800400801400d02049074451107410440e00201c040544940c2c110b50100c035040100040c2103041402903100c42001e02809613041c003049405d9a401c8415035030031209145808144501c592a00081e59800200e10701c0d04081c0200c00d010070428190820700c2d00c14035681e601e0113280c1e0b58902035030a07100e0100940303015070420030100f207101030b105464100d6010181404131103400e0864003200403c2c24806800c0040400c01001c50861504203806100d1a8100c0c62409101810518064840d07801000404007640d88942a61501200c1d413449002400004031020440c000340c01c242e0068801251080300503900200514032660050260a05aa5a500040000c2e90b0340440550080468900d4141 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 924019613 1250 924018363 924018371
    0xc010e0102101e0501050d1505070507061109090c09100c02040b1507060c08042a081006030302070b07171c020f1c09120309080c0a0615090b010e04090204 68
    0x22042c031940111003403980c442000504049030200d203101220703010707040343c0e100d5072840b01180c02240210a0505080c00b0305140000da0f03881d03001068600d88141c40c401400c803814000708501c454004009480340c10002d440701e904075a01c115154050f4400c0d0511103074010608065004040c0c4180d1802000c01c0c405440002e0004411001850001c4c06042c0c010308258001500d2003088000d010744140e02c07041c1e00b095a183d040903560700e0550080342203100940c81100c2d55502c0b44c84082c1b4141d10060810b44161095664003248900281c400e03400160050b1080e030300e0001728960200200d403a081e801040c494130002c482c0c450b0031601c0d40050700000701c558013527504481d10402440140014080d18903e16a40d26840c01c50f20320810f0f12407207110f401c51800761079a0208010380c0810002c190319107000162402213152a8200c0c1c00349007109241da1207441003140410560b580890019066a00c0403d641581c0304481c85c01c4d2449034104600082928130020300c0760601d60080d195040c80100042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 924020863 1250 924019613 924019633
    0x509060f04031217090703031b14160e240102070803041203030e150414030c1c111603030e0409060c09090c0207080606060903010908030f0f07110c010e0102 69
    0x100260400c0d0819680072200d0761884000a4028503590103441141c540c03482d403481c145c24403c1d20f808042c4405400c0c0152090080412400c208507a40138a5020a454960400007052550b4488418a801175a003d031624003040039a412000280706501c1d410921500000081c3e07180345070702100c000c0320b06600c10b160002c60492010300280c4058a08444c00c080c0400c0c00f03060043c1038481030000140c85402259012200006005050758800e0300104000c1c90004d19094041c5588110b01d40306403a4012000005200350401c0020111001907540b25540b01c80000d00f240e03151423400400030180c0c1c030f585a007000081d02902040b021000c00510000e01810726031205010b44038080701400003c0e40c034620600140d50288200d0600103030a01c010040c450804039410f0b6039020180c0100e104000200310100713a56002d4104030340b00c03036014094a80b00c0c01d00100890b0804010740c1c40564080078400040c400728850b5018201d2841100000d18141075140015590018621304681c114010702c8122 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 924022113 1250 924020863 924020887
    0x2031e0a050f01050f070302040302011d010e030102040b0301080c060306032107060507031b111506030c041b03050114011b1110021f05040206040e1018020306190303020d050906 78
    0x120b03003603050003001140500d000e10200c3c46184000344018141407042c003062002d82d0f40180852074141c030141e130040c802d10484005075034500d061f07400580d05600004001c52401d0254000e14100e0720060121038100c01010b00700121400115101d5070581d100010320810908000c0d085a0320fa510410114075007490f6480d41030560b041110701001190300c84d0b00d4810303442014503001024804d00c1c82c0c5500c080c00c90025030703600c2304010080f880036401040007041040d03170306118021610b10010010801c0026803802d481c4e000782094000800700f89400b00000781c491009004d4134500005035035043c1c803040f0002440115490340d50044e81c92400080b0b50102c603441d40c80b411000c1e081260010408030722850224000782d05216207110030681050103101c0142c0328441034078192001c059403e03d0fa50b90b03002011900c100198010519481003110700703052000c0d00e5005600441007a1007074402c50109001d40b0088050a01c0028010303805003d10040c12440344000d05414480205914900b03280302c044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 924023363 1250 924022113 924022123
    0x506060f2d042714160e06040915090612060c020f060c0903010f0e030f1b07030803041109041104021b0303090709060e011805070c2108090a02031e0a05 67
    0x1040141e8108010701030032482c0340c002c0070207903800710300500004a07204580103a190001d0400c01007205c41c0360640c038415004401d14080d0343d0007d4609515295103400200140038200100101c00300325500c08101110240120700c2078075840000c07019400240d90f10540104040c20f1072070114096441c3c6424209000c0c44118051046001c4042d11480e641081508480c00341151141c46031801c0c2d0010460764002c0140c1d1140d06004003070030780350484011070b4880c40212800403822801180c0f004070420904502441c019401880a414544012000d01500c808203460142c900070303031680460703094605500140710b01c00c0240118141c0d001b52480b903502e941c0064a42890302c4c0c0100300188001001445040b00038002000452400d52610480440c05021a24151600e0ba101d0002440f11400741d04081400c1d60f014220500d04200c0d018000b0304001c0700d113042c000144d500c41c04510043c1001620882c007603002409800d1010500c588003801000c07500d002c3c0300f980500040300d8042031050003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 924024613 1250 924023363 924023369
    0xa0507022d10030b0a0e06150a111204050904060506190905180a03050304080307020106180902030f01061419090e060a0c0801030b04080c210901030506060f2d04 71
    0x588902141800d4100041c10030503000210400d4504003120146564009403102201c0d2038406c50141d940b12103002c543e07044034881da00281c0d05000245402015400010100c0310708041c03007036844c0d0756042c00c1112444e1040e40308072075001600d0001f103004114a039001c1900020001e204100715000340c00c100c035004109500c00d0519540c0c40c4200109003603035144901c04402d820740030340801e200c16a0f010b026030102400c080d102460101c00103210350b000354440406051040030b0031840f2000804020058110410100d009004100120900035014001d000c01c1c0c0b40c0c0c1080c000741c801c00f0b0106110000f500740720000480c0c01c0481c03000032007054611802070940341e100042e0038039261110241c416150b80107186010051020010004100034107560764106501804043e5a18810001035240c01c1d4a81010103205840c001c038071029403c8034009154901003138030709001590b2420100446809034440c0180560b00400c040594030b1801484203907041c60044000440c2c281c004481119500306070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 924025863 1250 924024613 924024679
    0xc02120703020901050904020123040320040c1107051c06020d02121503100c020a0209090f010b030109080a03020307201f05090a031407150b010e12030a050702 70
    0x40501c00e6040003118540540707010f072032401050a16500080c9071404401c4441c5090005c1c800c107107503880b41502141e00a60f00b040c000e900c1455400c00e000c02d1100d807151664440d514010342028140d014500346000c000c3c0c458081c201843c40d00301800400ca10072840075400c0000c0407019400108644064215004071000c016100d21214500c1c09117001c0c0503048444540c0004040c2c1103540d80010035030baa06800700c1c00030401e5011201d0a0b8540320170307800002d611155000130090030204c0082c841000140f00307c001d11245624005140c220703081e0990180c05c1031f60820010001d0f0b406600256008001442c02c0c8141c03600b030040d0402405401c40e605040da070003040d02c150321442d071000c1103d0380c20004c0d0020803040c24080581c680d29150740c0e5004051061308510360030380310501410b9400040d00002c0603008128140b40c000000c16000220b5400b1036401c489a2100d41406101509880740e10b80c0190b1400d002058203441d560441c0c07070126402078034007401c40c121302200319a0440400e03284c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 924027113 1250 924025863 924025873
    0x10f0504060501020a170f04080f06220209040609240b0a0515090d0602041208030105190e01062703060903020714030c060318010903081b120c03070c0212 68
    0x86410401900c0c071540c0243d046511440300240860303415124000191041080d0301d50b95540b50100c05240d020b141c0c001081d9025103801d1203006131000c01c6203881341210824480c0340010030b507080300c2103101d41c2102035040305400000600181403031b4005e00079240508240e04006071190450180111130a0410356581d0700e4460a600d2403d110710803002602003201c50444031006004038040078007840300c045125000003c014400d00a00ba070444000d45040c1003603a0121005040c103080310342c000e2068a0242500c2102220b8003415449010180c400340084020329900c0c00000f100d240060714001d144c0b40c07840301003070041e40002d070107080e006511420001c00c01c081941000381c106000c0c0c1d40007a8550342d4500450b081607802084155079100111502520380d00e403410180181e400c802100745656207418007610905810100c1076128401c0b07200c804502181d869407540c1e80340901d03094000e040ea600c401007412000c4031009954000d002c3d14000c072600c40320340c0025000c0081c1a00c807406039001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 924028363 1250 924027113 924027119
    0x91501030302150f060607020609040e070605040812040302010e12011b0306031109060f10120e070e0c1c0c050d060e07180f0915030f031d010f0225030605010f 70
    0x10788125541c2c080e1004d01c1c907411524050b804203441e03200e402c00c028071505001500440642d681e1f40a0344250000c0750864000710740343c64010b01280e00600645441d0b101b100244030f543c030070b5481120140c3c1c1c0d0607516401160158030600c410303c502990100d80329504c808946c42984c0d20f0105c1c00201071104d5034046901c915504069001c00700340d10400340150b800404124550f151024042e40d004030981d60843c609011580484401c288411509502070030051090389510707000460340240d030206410702115403119035400b0100e11a043d18207022240428250001a032607500002d0301c580c99041003450700780031003420411203d9581114980e807580c1402d21008582c40034050411402c0745051540031400c0003800040c05220f4802c0d8940700d500c2d504170151201c1d41c04410380040d50700150000d20f403100d0b403401900600781c0c1c21030b1400220708044118442c0d072060f40d4181d0400085d40142c1841c00251900c48100d5281d80956403040705500c00000008200d442554000c001d91500341d2001d5003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 924029613 1250 924028363 924028393
    0x313030e01020a030e210f100b2416020916080903131a0c03040611100b0639061602060405032d0403030e1801080d08091501030302 58
    0x203144034880c119885202420002030700407200641c5204d00b10360480303400c0185e80001a04c1e014818400841e8051010210401c290000e05841d000e4031146050022070410360500101080501c0b4002d02a07110000c5c0c4520f45200d8030081c90510704440815001400d40c0d004121005404c0d5221040c1900d1580400100366124407403e800c104c2000181d864042d84a0128a4a0300305008a03040d480024403000324410000013260004011441604e44440c0d46520241500c007450303020034036500400300d16200c40d400e1803080a802c42e00080c003190501803081b440c42e000205508261000b09071710040748921040300000c0da062081c0041c0100014501101074000c2540c02040902c10356029a041c000042ca01100369003002d0301c041000f5032170300d071840d1b10134040410803919000c1e0040006004400d02d54851518a4980c0f402d45241c1030082ca42410b01c590f6a40034450007409802035a11110080d1103070815680094560003161800017016881d0300ca041001c0e032080380035900c002c6000c02009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 924030863 1250 924029613 924029627
    0x110a030b27071505090a1703030f0a150306020d090b1302031504020a030f030c20190e24130203060102150114090a0e0d0f0909231902031303 62
    0x210560000e800c1180c0303001809120541c418001200344000491714005685460110000405e46c450020540441d01d000c4241c4991060300d0381d5a40000840c001401001c2900440e01030560000c2c202e07240c41c0c5541c5565000303410103540b0b01942a107a45508012480c60381116024181020420040c40c2c1d031441010f140480000d00620f60440c00c80800015a48560380700080b25044469a5400b424a20307048a00b0b400000c401480c0450b124004951004400c082644001c0d00f50b41803c1f90000360071400c000340f80640320b2440d540c119500020524121100c01ca075401c07011100b110ba002d950381d0b000600c2202c08a603100103813507000c8208581c6603070400c11815442184000528994100a03070118488040444a8091820040880d056208a0b0720000c8000205400d641300c0044610f0010300800081485600151844c2c0d80803c40c0040c6110303440c1102c103444003850820368585603c2d540144001e0021450034000c0080c00588a00350005620616034100940402c41d21490050551 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 924032113 1250 924030863 924030931
    0x3030c170f011217120612030903060411010918050906060a0b0409051b030702060103030206060102070806150609060a09060909020304030f120b190f170307110a030b 73
    0x40c01000a0188410560100c541034a42e01201540042c840342041d2503208081c480000074103a000544280309614600c071079001303030400c0318003074800f488016405680740950047d00d40c0c1034100d140400c0002304849826172408806042006110307640382c1e00081c071000c94100c3c00b80380703070784850400c244580c00b4440307198409000c03034482c0c054505000300707500c06002c0c42c000c8100703071a690804241c1907200828149059180000026624a0f001c1c60094603018280700450251082d03a000c210340798004136450040c3c8100e180182056034640490784221019000d090b50028020054481a0389a18005001c60b07030494484a4540f481c000c001031848002d030703001c2240f161060042c0070003e030740310440700b10079429441d0609207842074680060040c52003c000d96804003205c841c69072000380c211509030442e02400ea00c054084d43c0c032941c40b400704108100316209034004004040015451000392100350401034071076101d141e100c1c1d5a030714034641c0c20b0f0b62400010715000b02c070102d801d00310b203131402c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 924033363 1250 924032113 924032147
    0x3070c0602010c09090c1812020301060501020c030c0d150e0304060f020d0f081b0c0d1824050c100e0f0f0d032304060c08090c060418020d0903030c 65
    0x83c54285480204902410702850000b00d4a8509a282c0785105642110b200f141c501140040390380c2e00c0c24080108100031030101d00035424070030300048560020404c0b5995040c05030142408920900030045a1050401d04a40358815111001c555210a202e42000c4064400080da507807410510050000e00003440e024046600010703400440e0350303000311101941003260411100640306d4000681a00c0c0174072218489600300403403c2891840c0c0012154100303031054892040307940d403021801c2001c40860044522a01c0203600e1520400e51a40241e2a1080285402030911403c0c4603201d042000341c844c0300f41003580307030000c440d10b01d00c007444080c01e0484a03030010101d020001c8031150300c07020003035120814165106004240125800303260440c0c1802030030210080e1410386040c070020100811920300044001001559038072002a02e664007140080c407171402d02e40f524603c006518001c0c95154051034092001c080b41d09503e01851640520a4a01103840e0a060320000c000c090f0b5106a078103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 924034613 1250 924033363 924033371
    0x3020114130b0d09032318061621030204030b01030209060d0c0f03020901090c020c0f01201e0a0f15020d090b091c0e0411270306010f0303020c0d061d03070c060201 72
    0x450802c041d400c403098081001f003c0f40207440501c2c00903600b40103980841103d4001c0d43c054404222506548841e95208005641144c1103200f4081301240244c0c00014148040c1c1c00060026140c0341a400750f210a0060603842046450f03620a00700c0308803540203000d040301c1d00c88103004500c4c0240826014010b10740b01000303060b101080c001d6503413001c45030f214050040080d01c200c40d42d104540c0b42d0840d05061080722a160315a66070745981e400b0080002d4001c4180046124045602081864071a504009520b01c3c1810380e40380d045624003144080c00250b41d0070001c3c0040b10250f0b0042c50f0101d40204810741e850b150142c3c4480c1042c2002c013542201c0142e13820a0f28005800406e45a00c0c20b000751130000f249001c86594016510503244010b44040c2c031008070080070310400d011400000300c25030688600340da98000c8002900c581d40030040142c1c00808090307c041c2441d107503c260740d50150b400462500c3c030200002a1200018071050080e400008102042c400070210a000900c02480200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 924035863 1250 924034613 924034667
    0x5090c030a051503031c0c17070e0a1220010509240f040b030718031109061305010b1201051917030f031603050603010603020114130b0d0903 62
    0x22803000825020a80d0b580308085a501121600200e103400f41c0903048964500100000d0343c1110458003400348140e05100303940580c0c91042800344182d08140040260075200c01c00300f0b40e0107112042c44950052480c0b180000c9903003440130b42d01001801428940e8101010f003403981003041182d9030050510000300011a5280c0b10380342048144104246401e5480302241e00f181701074442c003241d50085040200c0e01240741c240100046015284903104c04404040b1041144032030410307440003414011a11031112020b040124425500000c0103000401080d20954400101c41007a0402c8540780c1010a81c0001881040c004502402040361a580321404040c81c50303c03503200600603008000a50024854110001c1080d600018803400c6c20585a26003000a41664075045030101c002030704020101d5401e080604c10038003903d03010f035610b01c813203651016420345035403104201d0038440d00c9180300003a001070080090111140b10b9000880c0301240c0d810700402d00850f20403400e00a66a0b0300d494 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 924037113 1250 924035863 924035881
    0x50a08150f0f150a0e010210140c091f03021305030304030803010501050c10180c09020c12130f0e06040c050406021c09180c03060b1809090102090d080409060509 71
    0x100204000712a001c0c0c02080c1c400c0407640c2c160343c025242e00b0010300801c08041c0603820102c030039001882079080741c0300c144030410718400740c800112000d203203082c024000ca0f0381002903e00801048001400903201c040c0d8414940c0003541010000c02c001a9001c04d10071451080b5106180040200328000c506143c1183c640d10600e20040c410a81408000500d500590310180140211442d103100c04004032900c12501d80015031030080e0882ea240031000d8003056071109031090300c0002111200a200352407503412807190030340c89000c40d200c0000ba0104001040045014050082c100200001c42241041340501096611a004283c1070280900c400d0007050741c00079901140d28014131008440298401040d50444502c0d0024000b140b61905c0340501c4604039000300c02c8a415981c0e08002403583c0da8004482c900407502c00220800070a40c1030081860316600e51900300303031100b00043c0f0306440c0343e0005441010884044600440115040244a000f8800d034001801d090b21400700d0b500d0680b03c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 924038363 1250 924037113 924037129
    0x14030f071806120b0420040302131b08091c111603150f02070f06020306130c020c01050c120307020706020c04050c0d09060e03030c0d0b0f0109061b12050a0815 70
    0x5070f840303010750752a4448015a25504044d01d0b041c0180c2c1c603422242c0c034048048582c0d1b44240803d071300611a002041c14130103058440c1d424007108036550070210070900380048a00b5500a00300e000544035202d11a131040050901014191030b894072100316980018194030f041c05030050011030111007515040003c14038116246402d0521402d0010790b80741c400c54094000d0140c0c1f400038ac20382003c1c0107014104200d40c0d000b58041c0380129403075450700740702c428840d00f41c841039081b610043c1c11070038541c00c282d4005c0c4054040c407940c103015540301c240100140c44140d00216000030042e0f0208070200140c58052000030400303402540c040c80b81d031601d14100c000c9486541c00e007103109581c4494007030a0100603400703411068080310950780d507070521590f074050340d40007090b2150105140c0400d0381182d1030110820028020180c4070301c4078143ca44041034807001030302c0489812005030600c007400044c5d6003140386540c40d0001d4580f1600d45c03a084800508410005200c18034003411700074045d40640c0c0d6001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 924039613 1250 924038363 924038387
    0x30a0207030b160503010e07020724030b0a050a090e0106170715031b0f030e070929100305060102070f030321050402010c080903031c0c0305070c0b010e060114030f071806 75
    0x21f000503949400c4412032074510740b40d2101e0700d10300d0207000c0001d07150204040040802070a95090001c1d1104008000030b110307152250b141c3c0102d43c2c8404010b0503a0607003007450707003c05a04c00040d00d140d0fa001444085440c403049640d4541214109000c3d0308600c03d52920756800500d401c000801079161a60034181600302120140120f80f801d80c200c0c00c2c407940112280c400c2e10b1054803031150b6198150806802100fa511081402c001c80500c020b1150000c9174404e8000102000c19000b040b180c01e8000704406032141b4114081c848001c5008640e01d05031100035803086d80d5003002850411030526042c0d441d21400700c8540d00700020702015030b90000400e2059078014103803940d10080704001130b184d84034074080d2203001080c6803143b04204001d41d202c4000c8541e5500c0500266481c14401c69000640702001010a00081c0050080c19a42c849041e48801d0604164290000b014044142c03500201c0e042440810164104540a13a2110402c0303400d10070314100700c8407141020070107054109601c0e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 924040863 1250 924039613 924039629
    0x23d0c02090a02040306020a020c01110f0714120f0309040b0f130f0f0606030b0f060406170403170c071103030a020a0305091c0f03090b090a0b0a11030a0207030b16050301 75
    0x801107682c88516504450056a000030110740d110780001e006900c40d10784400003030100355481145102d5440c0441e45114100002024140d0103040004207088100b07058500703034110f5040d81c1c601080c0c25040084070801c80b05200150303180c440f14000c20041da180d0a22503802500e408451150a844a046107900c0701070340d11021607802e12480d07170749005200120020840c0d50505c100000c60642581c0004d013001420740d00c228070540002d0511145100303a102d40300010303102000c844e80302013040c5402c0e9009403217460180400b482d0345102c0006200d003601c030aa203400b00011a0320401140900000000000390b002c0e50914484000103510342ca445400902400700025000c0500d654030f0b90403410b515981c140c080c00114a50404800c400400c900440100c0c9111201065042c0e090040c0c4415000041900c0d942d61700f09418a64160442400c08080c404109107125001a06002404082c00c0075401410341614604018080d50005030201e4210030705603c2030740000741d01c03030100c0781503801d88 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 924042113 1250 924040863 924040879
    0xf1e0c0706091205070b0c03100506160804140f03010603030806040911030a14060c04120204180b0f0621031e0415030b12011505130603023d0c02 64
    0x9041c81409006045001000100701a8000003800e8000780039100b800d000343c0c00460b01d0380c0c0d01c0300c2844c0380d0710003500da045ca00c14544008110310b00d0484000c06c940049822030f0b207100300d1650385d105602d4100341c2100c041c1e401c150169040c1800c04034400081040c0403030003030010502c0e40e10080c0c0319400c0501030600640d2144840801d00002c680818103800025003150b4800c01d0314141014544680810001c042c0185000714030b0041a50303043e1002c1d6401c80d18080d9a07805c155007008014042000281450030100d200e050101d482801c649200c0c66490321240d50078541601004500502d100c1ca007200c0101c070a6840d08002000400c0e905201c20112054050840742401e840280c01107a00905161400011500d00154541c0010884c6041034030301603800385c1c102145500342c818100c04010050001c00007000b2501d06140350142c0d02603031600000302540c403600810a03ca00054140d0790f644d80e094040c0b128801d000c40e680402c140000c2c00344948120046008024800b0f625010f0710440302 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 924043363 1250 924042113 924042127
    0x10b07121b1106040521070611061906090903170916300305040503160501021b01052502030c040e030f070809090117060703021806030c040506120f1e0c 67
    0x451007110080c0c0001807146c3c1d20b0b1003403c0c060b16070207928003401d00114041d8540c0000c2080c018803091340b040ba00180030303000390341d2036004114684103a410100701039a2100400661441c0920400300e400c2c1c080c2e41c1d1417a00d0150840807140c0200c013b4061201079101c8441414458510304c0d803a020b56020380c11101d00392007600131940000e03058070700000706120700b0801241010741000081c02124800c1e015103484041122400b10129a28850280903810800056810902c1c009aa00445505050840c10b0000c101c4680c0050104002b540210301c8001c02907005500e010094501c10100445e01030240c40800301080b51640507a200d0062141404140c5008000c1e601c81555510640500504c50645e510b05070b24008038101e91944040d4054240401c2c0c0f2144a402241c0701c0c203111000316086542000c0c18002581d00051800780c09400a000c00b080356940c0c40c0081600c403024042c055201d042c48100200100400781c070014411440032010000c0010340700140f907100c0c2140b001581c82da80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 924044613 1250 924043363 924043369
    0x2070b0f0702131409060f07050904020901020f1e10050606090108071218030f171b040509040c050a090c02120703120e280203060c0903100203010b07121b11 69
    0x80b500c055083c41c20b2071040d03151030100507042d52140205d038080300c2c45070311201005148600107a070b0000001e0420003041c1ca0381d06054006003403541040c070440d8414043c5108440c101034402c0b603512190701c1000c0c0ca6500300e0b1400c02c410060402003e404001600745480010820b114039400c00d818802c4030400a00b105001e5604455081003620092000c1603c1032840060169042c004034007041d046010300861a100341708211089000044c1118142c0b121380700070902d0082d02c1c1c0440400790782000f000c81c00340c440070805401284a1850b803001242880108600030003990007003510285480a0801c0c1a94001103045840b00e003d5a00e580d00da0f0311b418100c5411101c004052040e40c1080c41c481c04c05040000c4040c01500c8005401c10748a041301640e0380c02c0480031038080d615038001d40c00b080b1030000200052110b81e9000381241c03080054070340404240d0300240d2081101c403002150090910400e41d0182710240158640071155206980d441d04001c0d410b000081c100310500000c00140783c0f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 924045863 1250 924044613 924044629
    0x61603091502070305040e0c12010b0309010b041506030b220513021e040f0204240c1406090d0804080d11040b1201050a050f0d12020a2a0602070b0f0702 67
    0x1c06040c40a65a03041c990902406031b81c0140b09000600000c10006600c1808078010749120b0070b00031110407010391070141c0000031030300083c2c888002550782d010320122641c1c83e0f206152a0f2440380c400daa00c0f051501d50040d04031a0380b41904d03801003600c0042c0d034003c0480c00c2c0c0c1402002d0342d80b00b400900d944038481c407011034180c50f450003500044244030748201449611502c2035000b004172424040a441940c2d950300340d0141e41300b000e050449802c12490002d013000d040b0400c504c02031801503041d80403901d440d000032b008a4000b01c220f401610030320003090400d102d080c80344907850515104c0303403c040c1c1c0d034120240300d08425074071042c1d501ca8000c01542c104000711001071015002e200d80703500c0c0003416403211031802c3c840c281c8545040240044c4a08010902d204c01880050403018005803035100c00b244902016411000c41c011201d428002a19410746080c41c1401420700c40c01c0580585240ba80b8441141c10400c10743d80166820000c101c09a41101e001d000100c82941d203506045c030100c0c41d15 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 924047113 1250 924045863 924045893
    0x201020426071a07110103020405030304090207080d022703060708040f05120f0d0b150f0f0708030c27031b03150a0b03100c0e01110a120503100806160309 68
    0x1c2458200c1e200c1c0f21102d01800c403090160310b02c1c010510400c0010b500700e125034440c650301900280000c01c082000ca0380036003d800e0140781c4c802c3c81d040c0ca08031514100c0c1e001d0800001e8004408062014031501c035964550364a000741c00400741070510100c041e2807020001c1c00244160040c002c0e40742000000e0081d90840b84160204a40b203042d44524248150040304505000614003000c511f418071785422a014204040e1460f40c0c03408000c040703d400d43d58070401d0b402d0504035007008082e00149080c4000d40c4190403400281c0d40b2140c13041d070814625403011480b0031204016542c91905030b5004100402100b00190460394489400c1002c13070b007080165501d611001080c0002c101c05080c980e004444042c0d4120240d84000080341c1c20282181c0c243c008420014056900e5a441035004040c103081c816094800c44d40d5070100c1369503c0b1000740101044030000344011041c03003504000c0b524500090600500a0b084503c1e1211044410360207428030f00040607250740d909030501400366004022 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 924048363 1250 924047113 924047129
    0x306030c0302270439030b101a18121002091924110601060e040b060c2505060304022b0803061305010501020c0d03020f07060e0a06020102042607 64
    0x5034502410180380003102e6404015080d0f20241040060022054510305c800300200110861141141c80c0c6075651007004002c03010100e45184080782d05ca02c203014085810010340c1d03c00d0350b907500030611101440c0407561503034012100f180c001544040045505100c03103813400c10041e12140d00d0000103107001c0c148820b00310440c0004801003025090428003810b4680301c500d54202e412100c90b41114888030b020700d04a40c5400c03420042c800303a841894401480c200040c03011916032404400a14258008910000c5c1c0350f100d504808492a0300408514042c01041d00c40429070380b0704408074886100042000740b217031900070500715403032201c074080070740d64164444000800300152401c0e040961041d02c84600c112100070130056401c0341130180c10305850060b8003422010300100e00340301100101d54000c80070350140d03c00e0030000c00010030000d002420903980755030015440d54140411000140c10400869004100500050600b540d410306419001281b48001a5240c0505410310b016a004565 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 924049613 1250 924048363 924048439
    0xa2703120b03120d0207052b030504080d0c020c04150617180f07090b03210307020708011a0414040b130521030a0b030715050c030d060306060e070306030c0302 70
    0x12680781760701800185128000f2140b101e80c030300810100502d0000c041e0700c400c4031000382881100e8400c1d040590014440c0500c030f401c2410440c1c4180c1030b11519445007006a1000d03107140c80524183c0a5440d03c01c19900450f60110308200f00203002044081141d00821441c101084e180308809119045d1026640160743d2180e44c031203142078480888d8803400f14058203200d2402c0350343c5004a50342c0c1da5084095100c0c00740c48500c2d0042070807500010160030560140305000074a00340d080c01005e464000036603000d103d10180c1c1c010041121940418080c40d00d5030002084005008401e43c0c940000d000303481081450214503102d8600b20181c003410302681c0c02140c9822490000c2805540905040b0605101400c404010b06545009903c2000e250000c82c048c0345003500d0080000702048013825040e80d01e812048075120041c0d0b10a0b510894486a55403020401290848091500403485107014480a0714546170301041d10050f000c0684a07a26900d0766a0042d002904251a01800608000c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 924050863 1250 924049613 924049627
    0x106050c070308160c0e0115031d01061401120510290f0a03050c0702010905010f200a0314040b0405060d0f18060501050301020a0c0602070215030a2703120b0312 71
    0x43c262680c44c4104031044c4140c20008034000c0080415941a82c8032110300103070110030070350120040c000091845010844000d81e00c03185401c01c2c01000080c12100800094100c03900380010300850809403281e10b25071600c42402140200c005080e011907009801d0310002e141464002c1c2c40c1c84c2c03070001400c4514440082d1410ba40f00943c0e010f0712440303c11345c804200030340d11414150450b04c43c607e0000c0c0014108001801958051100f080c10f8609518001c012110071300b44c0314040c0c410b40d031561007030b80e40100d40780350402d54424118a00d0b4414200340500f080c0c41c5c205880e065003e18081d0382c0c820040811081d01070109540910b80b5451590414840d543d4484218016200c0300c0380d05450795802d00001040c1030405000b11800c201c04c65131056403522207a16410001c1d00940c0049900c410840185003220840c040a14000d580000d40003554081180034100c8a900d940d9900b202107500310412400309400c51110350403012241b1340844d40380d400000123400d104810313500240009001c9010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 924052113 1250 924050863 924050887
    0x161b12060501080d050403050c040507030f1a1009050d03050705150a05040c0f06020c0105030a0e0f0f1902011b0611041403100b1c11041802030c09010e0106050c070308 74
    0x1941241c0112040d1392000350a080201d03801c0c0f00794000585142d03c045091811400c00341c0c07103540c0c411440d10f00026184030749145802940c0c600b0303400d00c40d8426800403d08682c0380c1459a04140d418030b080c039200040c54440814081e41f0414005000d001c4040303020410b016040c0888124000000043c14072841d16902c40d0b001450152000d071408003070190042855101c100c862801d0320400d4000301001c3c1d40840046556034001031080904c81c1d15003d8061100d8020059209140c2013000581106100907840b10f2806242c010107050102c12040c0010150340c0090b1942d0203070404074000c1086040314280301c005423000e1813171050b000000180000d050714928a90380030300742c401c605850803000c0e54503906003912000d80f00390f1342c4074441440b03074001d5055000c45181d006110f143e4003190250300c44002012a681610b600e41c2c041c4007240080704518045c059000464022280b0703107001d50406407032500590050181c2c0c0b00748100042d02032900001003201d0b44c019580310801c1c550318842030141d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 924053363 1250 924052113 924052121
    0x1017150703060e1b0418020f0304080301060809010605060d0b0612010e07030e06090c0d030212040f050f03031806090f0303070f06140c0a030b010512180f0102161b1206 74
    0xb54000f070b01101c0c800320701c0b442542d400120720030b54080741d000e0400c1e0502c08a04961061a0044c611080c1d00b0026201d520500f440a1449940a4905103440390724104018000d084010403801842c3d14068007444140d41f0441030b1864070a0003180002d1080000011900d41c2c07103001b290404080d880c0000084c6c101140718414816545942c0c14440c51480248041c1d444409445110b0160401603007552241800c0d038194060304c1c000d1044036201e40340c0341d10030301c541d50103a00054000012418281715606205200a00e80130f02600218502a80c1c074203680000b0101080607031050000184009082e0382c0c0202c0d00c00301c24401000d403962904145040c6038000c1c100c003000c80f00c042c01c11404102c0010b000000c180310ba4000c10700c1920303080c60001c003240100f9200d40c609051240500c011449018141d150521a00b8042c3c0d401c02c0182000f51103d00d0032545070356006250780100520454031040c07400c400d8443d584043d800310403a2002010503c1c41000d07030040c60030f01c050762010a09105032600 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 924054613 1250 924053363 924053369
    0x20601260f0a02040f0b0f0603070c12050c0d080f04021e15191404180f061508090d0504050906040609050423030f0a050313060c090617101715070306 66
    0x113010000441d000c020305c01512024401d0607445001d254844107581000402107500092900d41a08410915641d0786960308008806000107030f404100600c84840030010b14a108500f41001489840c18281007860b1450003480240a07c4008014007170890811002c402441c1000b0300c4000c800ca14220750407030f2a0000544a5402d60030580440222130240c00310386802940088103d15003801d114a00030a00c1c60000024140303070781d40580300401035641c45410090407401e055898502c181c400d00404943c00542071000720740201742005803090b08041118100c4400342d5660301c0700da4400c2c00003801000709030b002e050281e00300300c10802041210002c1c4411000f04a003921181c05200c0d0019540380030300b10041100500c1000165215802070000d5984040000071504698a007961090705903841c20412001007002c0d041c040c04825000342c0070040300340034044000c9617454a0f1a050035070345454460101c0f00c00990098050341c15060100000d070345851001c1001c0c0d030814a0b0001e00900c407501c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 924055863 1250 924054613 924054619
    0xa031211070801050c0915030906040209130f081207030b0105180303190918050f0604090204180b100504090c0308030408161104110928091a0f030a03020601260f0a02 73
    0x1b00c0d001c1f6085c0e05040c1030b640692220801800142d40d1035080c09550310010701003115580344100500d0028020080c0d028180d849420080d0b04d0340c01844580034600c0c009070114060506080c540c100036640801501e0600c50300342c03107611242d10b4200c0424254400e000c6841c801190b546c91300c56103150040d1011044800c4a0820921040d41c01008021178070243c8440e13a20a844c0404140b0907d05038110680207800144001041c0b104511807074049007181a003250003907801d8042183d40b149510413000140015141030082001e29591801407800c20b0000030000d900200200b030501c05264207031050210b0880c0380c3c003d48222030070a010512000744005118070f0038000d0100410000c50181d851450740039091043c00565415850076142d40200d28100d1904401c0303000032040c5050043c44c4098204040c60030761a89003030140301240c81c41201503030107039101d5010100040d0b8005003ca0441e0f182c0b01d5021025252101d840500c0809c103100004903100710b6442000742d98010600c41d103094400c13 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 924057113 1250 924055863 924055879
    0x304080c0a0e01060c240b010201061a070f1e03030b100306060c2409080903010b01080103241d0606010e09130f11040204030c140a031211070801050c09 67
    0x400c0000031000d42c010351080c585104010000c140c0203014480c0481e2081c900024603000340610340696000c0901a40c5170f2503155141c0d209103503020300c10800904800c0b004183da43c983c011400350180300384a001880413100c0a030034414444200c2c490100010a0800410f40d4145418000d019222007003106110319a1f2141c0c03c51024001d204550840c0c038581c48101c4505c02a85417040107035088001c5440c00b40400344400407094103445007010b180e1042c9000b540300c0b00003209160031aa620601c560510420200500104940c006a02d40320b00c03828107810340d5101c04892800241c10700c0b07400d48004c0407820000c0c6d2001c02d804140c15204c0c40c03080e6114001440320904001c0001000d54074401c240140c800c000c4081440d03003549480303080c00788100d442d80300174407408a003c030380c86680143c40c2000480801c2c000005180740c40084d000d07040314032400c00303070541c2ca030001c000a03015800d00610080c000f8030780540109210710002800568020005450061b156000c10383c41000301d20302c54a03072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 924058363 1250 924057113 924057133
    0x1e0e062b0c09021c09060605030613050705030102120c13050a0b0a0f140d1121040b01080102090901060e0d0204110a030e01090b0411150c070513020306181017030408 73
    0x640c1c030964054000301c1565004c6080342440b002c0041000b000b0030b8030301c40d40303a400126554904101041c021108400c02c0c0c0e00303000c4a41005070810f010b6401061080c0d004000d0a45880007281c4a10b400400c8005c00c0b5941c1c100e1840002c2a0325403642c0499080030225030005041c0e03c551025003244140c640398030811044940d01150300032a240b00b06c00d226141030198100321051640000d02080914549510300074450020918010303606502d2101c075002d5408020800601140807401000d10500a45c100050754000a40f825814005c0000f009240440411145e881c00300c01e00029402400400044184100c00c8209a02c0f540050740401d0408201902c00c400510448110350b8010340a22481d48960b510340d00c403281740c0000e030303030384180004a0b00d0556001700004103e2012550001d04000b0719210034002c803840358a07451340761680b05204019a40e241c4000740005414100c40e192083d54400c020a644210160802d5070f410000441806024070000300400070b54410408480220364 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 924059613 1250 924058363 924058379
    0x60b160303361218032d080c0f0d090b07111807030b030a0507090c090f090902091e07140c03041e050909100b220507091e0e062b0c 58
    0x2201d130b0001c0c0000b0315114020000305103028158054442802010580190380303824803030b0403d00c03054080e12000c1000a101300d4840c000c109011000103420044c10200c141100040e240001c1031050071840300001504400b0400c100c280c4100400c0010962000b18900c2d8416545104088504102080ca0b213240e42020b0f10300050000c0c1c0d07695011004012a6060030040405010b48001407028015048000701d507a41101c00640060480b4810014100380240100051074070701414041c28071005507510708250301c440c0032403507020205040171600c41381d4680c403540c018462845881d03103d01000c28041001106124441a01c104c40c7c0d1102d10351540750401c00c030426a0907a88111140d0040541035040051a0821b106d010b00080404075138040303007880070402661a282d40c50400e9036640401c000301d6041402100038203a100140103c00b09120403c1030440060b002e5204400c50361000030751a9920b0103007400d03d0307003420080c409000140c40482e0045200000c070440b0069035000000c10649 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 924060863 1250 924059613 924059627
    0x31d100e191203030b03070e0403020a03030c0801121b0315090b0c09061e09030a03090501080a0b150904020903030c0f1216080a020a0605010e010801060b1603033612 73
    0x1603641c1040e00c41402183e94250000c1c425100e03029010700403010b00048a40c841d000d00c0748070b18000d4001d8540f07103002d403a004003201d113168000024072a69800510202042503111102154003064141210a140c00c010384110500e501c0240201e5500c0344403504400c4582020384007501c140c10380c7c09191502000407070103020b500b000340d402c0101031201051031a4a8080d040d55603841c0001a4902964200441c0c00d002d0004000d40116602210800a55074441c0c111a84088044000c0116900090009082c0c02c0140200c011100d000300e00c1c95241d035901c1d41207845c1d07041d000301140c1c0d854020308a40381e2120000c41d130b81e500900a055052000d900c510044032401261001720f080303040c3c80b40c1e40d45104e581083d8800c07021032050400d1384001880700d10070203010307001044400c070329580340607509070940313209802420408405020010303c00150340c01c05040180e05046c0802c5d42c0080406144645c03503882188074858440040017142c41400c5103008600901a070421403280050400664001d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 924062113 1250 924060863 924060869
    0x9030a11030f12030c07150e0c011407020a09050a15140a0501090308091c1e05061b1e270a0f061b05010b0a0b1201080606060403031d100e19 62
    0x2c2c1003000010a605d95117030007042214800c500f11007068103401000c01c1100c29854400e07107141c0c018048440b04c3d603002a444800c002007203020b02d10b05415a4041621140184102c4001c5038450011409410303203078000000c0c0410741100c42030b600e503a03031900741e468196815181d801001846404145544104281d40a072900300100c0c070300d040c20300760900407040030140361a03961004440254001a034107560f40c0c07940c81100a0341c040501d4880c1041400d046002d0b000940b1107640c0741c0c51681885000007a03c40d60710410b64840e400742e08801098045101d003580c8881e540d002c0500d4482c1d50b014112240c011800d05441142c20ba607200c1041852400b0306029030b0010800340200441c68000780b00c00c518080388200c0011624260550101e03103040d690350041180d162003c19080a611440f42110740100380c044005e1440307052210215849208500014040194548003048047c600c554220303080840a4008031195400080041a51540c5d01090348150440248042c00d549141c80f200c041e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 924063363 1250 924062113 924062143
    0x301090c030b09010204090e030903060a15051924020609070b0708071703090f1204291e0414030d050a050915030103030302031006090308030f07020309030a11030f 72
    0xc142103480e03510100200418001481d9001c0101003485401ca0161180c0b19452000650f210780e0500201810000011b0200392058548003141d0310800250314013504a400039240503129603000a591481c0c040241c020b8959601220741e824072103090422281800f104580c280c90f0103489000900b900c0e070714288200c0390414000e02005000c610b1000040402510a840400041c00c034000c54003450342049401e058160400481007440c100c00b8002d0819040c540c07600305290030b08120f80d0090130760003c4002c105602d00840081c0a40300f2440803654034a40d03040e44100a454141700c0b9a00c075501074042c0c0c4968010640101a05050001d0940c0040c80c13145c55840c2041d088000c00c50361a0407000090783e0100c1c070016810200c1000c00011070123103000e66805640e03450314540c2580f95840070340c0400b04011650f5400c00c040750a0206503500300c2c5001d404449151074000c401c07403650080d508151f80c94007a004003e800c2000c01a0650030084042c2c0c1590401242051004c1d100c407428002070752 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 924064613 1250 924063363 924063383
    0x70b030f0a020c011a0f0d0203100b030f100c0e06030709090509030f121e0c0307030c170f1602010c120e011107060203100b040503100b013b030109 65
    0x9800008a0416500081c446001800c0c01d291480c902e00356041001445000c41800d41c8524282c200440301e1010f03110180d48250405c942a80460343d0345016800e0241d41c565144135100886d034050207629401c01841c0101c9074210b0a42c185c500080c00c5002e690b4000c01c103581c841c6580c0e814075405507885000ca58440c146c1c51071802a0076009031800400a9032140020000c0d9191070545d00301a0400201c140f0604c922441e0142c5044007242080324011409071004040112114034802165403002081c500480c0200e03101c074080d2400020744041608649014040011600300103185611078000c94420f00c601004c10034059003210340c070070903a0001501c90700f2903000108464000e80381c8000c2c0300b0000200d402c080b401034444d5030020030302100e401d41c000092041c040e5041c20726030054880d2082d95450145070600090340c513001460303514111901c86003005803d80c00b500104540120300301610900c0e800001e40302c034941c08000e003800c0d2811980c1c5041d0081e8181407048038a03041c1e010072034807 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 924065863 1250 924064613 924064621
    0xc1b010c020907120f0522020a03150f0504030210050a0e070e04140d080403030b06191215060e010201051e1305011e0c080906041502070c05270108070b03 68
    0x1250401002481070101c1345811400200141c4120801075a00300c40009a5042c992451100400c12000b0100b03c0b00c03c017080c1c40003595907041200d044962042072522103a0010340700d070010f4240140c0f40440c03a03103068100701c141500828a1064600b054000700103560350507a559044583e20110345075698031891040c4001c402e20074000390054000d1011458030048481c88070b2600c00300e1440e4200240b0140284010103402d406014840c06c001c8403080d0501e030089884a20200b2214818010010351540340c3d5502040c6a00120808002c0341380da05407107071580740140801800402c40b600542c42d043c0050301c11111b465046c1c81301501e140404040e520b0380b601e81560250840c1069800c3d5517510500028021016400d100540a50101080518604001411407040100300c214603400400800c000907040c0d07403081480011354140162201030b1820000c00714049501304582100c0038559001d58210070800b441005521032400b1107841e0b89a020850b268280d07031003500019901403002c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 924067113 1250 924065863 924065869
    0xf050409030201090f030f1103120c03040f050106090b0f04020f04060e01050d0612150b0d02270421020f2d030d050906010609051c061806020c1b010c02 67
    0x102200078000c2c80041503038100c036120540900700c408800c0340803404860194802c039400c40b40a440c0112648040c0d030400c503820900e2441010002c1600d41460b0300000040d04220f1043c5440d5515038024000b040104d48401e1302100034400e100010f881010319031188a064a4140221880c480d0040c80c010b0600307181a4003911202410b0340d01c141032041c180040136070004c146c403804008020803d190f5801d15091700b4900c0c5900303281145080c0003070070185020b80d1a201c4410b0000d03900c3c4d056809410944010001141403008000c024002000d05003e00061040003240304003405018020340602800000c01079a4407404000051820f07000300032515950b40c0c8003804d10030100709000484481d072943c0441c10b07045900843d0910700283d80d030f40a00c6010f1707a0400a15000d0211402c00d54101e6003448002075122501011014003100c442010700c040140e83d4018202141001c65001224800751403c3c40107504500b0541c2036600ca944207010740c0c8006001020840c2c01c06842d10190001c258081c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 924068363 1250 924067113 924067121
    0xb0901051804060b13030b0612150402060c010e06040c0806061302160c0b13090b010c0609051905070312030504020a090f1b0905010306050303040b0f13091a18010f0504 74
    0x14450388943d640c04001012903040e0024000c09411341810303020719003540781030340701c1000181905001d07086200c60180da800c030010340d43c0c00b21f2400508001d51559184006456449190f000b0f00207942072401d001140180015110300840c400d650700342c81640c41e2042103540742c60440703c0540c82010030001444000490b4000c0075251000c907210b05d8441000e450b10342000c141944201552000002e103424848004180107010b840c112006118050441c030000305203c01c0c081010b00500d50324a030b09010040300b04220000c00036002006030060b0024100107446100302c0c070058a032406181303403d02d07140d4030030710400c0c2c130441e0700400103000304d42880745001c018009002d03906800390791541410140221800f101081c0700c040c2d41c03015140350078400010180c600d2948540e01a500c24401880b191120f10280c0381107400502c0c0b015143ea00c0d40c02002c1141c9595403241014601d0140340f509a00600714840e60b004401380d405400075501d804040c00c244170300f407040600e10013403410140700d9845d280d04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 924069613 1250 924068363 924068407
    0x80a0b1909050601030f02090f010e0a0e0a050111040f0b16200a090f0e28230318010f0f08070201060b041e0e070c030c030917010f060b090105 63
    0x1400060001c1c040d034800d803404000781c005640d0501540c416408624064841c6540314240c0c0c1c4400c001b0354500a0007040c60007000d0000c145207034841e00c04049074682000b03c0024103821200911107440c950074400c00d40d0b407046c0104801d4401014004c1440500c41080301d10451080985808080e0b581e1202c52500f0741e41031480303245201c080c0c100341040e500c3e024410054030440c000050101c101c14221000c448900c1c00d150000d8110342600e10000055100ea14660303482e007030074940c94541c0f5107400d4446d6281c00009071010608c0340b0001c0390082000025024056404044840c0e490f0b18000665007a895881c60344000745030040001c40441c41030710304a0b08000c0500005c01c4441d1a40150701440d000768000307501c81034150040844200314003c14030014040c0503074100007410400801840d00c40369084c05018004a090001c0425100c0e030800c200030003513101c01c1c0700c04000d1900e0440c041c2c450101682002c03400c03e440410848202022180d582105031102864030503e00d000080000c1c50341e0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 924070863 1250 924069613 924069661
    0x1080d050f0c0105100f05031609200a080402040f0506060702011d04020c160b04030f060504111e09072606060912030c01061a073201060609080a0b 65
    0x1000d2500c2c030401c01d004560146141c020360341e0880c0d080c2494030000786040d030300c03280c820b9106100c00740304404100300480955503005000b28a00d260000c074030100001c040494060f070f2100240710f410955004144a0246108a4040c0306168810714603405480b003c3c0c0301ca5500c908100308400056001d03000c03a020b1080c04a03401200000c455002030220303001000a40d9254220300c030306200101511342c0e46400b502190401c50b081500f1603c13880c942a4184c0e5004244aa40380d000c9418014003500d9035007904801099009402040e040782403c0141e09050350340038901e000041000c09008200103058005a0b040501007504001e03000125408041d00c030340c0d0004000c0141c401c5070b84031060ba2101803c1440300940d170fa0071680102d1800c445880c3d000380320f0321003407048207420002440102d4444a40002d10160a4001000600340d01c414841e600522000c0045401401000640104040300c00b55140c80c030a01707560b00c00740e9442e42c10400700145151540400180c0d1003082c0c050f0041264602 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 924072113 1250 924070863 924070867
    0x403031503030503071d0a0803041e0b0f07140706110c0f1f1106070305010f0b0f090603060102030d15060e030c1f02070b0d0f1a010206040303050a0e1204090b030601080d050f 77
    0x40110b00d2520075600110519000040c082c080d54bc8404250b00441c86540700021005d4504013441d0114007440840103030340c0c0740000b1400140035500580d95244424502910f10440d92420050f2140300440c1008840d4024050f8a43c00d6180451181c03140400c00382620103070104c4d41a100c0e000c01403500c1a80c0902c12450ba1000c6a100d00700105482414035071000035484d4140398070701c8400d003e2540f001480d40c2040080f004050002d03030a903940d01c20306561135901c1e0b841d400d006038154081d504032011150328040851b040b0352250b01c41c210807501c244c1c9901c0c01e9007900c041031503107403000b40d6038003500100381080035032f403000c8071641c5000a08004d2041d1940c407500c03480404100e50004501d201042c3d11100c8055450f0071510540c110390604001c0c015044100c40c0000c2c0d1541c00041029003450765580002d40010392507040300c102000c040040d15052403030f114801d60181c104d0b0007910b1005162440790074150400043d0704d81031701c0749000140702c10440c56104031901d03880000280c0c844882 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 924073363 1250 924072113 924072167
    0xb090f09030d050a1d0a0c060c080c030c010603060c05070b0103020607030c0209090601060807080403020a4e081e0a14040308150603010f05040f0902090708040303150303050307 78
    0x2141c4070f040e0140102c0540400c03015210701c564100d645a80c00412016005580a00e0000c0c40d03601c03401d01142e4150401413480304050420b00d070140540c240d6000c4501002400603100c40043d80041c0035070348030719400c0010300c002240840b1540144100201811507810043c005071034444040d0002511901c0d000c140401c0300e602150407e001682c0300d080560001005220103034024a0442e4070030004c1c03601e11412318054800030b642e081c0d4010050a964500c01c0c0c0b44a20560391016000d4070100040809083c1d0b4031540c002288241d1036881c03040b0a4000005034000c2803244006502851030041c80400c18214150080184017000c0d0407020000d03a207a04281210079050301140c8214041d484481d005c2c54900320b0100c2c00c0e440c5003007251084004200504c503403001d200c0410207803401600d001602d001e5175010780d4000c000c14003000e0340c050b50440030001115400070303529204900c0381d9000c0c45440c100c81d803441d81d01324482c000203001c01c10034000140f40070710940f07448a60280e2a01260b03d0022 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 924074613 1250 924073363 924073387
    0x7050402090a3305070201050d021b0717071e0513020702041107050c0d150902031603240606090905070c02040c051b030306281a09040f0b090f0903 65
    0x1803c05001c10031500803486103102090859040c40115241e084c114904800c0b43c1c002000d03031140100101030160702040b203000001c0c03144c1c18034142e010a17100300c501c0a0348550041c0c4d055140303150b0101d420310403c4d00120780000d0f0321025140600075032800150313003070038041044a151a03880354105066401e006140141ea524090500f042d04049075044e916011414168140f032941c0190a000c0e540180c195000504440c001c54907001400308000390884843c0f0000c0d0900b00c210440c0320544650302004011700039406490060401c8a40220798401102c00c5082c00f907600c18419080230402401c001c2104010a03000503602540503c1c201100d07603107a0f80080c0072180084401d1000420100d20940d0800360140e1044510b0302c41c400035070540c0703400d0001400301106032061030303d50301e044805004010b424803c80f0740034100e4483e01d42410303105840314000f5608039501d141e200383d0402c01845414410361080c000d060401802641d8651f684030468441030340040d00351722651204000c0b40e00400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 924075863 1250 924074613 924074639
    0xf151003020c07050a05090703110d05070924080411010e030f060a14070c030e040e15011406070209011a1b150a05040b07030b0316030f0c09020c0d0f05070f0f0b0c03060307050402090a 81
    0x1c041e51143b240c400e05003000d0150035030000340143c0e0420504401429840d40150040d948154440000d158075031424004903150341f54500c0e26a09072040c0d8003881d2840c40041146072040c125007104002100300c1400e80000c10109441c81000724050180b080d01080c4289907100d0f00c2c200c0030300045070340c8035107a40140c6803210104002d13440d10407060040c811070007260070916640f9000c413081824400b894001a40c6040103200760045031140b20100752003500b01d401591091402c2c451102801c1c103494002e07039152034440310348500c2c4415480000304107112030b125803070144d500b01880440c1540c4115040d40101150410789a040c81003026050b40c200c5005c04090140d40710f04490081da420070324011089401d1504840303031040c01070205640d00b0701d0003d40107004035058901726000b10740f66101070707035144034002000e402d00c2e221396581824013201141c2a60042c4c401d00c482e5600396240d081500c0c19010544a50f40d1541011004010038902a00030b082004001070001828507500c500100101c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 924077113 1250 924075863 924075871
    0x16020d05010c0914060f090a0b03091b030d08060405060d0b0703020405041116120c05030307030e060901150b0c01062301020d090503060f151003020c07050a05090703110d05 76
    0x103a44500300c03082c20a9100c600c1000034031210f6101c6140c400d50100061150040405001c60024041600761a0390f07154000480140840092147c0c1c90804202107600d03910445042a0b00d10030b1503071401e129080c0000d61400c544a580d40390240e6807961810840a4030000c0d040c00c0c2e100043e010484e0100d4070b0040c1e554051090342c0c50040c2e50340d00d0b0000703200580c3d80c1c0c0c10840640d001c060003003902c1c065240304c081d00c0301580400e1614044c03452540030790710a8442c01c000340043c03002204010009070158080816003981d2001c4420540c2c803081d445084c0c03000340001c00044407829000700a4024060058035a00940800128400303844040c1d41a204180e00403c4864030342c80c2c00e1580300741d41c041c40550010103162134103140e070030306020100360b032030b180580341c01d009010100c0002d40780300e8010645045d410f0028250a02c0200c04c10004010790040b1801c40c450340180c0600140929048140c0d104552000e00340da0100c0e42d500b14250300074038010f0104003150780b013001040304038002e070320803c0e2203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 924078363 1250 924077113 924077123
    0x1f0b04020928170a110a08120301030b0c090a061d04050f040c06021b0904081603080402120d120b0a0f171509030711031c0c0b0a0b130216020d 63
    0x8194401d042984119a5104502580b0040f0f96041e4200d8046400e94805030400c02c0b0100750310003000441c58407401a0701284144c0684001000701d206042d00541c12203000b40c1452142d510b6040c041d01540c494841207940c04a2010303010041c0c0c50040c4e08041c03030103499020000345100c040e008101510070456032406070510b09010841080340c80b0910038007601c03443c0300500c04103002e2100c00e052a19001c0807a44980f10541c00202044038a008603003460300740c240101c06090043ca005030548405a504910582d440d0011705c2240400148041c2c1d8000710b541ca28080352740b10380118008242d44800700350052100d91000c550441c3c4407d20000802d81c04d400a88603c034040c46c0300d821700041d1640c14401d0341042c0b09210f01e815001003500c0708107410040c1d4403404030500340024500b81080d510000c05280c0f50300c4080d000c0c0d8012403215001c5000780f0b0031020341c0c0d5400c00188201d40c1c800702030b1540070b80c80b000c11424800c52540a0120810780c8038440341001011303000600007056100049079 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 924079613 1250 924078363 924078409
    0x3062d09111e070515090a06060e070e0303092b05010e241312180f08010e0c010903030c050a06090b06010e19050409030905100509030d021f0b040209 66
    0x410401540e07240c500d00a400b00908000084d0390309030322007030100034903140100404003062902c001800b80151080d403008042100070b80c3c544c440c101c0d4050498958003c1100ba1040464034280402240da407607000030300a820403441034040005511202c25031442001283c0310000004000b48039041e407510b07640d0010801c1000e05000c01454008101c07401c035a240c0d2000503c21a1444000e400d01e15a6000415203007801640000f02d404034503002170004501440f07400021921840c51045051311081c00c0280440c4c0940c00e003a65032207103800c1c2d0f424005003032000d00300086842155070310611446a02030b1240c80d815500c4113410340b1030500f016643c444e40c2c0e07400c0c01215a040309607403072000c205403134107610440340a40f903541039036451060303501450301d40580701e041622030a00c10001c3d1800400d019100003000b04000d0807600800d14403400b0b0300c61001181c00047c00044ca54015004114000986400402a2202034488900c013a0340142d028400078185681c7c0042c100d03012240501884 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 924080863 1250 924079613 924079627
    0x6020c03061003080a08041a040c050f0109230102191a010806100e0601020f0718051f0510211401060f05250b0109090303060603062d0911 61
    0x250406401030181d02d82085000c20400c00120300005495246031242425002903669050000d91507103841c0c0c00709110f480b0705003003008000180c01d250080d28000d07103001c0241e1103040019034a034181030088100ae0480000c85803c0300c81c40864841162106105492032032085200d0a005064540c0741140c4120150391174690b20044802082d0050261030000c0c4101d043c51818410340301020300584884800c054002032041e4020032800c01c3d00800002110310036603070b419414001c1711940d01c2d900d00250030200410700c4040302100794001003180e0341d85002040e00d44400c03c00325110240e14402888002c19910b44100202c20120b08803205003000401c000446000c40c0129030816000501071200450401c10099030050640e00030341c40c41e450b192486007169262100d10011410028001c0d503c03540081000c05c017580218000510030788050042d5a01c9000035000e65445000e080e242824198011138100e140602c8030451301d2103418041c20301e0703031203110030402c1c0c0d0f822000a6082c041c000501f1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 924082113 1250 924080863 924080869
    0x1e07090c090803130626070e041503030201050930130b030708040c1512050912070f0c052b06330f030c030f0303020f0706140711030d110c0706020c 65
    0xd1940241c0d83d4203180181889040f41b968060b0050141410419840c0c0da280294403036078050306c105126010220b821540c1c80c6002400b030101140c4024a60040c3c40007000e000195189003000300b4900102e819611038440031138031407500003400d130401898200ca80090950680c80045000340710640e100003641c03815080260180b9000e030b10100c5007401a04911000301c3d0f10140301151749220f2040824030351565040d1074034101c51403081c1200903400040e010200001150340c035034410310a91448448564610802000d0713001040040711743d42d001d609095002d0000b9072040742461288800103a240b804c6841042c0905a094000c43c41c10a4003440c811180e0303203259007130005c0c4002024175600b40d0856442c8803403403159103c01015014034009000806010350160b56000310348450041d04c4100307078105000545040f42581c42c010780d1240200750414812000c826005298000031403600300548542e13801091403100c9d135103d03854140b01c017005105090002c00c00400f1240c2c000d000340f110716010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 924083363 1250 924082113 924082127
    0x803040509130b270a2001030207140304050a0915060302031f06230306060a0c03020a0b0406230f0c0a090b0409020304050706080403020705131103040c03051e07090c0908031306 78
    0x400c0466010780c2d800b6000644500c03a83c04032a601b1001c1da0081403941005034068058240010004003054000440d0780c1b1001000e0701c116802100c0a00c0150381d9640d292048880404008420384030014003840345902980043d504120008001f80c40c0000d47d051049005800c0c4d040240040c20120044144800c2901000407a07030442d0125882e500700900042c1d0075200b00c0268906020104140909040c000d0042c004200c2d00b01f00c0d41e001c00e190a1602c40300804840e80559520008910035100c15241a1842445a1400801d503e0907403103201003031600780c0000380000304114505901140300070031440a0001455010701c0036859003041e2400905002d019080541044a203004020200798000303000400c0706d00548444884090268852000e4286d003511441e180100000344403c010000841c0000c5078060010340390403c883c01040b40715501a40c1c000e14a99000348414081d12501d42c1c030182c0503a0940c01c0c5030912903038a1a506041d03421540021013004e0001108000e52900001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 924084613 1250 924083363 924083431
    0xc060228020334050706020c0301110a1205101214010c0311040b0a0207090227010e0d17040e070203030a150f090c020a06021917010803040509130b 65
    0x61814002600d59070000c1c1e1075019202030f402c07040e15042c140c030703c2e200c0b01d402c2031066002025035070344680b28480a5551049001d0290180d841e20004500c03043e00c010a4494185403680c418844d4002c0c0c89035072000e04005020f207814036031610700000f28a821040c2c44040340340b15901c4420301880c448441400c58440d4043c034000c1c1420288030184c0e410011040f102510514515a0b850f6440014100d14180c50750f080007102e5440010300c0c10709030201000000801010038210944102c000c00111110342c904285650032406407040100041c01010400e4141c111700c0160301e081694590322100d02e8401601c0c1e003009070300004140a0005e03080c3c050b540c0162080e060410f40c1030702d070100c2c0c1401d031840f51040034110340e600c03804084e00520910102d032003140c0000e010354603130040e042c46002001804018802080d061004c0703288a1409421050480301c2d12009541483d2404007407143c44c0310300030604141c242601c640b0500103040304208900605e102113507071400903240e5410955100c8180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 924085863 1250 924084613 924084617
    0x11a0f01031d1e071202150d090c030b1b030a02071407060e10030c0e1c05060a1b090b0a0c1b14011106040b070e010c0b180606150d05070c060228 64
    0xc0c5040c072807002603c5d11175200960540b001102e80105540d40c118500074a00000c41490406490605100c1d0055843d0306480c0501d20491054403903110345588040070348400a54850103100080388602240d0140c02001d000c2c60725000d26a18811440d030901600d0341105000c6014030b07983d4001d80c00c103820381c82d000034001c3c00c013000070345048040540081c0c000f60703c16114440d41e208003110000d0381082c1400c040e038044110b038207505100a5500143c41814075080324404980048600584101580e4080b2400703c07261600e04400341c0000c0302c01030171414050f1031032954079064400c00c400c0303030803403400804400010307401001c0700760700040006030b40c0030850b4015032046003030001213074041c000b941c1c201d04c0d5070400c6941e2407201c1005942186003a540600301c00d00310300412203410031030781000c11409110000d032607031a038491081003010311040071400107041080c131840441c501d0070b501080d040030140c14411034046039552403070141d900041c0004085440c4a40c1d01c81d0f080007000711042035070018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 924087113 1250 924085863 924085873
    0x608100c05070519020f03011b0f02010c0504151806020c5107030c2102210d2d0e030d0902040209032409011a0f01031d1e 54
    0x5900d40710303518001c20300d8205404c548580307603004659070041104910300000d0700a00c2503030a50f105500503c1001c0c0c8014000c1000303a1752048440d4410b12030180311075021b48600b820281400041c00098100020034820311901d5500d90300203a04a24507a40101415401000442c11401c140311050240741140c1c415070307189071464483e00304850b064440c0d0603080a404d6030100d0b50389400458a105030300000714170380e80000d0101e040c16800b5800c903100354001c40610350b650f11205845202001107090220042c0c0100741a81c080100c18191407510011104c0c3c11810800c3d828842022684601494100e11110100b07800305100114a2500480c80040d0200440302c3c207900c425482713200304100b800e00b0580ea003a1410031544c0e0380c2d0544800e940b010381241c1d44040001001801408504a600640521840010300c0b03e20140511500000100712154100007018140105000580486814552120b015000e100480720141c043e9598a1000b031040c2143c4002c85401c0b000341c914808015041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 924088363 1250 924087113 924087127
    0x20607020307183801031e0f200a08070c020319061805030a050715020f070c090209030c220e010203061c1707030504090204030b0613020a02070e0a0f0608100c05 71
    0x1c9911182160401c03501080c2c25904012401008104a00054491841c0801078508071980c80308d51100c020700010002d102c03059002c0200d0321062091008000300030420010154803610f683c1d07821042c10700b0308000340310362580000c5c1081c450128400e0329000c625440014005980542d102500d1100b0500b4030304d1702262541d54484c8211400072003031000000780141008006d8048204880c0c02d00411034840c142c07075032510840e41c0032080030390300d0440b21203000c580c10005208a48a9080050080c00004e041070300b8814000710741015a03029500302141c090b40768160b80525019444000001a900c3c81c00d4001c01c411072004200220240305030700003020015020b0301f200910b414192a415440c0d039824581120a44540d4000e940042e0022900000704040080410702404040754669440d8405500745800c0b0f0051409000040c2d0240000304440d1000c1c0d86000d81200301000046108050b10301010191a560307400201c042d0711007040084d05000512900e684103e4501d01b0030700c1c0000b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 924089613 1250 924088363 924088421
    0x2f09060d02040e150c0408151e040f0b040c030b090d080c0c1c030c12020702061605012702240a121e050a0b030d090b0702060702030718 60
    0x40c9000000c0c040c41c3d0365408100011001c00c044550a0a1440000f51520f013040c0c0c04495600544030784a150300c42c21000114014050003541d100b1180002c081c2d100c4000d01c4454885100c0140040c0c0b0031aa10580c142c02203007200c440740d4403440c0a00060014245145810062008002c014034919007010b10014265584a101e523504500800d14958548041982d25800e02c008842c06821803510365500b90a42a0107402c004060701d01500c6240c204284d4244d0b9000382d2240020082d40100c1c10072201070f4601208901001e068050b0b0000150513080302c8405000424aa0700300c040d04071002c041001310714220311108030001c030f468411402d00c0b088100c0e107006130091240c1c11051150b0170f2100402d0004c03a40c0090070602c4070589109145c241b000c1840001c1c60261901d544190a04101e1400342c1000907441c4031300003a56840100e014a00101c1f04032a41013088120ba00440c2000388101503603040101001800702344844042d84501a402c16003200c0550350341c191341c000e108044100c008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 924090863 1250 924089613 924089629
    0x7060e03031605070e19060803040b19120e010911030a030215070e030313060f0c021c0c030215091e01081302060705121902010b0d02120a2f0906 64
    0x10061980c0d0351203800c41d440c046082044c903400c400c404d0001c03e030400207016440c00711644941c1000004004068403040415101e00c1240500d90055030100540080310101c2e038910308081d1118505250840c0c600200c0d64181d030844031568106030b454803502000d10100030301040d0ba40008070014440041e9658000e919409000850b101071881c80c400141018000c1da10105003100003020380e9075a0607180754880140150f8010b0720002024400041021801a0300512645400070301003047c940500700711100645904004654160b164074001006071038070701d403041d040f456485001743c4a10054041c07081b5140600550080900001590501640c00480464100050250a1b6003050060010032030501c20b44a00416510510303c0300791071840d921024211400d1a54044001c01094000072802da407407009401d070f4004411100003005280099120100c482010262a0b01701540d440f2458901329014a100c1c54804170810a4221450018002071000c400c96241c840c1d0700b441d0000c0f500708 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 924092113 1250 924090863 924090877
    0x50414060c03070b10090e0a0c0b13090216030323010306051302030607030e060703061d04020d081215040e100b0640060804030e012f07060e0303 64
    0x10140020000307200a018030440f400181c10403198501800e00500ea411410068441ca48100b807030202c030002215000f082c50324216030001d811940d080c0c100a1a24465403000038100843e840c152070000d01c020702c5001601c00c000ba1080d07003048660003070902805440e103d14205034a06690210000700d07801e2024018103503504018005500c2da03400c1c4a50351302114202000e0750500c5600100a0801d501d60024800b1440000544200c0d803a0104141e05403201d40c041c104410841d4800e485120303505541d500c0c0d1241c0002e0a17003a6101c025141c1c10260352004074548402e00318282084402017a010689a1011042d0b40c10800300392034104c030585514909040c0d03201070382c031000260226604c03041540c81e0136032040c0601ca04c0310118032044c642c00d0348008654410003802c04045031070b5002150000304580e510385a0420f1991243c5e021500808008205410701c140c00558a840d2181424852004100804c0c0303002d10307104000c42d81d403500e40c0700d5021b50100400c50b0180c4080e528044251201c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 924093363 1250 924092113 924092119
    0x13080102042402120408010f0609051504090c051203030a060b0f041806080601090b0103140601020a17040b0a0905041b1d030a15050618040201051e0d0624050414 71
    0x200020b410012810f005860102030b6855202040101c4d00400650004801444410007040065070b1215900180c840072240b4030404480071034090640d003403680165095510460491041d1500c441c0000c80c02840f11005800d103030b0003c0200318000040b80f240b44040c04078080d5083c108004401510524802d44c02804041c6686000740a812005d40e00a04060044c1070140ca42c01e40c0c551201d100102016440140001d040c68200301602d800c641520f40660010703400b404108031151102a0004e03a001c5420011130410040042d514450300c0c00341105024942e2008445450310041100f40c3d10b00403007040300c502c00f44c9000c082541d00608010301e500d400003c808201048880001e007010120140035250520031000f04041500c564485485444100e814210f080c0000d8101c442d21001181d0003800316404100740c000d0040804400e043c0204071070403d0789030091914505c800d4402c1e6503c152484690849180f0250b550a061524501c20b0340c94002d0901d0701d420b480014010806030041c0c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 924094613 1250 924093363 924093419
    0xf0f01060e030313060509040b0105030f070e010c1b24021b01020708060103080d11180d06020c0a030210060915051207080303010f150f0c060b120a05031308010204 72
    0x720303072410b0058542e144410100c580741d40c1e9035220003030040c0e030010034010f10661400070300035a40e6008100341d902480e000d0011304a29900d002d0203890315000e00d038185040c0810303e0801341c00580001c0c8070314003101e41074004084603847c000300c3c7c149400401e0b41003420220059164030813207a000071401402c0c2480b10b100c41d00c200741000141c0c100307080ca0300028046c3c02a68004000c0c481444018140042a91010040d10001d0540d44050b4000c00352103044003031504000c10000d1502d681045081c90040400600c2c10712070f00061454114a0201100560818040b101c50b81c85644240402009064014401c00030001144000503000c1d006140c0700d0b19a80c081441d10034810802c18015018900469581c1c1d616461500441000c6100e256000a40d0010400700036100303580c00344040d9100c0d21221695822640c038003002d00b070001041d541121440c11003c9111504220006440303004d0030245035030b14085150060241019013200c162030307004020400030360640740b4801070012110440d0071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 924095863 1250 924094613 924094637
    0xf0d050403050405120105160e031902011403131505060d0f0501020f122208042610020c010b18071d06070606051c03081503030d05040804030b0f0f0106 67
    0x1442c60301075034002075000400c1815003203604a05601c81030113401021002c0c00d4085010350102c0f020181020b0300f940580048c24103000c10100003402090319481414842007000003500c881d40c0c0340d00115102c46000607203072641824049503041c0709188e000486400d0140e4940000462001c240d0342c01c0c001d0455845441e9103052000030750594078280840c03481203503207a05081c802c51043c1e00c00c0d600c0307581109809900c00ca800c02d2102c841284254004d4401d401c1a02d005405c10010341c0b60481015030781010781100e104030100340304030301010814000068403200051451402c6400d02441ca5015610541c41c600742010068240d60b03000806140c90161610000392451a00780388000e1160011804114542045499088078083c1c62040d100b80003115014402100072000315003000c0c02181500700803480003600e008500440380780c007504807450000584000800c6610440b0155010310002c1000d004004800000e03035044406550924182c0c1424101d4540d8100103110380414401d110b0303519 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 924097113 1250 924095863 924095867
    0x50c010b060309010b0109060504030c060f020a02030d090f140d1b17060f071706060d11030a0603051c1d180a060303140c070512070b070f0b0c0f0d050403 68
    0x5841824014060036160b042c003860311400317003110552030340c0800e00c0f0400108250303210b101a05d084030b400071085040303585040c20030341e00ca08450907030a0450060420350310241c5c8040005543d0741c841c0383d6801001524041420007007081c40d0300000100114405210519070b9000c00e03500070035400c401100009101c00c08081000c04c120f91146081c140c55227507010307908174080b035923074421003002403050364550b1707064412283c1e00e0318405100d50710a080800b00326982041405890003141e0201c0015400c1c0e00c003909189290411180c5409a030344814041c820003800f4006100028078030802618040c8018102801442c54800707003038a0110340c0030f00302005684050480781702c0302204200780d0107810100c2c899805080d6030301043d0301040c824400070800611a90466412960b50f1000d00900c90408041062030822400c006045200344580810003a1144009003006445202041c103580440c0c0782c0010710341030040c8810107580003030119510400041c011102042860b11740020256520719007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 924098363 1250 924097113 924097121
    0xa050c1b011e06031208042a030501150602100519090b1e10031401060902040b120c0315040506040f0c200604051509012a08070e10050c01 61
    0x284064044490010030003504041d80203688440400125440740c54044040605441c07032407000600d1151100c10303940580748a11101c540207031003410742301e441c0260102c0c0b00b03500356289080449400c6070a030040003084024850002c04c0c850b45803181c000700745000c1e0043e445e00f070361000c91291035840e40c00040c0c3c040b601c226040b076000003c0f80100034286030b82c1400022404110381800305603c0d03110703800b0907103148440030070b116001c480c4180741003e06503528044052024107000820750340311400404c01c031101740041c00290009240031615000400c05003c00800050903c0b24896000c2003806403d000003040707085c125a0a44010519031101e00201e0010304c110303030420890304d241003000094030307922014210308a50788403601a5129444686240c0b19441518018400c3d4060320516584511080001d540452404000a5140b40614800c0703503c06000800c228013094600401e0750494002e101103400100d10302d081c2c0b06698252002c2050384000c00e00320020b0240124608940e07d509400c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 924099613 1250 924098363 924098377
    0x6050409060606032405040e16080a0215120a0902131109040b0a15081f0303050a1b0c170a020418020913030f140f12070e01020a0b0a050c 61
    0x400001899040900042c9401c2c01110000303814a1405040e81ca881c0007541c0804d2052243c0302041403810007003100a16a00710400601c0c0545c0311000b065480000f400700043c60360901800111041e481008040c800d114031080d50742000f488603084190035075440c680d2001d91560001a0041980001500b0400303800b03641e038010382842c00940300d411200b0302800d50541c007a00c0521040a03a2420403000003218040c464010380b102282c001a14454203416801011810b000c4461a00007145201c03c051260800d5002c541e0008080d01400da004800840703c0c0b88a000c0d03038200061640c1d621a00081ca4855003000340041000b24002d54403c0c0113106007154001c00801c880410485110b0070008044401d0380704ac03201c031000035114000e20854082040d41652a040750011804054802e01811085045085820301c02c000300d01c42c0100090410701c0703102080b40d9080c904100024206149203c40c1070464001990060008100100c5990480355949002ca1603a81e0b54032592201d0042e20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 924100719 1106 924099613 924099619
    0x1d090a020313290105010f0c170910020a1103010501050d120504050607050604050f0c1011010b100c1a0c04090b011709010e102a030605 60
    0xa4001e540c0004400c034106442c0809481e41c0c403400d10720180a004540344024070300b0b81c1800d008a40c83c01404240781410b1400320480005000035140f407001448100c2e000d0302c401d64401d00c0e506903400a28081c100c1d0b120302c02510002556043c0c02e0100b5a64802403181003802802d0601039981a03038406454272800b03916aa59030400c51a5482d000c2d41045400d11001c91540e4034540208103160044000741645d013400e0901034107001c05110392501a0340900103468142c0c403000c03c1240400e8580c02c1ca101440c25101340180900340c01400154000060103c0d4036150350400c07601101280640070040580c0b6071505400e8081c20140c8400f080c4100c01d1004010807891030300300e42a000b2040c90420213603282c01039541c0e46030f81e085d111803415035114004200c0d0040100000c0300055071003242407001074814045829041c00c900c1462241e5035203541d01100c1503010750402d80c010704002d = true := by decide +kernel

theorem cover : BRFrame.Cov 923920863 924100719 := by
  have h0 := BRFrame.cov_init 923920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 923920863 ≤ n) (h2 : n < 924100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
