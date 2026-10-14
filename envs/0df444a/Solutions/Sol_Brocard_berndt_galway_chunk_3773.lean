-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3773
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:37:57.27457+00:00
-- url     : https://prove2.me/submissions/aaa76ebd-9621-4091-9b35-ae5c2b6a9480

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 678417266 ≤ n < 678597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 678418516 1250 678417266 678417307
    0x604030f030c031805090a0905120724020f030712110406030e0f0a05120d020918040507170705121603140607020703170307030b090903090f0a1a 64
    0x980039180c0300d40420540d00100d1002e0380e511aa5403036030120b400b1903629641005600445074030902c4500001c145e141543e0009001c10300640858036251565221841113030b00c403034000d41d150910200c5d038180c20949018140c000700000e100852501e8001d58200b101408094952410803050031504c1d41c0c00c811940001c2c002c00640c2d0000d60380d0720b648100180050401c40640b00440c00b50182c1c00b05404000324091500030382140c081c00c500400203c4030240e82d80209003400100303500b0302410308591611010071760b400c604040520564206801c04614000d4a6840442c010512111001020001184480480701c09441100b0700c43e4110b03d03180e0800061881e00f00e6840c00d078400c000705116000e42e40c241e941c01240c2c2031302c02c0b907250190120781791186800003070700c0410f40b150385101024091000b56801055807400080c3d51090383d00061484a06681211081c0d1000c1140e08141c608907090030304508085550b0762100d07280c01c08658a020304031442400360301b000315956645d003c0a1400340c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 678419766 1250 678418516 678418523
    0x6030510030c06110f0c03030403030c140703030c02120d050d0b040917030423070e07031d06060312040320060c03070c1d070801231806091605030a0b060403 69
    0x4411030789800c4011304d00c1100080e0786010b4490850f0760f02c0d00c404041042da000c00e0026020f180340c142551800e845403140380104803000c00c0d002034041201803043c407150003e107200e580c1e00349240d07041740108804442a0010759009800c50745440c05d00b950890101c1e211001c40c171501040403c00600090010000603001400d00042a48840c2041564400551095111b2200e035040d01c2089404501204107a02e030640d140c2e070280c142400103405641445038019040d24010035842c00c1d0308400b240d03c4840c201d040d40254040410310420b40342c01c0c4141ca0805042c0342c076450905103140c85010702c0002c0500c03c0c662452286030139485a4a800d01100c503200c4190044a56a191074a446010445280f044080c3c0680b016000d05417130540e19409405a00a80e558040a07428036241c109400035400c9000c480a00082e113000294442464070f20042071241c45d140041e18100c002c6c004420740040c190244503c3c10341e0112100f41c3c11005070784d0000c103406000915101d04001051180c80340b80c0019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 678421016 1250 678419766 678419783
    0x103090204020708120702070b0f0d0e030a020105040c05030a05070509091e0c01030506151207050d0e10060803070804030321061212050a170a0603140f0f030909010603051003 77
    0x1c404c0c03010020003800320086101600d4a1a034900700d04a84442d00c9008107280114208401680305500300003400ca141d90410340040c1c0c03441c5d000d14040c80e65105c5a15100981d4448042005200300100c0090084c04141d0103000824019500d09840f44002c0c02028800ca0310400481c200480400a542d0600c803210581c882042c00e0000880d91781da1292141c40c0080e0401001a4032402c248041c0200348101d0f42d003203030074101c0502190180c1c840092481e0200402401143e1045900780a0b15194601100240480180d802610b01c1512110313001000d5950080114000042c41030301110100c98040c505020b000404034072224110614200c40510a03091100202c0c241140c0c00342070138018402c40c8801881038001001f5242030040b0308400b80401c0c1d8a69407184a04100c5804a0b80240840030010f10700d51030b81c0c3c1d00e440d0751410003284d284651019480d44603000741040705850100c84c0340d000710300300085a400180200c205020b1802056200c00114445200c0c4c00c21801c061344d03001001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 678422266 1250 678421016 678421027
    0x105012117070302070801240905060d02101211031e0c0f0d0c0e0a14040e010e0604030c1412030a090302010209041103100b03011d180d0e3c010309020402 68
    0x175600d07005400b884026500c1c006e200c04202c504c0c0c401c002040c0070000140d2450b14904244000100001044035802c0401d4031003450059407001801c90f908844c90b100d4101c03114a816a41089030b101c0b03600380190000170014001e114440700c01c002041d03000718841500741c0c0c0c2d0340c040540040c0290004030103801e80c04540e00880300d165800a0101c00b0250707440f003050740b4440040041c001c481d8425200d000000350035041a60900d50842045050701c02c1c0003040c0140b1010701c80303103801021202503001407112503011003000300c020041895011160014000710008201444447c84080c0004030f1042d502c04e0325004050003034069540d82c0d00d00a04c100140c40340086411995030044560011010b4203690102e041c5900c0802e40f81600c4525070303003980c0c001800c560107142c1d51015013541c0341035550307451640d06004100218000f0550310740d0384a90364503898040c03104820501c2035002040e0070122406151412254030011400c80ca01840700d0442e903a200140d0080c1103034170001c2d402c076000291 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 678423516 1250 678422266 678422273
    0x708060906070e0301051303030c0e0603360601092703020705030606030d0806041505030a2406050d020f041509051b0a090b030415020403030f0908010501211707 71
    0x948912502c0107840d103c07818290041050308a4500f222500e1607031010450803004030340302ba445115016840d050407580012880c0006010b90403c0700c10740c003042c8824803a6440441100c2c1c034842d40c5465030840c43c4248003d488415114441402018003803940c03010f00000f48908003c0e448200d1040f4106a41400128280252504101d0203954041e00c135802c04180c05d801c00090121030310000b07a440c0000347d11503408120140c282c01380039640d80c604608000c42e40d0b07036040c09248141813040082d403240040049a80c4887e103501a011940303186082c0c000c1086071941340c1300d99100c0791b044650144030341160340010010300d05c00207042e10306031510101082034880c41d409140150400c81039040e084610010202c41340c0b00e44011100020040002000740803440c2000d50f0300544940f1a00d9400020b510380f0780d0498006034010b07030008d040c0e5100c609913182c00c40d0041c800740421400a00c219810300c0c05804000d04100c0380700e000c40c2213001380d07001807210400f0030b5025003c40c8869180e54017403505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 678424766 1250 678423516 678423523
    0xf030406183917120f030f06090c0d021c020c010903020c1f050f1e0403060f0504121b0b040b010e0a0b09060111011b0909060b040e1807080609 63
    0x249100c46096680510306090941d40b01d080c030751402800c0c0d9480220781041c44404260003078000b800705030722410615180074000f0802400e050b1107080e10998580c0707000402d005131104046c104600800085081c4030380d4007601800c0f648101440e074000f60b81c440e481c0308884c070940160782041715280d1012610003903111041d0040d00c0114007a908032030070804c50008000d1000c42085503c0e4aa04250003e42c800c0340c0a0400380106088822140e030500ca031003c4a12004459100ca1095007000001e00f4002c2000034440c801c2d80e1143d0030010015490541d50310000d10f502c80c0c2a41c018003c180e0500c020302c4c41860f01404045500c03010520142c24075260248805100b0300032028007600c940c001801004841c40ba0816000d001014100d0a0721800015912201c03804001e1183d5525003041010314a400c24000d1464212a9030b0b11500c646046041000c417030307980c0c01c000070781202040104024000100703e19007144050440c58030216440000c1032500305507601c6040140602e07410000c02e008040b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 678426016 1250 678424766 678424793
    0xc0306030f0c0604030308062103040501080112151a03010f020a110a0b04080904090605091c090e06040213030b0a0c1209031b03030e0703210804080f03040618 70
    0xd404a40381c104440345041d07201c210000103076030003802c00d2004001091140d0074094110740d002e080310155044402d10707030030040002401c40103e6800082d0400065900c00c014a0041c8000c01852030300700029034803030143d000200100700e03145880e40142c5024282c54065030841000041c001c001c030091890280029400060400000c0303162960400700000000c209080c0c0281e200703101c408c29603100e5840c40055000500c0145e00581d90342c0f0140001102c0d4482c1d240212444070003001040c1c0c11034003000c4000c28407010b1800f040701e00c00003004001024a5a00d030450310440d40175844058007603e000000d000b543c03005c4c02003802030b4180b2101c805150b00072000b40c0084e60b11180303681c0304440a981580c1d51204001d000424800c145c1c1552a100020454a01c1c480d2801096203484400c10900d4070002e03410644041003010b00100c041031040d1030b98400c404103401c0c11102c0303260640f02c054a0b40151282001c08060000000b4100245030340710b030915003148004a168241d41d42081501c40e110b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 678427266 1250 678426016 678426019
    0x191d07030c09020c030d05040f06020a170714040b0d0b0301150f0519030305090307080d1107090507020303010308071104050c0315030604020619090e0f040b010608090709090213050c0306 82
    0x941c0440c40300b03820700850301c0080a0200561511042c0c015960003801c0c0184107581d441e44d061146400030703d0700e0000307018683ca19a6a03a1101c2545607441c0e840f404058507941c2803207041ca5903000c10600e003e050300c04031480284659107450f460b40424010703124005e4550f0307147d4600342000c3c80054070440c00d8010b55520550519400d0b0312642070221220b400c1c90085241400e2001c1000028030400040543c41400b50503140560f40c0e44d8000752a01f144905100081009000308102501d0304003c10401441420018022820305c48d07806503d07448107000144c107228000980b6000d01503100000c221104010740104000e107450060030303c05070030a5071f0f15030300c0c2d61140900686600d0f0000b50b450007560002d06040c0350251003000706040510b000c079007105014544d14006004003220300035601c190544031701a9407903d40783c0341440700d00700705820013002e10885000b48040401c002840c44241c920b031074000101c50701c07a8000103100c0303054821007420242c1405e00b000f081541039000784d40036010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 678428516 1250 678427266 678427283
    0xa0c120e01061e060507060b131b030e031e0a020a080307050912012018092401020706080a050a18050a11100e100504030b09060103030e0108060108191d0703 69
    0x30000490403140c4c812040002d00500140000c107243c0d0740040b840e00c80042160855900c0300c45d80f9010380d01010303030402030082220042d96446400d40250004440c604002d185088080f4407600c6189509200300c00700c0b4a8003280319004c150080042401d403581042c3c0183d240e10f00904010004c0d4003000d00039001d5814184002400e030014006c420842410800350110207420301107002868000c00c1d00c900710804010001105a191070b46040c2c0903008000c0030301c04030394114107005182d190004c41981107500200003008074a91244030a50881100030001c54940ca8800c541009130000c0da0440d1007103449a82d19404105001458180c2548140034003000e03001d141c01041544803210300740320040707040b2070f140010741d1030b01c10f06201ea80125810058141612a103c00d07485075811900100c4a0f0311450052041c5034001224068180d024a0000364a10b000800200005005003061500c25440003911180120341c0c0c2080036041e0003607803503039601c42c1420511640e640306403000395050746 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 678429766 1250 678428516 678428549
    0x201020c0904140d0512061203090a0306020d060807050d03030b04020912031903110d0905030403171803010c0c060902240706050a020403030e12070e01140f090f0a0c120e0106 77
    0x4e0203502a40c002c0506c0e80061000c540e03482042c0301c8020b21200148046000401814441e80e0f03548003203001a40c0240c0b40141c90b400041220740440304a5004813a02e580800400c2043d03a03101a0745104883c0c0c1481c0c041441000728001c500070340a040c00945d40a482c04042001c5c1900001c0680010f04128100c0c0c503120b542d5190507411501001c08501c011a404c2001c03d51002881d04802d010700e1044049078503165403038548124050405131404038041c800036143c0e0991142c01602d005500c41103000f00502c0841800103030000d2040c0400910280c2c4401c099001e6540d451000201a40e08202c0201e10040a0005c0d0130650720000302229264644000310f808a0300c3c6100381d400382c82d4141c58414510703076808200180303004228030b052590b02c2400000f01da83c40e5400b02050080c0034003817400107111596010880207855800c00f0f54000c112050400c0b038007100340110a6000894244009018003c104040310b0b681d0700d811402ca040c904141b80d51580140c151300c00000c503502ca808200d60b0782c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 678431016 1250 678429766 678429793
    0x604080d15030c05060a180801020a0f09060c06050408070203060c0a0908070305060703050c1c0b0114120a020903280204110304050715030b0d1b0911070b040201020c090414 76
    0x3807240005440d0f014412000e00007400c00ba0014061034035a801c004c0051282030030144e2842507075030800303486a50041008118550840d911202d041c2140c100380160700c1c10103030014240700317480d103016220f292154041001c1c071080d6400c07900c001c0d40240646c2c00c240340c00e22944169500024100001481140c000030f4000404281d4009899004028101c661180c0408501030704015044000903001004a8120012210b010841807915035202041152072000090300304032040c1070309803207001d08100d02034210302103481c2e0341e80c4031441507401611851014042443c0170f407800c2da201c02c1d00c0110700050380907800d50000404010f200321b50030b2001c0300140e0700158542c042900e005000e075001810030f00100c10041841455507805180001d00d00e89210009180318041d4034040d02c40c0410b80c0d10ba02c074016140308804010f0305c40c0c860144070014807482100210f110351080035241d88096400b00e403c5a20a102e00003200c00024040030b41418181814040e00400001c503442510800d04802e490 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 678432266 1250 678431016 678431051
    0xc01080c1920011a091f170d030228140a030e01050c0703050315010c0f06051602030a020705150403060905060108011410050d0302120f09090c090f0118080604080d 72
    0x964144c1300f031a072400c941072410b10601940140110400d003090041844d840c811003c580001040140051040704441480b07050900c18080b4840d000c05004015585015654840d48004421202680540c000e4070080c1250070940007511507214440014145191682c13581010303c0d0040d42a0080040e5192640c0704a610b11030340c00e0080120f0020300000308a03d050072048000700d04103040070064400240e49407103001090280407107409503100d040c000c0e03481c028181c29000610900040d4501074014030003940d101d0981c4945441035060354414039203141c4100a4400551b4002410301c4003032030310301d80152212000d00400110358030380800141c200d200c00105078091003250074103050540c242411710070086000c403c29000d601c21006480d034082601c900510b9403004a07405180c0f21021042013282c0d04038040c186200c510340074406102c06690340d010780a80203209090092036084c100040f40010b20f0703c1c1e40a02003e010380002c200a00405200030214400c2d41d42d0104803283e45da0003e0200c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 678433516 1250 678432266 678432281
    0x70303060e012d05041d060f01050306011205030d060801020405130207020112050403030b0d08090109050a0e010b0c1c0c0209130b1b280207060903050c01080c192001 73
    0x80c4088051441c00840241c3c00500d045400a01c000f90780c03181c641c030100c0c0655071aa1200c0c404007a80c00b1403c85511320a203d4240c00040c1240d007510154034100010784d58003018001c1191013445950558201703c001c004981c05403620610503c05c2540c1ca041140c001d4115124190040c400c0c0842840006540d02c02c8a448580c161180b0f01103002c0208200c004000c024021400c0c1981d0311000c2c03500b0355034522200d00440c45420310759612034082000400090407540440e020f2410044280010340d220031001c1c0c151011680107035120401c01440d1490724801900410303044480d45e601e1003c481d0f02c4003061903110300030355061103162103a0301103c410700d50f0424040c00000b210000b0903017542000204480240c13850245a06181900c04c0311f01001114950b0741182182a0340c68000d00c03038060150800a188a04002d81614076540303c007900e44141203182c0303041000020000d00c081207290159841c01044003104071060410850191030000c84920076001e00a01344040651000c0501881c007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 678434766 1250 678433516 678433529
    0x1140307210e2d030412080711030a06051504091707020a1701020a020c060408030d09020f1201090605010803070c1401120e0c1e01021009021203030421020a0c050603061212070303060e01 82
    0x3086840035120121903420508c422201e5208942e00070b440d582d010003c004884d4068000000c040c00c11b03003000d00403079844040c0940a03e003407081210128803981080303603812041080c26a40d0b0034051001900e4503002d50044920b4900034401d4821000f01540541510000c5400f01c3d40070f410900304002d62406180b0980c1c40e50350040103103c41914072a0040c1c480b4601c0a01581c00c0d5049450002d03844150040780c0a05030303992100c801040c45081d01545006007071500103945802002d460b851a10300e06030003020344485240141038041d91094032400a60501e520040040e5446404440e0300e81000444d0700f44900d04007400701b03805100080b601c68844005800901c048803030014084060f0246071400c0c5d81c000b14a0310140e10380314040c0015031203a48940c1030031540031081c5c0328200311020306405000c01c650020020b0340008001402c802d00351034040741c40548030313501d00300015051402c90f1205000c07401410b08400d86d02044078090122140b0a45050028540347c40134040800303024030403070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 678436016 1250 678434766 678434789
    0x18041a100323120c0a0b0a15030b070e060a0801030605060f03030a120f0212011802040e04020906030f010e1c08040b0a021b06090a0201140307210e2d0304 68
    0x803410b45408080280041d45614140ca000a404003c0300441c0d400c42180c0b0303580c83d00080100c10801007a080d003241d0040b6841c0003040b0f8008552864620510503000c0208030720843d10220b982e01c0d024001c04140154000c2055a8800c0ba402c40140603c40c20720086810a09020110f0460304d0b040c0481d41038a0070180c011800c0c200c2c1c04030b040700e01c0f0141800000700341c0c2e82c6110065610400d40000c101e01b5607040d0800700c480d4508540880503d084440801d48184180070a2011480da00c0409070003a0701204c040741d181d140c1d84001f03410708a8020002ca5158139181d0103500e03000f004100c595003210380c5c04286141c1c8025040903903071400b04880040c00c00d0f0102e00020440140c60b4040c015690100140d403008251031b9900c545403540950704812980e005140010842d07a001c42885c510100701c080540c11810a058094058100c914a504800360700c0c400412042c4a6a80300100c10100b0104941d0f42003c40c0d55004803101d40c00e00140710854518030343c440c4a510002c100c60441c0c1080081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 678437266 1250 678436016 678436043
    0x307021005060406180c0e01020d1b0317101715040b09120409061e03080306010309020f0a060809010507020a0b1605040e0f1f060c0305030618041a1003 67
    0xd0600400009059540c010f03940d00c800305071020100405050488031000c0007074011051140034180b1110403034170701d04660040066922960740702d558107100400e086d0813180d1701007107890161007035140140c140420140010030015a0341c61040200221a249584400a01c0d605038540307850f800e441c5080c40812050001088c00111403c501d141e110840200f90307000c24003034140000d00c1c0c0d0300035440151010b031900e8060140441001003607541e441c91403840355125196503181c026900000b40101d042c55502d003007020640d1a8400c1e0a18600001421510710941f113500290a620054442880b950718000c00541e02c180001052022182c00408001c1159201d10800000040441c43d81f010131005200020b07a03480180101c134020402c100c05800145800380001c1400d208064034000301328612141080b841e90801d04c40702100380c05282842d641d03982c000220745007a146580910a0b4280d40e0200818010042c10020030007400c90b003950b40a4807040240e02c030410550001900c2010b40c03031403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 678438516 1250 678437266 678437293
    0x5041a03090705090c04081501060c120905120a030e0409020a0b0d0e03210a1406040b0303070206070602120a06030203030d0507110d20060f13241a030102030702 71
    0x3840e40a0826000c58012544600101e940d094003a12041c01c640b001150074858800103001c9540101c04400744950150f241a00c01400050124005401035050b03003103881c0d040d84914910400b42901a0800548088502002e5600c4852040507400603001c602c0741501c5203454041c159140e40c00500002020742003104100f19030380203880304401159130b10341000714403c09201414003000c3c4200c009414141440048240e000000e0000840d00e280174039030b070b40461170a115039402100a071360018041c0100d4000c24030350f104602011b54090804113003041080031a0700101030341c418903c110880750b21401c030b404083da030090000130340c190018059204040910ba014640c0568546002020b107040c05401034103042c0c9104d82d44001804214050f82c41004401c0d131a4001181c003070003004580391003100420a40000b5140d090394505c0c411401d070920281c0c0c10711511040804405c024041c450034038000042800004030030400341c0c0f00900528515041c800e41e071003100d9903009001149a41070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 678439766 1250 678438516 678438569
    0x21e03190819060909060605031f050c271f020a06050402042d1505010905060901030603080f0a0f0302040501050306130f0212150409170a031811010f0504 68
    0x1842c840c00a4241c100008000c1020b014030b5000b01402c100c009012501400c040007a01d0450300b000f07000b60300a94a0440c1c0d03030215a00a8545050034000007038540300c0061030101d910071240418005100c04c41600451044400c5074610b44504890b4540021f40c46008101c01c0c8a00264010168203c103080001042c40b64003e20350152001f4400540b6184000c031408174540e503950702c880c090ac3d98442241054007a4402c01030802994480381901ca4075102c0001c0080c00c03240503030350241401046a070003690180c0c0058016661182c600c0b42c8030501090510f51030703004a201f10001509441000210070302901c00c9800341c40c01a91041d2542e603660007400403c08201e0964002e00781e40f4030b0529891000c503c0901545800c0021f0140c85041c00914a4141e03095441054811407030040000000758054050b180c1c100214200c45885204401e41540186260340b0606440311142002038108000901704002d501c1b8240c864a542c251005030894090040e030080400f41d201c80b202043c031102c0c040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 678441016 1250 678439766 678439771
    0x6050a0305071e030903090605090f06160c03120e1516020a05040c0302041410020c0108090102120c0c010f15060c02121510090e1c021507021e031908 66
    0xa0070200d451501d81d8191007920040d041a02001965511707020003055400700080c0d00904507483c00e1810404907a0001c0c1a0b40c010a080c94822000007032070b0310644029203508251190052a05002c0c141c0d039080c01c0804220007400c03d8001100004501c2c081d02c0c11000402095400884460070320200b03030f4900c64050402141682c0c02f0700c0c800300000d5140c1c0e6071701800061a03005d0f640540c9030392030014108015400212614407400c0c40a4804000c2540001e0711714900c0350074030b0710000a840700d1520707500a100b4020305601081d1980e040161355005940145859007601c0300800c011a000a0218102d80701c0514456219040302010000d491191110b03e08403400244103911480406446a18041241261b19034481c0c0c420100000700f00c21120000c001c00800c84140030342070400400b20307212402000300000002d015506007281501c200f1544c2d02390350b041c60600c0700c54241028060350320350b0b5948a014000c03400e507540360a1240c020054410b00c00074105c0d030328440d0594110a50744442d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 678442266 1250 678441016 678441031
    0x405100c0e101106010f15140307030203040c0801050112031715060901090e15121c03021b01050a090c080a110d05031611030c010504050f0904050705060c0f011506050a0305 76
    0x160080340000d83c00c00d004450007880d14250200d07045141021425050302c9408004003480200c07142d60b4864007901040b40c2e40901d1610300141d4035501c038600303640500d075130380c110710350300c9d03191034004101507150190541c2200d000c1c0d201da0005441108490317040728400c85020380c080d5050200c00800c2c1c10804041d100d03521050504588143c0c54490007840755104507140031100809110307640250404c107185400a00b203903006460b0811011044022242110480c0c0d802c25a0001e00a103072011070944401e91101140000d01107818800120405051180d8040d101e58a03c204009160800010b000b40002d92164100b04524080d0082043c11781d1f00c0f200a0b29240030800c401c019004050040214440c4105088071040c0085d50605280500815141c0d042c01070401092013640e45260103241d0703203a4101c440708071036543c5151032802d0040d01c0d800306800400102d008075260300d002c60305075812501c600080001c903490410780b0031319440318030407038001c1a41080312602035442900a103034007100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 678443516 1250 678442266 678442277
    0xa2607090b3a0f05011511070e0a09080f0304110f010e01080606040e010b040611010b090a0b040603051f0b1e010513050306070314070206102115050405100c0e10 71
    0x1244035050341500c0703058800c2da104541d04d00052044100b16000c0700307410101890030036840c0e51001540d40c5e6a900602039100c1132010700000030400c1c040703034101524050380490b80644400701412610000d4005070f40445890311036070810300c00e5051103071694064504c1651120005034000e0019516a80040d00c0b0f507400c0041000081010065817004030f00070902100813542d101d1400300005d00400c44212030410a9040414100c0e20790381d0840095041380d0340c40740c001900b13030320300c00040d00a140d030354402000c900408031004144907040c0345400c0c000905140600a4681c808200004280501c8100300d81200900031005507501c1030300079196184500160444c12130712600081d261000403100b00300001e4031654560180221814500c0d00840e6900081c0307010b040400520f01c10420354041c1c02c80029072161507120205000c495944869006a403144115040c03002040240030112002e80701c510903050b09420080c1ca40c03140a480791416039440100702c000e0820001c51502d154041e004005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 678444766 1250 678443516 678443617
    0x708070206040b070201181a2a0601180b091305031312150e0d050f0d0603050f1203010609050919140601110a03050f0a2607090b 57
    0xc45200c01440a003e082d2500c58450700548001042c0c0c0f840e103202c403800702c45564070401041401d808101c155405d01c01c0c040e901d9901c40720303c0d001038001d2050754414281e54958100e5842001240150684806907030710b0400ca08054070420030760750518100da800c001c4000004100609010032100442d01c02d00507a842d00748a800c491540e001e0725040076071003160b054510b20811000840c496803560880405200c00c00e5076505158a03000c249803c441030020000b10f0b10129144401107405042d1903080c20055240c80e400c10b165200c0070b0401d0900c592288100769021310b60b0340d0060383d0480d0403941e02c0c60001800c0c101440081200500220040500c540200e070070200e80b070142c0c4844440d80500c9141d98680000010300a042034a4884460b410004402e40803079409400c0354035018185030600d5580c0302d5201c0813114041504109011613000ca2004104c001009401c18003034102c0303070b803504507107a26484020f07214400d082007512809800c11040c4010f4040c54413108040e0701d0603030300c2a0140b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 678446016 1250 678444766 678444769
    0x30402041803032c060a0504020103061a040305011d030a0c030302131202090c030105100818030c060709090b0a0302132c07080c0d021c02060a0e040c020a1707080702 73
    0x1005407201200420f460b030340002e8803e0714041022030b0070407107001131034290a0180d58854070744101815412035283c50b68001000d42e4041d400c14002446142059915140a1540602c154000340421100c950800c0349200540401010403036441c440c041c0518646030306480107484000800000b101030640a00c24841405040b903130403001848c1c0b002d4101010101c0e441003024400c4001c080c3c103c116030170300c018405ea8458108240c1c065115042210392500c07801c54960a6192580030402c0310b00c000104440307c4400451042c0c028a11030b1a0484807a44500c110001d6a41c050040c9410041d80030080001d4030344046002c4140000140c001401d000300c0c0c6c40b11401090f1255501111020600c022401c0c4008001080040030b07840007410084520b0f030002804a1140e00c0040d2041644d4210355004003200600d07510141c0d401060365a0740d100c801e4000d0441d00c41706d81c100d4480c030701c2c2c030029400180c000b10319080d1140d40700c02e555241c41c103800b16034030080d0004042030720021800e00214006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 678447266 1250 678446016 678446051
    0x2010e0328061e020706181101050f0c0609030a0f030903020c281e0603021c0518010c08060f1002070608100b0403150b061c020a1e0e01140a1403040204 67
    0x143d9007103000c05652410981403410a583d050b007a000030481940305000042441030a1203174005c54246040f81e500c2c0c055042c40ea14500407410b50103164000c8406005202d440040101104206515452504515071200798121110860b02502682181f5034864051914903c03404a40c240d000e00c1c244e4549511100030b10300c8010f50042140c120846a03100038900c0c420041c0c50050a031484e00751700d00902d03140e0b903202c0c0c90b02151043c0c6109413104081015221482d0204c0c15041180c0000c02c060610180f00500b03440c010343e001030186d0860348401320369090000c0c0300303d410ba5841d0000c0541c42d20f404021103d0450040401c46028420000400c40c001c60b01c0050000394007414661000000510f109011140c9600c1c0e41c03442240300304403280c01040c0349035603d080070405010050311082501020f544041c0e031407000a000030010030032482c2040c0c02810803881c0503420303a18161030b4205071407240064030070902d150012492540715888182030340c0006607400f0b03102410101c0c1c00e44400548451 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 678448516 1250 678447266 678447311
    0x4090c0e01020709061406091f1e170711010e030d0603060c0302091e150301090504030f0503190506120303040309090509030a0801230a1202010e032806 67
    0x28100301104156690410800740034110790700d0100311207031414600031000c2101e81c60b02405040003094900c250798880400384621130b240c1c11a00069000303107000800101071100006094118840c07126111845504c1c41119034202d0115a009500d0f400e1703040d03548840f2074603507550541d2600801e4401c03070010300250100901d204408030700c03e400c0d490030b1010b450030080340754100b43c0b0502000002da91856200f07048041c100030420020700014010543d0f050b030742e6a8220807003600100010f85008158841440f488c0030743c1e0707000d08043d07060a0445180c0b10503110140d00c42d507100302c02c848020960b40b0135500560004c19035aa00c080d032103086070440e00211415404070300342d0a000c000003052402002e6114510304017851070541c48090141c076400041c001c1c03140848403031514a001c00019900044ca00e203009116108186e512400400c01e00c031042d0b0102e0021740c1c400701350030303940c00e0001d105200d456094406d012a00511a8080d440b403584d958142d070400d4176138030303003050400c030700001080b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 678449766 1250 678448516 678448541
    0x1203090b0c2a040515030303010e18120703020d09180b0f15070c06020a0201052a0a2109030b0a1e0f051815010513020705240105030a0819050409 64
    0x8003000468403c03c07040750001440c000340f01a00c4e60a40c50665008000c40b03041d10245080141d603626114103004144c8011102c0d495507119450054801032649405802114030903402c80e0113402c03040030308883c4845184541d00341941800012601410250080408114042c180a400c03a0020703001540b40e52644a4526001c034000500310180103c00000304042c1030782e030000b0848008180d000a100344640303c0b95045460502c00c2420204850781c3c0c0ba01043c0ca8107004443c5801c1c800d05022035a0280c4100c15a000b46807001c034005201d00544140044075000300c1e42803a02c4e0307210354405001d0003d5050011241c3e25040400c48410f11900c40c0c400344402c446da000403030b4a4101d4840700044801864840c0940c00320859100a164840001c0d064075004c0d80c40c42a505002c0059001900a03400700901c98056030070014034101031202e4450600141c41c0a40d402d0342d0f130710828140c0703036445044080e244407420803500110b0b2983d83c0044d041e80c0558504140741c00e03654861902200c0d100726010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 678451016 1250 678449766 678449833
    0x15040b041a0f060d03090b0c0708011d0c0d050312010b09010813020d031d0a17060c0910030c231b012f0c03040b0408071203090b0c 58
    0x402440301281100505200700d101508507400c100c2c0c9000032291004200c98420050200100101413044c80c002d0001d0171900c01c456181c480c10140745880306494080c108003586000700d2860750440352548803240350404809407001501801c00c1c0900341820305015036051008020581d45480c031074015500a0002521031505e802040c00014030284010b05203d060180000c00740c8050380d15098842013465050034005004107900360800c8050b1a02c0d14000d902c040c00c0701c0c0000300010200d15015405008505440450b03848600d0f1344134600030440800d801407401d904264034140290302c504149482424482400e1030580d0640300d00c519103101184d5140703c042510302d05201c0c040d1034a451301748050000d008004150305991001c00c418090000885c1d00840061710341724491341281d07141e00c242c000303482e90b440e20f0b849240d115920501c00c01c1c4c030611890707000140b0054810043c14a03254981d4510103150b01e40300b040c00c0550070070741284096000d6601c6c04000c0144e0303c1100d003051810210305 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 678452266 1250 678451016 678451021
    0x6020d1d0a05011401210303090210050c06101d0c04091d011d19020114030f07090803030c1801031514011103180405071b08070c0611060109020a0215040b 68
    0x500d00b51540e0510403052858004018008440c83c0d81840640c1b18840704034404140040c14202c024100040c6c020b03400a041601c2000320650002c0180103807410041200e8441e200c1400c1e007442c90455114040200208145911004051288181e0044e40700902c1906080c0c03110a1041162160741346800c0f00840c5450122401b10280560700840d68007011003000016030030369003516610604500c6c10811180b405d071404581c0510b901003090f8802c80e156540740d25140d1f09003901c101c42510000701082040034001221203000040301e10807090300e1411402c03e803c0b4039004200c01103c0c50750740d050646411114450480c0d40700403c0003000c0d0140c80888010030070b00058065000f441c108031040c3c0041050180800405403940c041a1007524006010365a1a204a0707d940d160512140d440d0075450340c003c14080344801500343d86c0d0103007814031029562050183c0d440320700c1122641c2190095801080405c00300c1d409000030000300d0060b5101780d00003414603001e000e000c580450f0301007900b0b0b09 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 678453516 1250 678452266 678452273
    0x130f060510110d0f2109170a0e0108091207080406140304050c0d0c0e040302100c03060f0e04110d08030601030f05040b07200f070306111c02070203010b09091b03011806020d1d0a 78
    0x420307a11140401fa0a4039040700b41300010515210040460f05005070080410500481000f00c0c1000b019206031103515a1010301c1d040405030300c60310881001410130744400d40d007540c1d140d089a01aa502c00b006042c042d11500a1182401c4245420f91315007440501c0010002032031605035205038030030742c040e010b41c05980d010881202e1414070070008042c603080d028891280f00e444c044003996201c54a800d115a04ea20302000a00040300300144c000d10040d00707190400c13003044040c5000d520b003600c09014000c5214582000c5600444024140c61780010103c0c0901d806030148865035181c40402c01250006011400d143c21600b0303524000347c3c2c0c030000c5c081080c400d03d4403540301500001764040c0c0c03a1084008048241c0c030008440d86407155800070f40f0000b1560254820b0304003a1015000f00d09920307002803004e88406061545400055800c514800d4929043c030420078002c400590384029002e00742c980c0c40094000c0407a100c5400da0b82c0101141b0019a40100c0699070380c840b00402c45a1601d15 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 678454766 1250 678453516 678453533
    0xc01020c011b0207060509042307022413050a05011a0a0b0f040b1c0c05030f0906040507230409050a0c060203040b0d0b130f060510110d0f2109 63
    0x11042c010a1009041610826074042002400c0302c1c840d141c038a4540200c40f0020b03000b008800c803141600c541100204032808880d0b94050b200d510300350241d0f107122038200070700004519103481889403c8008d80000303c0040708074803610601405541140d800190035604c00d421213145007145c40c0d280303982c11000c9c1201e190a0380c10501402030200303190b0034000d1010045810340124080c20640c0703a004103909041c60700c1c0843e0ba407040096040d040c007100000c0c51026009600550310020300010400024110b007000048240c0115030020003841450300e0000740462810701580641d0104000b082060360b142d940d80146042540280043c08011005141196441c007040e4415401d540050104100c241c3c07040d000d0702c60658140e10007041c4a4088400202d81c0380305541c0f101f406a15087d4400801c61107a030005041d19015544410500c0b200001039901101c942080396040d80201840300c10144078586401e090395907400d2900d90201c84280960300d5002420302e4590043d40c4100c007100740410780 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 678456016 1250 678454766 678454781
    0x30605011401050f0714030c010203070816051305130b1906081f0315020705010516090801140c09040e0303090a120c0201050a180f140a0602070501051204080405060c01020c01 77
    0x3400c00791314014595291010324091010060311003591440c2c0a0b0203080d0620131501540c405030001c650300e01d0244006480c600003611540200c5500d4009200070502440498400203604d0b50075106030761408080004c40c0c65a18105a02203071100340d5090141c80b00300e05251000c0cc0c0154040045080810040c85024020810014501c0c074101004000090b1080c0c68103503a046a001c00d4425030200180000e8860000d004040e503280204110384100c401c000c88a81109954a40c03d08665420105080e2508441c2d04500350710140301080302030314080014801d8250103000030442c06c104800c1d01d070558204985c01000c68003c19803c0003080303642601e41e40c0409982c02d05481050b203170f40008156015158034030040c40303c1c20070194401d410340d4801c0e0000b020011140c0d10802d80320508030800c1d40f51480424002c3c100d01201007001070010500509540c8107a660f281170210309032643e80140e90142003694540d074200400f02da162a21401003203001c001c20000f40c0d480700755501903401c45690 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 678457266 1250 678456016 678456019
    0x30a0509010e1504050c0901050607060e0307200f0915121204030503040611063c070c03090905060d020607030509100c050d020106030b160207050904050f1c0e0d050c0a0306050114 79
    0x1407c005116980c0c50300709403010b040c0c00c440001045c4030f140383d203586944207245015050103038902d050308110703100043c0080b9008040c1c0c0d12030590b500120a00418440c10b80d134a505c10340d4510300c110810b0515041d2243c00310403400444203030681040703542e445036100350820b440c1c0b600001001e004441c0c2208402c036040491600070b00c0c0c1850440c0001040130305956114000002407003460320304540c07445c070022182d0f1520301c074810740e03080c00786000c1c28050410703c0403400714124090004101c580c621030310740328400c007420070980d40c80c00b42e0821503907901c000d6084050040038000c198403500c0b184488024165640c50351900707241d203414000c0c80c00d40f480c0b081400b168100310052000401d0088030541008942d079051111416911003a410501c154108036000001d0604002c244000000d8a0380664100001d50700d180e21a15000b441315410072340001b0100e400080100030608014110041442c000e0044c0c5140c0c080e0180000c103942c101e1307071003a110592100014414541d801504c440401c20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 678458516 1250 678457266 678457279
    0x90e090703050d030908090315070e1c02010c080f03310c050f06040801090b0a140103030915210b0405060a1805090304030b0a1a0114030a0509010e1504050c 69
    0x59542e032541da03840c1412140c010551122200f500304110501903548014008040d264211414485002c01400440700350000031960b100c0c1c1c0d5401e04240c0c902001ca030b05808288030001405030010340d8007a811050480d11824100b01d88480301184501840c02032110481c51200c0e0101d2615200e40f07044182004c2d402106107598540010321a0002241203c0042d00c008018040090000341c49009a501030021542000c00b00001c0051510300e141c0310341c0d25007004200c1040111009621020f090000401040c0c195a00b4040015041d4010400280a20b007a000c1c034074028074883d801487c0825541020358860304100d1080c43c00b0f00801d40d110304255600c040182c45c02c1c64102c0d80c0c0d4050002517410310f96070804105206024002c075800f9581143c1c1001040c03c00e028a85c00800700791400b2036410f43ca4040b001d09562060141180c00141e07681002e0031038540103800401098084d01c0400e81c0d41d82c40a005907009401d0140f48066041410317069030707610746410b00c942002c040c80116171141c00e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 678459766 1250 678458516 678458519
    0xf07050a02010816171008010609091b0501090308070507050a08030307170c07061d030a051801030912030c03061502070e1503030f160804030c050f030604020f04200a090e0907 77
    0x241c0c011101682036504444c1d01d0f030561100c806c001201500341d00f055030b485d404c1580110350358565400010909100344030301da00c4a40c030215101000341d660f001c0c0600085003840100082204240500360090054055800041d911030005940c0b05d02c075070158030b8940000c802c00c011160030107080d84440780c421a003550145041645401c4034840d4400080000340d4841c518100a20406007441ca488a10343c00c69079a42c442c2080546981c000c03195030200e801035844102c44070751081c0104101180d02041500c80091541020340103040c20380a040105540ca4000145060480180a400c1c0206401401e40c11781030000ca89001f88000b4560000c40f014800f60841c0c0d0f480002c1114040744008140070307220101f031480a00740c28000b00003d802004086400f1003441400170001e8205c0c2c40464090119440c0306c0b0625456820481d03010394000c010b00c6c090580d41c10a81c02030006c0141922a84240d1181506c00c0e90080d00144046400030f05440c86c24007001000c034a0301908038401c00d000b4070300d40303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 678461016 1250 678459766 678459811
    0x906080f0c21031c0b12190f0521090a0518070507261c0b2206030602071b06020304030f0809041e05040c0b0f09060309030f07050a020108 61
    0x88059512880010940c9030300590a54207009440031401104da007040c1c80e02c00c004c601006004808142c40c810301400f10720380c006410008000100310031801c00d41403039074a01d03250380801880b01c9109651500951118207510606941c0700d500e44503022000c030352034000510a00080d1004d98100900900030854201b000d5803640701d00c07a51108031441c18541d100c1d03080c80d202c520040c550300c0003000c40f00000c01d1500003130094005068940d031407254400243c22004016010303a54102e070100d807c00481c001422041030740001a2204c010000c00104004e0703078943d5800201c0e84048002c0d54920601b400303401554102d10090002480c252004504050860300c0b40d90103656142e100038101e80002442100c103032507031781100001007404848921021400090240902011207044800002d041c502155010918042c0c41e0f00c1c1c1d03078108546092040701d60600c902c0303a2001d040c40903a440244010903000308420010f00202d48520b000d0690b80045100141c1011000380c442d8210418640b4aa8102c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 678462266 1250 678461016 678461029
    0x1c09030305062b03181413020306010c1101030608030d0b040507050a170a11030a0905060a02190c0203070906180c080c0304020f0a170c09060a1d0c090a0906080f0c 72
    0x110031803c900480043e01925003981e0351040a5410880d20451040008188420a004100c11001074620642184501c1200c804078170040b02c016010a854078110030201d0000c0402e40e006800c181000501ca81c0c0303881c1494a1904600c000088598845000c2001d509003401100c0d0071030310f107081280c10140c0012000d4442c2100d03010045000c516240020103150103a00103030b5140300c49015650b600d0801c14010800342410000075195407203283c2c08152140118070032542034000c04816001100360f0140300b100c40c2c080e000c00aa905200e4858046058500c6100b400010100b00314170f151502e00206400094030f0054400c00180251001000f0071600107104590b0f01c01d81c1190f180112080d500c000a4410400d41c101d0344442c21107400c01c43d160300d000030707850300821011210344103107039204410441164420b005180314a07524101202541410111841e0400d001941e00c60802403041d01144043d02c45601c01e44001b030f220507041119078802d000348008280311b030016002030405440490b00303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 678463516 1250 678462266 678462319
    0x110a111b120109021c0311070b030a151e03210e060a020124080f071206050721020a090504090b01060e060c03160b0106051207141c0903030506 63
    0x141c8091400c195480400e5010040701940207216105051101ca03058030682c90003071003200401c901401c001110715002840f0741c101c0300e40b1070080b40f6540e901029440a4901040c0104440c1d104400128940c2d2004981304e40071500680b200404a1560411100f106c116840d82e4800031001052501c1240e030080151104100a41d0110743c0c42000f400224014001000802d091040040324002e4503900c00d00c10702c040380e41e840d003103800f2000c64088090315911f0b10f00c41c070b210096400310040002544c80c0c00150b4040e5040c148207401c1c18001c1480501d01022014129031107500180c0c10400c503030043d402001412090701c04200d201090b07034031011585410f0092006100c40c0200c0905035541c1c0408881502100c2c00540e500c1d80101511b10385041103110302111031299210021881520500c2036492541900101080c40c0e141c4607010f65100b0340841c075000705508104041511155000b00c10181004000c0000a0051203828010225100a003c003071154024041d41074551112982d03055 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 678464766 1250 678463516 678463519
    0x11011715060f1c140912070b06040e0609010c02070e0402031f0b1306090507180e0606090409030e0901060306050105040303051b010e0d08160801030b0402040f110a111b 74
    0x2903541046140301c9526002d10185240032050011070441d2540190f000701c20081c0c0e44c480300c00b18588a00d600c0c00c1d182c1002c1500a102c541d4140010804521000125a00150003400003e410088021000d00300081124100e0090307440306244840c150b410804007005080d203003403490f01c609007580000d03110551078200c0783c81c20700402c001041c42e020942c40182c0081c8000c08401248403e80480800382915215201e14146080300148030640501d0143c41c0d03058640e00c80908090602502c03d60001c07003c0e1074540c0082d03081c003625005454030f10810800500a4481c030100030107a100300506040160040c00030113041c43d408004a91300b040540d029a40c3c982499520f070942500780154141841880c4007a039801c0043d036821000d00030a1408058181d50303545a144d680c1c0c038050010000394102c89800181004004002061480c80100e0f0030520080000c20b41c1d20750006e40d82d0030754002c0c44e441070740801c00140550240360460b030100d002e18400f10140110b1003100f00c00002d400c005407c0746 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 678466016 1250 678464766 678464779
    0xf1109130b0403030b060d0c2c0d05030906070c05030c19090e0f10091a040c0501030f0f14100504110904090f080f07020411070b06010e18010311011715 67
    0x1003c150190b004840d002d0700c00707042d460b1500d484044c07a4000d00b01400341c000106042c04c4004e00d03200510b005054004800644404071600d034a8180000c4c6d0159800540c0d1030f00090000c094250381d0b450090100c51b024181c82001241044101800c1001c0021041c2c07240c08480501c1c50340040d8094184100c494114002070b80e035110809650078801c1180107444a40a11600d014299280d5801009418003921402407036402d600c250f10302c441e109840140c110040003008020319172080e04140110528500302048030600c41940f94141c45403500700c182c418844800b040200080303401c8620051508640521080c40d00920410f26803040410b424095a190484002400505903110782510341c4001c101d0ba44000300d41841040d0b40100600724441c42c28a40141404242c59080e1454a0740000d452006519041c6c019510048105003842c1c06c003a04003601d0001020410240340214043c0c400011003002500c00100000007604141503d916000d040c0000701d0a282e4040702803400c180c414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 678467266 1250 678466016 678466021
    0x110a150210051012120201060e010609090906020d020c0706020d14070f020a03241107051c091a04030b0f070912170c0102070303150b0d0b040e0303040f1109130b 71
    0x320540c94200820307481e0200100c208101d05c0340c88000d1490980e5008112042d2150002d50070450f00303114000010314075000c01d00a0320940d81c009901075105000052614861b48a48816078002032a0501c0580101c1420000160144180d91481c0582c0c5060002c0c2d10200e440e04c08507008110000d0200100d041e40b800464440d5203c08001d541c1242703444c0516003203018a20060612004c1d4138118905107051600c3e4080b80301c041c2e440c2c7e95801310180c04041e200d020240034040301c04c850501041140c85000418042c4441c142100410b4011202e50fa2030540c1440000c80101400e02501e4165400400c5411948811894161150061000c002051a0400c0c01764883d20040039850b44200241d480c0498405500500c4002c0c407d80301805540700b4500d0070700b0380d00c4207031150b6a810003040240000760b045980c400e4624420050000810484141c117062840d00200c4003183c0c0f0941c101000800d1115154801c0c0c8010000c4442c18003502d00854034004445a460008060001c0b1102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 678468516 1250 678467266 678467281
    0x31c0510050312190c02060a1b02061305011407080304170706320106090b09011806022a0109090c050702090702030310440604110a15021005 62
    0x92030340003454010201e0b84940e05a0840d60880ea104241001c40358450074100c503490b0340190034280010750000c01d005e00744041c1081c1910001c050071810064600c101e400103005945080181503500d54211520f000141820001b411640c0039015403421400240b01076030000303404604a99005134040004079070001d078a64070038228090a40014041c2d414200308403140c0c0c103c034181d001105c0380360882581d4140c840744900d52040081c050070000401c05441405510a148001c091698062408101500e0300300f00c0d41c1880007090308070800503000038203505135140c54a4071050741c1c001c00ca103001c144203000314006414500c9620451405a40320b1f101645014016415222425005058425507140c03034903009481c0d03441111000e040700d480240110b502024502c60500384150142e00c0803038142e8032000c1c00c0c860684401c4840c0302d84035440360034141640c140200350180c0e1064403105060301c0c580c0100302420003d80c0081c80c1c1d2184c05c0703512468495000880d40c018000403100003850b51604031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 678469766 1250 678468516 678468541
    0x90215090114040b0a0e10090e06120f1e03120109050a02040b12040314040503071716060513050619120213030305031e160503101715010503031c05 65
    0x10000b82030541d001c640000c00207000801480010b00c1c6540e0410a10300305000c2045100d000e500200000d06010000e200a003c1711400d141c02c98401484107050845c01a5041d10300200034003069140d4101c61184850903a9080e088031000342400042d6041c241103160000004405108581c08141c441d00840c07440b520300c0d8102c2e03002d402d01c0401c3e6a5101401c481e56241020305442c02c50006280010301e51108809005039001d0b940c0050103002864503103c0d401c20009a0384003041c01d00d0103086800f0190100240d002c8009001741d0f00c806441d00d1030940c02c1c2290f0701003580701e940201401c010040d8840c0791a50701550040440c14100710740100650004024020421103151100001002005043d0044003a43c800c07442e04202c00f082c55103010b00340d80b1000054400345540c80704841d42d542814020000b031a40700c400f4070a124030b025604e035410040301f810301c000070030b83d174100c11040502060f04040b44e502400007038008500d88000d0090040da0000c4a0091516659550011804040002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 678471016 1250 678469766 678469787
    0xc0c030215100f0b0304050d110a0803150a0303090f05030303011401030c0e030d120b0303070506040b07020a170a030e06060102061810140108060108010e0a0b071106041b090902150901 81
    0x15140f109460383c4034001c0c451550b000382d805960521800c1c90030b8207031501c201c03210820400010080c0c9501d4101ea6507242c1141c00141070311038500503a65a40301d803a180d0031940790082d4029075501c0010340c40c12034a80b006103030369046a8000d400410040c08485420039a44040348800e00c0d000070459020b45044444050502000b98503000c2c40b840520482e034000710b00c0c4804800401c040181900f00c10805940b4464031100070059080130300050046044211503550101a60050700ca1005881d42e07120402207910000b100d4203000850300380c0b0496814841c2c80300d2000c1040042202c1d00744000040d555806c020070702d42c81984000d8000d11011000e000000130241029004e01c0500045000d020040000340100c03e45803184800000e1041014090020600500d5000c0c040700c02c1316840304000c00000a101c00140250340070454030f05102000154421402860000710102892100c100d0f1100154041c4420f07a0405002e40701681c2c42138040e41303542420035880b075030300e8900c1c1c0016291040030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 678472266 1250 678471016 678471029
    0x150f1e0409050115080f15100801050709031703091f0204180e0d0203040e04080f0c1e071205030d0c0908070f03120f0507060b04110706020d0c0c03021510 68
    0x1010140703000c00a05400000b490790080345035100c1141c891044943d941c4400b558040e09a00506200d0044041c0c20b10390760704203d804566041d2991580446401d6442c1034803000005800c0040c208180a280c04010340300e10060b0141c50720b1402c08001c401ea903110300c18131100b0140314480d03009004101c03a6040fa0002d003540c1d580c004031a25800ca003203006150303401c040010782c060b0082081a1602c080103d0f001d485102c000305245484941716400f441c2c00000001c50041d808126910504104003c0710a00310100100308501b5600c48084038280a0a070740014003a0512008440c0020b07404000e58822001c0c070040001c110003004030495480c661540000294003c5540100d040c03c0c030001002c01b6039008401401d400c01c03040104807803040c0308000400002d40c00340b00110004105800c002d00114000340042040d809525103001554442c900450320550f001640d529191528060b02d80328000301e0422400c503401c1c54070702030340721600404400341408041001805100783c1c240b902024046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 678473516 1250 678472266 678472271
    0xa1203180510032a0804111516051011130b0405100509041d070608070513120201030e03030c0414030304060e010809070806040c14090603070515070227150f1e04 71
    0xa607108085c04890040c0d8065030b403441d0581041d0101e007010700c41c07481d080c50303641449443e0400403000c04201c00c0d21020102d585004003a11180503480360b005066481c020842110342c3d50607000c8200701012500c0c3d02c075a0f07595000f80405c02007980d44440000070100141002590780d0303144000107006152600000801030100c0c281ca08480200080c404203440c01c0f41c0702c0b410152684eca09a0311030181c07500308100240d900e0b2042c8405101210f080e500d481c410304000c6070540d10102e00b6130854108840414510b5004601000400e030b40d1900b135002c2c01e0059018618050400b00010840b8a0300c1800906001024020584440042181000410a02041e18814142490881e51000107840740309000d1410f407040c6401450b103250001d00840d0010010720f002480c08040c440c0e206408040c025048005000d54405600c5d8904416120100c0e000740d540a5610202c038004d0004015084d4080c1c0c0313a6408080321507840c0e078251100380c2c1904075649414051a100d18080141400c50f55541050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 678474766 1250 678473516 678473591
    0x130207060f0c02101b050c0f07060e0310090c0e06060705010c0e01030b2e021e030712050a05030a11070501090510050c0f040b0d02090a120318051003 66
    0x40c07107030301920b0040001e03401c2c0da0030210fa84c0551000c1d00e0f40314a8440304c0038484030640b030346280601300034980c0411a805688070b03409040c8415080100d2503003c1008113040d402010302d940340c107002000c1348503800c02041095910940705c26030144070754000c40008008203000303d00c0c2070765603006440e0741681c014001c0c0882c8810640040c510341d01c40002c0c5012904044a0203410300e40724420301110309075803080180306640c04a20b003803000d0140d07070540c0c150f003d41d1f952070650441c89070140d514100d030040250b554404600d002c0c00e1520740c11012804000e018050142a0381d440411241c214488601c040341a2803d204614490310400304001c00320b62a109214042140100b000801d907070382c00c2010043e50b0344104016450344504400300c0c6450304100424401d068100d0041c1440500702c203001402c116100d00428800725868010051074080f030301c0001c040607446030740e032509100024009800c143c5000c000c42c007100002e02c4204181500c4030030f0b00b4804112080d004903c0341a443c500001a13 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 678476016 1250 678474766 678474791
    0x30905060108010209042a08070e0d0c0512060f010b090324160e03030a05030a0b090f0405070f0617060d1b0501090909020603041209030b040b1501090e0613020706 72
    0x1d6018545960081f4145a44080020b4051460a001c041034041009081c61f1281e41203036040700007003404050140c01c210302039032511094501001c1e980700740341100740c00341404100480080c0e0412003419660014040045042c20390b02c0141c11207011080e040e84030303000900040d0404020120802010002ea0211a5103520303200045008594048200161035040c48003208e04100d50f11071581c2540c0708112026045110b6401903502107040040001d0a5144034001102d002095070004c80b0780c1003860511042c054280302c594000c001154808034580d1038070781d014010701c5c01e0811440d05400548001222900c40311005d170515035000304200c00e518200d0007100310917000703406406c3c005404500701241c161007e101e0509250b400801c55415966540d46049040c842e00321b0380010030111280c0000000d2405040d030340514410300c0c602c00c00d4174013411040c079110310f4442d1950401100200400c40e01000e410016005042560b10a00d03c4003100b212101902c90b1b400010407491403d008a4601c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 678477266 1250 678476016 678476021
    0x161b060204031209260303180106150f0f080108060403030507031b051809010e0a020304030504151e021504060c030e2406011d010c022d090705130e0703090506010801 73
    0x2a10040c05c02d81c280d12061707424012081c2030030100c1070200d034030820124192440c080c44004510a00d0130021600340e849404140c060f204507010100490411003074450302711b80050109001038a0303841c18500ca5032420505542d20080944042e0902d0b42d9240845c03400c51194200c1c0413400011070503030541c101d659000400c503070f0005000100402d19078806014500d00b4080880c103c0d400c102c40901c054a41004100080d130011700101c0030f00c038040000264202c20106081c0c1c000849840342c2071440c080c00d6528004011091091003150031040c14032f48881176404c3c025410640015000031580c1c07000c1c10a400510340080184240c4c418860040404000790600488200d494056481c07503445900054031070307540400c0c5079140d4035045000c03e2640d511401143da0001d0004011408203014009e00203100100400140080c1d0001d40742401c03035042000748650407202c11314090f4600701d4401402450380006008042c140500303500441c0745244240c001d034032440d401030305403030940d41d440032020700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 678478516 1250 678477266 678477269
    0x10e190305060a0605060415210b04140402100e010e280b0f0403060c0e0d050c01090b0f0d05090c03010203090f06070207030b06040b040e071409161b060204031209 72
    0x1001d2040100243c0c482000d402910202d0b080502501e0405041008120b84004c00c02007071010000b54103070500002a042c0c1e41d4801d4078082c2c0e140001c10b00081400d000541d4608030549008082190500c00140c03030701c20b09150180001d14040d01d41428020040702c03569518044a94000c0c50f080003c0c81d0b8040480c864181404620740c1c3c8010380d640c070b50086000d4092500300c044010b4007440b0400220381310f40c220720b4420b02c1601d060020192090006211000044810b86159200031414111075800c80d5410001d0108040075908258007416201442d124403a040901c00380c40b032010444448080084581e490300043c025900d0b45802c000282c0d5038200250038941c18403441b000f107980b45001040040a03203030080040001c2c4c1d5514001c0c00050880058007541250b5100c5800340b0404061111070301411142d01c00241c0488440100304030500c01078088ac03142a50840c0c0d80c2074080e0004d80c031480c0d01034540c04020f180c1001e41400030003030046500c05444100180301124035130354011420310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 678479766 1250 678478516 678478523
    0xb1906030b1f080105010f030209090a0c030506032e0605040c0c020315011a090d06090b0901200924040816090905120c071208131d0403030506010e1903 67
    0x148031142c8031492001d14402400c0000c140488010700843d48134400c090300031052030902500c3c1800007000300e040c1440440303040350703403542d2010340c00282d5a02d4041c40c0e801400480003061030181801d11203000c0c41c0d0109420141c40a5052810a18051504440d0003440e00510401c8201c00c01070000d44080400001244240280348443c40764900311f12840341030710000c0014075400304996804d80c0142d0302c804100782c0c1c442004c3c2c40c6100081c00324000c0c2050f1a21072808040c103410884440c45c00d540d40081400b01d00c000780300d4089440041001039443c440d1048441018000c174500d003001c1e08a100e03281c9032210040024000c07030211000240030100340310510899030b00329610092841100c007000401048c6420452004159800c0c80d40548425908501a580350716690f482503164004900b030b0445120402186400340c04801e001501e00520544038018800308010b0408000e10700003c1c0002e0034165620041401a4413450100080d407201030000c0d60469000e000c54030030341045c3d21044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 678481016 1250 678479766 678479779
    0x1f0e1504060f0303120b0f130c0806010309020d0215040302190317070803041202030f0a030b120c03031608042c0c130e0a020f0f031906060e040b1906030b 68
    0x2030040440302c1040100d903010340d18400e2035090200070307002512102d8074003940305041c110550100c0e502c108010010092401c8001800864410094070031000200034506047c50803151001503103030320001900c5690b0403610381e0803603219010030303050502450308081d4002404040422030140100c1051013900d0260702d90303010011400401c007586204000c5c000304002010300100b400507640c0b50121020380124015203003405c142900303515042d003001c440c00f800240c680e10000354905041c8100032145505001a060011501020a0380c921a03011810718200c43c0c0c2542005010b45081920040c2120210024031496040105648440c00f0251601076030f12182c045001c02c0101d00c12101e60942c0032015003480703803030110f51074840c28000745000f264070b0702042b2480402180c000104450850007411070348904142003290050042c8a9103091243d1401209015141c4c01c50130184049004940114442c40f115000c1000c4010140042801c00640000890081d8250b0402c0404071401e5460 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 678482266 1250 678481016 678481019
    0x206010906030c0b131802070b132406080709020d0c08010332011b2c09040303020c0d030b12060609060d05070f0617010b030f1f0e150406 61
    0x2100304860a0388801445414501e408000d64900200900191030461040102556031210380e120264200719952181960002d221801c1012400d04540c20a41041141c582c04245030790b2903241c8084049899200b40004200da03a04182c25001800600591825502c4082d556041c241c042c0d08603407440045070742010702c0406210321505a40381200e030000c078803502401c4200120320342d00c0e5288882d0490003054100c8205100e03000d00980d0202400e4107040c1401c040751460040490b403203a44004800c10600d2442210702c4c0404000c00300040c0c0440b03030203a25864a180c141c0092007045041495402034a1114000c00d030954440c411652082d40d402d9441d80f80e9429541c1c99900407901c003588141c0320004240c40b402c226808094403072140084800c020303141c00000030100b83e950b000e00c00084110385081e0180140c500c540d4010013810000c01e0550800c849081c486990040181ca1984010166102c01740e20b00e411010083c15140c03c4001d840c1400c50000c0b001e100f0941c061405582400c60 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 678483516 1250 678482266 678482279
    0x140a20060304020a1a1605060402011e170717040b090105060a0302150a0309050307080309100e06040b1f29031306052511071410051b0d0c03020601 65
    0x4072485182c0c01080c41c180f403410807050241e108a00c400da02d4581d101448066003500c003c400c04d40c1e00030700a400400b114501440014050003c0070031030490806240d2241d4000358205088004032010344800f080e0320741d01c199040340e0740104020403440000b17001c41030200780542c00d26000d000e12480340007807145980d100103000d2101c3c01844001d40000301d6440e2a40e044140c01d01030000b10125107000301e040003452b04c406185800200081d01c0050002003031014000382001403211540b41254148100c1c6a4206856102c000041c000780c40c0741c2385500010301c140780c03c082c503d0080000e40c3ca01203065848281c101111085810304480c00540d15511141c886004401c0d20f00c51420f512071400103112551380d4401502001d005152013034540301e100c000494515003a0b2440302d0036541d40d00c0203c210658880d2501c40660703c603122011041c160741186403620130000c8509006403c000341d0f80d8881a21042c0c0d0b101d1500802d00f1755008800700303120f01a43c01031a80303050038002c0c2d0803103925980307415 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 678484766 1250 678483516 678483529
    0xa050f070f1d0a110a170c191d120721020a05130e010f0606020717190602070602030a090b180d0f0207050d0812010609230103020c0601030b0105100314070309140a20 73
    0x184d25543d07622000b800c0680e42449036600300209c084880300300f040747e00c03020f02041046402490203100c6800049042c4075a03e06a8042c0c051550000c40e2006d1019845d00030400f180c4150040038001d14104000c989070b694184c014a403c1c111450007042203509102c03042004201c07c2c090f034401030117481ca00003a049501c65000d06103442c1e0f000504046105841489840c1c0303501d010485e0344a40070f0102e00d02081052010790300c00c0100520104400c82d0714034000c1350541008111541d42c14129400d40300100c4001901400da0304503090801c01e070701100c0e800764030340b0116030711160703228100080080030050410003800d4403088254040301030f6601d6007010f465615050141c3c813200d400c1d11503d04001c3c844090145103044043c10010b00c0e10304a52207041c1030000980050300c0d900c440100400450400031410110380c007036854100200c2c03800860311801502c0c041c086070304140c1c442c8001014407100b4400c154080c00d80714215043d00109140140d41c100c04001e80c031010b00b01624030304805041c0b00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 678486016 1250 678484766 678484777
    0xc21081801091505040e07020109111903020a0807051c0506070c150c0201050714040617040203011b0f0905010311090d0c080a050f070f1d0a110a170c 66
    0x250805081100d00220920100c1981152604001880303800003030700078041824040c0355200e0341e9515921401c004403280c1501014221000f160315041340d040109910340c40c5080c03202012690340c9034031080604044809452a000039500405030f20300025600c800040c0e400454134143c034442c0c038004003a0404015159044005003032074109400144c0000c1c8600092100c491081c5070514507900074407818070071139410044000240c0e43d07400900c000315410032406590743d1100c01e2581e20380f505000008020300308820100820645580100b400c642d030071f4200500f41c0c03090520146464046060003002582c03080c00d5100400d610143c081147d500c24002c440400c00405035051502c1400b005110021280000584e00d00d545980e01040b00c9105214980d00940244000c0c201c40c8845003400c0c4c10700e4a1640041030100e0f42200420002c02c06081d8540c030b100b41014640301a58034000401d0103051010740450f640400042c140319070b01d03000500180742c11703186555815a9035401e4400740b000c1c07044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 678487266 1250 678486016 678486023
    0x106030507061106221a073207050106120312060f06200c030f0d141303030c110d0c03052e0c2303011a03060105070206070602160c21 59
    0x700c000a256070880205c40051900d0503150306140b0441c0f91112115441d00d5811011182c0b1580188802140e20042e09013041008243c124185801c0200b9100501c0c01403e100d0b0100c400841c03500240442076009200030b1030580c208408040107440d00428080328584030b81070203441d00d400820b10134820b00314801960314688680c5001d00b407c840202c2e0012460100024a114008040c281501c003803119000d41ca41443c020100340c8103088000e03040a05550000110b075000b40301c0c0311020071080c01c100c401c07650581440f01c140f11490605000060301449082d40142011420100b00810085100101d03070040d015542e40d000c0003a041d02e0300700c1c40d24061545000c59003010001c1e504403a444840c050103641070030b202c0501030705040e02c2d000b5150407555180601c0800104004a040300d0700d241d400143e00205880c6180c42d40020b0018090403001070f0040310b0104041c1f041000c00d41c11aa82240d018041d4042007405203000b9003a40c0071802080700c0c0402c2d024803040e00d85c42c400d07210348500c0c0c0d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 678488516 1250 678487266 678487273
    0x30c12020910120209040c110c3a170304020a080a3306080102130e19050c1c0911010504030b01090509120a030603050c011e0e01020c100201060305070611 68
    0xb612035085681882039104440b910740d0820018010b039035903224020062485888980101c04c61a050a0403e600300070118040c00003918640380801c4015591140540390301c0b800c83ca030099588280103c440240800be09010400707131038400212640024500c0340c0e10132141c820160740c84989043c0c032904004001041c1c0c0300111004242403101c05e204c5201c911001e00041d441083c129108801e80341c2c41c1d48134001d26540080c43c071140200d1a103501010b8452a00300076464109040500718425000c0c809110b0a660f130b00c0421454910001144c000c80390152200c030f081220020b00f403005140c800001c4401c0c0824010414255020f6002e48088a40041000100341c1c17806c0700110160500900214090142210340d05440217050094034401042cac0e0303000a001c17411860700e945400c03070310b4811340d05204030081321365101c6040f800070b5001c113036003403500c550002807050041c3d11700703480c032164150300c2880b80c0200030101e0360540c8590102c07800f030390448803a19500c01c8290358a40a2180e036095642 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 678489766 1250 678488516 678488539
    0x806040504061e0b1207030c09020c1e030309101506120e0601032603040b040305071704060201140109020406050a3c0e03011e1d0a03030c120209 64
    0x2400394812940709014034008201c8242260541d41002c0300500b0310444650349600e441000e04040c80441d4504409500602c082c82c115118030720120f09611626410b1500020b0801e00600c09104040c1c00030304c0c8140c4030840100d40305801e600c0c0c1d0000c40c2d540b2406e01c115082c20000308a03d0103900d01100c49030300ca08181d40e05001044502034034440b19840d4a0303450303184c442c101d80d47c1000854001c0d03005000c0c080c0d01d2203803d480300448075a241050300f00c1c84024000d00c004a500400010f0308079906040140c1e07180c40600d44546410021b0040d1040e0000c08980040c845406400c2459141070a01c1d4003915682c076011080100c0c00383d40034400005606101c2100380798050320544046841039403001d140604d0315440100d4140f49181c2c2c175a5003030f0541c0c0145091a070040c05840403070000314000c0c0000c0320001c034a06080100100701f1424151901201128500c07850b00c0340c4c0e149a800015200340084a050180240c01120080310006598800006182c5028404c2ea80c1916006120307a1441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 678491016 1250 678489766 678489769
    0x30f03431d1c0314160519230109050a08190201051302011110060f03020406080c090a0506011202030903030103020114030c0a0e210d020601060302160602180d05071a0a0806 76
    0x3070008410071800c2c400a5220045040000da0103807104005c4a0002800c00c090713440c1c41401c1840007410b0681d030303142c801100000103141c2c404450319500d51200881084584151890240503004d2000e01607004240b880401d0140100c0107000641e404400700c09405000d903c12070803102c04440040c140054019540c0040d032056104441022690086983d00c0c0d50f0101c003041100e10980c490036014800030803c0085003014040e0100a003d0000a010f154071a0000b09170340040041210380ea043d42c440000c3e174a42e00035019107603056a03c0e40119140d217014410150f4035030081c0030580c0401c01034200e016030f02c503020341100d100d05540039410b803e05407012026118070314000800c6900c80704c0108014607600c003c022001d0032540b8100180a140298a4040d04241c0c1c180c20a800305401000204115002c580c242407990fa481140140e840901d808503401c200810200241d00c98116810300040c45000640c110590301800c0c1c180030f13552180c8030402140e10641040c1c0c001b142100d400140709 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 678492266 1250 678491016 678491059
    0x60c090a171b1e19051002030301080d05030106021f0213030b0a05010f0b0a030f1413030806060a053c180102030909070f09030506090f0c03030f03431d 67
    0xf0340d10321050f80c545515000004e100080c01b8030584d0040c3e0010004116108007000b0543c0142c070b8a09060b499541032400c020740301e540c0b030b4030748485101c4180e10140d07c04034a503046552801030713001e000e0301c82c0f516441c04010002069074440c0c496800c000000c83d511600041141c112040c00000038905100a07000340c0190042c51182007038156913006600000c03545104003071142402824071048a203103031502808810000d0081e6001d404144104146190460100c0759400c0710f00203040c0c013036400c05c0181c003e00b914046c000c900d030040485601d00159489006408003000c1d40094185c5c0c0001040120780d02c2c0101d080c603552161007800840c1000d03004440e4080c260780b4a180150089403241ca440c7e103405400d56240e541588509050072900c0f00c10701076424204802c5000e140380180c0f10404040d11f010141c0000110313016029a0241b074102d41d0b1004c4503d2082e0014200a00c0d10308541c0c100e286205480e400200f422000000306503c18400040400d0400502500c1c0611450921100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 678493516 1250 678492266 678492289
    0x30609020a0228061802040e120d1a060c070302010908030703200a06091101020d0207080303150d0f0506010e1e0714071a01080d090305060c090a171b1e 67
    0xc03003e182c0100700104103a0300825004041c442c82d140c2e841c030050b03c1480202d40010b4484019500035207001040101580200c40907140709080114501021741c201f0000c0a004d5802d455109800107090303e01c80c80003050302d5048078000d0b00d50a107815a03a10556441f403242c00b0001f400928940d40340d0b88080701c29113a841a010040313080ba1900700943c3d07608000c60700c00d617406030f40c03110a46c10508215a0b041180c2c00d070f10180c5101605486140120269480c00040c00c621106803040040c14a80c2e15610b20300903000341c102e050110403885a00b0b1541d100d000030300854502c9aa0840040d0100003038401c3c4681c1a0050343c50034940e0f40c1c64040c1140c0140c02a4510f070101d6100300840c10118445d206086034000280442d16190351605020300d1514104100b410240000d1003801c0004c168042129036004510b00046651403440c0b10014103101e05071340104040e10784480084100302c80014440e00c0ca110120040e190141c082030400c04201516040740c40ca260900358400401d0501c08100e45 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 678494766 1250 678493516 678493573
    0xf040209010b030f06152a0c0406050102060a02070f120c050705040c0f030b010509040213090b030f1e03040e0103080a030b0316060302070215030c0a030f0c1d010c060e01060303030609020a02 84
    0x1414845404509501d81040d0584110304400305047d02070224824080060301c800221402c01c400d92920001079100c800081249114650208220081c030901300311403022581d0014a800c3c0c00b40744c1e0701000e85060200d00342901d16100d806800700d2582041c0c850780072074201c2600c605810f859004011005001c03d034070700a041040501c8000c400c3e84031800070300003900c0d0040e982412141406041c40031104140782082c4a50300c4401404135059022555420350040ca40660200004e01c2c041d02d45184a60307845100f403c0003040c000428400c1000180c8442c04440c2d40902440625404160383c3e41c1000302580288001101c04210003070190f0b000b0003403140301420045a240965140802c03076001151030070740341000010440500ea602d44612207120b2000c00c4100b03c2601c40900081c407015203400a2040400e441010b03050513809801c8840d45107901c580184001615826a103000e0045480201c011074202000442e0b22146802a540c4d0043d9982c010300c0d4650145032580894100c61031841c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 678496016 1250 678494766 678494809
    0x2061b0304290a0e01050c07030e060307171005032407030213050303040f062604200307030c051203190e0a1a070b01170628050f040209010b030f06 65
    0xc41e540074142e180e0a00c1841d1000000481201c0303100b10900b55240141001110f01e020050b4400003500044016103400007510225100d82d203000e000d4400e4080d111800010812190810142c9038051340518203861098080d500c00300040c40424950030810148981c01707203015000a080c561180c1d015019210f01c3c0caa42440d15551000460309591260300301105400007024207200341500f010170650320b450700c100070700e00380f64020030420384050700a40000c1004100405050803129502000036035207034020283d4180550301e103488a854061481054080c2480300e403164995100442550500c103031100001681c505411002c440f194240b86800364000d10841e80131074080d10320a42d406c0c8111842c0c450950700c6056041421000105034400b941e142c1010709a0840c0030300c00701d0038581146002c50340280340485084441d4181c50305007002c0400d18600030400c144030010400040c0602d000f07940c0a105645c0b94108141c4500c0112284000100b510300440c0c0503041003440f40358505541c2814 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 678497266 1250 678496016 678496073
    0xa0f0c0c02120111071217240d0204051302031b030703112202040e15010c061508030c070509062b02060403200315071709010906050403050a02061b0304 67
    0x20402c25041903170103840c068041494684c40729044414410f202003081d94894481c54105105107034031404620039428100071100d068440e4803181d04c090035440d030040007807100c0d1a0111040300b1010704018241d201c2d01c00d40c9904050200911081200d444001d000740070b0041c2503440c0c1c00c1508a8901842c2e0304000c1c40782103505000340548000441403090b11000d0396552070092540c41031000541802c460040c07002191107545c0c2c00081e0100425031103900811b0750042842440200505540107a040b800005100c3d20000710114102095a00171150420f0303580302d01080c0040c03100d814030b840e0840030060440710f03501a0100030140202d4402003e8038905901c03a580c22402e01d10b0300c0341034140b80748503003076450b92468180141d0031580412000c044403882c00520041c540855805641e100c100f8500206840714420f40001c000c0a400040c284070340d08240c5002821680500070741c50040c060f4402081410403250036840201291400325811910b03241c6600120fa42800d000b00303d0390554650 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 678498516 1250 678497266 678497291
    0x810050910090504080403031112070303051302100903021311160503090a0905090c090403020d050d061a04170106080a2306010b0c0106060908330a02030a0f0c0c021201 74
    0x201c134425441440800c2e00c40349149405000c120b800b40e00e0811340e4000c40004040d014081013030392001c40c4c1502d0003080702c0c2c980901d01200321a079088003a4111300c00845010156401503901c0b400c89100351900b02424480c0224102151200d5110b0b0030103500400124541e4814106480300c594000c4003600c1c5401c0070070002030198056079100e60000364442042080031402844002d0590382d003610071170010303e003035a030094442104405d03050900c00003051501540c48154003100180c0041100320040c02c0707c1d0b4081d00682d800910944c07948500c021024400c0c001c1c10300403042222103160041604020944c0c030100050b41c660713074043c1c02600792048085040030822130140242915050740e0354510380c034001070b4207480c0190071070b07803e009064404200503000002c21100c0c2010b05171360101d80e041c0780b0340c45144450403c0d02e819030110140091085060440d8002c501461900408100d212030010303540054407802043d040204a605411401601344148442d500000c100300000d4002000c55 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 678499766 1250 678498516 678498521
    0x6030b0102160f090515011e0c020a1e05060c06010302091302040903030c030f0204052206080d0e0307050a030f060504020406120b060a081504080f0f0a031b081005091009 75
    0x9100e035403c2c51201808020740702491040e00c0e00300644140900c026010000060900000182564175510700c201d030340d060443c401c2d01350380462940100000c2082d51b0303514044004080901030305004403110400016103180c107200f203c22004145e4050100d80c2c0c6076408021000c3c00c0100300000c03140200704400c005075251300c607585402d80329890016901c0e807110b03001411281d222a02da0159441000140410340c0c500d009510444100300a117864208440b10507006030055070b010071414454032a00d691216040300840c1e64030740059003121110781c0d0360030420001c1d07000b51002800c6041550407440100f0841d80207580c0c02130002d0000300b84950741d403034094460911b01405450b01c1068030305003d898a00403000c440101a140000c1c0024030341d203642c204010a014100810b149400141c0c9030000d003078107081d107240e110283e099a40722031b201c141c00390242807a07081c0754015480c01d126400380c00b40110305450082e0041c3d60001c0805003080184104200c002e001d81c1e00301c0b036500d04006410045030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 678501016 1250 678499766 678499769
    0xa0906050c0a1514060a0b0711030a121d180f07090e010801020711030606181906060903150e06190204090204091d070b07030e010e03060405070f0501050309030406030b010216 77
    0x883c001014880c0054449803004060030491084e001c0a0040000c0740050301074980d0369810442c07810300b4440c0b6400081c504072040300002c0c062040c40d00c0180065030003100103201804040041c2c112074400600300324810000400700c08260390402d000c140280941d001c1641e108146041480382d85441e4224011040740c00d91140315160340000701e240030090800d407540d400d004107078001e1101d0b04004000841102444a1010010f040e440000d20840034100c8400c5124104100401110f070325220010501c55150006a40f2603150501224034000d552088404e1003094501801d0152508480c0300301d001d1100d11003424258003848045249011032008100504407041c0c002102d50880c8030041c450181d0141d61903d07038001030001c0100003140811603a5099061506c0804081c1450041e648000340c03910043d0035110b01c00030042041000510174040c1d034550440b20400c2580c0c1e000449242c40100d5179000150418030041110b14001c0e04030800f0700b0014010382390583d213000d403880c078045200d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 678502266 1250 678501016 678501053
    0x1424030106020f1b191e0611210d060b030118060e070906030203060406032102010b0f0f040924090303110f180402160b0402030607050a0906050c0a 65
    0x4001c0c003070301041403c00d0045810041d00303161110f0303010303c4060020704269602035070010301c408220800d520251005003441c12074030101c100a8420b90f0040704c0d03031800741e80046904410044828200040c0d9017081070302e106520021f94096078001031042d0003a54000d0a400e40310359010600c4004070b005580a814002032010a484124200a09840044d4400c044050215040c8800680c1c040b20b0a0243c40c00c609001d40e681d04c5540120f4003c20f41ea42c4042c202d045005502e6504605000c0381100005132a4000d01011f40c1800400c0283d0364800c0610b68013070f0b04000030303d10f00e0034542c00c0044424001c1115090404a0031100302c5401e250a40d148230460380d681c406070806800d48074a6840d0149025190b040c03001d08023141c082031042c3c01d52210052110202200142e465404480c511362a50103901401c10719850f002c1d011303100c281c404910901400c4005410188035105440702c90440d5914901400c0c50040140c03659800707450204c1d92030080f00d03d071402058025640341c080c0c185 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 678503516 1250 678502266 678502339
    0x5100e190614010e0408030a11040b04180609021623011806050c090f0f13060609031a060f12011506050c060a050601020d032708030105010915080114 66
    0x70b840851895968140c00030401d00348410140404600e0013000d030f91740f00e941840c0c0010208c0b0002041201c0380107945c4000700b041800100402c280d0b2070006802600d402d000e60900c1042c0c1c50702e0171031050303020348032030843c84120b2540c1c480b020800243e15003160034540c1500707500880700b410f9042e094070203640c003c41d482007540405600f00101403203400c1d4000e0325400c4141c107000116000503084688081002d229000c44821a5040c0d62061032280103d00f04860030401503950701d002802c0941940f0040d640f042090b90980740601100130454803c50000f031601100081e4181040b80b10008500001219941e6031281c1619010041c40040a49030703e417107407510f801030a0509840d1820003080302c00094144402d01c00e250b60001926078407400941004600310800b15034100b4040205101c5507034042d4603030401400d0080550040d03060395001ea9801e0405501c0c0e036201c5600d07403890200342c00010000001000440590100d111501400400f001085015810419285003145244241408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 678504766 1250 678503516 678503531
    0x110d09030c0b130203070317131e080111070209190221070309050c09150406141009031e020a050924030c03030d0509120a03050108061305100e1906 65
    0x52000e58142d8401c0c0b4107503e4940d4502c10707078007280d00c07003103184001001c280ea800803101e071035000101902d800d9140c003126030240c01d40e18005500030103d045502030520b21804e501150740d07070040c00b5640c4041d03482d06c041031611056a09004178110300503c2e900d41003102480d40f24010445000420030203140c0310480380e45610011458100c900c010744118141803803e0110f800103a4049150700391401c084440da182642c0303841100a031042c1603d09550304c10301d000d90108800c0428200d81e05007850130b648104a40384a644140c40c550003071701002c0e010360003001d50480440e0300400c10003005031000e001c0d480717069910030114820003810f0314030010a120380f20070420107079070060003102c9058040b8010918840e95401091b264842c01040c00001ea4942d0b0001c0c21100b010400c0400b01001e00d064660340e01c0ca03240d0001c00910003809200303ca4041c29010850141d1648034a006c01d0b90048050240c900000c00d0907401812540a4420f0074014410501001c1c0350041052100718082c40c008510076 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 678506016 1250 678504766 678504773
    0x4141203120c180409151a040c120c02030903031902030f18040e0102040b0f07140f0a060f0204060917070506030a152411030c011b08061012110d09030c 67
    0x4034071007034444c0901c0c03620410380c0102ea0040080905405020310003d508051694403448591040080a40060502d1109003031240d1050485808509d458000c0141d01c08642c030880c0c40b032043d0104c0c558160702c18800c4640d071000350700c050507003003030140116885d20403c1c4000006c1600b0045440442000c00c0029a9041c100b50256051301c41d4000002c5250a044c811140414000e4000c0b2086100010464a082000d030070303503d0070112581c0c400c480082902580d090303a6281941c204480840c14180c01c88660451802a101986e246468807003815080041c5000d4040c0141450095072041a400003042c0c3c0783c01d8002c60050b002c805003c01d24070300c203a001a02a50700360703014003913488040101c20300e884114000040e007091986031a0003412a104110b610f503029940500b9000d500e0010f20300d00c1d49040c420402d817021903075140c02d10301c2c3c1c1d1180b04010300c00007500281d0020a41020503000000c1065002d00e8083c00c01903001030805100800d04403c503036104808501040d0b041c0c0405091 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 678507266 1250 678506016 678506047
    0x30503090f07060903051501210507090212061009030b0c070302150c0a02010621023c040e0f0a080a050f0f030703200d0513050102030f010f0503010204141203120c 72
    0x441034001f030300d00001d514006140383d011049120000702e02d8204019902040400e008540c02083c08440a64a0b68801c0c10900c4c4c41000075111907110365007801551511034024480c0d001160b81200348400b0580c0c0c0c28401650300d0340000001c038218003603404040c00364203010035064040c42610b951603842d402042e8004e400c580da0b58220a0b100f640380820f401007815440c1241c00140e42c107445440300c9403c0c406903540f02030020754086070540388045034600300345c280c108400288001210280110051041201d44a03102d4406681e07054010300221004203404c1d500800111b800c51401d503140040400d0001c8142c0c020201008000c1000801d1011081d414040e582c1da1140c02403001b100c09005034000d20152083d40300303400c40c0e2a19070000880803652003401800c10ba80041c001d40d0fa03450714540b4500c82071024001d1189000030320401151901f814802d4400351076180301f441e5480f00d45481005034039102c11000307000d903220810146125441840e1543c2c001c18120b0a65a100c0c0030b00d4001141c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 678508516 1250 678507266 678507283
    0x9070e010503072d0f020111040302100207050315062e030506030c120a0b0a022d090406030b0a050c031302041d1501090e01140103030503060d02040203090a0b15090103030503090f0706090305 84
    0x4c6a0408c6034144190460070111803c81e503040301e18603101444c6010680c205840c0d90b20455140c007603e10003041c030f034144041440c42618200d40300d480003070b001090401c0380400500c4407a540420040c01d015030b24020385c003841c0c10074070080c201d07074800c00750500150622034441841c40c00c0f504401c0056040042400307806820000c0d0030b5082d42464000c42204100d4506178058042540b802100c100902d440141280c0e4410f10180c81408910f840c0d091556071918191030359409030f443d00c0e0024007100480d02c113690190041c4602d901c0b103620f054080002405900d5030070801c0009491043e1580c807420822000e117003000d04088001989020070300011501c801c41c46001a905140d241070b107245102c0001e50540368181002502c0e910ba410106441c1051030b10000d420910010521060445c001a940c000307502c944686422503481c4841d601300e44086400054000003e00d00600020780900051503200d5804000c40781e0003000d259a5a14114081c0e0000000c02c446260510612100f40400301 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 678509766 1250 678508516 678508547
    0xf1612021608070e13060b04060906171501330f08090c101409280b0f0409271a0106030509060a0f0905030c10050609070e010503072d 59
    0x800d1510700f141092040314000c0100c401d00c105c003642401040702980c0314507140c000c00b030400c2111a40714080000105540c2c0142040f0240228005c1c0132500c0c0094100040302108084003040d0b480c1084a805001d41e03031040b00004161070742e00c0780220044034940f10580304660380d1910030f10b40020f00500600006400b0702c038283c120b84035210b081c0e100c5881d030381c041da5094038043e4071880c542c40c4a600340f1b00030302e00f9860340800c46c2d500740304103000007260905501031117480040182d40d860200840500c80c00902c10a00ea80602c07041000c0750069000c103444520401c2c0c0b81c1501d136405640d8048800d9141000c460062891021070304a8040044807405003045041c100100d06018810f10b40d503000040c01400d1490311004104d00b0741d1101d420041c6004e03403000441ea116402e40d525070380c844e20418070f0462b01a1030310380041c0c0d6038507098450301e00039001c0e030300c454011a00a8004507601e40c001400348060040780e843c00845603603500246654488921702403910542e0301c402c004c0032401c0084d580b2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 678511016 1250 678509766 678509773
    0xb0105010504060f0509010c080304211d06160f080c0c0108060108040f0203120a080a1107120804030e060a0309020108060307050102070b091f020a0606060201110f1612021608 77
    0x140f0445420420b02a43d5140b242040364941003002c0c01201c0c101d4120b0802082203001106000c104500445024202c21851031646034141600c5811101074070a00750141000c0b444242101d0903080c5040140f00b06000300c802182148090b03140c50714482202c20084926000001c0c403041311741024010542240b00c24a40745255042c0000000c01130080a40043c0102d0b050941907001c6681c2007060f072030415484100c0546904960f10040c10403402112014049810b00380010140e031301c5a012241e00907407100c0c5174000340541c0f2a08580c01c80c03000740110240001e001c42401c0701ea44a002600362004240d5000c584014584001004950081c001501a0303005400501480c0c1e00460344400ba80c4100d101c40707480321a03400006800c2101e4881304003243c400e009a51040a80c0811941c1440d4010b1200740906540c61804030b0032205800d2440819040c140f04e03401440c7c91910041c02c11000485050341010081d445c0c0142c0b40281d100040f01683c030444200c8040b0800202200c014a11440076 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 678512266 1250 678511016 678511019
    0x30702151e0c161502040f0e040503040308130f031118090c1c06060303030b2403060108150a0605131a0a0c021305040302031b010e0d050c0a0602030f01030b0105010504 74
    0x38441d6058025100e444060004905600c8202e05405030041c01038029a800d04001d002d0816500250b006018905c1c00105a01000c1040c1c0b407a49056400b03198850019494545140c0b2040156003180c0380311038103010380b02d60000e154950f0300da40902540c0142006100865007200b0010a4910030410344c1c110a201020412070a2010401d940110390131b441e5039814000c5400c400c9040e8403040c2c4020f0109262140101c18164154460f10031030809484c0626a08480c590070950170103004a02038589104000140d41ca51080301e100350800a0448130b5072411005e040080d04588990304004005400858070003244c4070140d1000008015003440c000c2c00002c10f010480d4244114401031041c002c2e00205041152036243c0c1c8031780c2c20210b160040010341060300e0002c1d1a9807046210b130410381c18110a4681000c41072141d120390110300c0c00100f62080000c84182c0e256000b113028400036004429090300410001d00096111303005400841c21150704502d046078001106820a60400005220 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 678513516 1250 678512266 678512311
    0xf1a10061d0a050603130b0c09040c1407060908040302060c010515010f0c020d080f0c1b060a020a0b090102251505100306050c0f0408150a0b0d031d030303070215 71
    0x810800f07440741900c0269581d17032140580e400314514001c00901c0051881c0c2003140d44698040a80701003103085400740021040d04d50b084035130079040c03410380100e03031030400207100012a1a800300c9141c91040450b6428260744c5e8000880540020181c0200d903511001009a000c010780301103000d4020900701029080e560148c001c00a200e4000024007421500c0095414001550107450790000002000d039500d00c2d00841d01d0782c40c4d020681040c13001d0210209400c4280c904441500d43c00c9206078028481c0c0e40f29a110759400781c2c4060f08008107550f080040b007040d01441d907000e01e4090248141e00024400034900005080342d420600d031015450401441000e00920f800c850449801031804216a103400000c05094416201c8940380307501c002600241c145000b051040c004d0080e0b041032126545ea25190f1810340b04100c0d00c05900c980d100d4000d20009010361400380b0040b1500724052070880b045800f00f40745031720540c1c00d80c0259001110045140c01d00c08502584590500700601c2d072401d1186 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 678514766 1250 678513516 678513529
    0x21c0509010f020d02340b041e1404180501060f1d07080c070302030c07030f1a0c0417030c250b12010605070f0501110c0706080f040f1a10061d 63
    0x30406841c0035803042d030035010000121030000da1008a060612506640d107c10411541c401d20035224a102c0e1040f0501c81200601720315000c8038852480100032000301010031004040382d003400c060b0390301e1580500c00801c1003440f40f40d000c1d000765203070303c943e16041003545481126909204400a101303030040008565000c84060703000146d420480c1e481d43c880303180690440c012041c01107002d208a040c008140b1050a07050910f25000700c00300b03440d40d50789480d0310549890850b032240504030200020007100403205881d143e40c18111041d40d00f0861644950b0b800d05203c06048000880640e048144600c0316481120041c22a001030720b20f00701c5411342e0f0118120052245500b48240490140140100700905001c40c03a4010000c1184500b681b0304400380c0d804c282042c0c11148503818022540a005a1016000c3d8401148401c559500c907942c0d05031004e2581c90071070350155031000b80700f1005145855207000f03001002402392000c0c03c00b08003c1402c0325801c80d11003206104100f10f002521480c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 678516016 1250 678514766 678514783
    0xc141212041a041e0e06030d0e13110d0f1d0705060a03020409020313050106050a050906090a02190e3d020c061b07050a03080d0507021c0509010f020d02 67
    0x58601084400c502040840e902a07907212030103624041c20510070131001e060740c407401d66031814426101034844205044d80d41f20b1100c0302d0030110b0b00d007a64400d42450900d07454204030138001c4004c2058a810f40c00e0101035003151020b021502d0301c810303510280322038034000c2d409601d0795130030f10510b400d041000341c5035200e034941709240c0201c00028060031458841d404403006003036145801e43d03603420080100724500010a000369a65442e0032808212464038000f88401c90700002d10a00d03103600c03010200300c000000900845003aa50030400c0300c5510304002c174a01d000c802e803a22240a090303000424482c05003040c05400592404c1d044012240d0044614902e02540141d82d240f0790390080035070107914142e188020254403110100b0f20f050600d4241202d000d1084042055070540c668903010310454145a020041c40c900080c0a41b48100100740d01c056030003403c5204551041040d41090a041c060b00c58031500003610008080b442941c000c00c12480001181c4014820b65520700802511000324 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 678517266 1250 678516016 678516029
    0x30105150d080a05191805060f04050418020415030312020703053c07020a29130b0d06170a02030318040905060703140a0603080711010302070c14121204 67
    0x1194100e44281304005130340c0c0c1c0c101c00c0c0b0f010700305401000102508a003030300d810040340c50800e5440400c4604040d401c3c1c92824012800090034182001d0422005d0036101c20003402c101096804680507944602858010440d4410745110490560400601c4400802d503002503007030040006c040060751100c01c50301e098035140e4040f403d0900c264403003031072088200e6002100e02c1c07006070f0a1180841c3c0e00d00800c1e07241e208558420700b580e51507074484661100d02246071204c540d002441402030301d84200414003003186d0141610025215800039280f0741002c10495921940c403c001c1c0b0201d4000f402c007109004d600002012805101c0d400240d481c4503003842904404c5a407103621a064496821415a541c0d100c4241da10368644280700a0080482c0c0c01100b22884802000c640818810b106d124180d07904440d1462a00200351030313001400010b000b101c0d04055007004954082480700072178030082d01004509010b018018070401007108620069800c01c0e40151411801040d11803040707030300300c494 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 678518516 1250 678517266 678517283
    0x302100504020105090a0b0a1107030c03080f04170703170702090117031303061b1805240307030b090c0f120403050c031308063303010f09030c02030105150d 69
    0x41d98401282d10f070089441d0b0315001040300e6804030321844400050450700303a043ea208001601c08500f010390791200c500c4060056580050f0900114030914001c107110000781e816185801d540d822002000030f04a410060140c014000a01c00c004072540c6203030f00c1e0070001014a061000300d400182041c8d90620130094200d00242b00d011008000740251908002c2c0d100d00c0b11542c03540c0e0b0401201420446150010341c8039004100d08142e80070318200100c1c004080f120300401402c2c1801d0001640841101400200701d1002c09960795201000031031203215030382d501151b070080000c10b0040c2030340054400c6903e5501480140044051001a14030b100401d05009440791664202a6118441c80d0203140b92070000140d180e01d50400c0d66008001c444429044901a40d0b4484d80065a401440d4002c0310100d10000440380d0030304d81c030343d010a005400800000751102161402e9044170709401c002c4002c03540704100d0005502d420b1050a0b40003912001e4030400c481040700240d00303440510401410140b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 678519766 1250 678518516 678518521
    0x18061115061216090b03150c0705010216050a0528030e04090204060b071505130803070e12160b130b0703020a1703151503270d051c0903021005 63
    0x2d45600300350216100c01803c1c0d944100302c4010b0611000c480340542030940d07040030030414080c100082c01210042c0da08840e1003a41c2c40d6094070320015481440291960340d001e108100c408402004a0070b81c1c0e83c030034402003001d001d05207803050070503074100d4070308804904011444800c40107000382e140540e58540b410040340f4002e580001c1c01005c5d035400107034025180c0b000101b02c00034000002c0035407502800a41c0b404000b040564030688808641d442480486a01c4c00c0c40003c0c440d0010b140c0140050034009001392103140420751081200c5114410b45e40928140803125441d140c910000d49130440045191070960b1b0344042c1e10b521288034090440800003a07082c01d15209200720f811440e070088070406950f00301103d1100306e405c282c824029a200400300e2014070301e803c10280500d8060100e60b40d0540e40c0c3c803000034140d450500d0700e04132815000110545001c8c414820104015140c1d06c0704c1c0e8030349003850100c585804101c0d644c1440f0a241914040120703400150304485030001c0c5c00d0115095 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 678521016 1250 678519766 678519769
    0x60609180a0605161403010501120504080702030f0c0f010306050315040812040317090c0f0609010302040302040f0c0809060103150c0905060c1c030908190c0f031806111506 76
    0x4000041c0034020341d1528051100b03221400303290030800ba1180d615910680e076000300c2950240320030f02c1214003091b1090882c015001c55078100300e501030300500d002d43c1071501940210b420060a00d00500781500200d5082e0641e28102d59140301c0c8250a01e003c01840742010003003079a0f0701c005501106a943d184c4000b50404c0050400c0f0b54804482c44500d0740141032602d005040101c1e00d0620144c1000c00200041420000103031a2508990086c605007141100d8400c0c0900e960114510a0416400301b10110168441d4080e4043e240c1d403200340001c60402003440140140c0b4054000c00851301312070010004107030740c201d003003c002008200c0005d2010000c01c041d10621030580c895134001d03d0100e00107004600105801005140320360050441c0041540100d040741c54a01c0000c018401c180150b401c40c2a031090003002400c01c80c113182c249011a5110002e00300301101040b00021001d030403880d201e81400c107260000b8120303800e000030b024100d0b104080d1aa502d402808404440c840c0016819 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 678522266 1250 678521016 678521023
    0x62301080a0b0a03050f160b0a0f030911030a0c150f020312130f0506070815150f0f04030b040c050102010c080a09020117090f0c0d03050f071a010e090f06060918 71
    0x645e0b04c002201d0307003003905001003611031181d2113000000003c0144001001e5400310100c0e2080c40a595500c0c40040340c07200c064000f44880c04040e2420080d80c07500c540940c601b045000400b070300400240c054149028001c0000c44030040000341081001c0042c4103520340c0001c02e41d032055030380c095076000e80d9031010441403000d01680f02c094007102800c1d140e60706001d808030b00e0318040c1c2a965100303000c5030b8515051101c401c3c52218560380000951010078500e181c00d01c080e2001020700080030345011070200d10801c071a00700340c2081d1230349424041440100404084a04000c19007800240400151524058007103000100720300c00d230740d17122142441160311655601c4181e00c0800c40c521040d0a243c84d00030f9a0781c2c111901052203100300ca440700300d00e01e07210300c1090303101c0da055a801d440c01e8402061800715030484641184c00d41d4a6401c2d15070354904035004103005c1c00048900140c02d2401d1180c041c40d0110021144c3d00136003044003400416280e80c64001c0e0700104c1020420006014501320b81e25 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 678523516 1250 678522266 678522269
    0x160501020d210f02030403081302060405040e0312010b1b070b1803150a0c02070608060d1e0611031918060b0f061305211005131203062301080a0b0a 65
    0x181a072a004008550340080c0d40030b51700860084e915420309545440c6090710f2000280700c0030394070801c04c2c03100300030dd07241641004d001442d4001c02c2d83c0c1460242000c4000d20035080c1c1103808480c0700443c1900c0740c00c0703521180004500b114001000020b151601c0200103104000e61281980c48100d1030803a1500e0400c544a01510314040c00d29061074401d403c41d000b0320019440c2030050048400004040e8419403110b07001d03c500800b18410702c20a55105000032078000c1c019610007078840040d10200d001c0c0d106544c1c4454604400507a03034a48040000881000e0982070381d0716903d0080d02e030349000340a2101040381d9901a60004a6910b00000074032101e4420300030a502500c0040c480403607140491404003210f00a1700c0070801040010070344034042071055a20b00082d8021700401c0ca11201e6a04242d0300814070b045295035000643e124003640441b034071205800b29460381c2c0200091820005020404020349150708205d003a078000003800320102a0483d07451035100c03a8000d880d513452180c41d60 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 678524766 1250 678523516 678523577
    0x3121c1a0306100905010902040305250515120109061d0403090b0c01090c0603112b020c1506011407030c1b0e011502011b1809050117160501020d 64
    0x24483c0c94a810350500e90310041c001e0800076400e0500001c0c49400d94001e0b1000d403039101024010320030300c0c030000754810030300300302c40c0420440304490001c5c480d120141101c520744010a45c1c240d88500c1558104409030341a40803a80003071820204111800c00f50002500f13501584001080c3e40e10f85040441b80c000c00c0b90000c100000340054a00c656180c1580100107a51003440c003549465501c0f08143c0c11503545c00094401c40d8401c2042611007001d51402211008642c14407003802102484c022080343c0220031903a81c1e035407201d402c0d54a44440100141d034414000d280000d010100c0f4040d83d0400d004948005041c8165011803008008106040c00c01e82c240d040b104820042d900e207103501d607200003032040300401d4039a00403603503a032403040c0125a840405086600c00021000e4404c88140342c1c044440d2072a03008200300490506118010b0074001c000d900c42c48000840c566059608101188200529160f0300c00410001d03030741c0100c4c0181070122a805c02841e601758001c0d0740c1c0d55603000c400924 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 678526016 1250 678524766 678524773
    0x4020f0d031101021b070905060117070c1209030b13150b0303070f0804180e0d050732190b06060a12020309010212010905072c03061503121c1a03 64
    0x142d11595980105854110000088841b0260350740c108004881c1e050781c5860010703400c4400102030030a40c251040d0405858a80350303200544a4480704141184441d2035800103200c40001c200b4806240b01c1590000040c0484030700411542d90b4100a42d0340d003440240380140c0301c040c8551130742c0d028402d660718190400e026994003045480c1140b140ea0241c082c0f10002e09403441024030101c6684110310403088118000c100c0450103210903180794010100480b043c40d5103c0003401002080d40200d860351043c07004132070200c00441034039402d0840c61500d030280a0400741c000b8000c034495590035504800b0542d45caa0b0395958844040392881121410301c0d4807580004188400381c0e40540c0100b000c511200400003259032514080301c182c03131056407450009405640c100c1c20000005104210b2166110540d05120071034901181c03c0103000c42c0c28802c0800300c00c80380103013424148031060058a025218600e469044110000101c0c036610b00c104244e03980303070046119810300441c2e00302d880710000d081717 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 678527266 1250 678526016 678526027
    0x209090102030403091502030d05100302131b17060d0f080301081f06270204050d050708060a0506011b022e030c0305100605030c0f030702030a110604020f0d03110102 73
    0x18042e40c000e84080740041e544900c0019806082410354042c070700c2ca40e02552421a0610404000d46405000c441c07100d03003400c4c00040182e0321a2103401c02c0744900355002c01c40e41c03400440c507100c021a5003544c005010b00c40e101d0015102c171074031145900103001c403244807540d911424040300101201da0700500c41c600000c0080794085001413401e8003403444211a0701c100305040c03050300c10b5070514800c032003150341341780340c88000d01642081c41031914011100042c20182d480e400601d0150011008ac0c885401010050105610034001180e101c90f003030b882840b2a0401c000020000030440c03407500c814803c00c841c480215030b40e04a1107142c2d040d8007010800701c50030801e13042a015542089080104e4906111030051038081c1c060503100d0740e60240301424031032900e2030a13201c1c2e9000a15900040344100003840c00355000c0e90245000c0d002582c01581c5035030300201c001d0310400c0009244816a8445070030080142c0d02c01141548030103080d86c83e2182e0181c00d140503591042c91202051965001041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 678528516 1250 678527266 678527281
    0x10905030c0f1605060a0305070c02060f041d01080a020607110406030b162c06040312020105010f0e0610030c031d1f05160507020307090618050106210e01090209 71
    0x260031100c0c2400c0c009580300c0d920f070a00c450805210611030140c2009080c082940107500951206074000c900381088020307500f503580007805642c0200501d1503449000301c0c00380080e03c407011821001802d0f0f440003945650420580983d501541e440003449564000b500c18100f1540914403420110081d0007449119144d1500c015490404ca40f40d2160042d1088050305940c0b0a08a4624900c0c0fa040302c192030040c1541140c409020380010a50030250800c80040002d9500c01e800e55100d05550000800b941014410158800d1075800301c98a4240351080c03081641d10300c40b250112207400e060000380712071841c8007a40500a40b100308569080d074907141c80710803080400c03c940403590301e00c1c0c25684d10803034084040c01c8400948901c0c840d100888080c02c3c1160080c801031003c2400101150640c1c0d0b52103884200f5210540c00002c41504180c000d43c555500e980101400340041c1c2c00c049501d504610001c8000c3c091007c12098629200c10400f40c0f0070001707501151600e03801034030f080010f240070032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 678529766 1250 678528516 678528523
    0x150207050321070c20030604060507020609030f180109230103180f0b1e0a060302180402030a0b0a0f0612050c0f01050301030b0702030f0304061a09010f1205010905030c 74
    0x2481400c40c0324200c207800e0165040380c400c0b54800c89032602c5007a5002525110494aa09090041c40410301c148620309010703507082065502c0303948101c8000c00d462502001c024100940503051000c284d0042c0a0b00f402c103070700d1609440e50404070b41d201c01d0800269100403a0842c1e4607510100c2a40032503d50300c00c8241010349005103070002a28180030a5203c526910100144884050421500c0f1301d4103200007828080c0c072941041a18a000d20307024521400000c00b0041600d41a81c000d682c3c920400440c10114004090540741038620750301ca18003a0042a1580ca2481c0000c003090084000984d001c41c80d6400f1660030280e0482c100300c903d031160f13920106041d4080e0151018031418180802c2c0c6e24014465204407030040c0d417454216441c62b9210019500b002e800e04003540800e10400d944602c0036006148a140200380c08144481c452007050204210710300c2550150b407a01c40180441944403508808984281ca105140c041c0030742011401402c80d42c50083c10f601000be901d020694000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 678531016 1250 678529766 678529777
    0x20702040b0a05030703080702060d05010602070e010503030f1b0a140d08010806091905100c20070b0307050f0408070608311401140403030c090602010203150603041502070503 77
    0xa80301040102544000c02005810314800d440d07241e0301604041c000145900042e00100c0e10180ca407605140b0980c042806480098000320010781c0310340010000c0c12518095a8010002500a9842d2180480100f01d5078407803000000d0544240781003d0035145410450341000507008220b14181041071100c0e82d4907000310307402c1c4600140714000045241ea50100300c0701d008480740380040043c0e0389180003061011051301000e5415006032548404e4200307442c0030f00003000300b039656007000384014402d4600e007800c4200425150756100440a11200c203210302260303000111402c01c1a150300b004440812244281d030091010350084000000c0d8503a0480442c41c0502044104084122810719403090500c80508035105103081c6200524007240c41081d0656006080c1e500110f0300c10b2044203003503103000b01601c080300026565080b01c103c156119140300040d0400740300a41c55814002040040c92003240202ea20502d40000071804025120360b105c492000701442c19901c6d00464280140c40b60000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 678532266 1250 678531016 678531019
    0x71a0d06091517030703180f0f05130e06010e0604060801020c010510080a03020a0201180509180d020f060a1109100207061b0317042a03061a1e0406030f06020702 71
    0x42100104801c2110141202c43c0042c41006605112458408444400b0307001140030b03100b010f2490200d80c0400c941c0f01500585030260700c2e40041450305050100101c10b441c00d82200918289984c00388810106082e811586017142241e001d484030070014000f0b0005030f00c010b4a42d8030019a8622162064005074031990091828203013450351014800d4481408120080040e00500c440320700660068211140c3c0034403a11a42110302d44501c0450401d2400365808840004d80d401d1240514100300312540380304183d480549244003955240c076039600b102810034070415850b0721804801410307180c240c401c140c000520301c0600c0418000042e4035103030180034040020382150301e00030020040c407030b88142442c4d160ba42d011034101c0700d4180729803006020f40102c0f00441e1100760610b408403404002a20941155401000d5600d54600241103c10f80c90000b808210701c1418451a030b5608a00110480035900c003521391000c41e8000600242070a400c020111a00180c2410600c24035034058100d0a10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 678533516 1250 678532266 678532301
    0x140f1605070524131715010f15080a02090301060b0c150601140c0708011a120601030b180a0209070c1104060312030f0605060c030a021e071a0d0609 65
    0x1c849090200450318100304159411050243c1a24000401d004150070000d0891051302c07161548101c40e0441d0104442a05560143c0d0040348406098050b440c010042c0010030106185001240c801c020582400d450502c01c2c2c000c0014030324021601260400400240200135550310b40b01c4000fc1307908908202015403090325180c0a0600d0303884507080c0182d01c1615800015000307501e81c80f2195120030008045c90140040000c0d40c40400d00440c8682d10400c010500d070464003000707000c000003a030510b09040342d0241004001260304a15080c1d04440043e074100501140600050f1910b001c401c40203400a2140040152090380000d4030289588036a0004003101c540104000944043e4040903200d400c0c0d100c40d0a501502070380c842c504800310789001080711940c0f0360015260b500041c1042034140c10005071004030660600450500e40b011070400901c00012000c0d42ea916543c0e07014058956061904c898404086081659004030304c80c1d10620450b600c9072911405005155088005202c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 678534766 1250 678533516 678533519
    0x3040609080d0c02030c060a0309060f0f1a0d0f020a0e010e04110409020102070608180102030a06031703010b030118061203030b010e06091e0109050a080105090607030203130201140f160507 83
    0x288507100f0314070101e0f001001070031002d000130100b080c00d91103106400249503031707940c1c42c000207041402500055503021400080810000c21607009603102465000c0b03451100c41c08203444d580c1ca22140300e1249400081d043c00400b89480402c401c0300380303504085051442071380006003072070b000c821141c13181d4072800170001d0700c081480c10300094840301e603002800f682043c40140525131103441480c1c1e001c52030f00c0b9883c00c00c0a9904c400d508a90080d00c0c0694600d854034010f1051200c0b038052800450f25050000c0e281d50f2510310f000c1030f0381c0410f01401d00103903841d0380b0703405095606800c5500a06880c0800b02841d9070f243c41c010707005250034403616001ca652140740c804146025800e403100000301a0a01010b80f11150100d030502c0c03400420075061004210010526031902e10902000d030454800000b0241080d010f040e152040c0100b2550416004204012010354003211114100f13034282022036a507074800c103a4035a28010300c1c4001d5a005c201084612030f0480700d0105030b5400d4015820b94200c00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 678536016 1250 678534766 678534793
    0x70c03021c050c15041d061809210f041205061b0a0c021f080f09030702060a0f210f0b03010c090302220f0228021903030e0304060908 59
    0x1260300e4003002d88250811200d04810342000b070140703135408030300540c4e1a10705034840f1030705114040b42c0c03044143d090b01c0c40c004014150038036007128980c400541c45845c40514006500c42e070390f1351540b42c1e0090b1000402104100d0560000d040d078442c0081c2d540101d4030741742c88500c244c003290740144065071031388200404910799080e11094020248444c0700b800b85400d000c00130968100c00030f20012078021910b1226811035070849a1341d10403030700d800e40d00c603022414034100c22980002e014011400c42c0d00f0400a5000623600d0700e04641505006041c0700281d43d0810b2419500c03e02c14002242048200d00552003614415510408051620080400800e00000300303050032582d41040030808600030500c03d101500d050440c3c1140c0d1514868048901c0d494058518152891103203803141c016004200045621480d0000c28400d01c149000c20808015080b03000b5540c010001d01840e51802d0581040c0c2454820f80291600c09140422a170f5a070341c0e6108024400d840d039104a40d094000c108940004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 678537266 1250 678536016 678536059
    0xf09060a060c050a0f030c02180106050403060f0f050709081203010f1413090507170319030c090b0f030907051527030d0c0b0a090b0f09070b070c0302 66
    0x402018080041040c141203040c0d42c0152100e2003680c20b07114503281307a0002003400e0315403401c0c2e0b8800c0e03455a440345030038818002581680a0802000d140590040c00300784d03441401e4508903034100d4008101100110390040c018890480b4049440f414081080b000b1600301c1d4403001191040360484904025002e0000218002809044090889602c0c10070140c3c0741c0441c00a0408130040c9410504001407103031904072520790340e0458054211060801040101c018440240203e4030080c501e41841022031264000e40700308603105250340c98007110b4890340b0482d03520300500800b20f9015914581804c01c0d000c1074008442d400c1043c4a0404080ba0a043c40300041c9a111081c9070380a0521107940c1000703c46008041d00340000c50300324881c41300c0035941000241519101d58035285031100e940e0400c034007a000d0045c403410300181046031000c00078482e6400140c2c459880780c13080b00c181d00c505161505102403540141ca41c41c2001c5080c00500c81e52a0803141102c0c8201d50201d504000c81c2d00b000c02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 678538516 1250 678537266 678537271
    0x30f0d0801120501060503150412030b031c111014100602030f07050c040203180d02030a0c0f11030a0c080712080304110a03020411040603051e07050c0a0b01140f09 72
    0x110800010014a110b05201070125072082002107689a00d9002091030f02d0000d50040b81004030000500040c040041c030b4020b000380340d51405005600a040201b41d0341d01d00030210b001c440c8040d04074188150320520f840a58401a48266011605080072407000303800001a00c030301104145022805041040454404491694020307505003c00c0440c80443c40d00a0b603015142c41c09884240c0348555510300c011071050a0b0317044c1e0a41c48104070550a8a003180241481c01554401c1154500980d080b40c001c5e048940e000340750500000c1581342820f80c0703e81c03500380d940e014494500c0304c0c4200002e03003100e141501e42c2941202c1410b0b07502e2900c01c520311102400600059401c201241c0440c0c400300500000381d5024161a041ca5540da000c141180c4411005c2e170300d540350105050024a9042c020542c01c00c0c208200031184010b2401901030108026040c035084c01070020394070f41220414407402e0041504180e200d20b81d0361f500c01d402131080d583c0c510305174030804014091000030301c0d0800c103290 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 678539766 1250 678538516 678538543
    0x60307080d2105040c08100902090a0b011707090e0709030b0109020a0507120e0f060903060a020306012001060e0a052512061514030c1606020412050c030f 68
    0xa4212101c10a485480950301d00c000c2c00030019a00c44044440342c001c0742c0c0a28812502e42c1c504500d41961241000c0401c0c02401ca000d090100c0c02d4090707030300d15140d240c11500c0b10000240c082e800d4001a10280c0340d01c150f80c00b00700020400c014000360840a054100c0d6040c038411510382da150780088800c0c605034040200902c0095005108020340c55020f00150303d03039414260300d032105a0b114003525081c0d140c0070b075000455100c00d4595504001041211041e800c3e01c5080c1016201c1d0000307a03e548008052050b415400310028900da84510385d080652440365442e50645011540d10358007078181c5010301401c180c019004280890500c2c85040e00c100c0c008c1032000b215004003411880c8006200341c0c010304102c5039a68600da2207100b446004014090318030f281908502002c00a4101c00e00c0d41c0120900403c148100804100702030226480d0180c2c101c40ba003051452894188001d00503034103d0005003a03255104001c0142c00240454060070072070440721202d0b107201d01c5680d111030141961 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 678541016 1250 678539766 678539773
    0x5040b0a051605031b0c22110f07060c0905010815090c0f0a08060907020c130207150c030c030b090615070204020d0e16050d0c0302060c0a0212010b040506030708 71
    0x35520744200c001d01251003a07030040c0c0200080d1a200c0300d1031604800c4070200404051035140d9040b4100f0400710700500c00139200518680c2c0041011424904000c810442080c0ca5048a14450b01c200d4111142e080c04105001d0b00d850090404400800e0301c80105404243c00280104046d07000301c2c80288074209100300d15400c2e44000c030501050350700250141400c01824014851500c5450300030346401091360382c0f281010b25100041000c040005030942013035401121703502c010f580fa400714010741051400c0b805030741c9a005282010030140c140209403c22071038040d69410540e8107400091400f03180b03941c180b03e00004042004801c03141900d100c2c1d4000582848034104e0710450014088041c002400141011a80a040c4064580c0a20894940d40000ca601c2e41c010358820100c02c007401096680094446041d40c401016000b540030180c8030345000716845420000410400d035189a01070034420b01140c2000003640079043c18550030f4801c1e07003040009001d5090001d00b410844003414000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 678542266 1250 678541016 678541027
    0x1c060603021611010903080a03091b0806072d0e03010b01171b0c01020c060613020705030306011b02030106180b18010909081603080f09150105040e030705060a0b0a050105040b 77
    0x220a00443c0e61000b0f0b506001100800201060b42d01001c1d1401030550f072400307d4501c85621b042c20818003103454504102005041c2071050580c0001e00c80e5228507642014075010104040a940c40a081c081c0500307810181c680c010341a950210751804c0201042d802401088907000041d50301620001c03200040c10381140005240380801000e082140c104511010700d0000c0402006003684e100c001003100c40e600c00c030280301c203c1c10b2040140c1d24881408608500704072040da00c65450344000741041e41000303024010070aa010340e0381806130b0003550080080041aa6400e410f0040b9108140c1c8a4245840c2069880c13075802c3c031504a140e2500c0212981c2c4541e03082519100c01071041400a641200040c48030084600e06000862b1032030f0302070b84030012907180601c5402c0610000030a1940c1c29000f80320450203608202100e1415900216004200e40c2e69902041e03280d8010781c44013500920034a0b00b405041c280541c01568100d00992380085070581307a00041d141e61080e80b00e0600e03200404c021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 678543516 1250 678542266 678542273
    0x31a03011802100c060e0a0b07080c041413051611010c05031f080a0b010305100612030e13060b041a07030903060209040b0d030503250c02090405010b061c0606030216 73
    0x8203c07040a5039401c100002040c1c545604080319118030f0100e172241d0109144809024001c6091a0300000d585840d0000e4500914026154011071250b4402106001222541c070b0783e071040d0b070000365042100304008510348030f14080f02144461a4207004504880c1c0c0700d40c4000818020100d15400301c2d1211443c54031040c82a4140c000c1d0f10000710303403150440030007160040b03080c4a1101c2d4540500c48c0121075505500b4100d0816410882a5004500d003140401080e5000c442d403998039501802d01243c00e214040224144010b4000055074131443c01c0da0104c2c100c0c005401400641d42c0c0019601184030110109400c984114000070700401c1111408100040d8550014842c000c0c001d0004260800c0c400007144203040c42c401c1c21804200040100407248684001d0705111920f41807003040d05c14001d0344094000240204042c0c003da1001c00014103000c02500000c00707849018058558851801d456820003544a90031245002e0401400146461290090b100a0b121954200d8884d140b50398 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 678544766 1250 678543516 678543529
    0xa031107260109080705070e100f0b072102011401090e1e0a1b0303030f0c1b0318060503010501080c0a0e06090d05010504080408011415190f06031a03011802 69
    0xa02041c541d215241c500010310309001a120807840f6900814030300c0e081450140d00404010183d09204000f08002c004040c0322040641c219408015a1595450142043c560904183c13403000301403271801400c0360001d6815441450054000503c8607000c0c0d0b02c404950381604c00c1002c0c490b500d40d0140083d0001b0400344c4200290b03081034101103422215080c2d59000e11055601514a00f01da0406400c005040e018040c210026182500405c50802c000c0b03000ba040c4145c10902d002d1f58541542d2640416024007415520750038050081584035036207a800600e10742c000d00030b0a000640d0790000c101c1e040a0007040c0e459007545529000f04040c9001c09011268101010050780f10b0f80f00b6440c60042103081c40381d41d000c3c60203441820b03074650801030410300713440c9000161100e12541d50104a80301c0014110001070345011a182c01d078810300408110002c40054000284100b20038a00040c01a05588591700c0010100094140c00a40d0000c00d8200e58a00044814000c510005c0c03000524140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 678546016 1250 678544766 678544829
    0xd0f0b0618160e12060c0901080601020c01170714070f050d08010e0f1021120512060402090d0506010801020307091d04060c090b130e131a090a02120a031107 69
    0x2d00f195000403180d8140d64517200c02501d00002d452000580840316580c0000220361114003030000700300c0e00c1704283c0020078500d40140c1c5050990740c00800300720110303c141c2d52886001e050b5040345c2e482d40c1990400508036000c641084a4038810900043c4105010700502c6048401054600846548400003c801110b00901100003240c50000204c0c52440048400180524060f40a020303141245001134030504020260b1042c000d09200c6208400f644404140c1c2c0490709460140e12042c02c0e101113184500c1c05800184503001d40380c004641d04e0015806944100e2059a40100156980b007039a5a200300450740404240e804100050100c0c00c2900f0410404e070707252600010b0325030380380007002c0740d40c02500381840130301642c440421081c01081c11035500602c542c01484d220300110343e0360256500c000402410b511041d040020f84001d4107104036480380360080d0200e10401032906003551299200c50046000c6844003007407545102000450b4000e9804084014180f84158000380e464001325 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 678547266 1250 678546016 678546019
    0x14240d1104030308040302070801060b04141c0f0b0f06010c030305190e0f07080d02030403120203041d0f070815061b030a2d021b0d0f0b0618160e 64
    0x2600d900040d0191a0001000158041e554050f01824203140003403d003842907002c071900e0780c1040000d0040017036180844080703540701c014108209034003401207408006140b020013070001e61500034078188001507142c403822511480d40760003a50341d1050a15854603058070120300003010645a840040c0c020b03441700c0d4104500d80115460540400403002c00d47c1c4204a0b0a40c0c1500100041d09480c1003c020081c040d100c0f5002404412040d02802592409144006442820308143c4c658a060080c01110090031624242d0003031400c2c02000194984015500f10300310075034000008080038851b20406024110740010690301e18461401c003c0780ba0028040e855520b0006107041c800e00e0010002400c1015a540390381080b01302c11021403640c00e5103143d00c400e52041c0c108944006c0c0d0390105245a1500c000660720303d96100c0c046c085100e064010320010101100384130844240410300c4000361061108984005500c1d41c880c0d40241e48080a03079001110000007001c4056580c002c80140314003040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 678548516 1250 678547266 678547271
    0x2606090703020c0d020c03010c09030f0f0807080301060e0a051807030509010b0d05010c020f0609060103021516110411071104110f0a0905030c0a051815040207030914240d 75
    0x2e00c0c0038182419407000000c1d026a04c201c0c211031b03850030b080c00b409043c801a03051143d07403985142c07201c04485051030b8008000003000b0790300300c08100105040d40d8043e0b41062300c0c01e44a40c0c6511000d0948400c0e100d1261043d01041000600d616082c80300c03400031145460004840d4465207010303805010054142ea905540b150540000d0343c85107000000883d01540001c0303904503401c01c001c0e0500501803098007468102c0d20400106600001700d150440383e050710b040c060201040c110312140e016034030036421240040c5210720141301000c00c1100b91744208903010000c2041c503000020f07491081100c0205240c0f071408003001140b03440e50080329186448180706140c070004110f0040194041007510004c242103000c06c0c4140d0408115240b03c2c0d05050b00c80c0300740c19040c00700107001c40ca0300d0703100c0074140b01071040015180c014a0504c074a0801d0054802d5444070200d00c0c0c0a0980c05841c06001c03000e060560110200b0310704200d032000704680250018010010380d4a44140c00e500c4008200e58958 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 678549766 1250 678548516 678548527
    0x110405072309041d150712060305030901020708161802090406030311010b0402040302181e0108210702010c17041e060e0d0c14010c020301021306260609070302 70
    0x40840121014070800740c00c41c5549550010400007114942480110360b1030700480b405090610002d041315010003c00144c841e1550b074224102c891250000380d9550141c10880d0001c1000b100001802d0448803d13001d45410036260000a07943d0070102d8030701c0016500922041100301c0c9031105420000400706c1015240076408400703c2c0968110f54012400100d0700c0a4603075464500303108031501080e045605500c2e092640e0000ba8002c0080c2101e41c04510621000c96122848030a20002d20403141032030110a60b0b44a138170750344a44400c0c04c0040078651204600c0ca585120300221001154140c44000100103d5205c21440006408000000c0302c1c08010200c1d0310300390006003145042040c25000c40e00350a1004c000c0c8602c0c0c20408440c000e20241010100044107240d6101c00d540c154030410400b55058401242c50141e45880a034055100166031440400340e03800c1d00c404d803404e40c1c40d00f8800003074a410480d2016946507010b0302464160307000c0b854911300520b00743d801108902d009030620 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 678551016 1250 678549766 678549797
    0x20c010e01020f060f040c21060b03031e0307091703070f0302030c100c1704020d0b06060d090c03050d020f0d030c0908190c3003051b0a0b010e0411040507 68
    0xa5070170b0740d0001c13843c94007008010400c42d60006040140c21100c0b01601c5403902c900c49081c071000305c0e4000800941d00c40707000d000c5a4900b0026240e840c0600605901d50110101c0c81c00b4955009440400c0010b174020b0000c110100000c0215401d4100980114a490416200c00b40c81500c1c40c84120b0031800200405100f0200c2080703800d02110318180e0000d03511410340809032804046a00300218020340704104409a501c950383d10400540140540d985a81d0342c0c800a902845440d42100722107141c81002d006100c40240b280c4242c92040c800c88516802d0544140d90311540300c010041940d00c444d4910000c00d110b600401c00d140140d05180c07180301c0e115407a10382005c00321081143e1035056400e004007030140703040e401402042c0441000000b1010304240c04401c0f11a2094501d92800c2d0401080406200f0700855012030034191810411000b074444681c0c4582c0f16038420360743c4480040001c21b61040d00500366004d681d100a00822820816086c80007030702004082c08180840702c203100340e21 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 678552266 1250 678551016 678551023
    0xf03060903031e13030f09120c030c0501030212040f03030b0a0602030c01050a021c05090703140601030b0c03060a05040b0a05040c0f080117030901052b050a0b010807020c010e01020f 80
    0x280c0000c0010716103030315040001c2d045144a40c0034100e0400010010f00c4010f01c89101d4400750b82c0c1d01843c2c9583d1645c80294140c5880c0c41950012000d01003003040c44083c019035015800a903846440c240c5001c964410044003a8054010600310131184100031400248018461850203840390a01190b6460f50a0020b90300990720390000340544c00c0003920302c103420402e00c1003e903c580e081c1400c5007040c050400d000c40700d490300446128511707907407800702d40220b0003002084015940103000c442902003100720942c60324006c2c88101c4001807440c1c08034200019070b0059a01c141c00162003041d14500d08001c00024103408014035800c02c0540034007080c1510349005e00812280c1c00d03105c1043e84041d40c0002040340e08140e008074000035441643e070103485004021154003050034078142e61a550030815440c6c2e400c210301000750f03880d10b010181121410301600814843c5903d520100119010b0070010f440302c0800701c504100603040113444c1d00c100d6008450800c45020103104446611846414252a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 678553516 1250 678552266 678552271
    0x31b0705090a0e010c0f05030c0c0f01091a07020c010c0f060b03060c092407080306060c100b0a121203202d19230d0606031a1c020f0306 60
    0x1600b41d2105201420315034240075450741c0100510f01340c20030800703904004169000c05041004140400608110000c10400c0511920035240b40200505030161500b62111481e00020101c03403c41000001d8a00380080b41d58040d80106848000d21003419a54501200355508004c0302c0c00b03503445050022a40702041414440d01d4030861980d960038500301004080325a0003602800743d41c02403544201c4000100507a44650350200e941c070317282d40b03c2a0014115004d43c1c4080746440c0314803c420070007032140d60841c4c48011002d90392a01155185e0002c0002d0001c0801c003d4a00300d0601503542d2554466409200c50401701ca40b1518185603507000300e2040d5011600c07000c0c02c103260300c0410340020601c2120104002d194107140340f07050445002881e03840c40d02c1395400103124000b525142d05008410003852440e00c1500310507514800c070411030f00148580e0080e0700009103840f446c81c0d02900d01d480c4c4401e140300010170000496038800b0010064040d0314400b240c00c03400c608084041d64404000e543d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 678554766 1250 678553516 678553531
    0x904110d1514030d1403090c0303070c09060b0423041e0203040b090105090706030c0c21030e0127020402040504050103080705060a1a060a03060308030702010c110a05031b070509 78
    0x4280b400c2c078403807051480603401500c0b940182001854494004449018030020b4844494981c0e075a00001410008528020780e01400001035603020004406010410303150429070421880e520340c074001ba010301403801400500304001c0102c4078110300c4284480b0060342c5c01000407680440043d81d00a140e56814000305c0101e40100500c420000d10020180c1e20800003402040540780240c1c05a40d2010184030380302c00d0503a43c036100c4610900c242d01d00c00255030458101c408410140c04041c04d515140101c0030300003441c01055840002c010700510914454006d402079903622b48200d100402c0442d09002c0341e0180c0e0030803000400b51110302600e4002c500030460940c891402d82030003400d2000c01003030f0349001441e080070f10004840d0b441040c1000c1390140c0c1c4142d25050100c01c00d07402060140c0004d4101d0b0804810445402c0d0f0540085110400300d0b52003803400c4a20192041c1c1e40c041c001002005a00248440809100c200d07603d8001c110100301195031155840011031500303002a941310 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 678556016 1250 678554766 678554801
    0xd170c10060e1b07080d0c0503011707150f030b040905010b030d080f010b03040f0506101406040f0603090c0e07080a0b10020a03201e060705040602030904110d 70
    0x4806016078030071000200381120041900d441c14501802c3d0444820440016050b40403e051081c049050241d0300300e0110361178100075014888002600c00c0e0801d1013000a0742c3c2600864141d801004a5100b04071012142121990031003800191421040e10704001e041564803082074079207650741c0c010a89918012400014042c00a00c207140c2850f03440700914080c001681e080c849140d031540d914070704540302c1202c490303242d07200d600d4501c10b00740d10301d800a402845140d0610402d030407c08901c0e022075141a9550003d071552030103010050003644a10558001030440070031205000341c0148900320b1183d020607104070f448080c0c2610354403059804c0d07400580101d00300250680d45206001e2480411a0520100044290000c1d07455014090080800c135400320310b0702c40d03035442c20809242e52165a0542d04407880d6101c0b88481585401d00c12041c500c0740101040c4c0c030700d0080c011201903d0203580034515103054002800054840c81700f007801094010030144020f00d42c4c901c582070303548810000c0d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 678557266 1250 678556016 678556033
    0x10e070207060912030f051c06051c030503011e03050a1b12080702010c0213060909020907090305120f0f1c06060203041503240e040507080d08060d170c 67
    0xc0c0341c8641a003244003440394450060241c0c0080b113140035180f075031501c3c0103141e94001003000c0f1054000c070681086100c030600c1d54550300607459044142a9581074440c01c0258120344140d80d60240301d000c010700801c00810060149030311102b281030001d1210481c04a07540d0380d07a69468949180d010040e80c0c0030985d10181001a204040312500821940100c100c81c03c1d010748035043c25106d0804024103000210302c00c0f00441d102c1080c0000f00c0e00300030508002c3c40c3d5a80711524054070b041542244200f00d80e8000444039801040d0b03410960b03810100400400024440b41c50081d031003401c0b01110b05c2401d104c083d4685003490b004150b000d01c0e02004102640300300000300c0039180c0c40d0b000300e015504244020300c03001c400c000400213403045a14002c21901040341d021307005401101c080e42550b41c03240c82c003c00c42d0b01089444a004620030405c90b403da44e030f10302c0d06507141c0591440050000d82c1041c04580f652400170483c01056001314181c0c10504480c00c090b02a40d408551301801e03941040c1c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 678558516 1250 678557266 678557281
    0x3190504060f080714090a090f02120c0316051612170a05040312020901030e0307030e01170907030303020702120105041202010c030203010b0724060f030209090a03021b0d0506010e 79
    0x20300114016036800c212001e418104c1000d070101c000c0c00200a030200001c603205040d41c1d174801d080001000d41c1041080801d0f0650044d5010f94031440202800d00004030129655000c1802140d10132440c02d840800e000710803410440b011b83c0018844601c03600011000c0001c580d510b024500e1000d11030310781c9968404401c540040110004001c1c1250714684400c110110340c00858030901c80d1120740005030f8640038100140c00901c40418140c000d44808a408810141c0060005000c62003d8031014040349a4501c00422050b0886440c540d0b0340009a041000030700940140c80081d100030400074081503403410540c2100c071f04075006c6d5078804900c000f022001d5020b10941c4c040440e286810361556040c081c071a15103105001d0020701566840b445440402c42071082c0402500e112403082c00304079580c40c903910500352a40401e0780310346a4140428003a40c800100382c0b0440e41c2c0340d00038085014a5402d82c1c00592403c24060b6001190149200d00040080c85414007070208060041d8582c00e0444 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 678559766 1250 678558516 678558527
    0xc07020f010e0d030f17390429031017032502042a02010b0406051c0c0503030d14010501030b1c030315060e010e0402031905090319050406 61
    0xc00550500180d04002407807034407070081c481c1e0300a415003031400c084410030304119203000f402e400c140600b03090a401d00660650354041012800824918640004182400722840002e100b84003c0681400c0004005080b10310b00d400108601c0400a0304124180400101c0a0f9200319503521204000c010306001c68203070540d0035a04418030b0320055003081c03480002c600d2001280e85e441501f0010b100d54500841d40c4540010070810307003150f10910761b00d0306030000104050014a40c440954200000c0b41110700b403038800c2c130703040f80c00c000d1011a21030701c60301c2003640c00c1c040941c054070f42004070100441c0d20344081008052807901410000b4480d00460124040840c060b0860781c109401c000f100c00183d55089010405c2c0d08140000700d141c043c182c036003170340108040d403d040700c1d0080c0707001c1c001500380c0c20904510001d0b101383c95042c404041c42d0100300c120f1004550702d20814981c0f414002e1040643d61046034020001d5044900e401c0b1300c0146413800b440c50000742800200005802d124456100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 678561016 1250 678559766 678559789
    0x7211d010c1d0f040f09050d0c050c2205090a020a0f0311100503011505041e080f06010b2703030409020c0f01200a1b06050a0b01090815040c0e0c0702 66
    0x34898408202c1d010b0300000c03e000b03520f04141d445181c694180c0421070081c1c0e8000020103622500b194100d074090340c00901661700103e801e0780c0303602902c3c090034460f06000c5000b4a15482000d802210100c8083c8840002c1c80007800c807440ca40304002e0690010b0720344032650000381c0310f204580b0398101e145282c0903048c002c02296440c015a141d16039500407076082002d0740d040d100380441e410300b0b02450000441e070500440d80030092503103c525103100718202c1c07400c0c25400c1c1c40a0300c051f0390740703201d001c400309503160000c0c410011301403020001c0440c2020840da0007a01d08022900c07804041122000007480d5400680004505650024544201c1380c020000d18408801100080c0012965480001c480002d1421481039500d40015540c030750070322588035030f601e03405210b04031040c001040c28a02d008000c00c85540340103a19203c2c0103540c6601462410301150490002440e50560303441801c2c14502c40988201c801c2440e0070004240c8400701800c25200d20303103040903691640c4440c0100601c28a00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 678562266 1250 678561016 678561047
    0xe041d030703030203071b0605041502032a1b0615030d020c060f09100f1d0a03020d03030204170d1e171503010f020d0b0907211d010c 59
    0x20061840480482a5100310340c041c01d00584942d194141585c6589103015642005400b91040c0000c200d915400329010714002c02c01c100b01c82c010300109400728882034500c12046101031001c0842011062190b480c031f18500240c29040401e2070b0550041c91003040f90b00046c6030050000c101034034060949500c00c0740703c01c400506841c0d0b000701020752650b032000b01c40c501a0700000b030b0307a8003042408000c5811850016189201003885080010608004070318a40009880c14007881c040000d1030036182c01c403000041075010400c1c6940d007004081500054101e00307054003804001003001d102446500f044140070040c250004040e2001020500700d00d202c00c014601802180c520030381c0c0300d0410051007803501c1641e40c003a20b0346c41c5118449590012003a80c198204458024451503e80190002c00615482407012210f132004000c2d90030000c0303408600095101c568071b050000c50700b8051880c0000500001101e4007940d04c104606400c80342c0d00301f9140c2d114003008030115804840705102c200e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 678563516 1250 678562266 678562301
    0xb030f011a0d080f0708072103200d0e011404081b0d0e0607050703080d0e061501020c01260f090f0a050c0f01090b0403050c03060c030601092d03030e04 67
    0x440c1d5548844134003516035580c0c0802800310b040000c00100340c08541d081904401104251910351030028203c2000115000000c0d013001410545503194118140a0009903c0d00e1814803143e00d205030014990302c2600a070540d00d4050941660450040c10b6024900800c0303116030720742103071514602c5561401d0b11040e141d4004030a000c01c140e44081103101c1074004840455944416080662510301541c1001e003614a0008a10f2840d50362a40701c080b9020740401031f60b01c2a9541d05440341210312858a05001d40c100d000940c44562280c03201800910090b00c140340020145d003010310b4088412103154100030180d50510008010401c8a6144641aa00103080d4003480303695180c1c0314642003a5090043e4420b0b08040700a1f0302a01010002c0d1030f40844003916155039040c42903944500d844401d009002c1c03240440c02420000003180d11415040e120036245918202c500381e1170342c48001e1004c8240340a0226020070016070142c06000310b00940c3e4100c45040d2050801040720900f8142042c001d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 678564766 1250 678563516 678563539
    0x170405011b020a0302122a15120601110f06040516091a10052709070c110906040b040e06070818070e100302030a030c05010605060408031207030b030f011a 68
    0xfa07440e86030740c0607698107445c44910060424010361400c4960030200100c000041e041c84450200e440e86010302840403507860f80c40703450315198400b1904c1203411035407031076a002002602950042c0840303a00c0e140b074801100c000f990008141c60800c081940d00302c036950040c0c6c01c0d80034490510800700c809040900c2c000c107d907400c04030803030b02108102c0040c1402804140b01007001c0c49d01900548510044101400c10b1354912020880b00c081c8580c08400d00c10358011010904081c0301c0c0d42c00080a69003d0002032011109004020b10707800700030541548552100b01554507a260350040810741006030004040c10700341250050f02d445001012012803070791086100171408000161403084548400321003c840d113400e803440c00840400c1c0c001a415101d521942c10806511911001c0084e010300000c000e80d40d283d00030400700c4d00c1f461103100450340c000e02800c1d603641204100c3d2600b01c0d0150030001240d0294a002c41d040c91b44166000a00c0e0350344905801803120495101200308100b2a08280b03103c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 678566016 1250 678564766 678564769
    0x304030f1805031c0201320703140103061a0604090209120c0d0f0c0b070b090c0102070614030703200702240a1107050409210f05091c170405011b02 65
    0x140740b207411315129080850b0b40e0701c003030600070341c46031001c266010400451401990b0350004008050900501d0003022000001c01c401d210780b10f060800c052140b200044c1d6441d40d12550041c1807482600d4094055000d03082d4101e98920b0010002421214005a1036415940800c11800c04217400e075890307600500c132901e1456650018007813000e0381c004880310440c140c03810003000000645d00303e0b990034800024036505100480504a1141c04203000300d86c030440c0403200480c0c032690030740b152034049500f00180c0c91034030303004c00301940c2d0241c228030f0700091098098170007441c101c00c900c2c0343c800c40e804006032820a5080070b610052070440003100701d6814008150010f03200e0302c0ba01420b0003c00603174010709032500d2800c0c0310321001004010320a10291265080400300540c004031200c580303a0103030001e0001e99000301c98805206201d03460715410280c500b0280207009050f402c052884010325681000001c00c07203890000c1207442003000948481c1450005031881d042c00300e040041601c500e00c0754006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 678567266 1250 678566016 678566023
    0x804142d060601230702040e0610090b03030d090642050f060c0f06040b100509040209180a231204030506040f060f0c030b030601051203180d0203030304030f180503 72
    0x20f4010084c0c1c00c000f5503410100b842a8020054001c0d489402c10190003901c030070026100713000329102560501580c0c0d4500d031001c100c80400b10f4168140e013003884511050030b441d03484034400a0041001268107900e02000c105084100302c1240c00f640d61808541a07030f02c62040c40e0071f004200881d0541c03d0603080c040014a02c40111046500c0f0b60b4000489650741501800382c81480f04001c4221000703410a89043c0001c45411100e083c00180e10301d00002d12498085011400f070f6801420080b04c1e51070f02c0c4424400071010f00084001841407411040008200680600070540b12100031007100000c40c103402e05003400c0d49c040202c5c0c0b4205120501c007040010030304b6504030346c1c4010141d1038810b1501d270000c068666804100304c21880c2049007800c0076010781081510300411005c0d11256030325102040311180031103046005951017840b07040c100881c000001c06813010001d141244184083d80000d140d40d0003254100e0000b858a903800241c15044508010015469002c4241f10307418100440d0f0f4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 678568516 1250 678567266 678567287
    0x14040323030103021e09010308030a11040e0a0515060d0609050601090303120c120612030e01020f070e09160b04080714060a0f030e0609010c110102040302030604030804142d060601 79
    0x890f40c246900280f2600008284401d031130030180c0141b540350f03503d0601d0085d54104a5030501c02c20b04000d0b800741e903043eaa400701d405441c03012610000d56198180c0a00050000900c000310042001000e114603a84240140c505a03c0d00c0002060550030f0201600a90b03102070704c2c640c1401803107641480002d4116825800700c0384101c40024068440d040211548800040c000100c940f409030007189440302c002d8000b10140c02625142c1590b02c0301e030012642d807040f16283d8001c0760400881800a41d0301c60588640185062046488003011302c02c0031b50031921107a01040703001a000600300101d1405115682c001c018580d18040030f0300d0181c0c0414200c1c03040703003021810040385000701d0702820b00990010403840014011114a454182c0c2020b00a080304080c601c00309000007201d45c13005205000f201d040d2517014020f40700581301c596096a10480c06007048812041d4400e144600010800a185940c190106c030740c20104400d0981c200c0058840b814492582c10840801100741d030411841d41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 678569766 1250 678568516 678568519
    0xd111b06030703151214070b190504031e02091e0a0c050c01090b10050405042102030f0c010c090b0304051e03090301150614030403121802041404032303010302 70
    0x40d520b5445220450091204207011031a4003911000814009000f8007100c070a6417094807140341880d420411180d0304c000b00e20801c034a1a070200554880681d040640d410311303c0c01404e00504007901d030740e19181541c4c855030102e21100742412401d02946412404542c10411400840d44038071024140114111300c02070840b07807540d450340d0400349034034460740440717280c281450020401c103291032801d058001c005442aa505a00207600420a440c003445194062940098807103801c2055a403c20a0102c4030100b05003580000d01c000c240c200004c1001f00040104400001a510120700000c0d000401e65001050811014800c02000480025400074640c0360f004e8052400000300e02858a1445010340a9405500f46142544c1d4005440b54070b40a40b802500c1c0c0e0301e10b01d0443c0d40e582006020403240940007402d4181007903814902c5502c82d80e000106010103d280310b0722a004641510450010b510701c2001c0d0034100b20a0590200e160345a1100c1d2131005203c884242d012280a80018003010f03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 678571016 1250 678569766 678569779
    0x171c0f05030411030307050a12031512061404110406060518041104050612060909011b050904020d062403020307020d05090303041e0801140402090a2c0d111b 69
    0x80d06200a0012070b400c1c3c0200142103d039140c10628150b922810020021074003103080e00700b82064070b4040d0064540d0115560341070b107001072401d021608000100b513401c0e10b513683d80d0260885904000c0240902c1240584001a8140e180c4400e000c2201c20350b40c40f00b4100714040c0310402d100c45585491201c80002100e000c150301c10f4811005c40d0501c01d0764000380e405a03000990b0401d00110b00e84e05403040784d08880c0400c844d51150501800d1704c6c008450203010034404900340810368051009040800c0000c0c20041c101364000503070760111501c039048050305900301d00c1d100210460300c07204078000b028186030130340c158200b040c2c02940d0341411014a40610002003952402d90b101041680c1c000c0400300209000c82c104d408460f80340c601b6074010b4000a5017005068000522034a81d0389005036401380060a140c0c1e680140e885c003d02c0300790010901200d2000c41c01c580780c0c40c0240404e10807005840a400f1a60800a02a0041c95501746005843c0c102c40c1200c54818910400140c0500094624 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 678572266 1250 678571016 678571021
    0x30215070606170c09090a0b071d04110903010507090f060e060f0a09030c0609060e04180506040c170c09011a0c01090f2d020103020a0c0c171c0f0503 66
    0x1100c09000140c20140f940400480740c240c2d0840300254513181d0400c141c80d0603001d515110803054a8401c503013006010901d001c004214924410020020349008807480a0740c09216680018107541c2e44000044040301d01003069061482c0c203100b0030b904960542040c1c00710360f1038490880c80c9042d06d8440d031010b10800a03940300d2140c544d00c04441316050380d00b004607522490544050034908241c00300b515400d8604501082c050701464954050f035519440313144018104004201c09808a60703420610303400100c42110010700304000e014021840713000d40724059401c16601015040041e0002134050784032004000d56515204170b028151b075240200314681d00e00c00c01c0440070314071900c5200c444641ca002e0841c0d0a01190a189241043c03007000d01602c1c5000050043d59480c4000032004214224000d01c0c1006601a80c0141541e0380b030790400c2ca0340459592a501105850360740a150700901e00c84107946020018040050700c0c03401d482c04175204110300c540007495003030001454000c0c450300202 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 678573516 1250 678572266 678572273
    0x5010315030b0a090309050d0b010e0403050903011b030c0527120d030b030d0503040b060d0c090f061d09031204060b10050a081510030207080c03040f08100603021507 73
    0x110202035a000401c100c0e0600f046290070000300a800003e0700004c0b5400d40228081c41e001d260301d001c494124000e070480381d0a00d441c062440038060b0003102440010070140c015500c007030040d4088407103800801c6c400600d804102406640200011074100b240411400380030807003850880921182c80c8113442d00c0c441041d40400c1c1d0007400c0d826908031900c6030076400300c2c5096158000d0301d00e021082c2c081c0c030015140e09805540300d010a40d0003c012503603400c001000c40c02c142d04030001c034a024280760f940d22540c2e0440034040b0340e0b01b491144601070f1921002d02050303032000140042c09050204110051802840701c41d1030f809050240305440c0540e40c0864140251604911150707400144180c01c105542c16002c3c21541c041a50540800c00c00c0c40028800c20503031290310410702019001c140700340c4020004400a5200c1141150300030700501441d100158108094006403100c12650b0900c5402c04d0f9080d458506600d14028410382040010b1006840e020300b402c48880000800716100e106526 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 678574766 1250 678573516 678573551
    0x506131a0d02040e070201060b0f0304080309010b040f23010e0c030a060305010212190c050f1605060c0903070902180618190f081504020d030903240609020a09050103 73
    0x2840c9420150003c40c000c10412003890742c0074000c034026002040400e03500c0905942500501075011a0a401030000501286401004650018040b0000030b17190561400180403207120785560411266a224502e80610001500e0000c60940300602038440d032402c100e0313070340c00d00004003030f026070040c044086030462040f40c0010001d950300c50001d41d03c5141810b41104580c500f140c40c542c8042c0e0005000e0103103c3e140c4521660109541c1d6064501000c110107010a030388401e2100341141c1c00d1031030000105109120240c000d1a5500c299a82d0300b182100b014600b142d203812540c1c1041c41041212203101155a2003000118151000d64948803180c141d01444458000c0458000c800410700015946016901d401a80d001403550b0b0010b0f9110b12a2a50b030305001c80110720700040e404041000f615060800400c4688240741c5802c0554503655619045103510b8081e100400002c0b8030080001643e0148070040c2505400450406000c071500600030000c0348074413410f15a4034100c606000c035640c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 678576016 1250 678574766 678574777
    0x74e06020d0203191406060a050c12030405010c090617070c05010c0806031002090a210f12081509060907020304081209030d020115030b0603100c08040204060506131a 73
    0x18115124040c1c801240d01942c41181c00c110310044c16040900410035a1080d003140c4c1ca00103a05109540d00d03881032000c0d039807094450100b4000c0600240c4580c2408121034100c00c01d4410410f031300c1c0d080c2841c02d1429600a2904c94003800f004c48000d0048945c4460144010310a8905404060305d41050641344d04e402c805010300a0b50078a0f213021a0140c0188516020b1002641180c480d20352059288049020387c810017a0f01500c4075008019040d000d82091b40106403490784002d65072800e07960708421240c0004221074100400008844898005002e00d40c010405070014101801d0000080c8011100601c103034420b041480110380d20910030410385000c1d000380030031549580d074203503002406508a520031520a20800d07202d903250070700c1070240f030300101e4520320a180d45609541c0d522085e40c1006005c4c0340c252088034507070000440d05004034113621140e515200e14606050040c0800c0d40c10030341026001e4002007102d1050080074860390310455403601c00c00b00c20300c000710f0042c400d00c1c486e8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 678577266 1250 678576016 678576023
    0x509030d0e130c03090c0501080106050a081509041a010807030b06011803020307080f0106140603012105030301030b0f0f04120302070309030203070605120106030b0a14130e074e 78
    0x1800f01c00258542c0607486902907602511904030055500c100440f2102c40034024880010801d00566032403a0149030305a400480c03680b51810b0403a01c132800f003212404101d5040c0c1384083d01400c440145200c180140d0f01410841001c5e1602078110f40307464020b03480140210b410005001000d00711624900f90100c0a15030060a94807102d50b03e08455941d6104840c1054083d46032000000740c008a0044540c040c980c054a8281147c3ca40000344050790920700007141a5104a41c03540f0000d1b006100650185100e03007045440b504149052059182008145950500b01e010502010070f481c80384100c09103400c0d15000d80e81c5e04c502c0c602100da002040d80000e4151207401d4020440c5078210014180032903101d5880b0b1481ea98920f8110255000c40000581050000000b880130f0107520034a41c0714418080c188124894420b0181030032560515442c00b00c94102c00002d00c801d00c02031034112000790b00303005561845880800a4514811741901501070460240e0354864241030401c5c0749402c0e0b641 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 678578516 1250 678577266 678577271
    0x10b07031209030305011806030f020105070302030c120a0f020c010804110f060301121a010e0a020f0c16030204110901050d0c2003030108060c030126070f240509030d0e13 75
    0x4503d8040c010b803200303005004c0300120fa0516211607a0301841903c08903134004481c1d0540c1c0b0032030b030015035182c3d04c421401d90840c04100a100e801c50802c000d111140b07080000c0b92680c40b10740660084c40b0181c0d5800200464000307440f0001580e80c044021034105422001c44a20a25140c0c001610040c10b0191746410a00c0030000044034501c042210a0850140070a0101031360242c03050b4101802c01d01452407207440c0c03036000c04c448403610b5024015614000495619154400d401d4901e4081c0c80150401c450695800a00440c14280690400d07010b4410703101c1c0c2001c20072000607103d03004120210039200d940f44a500a03040c41a45050700d0044001c04418903621403004d055240e038803d002e034200600c030303040100c0c00c1040c11000301ca0403a9500032000c0d459640030149107841850307141d804091842410030120382d0f00e0321410a040101102051000c441c05071000c0c080c1d0b241c0d0340c65001d0090080c00d009290690b100802e804080300c0892815034200c401810010f03400118040c030301c9150a2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 678579766 1250 678578516 678578531
    0xa0213030b100806040c0306021c05010e0402280303110a020a0b03010e0609040b0609270a03021005090304030807240c02010f0c051905070b07050a1d09010b070312 72
    0x34081c40903a002e0b910000e046402507840301d074800d645503003c0d20000c19400306800d040000c540307203501810703d03010a0381c000800e1038090152031042c0c0e5000c0e00b20a801c540c600c8203102c1103203040400d0340d011115082d1f8158524110301d02000e078000da80d11000d401e120500300864008075040c440e00000b01d5004000721680c0d91900b03007440c51604240290601c3c400c0d14008101c10b0710341503207154030450b403084134920240d640d074080c080c4030030f805010b10462600d286641030a05a1200c41449240b004500900d00c80515090091030907000c0f0a0402000d40382c00700340700c81c1e0a0088101c07801da0750802021075507441d1f546003140e202c5a0001012013284c0c08441ca0b03c1c089162074101c540e108051780d000f44403110301c0900c1001112a1040072502040301042141000003402400041074180e50520303504120f1300d82c4070020041c0c1b04456080000e00005101680590441c030022440c5242e58040300725040d0000c04a0400d0106010f503e020107000716614007054480c82d056501090040d41c21310411 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 678581016 1250 678579766 678579773
    0xf0a120c0204020f0c01050403110105010e070c0219081014010302090f0405100e01020a111615111009052b080a021b070503010501051c0605060d08041e090c0e090a021303 75
    0xe20094900b200043d241d0f10402d107900005008330340c1039034444010350030036445c0e9140c141c2c2c0301101051304073307000480c0d030045020f00d1003401c810900070003211001e0000b40700f183c1c000d58100c42c4940441c5450580350001840944c45500c1c552741d0009114840a0b650340300d50410794540918100c22113030a600b401c80d22403012006402410020009031140e1400c00081c0034955280c2e55221056500c414012000700082c3d01c401d5050848980181014608080240750746800c0201c4960301041c5151503007005820803404000d40c003d1000300c0b034000e40381020490141210318142903e00c07000c0000e40408182c16035103c0c0e0445203100500e2600e5065501c40519090329007845104d000d209500c0c0000000f181d0030943c61411100c601d810141f0080561507480364001c0c6009000c081e00600409100340006510788000c1001e8241c8000041c0040c2d200c0c545210061380b103802214440b0700b003245d1071003250340203803440d10030840c202e0f2031003110f5035402c044000901071581d943c80b280322941000000d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 678582266 1250 678581016 678581021
    0x6041206020d0905061e15010f0c02060d0606080405061003050d0f02011409100c020c010f12060905041b08030702010903110d0512041403030909010e07090f170f0a120c0204020f0c01 80
    0x840281c0c40394a684d55541003000072000c7e105507409010802d01d2054007400c80c0b05810400c00940f000b000d890400c586002c1100460304c242d005013000c01c414506110a208040103203d600c108004c292801b507509542d203594488003a42154828411030740b112440150003900b1842c1c600f501158201d046140030b03290959a05240c021100020749000010041c03544042904041c103141038440307050041002900310f542d80098550403503c2680c81d10007180040131402114001c4c0d0160000000a10110004030429805540079136080d5100300040d00060f60004031080849803c00b21003405800c1c4940402c00c50301ca10340c00100140101d403201c1212000d943c0150055600000100c44640102003d05a49100300d021081e0b1211740000100403603020303000ba450303204200e460300d01c1e1959a10944004078884070b4011501c0b00039151446c54010070200704030041100fa03100240382c2d0080c50f4484154110a8a4a580810003202031000654480341c0403078518509190f8200c0d9602c61070000c1500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 678583516 1250 678582266 678582301
    0x3070b04020108070206010b04050607062a090617010b03151201020436051003120201020a14070b06040203090a050714031c0504050f130905060f0606041206020d090506 74
    0x1083c0c80c3d034045003041c1e01c001b81403416100109401440c107810070003007107002e800c80c1108498454580407825440030380b8030a10b5490240c401d070f0103584000500740241c01c40030580c01010410411024170450707490001d1080c0d044070030b2400480d070399072660b80404000c115040041e5422048042d0f0f9171590000540c01803089a400101596078100906640d8910048800300121070300407092201c1c00100165101a8110818084009010b075903540c4441c00601e9254680000d40d50110703003002032940004022032510000c000740392070900c0542d03918143c008058600c40c0a04d5001c030005042e14010003049441070342110440d01d915035160003002c5040d0a500394280a805212030903490195050544050300469440c2c05043c1420134007849030810110100350b51045481440100903440c1d8810030440f0703802940580524609004489401280600243c0c012a810071041000503114644051481d0b8800341c05030707855201403000009000704034005480360240304103200f01101ca100b030101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 678584766 1250 678583516 678583519
    0x10507170a0e13020403080d05070e1804060b01050301081905011d0109261207020a080c010c0e0f0607020405060d0219030302011407080117120a110714060715020c03070b0402 77
    0x34074040d05450f07909a01561000601c0d1003403d20035404e00c2000c0e80c100d20b0b403040c1c4501e00280022031600001c2c8404e0142112080252440c206100910450b4080c02c00404005c1c01d21074079551514191554400c00880c80e2508942803607052003c0040a4101074050760440281680e410211045e080c02070219540440e0742a0008a003600380401c596890305441800b090034908000c0d0021401d11000c00083c4050304601034001c2c00b070000380382103006d08004000b0038000902e00d1944040600221310709502c6900c00c900129104d0169903400c1c00710b5043c0c0d581580c0203d05a110786000c50305110003840000d602801c0d56541c110105082000340e0120b0303000394024848904040901510490301340d07140c070001a40c1c0c0c00180f00e485011f800709030811140c00212590345c0c51700002400640c00c0325004c3d1000030300d440c00c400300c049004c100f914054202140241c020f03c0c000c000007109446800002001400b0075400d290440c6d0069054521007580b64060b01e685004074a000c1c0c0c07510030100c8089 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 678586016 1250 678584766 678584779
    0xa0906020c18010b280815090c0a18030f0302010203063109050a1b1511030412031b06092013020f2203030215070e010507170a0e 57
    0x4182c03920507000c00c108a14407030b900350240d080c1045080b040c0e00001c115482c81c030360403108000780c1d1001c03c1546200f550942d10404607051584240510b4210184000e10a18244062040080d500d4003200d800c096107007001380105107401e607041a0030086900141c1142d00c1034809606068040d001140310f40011202072184882c80101c904010308000d500350100a41c0c600307031014200580e40400745480c0108120b135144c030110356442007050400f03010000c01c0d18441c0350421100310703548900e1142d004a8200b41248e5009804850b03035034051881911001c1041c082400f0038180501c00240034130034903662038100d0840c0d038103100003d401d03801030884800c410307000e980c081001d035546111185800140314105441c0091000c2d0041e401a01c90b003082c0a504001400c07800c007900c0500070854020441c0c124295146040182c00c0103126019510740c0d2680c807041000403a8040d1035018038000c2401c0c406e46840090610030b0800020f000d60109100340016006607540d000300d50648449401c2b25407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 678587266 1250 678586016 678586033
    0xb0d050a0606020604030c0209070e09040c06020d0212071b1d06030c010504030b04111203071a060303090a17010603060c03020903010c031a0409050a0c06050d050702061b070510020a090602 83
    0x101e070b41d008100c41c086c00080c0200403040040c80d010104c03980040c028500303400c3d690710043c0002d000d628107640880c0c690710003c0c1c1c100070b416010701070340c808581140043c20f040001d510b80c1045521900c04000c1c02e51040d1503c3d62001e00700407030180c0103402c01034802005104600002c640417042900d5035031207485503051300c0001d0340c8200100c405899101c1c403070a00f2074441eaa038411640c0003504019601404051007410b00020400240c4015030041804422801100880c40c0311000c028044a009400030001800e4070f0711211032500031240c0c46894641e00440030340ca03c500510030742c0c100501285c2082010000c8551580281550001c202c0c0200081032400e9002e0b0211880b00a41c02d200078040c0c4410709052900c2e60100c42d40070700034020713180200a15641c0c159007082c190415000b00b500811202c1000160f84903140d40b04040b4001090300b0b0524500b491404817040020240b010707000603004041180c103005405181391550415501c641030603d011f441c00c05207000d118018480c5400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 678588516 1250 678587266 678587279
    0x40b010c2409080417061b0325090302010e0604141002010b040203160f0305070206061002150c030415060605161e0b0a110f09041d030a1d040c0f03150b0d050a06 71
    0x34030b5401002002000400f0340070048007181c403504000c0450042090300c032040544d400e046201d01c1c0c09401c9c2a80c031801103034218800540407040c0f40c0e01031070080000740000e0054031044000383ca04280c2c1110302d03481c0100b85070310032405019010440d941040c00402403001044401c506002d14002d00e0310340070481d11005004404440c0d00b2554500143c1c0407102150050a01d0b5041c883c254030a0703c10b0b514186500d4000030018402640c0610246000204000500c08184101100b0082d4024140203c0385030010007815405207844991b900741d0000102000c0181c0030441e81800f940c14881c05400c003082e0300701000405000c40c0d104034490b05140e580000b00c10786900f03e880700c0521441c04e13428960351070300f0300005005800340401441d1450103e440400c2c0100040c20790365040d035407a400c03076424080f001c95500c440c840309140200d050200003480710380c00c0348040d035030410300d40b8000071031a900e05044c0b03d85c5d103150b50203492401d80001d085150441c031350b0001d0b40b040d00c051034103004c0c60765100c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 678589766 1250 678588516 678588523
    0x6010e0402030609070e0d0b042102030a1202030a09060f0606020f0a170a09030b0c090a090c05120c130603021b0a0b010b0d2a0806040b010c2409080417 67
    0x441d09540461810002085c550140d2116010100702420b8141394880a90307500c585610103a40070f482203c2d500703442904440d902015241c03004642c1c40518240580c84001400280c030507280c0740d03203081c1c01100290209101341e00011445070001c00621000105d00309140003004507000302001806010004000c41c07400240e040750307666001303000c40038030412030303484110a4201400c01010025a810004041003c000d00d5901440002a009544203401b200b00681c900d131343e43c000d1b8175040c100721002070708913040310640f01e130320354070714100140f035134607040211310b070384201c90081e428080ea05001140e059030560181642240c00c0405400ba04009146590fa41020314001015010010012b0040e8243c000150804448001c4c0c0444c45204211601c500c58562800204200c640c2c40e01324a041071b1700c45e880a401c41c005aa00b0003c9144080000b00f6a00c2138210260001d10b00030f804c505402a94224001e810400c3e20040050094074541050154490f10074803100c2c1e1942e1140c61031070b0f40c011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 678591016 1250 678589766 678589771
    0x50f030a140a02120601060206130c060c05010f18140a0c1502010e0a030e041a0f04020703140f1b061e0619030c090e071a0708040f090506010e040203 66
    0x8009100c08185650340c4400c007035145081c00814021840381e0320040e25042c540302c80e032105071006440c4a6040181c020724104000b4460701d204c0522800150118400350400d200b0740c0c0382c0b0b14044d8004419405d0207800f401101d03911490480c81c041d400f0341c1c85400301200151a500c91540c1c8041c140f50102042e40c5c1d83c203c1c0c0c030058000703401c61300c0c01c10401d6040e5084030b10510300703070001092032104500c41c01d040810040080d0003040780f0075034091301da1a040c810264103010740011030b030300d04819002080c0b42e00000702d91180680d5000602d0340505005441d41c1e5001d18110742c0b0030790742d103d0455070021103401900030301e4025500c4000d42c050381e08012682c940f04030328640380c201c18403c0e400110f418011300582115048101c1074554610403c0c0c5281c60b00103540512203400f5070b40d01c0e14101208a52104ca002e181d6a0413018041c400740814801c544140410081c50a44650035403d061410744141e070b116070001152040d0000714519036400c03d034400c0209032503500d4281c08040a2006030f1004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 678592266 1250 678591016 678591019
    0x907080a02090109180803090c010f02210c01021e0405010e01020607022109120c0a0503191205040b190e04060608040212120c0a12020304051509040b1c020109050f 72
    0xb00d00041c040c403c0b0700d900541110000c1c1300d0502a41c081910b94400c0c550081d0341244198010031040180b0356040b161203481030b080d0388024006c064008036a90100e0941440305820560005100a0014000d4040e0f0390200d11422a40ba40786664090039121603110b44901c5d4007140201d40fa002c0c2541c0041051803080d20541c000c2c0940c072754980c10325080303445000c03411201c48009001d05085629040852160016144d00402c0c41885401c01c0120107615076116912030f9000803500034000746007029034591264020000e444656960006886900494020026030100801c0300d0100c1445904252102c00e1541c840007920288a01800b0a03104103004120101b03d00b000410014205001c0025000b500b220684c2c030001c81400306101f50b0f6202d035501c902c10340d01c22241e13a8140150b01d2290640480c0300d0004614040c0341c0340c0800c20201080e0895240113101060310000c503203c0b40c00084454a0080000390002411800c180342104100d0080c1e000460041001c03480741012800c20b180d6040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 678593516 1250 678592266 678592279
    0x1b09040f080d1418030304030503070c02220906052409060301020415050a0f1706011101091515091a1207050a0303052d0421171b060c07030c1a0106080907080a02 71
    0x101c3c0c041c02d96406150a100b24ec0140501c0085c0320b0403010034251090134441c1000100e03543c1c560382403e80a40348060082d00c50200100d811940e4804500300000c500103056505a00b03e5a81400181c02402664000c2502c2114243d8107401180d1020091801c808183c64402c201e40e10b42d1002c450392150a504658015440c101252196000c0c51400c2d5010861f00f0000c5401d800540d82d8100151400720313068501d648414540c0e10451110702c0c00000741c90000c1e810001d82681d2140300240f400c407400898090440c45906002c0d80000744542c201420000e8640004a690f13803500a0469016055091149094011508036102c803003200101c0004614082c600f014189032240c0702101420300c6440f81444040c01007000112103040c2d020011594079203441d160006c510102015900c3c81c0000ca1032601300c0810016690f400e041601d00700c50300751070012105101e0b8940101071030a900d5400c0700b0002451300000d80141c8c400703145c6208840c0f0006580003107554544d040e90355410500005c4d403044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 678594766 1250 678593516 678593521
    0x3060906060f0c0f03130603020903060c0f1b16050117010b030c090405011508070804030903110a09020c0f010b060a020604060209011407080405031b09040f080d1418030304030503 79
    0x141c5000608151280295030394a0b2070903100b0514070300040c9070700d820305541012415000404044140130b0040000703040070b62905200000103038907000010900d00030b00101044019286503140c081e14a080c840303031304440d0a071014402d050790300c1070003c0713040d8413020308544042031a5201e0401c5811882d402c110903400c903402c004041d01e194100a10a407280b000900650b2065a0746015450090248500c00d0610b9454164002c0501800800e10010b00c5144002e12000075884000341007200d4010f42201001d40c079500008082c08010f504c590340c0940042004030004901203803030b185900100d0003c00040f001d00e0107110b01401000c10312405a0000000140810300d56001000c51240514255516066480090b20560401c0e04161090f400202c0e0070300860400700100500205207014070000b40c0d5101d0009520500300410041240e8a0b1151305010494903100b41c48000012110502a080400320000364801d82203510f43c0306050300c9203031040340490100450780543d425544491441e03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 678596016 1250 678594766 678594769
    0xf09090b13031e12060e0f13020a0504020d0e0d1d040e01090c17010c0309380903211512031c0f0c020714040f0b0306070806090c03060906 61
    0x101884001542803041d28107100c3c0c02c0800d009100c0010200380e4135602030a82e9802c92000c01c0301d220780c0000c414208040c0a000700d011240810f65801034070b80a840c400c1c48001d1020400c0160294040c90300f00d4004203018240d21542e8000300041421602102c0c80291001d10031110700815960070204d180f6040b07140c468504180c0c01c5010800b03521070001c81c2108183d40e802a01542e01d80c8500844203910317440030b0034000c081c0038110080c122450305004083d52602d400c050f2007040301240e14226032500103400c440700c0010445001d01681c03001d514880c1343c0000d1040e141da2080c000408214190301000340709009501101d40155200c984289071402c10006110307500c820a06140d20702d00c03085c0441000d801c10381c00e6540314102045030100301c4914221108054450b841c100030f0645d0058501405880c150f070404605100e803c480200d82e039101c00500d40300410b0400302040d0140901c50801000680003108240115030584d080c0010755a102100d0308180400d0311b505510803212740206495 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 678597122 1106 678596016 678596041
    0x6090601080a0c05010c1e030905010e0301090825060903051e16230f010207030e1e04110f07060506090109060e010b0f070c0902040f09090b 62
    0x800009941c0c10f50481d48034010241003020651000003481204440f04902d4810044058a004402c0c03d005100704a83c0c00b849000c10700625030044213080c14420100016040100207052020200d0003030107214001c17040e4104070746c0125168001c643c95100300b0300f10902c01e84a00b583e4003084401c484030003405070030601c40f01c40240040040c4607144224014066441050980f403040c5030102c40c021990a882a8040b508c6640700000300d0140541c01443d1160203619201c08030391850307040110b00c40e1fa00800b10b404100007020b0060504140d0442103001e803100c001c00d410094644006049604a110182c4080b0303250803d01c002d40c01c0204802c0d005d4021000240400d50405c10101110401032140e5052004009003240c0c1801490090352441e907402800c0f2000d0964031100040a50418080c6040000e44d2039000030311103041c0d2042c6017616900a212040c02ea440d029416039 = true := by decide +kernel

theorem cover : BRFrame.Cov 678417266 678597122 := by
  have h0 := BRFrame.cov_init 678417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 678417266 ≤ n) (h2 : n < 678597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
