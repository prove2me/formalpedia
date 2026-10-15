-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5175
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:59:55.33327+00:00
-- url     : https://prove2.me/submissions/a9b807cf-2b10-4c91-98be-397c9a1abece

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 930575539 ≤ n < 930755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 930576789 1250 930575539 930575549
    0x40e070809070312030f09080d02040509071d1201020d060b0315011b140f030304060f060806060a0e0705091306051005040e04061512030903110609061b0f0304030c 72
    0x500200040c01c0c020001403800443e60480c40e034107560440e0420132005420100c81191060342c66aa940000900b60001410300d80400c0710010b07191030400041002d06a8003820810401c5841d8070001c4101890000907401c522086030000030b00254080400e0190103003400c481016898440005a40c6400d240218492000b280038003003184240c200568403500c65416107141078113800380d2040003400844410f440303201c582c0101c980044c440c42056107194001c60301204d0030b540701d90062282a54500804015202a00180600c0d15043d004601c3c814103074465800306041c4003001c90b5019009204035001003101400304490301c000000e2000241545105030fa0280c076600000d1900244594140e50030b503003030091002820740707640e02c2d0760015042060009080d070400200c0010400e8001d140c0441051203500c2e03540340ca41c51402c0c00301071005086000386c02070004216102c802d41d504412201940505500c0b8038000c1c09204c15a0701e0b00042c8042038505100003d8003000b481031100c3d200049032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 930578039 1250 930576789 930576797
    0x50a09060c090315090b06150c0f0307020906040e060a110408010c08041709060f0a020c06040311090a0630080705250f151403100501030615080609090c06040e07 71
    0x22000103141d086404040c5c0260091042c840403400342d2404143d002c0d0320250104280f400d0900303006400c2d0400d000b0000ea260b91b94030000d0740d68110f0405140b01036000204840c1080310715211610b0079198100109030b038070f00c1e90f40e83d91038400c0e42c1e004205a80207407414500030085040304000c0039010751070a0300c050b98031a5403c0b0f408061b26007107108407660160301030800c0b030801c6240d9615a4080d000050200c041d4021611a0100394403281d010344011070241c030103010b55071603000610800d1075000d403682d108681024004d002850510301010184a0703140342843c800e860600016004c04550200240302500000d1040c007440710020310310101241c544030818809015102d0442e00800b10b00c034a4101c0640b42c4010082d000781c4610b441002c0c1c09a0030005400d005d03c250030419603008540d4076824001c210424000c95901d481101c000c0d185442e08000d8215401001500402005160324826503440c0000341d050300003481251343c004800340ad2540c580d038503010401101c0394100d40490001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 930579289 1250 930578039 930578063
    0x90f0b07110a081b091302010e0d14010c0503060f01020706200309120312150d02060d0e102304020d080306011112070614070f030b0a0f0f0305010c11030d050a09060c0903 75
    0x590114500d01b45980e0305844a0101c241d5403000d000d00740e9040c40c820b44800070420200d4131303070481c2030080c286003003016680c441e540e24000007000804100c2e28009811940f150f2001d0202c41d0300200e0b504503030141440f03c8403150391080005482c507c13071042801d801c82103c0390121070200000028018514818000610642e94502214440c248045e290795004503554003036405410b07c0401000b060000384004500c0c242c000714a0341c601609184c1004080b980c0e080e02200c3d5003441c4000500310a004c120b0040c0701d040c16000114030142c0c418000d0f0030b108000002c142030368004c2c404a884545c03610b040e00ca085181440c10065070b00300c5182522110700700f450015000d84065400c62180d02591112486540601c1d030440081400c6100160864400032010413219510360080b0300500415259020b13a9040d880c00c1c0707081d50500d03140b4406202030071158080294010050302d5103403460f9580041c1d1542c54000060190503c0309015000900d440d0042030403550040f01c3d1804d99000d84410310007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 930580539 1250 930579289 930579301
    0x4120c0c27060b28021510030212070f0b0f07170729010902090102030d32180a031209150905030c070605250f02040516090f0b07110a081b09 62
    0x461300850b01000040c0c100c9900e820400e00040c08868115807001c030f90342032031612035000c1081d8031091050001980d000d200700b00150790b04c4040400c05084614002400c0240e01031041006000340d0800400050b00203030243d907600c000c8001d403404035403c07240b5001513808422a0300700f6108280b188280c00d9050400104460205008640c00000181e0055241c20107502900e4018100035040b0208480350703070f0a8002c000e4a88004000c01c071100c3d0361502e01400c060340d406003811081c41c1000c4440c1c12050725180400e8001165034a440120540850301104502e04400034245003a568080540b07409894024068000083d200200c4800d00f181c0b07041d86c6904043c3e03001e02540b010b14011110964000c040300c8424904400c8203482140300c18441d90303184e40001c054413011215240800400e0b220031800701d0b440703c1e0b520021309041a034031160303900b420318044a81c86000b030007608104221050100c0303501c50041c444010304003402500c24131110741d0000d40038180b62205180c0305400c0b12001c80c071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 930581789 1250 930580539 930580597
    0x115090f110301090b130501090f0b10050405150409060f0314060417071106030408071208010f030611130f05010906030b03031b0f0601060804120c0c27060b 69
    0x1811144405085085030318045810001d014076428480c1c0205020f00c940c10a5011b0b405641d01801100710042a0103038491039030811141c005034501d10410070301900e526101e40041c12101990b909580441e21070051000e84030f403a1040c0e0b48184442d80c90080002a40a040c042000c10b992041040c280c1d9446c011200035920603084d00c0107892014802d03c6414042900e0004208407449043c03201c124250110015059820850b01515684000a82c0404000b1006012044c02c2086e0510189550403c000c0400004240c00f006010590390701ea800c001000f10030035a4a501d00c902d40889a0640340c11841e0709164503840f9035804108010008140c5602902071070056200180085050400030000204001c050300e0300c03500c25000300d01d2001c42005080c0001ca002c1c10b910740785c2c480d16080620f428869240c0e8003014008024803445480000f03011354501d84100c0b1000d03031460100c0c41d900b1042c030300e1000806100c031004070b00c1c29800060102d601e101601c03004a0940c802d001104e5103100d440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 930583039 1250 930581789 930581801
    0xc150307091401020a0c230303071e030e0619110f031815041706061219141501050406080a0308130c09060605031603270807050115090f 60
    0xe0081040c07181c080c00800031103070906004120520444041c1e82c081e40303c540c054486504040404d040c0c0744862290702c0c2940d1400e5610100c02c0c0e0045180c40e04d02c0d200c4039042c05200407428000c45007640c0707400a061180115500c0030100800c40d680e24003400c2075004c00c898130048ca01000c00d051f20100c07400f034a0082007a0450b80410310186181c0581c58090f208082c0801070034a1344008488251940c9290f11406480070340110106138000c4c108034949286000801400d5500c03448000c401c07594801004508441008600381407080c2004040c035111030305e0300440c0ca00184031f104807069562818031305540a4100c842c1a6020801d007600d4000003034803034292900103000f02c0d102c107011861904401c81a0346005006007007030601c0c00d8580c031914054072480d030b2003503001030300210030b001c2620464441c100303280d152418200107548070013061a0040a040c40d883c01052103046120307081c84001c000325102107038000020090350110f158220744c0e482807030184880807407804c6001d5004100c82c2c0700709 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 930584289 1250 930583039 930583051
    0x61403010c08011202150d05010303111006062c19030201080f0106051921052e0b07030e03011407090e010b1602030a0204090c05010e0423070c0c080c1503 68
    0x4003005084980070300106e104a0000b02c0d030038500800540500c1692031003164080e40c400c0d51600d80600c0010505031a01e035840c07403001d218a141c05001c001003604244080d846481c58140245200c035010300c0410a50081410b031500003055800030019608d1454800301507170f1007602d419070540c031381c00b8440c034207280240121004600d080100c0c881c0c081403211041003d401600d460600201380541d441054141180f104009503110414400740f1890a03001028550658002c0310092014420041c182540ca11941e1903240000505100303240c41541103013591007001d0000d0202c11045884000500ca04494200000e00b2104c40450301051060340316048a0b5000301103814196200d214a080c907104070f9003284d1511407000000b005032524018a44418000c4078892030281c035140c00502045080c912961040303280c40d18000c0b40885a0b5800342201d01d200c0409125a0b80e1043c0c25588040d0f07900e0007400c804140480080e04440004e10354104c410b040d211000803500c0200b45040b980070603107072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 930585539 1250 930584289 930584309
    0x32409080d0b031905011e050603071e050d050304080105010510020d08060d060c090f05030a02011b03110303040b010302040c111c05190908010e0a0b070c15061403010c0801 76
    0x100c140180d034150010503640c0e1004080d90004c0007644038008050440000850345651506060300c072a9039507058081c0602882d0505024031701e08000041e4035604c1c1c0e4081c1840d54000c40400c0485044445070301c0c2e01402014104400c2c1e2404d40c102107a0760b070005d02c1108004e60070000082075034103203074203070103074944058000345120221840252801d540090030039401c1080c02c0c00746000704400e801049010318560704c41d504424100380d6404018900d507040b6a009501c840410750050340d0000103020940349000d1900c0c0c0c01222854111410001a5041d140784d10002c0248014401041e981c18100c030305c215020400c0c101d440717034191201000b680302c44040307812800141c1c000403d8504c900303061040b603180c01860300700040c002e548000800c02090002402c4084240800360091140500203840d100080c002c2d01c1c900d982d01c92181400130328101c2040b0000c00c056080028510004120b0b0130300d600c090101c01d072a07401642500c144861074038803d600303001ca800103290045414505840c02214 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 930586789 1250 930585539 930585547
    0x20d0f020702150d0b150d0b06040807062d090f05091009090203390301051510030e060c0304031803151e051e0115050315120703240908 60
    0xd042100740c10003490681c14a0711405ca120701a6074200080d4070107071301d02c5485622000c0544020741107070b1800d4001ca010380c6c4108414004c42000150060440b0040d00e895204010740710703080c1d1109081805500c1c009041050003064194208008030305aa0303509058441c0b060b903500811070106000c1e22201c03d440d140b807106222607041078011714182c82c0040c00700c84540e00900441c40750143d80c0e01e112151a07002c60b2a8400c04100c003074038020401c000714000d10140c01c01210000d040d03d5807040083c402c03503d150300040b006010b034018000f176010a005032860380c5012a00d9006580c001c440440000741403080c283c00402c07915450000f5a9000130360f0315100f03004d0402940c014a00c040300542a00510480407031644007500490f803081d10b07010f41071041041c0d90400d096021006812040211a2460701000500e6102d801e81e40d00040503038051003404105000315a50000c034200d0700d401380c041c015010042c0100081e0110006280c044103103141e044021400c42254080309005001d410208 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 930588039 1250 930586789 930586819
    0x70905060307032c0c030c030c0d0212060103050102030a0e030c15180f0f010b0306090d0806180f060a0605040609030609081b06040312050f1b1903020d0f020702 71
    0x600a5079101da820700700080c0d8218104141c4000060640c502d4500e0303034880340c4130540c1d2103007801405803500041e80208040e811150010303407500003036194540079141006240e025950f503c00400d4141d4610b105071204c658590420174040d600c00c4410b40e0003141025014800c00b400042154104c5030340e0400703041700c0030170720141081541001d03206410f0307621911156101c410b01881144803105054006004c0312070084011820358031640e40c0c80748a9084030f0100281c4000c0820307841d021380c000c1d03e800689941d814000802c0300250800f1500555000d000b04107000700040b580034094001143c20341e41040d5244011503142c8580d01501001031080501000040c6943e045000d61a10a44496007418890000c105a2564204164601d98000c409110901d50031440c09020442c501d0b171b003401685040300100500d8000a8800f0321131004d80c0c2c107285440c20201c0c060b6800e0344100c0041b00c88105e800e20000700a03400000400c20b8882c901503199510085034400c44007510760140c8452142a040c0d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 930589289 1250 930588039 930588049
    0xf0213360b0c0c0708070f050402030c0a08060d0c06020a11041e02032d10120803072d0e09160f050a0306090213080c0103050906180c060a050c060708070905 69
    0x5401c010342c02200b4020001412400d001c910050022503004229291804031a0380d000c00440d44001c0c0103d10420a0150135240d9500315406410142010b10480d140e01021030010440004090000708140002066983d40403820554240c055510350b0704e0460074408200858408001c5140c440301d40040384c84203104950041c3d82e0041e070420450054443e002112158911700840c903030315004c0041d0802245503060751500d0003410040c50b9a05840c0401c0da5000e81070300c8003809003000d10107201c5801c040622510000d2200c80e16000e182003440084a01c00b80c05004100c54092007192030303400003064503662429401e42ca40c003940d500c010f0014204020b40d6617900010b0120100342d00c403400440e40b040c090005100f0b1400240807038030300382c1c43c09004508184c02248424109418141030024540b40051007a80000031041c4803011440300c0e0f11501e01d012881d4408540241c07000c45e0180300e00780c101e07000d042c090914900340c0d140c40d9204074088a04200844816006c030321019001c1c0518182 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 930590539 1250 930589289 930589291
    0x201152102030609060f1302090703240b190e0a030807020d0c08060601120203130b060a03060912090f06050d0c1209210203160803040f0213360b 64
    0x380410529440d08640109040020840700c01d00140c0c068010300919119045400d584445c86505030000c0c2501036000800728100a01841e0415480310080c41d46558a01411511400e180100328a0181d454840307501680003929803101d82003c180345020481e0040800220040008248018080c2540d86040b03403a04860005d070780243e40104a038002540701c1d82c0000146c601c40000301038624203103000415804070001c908403450700600a101002408900c00c40219900150b40c005aa030750601103040761500d50b201031b10941c04e2110320307420300c608044074a103103a06559503100c41e2502c0d054a1007220080b88220f0f4001041088501d56600c007c0e482440540c8251911106034000340c0302800075100c1c032090030f9400304003204c40c13000b50810013201715081d09801d00286080c10409080d809506403c5000505080310020020f420081c0d06041d8a5686a000340031076200811481c07032100400b040440c8075103151111920489254611820f0108845a1200c0071400e040315074800d064094 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 930591789 1250 930590539 930590579
    0x1806090405010e030a03200a0f120b03030d0f1d03030a091110020309031b0f0103020c030f160605010b040e0c0706110f12151018030204020f0d0c020115 67
    0x50b94000c0090440f00600061030703212080c2c1d40210750060440b910200100440c1e0059030ba082040000002c4150800001c440043c1d26040000003942008110070261001114080c3d25002c002001c00b41d0f454141e02055100c80d51f500200040c09000c03c5580c10300b5500480750750f0590091001131205071244e040040c103244952030120003401e481021070f40c1451a00140d00140e080850500b8a6090800070040490641428070047e80031482c0070500c139408444c1064100b6400044000351003004104841c101c050352411256108005d1490351408003154008903401420440001100c1c40004140c5090301c0011051410720744a80541c4001507015a0b01241c210b6100d01c1012645024040a0800c10310022145547c800da1031045a195481c01482d04401444000d201c1c80781c2d03141e9511641c201000350802419605426502c25240059540001d40c07043c00010403070211012003000e008000d80425080c006000c1c03104d003c0c0d00381c03000c3c00c007545401004200204400d036840203100310000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 930593039 1250 930591789 930591791
    0x9050d060209031903030506041505121c080702121323040e0f0c0a140411040b030901061a16020609120604080309151603050a0e011409010506180609040501 69
    0xc80160040b908102401e03070315504084c02d05004105050301802090703413220044904002201c001c506c403801190250003031500031034a1040002c0b02003400c100002e0f50311108003c40c1c4850440c07020080c2070010031180031006004140c5145006102b10054a5009620380035041c01e040c00c1541040105010329021041c80d0042c1043c1d04060f15144034089900d4908005440c182c0c01070b40e880380c03400015091040c01404a114100304015424113480300303400341290003051085410041c104c0f280116041548842800018441440015840071040303c02010030f03444100c4104603042c006020300c2d01034140c442c402050480c018030b0210010b01124100800003040d5486800c1210b290240807581150b20344000024450519405c204040034401c00822148262501c101000c90206052444500707040d1103402081e645411070b045078910080c608000c100240700202d54079100c1e40c0503a00e2550551800e40403d00344e04182020300615407040018030381984560302440950503000304290707495 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 930594289 1250 930593039 930593047
    0x12011202131b091a0d09021f0207080d0e100309051011040306200a181206051014060a110a0803010b040611030304020f040504050f0303070f02070b04050109050d0602 73
    0x204120300c603902c01d100100360b4049440c0030042d4040c04089540c0c1142c5000c0d1254800e86040702405004c03201c2000380c1038800325058450380301007485641d03482d40407108203041e60381c081845980007803000b044802101c12100c806400001c140d81c030a094050b40340e00043d510a102c212240240c1010000621942c03c40e40d01c8a00d203408041160701214013103109420028040007031114601602442031340b00030b560000c4481c9015566510b2142440c9031091004840b050103200c6100f0040000420204284048409041c0b4120303000784012a9000e0034008481404101690009001359010001a06041c40d020f0205815904501d445284060300d200b404514000034034010003540c000c0110b000941e84403402e103480075101407441c0082903801d50042c020000540c8d90290030a20350035054034005103039159403c3c40e0b810302e90441d0168145210010510a6440c1d104031061030075503043d42559503131074891072124040d20a0b8410103000a140003014059031401105850000d84202c0c4010301d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 930595539 1250 930594289 930594319
    0x7180509040c180e10020406080f10090c08160e030c01180b04140102061b040e0c070210021c02060f0a050c04031a0601080c1611011106010305010501030c0b12011202 73
    0x140f00c814080c40b580a40b030344407000310403e04000c050103a101119055003040c0c00c040c4003c100c08001040b0b015801c2c41503010450307491080d12580081d03e842602807162480c80c000203820020305481c00700700000d03800710265419218403020941280000d0141c908000e49500449028280d515048840803d0380b80016456094100030300080401c20302540c21058090006400c009004103009602c50805d200380c55441900c00899041e2039023200580016140c0d03200e0400c450045000080d08822140c49100c0e05c031780c001440c4164058000840008150b070040704a8440100f6130740c01d4403001c641d0300400c02c02c3c01d858012903030009000054500b070035501c0c1c40384020784a45024080030301000c0310074400c2c2564404007041c3c0c01700000c15040d14005496030304120030340403a403000c2c15028902000c840d60341e1089185401d028482401c46010356140c4c02d1841c02080d003880115084d1151010010b010384c40c1c00203947c0c20506000c00e44050741e192460b640080c00c0c540c54100d034404d0b50b603818021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 930596789 1250 930595539 930595559
    0x1020a1502130e0a0e030c0c04021b03161506030b0612120706060810092006090a0b030136050c04090504051b0301060f1a1e03090607180509040c 64
    0x7403d0020302c1c414642003001c03041049074400c583c814040d401c100321920740c21b8030015100da03407800290340c01a52900418084424811043d11550103408002020140316881c04804520140201203070501c084060300c200b422200b01d03120003807800d0039540004295141c0b02c070a00e0a224242025100203222120440e2469882400110b54140e42c40703c0a002f00c680c104030700000d00c1c0603c0810040d01034a03444410401e00110003120012607400c21003003913a151413090702e42605020b40780c1c05215884402605840e00240915203228058070140e0803000788200c01d0703602d07420b6a1000350800729800304103000038000c020984903240108110001b100d241922502d4829401180580210742810200c0785134a0140e40c40f8510070b80c105001170052480d007a0101080742c0c595005540c61242500c110842401024000c001007100044961110038108000314410084501921225680d201054030040c4400c20340c00d20b005225541030201e0b041009100d90042e0244410300794040c1e94a81d01c0d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 930598039 1250 930596789 930596827
    0x90c05040603210e0609130e011118030313050d0c030b0a0209042d0f110705070e070503010e01090f0b0a030c1d0408120403170c070b0c0901020a1502 66
    0x4850000101110f800c221076555203021124003454040d0500700a000011100d01604428512034024860345400020b080c1c0d011400c00402100207000c141140302c0301404542000c109141c60804964945645c0d1801104558140301440d0088103881e0801040c4030900c0700480c82200c0002e000d00c8040003182000718814800c144200c000b50b52101c05105200654414240301001c1c00200315094068524814400700d9406240e0b80c001035640c12060918084e01100e83c11040030b2000091036001e001001c18007030b0903030300f02540c2c4500035110458202c90b544424480d4170104c0d1a104018494401c1940042201043c020004a0003100c50000540410240e5004890386034543c5001c02000e08502100074420000c0f4107800594942926485428807030b0001e1007078030520301c600080416000b400d00121410522240308485e280c001044039103540910015a654603000e0005002812044101c40c40c006060b400342000c4403240c0d03103a00d411456040728905541c0c0a00c10740d2480c0c1201c007084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 930599289 1250 930598039 930598043
    0x723180408090f10080c03060301090f0f050717030d1a0402220b07050a020910120803060901050d080d090c0b0d0f0b0d0b070f0302040f0608040203070801050613090c05040603 77
    0x200c0d6840c604030080210703c80079000518000e1000d83d60034400143c0000380c85e940510307002401c0b0307666510000082c3c0182883d5000030a11300048444105200702c042c45451054400c1040341c140035180c440440d00200c9036658038031180e004100149a03030129800c0b0720268024802c2c0d0308441c085d10000101a43c101c88044105244185001c000d00c1c6900c030405402884503240c0307507280c00c03102d864042e103500844001034040c1081d040811400000c18440030014404194003504810036450b008410f80c2c03007601d840f440707403519000104051502c011a000410345c0034a41500e001e000d00844400342002440c00c1e501809022400560302c840d50008100380c0d0018480040c030754000c0414601201e0f6011040b034010b40160080d00d0000c1c41000c0500d420500702d0030100803015036002c044001e841a80c009480024900c0c0c4000749481d000400070380245e10881c1624801520303450061b003200e4040341c240798080c0c0c072800191022440c40e44405002e030300680395030186a4a40b00410142d840c1c1d0380c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 930600539 1250 930599289 930599303
    0x819050a0305060103050606180f041b1724030a0c171b210307020402070606050f011e140d060329060334030b07030e07231804 56
    0x61880e28950501ca06a4014024203041200d41000d00200fa1306009401c00ca0841402046809080c0c1e50340f0f4080d8412148001c1040c42440c280700f081c41c48a0254642c1030002c605040078a20400c0c0340034260321b00c1007038150764142e0002e801408904022100009042d09030044168810108040400d58170182111001c4005030440c6003600620b031117121810100703180d44404104106607070b462031080b01c03416620249403441030050b00007400c61080d0200290b000b84002008810000c181d007001c1d00316501160141d51009800006640801c4008201d540c040c244400c08501c003802500114801c0b410905854140240798411508490058100342da01e0481064001e4400149103504410118100c040f0401824044042560340e4076080103098044024103140000c0f9600807501380e10a500c250680007450780d42d06103007054100c107903591b030002820b0180e0003d40d4130300022407404658040101010281e43c0c1d215404c0b02c0d0409904060340000d01940c01185640c548802c14040e42c01404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 930601789 1250 930600539 930600547
    0x9020d050f070b090f060c28020f0105030609010603110729010503030c15060402070b040f030e060702030703140f16060906030b010c0303090c080304060804140a0203060a09081905 79
    0x400d480d02d4816070003001244030400140f05152030320b810381032403030a00b5a40c0c02d4840c4070140e0307407600b02111101000008803a03840e8038000c40740800d440800b594000e903010075120b610540116014403045940c1504544560010080a4403a612148900c101510300600300001c50b07460580d11842282c0b001d602400f09000340140001504640c0d00403c0110300a5140902d206a000d44607200f5040d0280c4101c880400503074541c407580c0446141e00c1e8070403c1340c51945018544510945801e0303c09a002601d111018400c0741401000c0f940456001001000902d1441c0c0d0703541e90403800c004950050b8012030810201c011410000c4d026260381c0c0400034000c141c00c00704010b01903d00c541c000d00c10541802031003d8180d0f08842c84003100da405140c0843c0b240d0142c20f01c01014103260703112010a200010b0300090081c1e000521a0080d0311461041103e070100c00c144aa50740300201010354035030040d030003082c03500105504c0301d030f4058031a8560074104004881c900302048021914079000c110001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 930603039 1250 930601789 930601813
    0x20604020a080d02060a0c02030708121501031802040b030111040f031104060e070302090d02030d0201020a030609090b07200111210708010b090a150504080f0a02090a0f09020d05 78
    0x34070a040a030000c2d00c01442001d0048800075500c400c05880ba01ca0203a42c0c51100c58228400e00c12268420b41140b9120359071155030b054001c14501c1100e54901c6140c2c5501c40c5c00c0d03650300c2809860f0f1580f004030850305c0044196000c000040102404443d415966801c03103d1100203000091300080c07000d0074209007514039508040701e0502c1140b88291050b45071a4040c000e0a54000c1c096404c240c03907240058a8549210101c4c0b0380075441a070182d8144240c0348084400e507415001000801c003d0303642840110766030410301e41542d5a10b01d008040031620000201e10f1445650500c0044c3c80c8000d5034084a0545041170b421540c4031a510034541000041e4043c20950000c08003070480c513219030300922440c4c4140f0003031003464103008907070300710b24002400034140c0d94003040e4038007401c42c1051b030b04480b49248401402e00c0e40140300c1c0d180180115940d11904d13500200c0c1118a940c1c01070300c0041541d85802140000302081c1169068142c2d40d80203c4000da1540c1e1002100300e8030401c002c00d500d4201c0c07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 930604289 1250 930603039 930603049
    0x6020601080303040506040f0311060c03090c01090311010f050d09051b030c010f0f051e0403030221090103050a110a020d1e090b13211a0c03151c0302060402 69
    0x5030400d4038654001c00902001410004065034066023262240320040841d1400312481c1c1540c0b585c40015105103014002544100b80046026030005001c80311140125001580c1003c5103203c05808007072508440384065000d112910350242c02450080c2c40c00c0d0702d5a901c002103a0703040a058805500200d110300b85000605480d8020f200100c00900c0d500780d20000080045038000c1c45082007201415149190358022025503041d044107041d813004641c2c801c4003144c0242c205100940040c4114855000c7c140e9048050718240030b01c3c221240c0c0782503c800010f4002d41009003484007469a121117611100c00d1102c0a080800881c1e400f5001e80340801070002c003445014092822801c0310503080c194041d8002c1c654400700c81c807450b1035984500c1d00400ba04a0b03c3c00d0380d0b2080c100c0925100229a20f02c0241c402c216059126507114040740403483e084c1c15003040210340600d040482040810f080540d5141c2001d024440202900441c15421b5200d140c0800401011070140c2e1181041c07200314541 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 930605539 1250 930604289 930604291
    0x1c090906030b06120c0d051f0903082a0301080a0308010503120706110d0e0334031d1e0418020d021311130311102102070b040507060206 60
    0x14010030301031582103442d001c80c00a000b8002c5403143c82c007951850843c0c0e0f81032122080c420001001100030001500f0641d4440c200441c12441c480340120300070300340490314840c02402c29095a203640d41582c0304420140317414100e0300340030b0020049941c040700c01d800703c0000303502920840700544a0b8540038600030f002100e060b00000d1080c4c10003449a19520b2080080e18103031600110040396000040c44000e07103a109030550490307418100151043c44100c000010308060008044802c0503003152203990841c0910720844c442c1c0e0004903120754001c05d1048200120f0704e25804201000e01c0c4032000020f80d802e605844503a400f480e000221072043c0380038440d0703150084000100b400c0d0001540e00243c1d04000e2410003d01c22260fa81c2c00042c464005c2c1d120384412031080da4a941e48404126801e00c842d645440f04903422407900e074901d8074074100319811450082e170039112020001800c90503002c0040b44c14039000c00f146d40c24000d00d4045219620034501172401340001d81040c0d414948001e0400304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 930606789 1250 930605539 930605549
    0x7030b190c17070c11010e1903081b07031a07020f0601060801080708072d080709052d0601140d0203010308040512120405060306040f1a031605060f0a03060302031c09 73
    0x400e01c030f0803005c00c08040412900c81c0003460030407100f600740000204c00c0c000c3c0400c203624821900001208200c0303403900600e001038040c100176900b8241e0303400942d904d802c103020091010071f0107070a28046200100a0030b030802c01c1401560049101c1600c0103103001426481079001407101c0004008100041c44404041c2c4201009485000d00707010441c401160844801484401459682450b030444440c5910142002d83c0c20380d00c400c1e40d16407c10f005000155900c81010f13801d881104001445682c42525281c80c04070001c0d6140d175090015604610000030300b8003000001c0160403940301c3c5510055002c2e5229086854803942072805016128000b4100180c01d0ba00c1840030002411001083d18100c074012110140d0b41c1e81d0780b2020401a2a03902d03800040b0314107110308809011000c0c2410704201c4002d030201d41c20000c030502e16940c0301e241445030301c0d0450303000c10060504d030b000800200440c0c20301d400c000c07888581c2e136400b10703203040d05401802030b13461400365020303001070341c080c0002000700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 930608039 1250 930606789 930606797
    0x3090c0f1d0601091502010f0f0b0904030e061909031b0f03060f0609050f06040b060301060c0821040807060b09060a05060a031d0304060e04020a0207030b190c1707 72
    0x9070404490000684110700c0700701c0c50070406030016070b29070302c50010040a0a40c80c0040403080b42c4440c0040c2c080c0540c918210031131403d00100c86405a41e9114841103101c00820205141c0c8031501e0070748194502d1a01117821101c108841b2100042c0020303c1c640084060762026403082c51810f0800b4110620000c84000700545407040000c8031100540c0741c10360303400400019901402403000001021554001c000709820841048101408030280c2d40c80f481054405101400c242c904100341440300340502000b003407200100314081108140600b07031a0524456040e0701029501c07090303142d1340d03084400f1100b08000050721000c014140c010400121030035160052242441030004103034211030b000340340c0034060204841003500d01c240c01507810303104503c0110040c102c5840388030f900ca901500a5001140700c4444c4001103081078400ca540d40b946941c0905070f80d6003159510040c1e03100250142c065190250305482d0b8022842c0310307001c134451070394490700d0000c070302c40c40c04105c2058000c1201c0140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 930609289 1250 930608039 930608069
    0x311010e0d180303211b09030618050607110c040603050c0a061b020d0305090a0f060e010203070b131419060b01081611010f0905011a0a0f1a160303090c 67
    0x98101d201c08207849859081c400088a0031307044003000307001c1017034131510782585203000186d1103400c907a80c6004c0c1e0380a841c013404800014180069411f080c0d09000304903078054400101c850b442100140500e8100c3c0056407e4407010000040139643d10790000e803080d0300055111016413906000c031400400d49070404280508002c4892260502d000d800680100d891240c507008051041c030450307161401c0280711074469522180105508180350141d1404240c005844071070740c0d800042500d810990000e516285540c84038550f17200500d00c000d00310754810803605640e416200522035000980402d20001c4000c0303141c0c0c284242a220110841c0303042c404800709204140e15070070f46a11004065083c00e00f0502c0721000307020300502c0703242d044040a928202e4550100a01034101c20485e446100c0d05660407041c82c002c04c070054100c0d115101c080004800304003e10f84914420b40c6610f44801c40f4035042000e0030943c0d5001c40380c0c540044001030703943c000d02001c100c215441da00203850f103080c5070452 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 930610539 1250 930609289 930609293
    0xe0108070b120601110d0f03050c181e0a03030806040b01050c0a020f01112b020118170d020c01020c060106110316020a082509020a0503070c0311010e0d1803 69
    0x80d9108020103000d102a00c00b00080c0180d004886078501c65040001300c480c01c92218000410394084000c071100040e0401000c00c0314909998140c4404100c94480910848072550400c02c0b990410700c9184c040a044459030110359503030001e0310000791700030b0f00e5408692503c01c0811080b10030083d07045040c040d0600a071518550005980038031a0f506440c441c00118454005840c0044540d0701c0805a1154848142c8643c00d11181c1c90200150109401700d4180c06a10680c280d43c0d80048080940c0d603500c1e6001d0210790316006e09135807072898030020b40c504400c00400809907800900c41501036900000c3c0382a100700c2c02c000f07060040c2045d1030a119511f0203800a00d4403446014421000c412001540300159903540c3c2d03c450091100d102100e50000c4180880e90004004440113a4a10200000003035420b5160007210301c0c86205aa64a10b1a91480300c01e968640400c2c90a4040125070804c007102580244101013607944101d0051600744800341c3c0040c00c452201115002d207115102c01040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 930611789 1250 930610539 930610559
    0x608030c0a120804150b040e0613060e0d05070305031506070309080c0103150b07020f040c03050f0f04020a090f021b0c28090e0a05031809011d07081b0409060e010807 73
    0x42c21188038000410001081030007d4007802c41611130f548140106410f001d14807010448506090344201d0046c001c40101c1103c06850747c54480070440861f03010420305000034442c00056170702420065045280200ca14007041681c1c000c3c1c03c04401140c00c0100a000c40503080001240f94242460140009403003121900c440301c1051051031000c000110300d00c002c641e01d0844203000180041c00400001e4801440100076045c25a0f0b600d401c101c0d03002c08038804003d0b10340220b2013290064405090103140081c0400101080003c07500656030a204954940c0d04040c11410070009403001062880750f604100003001c0340403017054240d212817160802079602e40c0b0200500b02c0391680c1c00040e41066191b80b042c1041581e14006086000c001204190102d040c641005414825110300004d680ca900d07400e1005442030222921040d84000090036052059080c0c9611030b03914030710190070100640c1c0b40005a0031a8110300e2034940c5410302803021a00c2540614018080c80000f09055442d11103e02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 930613039 1250 930611789 930611813
    0x51614030a14150a1b050a021f231902041406030408071b061704080304120207120804050f0117010311010c0b0117010c03051006120608030c0a120804 66
    0xa000c405070900c082003403a0184056100110b4122060300180b4000340300000801ca02c98100400d9001c0c0b50500a4080c8106c0a488031241389400501044140c4480c04a4020070005019803080d251301e12009404000054040c692111629000703036414640340358900702e0210608069080e1042c80308000141d4110700b4114851000c1d81c005030390f0345076801c000c1c60030300c950000a8902600e1508540c0030422089205003190307030b281e4881c0f821001c0c610000644150a89003d01561803e00100300840d80c2e04914640e1400d40d0300458040540d940c03005440c080031410252406a404942080304d800c003282c0c1c52103c040301b4070b042060f51b08043ca074107043c604103001c05802c481c00b02d04c4000441e405150460885508544149025071b552200109451351580c50756629500300340c517201e0080d010b4012580902011000510311506202d02100d03503920003a030941c0a191203040000d0080d0080c00201580b8404801500803c552402c120405d00010306002041104c0b0b001004040b0310400c11079 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 930614289 1250 930613039 930613043
    0x1a1003020706061a040e06091b1615061d0c030c0c010f02072f060913021b01091e030906050702031e07050f060301050d0602070507030b0103051614030a 67
    0x40c0c60790000d007041d9006151a0700f2000c801c201c1c007a5155580100d460240003101c140702c1c056684c42c3d4400061092040302a00d0b001e008c1c406401092880590602c00307407103500c80c908103003c1500160b841c0d0310b0002c2205103070a03901c50b90390746c01800341b482a104129220142c01c6030350781403400c218030504041d00c8003c0c900c0207002008140c1201244080d00301844641c1f0340ca10542d2113450340e060603104401c3c0c00034036078410407a5640c162a40400000462400100203041d81d0410750707031344103110702040f154ac0107824560303080101001d240c1110f048989060550300000808201c240342c400006d4214608040d40c0e800c5007000c41e4002a031040520094503c6407400e25243c11032840232178a044090340294403000c0c511030340c40a5802d00018401c04a50040301c3d00e04c104140c0b0000c2c0301151000313000b9580c0207020f502e003000205000341c0050a005200b00101c404e19607590311030f444900300030b800450313250f00501c80f00d4209501103100e00010f410640c100c40d118038914000240da40f0a02080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 930615539 1250 930614289 930614291
    0x4080c01090305030d0509071a0d0f052e030f1b05120a030e31050109020c120a14040b0a0e0f011704020102120a030902030d0e030d030207051014040302011a1003 71
    0x80c6281c5001d06c800c80c003c9c4281a8681602031020a501c14960014040904540e180a1010104065038040c05004101c0d091504501080451303c100c0d950341c1240c1064500d042c2c54800100040c1444035603580700d0700420300304a0a170007507844260300d02103c1c0c0c407441c85039001d600303002c80040c404500e141c94654542401100c0843c0c040105401240880702e41e408600d400c45280d8420580c000000c004010500c000c100c244c2c2c80d400103074100e002e585d00701c044a0f4080e030a1800c5903d0040c005108541c143d0a01112540c40d0400303130b01880c0c0c4550004c028800b800300d03005030007a802201c20740104004440000d20000d915000a104840000902c0c007030340403410124040da4000d0000685003414200c82555402a100000d0050010510101d009120355100b402003140f0882e8030b024007910050140400340340d4280110040e410a80c0e0559841c050303a980d01e40a0319007403280d00305d2104007000c480b903607140606000c4c0c00c40b4200750700d00c0545400c015041c0300e550f40d41c0351ba4000d15112420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 930616789 1250 930615539 930615541
    0x2603061f0212030406020c12040803071e060c050d0c08061323180f0a03050306120102040b0304110f03010c140a030e01050f0f0a0b03030301171c0504080c01090305030d05 75
    0x200701d1400840418114440c003000090000340030441d0010640c011410084500404a04011304150310692040305450741061042c2d00024080c6282448211040304480010701455200d040c1141d000741c41c00e601007140080c840541040f14041d0f00409445410820b0140c035000b0041540d007a00e00407440815940c4504070101c01d1a160480060030840b06403ca03094507205910449480605c41301540502c5a9540070350104000540d51002d145e06a407010f08540b070760800d0150036030a86540340b800355003e000c0401c0701c2c150403002c2c510403030052400e001e82101110038440e0211541040c5402a414014a540c4881d04802c030f402108107051081c59031030904180460040c250b610f00e51000b5403d05051004002ca0038141c00c0c0900c1d4894a1900c55807590300e5440d044812130140b60360590001d000400107c0702241c610540404a4000d45030407094003100d200c404501c4201d591701146c00400c090040300c200b0098842c4104082c00c0201d18142551281d5580e801100164090252508 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 930618039 1250 930616789 930616849
    0x312050c0706060339050f0105041806150302120f0c0403060e03070212060f01060e130c030606020d0201020a080a0b0d050604030e030d210911030a260306 68
    0x822a01c101e50000000c205490702c0349442850490800c0988170b4900c03408039444481000070450020039601107900401062822007840900780c200c0d09002c0c1485010710001422107842d080074004048419400180139080103484594089a44250001c00d8030512400e40741d52032440d0030701c0d0812260a030075030465441004080c03040c480c41d040200f0307a50920030340c0c0750120350010203050003e108460200040c02c407600d1791551500308540680341c03035288200400c0b8440c060580c50840d03000180081680d6458980c2c0300094841400305d040000f650360030200000d5270f05014001c803000c524070007036180c90074444009150744c8000d000f150800360788100da401c0c203a4902040c14541540310003502d03850719040c00c01500b1082170b030f05210b0080c040e01c8035540913070f44070700d08040411030392040c0d4200c64552810600e0051442c95800c8407090940404a1500d41e010021120a54482c14501045981040003209100044242d2040c80582402840400d55400121001c41c0107401005180c21940c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 930619289 1250 930618039 930618061
    0x11713140c0310061d0610031e1404031202040f05060f04030f05030414030601050a09231302041409071205070e0f090c0f03033c03090d020a031205 65
    0x401456030510a00c042c8038003051180c0c005408030f40220001510341c8612031800c00051004960f111f9005000c490294400d0b4020350001100c5803042c6420b410398045901400d0850f801d0072015180c41e140c0d038003040109035021601010121101005508207440c200b000040c1c4005401102c1c0324141c04243c01102d1100c29094a00840c1c0010180700c40c0c001508025440c0d41c0a8018401015002c0319140150f00700040d030036040344c8025140030300d214a000040c030024501580311078842e0840c20041440c0c881c1c2964040d014240505204e203c01c0d05c42d10401044580d21020408240c000000300600041d010030f4072001c1f00c0c0302e2100c4404000b614600903060109940140d441c203580c210500071040107000d44c15100e02d0021040751003201c81c880030400e034040340140855140e4401c10000d0405a01d2310f1110181407920100340b032010000c0303035820030882e41c281c60030070b4811008010000821401c010307054032440180080d0001014540303004040101d03110581c481542c660b00454024a10307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 930620539 1250 930619289 930619303
    0x80606180604180b0106110624060a0c0b0a05071803050a08090a080609031903051b1b03031302010f0c0c05041515020d0f020c0108150307120c030201171314 69
    0x41308606030700742d68486038054409070f010309059007a80314183c001540801a02144c0c0241c804a409040c50148031031308001a545c01210303001c0c00c01c1110711a183c005541c0807401400f81c0941a000720301440c062500a111a00e0b101c0d1259885035110001c1021a00c0800c85d1010281c000255a130384004d0303900400c505802d0b81c0c0c03080e00305121341420000d800d000400581015001d00000500c1201d5420003201510416200551040c00e10480c100891480380c00502d1a0084912007484802d540c440090440d00102c54040304130f051030100508640e0700540d4621480d1440c01d00c0080107449403140901c134001ea0040c24022035550154001c145912510640200703507204070b0440340c03110040001d44441c0c0307060342c2101046013011008c00c594000f040c0c0404921060703649510a565811443c0c5080c51010f0209815000e00c40307008c10015245100040c1507400b901419040310310307503c00100031025000b1040b10f106184028064000d1902402000042e0003040010f00e88040f0003100d030401c46 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 930621789 1250 930620539 930620543
    0x10f060b0d02070501111201060f050a1205041b120c1d0a0f0603020a1410020d0203071e023303070503150f190603051b0a080a090c030c08060618060418 67
    0x141c041107030380c040247c80801c1d40c103172001070391041005120400c050311a8040c800d03a50300031400080c18400800781e1603001c103901034000c0396500000c10741d0b8420810000225001410780d6208003c5e003005005030494600010074440c4c0f40c500201d0060841d4841d030400141070159190745681e00d00600c0d00c1d140d04588081c50b00140752400080c0d0307441e1004020714442c0b800c0380c0180000e03110403e1650010416000b02c4409401440c9040219a1021b090340141070401c0d04040800044c00096260400145a214045003c991003001c10f40007405014806071500c01004d08100704010105511030180c036000310b08140081000c800e0440010240c40164040350b4002211203c0c0700302001c4048a198111b4055490400c49611003101100d414080c1c0c42d240d03d1021410407400800611941c1510703404900100300050484040d40d0710700b100d4603540e000b80c8a03002c56180134007007000144001900810120b8003920b030100c7c40c607100d071014080102002d01c52543e8582a282d01c850200d810111a6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 930623039 1250 930621789 930621821
    0x711100c1703060108070e01022e11040f0b09030714040b090c030610080606030403080702070909050a060501050603060121110726070c0324020706060602010f060b0d02070501 77
    0x150103101c00120341c00c00c81d5000e00150b2890041550a409422000760020301a030103051025810840501d80020410b104009a950a140101104010300c40c40d204801066005584c0d0751800c21a202c20a1f225000021220410404070f45c0302d513000203100f000c0300d080c1c20b10340211070f031030100103401000c100b401d198108031088104425449010f0080d0304c20141224203140c6415041001c88203100126101c9421810410200b004030780190301c1d031540308515104550905072500c0b00c0b10182c41000c001216681e002c1003000b410042c007800741d180035007010303111340d0704600d400c20008101210545044030b408039180301c070044484031a0040a9509400c506e1140e694107185040c60022070700441030640c0c0075141c03a4410390003034120100c1d58004d4011440207102e0b070a58480c03120140110301908501c000940345a1368901040c0081d1992601039a8005503e41ca88940a42902d100130305601185190260512a002c0000c01b41c4218070060b450041c1c039408c1c01d282903401810300c003410326451 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 930624289 1250 930623039 930623063
    0x3190603060e0114130c1703040f0b04030204050a05091f0b031b040509010c17061f0201020d0501050108060102070e040c05120a140d120905070302060f0d0605060711100c 75
    0x40841500503d8080300c40810880300e41e507541e211780100740034000000346070090703480042121400d200840b403103058a840c01d407490103546a062401000d202c1e80300d480d0091b4045000c0003945400e200c0c440c1e00014610b4144018540710042640318000285041908100d10984400d1040c2681c0306103180000513003203400161101c0c4001d088a0114070846100c0c0f0708100000f04000b00601800d04c1441481c0c45914041d182d441c9a01b0024034001c0049400c403d80206a04d400c490000c3c1c1c0b8031821125400041c0e94056003140e8100790b500c140c11441c1031012410074815242d034009050380441e191b100c005000c58442d07240911001000b0380c0501d9020002e0541c20741c48200104444032050b01c11290040d400700e014000d2034580c0d040301d0780b07080411003e50030044000401d0b000244040c1c403c10980e001e29480341e0008220b43c12040c00380d041c0d964045012100360989101d541c1c040c00080340d00b07074100302c069951800c9035402190070301c1c0a000000c0482654500902c949154a98071003241c00b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 930625539 1250 930624289 930624311
    0xc0f0d021605010503090a120c05070b0f090d060f090f051516120b1018080a0c0909050f010905010605040c090806010303051b1506152a031c0905070f0b0319060306 72
    0x524404c3c100241c2d0b00380a02f42c0d00051200e49001129040d020045016081c41030070030821004c580310900c1601e1385600c0e400307010304407111031250800c0140308510100138070b4482d040140c60114042e410702421882c1b4000e001c1118040c00483c0c56844603407902c01c0c298071042440310081d20710022110b40000e4550052411140c000500070907a10291403e0013429030f070b034000c040d503c00144002401049480405020802c40b5400c000c0010380214200d82445500b80051801c44003076500c1912265174640c0c0c14011890f05000740d802600180c9040c0c03880c242820006078071003406100080a11000060040382217442d40c005498100302002900c24440074060881c000c5441200c0c03107403107076501b020307049070350801103041c0c411011000e4110207403415a03100709840101402800000ca100c00d10108100c12443c0751407443c0b1003040000403404013014a040351800c00c058000e1580c0c1c1c400c406051001d040301d007050341e500c0004a09414015403900440c071008252035000071b8800c0c1c1c144904040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 930626789 1250 930625539 930625547
    0xf0702040e0d03050723090a08060f0103140c0310020a090b0c010204030302122809090e0c13050f041205040b030705190906020d120209060c0f0d021605010503090a12 73
    0x7061290b0380c406010580c0c500313004032020b4203010100d01c807541c820381800c030300100b951001d00224a4050302c0013200c0c1e0340b95a03825140a208880ca040410013960040c020020720320011014800a51300074030021001c1c40000c4d44a840c664443d4120075804030326000c0c9640706032840c0303009100065100b41d6841100070494040d511a00095025110f0315040000700b00700d81e4200e40c40e41c8000d000d15000400b00f500342e800f02e03604c050519800c010000402103003e01461082002ca070940d02d004040030744d24036080c45490391395500003a45051a000c00c00081c0108110380e5540302e0b90140800e103503034500120580e054010364018941141c1d0102c02c1084c41c64200707000f401911414010f07031074141c2d0005000c175403142c007030300960005800c10768040030481c1c0a2400440040c4014101500301a02035012950b1034011109541083e408003200c045c1c90b01c0d0910480c58540810300c050b00b600c00d440d82402c0d20313a41c418490f02c1d040010010000745070031018050284c10079807150602c0d06080008600038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 930628039 1250 930626789 930626803
    0x703020604031a1003030c060c180807051906080105060c0102160602030916050a140102010b040f020301300b090a0f060e070506120c032505070c09090209010b0f0702040e 75
    0x4403480c2407400480c4032028503039913074411a90305694241c40a00b8030355900c1c014100e01a03a20060060501c0744185480e50380300140b000e04030f044001e0520510780b6041008040c05462058040054400d0a0082070b91002100f0305460094400380d54803a907040d100c40c02072007103440c00300341000788032046810400290015801340040400722248405014885e201c00d02c0030f481000e9100010700c4003042500c403081804c0009032030500001902d400c1c641e0100c0d0540e611800f410a04a90010050044400f80d09081070b10380003184035a170400e13220994016900380705100103002038119500041c40c40c0c0301003090740501766001c1880004502c40c0e240c00c002408442040f4074590285110119035420600144d4407103040920b280c40440c4ca410710b80c07041550002d001010926607106070600c1e4621000a0340f6500c1c0801c0e652640d481505082001c3e00d421142c02c000641c038145a812000341e80c0d00c0600c54191070522100c0d940d05d004a007016555486021402900301d0f0410aa0700020078000c1005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 930629289 1250 930628039 930628073
    0x50c09010338122b050c1005060a0b031006080f04030c03080c160f210206310506150f0d02010e01120c091701270c0906090e0d03021e030405070302060403 68
    0x80940c00e008015519800b0306c010074070307180c1d0000c1c0c15580f85601a0b00616001400035094003c3c454171001d8410055208582e5803a200e50350380e41c200f00c01580702064070b40c0000d045200f5941c0b810181d40c024643c0d5102c010250400c002c02002c5440200c0d18000c03a4070f04501904246501180c0303213015200c00d9440041591007611400310107500380054011202c540d61a5405800703c2c0e0b0740c0110300d804200305070020441c6041c240702500c0f82d1801c000800c48060f07014200414582c544400034030003a41000c4681401100720183c001503584175121500041039090030018203a180c00e100480d1184040840d03440c005003003001c8040c02a4001d211041036030500f40300c150304404004901402c1c0c1d14098425011205908042c100d2800ca901041d25590303c40d071180c18200350b441c104081074480c50340150711b99959941c05503040040c02c0024103246400d9040550030003403280c070900c0008080312503070310034403900000050030000309006175000303580c0c0200400c0d1216183e040904603c0c1d520381e00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 930630539 1250 930629289 930629353
    0x40c0e1609080619090503070503030403020f0f030901050a030c02250509060d02030a020d03050c1c11010e0c010c0602070f05070e0114060a11010f050c0901033812 72
    0x215020002145444c8600b1426a401c6030b000c05001148000f0b00b49520260303040d020a00c17680c0e0000300c00f440294011406a03005111000400c0b880304e08000003500b0b100d103654410844007213141d8110301a40c40041c4541030014800b15000d1080c0e003814110b6600d03007040348181e982404814007200c4c99900f41c40090392070400c02c0d0f80311b03028080e41c6081e000c030296042d80400c50080051424003001d4525520070f15020381091207000c111340c07602082c03001c050f080445003110408290342c07212082010728681c0c0000c1c000700395140446038075072101c10a550304025903601c0e08014003265804440c0102d6100d41c8440c8000d0301803c1031600d4442d18000c0c3d2184400001c00041c07039084d028284038100d94020070107451b1015020081d54413103569800340398030b075492b000880d0814400d0b01c1550700c1406400b0410b603442e420310f0001002c88a010030403001c44403580c01403401500312401c2000f5000700912a6000040c0124009400700c000e1002c11111482450721804501c50500d0500d400300c0c0c6500303c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 930631789 1250 930630539 930630557
    0x180306061802040302030712020a090203010e011406072d082215020606010c020114030f0f16081902070803090c01030f0903020c0f0a09020a08060a050f0d0605040c0e16 74
    0x41507000340d125622010f5410352100800340021010035034440c0c0c4445c40104120042641c600001d401da030403d900900540c01403000411208028080558080004480c0c841c40c06087e6920740004000100100c00d10345040c61a56100c80c3c62180945001c2c1c1e000b1076050340301d010144182e8254060b400c03050a400e1615600010412281e40c54100d1002040d00a03103099920b0702c004544a080d60007040e8100140b03502485103046102c0300450042005c078003107000130718208101982c022000751503109800c0000c0c01441d462a070182c100b58020000b10040703c00d0a0144148501034003a560000d03207101800400d11603601c200190034030345c114007038800f4440d6102c0d000342c1104550780d9120180150f001083c07210340628001203d1007820b0300051410300d100b03440f2080c0340d0403138110040700008940741d1401d01c00c50385481d03810440148030032128002011041000724030040810f1000416a80d11103020800300b01e140f4440001501800d40c007036002e4909800b21416004800741d050f80480c2c1550 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 930633039 1250 930631789 930631829
    0x4030f1104380604060503160e0d050109030e011412250c030e150414150f181020210406030f060e01060e060705121b0d1202090118030606 61
    0x401034404517080c9403202425030750f500416203980d040f010b42c00b1003080030311030440d081503943c1e00042c070040340140e000007804041e171b18020740710745000a46141440400704812448400760005c860b000c079500c01c944a05a1904554041c00917220311102c1002c50f01c4001c5c0c200941e500c0001c01c18024001e41d200c800e20107261041c4103d4040e0081c0703629009008000900040b0075103014440040300280c440f4200d1031800c80811500e81000c1081642c603040003d5189401d48405412001e100b011210041d110f0800d072350140c804803251901c0d00d0b2910318841000e040007020b01204c1c5640202d1003025801400d0803540d202550312501480001c04d14248541503e840c007072044000fa1040110302c480640d0800e03100b076904180d60040641e2003001048900001002446591950600c1000d03540e26000c1c8904a0b103244220035404c001d80342c0c0304200000d1102d901924100c40240900030060340d4a0507080100d80c540380d0030b030501c840d100703050030000b0803c00381e42d101d0f50464003c1c5004500d9050b40c0c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 930634289 1250 930633039 930633049
    0x40509060603210729040503040503100e0c010f120507050a0305090a17090a1d1005030f0303060d060b0306090d08010f03111005041715010b04030f110438 68
    0x10300c1c1c03920545805001043c0082c1c0e2000f00003117102d10088032284c103803400e0a143e000c5072004407002c070f84540001c2000c0016090402911403110030340c250130302414041281482d82d602c002000c490400c0fa0b10146000c0e141d0040046c00d181d502c2400e01807006c0e15000401420f290304c00c001041c002480d11001071000b02002c541800055030102a00b0001d412800f100130381c80d004003400c0365115100755000240b030140b200f9115810918009400e1961070403006c0d885c601c041c1307a4059170007504014011000c4c1032020040740e6000301d013202ca28040202e54100440244080101c00742c01d8400e8405000b5401d0740040c40b000480c01d199680d151982e00c1d00140301080340c0c1c5200c01441e850000480f16030038601050003a070601110b150040c24103940d51200200803803460101922600017820034060300c1400700e041400b42c0070f405141881e1074a155599407920380c45040c081d0600030700103801622503455401074110315224480070115800e9400c00828404259444c4000040d03030755800c0340c140d00307003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 930635539 1250 930634289 930634333
    0x3052b08040b060d051e06011e06090b031005101d0a0b04090e03070605010b03090601140a03060c09030501110c0114060d02061b0304060f020d020721030c02040509060603 75
    0xc0311009034243d440d03ca0600c039154107040400c480c0c1d800b0390404200e9616140d50448061500407005060035490081e03c14191118060b01014441540758240403441d00444d00800310f410b070142003a500d554800b251013030781000d600040d5002c1c1002c0080c60b0115888682c0310f1b401d007011408580c10028a4042050704010b6106050003403c0900c02000441160b1307004110441400c4140c0345488003da842e0340480300d007600510583c00000c000d000301d0030000c110007070150000410300d40700c002d1580000b03a1401071510000301000d4580112a001c58030480281c13000b1540300303009001182d4a0580322090b82c002c1d03040c100480d0b02e00440c40c1039100c012039030680944800391002d01c0560380e030740a001c4603510481c0c8a80741544c0e5410460444001040188020106580c50703041030040c07010003d0900403c60800e00841d84681d0043c002e41d2002d040e0b050b025a44403616150310586c03450240d508030480100691301c0341c07130001003150100010074039900c1403000701d0aa0300d00060242c1508075501d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 930636789 1250 930635539 930635543
    0xc0f0d0b01030f1e09141905100209030a1106190e010f14090411040308030f04060507081b0a030b060706090b060102032b1d0106030b090d080c0901050403052b0804 72
    0x9413600030300c403020441d030f881055220301030400c2e00428481070300c0141c40d03c43c4010003130380e59400d8254020203011090020311400504a80190b1800c60600000f0750303242170101001c1e1401d8102d02d40c01c91295a08001c4503c2d00d902c0078039214a9140c01080500540b0050310410301040c035010280148070f120350b414110ba11040030b202030528444905220080070143ca0603405c2030010000400401c5a000186200f41c040740f14820251a01d0b1400c1c3d400e64401038900c13028446840280140301d001d200c1040c028102c0c5001c1d26460381e2903400c0c00c070040c0138101100e68002c000001c00070240012908261104c074020030b600c1002c3c0d200d141c01265a03106200300341003004481d103d9a030040603002c83d56100300407595004900b4040340ea03e48124010400710558190307640303040c1001008000750340325034005580700c05006442803039600038141250040c8118000e41002a41181d568000c2040da405190040704441641c0b4101c101003244d021802d0003c440c130000340120101040c0316101c4544201c1d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 930638039 1250 930636789 930636821
    0x12251706160323040618030806190909050703170c030d112a010c0509010c0b090a0b0115110307020f190e09010207030e0d0b0f0c0f0d0b01030f 63
    0x9a6505180101c504800c0c0d000c108258980d001a40950444048a1140118206200400c2c00c103403800000312542e425111244914424800380420740042c1610380c0400c040d01d00340c008699895540c1d201101940008100c1841d01c88900203002d00003d800c01580c2c81901d210004101b401c1080c4500d004003040e0701013aa00410900000d8441c41d0001d00d004014440040c1c01c0032001240358460400d2440c02c0c03510400240044001010309005091410034070342003561800200800090008020a40251514100c203000c036498a0013084034440058202000a83e42e58680c851203c1748055049903800107103442c41c2c040e2401c14040f007250f980e25130007041a40c2c0601020203000c20040c0700314070b02c41210b003c1d580c00180148030100c0d80c0d20030310300e00340016568142481e001d0954104014910300540001d1184000940b1010030307150090407400d0150342a03170394103216405c0d03441951001900d00101060003e516000e940102c80904001d0302c3c00e2114070036004c8072004035030710414140894 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 930639289 1250 930638039 930638041
    0xf060e04080a020a080f090102010b0405070504090e0a0c081c0905030a0f050313030c0501020d031a04051008010c0906080915040b2707080705060c0a02060912251706 73
    0x58103040040502d5500b60056407442d442d00e448404c40c1e80c104480b00945480c000a56a0b220343c0c3c28802c0b98092442254200702604019800406074021800340c21003250b40c490641c55050303000c01902d92110390200b66151480d48400e0f0a0f602c440da81020a0405410700d06c0034461940a101e00700150f50005c2d0080c100307142c4540710301c4d400d100e07040c000f1780702c134001000007541d61000034000788007940c0280a1401e1a0780b408000a26100d1760b44c5c045000c06251450402c110b5003284405001e5900c112004a550303202d8119080e2000c00f0380d44000229860101c003106404e8002002c0310881d1030390340b01e58246944013003079a612040b011016142005505000500050318174107400d802448a044601c11005102d10030381c150110071800910540c4a801c082000c0c2004105550140005907005824a04c0a1a01960340c989610009100c0ea6012400c140e01d03071205040342c1402d417050360450301c20b80f0302c10709032700c0b0504480540582d0030102000d0102d444884080a03112200e0403c008003c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 930640539 1250 930639289 930639293
    0xf11180114070506180d0e0904080703091806050411030717040c050d051f020f0706050a0b0a1502010b0603060109050108060a090e07060801050d0b1303030f0518010f060e04 76
    0x201d0741c100c41c840098030600b480242d01046042000324403c00d403413018900e80e04101c4402c5450550805111030401190700310840154586504040d0496808401d40741c50b0320340c0f4501a076944000340c1168042e0a42c41b8005c0840c80d0f0550854011640d00380ca04210b160036000b013260444c801100d545010519001c010781002000008280d440350140002010045c3c640c80015118070131082e05540603404160b03a2208515140400c1c0e0088091290441c0fa01e815001d0f981107c0c01450300c094441640c6000007261103601e40c101e0000030000404c00b0880e1a01c49020300350401c140b0b00c1102c01980fa200d40c400b000d06094003240d0207600161600000945084011180540000c0c0701c603401c101c0300400080e0202c0c480c01030214400140c0040c2a2171424400000c2c400c801c141c3c4424441e44040c5405000725400c0e08103950812100320403d01003d10a081c103501031301d91041414140303803400c0b081002041d03002291048410070040207016881c1400e12440541c0e40c1070151981c280102804100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 930641789 1250 930640539 930640547
    0x2250617060a030c172b2001060303050a02010c0206061f030207080309060601170f07030e0a050d1805182a04030b06090a09170f07150f111801 63
    0x540504001e050b00d2405071281d5400503c442264450300070f100d030150814605020900102c1a0120341d00d00403602031015034202d50a040d4a40215003d2106a0084000d416221300c86641109038030f030001d1280365920701d40104158085021440154a0200c900750784d64404202d10b4021580204040343c44600710310040c124880341c3c0c1d000c0c400e0640c20005003001a0346000514403851003000504900d252140003d0540c86480d021061480050820005400c0084280541082e0b852400198000460412034a8140d4104018000744188043ea580290348248801d40205c4264001500b980c1d651050008083c04050100c4026081900185803034110f000b0346443c031068180b102d000c03000a115091684c0d48a6041601d45c003810a08000e181e042c017000da02d4010a281c1010441a0300c6504c0e554500d50203400c801014007000120320340082e00200c19200080e400c02d290490301c1c030242c2c0450f0018030300d44880402c21030404004443c3c6201c480259402201c2100b045050b0317183c040c1c011a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 930643039 1250 930641789 930641791
    0x50a0e0f011b081b0a0b04150e10051501031a0928020415050f0a0e270105040e0706140a051b0d08180d0819050702250617 54
    0x15040001c00256041401c2c4012100300046000c0e4070710958881404480303400e00400303204150020341c45020f800c0c000440c904182d5070f10035080304a84c401114004140000f400b00c20000100c94031070845c180e401c101c0140d04c058003072800744a445c10443c1e000c00042d81662109000c45000c1601d10424154509001e06207a601c24031401708031040400094041d0030380c82c01314019005d040d5002c0741c20312606800d5084500003030403506019040442c00040c0c1000c611401c0d007014100032611884407090b446280c1402000c1c03800b00e07004142d501c42d55018000020091040c503110328140004000f00c1a40810004142d032003030341e00c0041c00304610180315001c0d405800030104106080280c007450098111481c0380da9003500000d0240c00d080500020160307170000e42141c604500c0e80003c0f86e240c0310b00054400d0360703c03e5402d00f0100d03030769501c003602198100024100704aa05101c1003041d80d40d4045012a02c003450110252a83d40c00003030718210704841030141a01040300c0d48015030103581c83c0d058071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 930644289 1250 930643039 930643069
    0x1b2a03050706061509060f03150311030a06020309011514032a040207060606020c09090706030917070f03080f0f071b0c0605090a0b090d020910150e040606050a0e 71
    0x454819951003200300544c414503680c0700002c011800600500d9800403034070b104405a8501400034403442d01404541504d40d1200500310007810075403039550303201441541151174000d0011901c070701d0403543c40340c042c15486403207a40007010a5000b0032403200c16030801544201c0030740200140001020b0120f684004101460400c030200e032010480c03503a03240001c11a442c4107005c085400e52410340c003e481c181266903001c3c803400747c810402c80c0f03401e070000d403c9044030b81d14500801c2518548c188102c0301082507200c0401103038006a19003d00401a0040406600c03a549800c0c0c29601e880031001c400b00242d4003414001442c6d00820059841106252009400c00c040c40d0441421583c42040c011215032050300880c070042642c2e416486e0114861000b07041d4a18480d14164510300001c2c040140d00710000c0c42148a6404a0b510201d00f103a8080a0710a0141d00d2098104401c4c0141c000b0019041291140341000008580700384a001919000c0c6d0380358036511070301c075080c1003000400c809150032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 930645539 1250 930644289 930644291
    0xa080a0c031b0f11010507121404031502030f01150509092215060909020102030405150909040305030103210806010c032307021203040b03070309060f1b2a03050706 72
    0x114214400708491641c01c1c8210200201d0440c0b902c0c084c0124000c03000640e044c40010720a280c0401d44448031000d03204094580608440c0c1e9480c0c031b00b103050286800c050081c800c19a17004020005c82da000318060141c1800c101c002e070b030381d42e40c00308604000480c1d54030010708140016411420020034064000d042d43d480c101c0d2079000b510311811450012001680c0200840c29000f90109061080314043c0c0031030300c010706c0003035032640020b942c0740b05500c00c05001e500345280610421081d8030580c1e14031003000701220001e04041c04d0041c1b1301c1c2c00c00e0201340c0e440c48002444140c12180e00010030032a01072500e4400d50341d55501b00549002134a0300702a02402070070500c001034000840089403a01200714882a103560182c01030041c0c0300e40f0b401954a16a0040009104814030501541d52080c000d01d0003103018010343c80c140c1b001e0005103a0501300c8608084003000c0da07801503048101100d80e590b4684a0741e41261149004c6c00300f00c000c1025804c2c200300c621101191158000300f00d11805250 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 930646789 1250 930645539 930645557
    0xb04091a060406050d03181401090608090a06090803040c0914221e1401060f0b0a1e090e0f160e040902120303040308010605120a020912060c031006020a080a0c03 71
    0xb01040036950f5081080700040c20f0440c8004201120511101c050000000c40c908c1c034400604c00070341607009a00401003840b0060300041c1c82c2c450300304040304486a1000007409902401e250440154000391801c0b03405104203900440c11401e103118407050074541a04e011402c1d158459503112298000300c1985024100c08503000101e80b9181c428011381e0700882950a00755090300300b0801130035011840d8841030741404010020b1a010700d04c01e900791070803a421107664214000c020f4925a44100091000d80c00d0110310203119600600003500b2103040308020000c581c4ea1505640786458115102040c0445803440412014450b0421021804d00038000007560003040d0000f46089200c40e09540150340004100000c0550049500340184a80e08196080c440d075045400d109440c000c003061340741503010840b00c00170341d0740001100d440d50380e0310b094510b41d05004045445076071040340e8101d0310411200000070034a10000e50444066040464542402003002045030806001c803c25130800c05402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 930648039 1250 930646789 930646799
    0x20d081b0901351e0606041e03050105010f1715010303030c0912060c1b0c060507060204210314120c07060e0d0804030912020609011404120804090b04091a060406 71
    0x52982034500304440315043c240c03070400c1000c0c990805000040e442c0c0050042440b105c0d444582c19134003600e14080342e840610310f0720580c480c020500395002411946c00c0c1000001c0079551555203209071403408034140e4501030b6101c2070503541c0e1401c2c044845070507103500040010a10035400081c000040d8907044845543d2140d0f250006c008100e025100c0c5a030341d4403500683e6401001042d801c103861a000342c00c40e1401c0e1a10700185003c0d00c108018000c0000b0b00c4800c22410398100e0f40982002030701030b48407201c07803815042c0c40031007520214003041d0840c0001070f031a541d13071041d180090041d0800c020242d031a44100e0226400005c000c480140c1c45007512261502c05200d6244142e440383d4032020340b8a091f04005104402540c04030028200480e20b40c00541c4800003220603603442030802c02101d10302544000c0d024411684482c01800c0382c83c1c906010400024024000c4405002d02070201e0402002080122240c2e800c00520041c55040401c0c41540781c00c0000da84007000800018804e6920 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 930649289 1250 930648039 930648107
    0x506150a020303010e0a09080703080c090607060e0d050309100b0d0533010509220c14040509030f070f060605100c050d2307170a020d081b0901 63
    0x81030400d02681000c03006018880d405280c00c0d500c0049000b0500ca124001d0312283c1c2d2911803410082d0400401c940003c3c0b401c84810200d07540007001800343e5640c0c01150500780c004003980c1c0000b002034041c0c41a01190030707205000b41c9010300d008402524280c4425040a802440303090031968000e4008501c80b4007250081c804641144200180342ca8144421000000c100ba000d00c0984000c51100703005100c60f0700c2e203213029a482102e070024252004504913a943c20080c4510000341850401100403c1c0e00c0c01520031451603207410f40d000d200d0fa4651005c6c0b541c13680a49584d0040719581441701c0e0010170220082d2104a900559000540c1602c4d43c0c04104002240c1040d071010a1280307058a040000401500c032007122145411804085582d90040310b0ba00ca580b40030440d00380100340341007030000354644005191901c110169a60321203c0c00039454400c0d884415020503100c41c009411950140120300800f84048010ba281c283e00d0b8005580c04020240604507003480355400180b00848 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 930650539 1250 930649289 930649297
    0x3904030804050a0902040b0a050306010e0405190b09010510052107021b04020a09030335040201031410030609032c030105070507020105030109052a07030207050a1206050615 76
    0x1000450740d181c0c202010b01007102c0d80c540c00303c0c05451040004001c0ca040b26410f58811230304601c1c1c0207980fa1140001251402200c3c1c00459006240c0b0080c804158110002c03000c2d418a929418000e032a640010088005024420385401040030182e00b0842485000109924641803860f8039003410840c003241c0c500d0b4011034803000035900081c0d15401c0d43c0d405000d840102c2000303c4096203440a00000200608458400107041c040483c0707046c012550007465000d025070004103010041d0b62946240110094192401d80c04203181c025040c0010000018441c03240c80c0f44000d606845140d036580e08001c0c800c002d41a0700304240416841c160a000001940b0b00c07400d60040d0800d810452130800d401c5840c080e211005100041140b0300041c0d070458162030464403690300010305c0f5500c020001c521003000301c400c0d2250440b031000c4c1c0d040c4013400001400d0080d010707500b02e0326440d4541d010f0182103156801000119210102428000b5401c0d8010340c0d032180d8003800d1321940029050b00c072803007904 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 930651789 1250 930650539 930650543
    0x30a1404031112030106230d09051b0a030506041b0306050c070309170c0f150a050d0605040203270f0d05070303050c0a050f030411270f390403 63
    0x16016444801e0b948104a0415010b044010607455135141c00c50140100500034581d00c810020403101d640403100300070a8855521600e5018081c850325403a0440d00c40011012225020144030b13180c0e140c908041c210031050320740c8200201310720348550702ca1250b128100491801a0002814040000340740c0c1e001d030b50b00440403d45150b481d120286000380c10b044082e081004141ea00d01c001d40480c400008951200c044281c3d1240c210560090214100c1941c4600c801c6026900003000b02c1e48541c044004c000280424004100e0140c9036420401a4482501d4500e120010304e0318102c1d0940d50b41440c034400b650402c0803a038800c5054082c403420b14040d8071510021490204488051507018022150301c0500440d00340d1610f003c3c0c0c80301402a0154420250001802000040420a00c010498482640200320149542c8142815070400c010912911f00e100c20120104085450030b2031094080c01e411300504011000703074005100341580c528040c0c0482010440480045500c140c003c1c00554 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 930653039 1250 930651789 930651797
    0xa020409060b1902010e0c0f010210060e060117040c051e0307060305061c021807050f1309140732180306010e07050319020903011d0d030e12030a140403 67
    0x26801101c20109074880c3c110f10559040501440d021303030f40031400860f002c0341152544803121203d03004034501840380c100c01c9440d6181000214441281d20100c0e440380c002641d880030002d500003111400421b0a80d0024403a8034215028030180c9022030301042c80d90001c02c881440004500002407a01d1056404140480c0d5604140030b00e0741000801d00e001890340312104440d241c0e05601080580c0f140b0340560381e030000150042030b9030612510880701442c00d0811082d484041010a007188010144034080c0103a1802d42440300480d030315506544120800e13103800702150700040c002c4c101840c031a08144900c008110b0b14a000107184000b920140503d2100180d01c0d242e0321040c10318180d0306800000c00d00304d6803c104501c0c25800802c885e0302030006e59050041602008a120180c010b0f005c4036a41942084544690410f081885101101030b0900721101d003801c25800790100c2c1d4095025441d00d0308055440b03036921803881300854002c0402000010030710300c03110400d69031043c2511300b10002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 930654289 1250 930653039 930653047
    0x608041a0f07030501090c0e0d02030c180105010f2a170f0705011107150b030a1505250e06091c05060a0b06030c0702010e03070503060a0c1107030206120a020409060b 73
    0x42c65241c03003414050000d2000c200040e844e01d40000c0e010312030540c034580c8141004a49a811902c05000c401504070740039201e8185c25140c2103803040b00c540d00340142400141144000f0101d184220390001c41e007144245242c45400700d02c400d0b000145100b09040c0c420b1200c4c146d005040c010010014000f0010040440d622501e081c501182500c80d1070110409041050040c400451001098400410107103840040c2c42209400441e0130841000c101401301400d0920002903490300c1e4010510075000666000303131040000031481c00544406c0380050001c2c00281c1d030503c003070820760002d000145005046e903402d100e02080751038200a4071641292603800820900000000d00d00881100400441d4254218070340600c03020308030b024140d000b904101442200e094940c0303081c000100035002c00f5013607440e14070f0006142c0000e41400700ca0f01000603940a0f40081340c04004c035418017a02d078002c4c50765280c100f640c404110722000c007070002d4509540c00c01000800307096038840c11006080704012031b600c0d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 930655539 1250 930654289 930654301
    0x6161b0f0b071121040e3105100c02060a20160c0b040303081924080c01090815071e02060a05060103020c070504020c19110a0512070608041a0f 63
    0x140484d6030341040c1441980d20481801c19010420743d41929102e0240a80c5683d43e03d48542c00c0040d241c40e401f0658140560444125070740c6001c0c0c001190155044442800101115030201c562410401006030008400700f1004c0e80035400081c070280d08800750403c075881046500c0010f9110f00320302a00482c0d401031200801006401413402882c414090600313041c59a10040c2861100429149400c0115042c1c281c60300296404401441400780c803002480314031040c2c507030003012035000301c50311441203424100c034a6228013906c109440060003e00003d00103481110700184028145a050009000d07200e42601c1c1c240e1141700e40c2c3c03059a4020525800c0040b00f0700119a806045641014010032240303070000030002301c00c811190107071401a95240281c44050408060900701510040c0c500152401d00c0811038001c000c0d1042210b4464049503940200010896545100311483d08640c908000850040c9040d5900c0707400f549c0c01602544840e0350b42c0d0f2003d40121582840500c00e4000c0c005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 930656789 1250 930655539 930655543
    0x50f061b0d080c0301080613060212102306122701051f030305090108040804120f050c0607050a120c0f0317011a09093606161b0f0b0711 60
    0x600030b03c240b42038614550401d00882e40310381c0c0007410303174075000c0c608407a0908100d010780c1120310300c0c000c03020094814100744444028400c0c01d4030030405900300000c030f00305d40c0d904808409011071000800042ca0b10340c0800442240480c000c140d80308003120151900d2100c3e41d0303107030f10000180e04600005200d1070201e00070f010608a070844603103050101c003404e20009801c00100d6075840c00c02d0800002e542e440d071800d500d00d4403490704030303030000c8a480d02a4000c00010050300c04260348034100741c40f0700c219024180880c5000303400340a4426800401180082046a041000a020300d40b0b0210b44075001500c0d001d40035103201314101c0c0002c1c016400c050050104410761380c05481450001c0c040080042e81517200d42c041d0003d072511400040d00480d600c110060140120342068900c0e1500b82441f09a041144001082e91400c0500441d40069609540c0721134104019a890321007255075010524600d80301c18071902c040b41c9115400c0e1810f008941282e032201d00c110841d070350364051401d00c00c602e14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 930658039 1250 930656789 930656791
    0x3010c0f020f010506011202030a1b11330703090516090e0f0717010e0d0206041208040209011a090915010210021312021915090b0304030207050f061b0d08 68
    0x1050b00d0b490a420b001051b80c1c801261746034240242009600d80d00c410011000070802d0034180020344400408000303150350030600c511070395458003042d582c400e003d81e01e8074800c120b5445010f810306c5510303d40042c080c600d501c4615800ca10a441c0c00100d000d0b26039103041c640020484c00a80340c4249101c01c0200794894040d07848481040001b90100c0010a40901e6540b801405181240c06038862902c1c0b01d41c03800d50010101131200e00807a03950400344a00a510f80605aa0640390600e01e50540c407030307181c001c0741907901941d400b40c100110b9a203042100e0800384040760707401c083d0400400c80322203d56903040350380c0e00030982c944c1c084a520329800c3c00a4a03101c00b548861000900620080702007040c0141c00004440c0070190345003c801441c80000c10070748181c3d038541d2411000f500b000c80d104c070901c061001c065034151105400c0c907494400d0300000e800100c90007001603001d1181031045e401d01060860f802c0d003010b0009401d06100d2586080b041d0707000c14030030070103a010811801081c0da000c1d0f112 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 930659289 1250 930658039 930658063
    0x1a0310080c0904060c260a0c0c05030f160803041407081b1507020a09050708010f150c0206040807171912080603071a030402010e0f240903010c0f02 65
    0x74641c011a0401180030100010405003625690706409021203008030421819141920580c03074061010118150f40d141007600c40340e000900d00089070040b1800741a08401e103541100055051074400006100c55902c000440060a080b00d0a0103000a40c0070015500540c81400342d0f038003800000d1095482c02c2c959034002c050350350204042040020881c42c201c00c0524040d42c40032041d541c0c0c1101c0340380c07903c9249030094100505d200009040b09041e40407038000c0020f99240e11059aa500f10012481c02ca40900508040ca85650103030241c012248030111728409010a800c20340c0e24000745003410303203584c400411444c92158244001800f4009115465042d581c00080740d07141e070300c03104445511b4280000a100000010035140d6608103e90340082c903030749903440780240c0c2d00010b800040d00283c0c0c08078089030030f603104c0c207a13540b07084048039542c40009043d40c81040701808810000c41c9030404041d100302c01c01c001c0d09030070f80c03028040c0004181082d110480030030183d04009252a1104180b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 930660539 1250 930659289 930659293
    0x6050d06140708011a07080c120a0e371a070501050a02120601050318011503110409110609010e060406092c04240504210806030303040f03091a031008 66
    0x5000203501c010b502500344c5d4100354070903103482c00b6161000030352044610b907100902c0b07101440c014040741d40e001400c0001565aa02a00d0302e203034070a0101502c203030000003246c20042c030013007805540c40380d1001c080700d2092480107800e50750300c02d025103121641048080c80c0060005d044c10134000c0c00d000d1617810180043c0c04501d05403c011110004c00070151a05042240010215001c840e0301c0d16500c40310340c14500200011000701c0800600441c2a02c0300300e0300089603038002041482c19100301c810054005c0010075401e9205004c015140d1b00503070300d1074107000c548100c0c1c005540310300c0050006005652921a0084d003481c008080100d07a9801c142c401004203503521140e45010703151507030059032044018a04801c01300c920309005100c04001d2088a19000c104400d00ca1146411996003010042404600074a5101114a804100e881c41e0b015402000480c0001c0d2041103801e100324040d15022219989031110f00020300d84031b4898030315401003c0107201cac00b0700b2000001c800800031800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 930661789 1250 930660539 930660541
    0x7020d080108070504111b0102070b0a0b01080a15030c1d09030708040909020105090301090b060112020a020c121e012a0c0b041401020d090605130c090504050106050d06140708 77
    0x2c4840d40e0358102c1c003803140211744803100b145024800c517081d074450f40c0c3c811200415404154646a000b50043d00098070030981d5039009c81c030706401c0d622454100110681d00c50000c2c0da10004040080c03c3c5580b0901c2c0959896800000400c0c0502d0f1a840908440c00506c141811511420b01c50030001500b41c1d8138a4004120080c000b410040483e03040b1030704d00c500030610821600040e00c003400703030820064165003007044c0c0604200041c5509441030f0b1090725402680e140c0070741070f80101d0141c0e107021000759100390308000796840c007210b0016400700500100c80d204c0160001034500940070782c090a1190303446011068070000d40c484007204895440402600b2481c0102009201006000d005045000110046800c1c130802c0d43c4051000c4215100075076075107880150500061204a80036a40700340781c0008112503c9600130440f6550740c0000d084035803107080103516001040c011b4402c944d0b030340d40c83d2400102ea446680b40642864011000028000c24043c2083c0d13002c28018580c10070080084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 930663039 1250 930661789 930661799
    0xa030302190519180f06020309040f060b0d0f0f020c210a09050d17030c04140a1518030f0b0403081f120203030909010b03041403211e090607020d0801 66
    0x10000461244041c0344c80f41d00841200d1001289a02580081c034803160b1040020601640002c018049114213480c104500c0c1c0c10302407802c042315520700030f4001030300b07041080e0002900e1540110041071540c10000900e10301507001c0c20102d078407101402c03109802140c4803902e40301c0d442282c8801504c00441147c07404c942c41304002c0c12203505000315445629110071020911024900c80c80700140a211819a281010707031100505400074401c246003c1181089000c09003050b1a031301d0200d903890008040310041e81c1d4410345111400c1e281c1b00c0c0030f2251080700000441c2521349804003160081c3c03200c1c4140c0c103007400c004204180003040c90b8144000854850302c1c03605089410310894030030009104202c1020b20009045220b1b40060b907500c88500707000829004011002103000c0d5200c1c5039a10740341809804a65141c1c01090850b50000c0e03400743c1407040c04c6021414a60b407001f5107908103080c05d904455184c8981d9415104400a940090104047e050b01000950802003c50034501c00030343c500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 930664289 1250 930663039 930663067
    0x105070804030f020a12093305090d2f030c030c060913140603010b150319060e18062a0a110d120c050301141009080a0303021905 57
    0x41d0000341000407408009010324820302182e901581d00403c840c1a0440500000f81840c0a5009840003541e403002800350039008181070b03c103640e1241480f03001c041d904840544554101e01680e941011040c224580091940480d00c03010845828a0080c002c004001141074440c640340301c02d010b81d011104035041682c0004212100c074500300c5100c0d0f03403508002c001c51250112011404081800c2031540c1c21380042d502402c80c420101580204500d541000822400c501c1184403002e004108001081580007040c1c0c035080200541007002c40d101d0f6842c850500142400c4a00c1c10301c5120f940c1d00110392100a01c40d0b1174020f43c1c09040800346901c00328100f406605c078521240c508500000780f24104a010303ca84e042c8101440e02510200d011102020304817440d0f248840118924101403d40014061400d80c0c2c10303640c000d0444440c81c0c0d820f1083c04081c2d41c03c00c4240741400014200010a01c40c204242403070140300759805a103800d0600380105200c05c811003540180310052014800396082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 930665539 1250 930664289 930664291
    0x12050d03111206030c130905160308030a0b031504111201050c0d090501060816080d030225050114010f0e0604020f07150e06010b121510030c12020c0c030f01050708 72
    0x1c0300542d103500ea151000001d26044040140a8010303191228101070b141c1d0382c0c0c0c02800310754003501c10b84103034419903802424444040e01005208090600c00300307000030760603400118400301c003500300c4011034040106009038200446040701c01403034080c459005401c1032502800e0840068000384924103006010103114080d0003564490990350f40c0001050040940151000300445400c3e00d04007540220300d441104140e01644035148148050340b55003070f10034401c0740e01d241c05262041598058051800d9081d69180728240d480e507407103504044603611035010b0540240648141036049910b0501d00701000305000300514411441400b404010a2102088075142580300c4c0c8401c641e5080c041c1160010110b8401c0c8213000d115079000414464084802449400001103d8070101d070348400114018103000e405e6603411071001d2185200302c50180c0c0200061000c01d06204880d03110030400c0500700c1e081a28480380d19400140c40c0101c0e420b041c05200e50780d0520301c000340010300c1c29070b1001d0f20220f4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 930666789 1250 930665539 930665557
    0xa120903050109210e013603051e07060206060f010c05060c1e1c110706140a14151005040e13060506011716050408010e0c3309010203090a12050d0311 66
    0x5c284c41c01200c008442d0500c0c2003a110311041f540000d140c8905142d95541c26540501030300d040e010b58800f004030800158402100c5803640101602d980c0e62050000c045c2950883c0d50500400c04c0c11040052401e1284604c40c000d45401c10b07484172550024241120300c100d014030f641210802003078094480d40051414034240e9200c0202d500900c85c50008030302e109172100a002140f03004480c0c2e014041115405005140000e403d000081c11082030b00d080500c02e882100c41c1c11604a42c00e0701c0e0f410121035080710318003941451410640c0d1004545d0350314004441c00180001c3d00141c0b0b400f0010070384600da81254003807810605449d0607500042d80c01c8030141007048a0386036080a182e1482c0320b04200c5003d041c030400280502c1c80c048030065914080e40211910821411034110031000c1003403084d030030719500d1103001c981c0254800441e10607036100300c0780d06045002c208414440c5071140410007000348001048030500000da4180349080c00b1280b03054004041c14002e03034100ca00407940503148060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 930668039 1250 930666789 930666827
    0xf2202211b0a0f170307020603040b0103061a0d0303050601110f0609120c0304140319030302120f06010c0602180d0f0c060203090612100e0c0a1d030a120903050109210e01 75
    0x800c0c00852403030f6000f20300b0000c8d800b140000800003000441110039040301c0c410307801404510a11f45200480f0488450b086800503050010100400d10a8004903009003041c14814040000002001d04043c104203c4156030390080c002d000300c1d1a0200545464a18081800c5d400e10042d03038901600c900c514490010350000315a800c1006036030030b00000410103000f08102054181d1490701a0281d04210705603400c0281c5400003031107214014100ca03115450581da0403071020750650384d250003500080c04801400100000100c456194100ca8010040c054121b04d9100859880c1c020700440068104008540040c0004143d0707881d0a81a1550401031003203043c070315130380d103000c04815003801d6101402c1107499800b031040b084111f2000703149902c8a40d030b074001507000c41c8218150341d002c4505e0b102d408d5888003082001141c80988204800003462402680c0c66940751150307402d41d81c20701c1d400e45411142019200110162281e039001c0b079002c3c2d0403d50034400d02180041c10030400010805598 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 930669289 1250 930668039 930668069
    0x10e06180d06020415030905100b03060a1e090f0b01090b061902030c0601031506091104150507080304060f0e0c090403111f140f2202211b0a0f 63
    0x400b40d010760b405818a0303a00818040d040c2100100900340e8400181c449014950900707030b6a1080b07009180314180080c2c02002e29403a00c2e0528001011010f0000c1000c0e00c0304440d01183c50300900075200c1e214000c9103010507002c1075050030000c98506a0100904034508074010480d603da41e0107407190130030301c041e651200010f00d103c02e0f801d502c00c1c4002400e080c003072640040104a020700d01a407034807808a44c00c10080d521a10694115050051420390041c030030300c800c100200c3ca10f10380c3c03240600c0601d00316060500b03680e54440d881e001540d089400a40b00c041110882131710340f080d0468100c81000801d0203030380082c0030801d003100142002d0100b01404084180c0120100441c080920034180140e004221705101407004214180301203d80c60101070204080d40f844601c00750245551040c1001c11948120420241207a03100080360010407002c40c0504031681c080011000c5501c06028203103c200e084540c20740741038183e1615120b81c0400405124440d4840c0d5000c0544038552824148 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 930670539 1250 930669289 930669293
    0x130b0705090612070804150b01021b01180e01052d010e0a15080a0b1017040f0b0a0902040c020d020d0c050f06010b0a0f0f080a091505090309010e06180d 67
    0x158440c00c05688407070940c4a05100c1501e40c4108014886d90017904000044141a00080309075007409240a00503440311400124808100d170005021540c14108400c240725020307a0440d032010154040d03801080358038010843c0781491108002c52044144141c035080602c0101500c000c2400d54003141041001e082c540500d494620f142e0000d442d007003e18114610349848000d0a28504554031004070b420070701c4000040c2820403040c0d20300c15060b01d400d002c00983d208001480c010041c0203942a84108101d0703000b11b41c03414241401441e03c50707004286001c8078010b100540e8002c07202c4100711342c04008015403456001c22402e00d800039500c1c100e041c1d90401d040080c0340078005098600c03c0c0c090f540000483c110600300030280c40c29240c03103100701c545411a05407007001b0094008804603080d8000106002c03560b03070120710024807a034001d04c09803002021100450750201e980601540c00011a50f00c2580c1001c0b86140d0708004442861908260802d01000022144851380c040c0b140e03081c058003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 930671789 1250 930670539 930670549
    0x510090902030907090518011d0a020108040302010f021303030323150402070203031b1c05030f060d2414011d2d01320909070f0305070e130b070509 65
    0x3020b0205c418401030418072032500c00812030f125840c4c0c0d40c2d0710785070241c4a801c041541e01103d00c02ea14000c1c080040144d001901c00c040001c00c11030840d540c50f00c107e004210f49202600c2c143c480420300000c1181549006030803951110300c4680d8540c00b80c61404481c03959106080d071300c405100c89540c03402c5440d5010901034003c00724025450b001c04100001629030250490b8602d5083d0b9003150442e800004450648008082040707001490030000141100c14184151b908550080c10b000300c54600e41d140d00c40c851035a030004200e520711216110058115500030248180c1c141d184031b4076903500d0402c0f0344e42d81070320003400315900411490010f010b9052100303170100001c00c83c1101c4941401d8803440c0c0e0060000034001d00c4200501c24000401c0c50200c011004403000340d54a004400c01036900c104028032a00a2210147d8411004041441c100e000c102c40700444c8160000d1071964281605202d0030700b401001c1c0b5541c0c1c4000c0f0351100c080303a0511a103d8010b078047c1403081e65041e500700418 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 930673039 1250 930671789 930671803
    0x10e01290d1107081206060f07120e03060f070f141209010902190504050c09061210050307180c17070507060912210e1b0d06060b1305100909020309 65
    0x301a0342c0301046036800e02c0b01c00c200412040c2d0700341c580140503595076000c0000c0360080f05a400420542807000c1c01c0019040c0d00151005c45003400d0065032584400700003441c210049482040012100080c0a022074115200812102c505d051047c001c40c88404280c030b00b4000d650390081c01e028010040391001d0790a40c003050300300e0340103000021007041e101d070303000c4002d4010720440d030060b8a0100040c00300c51141d0241d07208144003d0050740b90584581e90b44080000240401704100b100700c400043d288d4007046183c005240117100c8141280301c1c0d030040811241a1500201800b0020740000480400e002c0c0065204a441c2442ca07201c002a050020003820241d000808030300348407100080964111302d54208041386105100705c1c06000b08044001e03140308421440c2540d0084624180c81203441d11584401000070b0045a00b207a4242c9a03142510f003d580f00342540d400c00a14048289003076a0010050201039a000150300705850000309410300903c5060f41281d40172000c904521003c1c8458 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 930674289 1250 930673039 930673061
    0x150c041e060216181e05150a0e0f040b1503030d0b10030b03120a0c0503030a0509070602012f0705010f0507110c0a0b1303120503010e01290d 62
    0x40340000e4422845414035000074020754015104202040049040071941c540c144c0740e8104251000040940ca001d000e8091100e403140303002d00a90945c107000d401c92240506c0b6074904100e54031248111024003800c0190750300513104010704202000216550b501225070069841000ca00c0c0fa5940d0080400c00521a190390316410300000481a095907803981002c130076600e04640c034016401c603101d8282d0031a44a107400a42582040e00164001c12000000c1c202e88000790070b01300d007083c055541e071505503441244d8600300c0360398400a100c9407050820500d4040d10f8503000030455030803112003041d404055075442020350105812040c030300b00e10039415246010360110003881010500b08048003c2d00049804038000350710b449010b101c614001903030318040c7c400580400c540c1c9050001100e907680c02044043c7e003030740d00540000002580109944103400c1d05503181d40c0c595060440950080f901a484851210340b42c46403a551040c50035856100b120384036001e03a84c4c4d200488414000352030b0780c6040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 930675539 1250 930674289 930674309
    0xf0b0618120316030305010b18090705160605010303030e06090c0d15020307020f121e0f2b14014205090f0102060106020d050d06050409030c05100b0102150c04 70
    0x1403d504010001420114504c0381d00d050050f0307a212807010096000c1e0f803400380a080d044074039600701c6042590440740c2003a03c51070503034030304075507080c1001104210030001c441d01680c42c80100140f5501d8480d181e4400154005810141440410b9659610840c0d0a451148400383e02c50004c00086442a10f8041c44680702551240361405020751500c019019103603c5000320400781910f02c503100b00301c5e400c2444504643c0c842120083d501285600701501c102e0312084c0c200810644600c3e849200900008501d071203074243e0303c8001c07083d02912108d041e8081c0000608005000404031002c044100c503405441450000140008003040c03241c0d209010790380302c0c15841c564503c1e01d600900a100c8000c059450745d80c807690b0f10004980e248002d220b00760041c2c0004c86802c031301c140710710700914107000b00c080b0110304280c4850006046544c01d260440100c0d038111001c20800c28148154110090030043000c11815071007800207510340481200c4584400d1020000a41600b480c07000c0d0f601412003889 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 930676789 1250 930675539 930675547
    0x152101050901150e270c030112031211070804062a033c090e1e040303060b0a1205060915010e030304082409120703030f0207150f0f0b06181203 63
    0x200d040310a182411754425960560000245405500022281200d6085038882c2d440c4140b5241190400f954628000d080d94840344c00700c0c40c0b40c007071034060020540036007006a5914500030700078013981c10504049880d10301d111420b0240d801d0300040510100c0d010308000400d14000711000c00a503500e054a40003001c001c4d0001c19502e01c61a000081410154480e031145079100c50701039140b21021136013980411445403003200c0101003d800305070032601c20b060104465840e540d4604060700580b015100081303000180c0900c1c03070101e01425030060810f603004402804e182c00314620000b841c40203d03042c007851140c11440782c0c0b410000c460040c80301d41c094074000580c03184860746095080c010341c540c640240c40464500e010201e918030580303165189182ca4400255829409803141074111020300b9400d1000c000401c018010040c80c81010100c0041d00c900c250544508498600200c00c0e4002d207041060302d030f41d031120012540d0300484011414100c02d02c0720300081403040b1005c025201800081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 930678039 1250 930676789 930676819
    0x2060d0906050105010f110c0f1503041109070f09030816060207080c0606120607141c0e0d1d0d05010b06071103060f04050307020d0c05152101050901150e 68
    0xb50081d416240240d841d18a850240c80080f140b110100d1019101900040d202d00118a41504140340b204006881c0358090580648210400d800454050340c603103d032000301103058505a40040c5d8012083c7c280030040001012004004011f10300008000c3c0714000b171402c030400100c480e4a4011644000d040d90380d40400e03d88001541c02100e0407291600c0350341d0104402d40b0303105c0e074034044a5170a4001000140da900e07004980c41a00c00c501e030508002d0401401002c0e40c814488031000405041000c03c80d104c0a074a81d0749061088290001005000088503580d02582c0030b0800344280201c4150008501900701140101000f01c0c0007030b44040005020405c000001001c007003078140480c00d0b00c04560f9402003034800600700301d4000b002c50f00108040401460700c500078048003805001c0c40c0c000075481da0302041e0381c2100c105c005903070458042108401c9100f030701c0c1d520400100c1b41c100940c0551419021401d03c20741800351220348542440600301051007031070f8208100c81c00400d40c41601e9164 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 930679289 1250 930678039 930678041
    0xa0e0307060905390d0f0f0203060703020f0913060b0316090509190207031e021e0d080c16060921080f070c030207030b04081b0606060403020d02060d0906 68
    0x203008220f6860041d90b401c1d0310152508001e0394003107680702455480c0402d07400c40301c0d03004a0300130311681d500445c2c0c1c81043c000b00380444030400b2510b100789030601c4543d81d86d004041c034000008010004150040102c2c4000451190640b0fa0a00f820b07a844414001c20a05401c0602901c1e085844441000b00c00c00800105a08012440544075111742007150307110710900c03040a904a401d06007034141100380d40f5815819900030644da50082c600300c98803005000d4160140c0c2c02c100f0041006070b01132031145100840021303202607141c1c8810014885440702d01400344c0180e070020321f20390759490003142c0160551420702010300c1d0070380c0c0a80c080103240036501d400314910300f5001c0c01840c12649041c92015050040e05222b0190040c1c1200004903940ca000803030b80c00c4c6c40118201c013140559100040014080d62000e4080d91040a0341600e035410b44d10042c2d0321000d1480c00c241d1541c008800d0213110b44031001102c0540b0b40640340e0300384255a0b4004942144107070810003000520307050981082c4029 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 930680539 1250 930679289 930679301
    0x70918082b06031106070f0c180b010c020d03050a2604031e21020705030408010e0c0102071d10080a050106030b0703110301050607020a0305061801050c030118050a0e030706 76
    0x80c15041c00e4003005604a031030031215207010061040408280d514054a408005080407910404050382075510542d5111144e5409512201000740c203050110402d0b849800744881c804420300e0244508081500002c19140c00d00754040c0500400180c002d82480c400c062900b080c1880701d0383c65220011381d66071034204040403201680098204c0f444881c80340d548000c00c4412084590f0f44c3c0f403800c100c0700e590620850060407200c41081e07003002540f0015400780041c100800104e0000681d4410409005040171000460035045401880040c05800d00740010194805c5440e00128066510009403042070303c10b0317070001d00e07641c403e400c400810482c0c15004030702528403808401c00c00f6101d5450a034145c0cac05403850381d000c1d403030180014809070500303002130240135000030205000b1075a603442d03060038000256425201c00340d043c1a13400614034240100c03504401e4a01e6060714540c500b18242c8443c480804102040c01d44900219000500c02c0d00b141400811100c1138030b544a807a450b0110040c14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 930681789 1250 930680539 930680587
    0x42d080c010f0309031211090406120b280209030307170a1116050f0d02060f040311150a0804050106080601082a01021c02010f110702011b0507091808 66
    0x2503114800320b2158800d01400740d400c2e42c55241c8200b2140d01081c40030241c00540c103680c00501701030100c022190b941d0b000f580001d00c070f1569a810140e1139410600c0d480c02c8000c05501209085880754036441c0e8007222500c0080c0242140180c43c1c10b18480004e00f540318850000d4409520700154100d8504000010701e4036003141e444082c42d0015000c049611200030394404805064805420451801d00607690650210010708241c2080c0c851b0340000d019030061a0880141c503404a010300400c0400404440010021661503818401e2440c0e001504e11611b0b410b14108214070020408004003500410040c1048106540321580c48104869840c1281c00b94208100c107903844641d010b82030005911910320341a030140004081804c03541003015005c0c3d800b101190341c0e0b9152885503042070320558907503200326910150364900e280001410200034800000f5159043c003500070001354002200c2c02100c148240104180c0f040004054001c0c00004d0003411078080001c942500c005c90342da40e980800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 930683039 1250 930681789 930681797
    0x1b0b030c0c15010510050706062102010212090306040204020f13090b2e030c0203190309030905030c210a08070c0305120403030c060b0604050415051c0503042d080c01 73
    0xc0c42c0c2d0301c00180300ca00203101c0c2c2900000b9914561075000d100e05c00410126000340300200c1c1c1107543c0c00c1c050502c5035108103520380100c2d40c8001070013150390501a00325030901c1e50440a04084200001a89498000e00028412a800100700e4116a81c00e01a03c0200c0c120380d581c48040c1d903481201401038402c10342041e1080d1050320061303010005495029481c1c10310192880301c86603200f14140c00800c1c0310101d10302035102c140f00c01d88403441d0403507200a14000351b03540440e40000c98130380030b04000000e4100c90700c40d8100f110240540e03100c07607903401400d040103c540b440e608001c0420706e083c104010b5003e020b0000005c2c01d0800d0155200a520882e481402158580b1054548024541c0254000200011101b000d4080424200d401003890907074010030141c0f529590310000b80444030500206804200c001404202e14030740340305080030a604c46c09410205012554a107616841980034100209441201924840e503c009002c0046c2c0514500350f00810b8544000603612031500420900003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 930684289 1250 930683039 930683053
    0x3090105042108190605090c0406090e070206060127060504050a09090201201216110a050d1502071e0b130b060d11040c0e040b060c0304031b0b030c0c 66
    0x41c1c016840105000302c2d0390340e00740e055102c21004079030320592809103c1c038441d00c41e08040b4403a81c42c00725444c003400394240920384c9e40d4500080523040c103030301d03034041d140400b0000b00300170006070045403103a0312200c2480c00030840034070b8234058070380c0b140040c05170081050703102c3e00401c110343c120b4014001c0d81c008960508540751741d00148020b54a0b9050000e00240603c18907043c0d81d10b841c520702e809510140c0a8417000d40070b038038100e807250b040311065600c51a032a14400c0d003404106411002c0c002c00a07034a841d10a8140720100b442c0c138407401d00c01001a41c100c07840340842101c84d415119125072000010070680707403035200078000001c07001088d01d481503564007240c450039001c05035120040d4000140903165a82d0020044600d03240e0380241d583c68541c0700b80070442c3e41c0c0c0b0300c0355a80b090301c280c8030042d05030b1641c1c06000c00c4503c10380c4024060981003103003c05081001060714126076100301d40422070480d0500085010900d82d1140128540110900610981d00c8000d000c540160908903002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 930685539 1250 930684289 930684323
    0x12040306180c0e0c07170702090a060e07050c011d1e070f1403100f06080d0905060706051308070804030b28050c09030307121b111c06020309010504 65
    0x70190048008005014182e02041004420441d02c3e0f8004406500542400c03c00c0d20381840c10010090f81380340e4120009010700441c90810034141d08050040d200f0003007181405042074001101400c00d400348070b40454440d40e6168250030181c4601c0042a101041c1958110103c1d0344440c006449440100040c7d60f103644410001508001c666000d450784908502e49003d10545200d0403882c2c682500989031380c01c150b440c6500072890b0b116022a00000c080b480c0c4040305051989502c04d0100b00700c09003800300080d40c0d801e42985c42d0396400480c0060315445400080740c4d080b14103c00241241d40100300b1000b444540d0018204682c0201c0114615660308402c81c0255590303030250750762001003075800e1a2007400c603510440d44031401004080c0f902c03615000007851074000c0082114010445040c0c0000954040d42100c0d9041d9818090038400c3d20950b1703060040d2500b50081ca00645074100500500c40b818071809001a400541c11907032400c02040301406480100d8098a54000101e00d0201d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 930686789 1250 930685539 930685571
    0x409290427080403060c02150a0c1b0309050a0b120f070201140106120501090b1807020705060706020417030a0203040911040e0703050a050c1303080904020d0513052b0c02030f12040306 81
    0xd104141c4d514089030f1307961141e10209c000c0107030004010802407106000308003d1031400d80a8031560280e20303042d05091610041045100285c0c000741070503441440720480c0e01080880d2035070001100e0008071031941d110103080f401403500742c0e001c0d000c041a00d8000640030ba0030032102c0d84c8248511805001c560788800320241070351890716070150844444007003083c03201c01c05da041d1a0003840b41d205581c45650b540d0001412500454030541d40c083e03000804202c07402518203071003a6801a200134608000440740069260301440c418441410340b00c02101d00c0001c240801c5074060409030365040ea4608002c10010010103089a00c4d642c20b81c504008100300e00b40220a03503890140311800c2c158090300b1540c0b4000e95400103541650050b8082c001c24000e01c0c410f014180c8104907501c00303107106503402d0038206d2410305205a03521600004100c824070341507442540415030705141c203001b0003c1401e8808603140041001108a49000f02002e910b0600c0d20b000060048a000394018844103400785410782c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 930688039 1250 930686789 930686803
    0xf050103030507020618090a0e0709050112080d110a26060307061202070501061e0e09030d0c050d0e010b120105090714010c1202030409290427080403060c02 69
    0x1e8045079003030142d42c00616000d4024451070500c510078035941e0300000c001c02c1ca20f007000d59509640b29110041840d17181c40c00c10540d0001c0031035040a00942d4900801081da03d20100d00181090344000b421241c100c80c590460780100314003080d025925020f1030002011841a0031886d40c0d2000e0700881c0d102507110003441207000384002805821071514206042d500902c550f00d04403130a580901010340481c4080c46500000d1030904180044484824080e03000200e00c3d40114004d10060010300c00b80c641c000080d91203200c0320541c0043d1400f41d1013010749081c00380e030365030700c54090418600060034407064100b4001e0003001d540c281059a841c0700d006080e1401203074907404590000c0d00402291036005002c00c050141030511000e01906610307965901040152501d015074000602000f074400381e840b42801d08851000c64031440540d00e030411000ca0200100113100c1c03901e8448036001e251607152404011944192101d090f0501e40c500000907400610094a9083c0340440417525140040740c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 930689289 1250 930688039 930688043
    0x60f1c1112240601020a050f0a0c061d01030b0d0204050405070e0c0f070b04170301030308060a09020903030d150b070b04110a050a0e0a09140c03011a13050411060f0d0f050103 77
    0xb0350014048605502100c000340362038110704c50210360801080081c807881c0c01544d40e100c041d100442007810030a020744061790080f4100900b9043d40300c100c00313080074150041002440e0115100e0402000240d4222a03601c020750300503d8a000e010401000042342c1085684080e03c51600d6954100210b8240c06009101165140f04120300800501060b0708664420322503050766446590808803003c054000740c200310701055400d001c1c84007501d80710170210001d00030303504150b00c1c209174500402d48a015540000c3c1d552500c8020100c06040212400005448842200c5840d4101c81c20040c0001d0b20556060f0b42d064641031644405040840b82502030b50300c041e120390440e40c6401c448680c0e80c00001c0c920080b03556242654400681c170f03060701902e800b05e00341c010711858646004050846e024040745640d800013400e1140c00303507200c00130300882ca1018034070009410b07511418030401c5124003c2843d64803080000e142e90354680900003030410000c4184080115610403403952040fa6000c0c000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 930690539 1250 930689289 930689323
    0xb4e0709090e010603120801060e0d0c1e081b1504150f110a11010f081b0f09031009170a021509030d150501180509060f1c1112 56
    0x1c0c070040c07406810803260101644000210641c0c2e0b500c035a440810311000305000100705000412125a01c01440070b180c00b0211010603183c1c03219600c03983d0400e09403260140c09840c801c10303400301c0301d1a51582030041040a007500c04983d042c914202c007120fa118139091081d1040d0800d01000f204400541781680e040102841a244804c101030714200c80824654081049120024100100600c00c601116201d20800c15041815800141060303c0c0d5021010030840311604000c12401c0e807600c0a0250b2103d4460260303111007000c1c03071402d5440385030355040e058428a40700c1e1260301c500d07a0024000e280194080c5603078442006190001f0711030f9140c000300686c05480e518212881c002039048d00a4440021030345010901c01000d0b043e521a5081044010943c6400700b02070750700b1000c20b0f02410003030304c0100042030074940041d414140c0503141c1401040000403440c82d6413506110015040e5140c0029400302e00549440b20b800f411105001d805500100c1d01c0884d030140003d5041803104002c50 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 930691789 1250 930690539 930690557
    0x1005010305091014010905070e090432061f06170c070204050403031a0a0617090f030f04080c10020a0b0405010617060f09060f010b4e07 60
    0x1100075100207002010700707026001c4041e00d5180503100746280ca014441d0f61403099850003200740102c40f4000d242c24140080c200113441681d0314070114503406644178140c1201c03011807101c0500c240f021180700014284107070401800140c00092054803410900e07406203201c100b400b101026940301403040201080c018003802003210a100d8115911080080e400e038202340441d0009803d8039820348050b40403a81d214000d03896070364440083c00c0c8039081514038150301850030070000d00503011904d80048039840100400c461840c180502c148600501040740e840703004181d4840080c1c0d105101706e80203441501f115140c00d04241c40740c2c1c44031a40c00c0d00a0111a40c1d1030300c0e0368520301c00003041110555039030315022480340f03501d0b092008015159030041c61985001c609811003504050b2600b551948228100940344940450440c107485891103459141c8a10007100d9206949000d0710304042c4918400d0110100c09071008134203429561040c08440480c0809044041c1a0544001000542c062 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 930693039 1250 930691789 930691799
    0x219050306150408060f2a07020a1e14040222060f02060705040509071e02010f1401030c060c050c04180605070f050d0e1011121b1b0f0d02031e0310 65
    0x801580d600604502003c1601240e4000c01140c01c1400c840147c2c1d81c4002250020542c100410410041c002200c0d105944040e00340d0030034038004051280a00c0300741d103001206015107540d0142d80c20321251901c99900f02c09440b100d001034441d14043d000c0040c1c603008400003407034400541c0c103004080988031189001d00f80414058481c02c000c00800910600d0102014295241900c80b480c00d000e0394000030304c82a5034124842074858404031908140328001c018408504280719040032a034950a1811801c2e816250031401c0a00058405500030b1074040902441a4004079914101d8460b0703008202c41e03511020251030640f00d40c1a00d400041052066010110131640821040c001074000c0ba5100c1d41c2a56555060b0f400300d02c0c1c8421444c9020a881095005081c40150002050b400307950084240c500b01291a000d000380c0062102c0301d4190b00a1060400c0c010300074484000816580c500681240181d5207620150014000c1441d090f0100c5044403417505690040e01c0d03c041d10040d1510300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 930694289 1250 930693039 930693061
    0x240a1b0b160e09010b2a0304090b011e0c02090901090b1b0f0c01020405040e06240409020310140106031e02030403210f060504110d050901021905030615040806 70
    0x100d8a07900500c501e1118a4800355a1604000d000b0405d404940742d84a0300d8604462000c2064110b0f48031102e041101844081c1001c81a80c0c00d84d000100009100070a1030012204120344140c06050001e5103144810180d034000702e2900b0460090340c01c0449900c403c032003142203a541355406400440c032074004c9602106944448001e102c064010b06082070342d14801c0c030741c19611400101d42c3c10303940000c08102c40d0a0078040c00460b840c0078000341405142c080401e00307583c1171820040148040b4090101c1d40356441d80e00600945401504480b6051100150500200381c805880c1803410103ca00008800b80b19004040c1d01451150700b0a5000403000c040b600a9000540308809204507280e42d8020700c0038007031081221410380798012480c2c0110043c5001128181d401860160b82090385a401d040d44120841e024110403e6001540f540c420b05080c0c02800741c0741540c2ca00c0d240c0c030010800401e501002840c0a0705040300c2d1402c240c61801c840c201a48118801d46010781c0140001440031421 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 930695539 1250 930694289 930694321
    0x403060b10084b040c05010c03020303010608040201030f06060302031902160b06040603020d1203050718030f0314030c09041b0e120a050d0807020105070c020f040b240a1b0b 76
    0x103401241c41c0841c292900d051254143c1d030f2003800c5141502003000140545409001c00502084c2032042c851110358600a48911050085105000301140070404591099100815507558403504021064036250001c02070360054546c0255041ea034801d407461140e5920884a904100b841e150a0000082d07440210780c02006080d50b9000b80d0340c4000001580314100c040030494130800c3c2d1080e66800c16000503041315405000c1a04000c0b9082000c1c40d1030117440039000a9940008050b840529646400c4441031900c61020342c446401100380410303140784501901c4030300c60496040c00030b15001c121400d010209802c546001450b8001d802d811703406c00040f000301e1031001701c0a884965040d03803111440c024900d64203034002a150f038100090f060742840b8094000249280000200105400107104c041b00c0e000701c280b1582e500c094071030b40c5903204205010b0a034107418800580c54070b00201c01a09030040a49000440c3ca00000b9941250300d1001200c1800c0e4028241402c684a0300c1e81c00f404540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 930696789 1250 930695539 930695611
    0x80601090f0909060b1f0f08151c050d020c030708011103040f080d0c050714010504050d1d0a08100b01050406051602061b06011509030f06150b0403060b1008 69
    0xa03440400340502c0d01c408201120b6050012044c0245130791b10200100540c0701c17010004100f01014043c0004010909403800403010100e50300400c034a507110400c2040380c07054200400c1841100c0c48000c81940204d900c0d584244120103440742a070b80c131910745090310020b00c06c0b0280340104000043c005454051040b00340c43c02144c840742041030224401c0c0851b21081104008188040b88140c100b1116601c480040d0640070000d00140c20503554090313903024903070040010301c00d13101e021340c2d040c190742440078000c103000820a1018507176440f00e40392514035928141c0e9205042440310f0301e1030f5000300102c404070348603540c80d02e1901c00d041200c0390002c0a18003007280d001c101081034111400c0084010300100d03071540e0203080f45515110411040304e41013105403081c4004882c0c20404102c0410b12440403d41110022401410b000d103c9014a40e55070004c0c81c403800003003008000e100f810341c0144070105064501e19030400ba0b040081d541c921003101c3c506c50000000c05851a548031000c030002c1d80f81 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 930698039 1250 930696789 930696791
    0x20a03060506030903040f0b070f022101110d0e010e061302040f0908091003110d05150306040812090c100f0c0c080d1209050a1e2001080601090f090906 67
    0x81d1940300103103469209644c00d44559001040030700405021040c200c4c01483e101d000d25140c800a562010303407119905038082d1240c3c1512000c4159840754181c12214440241d008010900040344842c1c0940c000720607080640303103860040c42403d141442803410800301d60008155507036800942e098001c00d844802c90300661601c819001488403400ba2028051268a071036459403480d00c02e10030b64100076401c500803d4180010340f0004000103084440c0d0030702a00780424960784003416110310500401d103590b014441d01c03042006225020014010811040d581022551260792140d0340c1c8602c801d10481c0e209101940700c6004a00500043c00002b00a040800d0040103d8803084000d0586d83e11038801604407410b00d0140b41e50028150390401c00121081007004030704c1c0c40303072503a402c0c0c03002006020303c030a1500c4200c1c20b4910102c3e90842d561041c001c6407180340703c0d24150700e11526082041d0104000c4000b20b072496010307902d4001541d06000c49070415038a88030b2007a02406040509903281 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 930699289 1250 930698039 930698051
    0x901080115020f03032404060b0301060c02040908030903070519113d0212030f06060304030c06091101080603190b0c07061b0e06030f01061d0301020307020d260a020a03 74
    0xf140003440518810000714040760100d40c0501e200041c03120408045500c164035116040c03080605901c10340341950030350b14004800c20000d20204009084092024042a8000c1700f003144011000000344245032045083d10403e83e81008451058609484000c06055448101500a04080001c00460080e00006040c8000c028186c00343c0c150150340c402c041e80b900020310300d044a030100102c06400322028441481c2d0314040c0200e5621400c0500030500c14a8000042400d141c800c4206101c03480d080841002040c0f020320b0101c400301010040303503001c03800e2900003921354600407a030340501001205000c40200164ad80d65401c200b0001c1c80c00e00c1c403803003c0c040f8402143c401d100344140842025060900d0240001010f00100c0c403c5050b54440c0d2010000c00c034981c144000c13500d0440d415802d02042d6802d0565100f0003459424600b1605503102200708000d03160f00040b40c45802c81a03869100700c403015003480044400041406075180c0d0f003000081035181032513038000c20040c3c030145400101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 930700539 1250 930699289 930699313
    0x1b0302270402042304030f020723150f13150f0e04200d050a0510030c030f06092a060f020d1107050d031d0a1404200309070603050c090108011502 64
    0x510b8259410350010b100c07c0310261840703404101e44006010500f828000c0b135200c018140c906520b01031865402503a1090220400c440220203030346486000c54245600c0c1c20183c00d00c80b029031014400c00c10071a240c0f4801307090b160b005200f048100000742c2d4483d01a00a42014040584203800000c00011a0f005603030032005421009010700a5207600003244904200450300b0565401400ca0050584001340400004022035080403c496100001c4281c0100c582480740041c4080c9101401c642503809140d04420070250003025400c1c00c4100e683d0816881d02000c980328410100400090b80c0003000c00c8885901440d0341204505201003210300c01910b400200e18034849024003200031072a980c030482e140e01c2030041109040942600d0b03e80c010ba260500902c036030000801c2540c000c9a0340d03584880d0903d00d230b43d08d058420711602c03411990f03070400742049a506c02c0c0b240304210000b0720700350100b040c840c00c02007143d6100005a40c4c59505900348113444080c0b4040701c0c1d0200940c42001043d0107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 930701789 1250 930700539 930700601
    0x2010509211b0301050906010608070c060609110403150c05160206070611071205030402010906030e010b031203190204030c050120060901062402150a091b030227040204 74
    0x41018056400741000b0498009241c2541d4000d000d0f20f02540000c0010300080e64058500d540c0500035103000420b04049044c451b004101c00d400003030240d41807002d00d80102403960000e10841c0d1041081e144d9078902c417400c1404031083c0c5002400020820010100c01c80056600c10304d00b540010302092410155a584500711a241100c09805000c0410b0045c2070008800d03109540f40c03962b041851444ca000d5000820b020070314001d8605060352080f6004625400358410040d4130700103007ca07103078505040c2d0703c0c1c03070280c00c01c1f100740411021203003d20340c0e411094001d450460350701030050907509003040019a200d403c0c0554a603c40203011740c80118410040000a004000400000480c0c6007449002d0316000040b180b00003003100c00c0151b145080d0307400039800c4ca02d041003d01070744141e1200700140c40a80204074029000028072900d040b40e05000031b8005080b61f108480400d0f00507080b0305024550304029003689441c0c94008000b4001d030500d034002e480b00ea1506c1c9030b000003230784006103860 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 930703039 1250 930701789 930701803
    0x1c150302040f240504060f080a02060d06080d091502070b0d020d09150204050405010b070308060d0302030c0d0e09011d07080403170408180f0d02130f020a020f010b04090201050921 79
    0x1200120019108220f04d01301752043d18050040082c4680e0f42a0034030003003c0c0c0d0348003042d40c000d0140c000081e40040191843d803100c0041c1100405640010b8001c031001014190b05009005180400c20400b442881c000503007402190780720203906040c060184001002500f050000718411501c569445000a0b01540324042c0c0390a4680010381320713400c1c03009000446805800c100c0c881402080190003182e003040c2c5040d4040340456804030395103242d28003217065002d0141d5025480c41f60041c6403407000d800015180040d20182ea00d0059130b80c0c1d81c07032081e0390509208440d088014020740400c0c0303080d01c90040107078001d01a06011020228540161312028421a07080c1d03411603021070081d8003801d0050ba81c1c1c80400301103c983c80041d11000020f240401d55043c000d125114101a0380b0f0540c42a13081440d894003d0001151a01d56420002c0d4403814510600d15481d4600b403d641c14a1030f00388500309105406a48050400c0c4548081c022188001028940e114806d1490101c400740100300302 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 930704289 1250 930703039 930703091
    0x201151e0b03011820070f05150705040303140f0a080903040b040909020910080705060a031803210212190b120d170c070f1509081c150302040f 63
    0x107044c15010404140c080300c1213590520101c1d005e0451800204d20220140d800b81600210b00d0595100c0302c2c507001c4d14100740313030f160300044040d00010007603c20b41103005001100d000341c0f280c81581e4010030b03c41c82c451203102e0000c200068248100d007490b0b07102d40252903105484404480c40c01351111800c448681043d4814002e954682030701c0400c40c20072642a5400c5510284030b8030f0130354102078440d51105150300409024803c040703807824406101e508002e0742d1041611415111242c1410300074aa9081c1504a040252140c020a0a150074038400c071400c400801112200c2e030749900e0204004002c0c1150110030440d129881100e0a54500869080b100310032002001c0442e07580c8000351007845619100003d10b80e0802c20418594024070441d095154015101c40c0c920700c0c00d00c3c02d10001c5000c0400714292500c0c280d0707c10704000784907000789039021045940b607074820044200d41081d02d0f4402564001901c0100040005040c1754204400301c03641c800c17010031804102c607643c0080f00d92070515 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 930705539 1250 930704289 930704309
    0x60306151810140d150c03060518091507050909060f0301151404090201050306040b04020408030a0c11091e04230601050f0301060b03041719020312070201151e0b0301 73
    0x204590306003450110380385070094460021103141a203817064040e2200301d1000646407101c2c0078990003842940101c01403e80140b0313884d520010032011460b00081242c614106101c2d1800d408100b43d0080d0f4450b1052440d03503182c503d01103041c0f0600007a4a0050700031900301c01d0078030701b107815980d0a000f50390303440c002c101140320000d140c1028000741e071120001041c0110314251841c005030741d000d000c480e4007080c140d60110ba10305003440450021321596102c84041e000c042200070499502592003000343e070040309101e141c090a601002510f18003030f2261000d000a601180e08440c17502003100c1d60050041c0f05107180c13174040404ca40d03034101d01500303055290303009440140818500503030010742c1114254000c20005080012860701440003920281804d040391002c035031800610380c221204440ba400c0d6040304c10f945500065529040300d0200a0f084a840c0001581136105104d1503c0d01c121811100284c42d20781080386500c500341c00400c82d40d60304001000306440c917062005600070210149 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 930706789 1250 930705539 930705571
    0x703120203030703110901171009092a0e0105010f030f180203061806010614130f1805090d050a180803090108010b0c0309130e0a0b0615030603061518 66
    0x4000d00704d405c400c14400c2070358000e028010352a640280c40c1602c0e40102c254020181c0c81d030084641801460380e00001ca11410040484200311100300040c084030600c0407080011002d00c040034400c1c80c154001c5000e4140303031b00300400c01d561040b1180c1c40204224240001c5003402c580081d001d880714012072003590913032080030b102141000c0124503840035005209010407207042040d1516100d040c40b0344d03c10070060001d103600161280003140c005549124010300c105944082200040e02c0900c0350390703800001030903154903041c9030303001d0940300710501005420240072501d419641504841820820850518032543e029803c0c45c0650018100240085407a0b4240300c000400c54001600070401a0a0902114104100c00019a01100e00868031901e5122586070140028100900d5114161144819400500c035880c0c0d480c2c1c0c02082c06556240610711400000380e104e05c02034034241e405601520005a030032031115000399800070003c3c20f800401000c1d0500a00c280d03c19500f10040c035102003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 930708039 1250 930706789 930706801
    0x1050a0e190f0803130e09070e04060501050f010e010c030516060f050114030a050a02150d1401030c0803040608040209060d021201050a151d0a0615020f0c0103092102070312020303 79
    0xc030400d00401c4070000441c0742640c3c01e030342c154140180340305d1600d1b17280c01d4502181094900740940c1002e000c190703240c2c1180b813501e41000800350000b0300c2a14090124100c441da6594801e074078007110000c040c0c4074070b000380c21103907011622a80300168004450701900d043c03100040481c0680345005482440200c0c25505040446100800c03500180f8825800102018001180411074001d110f4045030240c490b41e0540500d50210302c1440540705880d0301d0010403048200110300d00506030b034050014224810b8485104594900c03590046101150b080f0300018010710700a002e2503401034000c0c0084019040a601046541e03140c2d07480c42c3c0c030326516641040125504d510650000300d0302c02c00e034600d400d894003590100c141140544c03c400c0602c4400043c84a0301c070b64000031b0040182c003115103d900704202d402511420742450a2640340500044903526600c80d00035103100304e40002105c4407228045001040c03458038820440113501404c2800008a04c102c240e4110f810715903000b543e5245085 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 930709289 1250 930708039 930708059
    0x33405030309010f200f09120a0c0501140f1804020301060203360f041d0d03292823010207140f121905070603060302030c01050a0e19 59
    0x4680c484413074519261a94031040c0d40002400100e0342080140e0303030340700f0b1a2084040640b00d03000b1902e8129a60450700c0c42000d00c0020006805030080d0340c5208816100d02c01154a08032920300c600c44141d0034808680d6486511008001c500020307400440440c858002240c20f03608240d2058000d80c102040c001d03800100c22140e0b105c02c0c0b00801c3d00308000c8425501c5581c50390400e0052a020342d0964840320015103c0d42d0040d2403540c0d50b95591028284600741c11981c0b101c0160700080000d003811202d00c08400744491484001d0f48003c840358100b030056090168452528141c111070722040b851003108000d2000c08100582040012804444a094160316015218883c502e04550200c60f0421030a070400c544240f03518412a014050303074450000040c0c82424505940170386003c0c00303103980b0590406c042e8000d05030380300d0f0041d52031155a411040e02101d40c035100113034040d0040644000150310440c000c0424802c01e0400c1400000b00e07a000c101d415902078016880c040b808102404074901c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 930710539 1250 930709289 930709301
    0x20406060504050114190813020301050103080d0c05120c0c0307060c0810141005090307090216020111191518050f1006050d020f01050708030a0507030c05040803340503030901 77
    0x703060318600780607080e1b08100e011081e0b404000b004405004600e0540b80300c1c00c00900c0c04d40003002407041c5d503124104400280c2c00341d007041405a25000c090310046003e2015100d60009141515100307035600c00c0220301f203a104050f1040e00d40820040303000094000d1282e200522050741e1403c000d071400c880441448002a006224210b8500780c0d0324005c0c3d80c5003041038840300e141d0703d0015124074214010a01e4102c06030041c01c0c9d000e0003c90184c8050102e0741c80c0c0094107000f41d90350250110704102058032000400d10b070800c680d00304001d09003c41c601c0c0440980c01800b2180005800d1030640c1141c14540b0310480803200c0e500456440030707440e41d0800001d1078106500408118891a220000300768010214000303028100c0c010682c040d0303a0007401a50030390ae030004412503403850200880030007080211111808286030141038040b4610482c20b4900707032282c0500440c5000007200c80e03401e100c40341c0351600000c4515100c1c08222a803440d03003080801c0303200e08015030702ea0a02c003103941c0c01e480e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 930711789 1250 930710539 930710567
    0x1b0314060a031e0203250f060801290409061d15010f0c030c0209040b07030608030306310203070804060c02120703030b120f011505090403091a072310360204060605040501 75
    0xf027000103000c0e48040300424080f41202d2031844400140d83e002c0c805240c05541d000d0a04103150a00c006070000c1c5094080b00d159584045440d90781c5e035554050b080e1501403400103800554030b0482d41c08214022003a88002d540641858161310b525580095441c0c10200c0d01150905052030078807289a070140a004040c1c4080806035080d858100c000c5032039070101e282004146040503980c0110b1213142c4016007104580f0341001c0d5568982001c0140154001b0740c1c0c21204a40f81644041d4013078030210754800081d1030002001d14100498030203c02610343c05e500186c0c00030b40000080c54204040101c1041c2880880c00451301088046943e400308140b644110f014405072000c110000b58010703041c82c183c1e41041c13207002211042101101c418001d0203801004e07064408281d042115090168140380c250314000c40b15900f600d01404010703512610a07203c1d98080785d40602c1d054808000c548100d500030040d42c040c441029400107800e0714002c0e8000000724000007402e02495078032200d4400108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 930713039 1250 930711789 930711797
    0x4060209100207050f060715060801020705071401021b180103060f0e0a020306010e0c040b0307020c040f1a040e010b06270108281b0314060a031e0203250f06 69
    0x918013004107441784c1410116501c24500090401c0401809405c10245120380e43d00820070b054a03164524004d40c0302c950203550b0742c4104000002d440e0420750480c0d40104060380507000302e104076040c3c6440b0360268010b0a0b4046c0c2c0100440004019a502460080d8098540440d5000303071844030400300c030701000b0220525040b02c0034000258600140c001d0442c0c04012000005944d588402c421a000362303040b0810007040041403004182d0b0004038032802d200204d504021400011400c081210107064080c6000c1c4408183c5104030301d800c4c0e02249003080460008194145820001003090b80103401920a211440030340c0c00141300c0e07004400500700006c0c20700302c082d070400c26000102c2466811401c0754203516010101580c096940000d442009a00c840a0040d800301d1000b5025000c1415550001c40700ca00005582d0310742400c5101c01c0701e400442070009000f0200040080c580441c5090f03030076204086c851026044140300014049020700700d00c07c0f8141c182550142d2085440c1d0201c0100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 930714289 1250 930713039 930713053
    0x12090e01050402160b04020f03070303080f1e0412020f0703030908010c0201180807020a0b040308070b0a0204060903031202040b03090d08070309080909090c0a18240e040602040e040602091002 84
    0x8455541521043c071790007812900c0c81d80e940e4400224810901c0d00c50b240c241c007581100004068020030254091200c0c0300d240801e40da6100850000c1e41040d541d000e00c2d007481000030078003013800c0309203681940c051841030b1241600c1d403400d102d1401010303900c2200028203031003080203003003030a200f00440003c0e9403000f4049004160700d843c6a503840d0501c050010200000e0200c11583d445000350f004100f01407502d078680369681805031440c0c020070400c1e5030f1600f1050004007007811510855003034500360348404902a0640d20119900354000035003810300b039400c000105111042e83c001d10b104083d00300080c02c40340342d00ba800604140002e440c0b2014107003042c107581c7c00034611005981e600301003030300c04c40c0b150b5030ba052589141690b580101c54000301506400315a058100c0301104201c040e801c0203215011601100c01055001c0e00000c0f55020040381c0305001c100110b59130150802e005210250401d611908115100001990100c1c0c28590015103406d0758101140303198240d8540c1d0001e000c40c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 930715539 1250 930714289 930714307
    0x51e1c0b09090a1b030204050c070b07020a0b0115170c0403030909050708010b0918040b01050103060611031e040807060e09061905060d0f06030b1807151b12090e01050402 75
    0xf03a1541884010901c0c8000c4000c5202105200c8061009580090060040d820281401c030116840101c003038460208039400254890b00000d80092000c3d80600d10004581c40d003d006964820540d11460810000f00140500d880181c00030300d006102811180782d5452035840c01501e0b10801d030b407003200c42c00c0c00d0500b0800b8907078006d1001030451300e260114990380d40303580c030020b140d1030b85519503018002e91a009010512a0b041c0e8020306070398003a203081002645800043c0d07051481c5950b103082030b6104112141000c000e1103520508180380b442a01d081a0721059012f081c5003107074101c4400221216250041072502d0960a134000300d06480b0411000762042c17031094000c840b4019640142c100180c036004005a603440710442c00205181005003070344174505002030070001d98105240984002260829802c0401d100c000c482d0406150b0129000e0444141ca0304c011001c000c540800694411102080102580502103034059036213848580c10301100091010041c1c101c10700461040c405a0b03c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 930716789 1250 930715539 930715543
    0x1006060813020d0611180415080a08070c050901240c2a090204080c0a060809060a110f0a0503071112072a08210310030201051e1c0b0909 60
    0x10040c0c060301d52040c140000d0030400f001d401c1a8114203030b205c100203103d200301141d02d8442d089201d001c9400f406214121b41ea072010b001d000380a207a40c190071102c0241e00140d60200241669845103042545c1c2558131800605810000d0303112601780c401c0b40c018005480070b0b80003048003a5006062407452002e064031007140180120615002e07043d030b240d4011030003512000766107000b405881001c0d541c680c0c0354801c042e01e0310812448a400340b070b190309000c9800c07405100028854141c2200500040c2c0e030703101c0020003901c00a26403001ca000200403540802031404000c081c00840340d2180b81e0344e0b040c0404018500039240301c2c0350146070403843c0d10b0195141c442c1d0864604c00c0d00805000c0940000d9000d100c50030303045402407106034000d00700c0003076990701c00310f0329222500c0d6940480540f84034000c0d440c3d0146c031049034480403a9904820038001980200060032010341c40e102040b4a181800401582561100504a0070300907905040c0041040a00450020400944005015084c01e40c1d29907 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 930718039 1250 930716789 930716821
    0x71e0b0414150a0209090603061e0a02091c0b130803072106080105160e090604090f0b071808070e01090b1306030c1d070206060105030606040e0910060608 68
    0x1000081501104803021004010b0780107480c910340c814104a0815a00d603400030b52000c1890ba02074001480010024074020403145d105031780c0f00b003810300c400ca040c6a2070121070354000c0c0045021603080c01503003c603890f100c4130341203080144101002c00f1030300750506085202c0020061070513242c004800c0390020b12490180d07a046542d509007e900181c4c1c0e4441c511400f9400380da40354400780703400d9000407101015080300380203031902c0f5054100e100c4d1400c8106d6002f00d8401c0c640b81c1000840022404608281c0d02007040740c2c0c040c0410090046540c0d4a074224118250795075000124010045440000c80c01c1c40c0710028000708000740b62107880c10b10b56000d0b481c014030402d450715075100100009601c0300503080007000c0e124802002910344034600641e0300003043c01040b03108420340300c1e01540702100340d0500e409195170340c004000d10355a1b800111030f41d40c030050409030490024000003408102c100f50041c060014030b0007905210108500e014200c0d003a6034050304c1041a42401d11150010083c807034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 930719289 1250 930718039 930718043
    0x60601020c0f032811030313060e0109030f060b010801090e060402040507020f0d050d060501050c1504020a080d03231b031e01060807030c0e0135070203071e0b04 71
    0x42040302d04580006414000031910f2001d20f950040b008414100084401c8010541300b070002c6002c0e2420714040c543c2c1c034000c03402d90b2340711340c8800e0209203c900c3c011003c00821002c1450481003d94030ba55540000081a02c81101e0058650f10400d065607046003881340540780440f810821040c0000c40b40796902c00240c0045d0290781da4101050340c1e14802c1c0504400c541100c5c0850340d40a4180ba0001d001e0703440300c0004040d0514003c07010a0561103001195050007400c0000c00445600203142c0071070b4800504101c0c0d0102e003181c80020525024003241c2003000d401d490028200e5100e010120b980d00010403e1606520550201300d03408040116808145821000c800c3e200d9650034800080b007060106200d00c501116000040e0303055220170300300c2c45801d5a40e801e01c0843c07604d0600352900c54880703041e280071404201e0b402c1441c2203c1120103011041c0e0389001004074024120f02d12032018240d071840c00603040000c0c4a011300c4940c0080c0c0c84080c1105002580d03c03130f0030340c9a04e00250006040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 930720539 1250 930719289 930719299
    0x1006060f1e090314011407090801110310090c020f1618050402060a1b06050412020f0a031d060409020403030203040512030f040905070509030f0706021522080409060f090e060601020c 80
    0x29501d1300701000d52016480c2c000d100c61640c0c0a08201c47d02402c813184610820318258208030030442e58445142c01d40b03000307408503c4032591150800905002500c1f240e0407402c210710448541040c0d07400c0801800f0881981100d442c03440c141031084281100402001041a1600f444144001030701c0311021242407040600d042d0480003286804542044940d2030050800c0f13042506006c1800644445480d61041d2602107c035103083e1101029180c0f400c0d40b1018000c40d0240b014417600d00400660764250b000000c280d10b14140e01c4050000480c0c006800550060b40046018003250815080e1416060301800043d8244020016800c42038825406030228070741c2c940010803440350060701600c807052030040c1034405000e80d441800d45d940e400d62040c280144103543d402403508208480d140d020745030b09a5200c01c030b501c48480c0840040c0c1c5205085a400e40d040000040521580c0306081c050098201551002490f0030040015030f1060344490000f42c1242e0148951b503a00020400c07013842080c1d41d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 930721789 1250 930720539 930720563
    0x7020402031e01030c0603050702061302040c02150a020a082406070c12150b270606040807080703020f0402090f0d02040f0c0302120112020a090e1006060f1e0903 71
    0xc0c08a8000c010b8400600340c03107101030004000c1003003024100094600540d0100910741d501c08040fa6603120a0741c03031404031110801c080e005804d16412510380e8a00c0b6004941c0c150f4500b214081110008550590090303501140c48582d10303911161050300320f05140c81c44224103c101c00d41d02c51030320081b100e4900c5000700203412001c01c14003901400051000010075107407601b4a04203280c44400e44c80030070b03030218a00034540b501407611710034101b04281c41e00c003508200c6420000f1504000c10141035264000000d10001542070b004000700d4002d08100700c09002030310b00d18810300c00e0300d01128007607500c503078014000310003942c48040788030003d060200c0d00080018101e0001c10010010442c0c4403054500300002c2008250301a0002d02c541f455504565407640c0ea141c10f0040071900d202c40003903000041c000b0400190f43c8903000f03024280404c4055a483c040c4020703a6604550b4141d01c000003250004c204042d200d5082440160102405c1c0713a01d1004d00500c2c4001031003003405000c01080000070036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 930723039 1250 930721789 930721801
    0x717060c0c0a0213050601090f0f0501111203160206060301110d0b0a0305030f090108090102040311010f05040e01060e0103050703110301060c08041d040506131e02180a020a020c01050c030702040203 87
    0xc0b605071a50040e00c07560741600200107180c098481295094081100d012000614040c0e600c084c1044480c4590f03a1030f071141c2840c2c011070b0804001c0c110508103100d410061a68a908600114041d141d81816111345412014001c3d042810081c8003a10907490b01d5030100c40b81d541d1000303c8103030941004001803c1b12924001506a28207908050304911010070041c41c886401001041d1145090303c440c04296690f140082c240e2003140002004c3e0f40c4d00400304000ca50080182411216403814003034241070305d42c2f031719400c440000da01c2440082c005140501c22543c140c13162541203d008e05e070a025418040400341d074548018800c440401801306185406d1050303810541c0c000d4504c40307401d610714100a22901198401c01c4d40c003550140a060041600c04c081e0100f4409041d521000345c2c1031800b000e1303000103400551031400313036000203a50784403c408089501c0c50500c550315000e00103032140380f0307040000d03d841007245000781805000c00410300705080c0041500e072210f504079000f60b92a50340c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 930724289 1250 930723039 930723043
    0x40303031e0501060504300809011707051c05100b090a09020309060105120715050d060509091b041e020f040b0714010b0f0627030313080717060c0c 65
    0x3010700c81180600d03000000c66265407050091013110980b881c0c4140d00b00e0074003102d0303200c1c01e40881100208828400b900000881010140148180504007481c00255001c800c4440c204221001c0000850001b0042c0420311301084c2e50145000b6a00200300a10f850703555079580c882103000f00344000d10007142e00812596080b900c02c01414620b4829502ca0900003221640c4040a008003442051504420080c908000594100300c078001d00d14180403581021040d034030b9a004044080d8080d0325400d02040c2d9488284400b401098040c00901c5001000342942c0c5100000302000d0b8802d50501300e00100303840c00d4008402c0d00c031182c5600140c0d115000b00d09405188034a90010a6071280880c208003440003240000500d0301803440240003500c9090100540d6145401100d54050b60a1040802008078594000149640314084d0542c01003140006807664010010200c55151500014815980b05010540080054400c4210035503080306100c3d88803600140f201c1e0b880d10010071086082541 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 930725539 1250 930724289 930724331
    0x10515120a0f1509060513021e130e01080637110c010e03030f0f1012050a05030f0c0c090103030f2604060f0c08070e1306051e01022104030303 63
    0x14101c0c056030240d50320070855000c0c208903c5468400c02c040d860450303001c002c5008944d20541641d058494030356407200b1127a1160000d401d403952401e00100e0219440030f09a400c2406004001c005200d541342803261840038034000c0201c800400c0006005e6541c0c20200342003245000590b1801003000b00401e44c4014881c0200300241441d5030030b1054642c0c180001100450041c00d01c00d402d8001caaa03054203140c1c07046c1040d2414407072148040e800b081111015420354400034440e00542c0c81d1140b05403907452460700001120884031100041805c0240c004014102d01d12005036503803071aa40c51a100a0800080d1010040c10b000c00400792079103140c0c0000c031526214044950905480c1450b04044009107000460040c0c090b1a007075000014a0003603400521650803681d803807149203010014040740d50920407042a00700d07100c07040803400342d4030900c2c92402065451080031403500d20000092410342008411640b044404001e0503828819100b21000c1d260541400300300800d40c1501c1c0341240d0a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 930726789 1250 930725539 930725561
    0xb090d0e09010b0d0f060b03041b060e0f01030e15010f050d02090c0f0f0d1b0e1f020304050411090102061003080313110d060e071a1c091a010515120a0f 67
    0x480e1800110311031090754095030027680111b800a1101d84034403000b1000160900808020172140e19004c000340c03900b104850312010042c94085181070102200c1803522001044403100d0075812030040c0490005055044014403040700d40215040c4240c012580e1641d01410014842c00c0000365007607107010000c12100040c0603194903c1d954001c000390b00c2c000f000890302e48407403500c08403480340c035940c4030340002e191603180185030f03500000a4100c0200d080c0c3d21041c0070400d45c0814440040c595403584904904101d0311441c4c10390350003a10340020b050980003084c0d4400c0c90344c05001440802e041038203683d48102c00c40c80800e210052400c00d540040d000d89400c0f0341c0300440c00121010002c87d500078209504480742200d032002e8035427200c254008104007181d0754007601400000d03200c800c9030580040b80760b806840000d034120141c569103d01c206400455000b07a02c61801000385040c0301c4800d00c0d0514400700704d9402d04040c5008408404c60240081c800c1649502c040c2d040104503901420f0750390 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 930728039 1250 930726789 930726791
    0x20a0e01080303060a0506390a0c0509160903110a1221140a03090f140d110604020d030e040f1b024b0303040b090d0e09010b0d0f 57
    0x141e51040309a6680d8401c072800c0f40a900b2117480018241420703419140090340301300e07602000080c1c0801e112010a03040504a81360103410500f03440c004400e01840c00b10034042d0384100b103181c0c01c00041c0041c3d44000b034590f00d50700542402c0c0e41d00d01c0703900030303402d0003502c0d03000001c400c2100c0b4400016170448000e41103145610b011810302c0f4100700c00c0401501c090305800100b8401c00c02048400d8401c00104051600112010082c1c140d4140c0322b94031420f5520300c1587c0d0180d000308151208640f088030010300411681c000341e2408005c076040b005003030074111035000a00040c0741c1075010451640302d500e0300409202d80c000c2200c06503565601b0030003001404890401200c0c49135036071f009082c240c20000380b0150241403941000003d00c007840340760b4454505014917018800b000c803624514a10000321120f242100381c032006444007400114000c17405281034089505001400f182404128101c05007400310b0744010040540342c0100312411a05203000c25521080c1314940703040580320a41c01444aa = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 930729289 1250 930728039 930728041
    0x20f0c1f0903051504060e010b0603010b2508070c0801060305100905030d0c12061d01050904051c0201050601033b070f0306050f010f0803030c030618070e031903120504020a0e 77
    0x1025841303010900c5140964014012031441ba40d025081326841211690010030400c0140551404900244140083c04a06800480d0900312992254650740821a49118009900e9003400b91810421001d0290180200400340ca11b44e14103036900304880e100e1040e1900e5080410500c6001e00a13200c00fa100d411052040c4102004003c1048005541c0c02c00c115141810100c4c0035401184800c03640226541129500d0342010100510103800500848061180c070f19140303d00400c0d5a4039070002d0701c4540002c682c50a00100140594000b2030301080203090031000740030451a40c03d1801804080b4400c2d050780403003140509410322006412007502104030f82000800c004403076000030b1040c8600c01041d03c0d40d0340c07200c00d400201c1c0325038458403500e40d00c02e1002c1056110444029904078400900d428140300030707091405c15880c0c1c1201c4040210b5900c0141d22410b013010311075a980440503084c01e0070400c4aaaa02624100fa804000300030250b48400240840d00c4075030400000c1c100304c207505072032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 930730539 1250 930729289 930729313
    0x6040615110f030901080105042004030c0f0527040c0512060103140a05030d02131a0d0b1002030409150302060c060109060909110103200d0c020f0c1f090305 69
    0x4031110701e60035001d03105444400340030040200a540052205945407201c5902e828100700242c05020802485041064201242d18000200801c0214410761b48030b02414604409240c04243c1540a14003502d60000307810f0b00110703102c000858011603107070314a040b40c8803812304d10503582d000c4c1c000036080b003101001814449030028441c1e040741d10031224800404200220f16840300074440c4020301a9005010844c000c600c0d9802419503070820400c5210340755a110b050080c1c01e81c0c504240e01020300c001501007090250b9001b80c2c0c481184c1038501216500c15010000e60300d01c100d00c10b01804669410300c048140d055002c400c401107400a0509880c2c5181c400780301d0302d510003846150b002c41c2ca0070500081c8030049024a0640c540c024241c8d0b02c2d02d2003c600150301604446810b4810000004020058480d0f4034010301b5255100c944000f0b01349601c003201a142c500358901c00b04107a40300c401100d00c41d903200f01d0000141e10250b403c05010000329030007668025401c0d040103005005400c20240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 930731789 1250 930730539 930730547
    0x305060903090f030c0a291308010c021f15081204080d0e01020604031b020d061e05060904060e0a0f060c080106181502120313110907020601090506040615 68
    0xb0352808075003038059000504101592561051400341e0445e500890400c0341c1c3d5803031014180604031a0b001005a100c46146280403507102c0040543d100959810500c102142486401000310761400108940400d030f11889140b02107154000102544526201e0f0402030002c40940061507920304440c18103a0150715900d0940060280c0302481c071030482e003d40c00c070340f091882c100c6207030040c2c01134011501c9549080f80c854624154044801a2007200000161106ea424181c454003035040041c501e068a10004080d50b001e403041c0e04100e0a01d003e1100e69511000303655007199100c10001000c80340c03c83c002d03082c24a5140d0280000c01c50f44101e4092003507542000c00d401000b03a0368a840360781c85144c142e5200100da01507400391441080e00b44042000c06a0040e050b1895004851400b00068a034840d1503204882045420489083d01010014002c90704c80c10304104890b04007062615400003591480c0512419820700e8071394010508541307440d80300720007418404414000d40c03040e103c0050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 930733039 1250 930731789 930731797
    0xc150f070f061a060f03270f0d0e030307050c0f01020a08040b340f03090512070e180d05030a02070c0b0a02101a0603100f061101180c0501180305060903 67
    0xc10019010b60008240c0c503108017140c00d8002003844090840d26043c1d9242e041c008912100143c0c103024850000700c1060410042c03203000c890300000c16081d120004000c010b281410500c034003d0342b0034000b2400290010408208c400c0303042d02e1014042c41040c0c0100c0c548004c8110150205000007400b00e64082c4400042c0740c6c000036164090009a06003180500c4414040f0a8103481041c4604000010b00428003001490f4080d15240c0b80080d02c803400641c0907034031100510303602d62011030100614000e200e101c0703031701c0901a0f045c10310840204070300c1d036155200e50300c3c6a0304204001000816400d4141d043c2c2d83c150750048001e00c8500c1e1110403010303da5000c0d004a0f800740c421004000040040c40c029102c074403000c0c03254600c243c1c10000912816401c0602842c0d0707141001d0701d0100c0c15007038070079580d0003c103a580c0d40c420740405150281421129225550050ba4000c01c480c0d0000ca030400300307a01c045403001c0c40c101a200d00401d07901c03145240c0300c2c0c10081c814060001401907854000001d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 930734289 1250 930733039 930733061
    0x5130b03012408011d1b0a05070303060e0c04170123070806040506060f0a03020903030304051510030c0611010209090f071b0203210d24080c150f070f06 67
    0x500c809000b429801d8605820900c5140445c60b00c020040c1c4209030074450143e001002c60765652250100c8299070010f541009600000080000c07640006155240c000c1500400e40c0340b10300344007400c0c45100d4402904c16800b49092800340c502c0c20041c3c600c0250f00644441000c400b00b00c2c0b026500c500440b03490542aa000800101c038034000c11031a14052007030b1f07402440000e00d6549054811070032a0a242c000d10080804e040d07003030010985a4a06000645c81648200d02800e100b20b0f1580c0d8401d04480050015001d021884d1801d20004110b610020195201e6041aa0b400021120800d0191040d0900d498000e00c20600788900c00b180290300b41d001c1c000d0b544441e0302116202c1f08260180d10f03400d06c04bc0d8140d01000c5400403e0341190b040e5010010320811a40c41d04207400154819501400780d1b01210380e55070003602030b03000c0b03080c5402c5000c0c015440c00703880090034820010384003124000389a580801c00040a0711007121200c101e5000560100015032592641d0070040010604c2c0000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 930735539 1250 930734289 930734339
    0xf030801060e01050307090e15040f05040302010513030c170912100b011107051023030105010810080c010f03020408010c0c050c10050301030605040c03020a030b060325050105130b0301 81
    0x4500b20b035800ba4091301c4c4503036007a549452036146004014150700310007a041100d90500f180000601d51240d024080d01007449150102c3c1c242814a4000d08440c00244480c044940320401c0c42d0000f50300002c14480d0541040300395106040e88203034040a0300c030b907828480d40810401e50721000b40a0100e80d41d8031141c04940c0400074118144015900092003480c00700c1a60407ca01c14841c1c1d1078a00c0429000f181940340189542100c521240240e08400118408100d0007200401496a003e040541c4c080707080b400d10340d101c601d4040e1040c3d82c0c144983c0b03110705000002c10003200c020b1003031b8103a90050145c00002d00154400b01d0b0090310400110340c040d601406036504a5000c0d04003454905002a016660b11307242d40e1840c0c1b189001031601620444081540c010000056583c4202c0107001c1c5000e4102c51000742400402c0601d4200300003000c950310094103084040c100101030f0600c08913942070074190380d5581b4070f107008001300009401c0380c04000c40201c00400d40003004200d14540b1300146071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 930736789 1250 930735539 930735557
    0xb03130209090609031c15180c0912060203041b062111030105010804030201060f090b041802060d0b190e0405060c040f15020a1505220f120c0f03080106 67
    0x281880d1a40000c46050840b42e000b006681c000c024030b0301d1b84800c10751758083d00143c040d1900300600c030300303242640c828205030900d069024240360062103840c400e1189410f191242d603140090809001090040241c0002c0c1e012001400303101c051681d07230701e0001480000500e21a240c0c41d010703190081111000e014020300c0d07404000002c00511814002e04442c01a46055a01c1c1000445620b0b01c0107204a045548400b00083c40010b50100301c0060880c503c8041580d40680d4144011a07058a98490900030b4502000005d0303104d441c00c542100c0b26101012610212400c04140450100712860412091034040010000c04084005015506c50419a4004e444204081149018500440c074414a900c2c40400400002c001c4e070a18050541c0161390007444140c0f0b481c1a181c0403000c0d00810140c40d8406c0024202800d80000000d00282141d4007100303220b83c88403042e4406280d0010300d03403640142000d46680c0101c03d01d1002940c4441c0d54141e03000d80c2c0c81c3c010044c0d9401c0c481c0b0300101e85a02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 930738039 1250 930736789 930736801
    0x518090a0605042306131202120a030c0f05120402040f02070c080f120403171c1b020705010f05091e120a03030f1103070c11100c120806060d05040c0b03130209 70
    0x1c40e0446c080c2c0c01c001d01c10303428a06240c6581a1085003c107110043d403003203005014517440e007040600302c02d600d036460000f01c40408180240030343d08401c081900304281085041c0d29524081d484540040c1c0550f0001120406400030308020700c40e410000d080466510000202e0890000383d1801401e254403e4403950101100d440303019005a02006191800b00c1200502071041503000d0401c070492054210980c180800514048907003160345e0350000a50050400059901000343c080108401c3c44d14500036142c00c0f4000340a4040c20f141039103c0c4920035140c10000c0710002c800038000000401c010700002103010b82c15036806088408402203410b000650842130050b2040e181643c4156401d20316665400c8000c4a002c0f4046d00e00300c45200700c50319140d2a40c1c41d8681d102c0c108100c0d41d122881c019044c0d0900306040d00150303a4500400901000b00401d23902c441d41a940c1d1015608000f09041d00d90b468035414484140e000090f11140100400c029501815101c000080c000c0e20801526250743c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 930739289 1250 930738039 930738043
    0xc09040e21040b0406030c0e0a0303031a0303030c0405210f0d0e0406030b060f0d0c0b09030105010f05010c02150c101d0106230f060f0c0607090518090a06050423 71
    0x1600c5101c685800130f000c100300351802a0005108690b2078540441200d240100180103d40310340c1040d0002681ca031015001e20720002209410000210002c5003945800070f4500490300c210301070140108520801c5130300141d40005807164001504003560310742040c031070945964114000c90030b40055492007042d589c0d820588100300030340340c0007000210595596400e01107000344961100307070041102804400490840e01090010b080507090b110b688248003401c0609548041c3c00c4003043e0008800e0412181c3c0c0c000e5180413400b517051b00c0742d03031900003130a0200d5414041c984000002d0300546201603240300840d8800551542c91000045505400f5007850f8200d030044e00814444441103100300d90101d0400c0300003010241c00070301038251615100045940b54000d1005101c0303c84020416403801c42c0240032070765100c080f038030301440614600300005403176103081c080002440741520040340d11042c0030b004420740756401000c01d010500b0030b8034000d480401e118581074082d6441c4100e4405034400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 930740539 1250 930739289 930739297
    0x140111071206322a04270e03090120100c020c030318101416031709150c040f180c0c111e0603070c060c021b0603090309030607030902090f011d0c09040e21 68
    0x41403000b94142200368006650b804800e0171a0301ca12f50032101c02c4041c1a400b00820080d441405c0320114010300a110f01900d0241d11105541c4030ba00103000080080c504d152500b00d0b03454007242e241c600180170405c2912140c100d12415091401c00003829142069640d528818861103540d9880452014254400190300d0965040440307410041c0030381010418004819000500451814502599040000c0303c0e580941d21210022104001492200d04988150000720706c2038200000b041c4450340da4106e0041161f801d031031141422480b07114084810401c070361500300000d840159a820841d6000d418400b03031080c115403007410091410380840c80402c11401c022008401c81c40d29000030b4042260681000304090758602c000c0c08000c1e41c0d80e80c2006007900662403030b00c002403900181d0040c8004110700a201e51402032a40c0b00410000b0101f80440e800301150b1049007003140c503100c40840452289038510380d8080d0403c42c0552000c01c011410b01414289403554019001d42583c034203106004d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 930741789 1250 930740539 930740561
    0x601061106071d030d0801051c02010503160c0f0f0204060b09010e0d0f0b07110f0a020906010302070c1e0816140111071206322a0427 59
    0x803220100b040755014041c405144040056084401e0715007101003407500380740c11742860000325158010005030800c84030391050074460040c214001e1a40360000390079480060b041180300704000602e40c02040c41211404070190b0f200c0e41250780841103060101d4441a0390b03005a1041e0724084001681c5054801101c101c1c10040c0c40741c48151100300104052a0f80c040016941e03621740c50545070005030592045445400540c85c1c00708452000d40c0841e01d450011088202c182d4069100900581d0760809016440503007440c0c0540e4440300c610b00300f010510283c2c8101c01504d4007c840f0403100c240c221980090f5001c5501b11419504501039068010b01d59205056440c00320b803c800c401544121949000c0000000481d41c04c42c1e41c940c02d64044035843c20041d18195911000e5480ca9500c00808130401c0e2211602d03440315480007246440104006407104800143c6415203507049080c42150790941320690000f9510769a54034801440c4545a40a507100941105565091441d242c410b140743e200d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 930743039 1250 930741789 930741793
    0x207031d09251101022b060b0304060b040f1e0b0d0c0302062a0c15070b060415030f060c02060112080a0f0908031303020a0f230103020c060a0e06010611 67
    0x22140b10811440c200220301014100181e0782e02c01c2141d840c09000410000c41080303140c1c90102500c01c00c54120f991a80340d0658180d05007031013041410051400d0340e4103e5000b0400080c0c0304a0040024010100c42420714041410301c1c500c04a905600c100c0b45010a511400502c40c103c042020800c0304510168010400300d20704005102504014000e4450810460b62054625142034030200078100ba04d03201c1950f561261040000604211300d60300c540850440c90b1904210b0103644e000c031900341c0200381034041c0baa10070841d0f0703011424080700b80c015a00111180b441010b0b609156014000d80d00d074a10151140d5400020310b4481c6114603541140c0203002541070403401042100d1448944040300200040b080010411540a000901c001701c10241100d03009031461040c050b4080c0250700c08003555840f07080401c100c101840400c0000090340290b0742142800c000141d000b17001f549490a101e2090f80100102c500c0340e6405640c90001040407030340e86d683d0300e1008803a2500c080a4112240d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 930744289 1250 930743039 930743071
    0x180503030c07030e09180d0305190c050f0d020702030d2c042012070e03070b09031501170c0d0f030c030c080f0d060f05220f0207031d09 60
    0x400078280141c210030b407003490042c841c00d82040002d402c000c02a107002e189101d40a400c4020b940f0100a000070f42ca03800e04040c031691030f11028400141010a99002ba00c580f29121016041d100343c00b10b07071113051035100942d103030307001d04262070025000490128081d00c200402070a00314011100c082c9941500200c00c0c225903400b803103200c2c6642e0a103070f81a4000e0703210014800410721012040500f421402e05003501c0315090440d0003807000c405415130342400b82c0c1707208560300c035100030540c0c070160b030114041070750784040d054042803620942000c9165580e8500c2c00100701e211503025082a003400e00c01c02c5541856100041100302c1c1c0422a00600c440315220303c40001a01610040e801d290280c101500e0341d46030790b00c8901850b407020794050019100045c60304403202003072241501074071000c1c80e14003205041c0300204260044541d000e4421078552811142c7c1d0700c445402c00c882d0b0109418095495030030b54600900030300c2c0c0d01428144940141082c080c0c0900340044064403c0307005603210020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 930745539 1250 930744289 930744301
    0x607020d06090609060207061a0f0402070503190e010206072c030a02030a0308100b160615081902040c051c110c010e0601060807051206041104080a120318050303 71
    0xc5203105081215219282c4040002184040c0320381843c180c0105400b690703a0b4905d00e0910b040342c01c0483e5422445058101c10300349070b04d07106000b4080700c03c00e4400607540d014a080c010310b94090031440d10b072441c4807018103020084d400f0402c0f14404600380c08460075625283c00640c0c012065a00e2643d4466822141883c5a091104103101c003140250a842c2c10248075004a401c108103403c0075000b06070240284403405c802000c0034001841501c0807a0b00b84080c10203810407610200304041c080a80300c1c8032240400c140540c0e41401003594008480e290515000152002c180c07005050f4070492130207921000e100c0c0120f0445d0042051201c500007109900c4448000070640d90402c040b5008052080020103042413003001c0c002c45100000b480150f140c0702d001030420500074143c0041010900030b041780940030456540d042003084030046025800c200145010740640d60003034485224919200003402220782c4010f90300019a9001c0c00641381100008000640b20034001741581c0c4104001a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 930746789 1250 930745539 930745549
    0x170a0f0f060c2a080d0507080906070c05120c2506171306111c0506040501050126060f0d03080603061008030906090f06120f1e06010f03090b01090b1e060702 69
    0x20018404c0d09500d0500700154001d40c00c0350811152000422001d40520202c008204200341c0d000500340f91244034401c482c0c0e0b45644984800500fa074106101088011002c0828041101e00d0441a45100c02c030f03062400d41c0302a4101148a2003012400d07941d1407155003040c045c18513116016210001840b1986a52040005c0c0070b580c00c512000310b0248141c45045109441400302e0744251100800c1c2d5062080c2013008655060b4405414007a40c8042c1108050541002b0180b0801c40713820303c1c182d03503141e2001c180c0881190154643c401d202d0b5503104105501301c0c0445003d41e00581c110354031555624010794076505075009071010340e4410b0204070b2061400c6402000e0b4050040c6c4460f0625681d200800d2080e00206044000d540c641c1d010821107480c8000544da000725044c46d008404050320070010000207016000a04000e110b203e43e8444c82d002e9000020807130392045e2a00100d6130b40c2c04071000105000446203202c2c1c551100c0c180045140b0100c414200302c0300500b17440c1740403480d40c2048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 930748039 1250 930746789 930746867
    0xb060906090f04150501090609050618160203041a18010f0518040216060605010206070305041e0f0c06091412250f080618010e0601170a0f0f060c 64
    0x80301c00d113100c040080d5008803401224024a598400480c0260400f0f9000d0152900105101d0141115041381020003240003643c540082e0b02c05000c03107a090500070200d0940c4110340004050418001d904202e0b0031f5104010156559004508510b0410305001160007000c10000140005d409203c00100600810b0801d004800010001450020003401a80300008070a0f0142e440c25901c0d4804c21081d40c05220880d80445c02c0c5c50300304080d261a9442d16280c841c40307101d4140300740e10b492000c002c11885120740c0c211560004444070b101a0394a100070211005400f45405113141c02c40303040e00c00d084c80c01460001c070301114045c02c16200d41d004483c4021803020b0816901c41411100010000c403c1e110385005841c410f0701405052900c120f501d8041c8245581501180e854001c501444203c0468017038159032150b004140700848500c41d9a01d4075500102c00b501c0c0c000043d13801c10810450b003042200b080e20504c024000c46032810703000e41d03110382c54005d18000d1201d40420841621860000c0d2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 930749289 1250 930748039 930748043
    0x20c01080c0a091a120916030b0a180c033324090c0206131e2102030d0b060903191b0b0913020f0421080c0a0b060906090f04 55
    0x4a03481e5603130b12070310114400301140240c801000010b0f01940d40d6480041141d01070030b800c00411071600c100c000a21607110610019003040c00010203d112412a40c0228101e42860342c8402615100c1e42400100d26245e8481281c255644445c103119965841060607001683c21503514101554810810007900c0c170090580d03150580845e541c614500210042805880c0b0f90304002840c0e81100c6000c0e24106001e8044415491301d241c464001550301341c1040103101c10410400380c070308602d2a25040d031803c0312100c0c10361440d803103500780c80080c4c0c0003002e400c4444c0c8030003044c0605038190301400141d00c41d040707130690036800041510303500c40c500040d4130032000d205d08461200c188074400b20307160f174a8882d00040465103000a030a08180781981c000045000f54240440c50894180814200c910992080b4009081350651040c40080000801d100454116402564070303605c0076040364660014202c2103075007840380c0000c508a818900032031ba10503a03025182580c1500c80048450903008010b2007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 930750539 1250 930749289 930749297
    0x103150f0c0c060515100f030e2d1c05130b0403021f1232010e060d1403070804030c08060705040308091f020d02010e01050f0c071e2001020c01080c0a 66
    0x1170200741d500c03085507250b0b9510311607941c1a020300456900030b043d2009400f101075164800300c80b00803c018200020350030840c80740342d02090134030f021203e070303003881c55102e004141d80c41d480000e103c0581e0458020300f139900076070444c0545503131945041000d82c016030002a41091200d07811510031f20800e20300002c001402e04114546110002a400940340c3d2040500144a50b0300a048800310100303003110000010110b070402198100928041070324001072040d40308024403240301d0180700a80c0650200300004a082c0d03a038400b0141001e04181e171203884201d030b004003035120008074014040b800314000d03c2c50f1341d545441e140c515181e0348140e0300001c50640d40008184078004002c8150110280c80b1030164022300542076040c8000390071030714418200b0506034100410400c100700c0124840e54808801c1e6a070549500545c101402d0344900808112254000d80d0380000170303c51203541c4242c0003421717415101000c50140004985130000804038038007143e07442c004110840300316005040050030b43d01c0c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 930751789 1250 930750539 930750571
    0x504030803090318010804111903050a0b07110f03030105011d040e010504140c011b0305211f080a02040b040f0911031510090c05120103150f0c0c0605 66
    0x452a103564000d40c2c0b004032a03070000800e003203200043c1310381d5015075a00742400c2d400761410f0303180c0c002040e0500c00c3e0241300c1d200580c41103c0c9405040e600c18081c5411a04451032000309250250340b0503001d0b14413001245031900b0441003c1c0e0001541220404800c000d0360940c3d00e040010342c1c94018081000380040038a6071040c48a440e2841003100003072110001141c40e080904103242e648174101d81408181c0c00160200d22140d8010040800036143d41040410003003040c00d0844040c081d4075210320401c4814a00c0441c100c4454400d50300450882d0b0110610a4050740c11112482e07141c41680203c0d002680c441300035140580c0301144958001c1d00100c1c2901d04250014102c0780d402404a507081c40c40403114185040810950600c2814200e884a40d41010b20714500461000c0c4110b14407252550404102148680d09440f1070600c80070440030035584038034016990000e4540c1c0d03001c0683c580b643d0190400038074054111018903507110600900120344800c00035040c000c1c40d104410300101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 930753039 1250 930751789 930751793
    0x30e0a061a090a02160803060d060903020a0b06190603231323120309010905070605030a140c0307050a030605060d0b031903020c04020d150906080106060305010317030403050403 78
    0xc0500c0e90105044101c003508034407a1420058080005002d00c1d90729881441620200c040c106030004006800060b00c0b40c0702d680e50000100d4100a801d0020000d5003800d04100815030000381400d01a4490640115280d49010901c0100d00c12300f81007000c4d6251024040040034002c0c0d0008030a40800d04008501503e00d83c03003090001c2d0161042e04401601c4031528040c4452100c05004580c0c3c0e4080c6503d0741d040040b1030710303a190503200306041400700010225020303910940c09400c0c520791050a40d154290380b4039016282c0e03002120455006401d00c40700400d80423200710b00b603210705a000c15240c11505d900c0002c9840d504641c09110070b1507500c100204081e130300c100c06080c04031703084500824131240d10350906040101d9101802e1500001e1850300b40000c0e008504458103010554005031118003618040c0003070f014502088502480360f510100b001602a005001070f07400391002481069540c1c201101203d4092201514802c107000542c80c02c50718420045421900a24100e07003032a40729 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 930754289 1250 930753039 930753041
    0xb01052712010e0703230604080307030506030d0c0809130e06090d020303041703150904140601080a0c17070b13090c0306140d080c0d080604110301060c03030e0a06 72
    0x486500140020444044400d62601c1c58140001100d080700a0100b00d289411844d0f0314605800010300103901c140030000c0d60381070740704000e0510703800100325030650502d801c102c0320550050f03e01c1000a401c102c00205a0b0500080307403400580c1541d81c0d5401e400e00c5031602c1e05141c1001c106998480c11200310903114012a01a4604040540001d0181400e15045643c6000114141c64082d90014400c00c004220a0800380001000c0500d43d527580350790300c5003650300403003060380241d6000d8000024401801409900c07012281401303c2241c44990b00d07107c5203580d94000020003040d4104480080c005031a1000009039118545404c0320f070400e07200d8030b588009401142800e02500c0c4005070400026174070b80182d9840c110642400c001030b500340000e2851644c0101103217405050008000780810203040100c41c1424110800d5818902c10003100815903441034400511482c20082035140c020360020850b03048840341e4480e54010f8030350313540c15000360481240c070280601914200001003103c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 930755395 1106 930754289 930754327
    0x70b1906080715030c0f180306020c030304030305060a080a080c0a051207171303030c0c0e071205100b161406160f030501080c1e1302040f09050601080a0b0105 70
    0x1007040c5054200d1f00c0303510017005a840013034140040c0c58007001550045100795000d0100340c50380010407000e00d500d070050865607041441c07408001400c8400403c40444080240c80074a4815140c480c107102c0d2008090f07003002e90000d601c80410105581d84070315242d16003e1103003800380320964000310158a000c000c3c28000c94104050900800103410740040900b049400b1141ca4894001407100e6401d214107c1d541c0e00702000710700030b4540180c411080e2681e0b158070a0403c154400c80c400302104045054034025000300c82038003440410301a60380300701c2e040f022004171030b0300a050003002441e8440040c0105440e0a0050200c1900411420071691080f295411004440340e184113808003400d0341640d019010005c00311440744660080d208850307103e48440da140e6074402c15001075810880300107002640010018219980e20760120030319507010b1411a00b094005108031801200d = true := by decide +kernel

theorem cover : BRFrame.Cov 930575539 930755395 := by
  have h0 := BRFrame.cov_init 930575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 930575539 ≤ n) (h2 : n < 930755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
