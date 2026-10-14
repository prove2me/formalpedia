-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3688
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:23:32.304241+00:00
-- url     : https://prove2.me/submissions/392ed159-7cb1-4eeb-b95f-9dbf8a2efb4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 663129496 ≤ n < 663309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 663130746 1250 663129496 663129521
    0x3090f1e06161701150e042307110a050a120e0105190c02060304030806091b09061303050723010f140921100e1203061e03010203241e04 60
    0x1008104001e0418402c40342c0c000d00d4820f14800e82e40c005d605001c0d041c0c14601c99442d0140b81016002200244008400e401106c038044004485a48880044650f80f44801e4401d8080c068200b0203402d2040016000206c0382c000c0600b030047c1010303000141c070b4814280141a01140301408440040341104c40941c24200d02802c01c00d0200c04540c2c0010859401218202c011030b00800520106048c506c1c00c056000c42d05115021441040e0307068400d190081d90000c07842030310000380d10301803032805004003c000e40c1d000041780c40e003d0b00d641caa58409543c503101d0290703030005814410981d61049024041110842c0c42d900c0d0800c0302140e030702600e40c0c0308107807098110314605403110340c150414400c91889080080a07040400c050b02154080c0e03840300c00385840c0d6505c00240801d00114000499410440480c0c114840ea000d40e222403599a0085803141c0e03040d40301204025800c0c1040021400c001182c00e08940c070f5460b454100b0119502d400c17070582d18416030440c2c100e55404c09912884e60703410b1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 663131996 1250 663130746 663130757
    0x1a0d060204031a150d0c090e0c03010e0607020f0d0807080a02091302041703040e0f07021005040b0402010e10022107142116060209130203090f1e0616 66
    0x3240d4450165540d100103421030503102580c20008911881c0040d040c92913021a400f2950300f659460b000a2141c140c0144184035a841002c500f085d00e0400c110301403580040c00a100000000c001261071741d00c02c03a0340c1805401351443d005c860300782c08900d44400705a15159101c00b03840d02401244c822000034a100c8050b5800c000c070300703407a42d628044410308202c850f9000d13039140d0500240e840b1480f20b00e12113403000e600c184418842000903000090780701011341c140c1030166030366003400c03440c280602d603138070020380d02d40710030f01c414440d83c400031a21483c002e0301c90400c04c04000d410b0000743e062000d0144016081810600a601003000130707001564004030011b420320002c0e468035040c1c0401400258810341c01441d04150b001e40c00c0b100520100007000403107081030a04000340d4903101d040d000c001c0141d680051200300587d9007a80702ea4180300c1000c011508e0b481c0646c030032940c80c0000d6841000030300c01c90481400c038000070058500c0e5402c024000d041c15840d48902004c4603200d00e080034041c000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 663133246 1250 663131996 663131999
    0x90b040603050a050d031d070b0d090803132918070b0406020601030b0c0a05041202270a0f0209060409150509040c090c0203070201090303050a0c02060f0a11011a0d060204 75
    0x2c504025000d1902d001c1c40c05010f0000580030042c1c100c1d501e81c0b4004000400b2017030040703002c4002096980c2103030440341050307a8420100410000a0110a8000742600d60100510860011564a941d0390300e202d207070302403101041c030000da070610000d900e038440f554181d078400102415011850521802c1d0004102e8155a4490302c010b00e542e00260805001680408010014400792490003900541020041450b01c1c1c01c40c00300404602c2240900020380303200d854180215100c081044c0c64025022124074540d2003e01c1c400c64100c0010740b0a609080d04020b844118070885200b25142c5c0000180120701c0d1038031300004035024081c0806240812402ca5400281d43c0d180c040c00c281c4a28407031000600d0385810f2105900884008603c0e08086510a01c000300050b40c00c00c80c4041903a8140c00e110341c880d000704070100ca505140e020025044040030801a604495000241c072903450107440d0112146490340006080b07513242091141e0804100c0b0700c0d001d0f2418040c001844160203100c000d49443d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 663134496 1250 663133246 663133253
    0x26010f14220b010810140915090f071d0702010b010801052e0c05070b0702061c150f05010201060509090307030c0201120203040b011d040b010b1c05010803030117070b0301090b040603 80
    0x110090348203040a80240200c3e040342d05c81841015851454081e09070b48504107682a0b0b0764600341542c9190002e00c244010441d50801002200c90740140041150707400e580f40d20324007068514400040002c2038241022031013050060182e400441d0040c0e541c0081c0d60705c0d000070080a440002d8894032001c8c0104400e048440402000060300c0b43d0503190040c0000851410502d466516448003100d003509021101c0140d031540221209841400443c054120b000311404000704943e01d40700c0f1003031049200026080e42c81c080c2c080c1c11110260001c010496a807001d01510f48070407546011107402c100110742c0068051800303080c0040c018903000c650110541308010899000b60b600b81e5916214400400c041c80b00c0381410810b01c1c4401090b4051803e141c1d958500404040c0507100003054080380081007032403411035440c01c013920020305200ca941d6078141c4030307200e40c8203004c2e404120840c6800800001c0340040d504007200e24051406145a107044200c0001f0701b4198100b590054840c0f5002012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 663135746 1250 663134496 663134513
    0x240d0602040902090a210609020a1806030606060c030e15130807090f09030f03240b0409050105010309080f0a030f050f160206010812030a0626010f1422 67
    0x9000b00200040c0d40b04844401c0042c003807116400074484540d550300d017514021840c40c2e0f050140d94003144c0410800c01034400980c0c581c0854002a05980314410f40c8104403070550040012240150f07402c00c20300e5203030003007103c202d4081032000d400310741c0341d541c2c3d11070314108155150b1803511402c858604000028154294000281d44856856070200505102c550200d1050185440d69070104001c0c5048070b99014240780740305882141819607842e582810000900c4d1403d444403801c120700c050440e110250364100b03801500803007030014506400070601d940280314541029411001850525190959000c80c0754080403d00c42056291301c6040031444079801018064401c01009070000e00c2c00794445400035245030034400c01c5611a0004015038440480c070803c41402805165641c1c0c0e85042450014100b2980f020200040a18500442c072000e003a04400108030b140003404503409000502081d20b01c0c0d145485801c6070340a0110390300300c45d049880c086644e01501445507045142c3c07620b022 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 663136996 1250 663135746 663135749
    0x30102030c070501050106020624010e10030204080105010f08031b030408010f0209101e0c030e03030703020f060c0a020303071b0204050f15060403170304150e03071a240d060204 78
    0x10140c0780480d400c4100682030092601502d0184000d0070586041840c01702b0504855020400e4400104450030041c0d2050480711107a0b0405040d045460500c481e00500035880b61042400d2946081c001041031b025500c0c01c1750444650b038004600b41845030942015201074134100b0042d41c80300f00000070310b0790001c4c051500ca29618400041c0c4078070400c17003409401401d01640768100301b00c651404400a034000c002440101303480c070b00b0148a00641c40c0945441c0e000e600d000ba854840801d080041550001c3c2d1205002c5210b01641c80344d4588104224181c080d106020025800600000301600c0c880d8030740f00c1181c8000350300710030014502e80220f8110380c0d090b650700f81400980c40c1008003d601d800d00340f9111890030b40b502da24180c41c40d00c50310391081026401003e540c50000104044c040420b1f600c048848040a0801c040502d00e03a41c0c2d5525400214101c4580d8110842540408846001c081c400c24100c2010040a81c00074208504545911807055102c0c4680440340040341c0c0d603101920 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 663138246 1250 663136996 663137011
    0x30f050601090c030213150504050415061b1a04240c020705010f050f160b0906010305010f020301081510170309030705030a150b0d080d0209010e040b100507080903010203 75
    0x200c0d550410302a40103403040a208042414010050014119a5088490304a50100c04220031007183e07500c0c11505441940c0c4240e50103400d001c40c08012040120b07814046603e913444aa10219038046545508481288042c0c058040100d1600c070000013168402d40c8076206402c1c0210900504403050f440d44140d24031049010781d500c0090b40401c1d010000071300074010034204010300801e01b610040c0305100d0140380c040002c2c00403450801d0164085091240c5d12b42c00716018206181505015940701c20901c0252450343c02c000921451082503c200da058812100c040d00024070114041c0c0403031070001e000100041c8102800103200c0424034408161090603038003840c0d560160f41e040514104042d045a8803c0e00600d1071040082c0003119820700b0903a10390008910300c6d98800000f8460b084002028010035800582c4100f40e45899000340124042600c1d612003040241081c0b000b00e810741c04203660002e8448071541c000a0045028000c41e238810b5441a10700394890780442e0070390f00240c8010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 663139496 1250 663138246 663138253
    0x813170c0901060e100e120304030305070b0c0301140907021c03060806061509010f2a02091506030705070f0f0302030405090a0c1409011b0c08101e020c07030f05 71
    0xc0000346800701c0020700400d854901202c0c400e4980c2e0000e00424600070841080c010f207484c01c00c2190302c0b40941c180c10b042001060303c0e200d0356242005001540724450849500e001900000e01071902c600036281640d0801ca0780c1d41022500c001404500100030b4000307410740c404d290308141068200680032141040b10784d00840ca00b454004013914250002d8403513031194031191020351031000004244d03040c0403002d2801001c0c03404400c00a82e64184061001c44610801d14010080d1399905040550b009100391449042070781d0b101e031201c1125099201d81d0313a00c444100f0200d600300303100b000a001124052491100d51748100c1e55542a2021500001c0300507810202e406c00c12442c001c1c4806900824401c0c1c244500592080001e210494056900c1d505940100b02c003d1903900c1000c2d074101500c080000300350303c0704060619024401541c0304c1c1c410544a4104000800c1c07140340140b00b02440710300d280303912081401e41c0240c003940003001c4480c440e2203828000408192044040440140a240907 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 663140746 1250 663139496 663139513
    0x5130f050a080a0b070e01090902030906070f0201090b0105090c09060d050621150a0207051b041b201906090303050f0609060d0c0902070614090105070c081317 70
    0x9200300780001d50700c01500da400c03844a0700c02007016000300d540d0283c200c1c90240200750989005885680f082e4000000c100c0c0302108020703440400142c0d40340540341a07101c0340f00500458404a00fa115503980003403d50000b5001000ac5003001680719401002500841e41402d00320000300740a83c00101410188503101d00c1805030504250320180701c100580b9095090079850b550f080d43e62400781d0602c405107084604006207400c2c045505862143e607204098800503503049650085014a201926200d00d280c9408180414158041e8120b03c0041e034491000c009166605294180f0820418052a00a0341070700c0742c131480000300401d881d511070038001541c2c40550030024101c0340014022040c00301407500307002e140da96a9540c5a4014001c4403088414003c170f191230201030109500c90101c003800403a44c83d0402009802030080a11592543d000964800f202e06003070351400c0d03804402042c90500703210080f070b88080040071144901024030806a5403070340b440718131074100000710400d5000400d0707 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 663141996 1250 663140746 663140749
    0x30617030316080103020a0b03040213060801150b0c070905090a02041b120506010e1306080714041506051c15060e041a0906040e0c06070308040c06030c12090305130f05 74
    0x42c81002c0440d260242c0c59604641c0820040081d902074a4005400840010110f503660180d42d806410000002d00040ea991100b5902030692581c1840700c4102e07450f00450512400340580710801d0260b0000c0180b6481e00114400801d800391060900d4004c1507c001c0141e251760180c0701000301580c0d5065480c441541005101c402406017901c0001c0c148424840d05030703403180f200c121802080b103400c965000084030381c100070010381e4000c8501c0c0c0100c547c00103c1010401036544401c030180c5050251303c80c4420781c000d6164050040f500410340c1400303c80080c001c1240381c40d80541d01380f100000c10705080d540162447d440790b4000c5001464035195000c85082c1401844c0c110482e80000d01c030390300880740004811010091100e4011030b07840446404a401c20001c0ea01000c5003d0b04040d903810b560b04004115000840f010b4555481c000000111248603200d0011103000f03d5884038100901c40f10b10801820200d103050f401c0202c10b010f441e0081c181030301c01e4170081c6008075810300350074602030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 663143246 1250 663141996 663142021
    0x303010f1e03080405010818060c190c12050307020f071203111b091b0c1005130308010501390203190314090a0312020c03011116120306170303 63
    0x8a00896200d08200300048010041e00d01781c490900309071300c01c3d1352401a09060000e0b0104a41e04a02c5084244890060143c1c0200030205e140b1a007450702030003006082d1038100100d000145580d2074081c50300c070706a1091010b940c00c9002441516803440349040381070310f0001c80c0e400c0066907a0111040e841015005411804013100a20150a00902540403105103d6804901d54051803405d40090300009011078030820700101200000e445140b01d4080360b9840c042c90041041749440d040128a801620f174003410750f03103035050f510322025078280001128842180701040e4022890040f18480a010010099a070300b44030042c501c198601e00c5c01014500303400c001c2c0c401550142418004082588081c040703003040c00301ea0300e040d41c9800c00c80c045849086190700140840d03980100b00c240703082d8040758070403000c01c0c220024824101410f01d29801e6100d0308044852804043c000d500014491030404800350b480ca00f000143d0540e0303011400f01c0b80300124602e11080c6c01c001b041004511040c07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 663144496 1250 663143246 663143279
    0x3030e0601030b0f061e0103152304111611030a06061203030c03060b22091107060b0405010b090f120303010803040303090806061014070f0f11040b010906030b0607050303010f 77
    0x445000000418041900c410034600310b2206e4105915807034440c0d80781d00e01c0f0440000800c01d82c0031000034400418152207a0301e0240c444039101c0c81c24030280811740399100c81035407589034020400322007a45d4140e9074080703069410541150140200746801001c60014801c040c02040b0380300481040401d11320f8000c04480e01070041c0002d0510308a0305005104403c4181e808401642c1078140903240340182850342d00d5020b5104401c685d040043d49459220903001801005110704814006d03816480204015140e0074080c0c1c000d900c10502c00081e007490941c3c4a03040084002d000c0100c1070000a50043c199031098000e4141940002010001c0541c4251810010321448000d4840342c00c00600041c4610707080803409041208800b00000f001504074200d42c80190322810b01c0307801c41d20601d41140e016619000541700c0c00c07110284602e103030400307008842502e24141d403030260844c1070030400c0c0c0082c6036070006150016018820300300056002c00046020700504414464418031300004c46c0604000c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 663145746 1250 663144496 663144499
    0x4062d09031103210a090801020d0e0706080105090609040f17091c0c0504020a02121c06080a0b01051e060d0f0b12031e0706020a0c021c020901090903030e0601030b0f06 74
    0x2c1601401344009014001e000c294804131a40e15461103100302c407400c00540240707459501c0014210908507596112482c1e40c0b10007015a030100d5554041562003500c00d2241c242c001c604000024264508004610b510500c47d90340280c45020b6910b0380c160724120200031603010480003030080c1940c1f4001e04d800400c190130100002e00101b480e583c004080c0803a104250056402140e00300103a0700a1141d003000d46100306810351910318103640300101002c08400d42a100c2d213003c0f400301c1c50701e90105482e0409608043c602e100c607480e0001f1b010700d203003000142d0760001c0410490b06480755240d0303008008240803624042802c444904018080310503d050003441244821140400400040151042503d43c1200d0503a821580d011f02c884900c02c186008080910002c5d034019080e0b00602c0c520f59241c000da0f07081d0701c1c00891542c410300d92200090003035480044040100100d4503a50400c0c81450304c02d181c0800d4003040800ca241c90710400f03820895120940300108801074912140f0603a00400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 663146996 1250 663145746 663145753
    0xc0f0c0303040c0314030c1b0a0e070e010f030b06070210020c04090f1109010e0403080a1d030c0105010b0a0c02040e0307020a030b04060e030a0509010309110a1815080304062d09031103 81
    0x1f9252846944400340050419084040c880e0305800d940c07080b041400400d08000c41d03000314600818028007522807208494003003240c9010681d4060f10030b2054480c800c00127080c45291206980030070503100039a40d80241144500c0010495944550103001c050500c9420090552a0945890b00074041d020401d580102c045200410014400b003107186c0d0130131381509011340c071500c4540c0108007a1000b489110b4414104201e450b00b40c0f000040100b000d45140300003001030340d883da102c80304140b084172100000240f502c804a00503180c65400340040403a2401200e1500c61240d000c00c0402100b60700c1643c900d60070320704101c24000c85004110f80c0f4a80c500245207409820500680381d8022009a80c2c10076503a04500c0d401c100009400c920060001404130080590f01c01c80525a8605440d50300055030a20302c55803c201041100745040e60250350145060a043c0007048540c030005a0303c1c08a0b500401c40c0d068000d22045407215000b03031403940c507100e069065003402107860301e040403094002d60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 663148246 1250 663146996 663147007
    0x624040812071205030901020405061c0c140912010209030609010b120313180f050a02040f051207031b03120201090605061c060b1824010203040b030c0f0c0303040c031403 75
    0x4120f94083c2412a4280c00c0480c0c483c0c55911070240240074580241d900b100c0002485a0700040b04402d48001c0000075a091110040805044442c401d06103080700300308905200c81440e5140c4481901000c1204070001420000b20200284c9001340c207680c40c0c402659036524002107401c1100e0390000600340d144c0154a0f110780c00040d003155120fa480754041e04100104856402c1031581c101111030040100c003401141404203241c03009500500c141001045a0100020705060042d81300c9071407080710014005403480c1d91140061100b2060109820000494021001901c50300d640d024040e03181d0300000f40b03040c541c6008000c645000e0201351091490200d4041d28403014203070380340281c1e40280c000c10880c1009000c00d480021616054040d818a6810042204056510307410f50006841d0304081c0728640e01c0042e84c136445a030291a100800c1000001c0c1c3c2d9245510040610f00e01a80c0310500d0100074140a50030340c1c00940c3c2c00c541065000d40c0c01c00c1408070400e0489494042c61780650710b0207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 663149496 1250 663148246 663148253
    0xd021c0318061b08160317090d080f090a0c081f090f0620070807050c100804060e0c0a030305031803040f1e080a0302060f1302010801030209062404081207 68
    0x7440e080e218141c0740700f841c40d2031010425083c06603180039603c411180300010b0a8540645111800f624020712400007500089080c080021241e0340d0084507200c10307180761a000141d00805400400c40a010300c1a280008000313503d1102e000010300419001c1c0040160300300a0884026903809141862030400a001d004110b00d2900d031142c1b02d90081c40016000718164408104029503240031019100c042010801d00010348000d1900500c9541075032161410704c03040008800d01c00ca140740008424000190005100f5480b401404c5843c1c012244021250400140e407141d007038000b10009600401400f2454030303017143c442c850084020217103040605001100c10602c04501c140380c50014410510b040091101109034003802180c0165204040b25040203541c0311419100e000d5031001310b000017107461000c0c4140d01d401540c16520700c0416480e640801120400c081c0940307a100c41a02c1d00c207840100d01040d1410b65210103105141c4491601000c64204000a003103001402010404130300003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 663150746 1250 663149496 663149507
    0x70b070b0105030622060b100201060303090e040c050d05070801020d0b03060603060412030c0909060e0403200d050702030c210712120305090307172808070e0d021c031806 75
    0x101c4004100740c254402411b00390051301c07038601919040404202d0b09007030154190003442c1641e0094681c0b8400039500c1004030040f0108844c0544030514400c0c042c000c51408003c900141c0707000388203c402e070503110690f00d42203901c8088485a10b6599080300195410140310030b6520031801c81c007074443ca00c0d00c2e44403c1084484082e01c00c0c101a92400c90002007405240003401600703c4031410000c103a2281c249040400040d80d0aa000c9007810b403041241d070344041d103d082440340d44005840c8a4540001c01c5d1802d4103d80022a030600540c00c40d0221525480700c10b0039071311440d20b1856510801911074034141800d84c2c1000000054090191002c102c4c10f0300e0004146d113043ca00016150790ba55505421402240401031400e4a0a565148803001c11030141a18001d0903030b60010710f040d4511694950500b03400c0320350124656074005141075010350300716413010314041d101480a021941c0080c0c42c1800d540e18a200b0201982040c1040c5a8414101480828030b84100f107101d0781007040c098030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 663151996 1250 663150746 663150781
    0x901090903080c1b06130302070b0a17070c201e0306240a0305030909060409020102100b040f020c011a10091701060b0a051c180b06030f070b070b01050306 68
    0x822503001a00c8520340c40c1c0c42c4c0c0e04d603101100e030340180d45080c10000228420700306a07000950040c49034a00110b04a1940811140c0f04034060b160150507141f00001c2c50361040008020720103100641d0f00200200311a904035810b01e64610805400d094141c80400040b001e81c10606546200c020320720301455240020040d03003004a0040030507100c502580c6200c0c000283d0603010b500f040c2040c0000082000c0000a004000741c07c070381e510890b5803904103200072500040c1d00680140d003c514441d20042d2954410480720901510200741c0384010030a04099900c2001c113111a07279528482d03800350407010780080212207421110503c0004c845017008081e06c82ca80241d412840000d15240010002580000010940c6592030f944607482400058000d400c1949101e10346007541c0c02100c07401140740b16007120401c00007038a0a04001903240d0f1440b2080003800d65401d4411280242a401030400c40540209404010380b07581d02c0243ca0204141141a80000c2c0254402c1c824055128100d00a480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 663153246 1250 663151996 663152011
    0x100e061306020c0c210114040c09050615160605150303120c12010e060909070e011703090901030605100e060619032009031b060a0e0312040b0306090109090308 70
    0x607100e0480070112804c0500340840144c0c4100c0521500e41204440800d041050602100802031400500006090310380111002003084244810901c00d0008c2540542d4011401400203d40050404480c04543c0e01070305065006501c040c500710100300c00c03401465400402d10701424407140042c0c010070b549010f41c0060b0079102e0003d40015010742d00070000d071403007402480c00030001942c1d51903081001c0401503075594000c0e841c040004203649400605c1008403a0300c0c8070a000303640e18011000c4070100c40702045c2c00c0c0a0100300100842503640d001800d02035400307100c000683d401c05031b404008480780d643c0024108181042000810f540b40c10035960154642d0444100c50a0301010031001002d800040215100301040325400071074104000e050301e4402a0100c404100c4483c407000c000d0080200c0d059032003a002c001281a480c81111201075000010f01110800c040030b038000c04c03a80c0c1044c4c00c403901c01c010110402a8918020310310714010141c4040030400d01609450040403c90001c000c503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 663154496 1250 663153246 663153251
    0x903120e190308072102150c04081b091f0902030a020705010510140616080901052a0721060515060c100f1404030c0501021605100e061306 61
    0x119040d4445a40d801da001d00c840041218603610391a040c80319400604003034403a180c210807904980707549a26a0003a00001c5d4004000380c0100310b1400b6802a001482e079901c15100f8440000c040c1c000704001c805a040d54408a46581d0441d418090264801040d01d01208042c10068100c4c0040910000076540c00c003401580d2655840c2650000e4402d0650040c5298a86020851070810350340151054030b998403038060501150000300f01c207a008410344d600d09408040080780005443d0001046444018101242494411140d40703442c0090b13503075049103401c045080b45038601c034144079680c050020007003d501e958a00e203003000b0740c0c80d208400c001c00142d0b4500210b01224101001d407114508020602c1e42e8401003004160f4482c07012500c08801c03d81411040a141500d40c02600031424400d00c1590302c035501c40d101182c03521051030080e2610b5500b001020074203810816424801e40c0580c0c01041002c41c140b03141750440b00806c02c0300a0300e802031428002c01d941207540160b021504244003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 663155746 1250 663154496 663154517
    0x110d0905150c01110c060601020709020306030c04270c060905090c16030e3a020102060415180b340509010e0315090f0601150305091c0816090312 64
    0x80c20f0040205402061240c10301141c108900e01e0300181851040e40d00781d003940c8000d80d5510302c1c9810fa01081d81c40952540000d00041e40a0230990b0141d152030fa4401c400c280c90841004001e8010940f6140603202d400269505015098100c0c044000820058a0624075803070860543c10a80c01a44404a030900c0408a440141803048070017036803590004103004280e4008549a1140c03074071124420040c00340015108414070025502c01400f9a0180c01401e82c90f60740d83d5070a600703100001c021450080d600c800060240e80010108082d5502c82e0380502501e0a1800b6002d4081e102e4400c5d8115182030b0100c80c2082d5044044002e40142040c1480350702c8001180050320020500c00e00781c5e42601c5898560022000c981403d1130040f81c0c02419031304071222103d03a0030b80341d190074002d1030000c02203d80c650001d0b40c0309030700540e03002c0d08690654000e548440702e00010051543c03d00c1d00007a00c840103101c14000c0545800c0c680c2074140c10029041071456440208442c1a00d05d0f4130103000140e41d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 663156996 1250 663155746 663155767
    0x1170618060f10030509160326040306050907090506040902030a11060d020c010207060e0a170f040321090f03050c060a090807080304140d1a0a1b110d090515 69
    0x100b9207214400180a00115101480c00400814049514200d1486541a40d80000124403800420740b40c103c040d00325014851515883c2c102d0601c1c02086410008000c00804103102e403003414040c4640001800d005480d01c10240c081d00d4000e082d00344540d00c0d040380400141e400003808400603911121031191a0300420014040703004999001c0419400007078080b6240a040d4010701d5407911900082000700e1000c6040f5070f0b01e0141c054018412104918400c0350981840041c0c2190007040500e24585512591000c01000c50980d442d034000088507400c0c0c60311038121507058054040f0100070118580313141c450507507440000c09400d000340c00c0020100c1106200301410801350452904440003160f452140329601e6000f4495082d004040c2d00d102c0d07426150007061030300c10940045100c00a850200c1d08801c040c0f101611a160141d601e9505501c91490070a821801d900a5201c1400e01c1402503110350410816030824010003c0a103230601255072030840440e109003543c03a0481d105e150381207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 663158246 1250 663156996 663157009
    0x909150316081204150302070c050a03080d05060303090105070b060a0e2a030f0a0c09050913150b03250b072d03020c0f040902130b0117061806 63
    0x12045501030040e620149007180365501c1c01000c449140707080714028060b0b00104900c03800340d40903501c03411081d001225262403094010b012040d000703024104440c0da81e0380005500e6000c0b64021906050045400b8410010610600d40d2260307098000d1440d007403509000a065214044000f0800341c41c2d0000318140b81c6414000d24003410140140e4401d03414940701580700c041282c3e06081c1e00350340040e100c0030048410002c0d28007500c510200c000090f100c1d41420405072110038120020042e2862000849580d2400094040c85d0500407004035803c0360b00700410f4048114a980b143d0608205140f280c6880c006908115500f07a4500e48180d00c00c404585a40541076a000e0b0f2281c0d0710206100c010720401c40c2e580c0628002204141d0f10000300d6001c854044840400050050380080d0202402e60500300e62805002000500005e54001d203a130020345569001200054295900d4061700c5540d600003070b15408800246c0350800c0103203031170000920384120000c40081c0700d10348900400e44030341301e11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 663159496 1250 663158246 663158281
    0x3080d1104030b07051209031204142b0e0405010806011e0e010312110c03120307020c0a0f081614060a032a1b03050301170f10050a060504020405060909 67
    0x1244048450808403001015900811b0440584150010200715904070000880d00c144c00c004440300302c580c0da40c0c2c4440181c00c100c918200d659004a40817618201103003c1e2285010100001802c0d81c1c0b0f589800046c040011511028000c51405005100c0000f0002e0800d044801c10448100344210541d8103000b80b684035441040410b4002002100b0440c102c840c0c10100c00143d036540d8900210b039103500c2c0d680c0301200034054143c0c00c030b10100c800d2980b0800046504c480140122100f14100d04007155501c0785a41c029440c8640e0a0402e015402060214101c17203c03040301411500e90401c903180e20f841d0f003d480e40b140309210000c0e034540018060b41115650610071500801701803147c0104045180c844070100c000140080c103c0500708404041801c0140d4241e9225030441e820102c90256600c401c0080d03041a114465418102c500200030a20480403104800329040c00c04080c01415244103401181c4500e0041c0400c1c4126160001581ca09120817560851a501d5100c0801c4403100700d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 663160746 1250 663159496 663159503
    0x50a02030304080a030e1f12150609050301050703110d020a260402090a061202010c062007050c0a150807090905010b0a080f060627030109060605030c040603080d110403 74
    0x440c0c000f030504008034880c100d05010362540324489809000300310007078400301c1305801d010081d0078101010510480c00c000046868440010b117444030345a00074483ca236a684001700055111400b80088d00f820300890360084540d00381030010000042440c0450f000c0c03158041d00656021814000140c8503004401d031040c6608580c0070490441e2400d0028803c040380c00307034040c1480c44007080d202107281c4241c104446855003417130180c103101e900449050844110030b841803503c98592000303519001018040700c00110040c160f0300c00161820b2820130241d03066503031007411b07401c03003c000320700481132188a0801c0030700e070800d040d540c2d00c841569411100c0d00040c002e00d00e80400800d1031280f803c010004c2d6078060722010802c1c1c0e038440c401c11041a084401c1c5400c0036007407012245500c0510380d00043c00a000d8941295070b0711800102e82150708a40c03043d01d20607203d03c0c0400080c241844401307401d1005490900429046440700741051203030340c04001045988084207000c800a03c1c0548014550 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 663161996 1250 663160746 663160753
    0xc0114070906110703030203030a0e1018030f0206010b0403060c230a02101503171615060b27040f060f090b0d0c050603060609330a1704050a0203 64
    0x80c50300008048815500455010404590000d800c0540020300042240ea2650055185695020b00880a401c481c10700c00150722402c03003800302c4046580070304400c203400c48210f41012002820003c0c030346040b264500003036402c14401444000305060403502501d400140c04a07240309444400ca80d064018a90040c156000d000d6400d001504c840041414200d5a0708966420000358400002c03103800d112900c010403c2c01c0e4080001070741c0a550a95040f402464150805000005000d000741010b070088031341c0e000900035078448405a10411020700990200c10b030030005c8555949290024140f1509940f5600034808440d5903515004a4440c000980c4180a82540c130101d2104403207180c0a01d42c2c06c03505025561a6900704900e1801c000ca80140c5002e0300545407000b84640d507480604603c0d0016020003600c051030320341035505104c0b1006010841001109600741e054101c510400402295070200030000c100c0e98000d00d214450212030085201986452070070501d42081c1c881c00941500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 663163246 1250 663161996 663162001
    0x1504050432040b0106032c0708100609050c03040b060915060a1d09220201031104030821090d110a17040806161d01031d0703060e06010e06060c0114 65
    0xa038641e10741c5004510500c0e101d44070740d8031800305038141d8069405c503065001c2c2202c4550480c400c415807140717103070b0400800c6e200403685403803030300e420484c01c00c03140541c00f602e922003003003ca441485860b80c000c00750b01c45d40e401d505240c1c1c2d9070903d80324080d140078891103c00011030500380030340c101004594401480346030344004603000079007031040114a8120700609089009030500f40040468072800075007001c0e4019a45c071144040c00f050b0040c200b81d0405070703102615600701d04200003c101641c083c004640e10750b405181452220804003400c990000c0710041480f140d00400a164140c6280d02e08042c40242d4500112a1908205120103400c07004265003c06034440140c000f402681c1c410400d030740303480e540c0100261030313001c1c00082100014911107246e2480405c11100c00410304051501107804140e0841002c1c07031100c008004007450b00000c0d42082000454403940c5610504a0050542d40d0714140e08100001c000409060003034030300184171103044e0707400c0d0f202140140c540d040414050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 663164496 1250 663163246 663163331
    0x50a0306020c0709020c100e0a0201090b0d0b03070603020c01051605090409020105090301180c06020a05070e0612100506180c1204050a0b0106020c100507170d09051c08010515040504 80
    0x101c7c205051540d02502c1c02c00d802c00040f001041001103680c060b1074952450b8900303c05d40507298441c95000f0070083c0c0d20f000d210003d540601140d0011300f401d550268036034061040b981e0031a0406820340800307101582c0803014440d082419503111901c2201c00040e0202c0500059805114402e10341da032652a00c1d03a603070200200383c5d14482080d40103e1150013600c4c1c9404c000e0f42d0781c0791410030150055106040c00c018842d0100d0007140d04c2840a40403510842101035a1442c1c0500906a04401031300e40003000010308107074007610b02400f0803104040b61401c3c5031654510703900c81c022068000740881d40024060180800008849550005421010350394a00307000f034950001d1000c2c20700c81d00c201ca181140c1c0d503100c1c00a442c80b8030780006025508400d414582a4990b1100320005809501c41a008002c90420300084100f00303201d03004c035001c50422240c010301180c4160000c501c60304008042404403150b903c142c1c2c0c203403041503d001814040424405000808441d01074074010344460740c80c400d9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 663165746 1250 663164496 663164503
    0xc10030e0601092307050d0b0109030203030c1c14040302100306120c06020d031a0906010e03030406030f060b040f0b0a03180f0b07051603140c030406080415020301050a0306020c0709020c 82
    0x2c03078600018450040402d4801c8804c0d00c0e0140c1c0e80e280003a2040c4207101d1000c0503903100002100741410070010f0103503242c4c0441c1c01c540241030140669000a0103948900c1c0c0c82c6a0000d0001e0b1b100c1c680306150003461844804280110302000c2e005051110544400c54022391140300908504c04000321143c40c00d243c11a0f400c00070327008070f0005000f4420510b40150003405501260300311812514650f040d0701060001702c6900610050400102d01c2c90810103480510041024082e25a004101c940b00c42d103111055800541c440501a6410441049550b10141100b41540c2002e01701c140d5499028004070302500803c40d10641c100702d51120740c410444d00c1c10300303034420b40d109201c4512180c1e1001030990b0305009400c409400f0400c43c1000500013072051b495024600840e056803400c0c015003004542ca950003942004010603001002d110a10580c4184903140f8640303414191325660520f000b1801d22500e07480001c000d01c0d0041078421184005011603c050700140800f1500c415801c1d110750387d0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 663166996 1250 663165746 663165761
    0x40803161a0609040b040317070e180601080415020403060c0806090a15051309080a02240c0d0b010c140c0f0306010803041a04090915050c0901020c10030e060109 71
    0x1010180707106144100705001c1481d900c289001070a8143c959640e8a60740c0007404000c204030100200d04891009070142038032424054221a507501012181180910141454030020181d2080100342040791070b0fa407005460740e1082e84014040b601440d04e2040c1c1002c0d010b40e80000340558202007088903031a901022451140504541000250315031981e40d42c12074603994003a50881c0041c0310103000b14148588011400801c010002802d42c6080c3c448064540001e48a07000680105c40301d40c9403112164106c1c407085426515000803410000c030043c62510405440310011522651000301a0380504910044283c1011360851003040f194009d54962035801221481070001c8840309015041c0001c0081c140e45500c0000d616250400c510b454402013818010f40b00500d0800021030340791802e004596403188150781c403010106d440704a040030f076403001741041007481c2c040c09207201076070340081c0f10808840299544241d06040240440c0502480307010040c00744181000010418410340c08900c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 663168246 1250 663166996 663167003
    0x170106170703090c0302041104050418020307060f0f08071b0b0907080304120f241b03050412200f100e030c060106080a021c0b0901060e010203120c04080316 69
    0x42540d41d2503426401c9495220000e0035103181840140018181584004d42800d180c4400310700789135507407000505845004400032a100684000d2104508040101c00c0142005007400d00e800c045254000702442d00415039101004419008500080d0188101100425001c0308100d000e54050070b05040e0360505683d00c40d9184030b00c00000420481c08400d41e401e0740c0070048404000c10a03a1254100c07a00540410384060a0243d03003140041040d00000741d0b60826442c0100c1e80680c000d000d580400c808034904020305007080100000158941e500700441065814203801c0d00d2042c0407800308410240300c40d071100d440355245041148600041089038201843c1e0180002001c65420545902070044030400310b03031003080107010050080c0c40c1d5581c4101110001401c19041c02c0480740700303880001503101115900d0040301c03818107202400d41c0c0035100c13604140324404a0440000e54038400d10306420b10031b60a10020458030503000f4110750051158000300c07500c0d054002c0410802d402e0044084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 663169496 1250 663168246 663168287
    0xd0b09090c032811060c03070c18060b040b16020301020d15050d0b0714070501020d02090f0f060f090d05060c0901110105060a0b0f093a02090601030b01170106 70
    0x140c0c003120780c0c1a8070100f0031a8401030304140d1140e60b24000c4040320700c58164004001e0104244510042004d07054041c0541e000041051074046041000352032010314008103410710300244014481d01003150f04652070145520360315201680440c401445c0904029895400061504010348981d0020f6031807800c4908111103407a034030000c001c100c280007840281540f112000140c61036004919085d400010010040d140c095079540d15822039001507048542150b000c11006054101600b0143c184181640e40e515103060290000d009070040040103110b0b00c00c0000e0390410703500c912040c2c041c000e9101e0111011420005042130164200c81d004d640026140501101c0341c400500903d405a040a0309014445062581c5c048440d480881d02c4018404100a6507495480e10b5030365180741128060381c0c2000c5442106580010042c8104040c900c40921800342e016a407444061604000b090900180143d08100180d40c440c8035460740304110383c4e0750b40000444a4202040c0c01d95404600d81c603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 663170746 1250 663169496 663169513
    0x5060f040e0c01030b1c060213060c1110030b0301060308210103031e0c120306080f0a0b0613110c01090309050a061e030b03011107060f0c12020d0b09090c03 69
    0x602085640d00003003a4999403040d0b032945019402944101d8200c44003408030304180c0d03a0f54079011130b189500d1000f180ca06a000550300075080c2005400300c0a42010324040c0c6c042615a210080d44070415142c586c45207948032180c0740d07031501035881141c0c1b0181c040c0081c04500e540382000680b607005860000c00c0e82883d003140400d400030300c1050f54103899158503400480b254042c40c40c520980d03440300000500444000240229104180e03284860800e658041012400d100c011401c04640310502c05250b480301d480c400001b04c401a4040c2d2086090303480001d03d03400280300c1d4001d0152100c501b08851304c001444c0001003010342024140c0f0340652a404941ca6640c014440c52084601c209800191007402c0c0c42c891401005200d02960401e140110b45a01c40c038000a00712001d4441700840c0c2039000a04004020a5000b42829494082d10803c60711113003100c05003800c02100340007035030658000b03614040341e001390703001428007040500725100e94507100c13440d60381d200654140d6910a1155106 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 663171996 1250 663170746 663170749
    0x50106050f04020f0a0311070230010204210204060b03010807060e09060d030c06091b0602010e070e010302100203070524130519050a020925020f0a0206070f0c0905060f 74
    0xc581141c20045001391510a103200d049000b0040f0f50b04d4050b0000081000c4c8000d0303130310307a143d580001c40908202d241003c440d01a1510714025405a24034a900501003045a080c1c5027180130300402d200402d8051581040c80014018807107a0040d082100000c000803980600002d948005e03030b4215203e01c100d41c6050410400c004100302e0350300754417011704031100c0c1c000381c400d100310118070303100d16804110414070ba80d03601800c2503c481d0100408100d50b204000d0140d0900500d0140306904001e403000d2410f012616101080501000e40a8220b8031204103460340700304111045260814240d60242612080300400d00151004034182c60b410f000110300d80e011850f40b81d00c140c40d0b00900030808074902c1c0030070f02043d40c41804280c034a40500701400c07001d80c84018103148142e142850102030070f580005201c0c10f01a2068a04045500ca030400501094002400c0d000c840e404a0355217031513140c2850046189110a04020480007120100040b020000e4102d5401624202c0c0e8102c4040c08040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 663173246 1250 663171996 663172001
    0xa021608010b150a11070e09010c1b0201180308040f0501030e1f0b1302030901090b10030f021905030d09030605010603090c0909032705010914060d050903090a03050106050f04 77
    0x900d02c0741c1c401c1d02d800d2490040100d00d40184040512401c0502945d2008058181803c0c0d403503001150300807070b9004000c9080300a100d426501141800c00380c840c1c40000e80148504507428600905114440118143c07a00c03400210300002c40d0700040041d0b543e6180c114800059050b885003902083c2401d01d44002791002154240088001603444010150b00e602e00c0c001800300c1d0b050150304040d4000800e0030a41043c00118030a6815000101c0d01d51094030b01005010f100404c5c0003500e4032250414000218840c50503941580c040741d000b02c0c9446001070107501510107503c81649840354403d44081650010082d0080f0780c001c90003003116a070390301780c1942a20b9055400a00d114200b49062103120302c55031043d4103040c001c2c07510391200d5030f903580300d08000c1100511b2045201c1d07030f28108000c45c3d030340090004050303e0103110506604003e00080b039640e004510b5900d0302ca580b6030700003a49044080040d00e088102c0181581031aa40d43d040c090f000309006d000d83c40c02032006003201c8070641042d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 663174496 1250 663173246 663173261
    0x12d0b1f020a050d050a1b0c050604060503010f080316110a090c2f0a031101060f030c0305010b0f10031802030709021e03070f05030a11030a0b1c150b060f0a02160801 73
    0x9440e858225903007003050207d20042e00804845030048010007041725110000901b001d0940d80d12126940d5050024030802c405483d4000031055104110508104203500002c0141c0f82d406004100c80c0c1e4080c3c0c0009181100e00c2e08910452807416400c48019548003031141c50f2070349500c0b040c4201481598010050042452200d80305501c00002c090010f4890704040c1c40708001000005109900c07004a030f1081400ca520548103044203950a1040c440e0038803403000d00a20841c0c1c90390341100150080b402c040000b4000e0414180e8801031a0000000548001c914030b50050680d0016921420103030003e4201e130f02e121014183c2c2c8031007032100d02c441e0710132207000c1c400d503444601008800440850302075000403e40002d064507800d100340c080700e0749006103026014400b004504850781406000e06a07100140ca80030701411f0405820105100710740d2000c640c0c00240020907100e4000003c51424484c0929003204d075407000500c002101c0e40460540c5400703010b440d10405480d80d9030203e50a03540075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 663175746 1250 663174496 663174517
    0xf0809090f100b070f0b0a09020a12030212030c0c0a060c03150503031e0c03030c040911030403120c05070218090609060c0a18091d012d0b1f020a050d05 67
    0x11100344655402c0e03c018121143c4210341c0c0c54181103155603100d0a404003030302c0c40c0903170b0341c1c503403440408514040c0e01c1d4001920304c01035102c60000058400030340d1a94209418074807100b001001c10380f060525000c880803040b120b4219600100940b41a5004040229048001038906203d80750380c400c01041c20021683c00500850030804610320360203084441881104010004001d00d801c146000d10186100790f0a400c0141d03121480d021055040d80d05030800014100c00420800000a422000004a405040f00f0015010881005c2039450384140c6030069403122068141c2240010034851091143d5100d070f0a40b81252120005181d07641410384030910304040c20b100c0002c8540c03043d0100309581d040c0444040c4103503520040d0208440c08803001c02c10442c081c55003200c1d8440709010700040c8407002d40706883c03581c100300c1c6100c0d00700d83d010910030440b6480e12a0000300c0e580e0306401000100900842d40c42d80040f192001c0d60302e006205040710140640003a2409190060f404e50312a80070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 663176996 1250 663175746 663175771
    0x501050a030506040825080406031a03060711030903070320121009060b090c07060c050f04061404031b06030c0e06030406050613020d02040806090102190503130f0809090f 75
    0x226695a0380e81c41c0c0080019913102080c4403140500210b0710141c0312102e40c0039814048d0740368108840103055980501c80c44001e00c0d04817144425503200002e41c6644410203151100100c2039240e08903042d8803031440d656500d441898004010301c20a0940c1c0b4400044801c0030140840c8404107000c19800040d2070703044681c008641009034626a9000740d0301540c440c00c000507280d101a80001e80985041c2c81c800301c041008200181004806d01c50480c0c52000e50801900304405040c09400c94401c50190004010480742c054034049202e10588020315440f40d1380400140d04205d800c03021403138a11943c00003e0510f1203024210f4001d00b0800300c0001c000c0c050524555950311090054507000d020980c12201c840e841001c40c0846101801000c900a007016a40b00c1c42c14822603d085405000002e450b481003000d42c100c0000c152520a4514442c1016038507580c5182004a04104101c40541801c114041c03190800501c0e500800180743c04586e00c00c204e03215102ca1008021040360340105004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 663178246 1250 663176996 663177001
    0xd0e0607020a03110a0605180607020a0c120c09092a0e01030b06031903020102091908070e060a12030302030103060f09230f01060e2e051909020a020d030501050a030506 74
    0x34400c0f400f56000e81113840854880408030760f2901c0c1142c008030f85249284400c03c980b100d8095017402003907084a440d01c02401c4018640c0c0715100183d9661181d08201c00c040d201c20404c0041c2c03042480d0040400d0b0100f0003205c0303454240b00160021041c51903611141c2411404d402d01071200c90b080903610904d02c5800a6803c554840345070f04d00180207160306106070382500d03000c004494a41100988240d0016841d4480d01d42448148806080e100341c9a210000080c04003440016100c0203c0c1d280c00341c5824280c5070200172986c51a042d8126030944c81061a00c47e06142e0160010f6048034803d54040191815a05642d0212010040000c0440103501d100c400b01d00281c242d03150030f90219906984d14417003c100c0403800c41c0c086a115401d060000c80410100300c0003c6807400b400071101224100d50820841e2400082c00b030380c01064491312070302a6082000003001c52020150030b4500d0219178451003040040d554010b100301a80002e410300c8004506400c1c0a503141e0101e80d8440300504070358 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 663179496 1250 663178246 663178253
    0x8031201090f0b0306180105070e0d1e0c06030c0e090423070b070f050f0604150c090e15091014010c060207080415030f0603030905210f01020d0e0607020a 68
    0x5111a10740b0442da540c58448140756940d0138041c4a008401c040b600c0c01d2006605c900c55425508001c080c03a06011b50f08180c1070280d152480681846540070740324024121189011f0701022180d183c001e040c14a400d680410b01d1a050b078080f21045045d5215500da01808004019042c03c0454009000381031100c51001c0c000d1055152011180001c2c3c2a250f61720f440f203500190a4015400568420707413080d000c0800d00c44203102194248601e40302038500d07442d113916000c1d07003084115907122003607a5402444103258130407519500034010243c40648603041200c00c00c0190507649200500c10200e19002c100248001c0940d4030403203c04040d5003410200c1c000c019a0843d65030013064400580030080f80c400604c507400140040d03c5e042198a00d00c0e50b20000c000c04680e400b40502801519102043c40440d070031108010845e101120181c101c2e0015030360301e44900406103170900081c40341c82c030034004425064015000c151901e0100300b21440300c0545181d07961300c0503241c0300d000d80c10540703085011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 663180746 1250 663179496 663179501
    0xe010f0611070b160213020307080613020c01020f0c0d18060f11070308041802030609060d02060903070321090b09120f0f0a0b090303040308060108150415030506010803120109 77
    0xa10700960030344082c0d82e5075031900360143e8030800c800c580101c02d521040c8210f280c504446a501c20b10725400b1070441c45d001d5005080c1190140c041d40c4103203140101c2d04034034940d54040f030340c2d00c114510095440d05000c080e81c45d8243c01c010f000004501403d01b441007120b00c01d8210717904041000d05c840d0708940c40c0100554070500009028402c120815a6000151000304295001188034508144d40d6038036001c11404080103c14803241003600400501c00507540e81f03001c681e0011800c13541518506c80b103100080b994441c0c1544950103000e0041c00006100715054002d0b0106a07054410039400031500c411260380003107018403a44e5440c24090500709081140300040810720400485900004601c9010302c2e0400d0000115541c1d80030074ad079002003060043e5026000004d82e0015821420702c0d54003c0d00600001f0000d5040100000008030720000080c2c0881840308040c00405c186240050b1001c403003a81800207441da07208003800091102030000c00c4815650b120440008280d0130000f03690017 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 663181996 1250 663180746 663180767
    0x2090102070f030b040302011410060305060a1806060221040e0907030f20011b0b100f03030c11010e090112050a06020d0209040c0e0a120804090501030305030a060e010f06 75
    0x451007510030100d00000c02c10b900001441c0616010032581c41c0c145002420b596800308540e000d1b600010034040520400c00d0b8100517916039050116080d521040401d01d07481040c1d0103010b141005401010b00400340e5480b04003036a01039400ea50103c143c145e45900b0b001d2800310251101c06c001c12040015030030741c0003841e0300121044155104240d80f901e502000034882502a00c0d030584c0900101070004400c03815100101007801e03d5049500c07514815081e03016550005030118900c4000a1003003d0034021183c05441480300c507100150302c0e82802000251409002c03280c00307406a46200040d03003e40c142d004100c0004200140d184c3c2003e040000a100000d1700b10350522508001e0b80002d18203002078540c84140303120040c1c5801e02d0a041009840c240e1001c8010b201c0c01c9204c00070540c40301d000d0f044c1a80c400e02c4003200404a14a06400144590b45c01100da441c5030030004000c26510000550290b1000801408056242d00d02485044820b22540041c542d40d07440810402e40511098035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 663183246 1250 663181996 663181999
    0x6030e0c1917150405071d011d092b020c040b0a12030e030319021c050d09020102031e090117010b0901081503010c0509031e0c040e0a06021602040f0513060209 70
    0x90303000030f40e40840d10701e4060682d002c444030341003001e05001c0682c03550f20a80b0040300e01010040194907020841d0b502642400700e810702002c000b40025040d10041103a005060100a421840c540d0f046084180080c5154010340c0180120440c2d041145082e00985c3d032080340c001e0641002a242c40c001500b1956106400c1b02401107684800100750b42c280701030b080390040d07040d0240c0e0130408001c00a06012b4003c01981c00a000031204d007920a900109598040d141c0780310004990096000603071170b60003051014103550520480d2049400100b501502020a003038840c003010f641a048107aa03e01003d009044d80e1107002d000300c5a0a604c01c2c1140d0390050302010b001140d0749403010100303094600c1d41481e88041280018010500d0404108000070400c130030342d980c0c0f1071581200081751603100c0e2024140c400c81d10b5074154024581d06022110b01e07651303c031108540e503c8005c01c0e1103080130321407c4103a116501e400088481c40c88a800703800e1148611150501410141c1e5031100001e400041401c0d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 663184496 1250 663183246 663183253
    0x203030d020c10090615080102070b04021908120a0801300311060f01061e021518060114040b0904020108070c052119031506260106030e0c1917 63
    0x80d85250b0180300d468013903409a0008136174007050317040c61006000c00343d00c83c2c50300d0780c410007201c0041607254048a030029812150800f40d400445881c407010003080e08003d91034001c455620100240100c000e004448807611420401e0381d0b107046c183c0704011001c0d07200300392191140b1005034000626a200019a00c02d0908001900340d1911151805904480302079880309500014029241c01c041d441480f11013071201c07134500220380e46d4025121302424590030301f640b180c0400b161020291100811005800e90110b90066954158400040044001890041e0b02c1c02400341800d080141c1d50174441c2c0c5d01a161046592156142100d240004840c19600c074003c010f10703940922950581d0000e4064031580250b1648c00a40d00c036001050500b007208240761030018800e45e04244940e5a8048801504010003600081c018480041c00300e03d400c00f40114202c0c00104900f905070317100fa070815004004444540c070300e160501400030002c80003090b506c080b08500700b058080034101d8160603140441039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 663185746 1250 663184496 663184513
    0x30a080c0102070501200901030e010e0321012309181b130603030c020d110a0f06020105160801141c08030402030d030c0f030c02150f0a14040203030d020c 68
    0x10058190811000229280d400040c0c00043c00424001d0012045030f07144944c05644104548015920540f9590b50600d0b495980e01600c0003130a51201c440920660305403596030015006441800382141240c000c960060400462a4030703442c40d034050341c0d803002011b01d0b456550220030480000001001e8840344500088800c0800c641400305016035601c50416001a4940700204620342494021b0f0003510761416408101003607011400b421011380566541d4802c040d1400d190100e03070003030b0103000c1d004081500f000801c107605010900481d0b520343d00800042e210030048a50007001074501d000010300010041c800d01e910412940b400e10700080c500c29040b00d032200c04641447d4016015203005801108100950905010b410801e064034542009100641600500030382c2e02d42e0103842c101581c9038403403202c040c0200540369091102500c2101c092a0035100c00c06042000c90703070100c00a050070003c01407000c03a03e05041c025540100918108100c50380440002d40007021910300c50b2280e104d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 663186996 1250 663185746 663185753
    0x3020c0304230a0e01060f0314060103050402060409021801030b0909060c0a2007140306010b071707080318010b030d050f0315090114031209010c060b0102010e1203010e090a031d030a 80
    0x49280091130318a14555156141c220050000c00011001d07906142c10407410701d6500300001d8583d640310000f400c5c0001c19440b00e00121741140260381220856510005d06890341c8045d800a0006001090fa810b00c40c00b03c910f000d1002c0400d054034241021360000d00400c15100002c0050440c0d07000301d261049142040100d014262800d0540c2c4642c20b80212009102c0d58082501e03004d01920107400901c01549410b0750a11580f040110280c4441c070586003004c3c440384403c08403142250441710240c3c590500e150034121180745005861010340c600400d034005410085000d0314244103684420303062a9007a0910700c1e00350300040030700344c000d062030110031260f0341c0f10251903020f810704c1c0d100c2c1d124640e00360302810301d010321500b01a1030410041c0601c048903030303020500030042d0394803a8010800d0403903500180d024242c100072401c000c0c00b45100c951403104814020398125154034402036001d8940d01400c43d11802003000142c00070784010184002003603e440f404442134005022201c0c44042a01d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 663188246 1250 663186996 663187009
    0x613080f0a11060a060608010b130314010b190b1204020406051c0c061704201003020936150904080a11011b0c05100207050a1203020c030423 62
    0x240250200d0418126110341d00401c101c880d80c0030800110800000e4240f460240c07d43d1014455140440c1001900030301881c1ca2229030001558012242802c0900051031b80c0d01821003016107a0003903d0800700c4517190326040741e1000841d4550a000c0d07141c10854003000b00c4007180240143d030450b031940400141901d8143c5501d20034a4106d44a846040700c52070440d001c500650b220360100300620701c2c3c003c1400c1d454107409030882d5203c20207000c0741d1413411007203d0000d0803101c440d034061408a10380d081160150014001c40d0403c403468104a078040c0c25400c11494001842d4501d06d0408160105284d104403032560004108200d20f160b020320380c40010405035040307a0489401c0008a100c030281a007044043c5107884240c00248054a80083d00444000d603400f841c90410030284400410300c4030500414501c0300d00114107540d01d11141c14000e82d9405801d10407500d0754440341281003114824400d0314900c40c003942c0518a070510b8071022001c0350000e0b10900c50880c1d84450749002641d520f5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 663189496 1250 663188246 663188257
    0x140d0e060f0706062318090c060901030f060f0602010b06040f0b0f04030609030e1c0330060b0a0f0c170f1606290607060c020f03070305090a170613080f 67
    0x250305c43c600c10b02808041c07020070719080d21008524105501402900342003c2000c1c020001e00ba81c615403200c120702d0040b000340001c0c081607420309103005008120300001304948415606e6a0b0020300c024035404040c40b10f10701ca0740c41000c84c1c240320050280040141d0000918100100c0080241031076100c0e1240b4003110f06a1408038013007994102903001c1c604002200d800741c92802d000103144000252406071008a40e405071080f2005090701907900f04003604418041e0101a150070000d4a484000380c1e00c40c0c0d881000700a021424808441200c0c601c28154011000d60050180c001c40d0f44242c20841c107134104642d40c4408800500c02148081c000b110100e40303003030049030080f0300d188000408140f2402c000351080051035140d00c04d0703036240e1035050071035406179070005000880303040c000401ca080107800324241c4618080018003c091540c428003801c9070401c1111050240c99550352003e000040c2001c401c001500140d0000b0f11030107546d25508442805446207516010078001c08200c2507100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 663190746 1250 663189496 663189539
    0x40207080d02070605060901050306060d390b0412030e010e040911040b01030b031203060f030303040f0302060a0213090902010c022701080a0f120912140d0e060f070606 74
    0x410f094060003818000c181e00031324103a4101c280380d414100469241d22008080c0707405580048072180400051341201c2e074120072285142c1344030307500f00c40c084080304000008145c0003c100400c046180c082c8141242d044600e1481d0380300d81c00b4400d640603181c83c00380d01c40b068144818010400100d80b60f9004280e4103030311561880034400d14620801044981e01c405642c1094a0520718040300c2e100082c240208240500000f0b8891351140001201c1031407800c40e071501030101005001c10003c5410b107400d8a11321075000c0d28a04d61700c02c1000d50481c040c1c144d4108500c01c030800204501d400c254040b2001600624085001d40400c1e0049002c240540c5040c3d1000810361003984080704070810540d001d070040306d015040e0482640ca0f5076050002c3d85078068090850900d90307980f010300400c0c4507001401c0004440c184001c01b420100b61020032140305c803031240103046140c0d440f240b00750010b91001e0340c0180500d040808104540f50150002507045030b00300c3d51801d01281c9180f400600302e8489a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 663191996 1250 663190746 663190751
    0x60e0a0504050f010c080c090f04110319092303161407080c0d1e050f031209060f220204090b0a0606110304090203040f08180306010b041d06040207080d 67
    0x2030910300b851400c2c01c910751866569141000e4811640c3e4048038050304140c4a49503184c4482101000a09640090000035449450320005507041e1501c44051886500d80d030242402281c00c2c181d10100f981d81540c0300400b003040301124417840c4680c241c0c60004484100003105d050214015032040d008840000540b403200040385130750238102d810404607018003980c50251000300070400100e0032448060100a00c3c101501c04140b13903801d101d035040b0030900c0c4c200085450f51820441da00d03440e80e100c113030805605000b1f0400a0f000020020708a401221810074040b11665400c8510070045002e078180680f0303081066940000d81c0e6103018510101c0c1c000d201a41e06410207205402c2150117070741c0001c040c0700307540100950b40315020098400b01c501003c005a82da82c0d5900e03040c1005911580000c14003130001c62901d0175aa000301410382c0410007079040b28116602c580d410491400385100b01c401040845000c448044800080150070081c0a03102500300286560780b8000303500301041c120362007030307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 663193246 1250 663191996 663192001
    0x20307030603200301200f09060c0a0b0105090601050c0c01030902042301140406060c061104120503120a021611060408010603030807030b1c021e06030108070812040f0e0a060e0a05 79
    0x10b020700c1b4179103064180e1480322101806400c900300350350141d070940c520070580c0407a5540c402e031190360840d403903198684c00351804c150381450010400c0400307024650203080440c0000e94254002c80444282050000040408602440c011409405000402c980080d2207080000c01541514400c81a40ea2202c1e0f10403003035810080700c41040c0e180c810010344500d00707040c01004810340011b000c040c036503005103003c41c1034007092046000314401c643c80b400e01030500c0780c4208140700c030100180ca102e0280103003000c1692514007140040c0e0207221906d07013125000d2451040042c5200d01d100d210301c2d00107000b20b03062664a5152900310360140c0e005601040f000d008108082c0d07454411030601040881c3c028299840026122080e09144000203010b10040c034418841801148100c48003503000030940c2d9070302c1d0f03103c0010544612082c4030700c03d018860f49000582450705c050540d001c0d074160300f00304d04485280000c4958442005400942c990f540d62a01084807801060740d0383c4600110180400d050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 663194496 1250 663193246 663193249
    0x513120f020f150402310603060542090906010608070c0302150a2a0e1206070302091906090501090905071d03011805060703050c03160302030703060320 67
    0xc004448010040e009103400d100c0b900f0a41e4005038105406440044c9604180d8100210264074410300045101c81c552030741c5440ca690340c105005491040c030040c00303e80c942204004480503500f840d15008041d1104108051000303524454079030002010340c0c44c016541102040b6055015158896607800c00001804540e8000000903013041c690b00d03205486d0130362500d0007910f90014a80003110000c10102144610100e41c001c1040550400c3d504290320b9140603000c12407402490b84c82010803c0b0b40700505841c680080312102c1c10000301c016000d41d6841c0c800c202c00941c0401c00c456800608800c0401189401203001405400d0742d840300c0c0e401c103040500150045005500105020707043c4400c10180da41d00026110b48103485c05000141c0480301000240901040e4642e861006400350640c414001c00080050180c02240c030100865282c0c0500381d44684002c983c15842407c0f20b400030303422a4801d900560744480b0910303000a0403900e039030362144585d1500380c0030340c044008070802d404c69 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 663195746 1250 663194496 663194503
    0x3061409070b070b041104060b03070906020705010f0905060c2d060604051302040c0e03151b040303021203040318080609010c050412020607080403050d110705041e0513120f02 77
    0x14050080409080091030340e5880f1305202c0043c8014140024841e48407500c0d06c41d40c01c0702001d0081454051703120f20308040300410701042072140c0030040c840c40720b0008031035009640c82840c1080c1a607894844e00d003003405024131940075919207140c45c0b04404105c00048500400e20718107080340704c1c2001410b11070303081440c03405038081e0405200300c0c41c00c0148400a07814404409905078140c8001c90002030110090350010111082c3c25014025021203280b0046a03c00044c410140131103280e03568820343d10b038223525001c0c038040100980e08c80414002c85684183c00346501600ca450302c0d108505042c152a03100d207140da400f00b4103592140c1c040c0b08261400b0300851a41c0c0c10301345801410300b850007803c4d812801580358040e000740000510402444200d074200d43c0078603000021034080c0140940014400071249050542900918401280d640341602481042c24081d141490f00d01011482c148020310000e011900c00b10300441660001400c2c0b03404070340c1d90341c580352240303c0741c03c441c18406800c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 663196996 1250 663195746 663195749
    0x71704080c030417060601170411030f0d230702060406050c031903090b1302100309030210091208130305030105280803030711010501230310092f0108060f06040306140907 75
    0x50240500c170004d014000c00c02441c2e4401c1d004ad03103940300d25851401003070034600030b100050306900500408110306600102c1d84140c00c03071580b41d0200d400121950003060b80c080c085009600540c00c0000700145841003024080081e0320070142e9190074541c000c80d942c05240807002001094072007129800380075504194981c0a90000ba401e50401f010b5400902d500d20100902018903030356214250505200300261000d0003070b80784041009804a080100c0041c001c413111500040f00800051825902400c20b003030040d03807503108d5506507401d04041280180480090759000c0142e9008511b594243e120000000c0007800040d42c0d0707a0400e82c1005084440f030649004d2684e04040040003058071181c020074500819004c2d440c00c80c20248000707400c0c4428600c8a0070210309004104040c0b02100b03600f13079109030010404200000b1204159085112640440d50214000b00700250b072908107007a13204000800106046c0c5015100c1e03035948101c44200d460b100301011182d08006152004000301c20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 663198246 1250 663196996 663196999
    0xf06060206060f010809151005101d04090f02040912030e0d050403060f0209060f18040605010225081203090d09031e0203070e13060c08071704080c0304170606 70
    0x110b0314001c80401c901c00800d071003035810040c201c2e0020344980781c24440c02c2c1d110040e50381c102c0f000b0308245142d0728100c0041c1c02100c0c4a40d00011480d148030b030081d04c00c825215100a00c0c141d0000b0100308120040c18480b209071403c00369140610016600c3d441800382092040e81d0102c0c20f0341c1e0a08000b01201c131040c6844801c1c0d442256060403407500b0209a804696000c0c102098000310b081a1801a014400060342c0046d008942c0b1100e41510102600d030ba1081c1201c1c10180143c11000c00040d04e005110381c6015800c0600a250540e800904022030103c61403242b90342181d40745a074615144150302d0321400c484003c0280b006945041c025405407510510380302c054a41142c68001e40c80004600000c0b00080c1090848215201440080000c00544407890400c1c580810401c0c1203403c0928211502d903c1c0580380c44595009506a501070309042ea80c00c038400042141da100140c40207807055403003903001d01c0030407110081040204080c05a0700c0580c100c00104119551401c200605001d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 663199496 1250 663198246 663198253
    0xb15010905031e0304031b081009020f2e210501030b01050d030e180402181018090b07170a06081f150e0610020105011d040201110f010f060602 63
    0x70016607a001881607140501884a00c590704101c048452070341c420b691005190482800484a040c11107030300d032404032000b136029035480710504e002039030403140b100310000d500101d606412050740c280342445041942840c0c0d80715401002c0e03a644000c8080300100540001184440c117015031400c5c0e50000f8400031003014040c0080d50555980403040c0c4814009d03039010307000b075000301c2c1d00b80752007540e00701c844a00281c509441c0f81c0880b099181d40010071142070b40901401181c1d21036129110402620901302c40c0d0f842140681466150140c5410001500784502d49509a400c08150704000b40c0d03007c1c41843d280c5680b10b680c86690140e9211008040781001c900d056010051110302040c201844043c4000e03001e601d8109000810080004036900000300401e0354011540303285400a0391f000e00421644c1c00070003800c400c8100d00741c91090107030308070218140c950a4090718030b000c09180c0052050403c40302015a6400162a155501d003410301a0780d1202d55100c00751889214000183c111440034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 663200746 1250 663199496 663199499
    0x20c0a0b0910051c0c090b07200618270a0207030e100e150f0c0106211109060303120c1309090305030f07050913090b0a020a0801030605040c030b040b150109 69
    0x10000300704014134556149480320010700702e01d445141614060420a200b583d00d17402241403605027101c10301c0c20707810302000200f0444400c1c544030b400d940c0300b1810445072010110900040c0401003600c10361000303030829003036485115040d0440c0041e20407105c034900107803254000e0a008001400c04182940680706505142e00010341c01481c580110009071910070740c4040c1c04460620a00c6807101410b0913010210b040c0b02c0745101900050304407002009035401c0c0110000c0e1240040c9029000200300207501c6000112030b0520380400c40c2e2020f001001d5a0030580591003c0501000c11101ca80d10400f00061a141401d40c00b105200600003550040121001954010745940300152800c6246000000003485141c42201102c040300000ba00c9062801044981807004e44a00c030130881d00b040801000030600700862090311150485aa42c03548140d181d0349590700108405041660304c3d084201000c004200c1c1c566003240070b1480303802000c800f032522600c04c80300044502030f05030400ca5407040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 663201996 1250 663200746 663200767
    0xa050705091804150903080907050a06050a0c0c12031206080d140d0902040e0d080a02030906040f03021c051c0c210b0d080c060109021e070201020c0a0b091005 70
    0x900014150441090b49140e454905004941c1c54031001009202c0e0700b003580160400d0341c00300040d401840480704441c02a81c641e0100b020511242c004c6500148080c440004401d224900040e00745000c0c0d042040f61a40300e442c0000c04009140c01136000c1000300442060a2040b40b05403402882c40c50f0281c001c0c030303068420041a5129640e022031a007540492142c0b20f21050380c0c06520240d900510030440510071040c5c4030346420903416208081074144001480902050003120f1058540301c001e000d140c0e645070340d400e484c00302c914000e6003144110200e015510075144088881c1042d5925030940300d13862190701d00c181049403030840c1e00e41400c00d1001780145410010b00744920081154554855040100c604d000300490322103142d010034041d0b041010b0010b81e40007801c00d4078600c416034442d80e881f107a011041e48600740307940b5101c00cac3c01c00803001483c4000b40500300f440d1051058807030a4290000250b21002a138008503194000081d440246150a007148a000714844c10520b040c040d0700034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 663203246 1250 663201996 663202009
    0x1060f020d08150405250309050a26040b091e090402010e120601140a15050f13230a091808090109030b0a051b0301050d23150a05070509 60
    0x960240b1001e00041107880c1e0084030300c8144008090070802080c9070010f00100071b070104080c445011100c0c8200200114440e0040d00e003100d820030010304240d03141303a80b1440f000f110340d448001c01d0700300c28200c1010302c1181c1000303200510b12580c21589801080d01040b801070400d00c408031004103071612040203904e4200c41603a003d41c090030849540d141c0a0b01203094401d80c81f220310f000f4000c100010521803c0c0e04040e500c100d2085e910300e5540f6495041640016040100700740110300e080c0300e9003041012200007041281d5070400d030b54401320768580207010000c11b484032803011711032604284602810b18a01c14801440503c07000d11022014042c00000c03400480b01c06010030b0000500c03042c03c0d90284014a00071039200e0701c0e00385e582c90880c000c40000c1c60300740c0e04030980000c203c50f01c281c1d194800003600d050703440c001c117010610006a03641c0c08941c003101d075510220800c40e506c9801c4440041c42890404049085820344920702444190110340b0006c0c5800203000c41401140099107908 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 663204496 1250 663203246 663203263
    0xf11010207270b0301060f03030201060905061903151d210307140c0a1e0b010f0302010f030209030c090117061f0e130609080403020102100c08070c0f02040606020c010801060f02 78
    0x34400040d25030440f0010074050095074016440d07218001400008140d41503000c40304651160a08000d0303502c400e020400048400200110701800715281800440c8902d903060422078182d400020396600d03ea02d132000221100131468856400030742c000f202c04c41400c160340e601c0c0415803102ca491480d09600143c2984440c020901c04054003280101c0840b0003003040441680e041346041c1c05200720010182e0b4203044072442140e24100760800002c0302c0a4421496054a40c16110007104081c2c040c0101c000790031001d88990f161081d25608403a540396081c034503011709180300e01c48000c2d010404a651600d48003410410070700e03030309440610003841c0e03020356102540d0070710981c6034864460703848210802000003c0075050500d04240d5a0400100720b0017801228400c1e002e40f8000001c6088040403904410106404603a594002844940c40b801e4000050f51040140344050411900070404480300c540200c0096846103001d00d650b980c000c11003500524240c6003055199100c540001c0d100c8105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 663205746 1250 663204496 663204569
    0x70c0b04030924080114040f0e0c03070905090714210f190507060f1e0c110102010c0804080a0318050c01080c030106120c090503010f062c1b070f11010207 68
    0x31041c0c1c0c800346071f84603040080d85c502815424020b05404050362502c1e0701044414a2007407290480001c0c80b200300740595445890314101a20b45a85000081c00ba45000394030541d070312010804840941c142c0f8070785995408140b00e0300500c41408840400f070300d004450f4268030803500452800000180d00042e88005a502c4c0346071144282c000c02d101918280e5a00b0100d01c01010700040c04da442a5114515040c058000e0f90081c0c401c05039030005900703c0c3d2202c0100000982d100b000907010410210003051442070b02c0c500010305d50800328203001544ca0500040381c1c40c0e0440b10b103164807582e11804254101500b45100c9145500d0180d028220030454103000c2e407010b449068078147c040c0942c0f1100c1c000c20f005002072041c59480e5002000070203040c000c062141c0b1b14203036611454040404401b0002041c03100c2501c1c152101b68200c0c03030001c11500e54520498080101d40001406000740d01c04280c403480080d40000c1640e000a402c05c107182c1c00603812950202501d4035003010b03103401c5070700030b480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 663206996 1250 663205746 663205769
    0xc010f091e08040b0c1e03031e0114011409030d030605360604140c0304050120070b0c040308070f1a13060b0a0b0c07090b12030304030503070c0b040309240801 70
    0xf01640c80d003407a40d0a08000100400f010045003206d001200952080c0c1802c3e00310301540c540e03845400403500c000e0098491003c0c401d8120807455002c0c210341610780840240080c1401d2400300000e1070503100960400000c0c0d2201d404104a00381070405c00e48030744a614104440f141514a00e00c0042031480b00002001d40c008081042c9495070352203d0543d104010162981c5e242421b943e01c103543c030a80e002c4802d58a45915003444e16000011801e040f40c0003100549040a10b8440f10094140074243c03c10189003040b0000000b010f010040c50640d00c1981110206000d50400c1c50041d803010aa03808817402034410000f00a00c19412002d205602c6000080c0c0b180075075000c070354803000641000c42d10210014200c4a0050001000c01c2210480001070049d4404841070000042400050b018141d10170b0020900090180c4042d6900038407500e0310079103500050f10b0b008140d080c180c4e01507020a0034094240174030010400400742e0095042a20b8001c50780c0e00500510342513052250040703002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 663208246 1250 663206996 663207007
    0xd0f06060803070602091002060402030c1002070801090501060510020d08160219050606120316260403111509030a02130e010204030c060801061706010f03020c010f091e08040b 77
    0x91140d20520240c6114030459450381c1c42c51514100950102d61464883c110f0a00403207411840007420360b00c00d95015001e003c1c2030b103441c1d0a05c41130b00008920401075001e00324011490080c2445041c02c02c41c050000415a141b1741400e02c0950f04410302a1001c540084400482194200c1105504410070798820800a0142a422801c1072101c109441e1107002c040880e40c01c3c000c001031445d010381c000301e4500d80710f440c60b10903441e6284034540f007a0518016a00c1400040340201c65003000c00f221b07071031034a640c040d030800d440000c56106420454014000c01400c68441c2032120a141d20651a100460320b08041100001c0c0d40300619000280f00f8440340c0c00302843c15015412011203078040e00d00039500c83c0e40b249003000c20f0250500600b000100b240e030000450310303c07172444120b442200c0540240c1d01d4940d1001141c81210550041c0305141d000c1080f00030a40b030034030031034111003c00c140001f001c0c1004e203000c002150380b6882400c00540880604e0020509003c110707421240d21005059403031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 663209496 1250 663208246 663208253
    0x518040c1d01051e0310050108190b131a04050318011b06051b04080615010c020a1a090604060f030b041130010b040905060303041a072406140f0d0f 65
    0x28860780e081c098140c0175100c42c51b07802c07054540040341607805000c1680c2070038800d072164035003080d40c3c000702601c500e10182c041080f03444140301c1008042e020301d8900296201e0708500c07252048082e1401c030b0b015480083d803140181d10503005603140e079409284c82d145420b030003e00444d6030050382002410090b1f513080492001581c0002610311590203080741621159038458843d21b41004071030721091500400c03241c000030340c40b60444502055006241c000791900b055034044541c01600300010040d0004c11000605650f003001400040031a555441200d00718a00c0040c00e0360352000c0410f00640c01d005403442007030402c60644500000d0484101c285194070600744401c4d44000b000410b440c61110000314009039984010015901400d0040c03009032205800c0c1079407403096109052252184032032161042400c0e600411020b401032820070104001d0280e460050400c1c1c02142500907910a010005170b52030009402d4007020860740e03104000c20403408188100c000f424000d0800c2d80d126202c5080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 663210746 1250 663209496 663209539
    0x6040b0a05190f0b0f030d0c080a020705041a040e070303020318360f100603020d0209210d051801050901090e090601061e021e01060518040c1d0105 65
    0x40e18210100740110f0141d001030b1001006410799050240c00c1156410510b811300254540c0b1203841c590f50300c4008030164a074880680c2060303100200714041d4580c0010260703100d0040c024003030042d01604000310306007410401242c05e89103c40185411000d010400309401105903080c140c4c0c450003c44a1107690000560030080d4940016815940ca1421a0390341e40300303110f809984540311484840c03c2d12070008042c501d0038101d4884c8030094058200307200c2e05120350060580c0081c03405015081210083c0003911042911a05500c5165203a8075981c191804005c0e4000146460800c81d03e03000d0920745201044000c03d90050511800082e400c5490340b1416800300208100d03000e665607418a65071168580100f80b0501d00025200c5d006006046410228200c1601c0c0c03603001014a400e0b2076242c01601004151700480e030307550b550070004517605ca085c80340828402050302981c0d00d14051508000d000b100c0d030004990b001800c00324031980005c0543d602e040d82c000f290f03485611400898404113 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 663211996 1250 663210746 663210781
    0x30c030605060d02180303190e18040f0302060a0212010e0702030909010311010f050a05270d050c10050306010c0b09100606230f0702010810210605070206040b0a05 72
    0x1080200010fa844165040b0b0b400342082408048096030404255010160340340a03040c0c40c41050301c6c41d8458407440c40e00031240c011901c580949010514140322406c0071058504070b900707a42c0d02c403404001204250f07041c042d0303503071100b081a011400c04583d254810648001401800141c00c0302c400030401c5a802001610b141c034100822016072036850b40761050b03a075031104801c140440c00e8601c5141c0c2485c0503030140c5404143c1a6142420922161010140345010702210500b1940440306181d440d11614010300c9800d00890041190065490511441b0940725000307030201301d01072003030107416030340900156911a0813120440c042d4842001043c209520343f00d008401c940782490000b959900400c1f401305d0044100e1680300d0107c60700400c413070b00d41f18502e00c40b204100100176250041d805466210342101c1c2010010703c0180d214000101003640a14001c5c0784a0254010001008218061705a10424a1015003034070306081c3d44412841001500202171141c9442c00a0891030b181c940800c0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 663213246 1250 663211996 663211999
    0xf0203040305070c0b0f0f160c06020114010e010f0501080403020c0a170c010201052a0d111b03130603020f0d0c0915030b2803200901090b0f01030c030605 68
    0x1566424203240161565004440454a0702028600000c0c503c20301c030709803025500c2c00040140307000411005510150304c0002940d50100c0e0351580e44020400100c80200034180c43e400015500c0807440307011030f80f0300c016401039604004c4440107000d104050b581100440700b0a0030500702d25155413030145d00301625103e4068000c00f130850001503d0a801060f81942c0c1e48110a40300d10088440c012800c0c2ca0701203030100d51401e80500a908402100344200503e08108814641441e05080c2e461058030701c0b151309801c6076500800c5d000322105003a1004884940b41c0c000070b500e005000551424000c3d6688074503000d055000c1842546a00c3c0482201c5640c00e500ba41003046455881001d0000601c03405621a030032041d803402042e03d4068031800f01200001406450303441e080035100900c1184104e502040e85841007000000640c0520b402103000402030140d20603803c03500e0030302c910010140d1104250301c2c1018500a030607140c1051040c0f41d41420321b404036000309100e1040d8041c180b2540800d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 663214496 1250 663213246 663213251
    0xf0f0105120c0315120a03110a08030c031b0a0903060b04020405100c110a080601030209130506090609010c091202010e0f0d050a30210513050c01030510030f060f 71
    0x100304002c40b080114030810841440d030024071004410301502c40440700e524803807a4130007480440424010720003099503481c1c1008071031032981c003070303a80310015007042d02c449100300004820700041501c1040e45080c4014105515810000c1d03407034005019001c02c0c40090410f075600c5809032450b0315160100d81c007505001d003001e0507194a20800a2404800742ca042d01d000e01261454a01440d26a87d8031080360042c000800391030f421030b0200801180d014090007a135a040b25035000008000f440024070900c2940302038200d51520030007160954038900e500f00b0401102c07000c140040180082441c04080d02884c3c10b903d140098000310705000815051680d11050782c0301800c040000005100034143e10a4869401c0501e49581210f003054210310001c050b0300800390b100d05800c0c07154070783d42085040303401ca40f180094407018150448000781e446090a603c980301110503c1801c20000d402d842d020300e02004540340800448100c0c0000d40001091480c8c2000740707030f0511605030800700c80032007507003002c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 663215746 1250 663214496 663214501
    0x1020706060b0d05010b270f04050906100509041e170c010f060e04050a030c2117090705150c0c09130506070806060702330301060905030a020f0f010512 67
    0x104500343c02c64803500c00030702c0c100000031541e40c034403400347c0c0d40354480100c2c006070044000048866441d101d031304040c0c01504803150584a540c0c0c50003154024482c034800340415081021a0f07032615049900014040e92043e01844001080e10402c01e1f481190340c080000d4142040c90b01020103401d2540c402040d140104c0d120b090040b06500c401d13801c4996280410203140c0c0c1340b0b031030380e43d400c070458025215410514280b00440d019100181c006d922414006180326100e0904c2d0124000645c5240005007521042d5924640ca4500954001c444100140080ca03d4200015240b620102100c04040b40220780ca040d402d204101c8100800c00c014000e0301280b4220403880c01c00c1c040c1000030b403024855107001c41c0c051401842c4080c042d4002500c401d241451540a01c01e40204c0e0002c0d000450035000401201c1103028085400b01d80b0400004d41c0c0c1d03c0d403406200419919030b5801123407098011600160040e03031800104641c003082502e000766190628401a19540224002040c0e441e8542e001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 663216996 1250 663215746 663215759
    0x50d09050303013605071701060c1109090a1403071a0a060b07050a020f221a1e04150e10090609230a20030f012909030102070606 57
    0x1035410b80c0d40d8504540c0900c020000c80b51400c1c50b80c100c04404c0c801c0303e194101003400c207542040f0750190a07410910001e41d03a9001c0c1d40300b950402d030700060008407004106001c10421020b461108001122240b55509188095a844462405009050604480c20a8000041801510003440d004105480d41c00000a803201c0300030340441f00d02e0000d500d00440450045103400581d082c86411400400b005107040d424440e80d030000a1105070b020b248103500d1368940c41a1410b402140700343d481c0120b00895245000074120080b4005c05204003088218004031a481041c41c1d42600c0d01160042200f0220718001aa050410782000d52204002002c11004d0442e18002c04203c03440320310200141780ea00d03c0301904564907444600200051120b03085020172a4001c265040100910009811000d003a500900082c170081c043c4000f400220400810552184070350303005000d4207090145403900c511448040c4a070140c620582c1e1000420407034a0742d2000d42c1917a0301e01c0d5204500b00420303900c650 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 663218246 1250 663216996 663217003
    0x70c03150c14090315161d01021902061b240c0405010507020102010f1a0a0914130c030f2d02031e160f06120c0801090c050d0905 57
    0x1039031038000e0500300c414503155901c50303659811002c0c1d441009102020001c0d00d429444000415410710550407a03c030401d040f804100c4c0240080348003042240140f90000e0401d410280c0b0455810f4807991220b801a60085102c012314000d10a0410301c1d000e492000500d00e005104815822132509400c91204260001e450101d90300d5001340025402032148604409800850390ba8070282c0f0140306c01c1000354010005000280e10500004c2443c10039055034200321500420404428041300e40c0c4210a801c201884501030028210180b1022000880f0403074606006081c84000000b40c01c0c1c981d003400b01940a01c4081c6a010026a0100030141407010083d482e0208664950f125680503500f141c26400d100e03800c25070f001e0b016210410404030191051051049904841c0c004d000c040101151928a600302600e02c28a60300f02c1c450502c0c80c014250341d1007130140760141e454252880c0350765800051590443d02e1114003c0349218402e001118540100d4500c0e490711401c01d19508200b15011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 663219496 1250 663218246 663218249
    0x3090e15030616020c09090109060f0f0b0301090506130218010602030a08070f02060a1104120c1505070b0a0203040812070c0506060a121103010207080c0a0302010c05210402030111070c 81
    0x210708845041e01c078107000000f400112207a050143e44484101e40403414140400c5600544031b1000150541450711f910b02a0344110548185d51581c500c0d024015101c248130f5030500c00c5043d402081032803400d81d503081d80d42c0320140c01a007002c0082a0441c01f150394503102c1ea1003140d0101000c1d681941d44500180d5070f0340041c041c3e0b47c00300b014400010003041c41140781e09521842d543c018001a124081380b070004113182444146030301c0c4100300106880301d100101e42d5040b0f115540740c0c0c3c20a4030342402c059516808010003000c008007001000045444502d82c00e4010307104071801aa680c403a40380a00e224810821403540c030301e00840c100080d6030342140350035107100d0145098400b00e580700740400c0240729490096100c41c8180005c51070204241c1050501408000380c001480c020050300d6110080d003124003810001d9000d0307001002016420b0180e0240e175401070600c03074105000c503a200c03804440b0b85203407900311101b030b000046d0541d982508030750b080480c034800490f550b03003003403c10340b012444c203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 663220746 1250 663219496 663219499
    0x80402041805030307030506130c0207030b010905010b0f0c070f0303030506030601050609030a111503040c080d030903050702010503072a060b2704080d050f090d031a060703090e15 79
    0x1c10780c0d80c10030000d851480d1850594840090b40c0b86a84001e4160002e0101600303442c2c22145800d006c0320180301314070408000780c1c160340007400317424075500e010b011482d8160030404009003000010800e032151141587c80c1c0603000c0d1201d6445194001d912840d01580c0e80c082c0c0010004034030008203240d0141d001e07a01807041503050303039001d0b80c0710b10034040b0303600c1081990340e00b59004115600c08180400c1c030504001c14024011042603a014455100641064500703503480c140c2c81c031003040038200030040c1006036021070409001c0c10100b610054040e001c1c030300c1e0103070503c08000002149030b4490050344403100c011341a041000300c1041412035003117445040455840d840c18902d48601c1ca044029040300c40d070fa0707020711001c44c0c41341b0112006001e009407080310016018800904a0f1140740540c5c1e00c100c2450500c05414601800c045140180c03007403aa10605150910006500030b2020807149644402c5d58150345d21103407403404a035585626400200c01c41d142d50107103d4406034000500c409184d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 663221996 1250 663220746 663220751
    0x90b04050903091f2a03170c04060c11100809060709051309050c100e01020c0a12060903021009150605180103030e0604030501020f09010215010e0a0527070812040e0a0b1f08040204 79
    0x142801c120110340042d40c08c0c3c04021401e1104001c031502c1240403809140c4180c4014a40680000200c1c901c55100c5075a030300403604003000c1002e480700030000d10364001814a4070f0f00c0d50929103404a103d0f03456640300e05071082d848919810512804006400c2d0740710018140400050854400a004070030400c003d40c01070080112040e414076116640106403108246400c117030076032950b680e4005010000003182540604580c2002041d8184280bc141a02958030008034841007143c41d0201c48554000178440d81d14407045044c0051514a49410b590b407500340f0750100349032074000945500032a8001042980002104200c4035410005005880020707000ca8048500c5c2c0e8403680f0103400c00b4001c030700c0c0f006055000183e4440c0c061b0411500030701c140303030310003510002075100b1092070f01111414000703540901e4080040700c1080014011031801e04007100d04081c24040314a04c05200038110342c0d0215140c541c000c2040e0707a0502a81c03861102d003e10304920828010020b00303900411141a8816031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 663223246 1250 663221996 663222017
    0x4231807061107210803010b030f100806160e030a0606090f060302100f0504050a09020a020708010b0f040504290f10120b1906090b04050903091f2a03 66
    0x2e002d040d4540c1142c20000203450f8450400d51404001094035010000302075000c008200030505940046001c0c1c4010400c060b81c070702d40040780c0026654007401520100c2a806810041c000d0040b1303110b50000d000c0204104400300d600b0003240c030540b0104885505000d90b105240400000b40c3c4018200d0304118020b00c0b40700c401e0324185040f250540310280d00240c203158020300c0240b04d003840184c1e84800d42080d9051586840109014031b0080e00250102c50340001c00c0000540c041103080e004180c410028803500060340c02145640c620490f41e5801280ca031808141080090a01d020001c1d001000c84041c0c4e00c1444401c0035081d50564200320300d511040c01099102100102d01c07825030303440c207120070042d17800c581c1c4404641d90010725150310110f2201d802c100c000500c4c007070742c0f004001c02207022071b91802441c1008126400038200c6807080e40104850034940d01d403840515880206200403007400780035480151595552584031054084074080032001d01d4001080a240c2e0030f019541d81030044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 663224496 1250 663223246 663223259
    0x9050c0a080a0903050715020f160201032904020d240608070801030317060f030f01240f121407151115011502100e0105041e030e04231807 61
    0x2140c100c43c002d40024420000d200120340d0a0035456406d188080b00140781c041315141c51388080d0080300c02600080100e400074029503a050180a0482d50280070309400a000c400d018440720300240c880714001d40d00840d400740c0c03421155020148562251f0411003e110341003007440180000b07030184a02203100c8401140005218180c824142c0341e26071150740e65481566945452840c0081c03449138405e081d0140d00e001500c0500409114a00c14030001c52030030040061001606107070040040c2c1b605040004100d15800050420112002c8100010200f019814011840b480b00700350290350b4071130102c0000d84481c40040082000112303030b071941c62110b880c0d510a40c0301d02c002907401b59030840800051101502455500b071142115004a030116050824050b0559800010f4500315035940d6080100b03002c151001e85402032070700c100c9000c1138106c0e68ec014103842c0c040c03401c2c0f07802144d44a1008854602d4900743d8442099041440415071901c40c1541424944041d840406400343c2e80300010329 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 663225746 1250 663224496 663224501
    0x71401140d20030c07061a19090b060c100b010c1e151a042a0207140303040e010909020121021b01061202090a2703020c031903081009050c0a080a 64
    0xa01c035101c410034901782080e202c190107029030180c107003491843c00f40c0c7c08003550348070007000f030507a0b02c0803820310741d05450400c0c01c000702c8039000006401014200130400140078042074264480320148000507003a000706004035a0b08145010003001d0020808504042d00070620806510703038440c00b45020400c0109018006407070058041c1c400e2084811154001c0f0314054000015401c1d06d144404424106000b00b03007016035000f00c098016030082c0100b4020050101415000c4500540003140341915003a046506090144208040d090b51174640000316882244c00a191002c144090000c6040620032080258400b0074108000300e001041540c2d0480180604800c880039000c0604030660b81c5d0f024000e07810360003844c84e24215990713600f024075035080403410b510803264280944000d902c01d00e4040e28100048034003600c40e900c18a00c401703c1c00300d588405004c0fa030341450102da1030384a4203103e078200b50f426003080c03102e2130a04003001864480c01c00901510100c170782d180c0089881d8075040404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 663226996 1250 663225746 663225751
    0x3a0513060f1b1a07030207060b06030c030c1b0d0512060406081b0312120105010807030203010e01061b0501050a0f060902161b090c020c01031a03071401140d2003 71
    0x4200380a00507007081c00815540d504842c01403a2070400034400e0766001e07500b04000ca0701d00d008661b01151403001d00c001031140780c14002e01542d586245050002a15480d400010120b1841607030028401d40e40c2c0e80100b248035406500d090844081c03209081c400781c1240c0004241600008021000404904d082d001d41d030112509000a00b02c1d50140241d60410a0144d9240c80d4161054500c460410f1f1260001001550b075900e606140d02d5040ca0300042039444043c1c13101c0205030041c00140310616800b2201030464620341040c0e030034401403a81924440100c03202c060541d51070700f41003000c07442d0180c000300312045c4003070420850182c130f4040700c204901074840b14004444003c0035070f10004000b08803642252030340e15941c11100b603680b0100415254510303208030050f08401c2064166513010300500d1042c42d9420204400440d00101183d55800c09108240004510024036602c5134051038034280c0140d4441d48851b500c1d081c003405000034004c0b803181400b040003024a0040c00c0011207003a01e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 663228246 1250 663226996 663227027
    0x80f0a150507170606040e010314010c02030a050301120f080d0e010b01020115090b0406030b160e0d0b0601080a110d0207050c1c0b0408040902030106030c0206010e0106023a051306 79
    0xe9600c0c1c0441c0ca0704141c0710f00500c00f5400100403c4041400501a44040c0c002d40c030400744900800c07190240a030a40f1203220201c0c056501c00c0c00759101c0240c0080a8a06550602e4400a24030322503040000c00c1000c0c406025017400070028954410b00c09070b0f00305031036038001c11000340058107070807004a00300c40340140090710007580283c1c20712052100e50840300c0208002000807401c280c603911a01095102030310b0744c81103242801202c11b025508007440c00c4440004890450400707035992955200a5001000345040040000000e03a42040170791090707100c00b410408040d03c99400c45601c81c001c0d8800703030040d1072034880c100b0406001e1600c42021a0080503900341818644101d0740e40c43c516070000740c022242c401d01848042406401803020314002c10503a54041400a020030700a400d210041c1c029a1400c400740c001404440c1d00001c6441140e86549079290395000d0304000200100c0e8050104880c100d00c80b000300204035030001c080d003c508d4448030302040f095510101550700c42c0d4038805a5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 663229496 1250 663228246 663228257
    0x12090a030303050a0f0216030806040615080604091b080f0609121804140a0510060e10020705041d1507120e0f0703060e071d0408090a080f0a150507 65
    0xc0c0300003446500103d4000403000004100144030210740b000342d03000803c0c0d1650803240356100c0e41c145a440107080b9006501600c1c200240d81c142041404e00c6504014550140f044040200e0000c6d12280d2101d1042ca401001c20302d070414445200d0901039525100d00401c5102d42d04403203911040220301e07240541c07203000080c030783c41490300078072207094201d2510101030b980340f009c0d240c201d40c40d90300444003d070215241c1620036207007881c075032005c070348000c0c1006040022442041c4902500f00c0c0c03950b40404011a0070200440542e41c0c224602100d03500a1a0041d0400501c0c941500d100c402480c07a46010400303480f4070b007480807000c4082e207408840c0740001800c2e140a4241448040d07000d6080b00071036009451100160005d96481c04040d680111805070343c0307485c980f170a02018440207020b8911400d0305104c00500b910501000c035400b40019000410008503140704d9aa680102d0000782000342c1a2405040c3d100856a2550304510b4103a4071a080088118400007030391103a07510441c100d403501d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 663230746 1250 663229496 663229499
    0x3041a0f1014210a060606030b011b021509130905010203093003100b030f15030a080f0c03121513061511010b190801180b04120207090e0d0212090a 65
    0x41c0503c400026801400c64064a94001c0100d60b0b180182d0000e00940d03240070624000401c00184103480340c0312039606030581c001d100d1006030f496840014181c20786600c0241c65219250009070009181d64114401a10703049520b01040b0064001c1c600ca1441c48060300c494000c00079024041406401143d001c7c600300e44072201742e0100c20f60265400c51707240405280041d0710307210410681e80c0103507440045200e41208100800b1560003050001f0034099015048144a560b203400e09401802c403483c0f10031202240a01e00f600d002c20607145821072908900425040110302d01281c1c281010036103000318401d4810822801c00307800307200102e5a0742043d40411004180701207071380d01c88105090901d9525013090614585d5500d4407041c02107800d2a0749800289007640c114215987d00086c2d5040301d050141e5900401c0c640c6010503405a00580034500e010181e080c100d0a00c40250003049245251000590b803007180020501d040c403415408a402c01900200d200c000c900800c44903907400a030f0b5180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 663231996 1250 663230746 663230779
    0xb040303052b09020f030313061d03010507270509070c060902100e03100c0c080d0e19020f0d02130b010c0c061e050406021203041a0f1014 61
    0x3401d060714000c8004582c140c0d200d01d0040c2c480504002c1c2c19805489001410070b6190081c0c90050200040b00107502e07001d00c1c0c5524a030400d041d4891002403100382201441b035003a0030070f40d5a01000e4001d00030402031400c52405000700000c40d48001d5109844040e000e0113811707442d404010794600401d000c00320356809000720341c0c1c02c44841d41120802d4560010b200141c82d083c00c0581580b946484040d01744000e1030a0502d00f4203486441e03c0058200302d2609803158110600d55030316500712024a03525005d041e080c40240c0307100c1840704064814807800810808000050003a12031003140e80d01c00c4102e40504101c10341c0010070010358004821400c094000340ca07503022044003d010304002c81180e81c0c80e211440d02c44d00796880344d03010482070900108140d1030b072007840d905003169081550500e07003005002940c442584503041115400080800c0501079042070510300407010f51010040c91500d500b0341800d0711780a45d1442d5520900010100740412041c00c202d1390060060000e816114001d803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 663233246 1250 663231996 663232007
    0x201c031104050f04090f0804080c0103020702090112051606180603050708070521040b0a0b150a080403090e10050118140402132301020c0907080a0b120703050f01050c040b040303 78
    0x3c0359280d00607901c1e9a0500046c4a0021400c82e1502643c01151136516100d1b881e0f00305411000f859040601c104421801030755140d50301415901720a031081e04004652070038914190744000340700580c0fa1a400300141c0c0c00c2c3d10140d26100c1d0047c5003489e040071603503804241c068400543d000e40101d030300440001c6203a4410f20141408010603410049141408010f8550591055409582818206c1c1c200030220045020720404c659041d100c000300e001d49a0312000050003400e02c1c800400144a01183c1490320440c480005040c4c0360b5000140350401040b446142d020b103120b40c078080b9002591080c058810b07092030034100c070b00714244a040c10b456001044000d500469800000c0c2d007524401142d8490411036081401814000d03810740601480006884d0800b500e43d114072030703101041044400c42c0d000e24029004040144041415070039540002e02c40f80510b8001c800a12802c80700106200f00020071907446c2ca941c0003304895100c1d410300301c0140c82a0b014028002c0410441000000d1049 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 663234496 1250 663233246 663233269
    0x10e1e010b221a25080304081c0501060206040c0b160204110403060207030818030306210c091617010b190905090c03190e06070c03201c03110405 64
    0x211210005030729000f081096415500d403842401c0c00104030180b644003045a05056980980c604c0740c0f034150b00b9540c054903071000903c020451070002c604401d01a020400400785196a244213000940c2c541400a5441408030340030750b0010351240f000a01051031104545401401090300364402e6816000e10020300000c0244107210101000000081401880a441840d00c40d550b114202c1c184210011040d08000024003461380003001440b0b4150b0340c1c600c81501d42401006400170854040005906104846518a1b04410484108038050511841011a03d011901c2d02c8445480c83e89030b241685000340105004410100480e0051900342c0d003494200f509035240044c180c0d515940802c5d004001503690460641020060240c00140c00000301404404441d0800110b401003010a50340d0303070090325041c00c0c0603041c441003003070600ca07c540d001c1101c0918001850303000d6800d06e40750f9500920b500111a9402c4e1003810b500240b2a004003503401c081f4040040c101400d0504012014441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 663235746 1250 663234496 663234547
    0xc020118030e27181005060904060504020303270102071d0106030203091608010c1106150906030a0828051e030a091b0e1e040b040614010e1e010b 64
    0x594100d2401a0740f0a19058480c8001840e03c00469001000301c0e0304e045042c003103114405040c90200070090b100d241c0351640c019040300d00444e8a45480c00400d095124428a0361840d4011038114013000c3e101c0101c903d9401c2003a0300700c4000a0383c070420320840c5003290210608055070315004003c4c02d4860340103176810080c030400b964042c628008480781401c50310b600c000b0407651200644070440790461500682c0b1002c10b000b0340903619241640c180b918510190302d40c4207007030780e1000c0f40031601d040202041155101003050b980c1c0810f060300d45985894210800b0202c0b0050000d0b03c1110300c140c06841c100b83c060312800040601140864483d07800081c10400115036030800c0c9d00200d05005c120b0344080030700e1010030b40200c0c24118020054403000f040c22100b018440210080c104003001c595601680001c02854251503919001c0042c203400b440b4254081e803450004580c404011640074040d04540054500034014404440d00c010001d11134085009002c1c0710401851041c0c0d4800ca504164 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 663236996 1250 663235746 663235789
    0x14070605041412070e0106030c0f020a1719030209150c190f0c03060e0609010506031902041d0d110607080f060a03061b020105010f030503040b0706060906090c020118030e 75
    0x607403807154905080c0d031744006105820100100001d42c0c043c4190344101c812803a054402c0c52195801a60b100706411005000501c0d0703444004105544806440580e03680c141410000602c03c0d60003000b81d084059200e02ca400920545409005143c0c03c481d4814507000c040e150900000e40024a660078014040d1015100031781301d900002d6800082e080590311171000015441c05980000f490508002c1c05106107a14010601010355030004049512802008111500781128400705000e13140e00c011111007201025414222a070021821601070384c425a1a141d040038512a081d0740e84000fa00c08401154688020440030a80e00410607032243c0c010789050700c40c5a495036414220b070f40c5e0200742284854440c00114a10364280540b0340101042d0520719406400c58a80503240d103d40d1103841080400040c0304820040365801c400d000f410304080402c0043e41e00c040030030240c0140c0300f040d0010f51134032180d030410510840800b0112034140d030f40c1d501d40d55541c40501005820840d4100305518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 663238246 1250 663236996 663237019
    0x20706051b010903170a0b0303190e06030702010b1005040f0b07060e0a03050c1504082b060b0a14122d130c0501090e13022b140706050414 61
    0x402401a41c03e000e2017556001e501c800d035610380c141c3c00307207001d001c1220030b130b041203a510390039070b030010a803203d0a00f1000500408040301506655054020003041e40009012080260007601903001c8035240700207441030150040150b400301c40e98840c0e8000d900c90955468020b100300680c000261080c4c81c0b20340d40000d08209441c99142c41c1c80240b000460000700300080c0d140c10188180007218451b580001d03498101d040941da4030413175004000d0b2202407114200e150106000c0c8001750225092103100003009035984034a100c245d5a07100e14408070105204d84451024003100c0401c441410501030b05c094001d455a588100b1421104007014460340103d0000391b042084900b0315600030351801d002c4084d954075500e003422070314050341d100ca814001c20400c200201000800c07038960100005444ca10003020310300c0000e049049060194550006070a0f2024103461401c248a2010b0300a1040141803410104140d41e520442d0040c05d00040003030208101d0382010700d85143c84940f0051909410f003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 663239496 1250 663238246 663238297
    0xb1201021201030c08030a0806090411090103060204030b010b1912150902070209060402030705030a09081201060f02010f02090312030a0605150a120c080609060a0308031f0e0702070605 81
    0x81e0001ca05030740c070401a48004100700540c0c50701010050844101440c1031682031400038082c014010541c0c0e0003006007000003410400d0080e901001540c2c0100188003c0d6102e0a05200030b400070300003101e00800d05030000c03540c01260001ea514003540696003044645102804a0b80c91045501c80c201168031071174001d400421484504000c1c254030800140c80c2c00312070040180c83c4e5005420180150700c10000e0004a43d80301048a9020b54008000706602c825841e00c099203214503441c10903c2c1c3c00100001c10010383c0a401582e0703075100c0e54002c0c040d00819140303c004078070504001a901d644080041036844e401305001d540d0014061000140345603888c0c01041c0a420100744182014030006040d54002c0d810607900c1c0c1c2010b51208042140a46d07880d07000d407510f00e02800b010b11900b000d200180040d6105903000019503401406252203050140c0d402c0b0540705c1d448940c0d9014a025040031410000038108070340b240102e603004000d0ba500d044000d0718950f2040c180c841985683c1c200b180f541 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 663240746 1250 663239496 663239501
    0xe061f0e031c0905090c03040f050f060c03240901140f03030d0b0a0b030603030301030303090f02040c020705102607090f080a0c080c01090512010603021c050d02030a0c060b1201 78
    0x94051404840e03105080ba035100400c40c03034003508418070480c080d905101460b107940003601c1d48203601580c1d071600581030b420070030302e010013401d0b20049500c209010003100000c580061800340e040c080c000420091118003100d1080d4030b080d0b0283c0c201300003000400c04000c54180c0340d00714101c0548288511018074010904503030141d00200380d403d40b0750115081a00384620640002c201141d80c5a0642c2044030000c1d440e0310040c800a030416456110400c00d000040e81c9100c00d49500420420172484c00f600040d4031001319100d13840c070410001d00d5480b0f1060045644030240302000e40c441850b200c3c664802a9070342005002407081200c1c450780410b4035486094448080c06403000105224102450600084e407060380111066410031400c4860341d0741c0000d51101503d0045070441005120326000a0050202e40d101950102c1d115040f200c02454201207080e40350f0244098514610101109030798030301c104e50f03144002071180c2c44c0c0f0401066050b841001003c00083c0b45030585100030010f01c0c01d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 663241996 1250 663240746 663240763
    0x1119030e43080c10020a1b050d150b0d05150705120408030a060902091c06110a05031611070b03070c06020a050a0f02122d041e0e061f0e03 61
    0x141291451040c4407040c0300700b0541908000403180e00d002029a400025202c0001c1c0c0340061400f404107c61281ea1820045188080c3c20068220800342d00c0c0e50400305411080e5900017007145d841d16400000d581000030500101c01c1c1c0200041c8109000040804d1b080c50300146100d040081c00c2c0685401600c1a4802c1070145005618058890070000b0310001100c501d50f00001a0520420111541e03132202c0c2e9450b03075800c1807070f0305011442c2c03060309100004d400d003007080724985a0001140c02e04a500000614021042400f4824440748050003d450040303880e01410050f900c0b412040049a0102e001161b0041c0b9a00d40700d44400340d5991140140c0e045030000f000030500109403034003419440350144444039058401840321407400c525109051082d081142154001001c03540380303032903025002c45c0e804040302211607601e981e105082405540041079491a561050350000344040850184030700400d00200042482e0160902405810f100603072074500703022000300010420f0360148907103030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 663243246 1250 663241996 663242113
    0x3060510060f0219140f12071a01050306010506031506030703051e0121030309050706050322031403042a18050c0a050f0d1119030e 58
    0x1800c1414041c0c0909680b41c1561032004540c401606507200a40f056405071250390072065802e480c02900c1c8141c1c0c1003030300b00516503085110b11740383c045440502c0e900070401c6034042c1051040010704440d04401a420a120b4113034540c1c480c0380184098a001d00003150000701801c00034840780100004070348035400403540440882d90310010007c0300e041a54460907011000ea00c2c000700c66040181c8400491840307910f035103520800300c503034000b0503019600c038045079034001048540783c95845c28000c0a542c0210340072440e814803240071400354500741d1903081d01141d00d84c41e60140041e0321100000203400c010000c0c4d03500c00c85242103034002d0504000308001e00c010380c5880c410560400c40604c0e01c030702481c408440182e29144c00c121100b00c220f000c0e00c88441d0149052503503200444401c15aa02860308611409841c208203030181c003002a0003482c480843c000001e50340500fa01d0103408481d56079051700040d030800042881410742e030704409200550506006640181c580c2c5020b10515940c10751701 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 663244496 1250 663243246 663243271
    0x70605041101030e0328050f030103061b050f0a0e0d14070801051e04140a0506100317071a1807090f06050a1a0309011127010305070c0f0804030605 65
    0x8141e1560700d40120100380c00301800852a00c6140c404d02840780759000204e185103d129412880700d10710a00072249142e411440c40e42d01c2c1d503103074180f02004000280014185481124400c1040c0780035005541d07030b48403801c0280d400e100e6044029910002d11512080c2d011120403081c000180101090b40c1140794510b0051a0060030508000d0031036502a0645050390b210581100c0c0a00030111b60b1030344964014054010308410744680b51a00c00000c070024901e0098500b0000c03043c01441c0040203e9016283c00d456400654645c240248600301004e441e0b5400030340a5684040c0c144a05504400303140385c0c0aa8856043c005a802c149880d004002c3c00ea0715090101e50b421000d01a44000d00400c450f8103808610741a0100a1180c1150414101c00c502000013044420f00303600400795402480c0c0040d540d03c9412501d14a145000c40b6a140c0c0d8040c4e90000700019442449100c0c81000103840b0011aa011a203410310300900c40071080f24107140401001c000201503011b0940110000c9148 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 663245746 1250 663244496 663244523
    0x3080c071e05240316090515120402030f0102030c09040f0b0a0e0907030c060f021005280603050d0810080a0b0c09010c050a030503070f0801151407060504 68
    0x182800c040d041d5000c1c1004103010a02031404a0a0780001400c4a60844030109040200e2242410340b01c10074481c1c1000340000300402941001c04c4c441c18444d0f43d030954428107039075200d80402c52081290078907104c000c0410300000c29420165154243c01c180010115054044030b068110b0036a030048a10fa0003001c40810252100e04060044060703141142030188075600346c03c404a801400c8901c80c4649074941c000100380d5030a0148404406180c0040360807044944031503016108a00300b140c090010b12550f54085030b0b0806c580304007400382c040700c1003032131824101c0303040a44951a43d440007101260703140d07000070005901f00800e91445a403515841402c0c5001240c00c00a004030b54009143e58000a118900003000300c510160302101e01c130000c548881e07207080100d96405064200800c10300c990040c1c1414550001e015621503c00c5541d0403130000c8446404907200724081c410f00c01d03d007561005500386e2501400f81080240d41d021080c0342042c501d074903010151502a1015100d00000511 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 663246996 1250 663245746 663245767
    0xb010306060906061706010323240d120f090b0316091203210b0603090c19030b06131e060504050609042012100b090906010308220504060308 62
    0x1502d00140043d00f070880404445900000d05d09070001c1003103040541d40e0020710400341c1d01e2544028409203803000d0303040602d0011002c1400b030410038500c0d03010140d4504071442510b40441046006680715540d0038000c4095001690040c070042905818419040c3c40490b050f0501d2014510600480703050040e00390030060042e003150001d80001c0440900d0300c3c0010003280e0000c1c0075420066585d070691100c141480412401018841030703ca82c460340000a010a803400014034294084040310986994984141080c0c107545280c0300c0100044181c0002030768900e000101001d10303400c0044040b42000e01000f10510110300c0c03c611b40403d95949a00340014142842040c2c2c3c400d605540b1140c550600d51202050300c10b0007000215081c81d00300c41c4040c03d07154800050007240c0305408407000c4100382e80500c005410700d080c04501595889000407040400090864120390700321681a00d0180031f0181c1c4034a001012020113601600f1401c0041c640d240c607c00c9100450060141c184c903150041c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 663248246 1250 663246996 663247001
    0x40f0f060f060201141b040302060f030711030306101101020904150e0a0605010909180c0b0705100b010f0f0212030f0f07110706030e01060f080106030c1a1806070b0103060609 77
    0x1004002161701d0641c2e424004016000100c2c0c21a4095140645120700c2c1c0a422429105075003000b50098004212481c013001c1001c080c6008894607110f080f4120070700b0003816503a002c2180d400380c2c0004041900018913000342c0380c00d41c486c0b01d41400585400f841c0310105094602c0614446504c8900c12001c106c00d0f03945408042c1c001c014140b040c4120741c1381c100001c00100320342c010302d07580380d65416202d03a50386076440c030700e0b154030758400032043c0403640d128120681a0403440054480e40101809064044441d01c1145c15452058560105003a1041d904503100c1070701c035181c1c40c298801ca000003501035442a0245209111068039401c2034a003c80003a4141400035001c4000c0c4850f807094044964408620305043d2656450002103d1050f00c102c01c4c01341400c1d50182c2c89154119030041040c40041d00080300341e03405081c0320040103641d000e00180f4000f00340801441107000b808940090a82680c1005484400a007054182502600c40d0000c01c002a4000c4030495510704041000c00f0590 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 663249496 1250 663248246 663248249
    0x3021b0106030809150a0e01111507110706050c0a06020c1e0a02010905032d01060506301909060e01150e0919080c07080d05030a0b06040308070f02040f0f060f 70
    0x14084d440c14821186d801074094010050001c2c1801408060b2010f13080f01000116043c43d4150012102030030610f0001d0180c900202c9401202e000ba4040480e40c240130700100c4d84240038000041c40f5148683d19803c000b0341080c103405100d4000d040e403840401d0143c0c182c0d06949600c0170041d201040780303440054021512a80480d00075000345e03070b65803812460480681051703110151016101e05403004102d0044c0166000f4580c828008151444079100920805980555100c0708014800604400281e4a40112003468101c1c0103009086100d9009403c40c5910700d1080c0c4010400d26080100307a03080d64040070300c0c1e8400440b65030040066040f034002c0a41c01103100380c050316085c1040da10f84a040c10880c0c0000c2c200c0a00098000500b400400148004103071080507185281507000340144180d20a69143d001d0f103013000004851445d01c0e4044500b202d81c0400d031203203000950b50b02c0c48001040280141d90041d961030542d101e002a03405443d00080a02600051036030600e044042d040300030703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 663250746 1250 663249496 663249529
    0x1801120905280f0606180e0d030e2401050a080c03060c0901030b0406120210030204080d0c230709111303060f0b040f0b03010f090309051c020607060e010b010f090603021b0106030809 80
    0x8094100351104400702344c00c1060a8280b50200c3c941c0d414011240c034040f00303400049440b0b0b0809d90f16030004448200c103e03050b80c00031140031028999454001c1e6480310600c08459242d0401c0c0080f84d44851040300900c00f41c0010b04001c12814000c030001003c942c61580541e040c03a590600b10403c5240c03100d08641203c2ca0303800c1c01c41c10305050540f042c8e42d558022001405110381c00401c84217020914500002c1c2c1c820042004c80301e5040740700815103407102c81c800d1798242400c0c032040903a42c07643c0c0008d9444c0c0f01300034040210705a10710b4a501002e0158041c4901c803199a5500c86815030b100c1d802000c8050f030480c0d90100f00701c640b00051500316030a02c03511600051401400c0400213510084084c212142211000c414012400e0015100c1840e40d00c025403040b00020381204102c080d811080e68019800020883c00c1d40250043d03a08038034a00108001916404050120703d0007913001c0e10f00a5900781c4200c0c90340c1c484c0c0b003103d402c41c0c000790000d0f036549002046021951501c00311501c04010b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 663251996 1250 663250746 663250751
    0x40605030a140c2b06030f020a08010908120705120106180b090d021002030c010504050c0f0d021003020f090a0b070605060618040c050f1801120905280f060618 70
    0x1001440340d00306000360101c0744c0e54102d00004202c038a001c07a40e0780d0400ea42d981d120401c42e81c0e0762845c000e81c00b0310140750120b02512210300d00080c0b0780300c18031071f1b00101a0450481c920780030800c1220308043c07900604140c01d11200344503080709560054000b5000e00180d440d03034082000600344081d000c800710750180d074903688100688070060719002e581d080c0060741505c64000a03108803109030f045004101c28191a5842d100800040c070600149542c4242e905448010b106803c55040c05202e080c40034019410600b1040b14440c0a0710076401080070384003544805081c0b0200d00006003d07041d8650129030b0000010424074103100280c070905401540444e450f07407a00300050590115210b4059841d0310070b035030320100600c8403401981115045000790000c5681d8084504e0501c04480366a0b5115000800180501e14080000d00c84c0e2245c448e0010001c02c1d03005100501c4500002d02c0b00035400d0450040440440001c01170b00302040c5551007008081185401e01d0508802d42e070500311034050b101e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 663253246 1250 663251996 663252001
    0xe06040b0a021e0f1224090f040b15211603020d1e080d1e0c1209050c061219020a05040306091b0602010b1305060a050603070c0503040605030a14 64
    0x8041194214204201d01c1403d511803040260a14290207442599080780c162002049a0441a00143c000c041d0703072540d42c04c9920500704140709008401310340e04610803107880017103404100108038082c1d110181b5a4100030031b44c0d484020130b00581410949034003040350310b0124090b01034244081c207119005415000307040d82c51900001d2800314813450150200d41c60b5580240b48459040156054540182d511a81e13090084204e100900500b15264020650078180003141c1980c1d00888000180c10b90fa0110003401072804000100001c002c03c0b202803161115000a5480f0900600001001010130200c43e180250a2800300341d5040b010f130880c18070400540e01c13103c1d08001500c0c140d0750480400101d140081ca0441c0300c41e10005003042e00d034800b1620000d86154150010740f2034110588240008003600d041d801c065810a940f803e134000f46018040c401420000080c40d0700032107624000300c2c049500d40703030f141c11940640c219000090001040183e1420203009800703e280e581c0703940c0c072900e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 663254496 1250 663253246 663253267
    0x405060303030408130b0414040b010201052703040e0f04050d020303190b0d051005010816080c012a050a0c230103020306190b0304060b0603010b040b1c0e06040b0a02 73
    0x902c0018002020984042a1402c481000410302005003d10341d1005039610780b94404038014280d01c07020a031090b0b04101c1c200b5401d510601441d406204411800d420800c00340c01c40c403210303d096110b0030889220521001903015410a030860081f80d00c0048010380e405c00d81071180c14485504000000d662003003050040d02042d09000041106480d00c0000c0c2c0c03040320000203a030209440b080501180b03c2c40345541d0001450398080e0f4101c420003012254400540d0000101044080c07103403070300c941c000710421026540078820216a0303045032951003000030100442260310402000702a289170340704c40c50000411040d015503201030605440d25111039424000c0102404e9108038000c0e0406070048089001516041c183c04529030f224018481c28685509030442107403c11a825202c0341d00f0005c103503034a4240242183e06952072004007618290602c01c3c0716109900060444000ba10b80c0c0e40030450304905071094400898141d00034103440d007041e0400c01c1c0300e080c0c0641808102441000b59035402e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 663255746 1250 663254496 663254503
    0x20903100b030712031d010306030f050d08130201050403020f0609060d150e090316050f070b0d05060f090403030c050708030a0902090c03090d2f03270d03030e010b030f0109020f04050603 82
    0x224000201c1000c000c106c20001203004d8080e81c6d00050081c41c03c000c00d83d007085008940110b80000039514604282e036166042c0510141c0c0b070034041d0120340104000e20242c2004080d4203034180018107001d00d0103494001040c9540c0c0300c0040001704c19550408804d1140303020854078005c04450344800c41c0d0303081c8100401d84038030800c5148508203079840c00d80001c00c0b07014800b082403100d00e02d0a40301802da445000b010141c2c0043d40c94015940361100007600c524007206c0b440c42070076015182c00ca850b900c1d55410b40060407807104910070f0040500000000500e058004c0d07114540044021800590034818040500e402030f00003454400309200300103c18a0009500280414602c0c01d88204400307002000303042240f41d0003281580c005111392242100c0008020003019158511498051411481081c6075515103079030103900650a12100011038880d030484d101138440040000307032058184001a06c0c00c1c3c0112075021050f5150030000e0103500d083c0c4510040c100741a50b06001d14940480000d88 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 663256996 1250 663255746 663255767
    0x111b1b0901090504140d0e150c150907030203100b01030c0903050d053007080907150f030f15180509030a0c0c0f0f0e0106051201050402090103020903100b03071203 72
    0x100f50740d0700015041c000c507080581d02c0c4800890a56030b00d240242d8004010104200055000d03003a0080c004660891803c11a113050900d00b010b814030305000045082c14410241030817038a8400e220020015942c180300d070950310003c070b180008403264110000740c01d80d01c000400509210b158101080031801c0850a41184192450704550741d21101240342c41100600c2c04c14107950702c41002d02481010700f000caaa0007014a0f40f9a2241962204821a602c00c002e0041d00761003c90f00141e401000d0103407400c4010180b1905010503a101c201a40344202c40181d1a03440881e40040002c2040800d444410740d90341800131010702861800328915540e92140040081c02c01040c5600c1d0428080070011501c0505004003a1034468ad984442d00460a0b416004001045035031500001c3d40754010310864003880d007030300588000eaa00e044200402500082c91250516070200b0a070300c0386543c14451407800c2c0b00702e080300048a480f00e10600d450410b450300400e241000c25101c4001086c4c024250a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 663258246 1250 663256996 663257009
    0x903020d0807020712050c0909060408181807031a0604211704060f140702030613020301021306030603060e1f02030402040b180402010f0813080d111b1b0901 69
    0xa0684401c803041303103090075692140c182c450710021030208100002c240360280c104111850016911006080303605d41d82d06803802000e4042c100003401b11654002502d1010740e400400788454580802071310140403d0480c2c01c0c5001990b100d40d504800e12190800407586842510101d041500f8051115010300800d8000c2d005010315410840411010300060102c0c05290350304175071181c0e0345a001a042500f5040044085400c000c0705429408030a800c0c2c032001034000b4014000c40c0c680c1581c266020482903000c0e609550200200e0301c5400e040c400301c40090019540004456185080a0f41200c46450a41c030131034014180c9400b0242c11101c00d1100071019400060f583d84640c400900284440e00c0341d150400e070000800441e40980200044c804c40c000c3c0c840d200c074407401180407940000c0803510f1120040c0300080040200d5130345006020f40340c0d00490001000f21406944851030f4021540d190040070717001d00d000328000000d01c40d40b4014590748070450018940040010302e000c00501410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 663259496 1250 663258246 663258257
    0x40303030f090c0f0608010605090f01120b030318090903030108060105150d0c0509131407030906020c07121a010b0304080913050c1b0f0a060e1e0d0e01030903020d 72
    0x210700c920040e031002c2d01c6a0380c00101e0740843c5a4030341003000c68044038420800450074040000036210301501c125091150014a21021041c00800540e032149a40c0740414402e82c0d00e50400d0110f4038204004d1581d101003080c41e86480300104100100038100178481152600b0034001000030344000034409054501c2115520a01603001c40c640d030b200e014448500c1d81d220b0401c1060344076950000300030415200c060b81c1c0411300041c0404801c0540c2d44a4200100000c07000c800118010f100c2c0c2e201054241c42161301501d0031843d41000c91411381e1607007104200c145002a900100820000481ca940c8456100c032000c035894001182054000100041d11001c40090716040e199134044001c504281450320030800f6050003c1d000e032182d0000c1011700d59803000b00c840b8041c3c41200040380910722489200420402c0e0403a9235507000341c0110103400c0304600c90070b0011218801d8460b4440034248100009003036070032180b1001802d410310440c90b5414586005100e01c00700760b0102c1c01d0700e81d11000e130529 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 663260746 1250 663259496 663259511
    0x81501030f051c05040e01090c17060607060f0c0314010f12020a08061006030b010c050604150209090705120a1a04051f08031c0b09010e040302010f0e01050412050301050604030303 79
    0xb15050020901c10302240380314500341d070204690404080c000382c8580001a000d9680c0b540c1003241242d2a101011012600782c0c801858144640052640e04c204003814107401d220060703507060700f0344d504d0581ca41600740e00c940384064050b5241c41106400820340b003031201203514002e08207242180c180984000c510341501c1076025034499440309001070000000701ca5061078001c0a000c007100c0c803030180c1400a403e00458405961080e03194140d00f0fa000806019241c441e5a502c00010603002000d011007902800402c0f45d0ba0b4884524504c1600b46451706995a1a58500c1010b0500010401c4a02c28540b0318110120007250720712403202c01056900095644400703000013404c11603070035203000301c404503140030a00c0c0350040042c050b40c44034032018a50304050280c40f2400e641c11310350f54580100300440100900e582c1c0160032a0007038000e000000320385031580802425103034510419880e582d1580300788020455804503203481c4d50003614100741994180000a0079500c240d100c0501055180c070f68 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 663261996 1250 663260746 663260753
    0x2041e051f030219020d08090d2703080a0f090806010f060e2d03011d1c090806040b01030b0618061216060804140307050a0210031d01050907081501030f 67
    0x48440404822030704c5030401c41444002599007082c0c03600c4100241141003c180c114a00040c2042000050303104c0500b03046c590302c54034814185c2e1410b02c24103200951230010104070000010548101c099070743e90031140600300080d24041142d84404040e91006004000802c0b410104200307551191030b050300c42041000000398070303c0d5014065a0880803021b019582000e045203883c614840c02d600a200741e00100c254000c0c08460012546010b8111070710004075400080d1894105099905181966549442900349024811076007140d42c0c512000041c014424040310441d8446000c468500c96000e10885c0c40303c1007003000d09031600400701c00144070015a018407103002d80044205040c03180a43e21800189842c10940b01903611601054158042a41c048101c4a8154200d00105040b20b901e5080c415521283c100c524109540e80c12040799410b448810420304400801c000718250900084490812030182d12843d855840b52103103148110f80f100d11035044a801001c0c1c25030b94040c03800e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 663263246 1250 663261996 663262001
    0x306040303052e1404060f031202030d02040b25051216050312070f090b0405090a02091c021e091b040b160c0506071a1503030c0102041e051f03 63
    0x704041846610382c11030024141c0c0103070810081300c8074807800783c1c5030714000c0e0140710403600c803030182c80c3c1424a1800140b0116a45402c090041c480500c1124a4401014030b144104c3e080758001481c141c10014035907627240c035102198100100c502d070302514040800d9071440c0d5201444071582c0d641c40c03808202d5041e404c00241151380700c1c0780c03c1016203994400301d0b04c584440031402c40b0500d000c40d00e840c9082050b18855244041510111000a0b10f014284030800001c1e500080908040c55000c00c07841040d515100d403140e10080001d42001507900e603034030410036403d441046040c010790a00c00060306503034424038101c3c3c0041071400700c2c81226240d032043d41070038401ca1304011090b00f000108180c0a000d99142440b8030303402001d003d085a5200d9081016600c43c121020f003c0e001d114801102c0c0c030140c0c01c00290000c400035502e402084000c0007190960b080030781c0500703040e580840c04010f038040703000b6841e10b0344502920702c150050404000a41210b040180c1440015078010145d42c11806035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 663264496 1250 663263246 663263281
    0x8010b160c1a03011d0405070306020702040f060b07030306080309010c031b020303041d010f03080f0a1701090e0c030c0109270f0b010f020109080d110d0608010203160905030604030305 81
    0x341e003101d010440d8080714200030b40c020700c034040d17800941d943c8003121400e40842031400b0f10b030b0017005072514a18640701d01020b500107500036030380160b07184010382031200741c0d10400e8000c00c41205402d0b2140311500303010701140d4003940300c814540c00070401d403940c0d80e9000f42401c1c000c56050410240041c0b02c104038000f00c04e40124000e4051000060102e40c0906c0240012510b90500c4060b040f507a1321451f403450032781014480249901760174480e26255405034400380409111500d000090702e1480041502040000c0c0d210b001036a1703507180070212006090014143c807000507801003c81682070f0000030f1007150750384a40c4200c218403c00d040e0003102503075234801c100a8008801e001083e10528228001d0208540d0203002c40c0d144c0004048803070041c080c10050a4000c0c504d07500b010301190000b4040c10f000012000500c0c420010340e80e0841c2d080c032031400a03112030700c001a202d10348442c0f03004030104440c5203a4107104014a04200c1ca550016100d45d010b50301d4500407a8a845085682ca03500000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 663265746 1250 663264496 663264509
    0x609062413030c120203070306020c01020c122a15190f02040504060e100527150f01020303011206020a201f0213050d1e0605040201020d08010b160c 65
    0x462030309a00340c40315420250b80c010480010300541d03a040420511310b984a0080d0141c00c035000c2040404e086501030007a544140001500c1d2150782441503003026120b40120840303030f0380420b0f60400048440d03640d40540910002500000b05c40c0c040c041d90300e003520945d00000e4590200084c8142816081c2e01e034586840080c240640702c0b0f0b525614000c0e4010380907481c02549400700020f03d08561180e0719000300d0259600c0030b011400c1c1400d10200340b0300081c1100041143c45038011070181400713501440f5413140c910141040520b8010084120040c00801c2e04661041c0014000b0171482c006000240340e0202c401661400c0048055860700c80071282034501c0100004000d4644401181d0235824501100c4840c0701c1c0343d402070040d41280203000321040d40305083e55083c0b0079070a000322001800c0340990082c0d48883c07c91401803540001da4003049078140e480b4018442107503010040400038141d141000c0d03940d50306110204050b4041c1411402461000d81012014400b8440d110300103005d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 663266996 1250 663265746 663265819
    0x1051e07050604120f08070e19080703081e0c030307030203090705060301081c1d0609040f1d01050c070f021012060605041403030406090b0307030e010204150e09060906 74
    0x819041c9000075040350100c0c007005c19444900c1d102c01038425508240305484940315240c401d801c0b00180000d10710951503007000c00003030403c042040c4000700602030040d4400d0302402d179a0444500303a550084010754203004000c9d0700340019844600040192580407102d89401a140d40e268158107240c4000c50348082d800c844000000b08000b00d0103c0d0120500059110003507001042d0300040319500445102803609a0001440141c3e515080c002052184001403002c25005030141e00e0790122120205036220014802d1881035041400780666540030607188981400c00200f601c543c800c040c110311009200b007442900700c9031010301500d030010b844084484200012601c5034005840c2ea4402d0043d42c451a071407841d0f206a0b46400400c840c1610501e6441e00500d5140c442d42104a4001410304401d068030341c0f07000c0a06842c00d02c05400144400c40c0c81c0c030802c906c0c840001c0d00f1500b1401303805000d03441c0d503800c001c2076803200c0c0100d5801200690300c200b8000e100c40d46003c800b111500c1081e11022 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 663268246 1250 663266996 663267001
    0x20306060112060905071e2a0602040b0301060f140414101b060209010e030304030c0b2b05040b0c13170a050601080c010f02071505030c190314060f01051e070506 71
    0x47d0301104441d00c1c280f0320024558000440001038400c03a221290002c00201146032003803000d140444c2610701da500c140e40143c141503d440d110340c11a003003600024000b034402d81e020302409910a084005150441031024030b01420a980040301500000786c45010b00d001790074401c0303a18440c61a2002140140e540041c6940c41c81c9402c4019501c1680010700085906040300614500802210b0469a01c607002404807440d01401040075000794200c0e4048103d500c0d9502c0288011944000080c0303076074070000030306250900e41483d078408041c2402206800600c240300034a80c5460303040c01643c04c03041c2140c1c2080320034107540c0d1070701c4043d441c010708501415000141c0c0030703400126201094400d807150300c0407440d1882e0032640c6402070701c25106071142c02d425001900717005600031600f0440a07001d40d0718050f00c29040f104c01c40c800c2214100029507034000d0b0b6030380e904c2c09121180c01c014101e91a00c40150281c000a180b0300401d4842e18408604440110380e10f03802d00220341180d030f03002c01900c1561 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 663269496 1250 663268246 663268261
    0x804080a0c03110301060506071b0b0c0706120e0a0609051002040b03090613082d071202071403070501081503190b06040b100507020102070b0315030c060304020306060112060905 78
    0x103010500c811214140c0758601c1050344e240c103008000c20b0b00c1e00908042c0c2850080d80303c01540400d51101d11100740384450012460030b40c128018105440c00100070304007645803040040014901441070760015150074140502e82d5070114440008903040b10b00481e4a102c0e9081040c01c0298800100480510008000400f1031104011754407400c000703025140a55900b490b050404544042c008052407410001840040a4111490f18612000d0543f41c00b90340c51404080d038980c040300c400e45644204411006190354100010f038042e00c5001c1280004042410100756650010300555040c064400000380304504180c00e0b0f05958a0010200c46000b00002c103100d803450034050041c0c1d40000b44c0d5001400d1800c05000e006184040507028081c1100724081c00c8601742c01181040381140204140041c02c014050302450155504039024800f42d1628003c0501d0f0180e800304081c090f1000784100005030750301150290344290f003802c1c00200052210b12080040c5070f070303400074203240346000c0521599 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 663270746 1250 663269496 663269513
    0x2060307050721120e0102040b1e0403120905030d020c03101a0d0f121403011701140f01411302030106080a0f05040f021e42090d0804080a 61
    0x6407a03482c1c1c010450040015101d1b401d030f00c40d0380a01043c1d00d004000310b4102c000d90315404050200c50300582e90810703440340e45001c0e1401c1080403c40016140c1c000a10261070240152490619280005c02044420030b0100b91210203111946841503a01c00110420300c507045405d52250a0007031103520201076501d0700318142074004206503074210003080038008407809540b0301c9512a2403080d00720708680c83c020170034882c0ca40310580400c07595210b0500751110440c1c40203050060768001c51504a940c140102c500780c0d21000a0f01c004041d240c2820741c1a081e40d513810000b0074070041c0030020030b14031000e03010482a405141202c101103100000004440703503c10a11b500514292100740903000e50348881900307070b4005840107480501040020030051410b8010020461419401d46004000b02000124a02d50703960039000d0350f2146012103003400300d00382d030703508823659202881080740722018482203110b000b104192401980c5004295061068800940300102205c0d011920807002d41e1514109 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 663271996 1250 663270746 663270767
    0x31030302010c1110050a11030414060a1118010e03060f060406050a0e0a0c1e05070203190308070c2102011e06150804020d1e14060402060307050721 65
    0x5510b01140488060720420300820240b40c071000820b6041c03603505200703004000281c0103401007556201000074250541c0d000d9881140940c090100c102c25042250f8141000181040b4140b40b400c110000c80d07040800580c3c201c0806421232000034051100103840d402e65048440e41d051081c0f0081000f44a504540588213180071b6400703203e000d513500d0031300c488a4a40e015101022190760009403140225a00c080803214007850903011904035400100d00e2411941c20180000c3c0d00000c00c801503003010400d11003007034040154a50b0300011070728000c01c400c034058100410020402c171240c0c02e000e010556500550080c406112406900807401b90081094a0700b881d5008044045114452954420b8108550099018818510108204480380e0000500c101e03400103070202d420b0085030202d41c0c0030303041506940814a11540c9820802c0303003469204809801c5501c51000c00005844038002e03250042c040b41002c0c0d44414040c5070200d03180c2004010f420703000110503020441e1a034800c20701c05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 663273246 1250 663271996 663272003
    0x2090a0914041e02060f1e040602240f130501110427090b07111f02030103140a031223090d1115040305091f03020405040506011e053103 60
    0x1108034a03c10784001041c1c80030030010354040070510001d94001c00860060020f140d5207210000982c0c10f64040785c0c2d0580140e044080141c0c408202c0c400403100d03c980e1007280c001e00260701956450011890200c030440100310040600301c012104041010035048510b03044a062842626161214818054100400340b5024014120074241d40100d08a11400001070f8000324540e099a685103002e5034000d0881040301d45c18451000d601e130181144608014070a42441e80140e980d526604000d81000060005510382d03400155406002a0304a001d450b508082402c0209003028543d50002d107543c260300201220321803940030040c810902081c0d1280d10f03426501c0c0c022892074040d5900b0350700e140368584015140103a001090200b801640640854140249480c3e111075401c15950500392480382640042034020a040c4500d01e442d01038150302160030320340440b811109001000d00350840405a406114000480c50749a5020b04110880c0007845e140c4824200c03442001110050035a11054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 663274496 1250 663273246 663273263
    0x1c18030f08090c01111623060c031801030204081504050f0a020f0f120f01050103021008071215050a03031101180206030c0c1501030f03020c09130602090a091404 71
    0x3109201d004010321401007810380700825556141000554040b02c43d0f4001200030f00c2600e010889174401a420724010341030500c4091000300016560500d125103034070a05100300d0302446041000c840010503103000303000a01c8400400540c25005800034032503500214000c2c001e003001614150141e141d100d004070310400481d544d00c1c40160b1180d840351806034009601c112082411006854168010743c1c080400070910542d00c4010035045141112444542c1640d9444500410030741c070f000a104c0b0072020f43c0d82409800c0c2c1c0b402110041921030904c2141c40500d0b51511103955601007900341a0103040c0144c5510b05442d160f0078040c2c80004400040c40d09503007491442c8030140b642018160455602405243c00c40c1c907000020801e075001400310001620555109009a20b105005a8000d40c00303280c23240c64500711401c0c0207040c0441c0c001e05900400d03104040c000b00a40c40c00612180b16000000141c0350b4111100250188070300da0b000221b11410003640c820300d44002c602c41c6020f20b1049410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 663275746 1250 663274496 663274517
    0x9061b0d09051212030a02090d12020d020105040309050103020304060b0310060302090105040207030c0b18060106050a031506120e0f06040606180615050315190602010606020703171c1803 82
    0xc10001d40c1c0d259000c08010380103866201c03212684c3c040a103030400300403280503040513500c2020440107002c4420607a059601c12440340d000540502078054080031030700c001e101c81d02c1c00e51400b400502162082034105580080090103200199200052503c3c0040c2a00c0d49220201045070241501c2c0c08241c1c4120680f4000281518182c402c0b50314903541502c0740150000252a040c50111004124411450403400e007800d4031803050103100e0103810542c584a495a03680c80e001012540e014030014850058044103100030354000314446c0304000900301c04220344003404525400c14000780e2081d141c030302c034803000d0000704206c5030054000d41d502e030f000282c44598213045040546d041441006402c0d43c15030402c1208a204400959100c038074025140014030f00e01020030008400981049802d81544505101050742801070300010022480103209080c255100c214440c03007517801903d403990b4005003015203640e1904006100c0c100209080200e00000400070100202c50142140007070001c245 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 663276996 1250 663275746 663275749
    0x2010806030f2b091a0702060c121b0c0a0b0a052502040e030304200d0503073219141e0d0c08030a0507090504020a030603120905031209061b0d0905 65
    0x7504c0301251103550307900081030039520780c0406603400b03440140d81061081110541240e070801101020901c04960180d0315100814400100144404010220f40060124500943e02c201542042d00c03107011125a0320344c0011402d854522600f10540490400019500f40b2215039280d1071a00034002d907014020707881810a0540c5138402142d00a007000d042d80240007000001c0035144400240c09043c11020384080e031103052a581114000722414204d0fa040c454010041d402ca44240e540c00852a040001042c04502d8540076640003c41244200110101c1807111404800c10440b030b404c02600d000300300611004013030108221807100c0c00d100d07401d540905144500000c041003904002540d05507259602084003620700a0450303c1000b024110101e800d03074a52000344041ea1060f11300040140c03551410f12000d1f500c2420200511541e4801000603440c041341d00420a441c821595503100c20080c0040d400340102c0a4503410000d2440c0007021103e000110715020440544600312541e0b610300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 663278246 1250 663276996 663277007
    0x9050109111f0c0c0e090c0415050d03080a1d3304020616080f07050c030c0306060d14030729070504150c08070812011401080402010806030f2b 63
    0x9050202401c2021503030742c075203200b4005614111320804440d0342c40d542c1c1e0b5100701c000043c1500c0440d2243c00404502c9800d18040c850721095520099024005502e4800081e00100e6400b50140500ca0700f0000a109008a984240070110806840c110301444201016030356180c484034a140d03a2020f1000c80c0c04544a00924503161818020749610b10b94540c0e0030303c1229000342d268030310031940415054001035035101c046c0815a04400c1640d454550505041d4541122032101d14081e411a4000518548021580590000081c6e03200f01c0d8110084c80d28200550b24a0b0543d6128000459003400300b0904000005e46070700101442c140e450140310a166600c40242c43e10300c0859001c0004205041c4420030304005241581440c1048015a40759a0b1803030788200001c40320b500f000074850041c6022100e880380584148117440c864401c1c1030001a00a28002d00080e05100311400062006d82d07080000d403e0460550040c0c8031032248003401e9903007240510f40c00c0ca040c84040b10302080003070f1144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 663279496 1250 663278246 663278269
    0x5011802270408091201060902091918090c03080706090c06030e0a060f0b0616020405070207060504090f021908240a140103021b03040501020c04090f021201020d0905010911 76
    0x503968500d20740c5903a40c800300f440c0c3c8401d500e5500103c186070700d130800300002e00c2064006c0c0fa1a10000d6520b003d09401c208007180400d5600240282003c030500504170302d59800c001d0031000c100009242e8445c0d041454500c0001d40c0010a0840b0001c2d8400802c601900240c95161040600741da159485031402c0c1c1c150381020160981d9a03020180400100d0425040380807100b840800c000b6900d88220042881c5502131001a941c0100250343c00d41181001c0c880c103980700d4601e10160503d641441ca009055218a11541e0403d0385c40e22000d0000480c280d04842d4401c2508104500b407580025010309036440071260104440c00d000c046c0310321101110001000414010700315640d080c01c2520804e2030700100b013089810150b00780403011207020384020280c07400030b81c10001c1d5200d9240800080c0342880c100c03607945c016410810b9000005800c0000114101d0703040b21501c400c0702c00c48410500a0241074079081800d0f007814080800c2c440103601020343d0501980c1464041c54922007842000a00e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 663280746 1250 663279496 663279559
    0xb0a090e0c0907030b0a0308091201060f031b05040606110f010203011a1e07030c0b0606070f06050411090c04030b090d0207030f14011407030b01020703030516030c05011802 76
    0xc0c8541c150390324040b54003030b81c494142c0c1000102c081c0210045502c410341c40c0c2044800c0c420000b492242031030802140025102103c00a010450402d28049034503502840000d0801c003036a50001e625500b05400900541009003040001c50340e05d690041201c00c008107008154043c0000f11520503406000b00c80c188c80d41c08400128005000040c0c40e9154001c4001e2a514044041c1c40f60103010b102c0001c10886002c1d68906005010506002d034040c4400380019201d07140811603032001400011446203013a8006000007030030350702c82c201503003090500004180e0040c140c80c2044a03120917000640161b901900b1500600e544045076a40c0d11000e000302d950150b030100100300001001850002c44070782c0b140400c0000c540641c0c440500b17445004d03042080c015000750820458642c1071103260000d000900c000d000061440c0c4000d4998421074660b0300312503151900002c180760041c0030a6404940c404020044a1103172032202c54030110f1803404a11a81c06078628800071110030300003000c0c0640 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 663281996 1250 663280746 663280753
    0x61911032712160614160303140906011503090816140c030307080f0915070605060126010e09071701020c15010e010603180506070c17120a020f090d05010b0a090e 71
    0x4c000e02500d00d40c201c0302102d05c146904014204108040500c5030107900e01c26100441d00d4207892200c2200c4420082103203200b54400c3c4010041540c1e000e1009500e0300160500040000c034605200d4054410082e001800300700e2401d45208201840203400c2c00349035000300740c82c0c02d52119010107403248205d00b405000c905090024505a100e040c0041c21107c00c020402c0048420603090409107803c104010b48800e0355070400c200095802804940c50250303202d1448a0880e030f940c0d0070300002001800f0386032194000340d00080280404011040c003034107020341c00300680203181a415003c2c0d8016000e404042c051520031049111030341124505031042801032540340e17070802001314005c0803414a00c114050090003d0b00100e901402054042c2c03620f640c400c10ac0320064107040811400035200901d18420400013403115121a003607040d0401c1034840c001d65121907400151200d4024481480c2d8407510040c40b0404104055111340c040c0783c0c0039101074220721b0342d03a40d10324219030842040c10401d40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 663283246 1250 663281996 663281999
    0x109020901093c0801060b0f0d0f1d1006090e0703030c1b170609030f0405010c05071a030901270228090b04050606191103271216 57
    0x501c00681d010400c50a10b503c5030361107180c000d0041d0000ba02080040c03a0125100140f001060a02400c4c003e4480e060503545031009040c06241284035104141b100d4550b1142002d8030305009803c5000b070004042d50700100103079810002511110740c03459580700e01340340400004041455018070800290b82c9409011040c0c84d41d202564092200e9200703c0d01000440081d020708014049004058004a03006803a260f50b64421140340120144c40160654014007840280006403000c03102940c20070300e0044c602080900d007003450f10909800c00c0a407140b4204010400d00340070b0026605c20440326000388a0208034400018120080307c6100405040040031030b000f6040103440800030f200041810400200150160440022240c11294100d03031900718520485c0340500400d50055022a041ca01e84011030701d00800c1c030382c0101d09503024449091000081c05c6000e00035100303002c2080408840c0c04098400c054141d005112040d81301d50800000d03400c43d0a000200d14840c114040503428005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 663284496 1250 663283246 663283259
    0xf1815040323120c0f2a150307021c05030705040e1f06120f06050907200105011401080c0a0e0108190603110103050105030a0c14010c0210080f010902090109 69
    0x12070800d08919025408000080c0034002c041240c0500802d1018205445180801006081c4241208104140d5015403005005042c04034041030f4040c61907004100312500440100e48002da0240d0a07105e40c403404420848800d030040f604148030301020010214640d240c1341c05482c6070006440100001d40240414000c1ea405410401e0300110092000c9071112400c0c03403080d401038001d80200f400242d015405144115484c0110f06101001d88000d200342800d000108040c01c000603d52001c000403402202040304400304840c036403401c844000d01c0f030340d80c403205000740b4084681507035800580031100140d00c10850400361402da4145030b50384036050481e0380045880c181c002d40511012350103c004035001c00454403d00000718850700c3c41080000c1700d54005411039030305902c011b000ea0044c034010300008280900510a80e002200d40584400c001401283c1c03405420200039000740400a0ba500e9090300600e1b400e11910f00c01440e01c0d01607894019103016070041d4010107010034884881800300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 663285746 1250 663284496 663284513
    0xb1008040b1e0403020a140705010e060726070201021c0507020d0c08100501050418050604060f1b0c0605070906021b030f0102040b0a021902090601080603070b0f18150403 75
    0xc40a51003100640c802c0442c201d94081e0015030301180907901c200c140104004105425208200c5c1110241c240c46185c00c00207000100d00c10b410a02c1140c0004081040000c0180c0e00c03d020809055030002c052007030000304642e5404407809034054400c5601c080d07850514005440e400c00344580d500c6081856560038022021950541141e40e680c40389400f04015404000148001c0310701003000c01c4551401040c04110b400303031000c0312180d20000803544003194002503a2a0050b900c250001008820a110f640090032005d18800c84c90440303d1801c81215401103640c82400c0c00b07558100810b1300d8100341901c036031889101c0c010140e00846801d0a140e420070f0b0610100082c0078050710445d65810030641e0072680950000c1180706008906942c0d100c1d41003100134a0a0303004c1c42c1c08000b00d100ca40000c0c200c400300a16660401084c00002221604c080c0003039001000004030054981d20f45429446039a0011426a10440088288602c49280450040740060ba40100c8203142a0854a64402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 663286996 1250 663285746 663285751
    0x20409050109020603160e06070f030f0221030402010206060a05091611030426010507080a0209062b0e01020f071403040f0e010f08010203060310020a0e030618010b1008040b 76
    0x1280c0d581c6110b8400940c60310401036108040d41c074009900d8802d00351020703001059520910b0300400c428410540010920300d0f400180903014280301204802e100380891405420382d00c19596a1070359520308160091960165005620076000d8524958a440601c005944a440380c280c1c4018440c001c02c010408000446810181d9840c0ca94039940c9a0101646541d129030700c0301e0102031965191614020304c000c01c04207000d140c94004d0085080944000700084c4003d00b0800401d0790000c1c00402c60303540c040c101c1d8008030542031103000c00302e455514804080d4952a031044080d0918070600440e00061003182c4840b0030f030310044d03410000c0c55201c0f6104514003c08035425440100400300c0c00c110300304040c6000b8800d46004402e990b0504449240081c01c5902c2164560f00502c10701429035404103002150302101c0740016240c0e020b08004440441c526414241c160081c2d2083c02002000304080c1d80240603070400900c540068a41440741440e481c501b103800103610780c0f01190000300c110803200d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 663288246 1250 663286996 663287003
    0x1a070e100e0424050618100c0f030314070504051e0d0212030a02010f0605030c130f0f0e071d010605070609020916082503020714120a1e0c020409 64
    0x1018620041021260701c40c0008000129035091079011503c1d0b4071021002c2c3c981916940d0074030345c40342050080c00d074991441c80d200d0400307880c4050046124140150415070030600c1c50001c03409034100a0024070166082ca9810280c1d40c00103110180514201c130210741010300540070002d46203200690260072a400180d005006540007c05aa9102e19000d4507210307040155a0310203040d800603003155070900007070400310b00b0008100300f00e540106d484001e500c02610200c14000f80c60300b04800402c180c40c0e409103540d18244001c1c2540606a002a1210012030b048a14a40d01c81e000604108003901a144040320288014482c0a1180c405020700c2b612411000c500703800309500013502010300310356480f00034100010340402e103039100c0e5400f80c01207984905e0b003122581120001d003002e041100c458040c16000241c0e0803c000144200080c1540d4290a841e0b04080800841d02e0a03800010b03c240016058022041c0300c003c0b00d03910b1203080100b134403000600c000e9982440007034544030f10180e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 663289496 1250 663288246 663288257
    0x91406070b0a0b030a0803160806090a020d0b030f07052818020c030f0706050f0108032a010905030c0607030204060c020d050c04090b010f060207030503030a150b0c030301031a070e10 80
    0x25a1502c003009031178196842407031815240d00e480000000240180d000f1041080050018840241c4500c451941c200c6a20340026940e150419010804cc103165808a40c161241100c2c8112a400c0420b0400c15a80e0882d81c01d1900d842420104400341c0d520003244d070090a560804021108034202c0340321400a124002505140004000601f540c01c030440382040f101c00011702d00100a2180300741b0342d129881148003c0e2035418000c1c1c0a549000307050b50340c61000016545285425142203207900844400030003802199030a18015031203402c0104500880e01c034040103c0c2c51280a80241c4060745d1090b510034802142d141c08000d000106000152001e001c3d03d1901100e503241c41c02891001400394541c00135079450314038241041c80c45a402042190490602480001c0d000700449800040b0305501003004100d9036009030740d01151798009210000e00080b6044001c8022014504076809058560090f8812140072603805c01c08503040c03800102007030704181203072070305103200043c6200600e1308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 663290746 1250 663289496 663289511
    0x1e050403021905150604200d0914011b020f0d0c020112021201080705060408031b0f2406120a0308090c030d020a110d08190c0b040305030403091406070b0a 68
    0x200a551848105039180c0c1c2082d409281c0748190004a00c3d04140b040c1c40070004106004240210b040e47d87e400401e19100003e0005002001900403020182d000404004d8101e00f1222032070092038900440c14110400c9000410140c0c0045580d0f4903a09101c03016080f500c02041d0101e56003621540103c1c180104825503141016162001c2d000002074408011000d5051103c22440d000030342c0d1286114143c01c01c824000c0c1c5201109035100d0001d00c162130030614400441072802d1010400d0210307030620581c01c500001c180010f41e01503a00003c100daa00c1c268440c3e4041c0845649811044803407940a020b446000901c644c60702a07204800c0c00036100c45046038000a824070504141c07003070040e405030716000180203d080b60441000c000b00c4a891040308280d44016250081450992420b80d000700f045030000c1c081c06500904544c0189a00050b10305854060038a40083c1d0f016000210708410219407100302c0c035041e442c4504000d103068209200c9070349000400800601200200f6101d40b50b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 663291996 1250 663290746 663290773
    0x151e180606140a080607050d091716060b040b1c0201090e01330e010c1403030c03091e060613060f24020d1704050109170d060503011e05040302 63
    0x80e03000074007960b1400315944604201000200c84072034100003016080001448040360f0440e045944000c1441804500d480300e03810031122070568103180e0948144001a620071600181c0d000103c4103104000810031500440b00b88400c0346c022002558004100c001501d0008000b140a61212031052500d907620719242d08200440ca02c0c2a0300840421084201d00700300039542d051020303084240f02116141070000b07084010144c04200760302a040c0b003e034007446000d01550700b41884c3d000001400f182d0b517905040f2908010713548120f40d40c070704501503a0150960078000001e540c4035808803000910383c540f5035104000c802e005081903010060380d100c2c0001001080c200100d4001c1038400f440b0a1104a0722074146070119140000348119000580b2340e52020f9044001107440600744400c0901c256240e1916900400c2c00d02409400350780510b0403a4007440c6594014200f01010b20414402070340d48006140c262207107404000318902c00708204100d071601d07a5002662280c000c2c81106c007000350313060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 663293246 1250 663291996 663292001
    0x7150902041103061005032517070c2009060909011508060601020f06011d070908101509020f160201050415020a02010e060405130b190b07151e1806 65
    0x1114200c000f0042003050302d400036042c4645080b42c101a413071441c0c01d076110482506140c1000101d2502000704070a46445880c680d151365043c51007403666030416200c054120283e85601b100e8408210140803240c2040d44102d840c18034004d030400c40f40d03440342000c11001da4401845100310751350b40e02d400701001c1c209221030001002010050119070419a00090804060407e8034003103a1181c4010007e031a1404248941105400b042203010340b11910100c48032100c9070700c20101c1e4407800c2080070010701942d10030b0680d0b40c0e601c0b03403228000d07a41c1c0800100364040d041c95021000e5040c8000c0c0040030801600c89a041e20524200c2c1c80d0503194030342d84036181c0345424050b0050344940504030071940c004241c40c1600e1011910541403915201c0004c0310040f000b121425400e0f1245501029912605025011200900c0680c14080d807070700820600ca400c401c10a503208810409100c4070305038684501d800380070400c9400c0410060610504c005030100c0d000d205252803452202801217107507031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 663294496 1250 663293246 663293261
    0xa09030203210415050c1207091a12101505090f0603010f0801050601051810030e060a090302160f060503150a18050f070503150105070507150f0509060715090204 71
    0x111081c261424a8141605040c04c8140400442450b000c01e03c0440802c010a4507201100c444400f0354566580300110740c1c040c07080c0d0049000340c50182031101481c10b0140a055500c1c802070160585540f14000b0612902d40c0c0c1c415000d01498515807a060180b20b00b00800481c034020b070203801415101404a69250700036480340c15140384204051040c2582070180c00d810090034070b03140b8104802e0381c107006024200e001c0d40340c4c40b41040c11150501a800b94010002c940c0304d100070ba400500c0c14a101d5000790030055421070060040d0a42c1507040140c804d6001d0940b10034601080c010b03030400c1426100d030343c03001c3c080b0b07484080d00055500301c56482c40d040c0c078007a02d4a06640c1818000c800072000644801415400c1c88407031410030030120b150710109995100e20100d46401c40d029a180060751544a0346030f0103045d078010140c2c086180340705070400031090907061b0f6450002d1100c058044442d0f00415400c40e52080041007140301051034060080c0c0a032103124800555146250700080403070710358 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 663295746 1250 663294496 663294547
    0xf0609191d011b030603081206040f090308160c0c0501030c02070803070501060509010e130803180609010b0307080307200f0607031701060c0f0602070f020306040c2c0a09030203 78
    0x1607555030141c04090b107040b450003c0301c5080901845044d641e4504850051880950308000c00000040650342c030b58110800ba401501000c020741841030400034003010044409201d00345d91908558400f5100d46400e08071150000101c2c0341241c1400011005000310f074041030b04600c10700d030780403078105c000f40000d015a611460001807060b240c1404d0001d0004140d0259550650b46010000201205d0f201c01e20174a0340024620355070303500c0000005e00f62105498820851087e40c0c01c0203103041d0b0541c000011a10300710120340403035070741b845c02c0c40e42c91180d020010603c1d032100250002d16038011400010b1902c0040c00040d080c141500400c3e4143c0001c8020b50020340050010403140c00c05000460261409241c80d1445010940354805c942d026042c00030042c0e076002595000340324034030020944460b0700805444040c201402c10303d048000c680603852841940070f08142291400854000085007813a50311101c0342e4901003a0303002020104400d03804d50100700802e101c0c055446144d60403c401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 663296996 1250 663295746 663295751
    0x2060105030d080601020c0f04060b0a2a150b180a0c09050f010221070f080703020709090b01090e0f1e060c131a04080a0803010603050f0609191d01 65
    0x50300e0101440d058550740c40105101c000d40500c607459a021407907030003052069507002030703500600d800303c2c0042000d42c2c0030b80440c020110704085201d5101040030080b94051b8040500f04044040702129903003404030041c0240e0813030150390b50101d2941c000f29100d80c0b0013000008200c0c00301500c0101c2e440100d40241003140c0d100b4200301070b113410800c8040078003020ba504070f280180c02c07400070350341d8004140c4c6c403c800c0c803079550300d0710f00744805078121869590700201241c1000024030341842070f600844030031400b502a03c07801003503002c1e19109600b0550303001400000703142d280c614403c0040400d04210412401286554040c42d0810410743d0740c50503907048184422111300c1d00c00ca060140141c41818501c608010218510780318507820406d0300c00c6000c0f00804400312400c046194460756011943c98001c1c5003103902130115080146048401c0350714184074a549045200000d000c0c2121038070383c40f801c00408210440014003480b18400046440000c410104403a010b00d0080500c0341c01720b8076034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 663298246 1250 663296996 663296999
    0x60209041404021c05062406070c05120303070c060f02070f0b160e0303041a1c06060e0118030320060901090c1a09060901031d0a0308060a06021b120706020601 70
    0x10b0680c2a25002e0803484840c002d10f000c99500e2135200d01b4003038440c00d19140e010b8401459207aa081003056900c80040c04117560708420710f0003042c3c1c072909208152103002000300c40e42180d00040220f900c510525981c0c40304540321030791002c2c010325510f150b20403500d60900500c4c00003085002c0c490801d5000307a81c00212444d06220182151012481e00401c10840100701d40094a000040e2829038000c0300360040c130201d01c050721445500480340508041071a040041c039510480d64480402c1e140c490755103031102425000191030360654030f030041718448884981040401e1066002c00425950521405604e0b00f60000b5686001010381c5c0e40e1803183d5443c580002000451000b03c001008100e0810140b0580040b209a4502a0006660040394001140300a581c481c1d8003848030000505a002c52095141d00d5803550703034001e004118045181000070800c0ea01c1d11445110480e14554018a11104841d0400c40c8228202c40c44070f80086100c0c1808410784000e10125010340300710b600801a82d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 663299496 1250 663298246 663298249
    0x516021e10031802040e0a12052208030d0e07092417060112080f07080d0b06040f1a040b280302040f030b0601090b0a110f012706020904140402 63
    0x7210361030184040c54904030012007422602c0e510610b04580442d00080c5040c3c51590707072803c000800200500d03160b88501a0902c0382d41010107804001040d240a111920542000c0c000005a600a0340c2040e0b009000c030002c120b03000d03009010201d841c1c01c1034400095a034400501070714080c2e03c100c40520f1180454428007400d480c9220004c01e99401c0401481641c0d221850301d501043c000c200c02c0c51494280801030082d03800455070010b01d1529400d0742d500301410035141c41d400040c07112200504107810007000d4584402501d040d03d02007160340030b40302c3c5002da02e01da889610b00c00c000c0031542c090000103040c10062024101c1000b8010207401c01001e1176205142074007140d01c12100b4548140020301c04c0c20011810482038961001034200152601c0c0c0051740c0f0020a42c1c04000b0381207001400c0155a94001d151404800c003820468a06044440031107003a0303190302c0710104680b4644440e24041403600b810802c60240100030040c0740200f1f00d008101034641d11090311502050690502003103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 663300746 1250 663299496 663299509
    0x9020d060e090601050a030b130803040b0f06010f0203030a1a03010c0302090a2103031a030d02010e0c011e0c150c05030f0f132307030506090105250516021e 69
    0xe24a4020300f03010360400d07000920300c502d90701000e45420010310000764212400360710900c000b0303004100300e07480b1301c1d00340350600c407405007110b425429081070030200b40294001d00c50302800e04029005076046688104110000f40607122104005407590f140c04203841d1420b100f21000c40c04503580141e540e070661070910034015450381c403d000d400443c0c0305045918a120b100340d044654145004620f1282c0b62000340c02d40f00a448050b03500d40a1074800d10708a0350158400c4241849000c06e80e20501225401034603245a44101d0b081c40c40b50300b1440c0320060b80b0403d5000652449040200040720011801d07200700c0d0741d0402c030140810000014000701e070031000301ca240d00a510890070b0b90140307000c2c0d1242d00e80c04800c400c014070343c0300a010224a070000c1210145841544541203a101d9656420710f29a6480b040e6a202c007554680b402150902e03000d00440019403c5000281c210005400400c84042c0d028030426014800d04440200060b50740101c40ca42d00100b40c054113500d286034030100800f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 663301996 1250 663300746 663300751
    0x6050603030304050c060d0603021905010f020a0201020309090702030408060915010f060518042306041407091203140a1206170d20030c0307030306060c080904021309020d060e 77
    0x403940c418020840021400141d190521000f9a5040d440d03002c107106910241041d504025402500070b400341c40684400d041c06022250b00b66118100c009103043c00307a0701c8400703150307000c1d0040c1c00400c01d0003110300b085106240c000345036104991800e6034542d1800d04080d03043e43c103140590060043c4507061406c559a10b40584140100b0000c3c03a407810308003602038400c0143c00c2c42d090303505c4183c40303003d5a1680d010200702c1e860485036288441da4901c120207031603000c46d0400c2c442c0c1c6c9441d6075214400303003145010344181026107401c00100e043c061000520faa000800300c0c100811441c481070043c0240000c1c0181d03100b00c2e01e548024460700e141b04825640160044034030100191443c6600000c00244810503803020709010603032240481c0c402da117000118045e030082e44000100c804890b48000010144607000790b90401c581a11100112540c1c0c00c80722000e411440c0c280030440385441c280d40103040320215841c015a00680c0c03090811b0690b0006025880440d0703441e403007048172060f4014001d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 663303246 1250 663301996 663301999
    0x30d0903170a0909180203100207030201050c0304080a08090309041b110d0f051b0d0e09011413020903010905060f16110a030c0218041523040212010b1c060506 70
    0x50414080b050014092843c41c41644030442e12660101d03410705007a51114081a00942601d00b60304001410801950001c0c3e4101e005600c0c01c2d00042591031141e09407401107034000b5007507241030034925013202e02120251906a207030008010901150b9264803449000004c4c1285082d424159060081c0900c141d000310300715180c00561540038540d500681308100640641007139174880480301ca045011940d16404410b49100f04c805540219400111014900c1022034404905a80b134112805011503504880f50700800c0d41d440d5603440003041e0300039043d0010090b0000030001d0300b68803520314050080e5007050400003060103100b0381d108070801e50221711a0b103040c9020480165062240da68420f054040c040011038042c900441d80ca0407a416039940c00054851100d0405040c901100044001c0800312a4a80244070328188100f203500150802d03a850034188130342e215020701c200020103144069841d540e580d1500d0107651410441c20301e440c1201c2c2c41d40103800c094500300007280c1c03018055a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 663304496 1250 663303246 663303293
    0x210902010801091506080c0702030102040924060503042d060902030c01021501030f0204060305060a02090a2c0402060408030c0c030c010e0a092433121a030d0903 71
    0x7800112814440104179681743c50106030607030b60080110814051050003e42c15400000c0000c0c0c0303200641c0013180315510601c08103864461400c58020b000c4410b12800010030402c1c000140410900029000d0507400301c440c220300c080c01c800f40100300840380c20342145c40d5030b070f00c81c509800e5007410400d440d0030910a000030710820f22552a11a82942d05200040203038a070100305c6d070210b450f1604440025a4064104d4605091159180000c2d400c2010318600501000d9800185500a0150b80d0803110296500717400341032076041940d101d070070002c1003030360014030420001a0900e400c200408042100b00054100f0044100425080281503205981008052101c13039290340c0d160600c1d0b4080755503440b000110207c00b154044407550100c005a40c1e044000500020035030907802c0e02c0151292699004503e5003644e8811441c010010310000001076900d40c04000c0c0e4500c1c86d0f000782c6404a03107110700ca21205940b00000d10341342c403040070b460001f0501201001045020b122801580b035040c03412 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 663305746 1250 663304496 663304511
    0xe04021914030c0708071502210906071b020f0603070c021e0f09070201090f0c03052b0c02031011220305120d0912091d100e060121090201080109 64
    0xf80074440c0201c41e07020b03010038800a01c203010030030140c420085030000c22009648406d1084a00c00450810501c0600c6019110001801600700412080d204000a8a80540c01480301c00341c0701d1010a0104101d0308401c4640c01c80300c5903907500d0055481003e0556440342408001e01c1031105c500c400c00c294000e2a00c030b4020810480c0d981c0030085800315803d9400c4034a5035201c200403400340035a10000b4150b4042103c2c601d080c005481948410360340038508451184141c0d84401c4420183c4100800f07a20403d07891000ca1603204a1500a6540c0024200e4104010702d804100444494913800244c000b800107a4a598420505001112040101e20b05070681d1660311595152040360310035140c0c030900040c03407509200d402d600240805030440454412111064000b800402d011302688015100c042c800180356003641c005c807803180c000d80c1d0385120824a00b030617100702c9440203060207045c4020850b0100101e5588040c406808240d03034030104002165000150004c2010780120000d00e00380800c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 663306996 1250 663305746 663305761
    0x3081e0702100c0203160f05010e1507120c0f0308070e09130803071110020c010c140307030203040606031a040c08070602031209120a09060f0c030818100e070302030115060207090c0e0402191403 85
    0x40d1548550450751401c43d00050dd0300031240c04040040003001c40045250320310906030f118500c20312030307174180c5c607542196000e402c10081842c03801c46d0010000d000c20f00314500080c1111029580009c1d1074103100c0c5103003010018041c144191440b0b0464400e40c007007000c00c0c003030109004028040d40c1c2404c0c404440c95582c42200194400100ba07101450780000201e001c02403950b00c580001c2d60030501c4000707030807051030a0f29081e035000d890aa540f1030b90004d02144007100414100112205900210702e07209500c810a00d81660092121006001e10086580c8501140d4018440c1c0496a55801c0c4440c1c20b116001c1d100d1017401d2818801c210340640c040c000640c012080030b4000078030280c4c04200f1021488064689100480b5000843d814040e03642c556007400180e92090b41d20840c001d101800e43c10410075014142845801c005900a02c010801010740342e02440f0071000500d031480300c05071010041002e07a8032940701490800701048010a5080d80244500580b541980607d40f0b075040900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 663308246 1250 663306996 663307039
    0x60f09071712030a02030f010509060d031d0904120201050c161e0804090605090a090242190201060b0d0e010209090103081e0702100c0203160f05010e 66
    0x3600144110540800741007002009680044507600b102d0640d2481c105900c00080e42050b00c0d10144909101c1c0081070601e03050510520607100078152007048401d5480c1203c804540d0700d8618021100c0d10608600303501ca40c01c00e644124060528000e241c00c0790030f030080c04c544005000032306101e0140b1941c400c0460a62181820f07641140b4071a00b103985002041000a004281c004d04040002500140124a50f0003850031182d0842325459103075541d403802e034140c41c201d140080d8440200c4941489141c000c2d03548201e14034010b184050100d180c1006103d444000041035840070b080425203200c91108400c94001091541c170080c01401c2c60b240c0c1d07030f10080c0540308201002d5611100b86003080d040940c10307100118402002c01c2c0955941c2d04002d800c661182c0d541a030100c441e080800903401a49045a0030075a0180255020740c0c2c0d5031804035000404900c0890341401008000c010002081281c03c2c054201c241281150394074001c009051844405019401005003c4080c1107401150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 663309352 1106 663308246 663308249
    0x61403281d0312010b0c0a080708070c09090314030c160c0614070816030306050402120601031d06041101050c070b0316031b0c02150417060f0907 64
    0x40c40303641c4038443c2c00c1070701070000003040040003403240324030080c120350801e4819244131705666039400745940d000c11025150340502003003d20500901007144002400080805c10699089940140485031000304c04120150044001403d496800084800d080c4002d1201c1c03661804514100803040c1c0c0074000d210000703c84100110300004c000e4100c805070b603040b15001d42009505100c01009008002c02101015268800046d5540b501c0c005410140c1001020307205cae40c50044001000c035030041ca001c600c41c22003600501505403010078441e8220341c02a481641d59114040166140e03c1850030b160010b1103055070006030440e4507405140a2020302190306003460f00183d0413030a94030000820022840218820a070310f41c0a4032680842c0c03840505000c21903082042450060723080380d4004600422100c01070000c5c480244040b030f80c003024002680301d007400d000603500d07541c00c1c07207 = true := by decide +kernel

theorem cover : BRFrame.Cov 663129496 663309352 := by
  have h0 := BRFrame.cov_init 663129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 663129496 ≤ n) (h2 : n < 663309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
