-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2276
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:13:14.452509+00:00
-- url     : https://prove2.me/submissions/c4ef3ed6-e7d4-4fe6-b373-a093f352c649

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 409172661 ≤ n < 409352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 409173911 1250 409172661 409172663
    0x2040b0a090302100e01080411030f15061203030f0118060e1f051002070b03041a07021501050303130b0c1011210708010b0a0903050111030603160e130201110604 71
    0x241c01c11030a00c150f103070920005580c42058203018141c0909407001a00c1104010b001500c101c2813240c401480303807070920032012510202c00544440c000309404000030800c09039841070003542c14007444501610000b044074028008803a9000c45680b81c55240031280f80050350b008401d646511001445d075140c9407440d4094060320b50003104a14a0760b5032000001926030101e4400c2034501c80c84a401600070a820782507403103094216030f880d5200d050016070030160703010f1001d07207c0d043e8040050700e582c0410048000c1a009403911780d540d0340c41040517540c0c00f820405002d4a040d40c00b00708000f410010003011074182510a56128150088840e0100c0710103a16020103a1800124405051380c1c0030694801c03048030601120f00f44c28455402040910305018401460324006003406031280507001060096901800910a41010034080101508140e550900130300c500c0131220058000c80001d40282c4a02e40c8450b90035541d0758050620803000c901e0240d052201c1c1e40c60220300300c8400c0c092540300d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 409175161 1250 409173911 409173917
    0x306100c0b0109020702090a0501060914010318030c051b010e2106070e040b01030e0d03150b04030c03030809060402010e22050c031008060709060c0201090e0406060801241802040b0a 80
    0xf45c680d401400f12500e40100b0b4404198502001400700035003150500050703441c0700034482030300d41340c010050b4002d101c810000c0758844003102c1000c0400d9800101c05429074410015075000d42c0d107000c000012b400104402d2808180c0380c44107200141403007184450500e25943c591589000c40e5000d1a04010060321203e001804080c0d104105003401d00458850040c207182c100714a041e20811941c94000380700c061410075441e0f51600310b44040002c1c07040054460500f51a44e03070380c0d50380340502540d49140b01c00c801003101c1d9800140705030b0300480c0f820711540d01a112540c04d00800c40070011341400000605400e2580c9404400d480515031058600c41e1441c0c60700541d81303090801c042803131144036900021b5070782c0c0201c081100c3c081d40810702d402249e100c0c2c1080004403a00b440140d41c030f03c2c240e03002029682107035400c200c180000c3d40c002c0000c4911020081140d105500c1c20b40c0c2c150100b41c001c0100e0701e01084800c2040855040c0e01404030130310002c0050403e600c80640007010f6001e01140000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 409176411 1250 409175161 409175167
    0x1728090c0503150604230a020306010813030203030a09060f060f0f05040b0a0905060114030f100609060c1403040503070f14060301030b160e040606030c021504080306100c0b010902 79
    0xc2000351280c003000703090110300916800c41207514040c40c00800a00fa42d00a94964104000600c4210f00402d00c4100280007541d4501c0e01e280188025001119014000354007a004224400707403000761034103000e81690140d0b2455654280c4440a40101c1404646055464683d202c49158030721038000901140107250b0503591800d205203001c140030f5003260b40309a00e004860020b45e034030056108121005003030082125510400140c81464000310303105440a000410070803c200b41e01c80a501c02c0000c0010640030315100d5804580802031401013002040d92a51140042014041c2003416500100e00f01c81c505501c44020908080c0181d00c13245a1059143c402d0180c01d4445c0f03a030b080005c0c016116541150315588604a11000140030b500104101400c15100544210201c001100000d0000c1c041c441e83d9007001001401000c0c1d40ea40140160106003043d5090501d5103401203070441041815900e070281000980c9400350800e500f8030140300740900004488200c028001c000c541d6005807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 409177661 1250 409176411 409176413
    0x1a101e050411030105030c0d060608010f020d0c02010b090705070f05160602070e04030207090b03190c05030f011b0f11060108060708090d0f03050a18060c021903172809 74
    0x944000c0b0503107500000e028001072109480c006503001c8107d0b01241c440005500900b0024010034680e00191031a500702000103044d20b003550000d03c0503003c0154104886004030303801300c0c201ea5040e26070551003007818010a40c21441407002e028014040c940d968010f511540e907030707460b00d94203082c2010740241070041004015010702040b4005e1007041442d410914180d900292134001c50701450509650b185108046c40e1400c002c00d140c41c07480841207441411a5050141100a1522425100744100c6401103020041801001c2500d551201c80c1c1e002e040d0f5032802036840c41c142c034141c1da04002000b40310710103040c4104401070013001880003038051824030100007051040d004188081a90008000800e031350352040e0940280b03409480d0009180e01c80c0c5203108042c2914a0007001e621020b50000824000c10358003480c4160010b0f003c40c1e0002e444003007814500140300c1f402401040d4620030707440c030202c0400400d607844080c03a985500940d44140d1400e0802d80c6008401d048a50b451210310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 409178911 1250 409177661 409177669
    0x60311190305150a0f02160b0a021e0d02160804030606060c21050c0106142110050702010f1406012c0d0204020c03040e041506031a101e05 61
    0x110302000154144114508645540e40d5544505444040020b019000202a004194007001e104050175406541c0d0303c07070304107100030804140c1800369490200312004c110440d04620840350701c11000b0081060300c42804070400360701d03000f00741c412a00b19020861500100c00481d40c03260882d100d8095651100e0031410031200300d4403c0c2e04a10240040041c0000100b506c00d5402c9244103004500c8400f51955903208581d140541280041950701f080b0000c1802d0303030000f40d40c9201040c25100740c1c44090b0354a4000c0b03400c620700c0d1060b040380e400031080914010040d41080c1d601882600021844007102c100d400101e6910800d15801c0c0d10303048091000960b0300582c8105120004250b00c00ca020300101901c001c81c00d0882d205102d000c05410004c01c42d1280c0c0c060b20859150346003603039159503440103640c4032040d040f101165a011480500031149050f4418034090341c0c2c1215010078000c03a611b41030429240701134402001c00c66400000550b103003081074014558030b0304511078003419141070188 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 409180161 1250 409178911 409178929
    0xd0b031e0c06031311030703021531120807020919050601020c0a1e0f0303030e06012909010c051204170616051e0c071a030405060402060913060311 65
    0x25502c1804200184200303580541131126960750043c611a5408001e000064030b4103a80e9072000350004520017801d6840e40340e0380c01500136903100c4082004000f4405082c2c4000e501c1d0140d540c4a2506500828030020f9460001e2405680c032841142d4501562600014041542101c990310b5030000c00c49030100c88543c81c0101a0440c10030f0008040740c2010000080808282d40500880e5100c0400c0c10120142c1720314400d8014940d0b0306541c4402c0d0b40302e04008024140c80c00c10040c00340708010000503007520b145000c00000150340c095810010342e2044110a643c4081a40c904105a003182c49010850a1100440d00c2c002c3c40a03031540d4502c1c040c0c40e120601c4079180c04041d90b400800c2002010606486c0025000d051850700b180e40303101e10002014401040703010001e00001c0030030320b1307114540000f4090040d1220558445032034032901405804c14841150000c14035085100420011304000c40074103500c040c002c0a40d000300c02c11007450422204164003c0c1d9000c0c5034414900c119042c21000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 409181411 1250 409180161 409180183
    0x606091d0414070506070503070b010509130602280e21060f04020619021f091104050402120a11040e0d05040b070203032a070e1005060d0b031e 63
    0x6854010040c0a04400320a00000d10103441c0680049007028120410303c4480d001d4880180349a44603419402e0407070740d90b00090b004968901d40751001103128905204890f04c128011440c001c241c1d0a41e588c0c62001e5044040c5180220803c4c2950f03905a41c0c17982c102280c0750302190b0b600488001000e0030013400401d0175149841d114100c007940a0404400708409501452103a00000c942d1124400328195114910302c0010303052401005104403030340440d0002c416401c003d444541000c41d8030696040324010310b00140103891907420f075502400c01c0d412107980b0034002080b894220541400090421b01c4440c4101c8985c800c0030400c03140303403900b0b11813110014600001000c1d400d41506c2d01806502c506d0003130304614540030900e407086543c10000c07140c2807048900802960344074205c02064600085040480901030440007180b21101500d00e40d1182e40d5034451003000c0c0b072400040c06610b6011050803a03005481e440303403007182e8038100045484600c424030106c80c450348034200c00341010b0031082 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 409182661 1250 409181411 409181429
    0xa1d060907020307030e13140106020106140607020910030b0c09030f15041e120905041a0312070602040801050c03070f020102030106121109041a0109050103140711150109060609 78
    0x814800541ea0000960f0091a81030504414000d03203200001c40c1e40c5405034040140c1f50401c014074100c02d1800460354101c42d2180c009000c00394484a000d10417800d04010700d50441814001c80c005480c0140c0c01c15009860842e10704441c3e620ba856820901c10708032506030b091500040e100d802070074100240007010720080c020b00480f03602580b48460644020b003001e08200423881c403480300382c0480000914855403140e0021000405000080c103800e40c140314407132003039280111307140c4005c2030144402003803440180540801c44141240c40040e4008034815035a541e400d000c0403030b521100748189405240d815410a44914141038024105514a0706607011640140010890241c001c10700d8100c16160540c0801d55040da181303400c000f40611549aa80641008290a816031001d00d0303d0001841c280e032403000c0f03903072110019000e440c40b445062840b895020300084100d4468006409003c42940a40d0400700187d41c0c803800c0c00000b130308501e40c1c913641c41600f00720523500110340400610ba521 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 409183911 1250 409182661 409182679
    0x4080f0610030b07050d0e01050103061a090106030c03111821060c07031e08040201030b0f15070c2601060906060206060f040618140f06030d031a0a1d06 67
    0x6920000e42821840b00815455001c0045201c0354000d206548041103000c038100407110f0004010f601a117001c0c071059924901c0d060381001004000501c001441202403d0464180d00e0464114014400c0941250405176100f07120201040d03928020100620200b18030380c0300c68989400c00010717a1240c010101450b4032184600c0300c1c01008a0202d5119841d90322003a190140341c181a12552010b0b101038500b80d00d80c038800d031105900079884900860007a82c0411070b1481001c24004803400d244840341d8041b0703516004903400358100e00203007102445480260012980d40400000b08d600d4001d030030045d0288050f000240703030401d100b000014020450140075903880c0c000003a440d03c00c050461405000303030086c404295121600903000404401c0e02e60710f45440b044a0030401060480701220320181100c0100e8030a01c25007080e64061341008024003243c00900718182c0c01403401000d00d11010000c5060000107a0b83e18895400030840514048004d1078207216032140d20b8401400e0501c00e01c829 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 409185161 1250 409183911 409183921
    0x220804170a0c05040903021c0509060423010315140d02090702030a02060f0103020904021306030b09010c090f0602030a0c0519030c05010b04110a0f0203130605040303110c0d020d140609010204080f06 87
    0x1c8040401c1410b84014040c1004d02c40304130380510410f15000d811200c006800298141c4480c01c0030910b5400116406402c03401d08011025548030434030803450500f00e424144000034511030401c12210000b0212051010369034085100c030000bc50b10000542c00c0856445d0050760144511940583d04001c04495503055a0001da056400544040d000e5440c4529001c1d00403030503403200e00a9500714000d1529850400c0c00d803030107071030b0281000c4001100343d00001a003903c8400400d059548940185040c824504021540d001e8a00350030b96092094001c441d640c001282e500381c003d140280da60312181c440340e09006017910749030a590b60044d8a001842900080c941341940c084411501c3c1604c07111003808022881c5000e400b511051407404500d000644c40c1c1c00c14010401c80b442034481c4c10f10610442080750b21a8142100550000703000a100c40040c50410410003401b849284001c00100300d009120745001000c031000707032581e9400202409a42c000f00000c80354061080010700c1f540c944 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 409186411 1250 409185161 409185163
    0xc030b01060915080a02070f06050105131109010809150406060501080115020d080603070f14240708090619120609020715020a0309080f0310090203220804170a0c0504090302 76
    0x10043e0715600300710006021030040e12058048412654210842070442030f10360501e04028a028403e0078480e070703d400b030b18006091040c09500000f1a0314081141000103d1006584c00d07180140780030000d0040581c449a41e02d01850200e0151740203180004034542440c002420203041a08034041603d08003c0040c03031546d001440912032000c500e07220001ea103540010905d40030107500039441111800c5d40103c4d204187da0066504680c3c203c070704030b400c0c2007803045034441002d150010300c80d40e100401041022070401401010905d0002e42464a04112500c0c40040170922005001c0021821954582c4802882c021507001d00342001c01145000348540e50b01d1900558a29100c0c011038001c98035520302030080d4403421398180c0101c0d200741d483c00e00200c160403d074000c0756040140003c021000c1600a85c603c2580e00c103203040000c40d10340351003050110304445c00140044038500d000704004105030030ac24468284081501c8010100d00640d864450408482c9800950190341344c80108401309034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 409187661 1250 409186411 409186439
    0x804090c12020c030913060b0a020109050c0a08210d06060507030207050901180b1519020105130b070c11041a030c0607020a0302060c07050d201030090c030b010609 72
    0xc00c96142c1e040c40c0200034010060406640030300d6110601255025402b90113400141610344200c0650790030114000810502041d58005c800d0380f503000380360b08078400d088108400300c0d1004041a042c20880c032b0000c0f440c00d5903480d811071304c00600082904400c164040000e44081c040403a2244031643c1008402c1030090b41500702c01c042750b80c42d05c582e0122901c8031103a984401500c1044160340da03840840310780707801c0f03c00000c0c14015861301000801e2028201d480c0c1861650060b250241c9883d0700500b200da10072103a5094840c0040701c5120007156882c5c4c82030140c410141c020315503c444101d0b08050030486408100360040074104003100069541c03951940c140d81c0d0407221103440c1d000043d040b03450701d11a50401e58120b11000c0850303043c807a0000750180007268610310102061850310a1180c44c031600c601c407801288180501d8401400103041d0315a250b0100c006d130701c1110412445e01d0007511300b814800c0d40c81c10700072141402444080e04609001d017020b800c1000c2a203191a0041c0c0c4052 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 409188911 1250 409187661 409187677
    0x1e0503070c03051b0c010809010902060409020a11011517010b09011a0d09081201090b0d140a0c150801080f03041838010c030203030a180804090c12020c03 68
    0x40380ca0079007002018000c2080d2004802818807501d03801a91401043c0d4401e51110240c1c0400e2222000070310b90007050081036109035028115a09141c03501b81101c005c1e400015014043c01030310303214191445000d1140d04449194007001c51001803410141c1c01d462280300b0002d55459042000391001c1e5140d02c207400e0b04603900051030b880d8048012130a070140340600810740c9022401c160b1101309000411300a004942c1804200e24200c0e603a42202204881c06845000e42002ca00210075000c1034440c030640240b00d00c0642529243c803010741d107481540b0303001c2d001185807207035100c1804e52041c1c0c804200c5000d44460b070300030a05403d00840c0196280954440e441d0b5080030800320000280240e081500c4500940c0600a00781c83c0d50a402068110b10b03440c1a41c5403001c0c02810050b0390310603282c211030329406401070340c555102ca41307405001c0c200d04500c17041a80c901c010002c1c00685913400070402060542000a0b0b03100c0c07401001000d140002c161040424014001e10825440100481d2480 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 409190161 1250 409188911 409188917
    0x9050a022d060c0708120c0d080f0703050a0213080f06010603091a100f0303050a020105070f090e040611070308040b01050102030f220803130305010b060c06010501110c03060114011e050307 83
    0x43d1020301c4101d181288541095046016000d4400e4894101ca80540b42155031101540c100f6800708008880320071007110001c264400400101e2403d6000c0c0d4409a000201c00801500d00801c01e24200e201c0b0f0034689c4841070580c070401541541d01024031119000d050076160030312801c2d400b5124490518441501c5980d40040a00071440b1101610600c0d070092116011140b0001e55a0401a0441e040b4050036400365080100141c241c0b44a52100c05001c1a81d40f105402c03e801d0031228000340400070402c40300300799100d0358010b00300f000714042c0c41d80d00e01c2950b4ae01c11a150a00d0010200391041c1d020505562080c03011540004000081c3d4200710401c04402c904500701400205c900041684040c086000c0011200003a9252000601c16a40100000d10468552105006452040d4000d0002c02d0700101c0040c4000d61040c103586500c0d04250044404c4007041400007400d000003070b88056410702c9001c04422003540c0000d10581c1001e103254120925401404c07002c3c2c858440100f0000030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 409191411 1250 409190161 409190167
    0x7060b120d2304230a0b0a02151909031701030b04020a0f060c030807030b1221090a03060209010c0821070507030f14071b090b030a03050915070609050a022d06 70
    0x213070f203e03040c08040d20600078255554280c1d07510b92107605502c414184401801031540c14a403c040c103032001c90142c401625014080008a4403030002440488012002c120308000500e00d21a10300e00e0b00c9000c0c601540b00201c4a00f4175104101d501205584022151007602008008054000c25580449a00350800050555895101710000c180b4046481c1d402114007203155020480001c2c1c40c050030540c6002e00b246501b04900c1010b1600804920715130003000c58900b40002a0f81e03030041d21401006042c4031400f03004603a58150550442c0008414080b52404422a14124209420b40011860410501d080415200105024509003041090000d020162081420050120f482c12904411515810f60a50b41800304199983c42405034940c00d00c030042d81d4524000c104101100d0349502d070f031441e04404000b400440398803040c944007510018070282001c01d000f4000e8402d104d1040c0c0103040e401010b031040013079a1806100101004281d40d45504a01300240300082d68002c003207804c1d03a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 409192661 1250 409191411 409191449
    0x90706020607020c1c061b030c11031c02120a0b090f073c090311030f0d0e060417030a090b0415031d07081c0305100b07060b120d2304 59
    0x44904405100400413803806203440307400303100c0700403c4507175401e01d035402d00040d581d030380040350842b030349500085564108210a8018481520340d501c1003c24032400507051100c02688200d03041800c580340e0440305d480b0703421080640791600056038010800d080c030325101d09101c080103203213040008a4110880c0080481070603001200350b02c1c20b102d0014107041d035103651000002000e482007032004481500c01807100135038070324000c03c002060014800c01041e0415002d00100c5040602d041c0840d040700c070800c40800c5128195122603903141c0240c00540d40c07a41040fa0080008056a00c20001c0480a200610040100c55014040c420380b520f0b000c10100f59107081401c040103078504142c1c4a1244900028403d903001c1901c000c1641101c3c241a294000d11106406031074088441004c5030b03190100611580d507107a8040c0c0074990041c0b000049860b185800714400e0511010340307042c41c2d4005580c800c0400d60200d1540302d9106280300307244000d00e0380701c0e01d10100d00450184c2d40312441c140b00114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 409193911 1250 409192661 409192699
    0x12270602130308030117100e0c091f2301020615040207030e13090b070c030512070203211008070b04050f13020711090705091f0c05070e090706020607020c 68
    0xc003942c1c010440f1075803941c0d0352804101910460940664078021001c04a041a019103e580c400d1240c010251000e00280020402040c9005006403590805a08440801c2c0090384444014000240794028034054200c007004003031981c8102e2a045500100c100000d513400740a1445d2804000c1d200940c55008914084c1e034085140c0e001680c00c0020510b0304010b642c20f5800040461f4083c07000d00705540c80e800c000711100b100c154070141c00706004010358810310030120107031a031017041c3e84103581c03d0840c440c254114281c02d54a05034800390410080c0a100c4032448031880080012800074070bc05d0345031811002880c090351203518440d100c48946100151261207805d03903000000b8004640c0c0c0c1d07095240c02d800d40c4500f2403045010340b0003000003401039405081213621401e8000d2144049160b04481821540b40c51121002004003004506002070010803801c80a0544d8030351440b111b00c0e01101241c80c000d415031001b411940081c0500000c0e41d00412640308600c005e40f801e44854001c81912 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 409195161 1250 409193911 409193947
    0x1c2c030f16030905011b0b040f0204020a03140108072301051902010509010c081e18010f0501080c1f1202090a180609020a02031803100c12270602 64
    0x326002080000d440c50907855000c1050101d94030a858250200343c031034004450b80360f9071074040c1221910302c1c080580070981084c401c0d9405841080490f03120078003540420103076041712629401281c2c403040150700308181e1011540c00740c1700d000c0c0203040326850400010020074940b9030180071015155801910f9034407841c1251807448035015a86030301c8111150090080034100d80900c280d501e40411138140511841c40f25005600c03050761216203007000c45200c904d5000103080324802d441e0300ca00c2c224001c0804e001c2c0b5000c12400d5200010f40d0741c500301007107090404004101d40705206200e0200c2034551041c00748034807a802860b28030506d0710200300c414000d208000c0310940c081c925010018080608890210f20410200014003115585a4000040c2d020f240515409600700340408460003120074002c0c403100c0001000c80b00340c010705007111000c0b136610076130700d02c00110301640340c5684410500603094114040002000d035200300c15174605480404110007000145c0004485254544100da8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 409196411 1250 409195161 409195177
    0x1704020f0a060507141c030e100e0a050709020a020303180f060a0c11010e06060409081309050f090604050c0d0302012306031506030309060708040f0b1c2c03 69
    0x10007228a4581e034010306140c0120310202c3e0008814840c1e410800c1c000302d904505401c040240310f01030f217208403041d00500741d400082c821510811a00340803030b00403070042d001518005400703000c1c0580f2608109042681076004800e01c913004011455241d0f500104a9620501050070340c00801208030701c060500d01c003000700e001c1c24400d1805000c0074050603400b030140e01c181070f1036890340c0c502c0b03c04045083c0d40466101c88400e4008200049031814642c0148030741c640701c0c0490380e1030a05401c104805a005c1030f0800c0401c2650f9001304204060002e4410b50040301c410001e00446c07610343e41d200d1303541258a41c0680074601c0400700341c04043c000d4000c5c0032420f0254801a0070104100b60003800300034200e414611074410910b1001c0700200c0344010b20f0048170060084c0d03150062802c180035099000b60011030f13105a0070040001e083d1a10f07861740002d4050242103554070080c81c444900c0c3d003582c0d04042184607140503402d615a011001c46903803400f042c4003888180080038800d003820350042400e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 409197661 1250 409196411 409196419
    0x60306060c0a1104050708040f1403040506160201020706180306020a123306050910180807090b040b0d060f020405040e03040905070e03030304110a03021518030309011704020f 77
    0x40102c20000d82105003107040074282c4080096690b1307210221505402075078040d001c2c0ca1002d2140300400c500c6803101005104c00400c40c2d14280d680c10128140d40e000d00c803020307103920701d11000302c1c04c640c0d06001d030800408680c0360006d00c6450f41840c004085401e44401000690300248a0110b00d0207106248130301d1442e51010031043e1420050701c049900c004ca45401007151204103003411201c0d0001d01019a203051341ca07036090280020070700c00c1206403e50a10188000708440314141c18025035134001500803034018045c51451f10381d480050303416900c0d04c075200c1c1d810009046815102c40e4420140c40c0c0d000031012440c010958030070002841142c1296170400c2c2014801621070200100400071100c8e030304410001c580c0d41e004210340a40c440101e06a1541040004c1b80125003007058040304078030002c00070b5000c0ea0740c90340011030440051f90008828180465115003801c4002003443c200380d02500a5458000e04200003048a0b5201b10054040701d00c12001c1015912282c485903001c00c00030f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 409198911 1250 409197661 409197673
    0x40b030912070807061b120b0d05060907140f010c021908061e0f061f030f050a0b0117090c01201920010512090f0d0e0307060c0b0105060306060c 64
    0x410500c01079441300b03c0685505007441052440c0d03031102810181176103103940d500740c502846841c9500243c4000b0210035403007800000a000411000d110380380c05a01d005c0d0003030805900e0b24204c2d0b80502d0440e1b074004e2089410380031280c0e880e60000d503103500d4075604445044495004106400d030b42c0400341c00001c594800d0408020740c510007503004505070000a80414071b55510546640c0d640201212003940050103003240c1d80c0c016130302501c08024401c02d070802040c207903540417052049a10031620480c1890f191405480d040d40c01c64050404003155512500e8140b408080c2165150034235010300381045130321401c030074602d0000745010031b00046900c242c4c0c02c8a010204664110b403900181515400b11390815081c0c2d0000e4000400720142d01a11010300300000d11003001c00a0000800400660040500342d05d19060203000c00880c1c05000e403100c141c520700010615140c50002e41164040c000c1c0a040140841c0700c407030390141101c2d0201e8810317070340c1d0359000c0100300c6502400e03e23640c0c507034031500c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 409200161 1250 409198911 409198913
    0x106121e0c0210050105030a0809130203040c21030f12022203030806090411061602031609060b2701050f04230f0609040e071701090c120503040b03091207 68
    0x740c00c01c1d40d80c08403507400c4500d64072540400c442140c030288170380740c2d0551102a6407000684440c0141031007560003882040c0310180700e284001a6402141c0840d0844040d849c2440014840f52107810030400c3e2004103d2019800d5a0180841d003008818105000d502e44035915007503420b4048070ae400200e10411407440140310038034201c7c41d001c0d00080f004107040c0e000044d42030505181c441d20a0350400e00080004031018188142a40803a505909a0400384400c10140e2003c11001c8456500c90a80f8a11249450503d004654403504a0103642c0800c1000f408a5121007203140b242c0700048041502107680e600058545114018000f45c2c0074a000c14009078400180d9409803072443d40d00d0344564046168010011502c201d14083ea030b00003002d01002f02c00b420302ea4051400c80740181d0485407e10b07104c0c032000076214628442d40b00b55a45418114040000c6501680000d0034000c812185103c42135461646a0141e4016060b101d10040006280c2d04030420500380b20982d1010860b5aa42c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 409201411 1250 409200161 409200221
    0xc0702013009080d06150f030504080403020a0b0c060907150e130c0c031407020d030302090a030501181b050d020603040c1806050324010b0705010605090f090f070b03010612 76
    0x1c018030841c46141303440c40004000d1401c1110200a030011f0b0ba0b104d606034500c0c00d0035402020090029158100c0c144804001600d45038903540103841c105001d0794540100e5002140341040003044500d00382c1105008110040c580040c42c406001d0500305001c00840a001050800c40d0b4603c040414504140319003005603000bd00b1080d4050203603a99070a45610070140d40450b00c154000290458562850030380400d2181e805040607000c024680001030703035a91a41800d481402610141c4000b84400443c1000140000c0c40e00f400f81034050290220f240c0800100d0050740e200000e405864000001020800b06c00c0300d150251010380121903211000122441c000c0440e80a064001c0c0306084032800030706001c00f482000c904900c201041c0d243c0c20042d41c42100e0b0805181221151749814010955039a0810128490001c50f000c24803607180803107405240c11902041c0881507080440144040c1060004483c19500c0a040c02000c0e40c0d8200c55000042c0500c0301c521040341d101f4080707034200b250 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 409202661 1250 409201411 409201417
    0x110912030d090605190e0613140a0303021809010518040201091d01030c0b03100b0c0c0310090c0f030305070204021b0312090606030708301206090c070201300908 71
    0x13111414038885d42001d580c2e0001120300c01d0200a6941d404200010044d4605143d0031100f80d01c108079420b005007041d080d0074a02001c0c900100c01180d004219a001c2d4041c1c1d01d040000c8400c204e4101401d5454a0003040c0c40f2039000c03500c1c40b50b40403004005800d59014528000040020140b0521181c0070002104d400c040e0030b0004071034201014000003030800e4108241d9021355031600b42456413505e001e04048190b400544091f1081c0903400d90b00c0e115540a201400c01c4821214000c03d102851b0301d443c122024507034204001a800909051020a03481815241c410f0b0f410341c1c006968064070000702c41e210410b40360031403180c80005141880892140f8600340a001800b04030740e096200c440803d907d500c500d015055890b48040498008800c0d014488013615041054005074020302001d122400d500542c0c4d082c070140400014404903050020055901c44803500310241003480544c00240a118070241c900750030402ca20742421808010b060710a0900c0880404001050702c0d80342030607141d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 409203911 1250 409202661 409202671
    0xf06090503010507080403020d0f031d010b0f0405092523010f08011805151c0507090903120b04060b03191503120f03020c150f0a110912030d090605 65
    0x150030140031a454500410481b40200e6142c0c01900654004810444146504d80c0c200300c00c00d51110b0b01030455955581c0364039058092440089041e141c800b090105403441c03214014042d500d410100482c860f4017084210701c5000c030021100c0c1c010098240c40d441030720140c0000d0183d0f008507a0807080c0e10070080c0d0a00000d10280c88400302d04c11040415034500400b40300b071410a4a2400034815200b07903070350066521000d8080340900c00704a910115200142491103c1020b8042d41c0b8214140642002180020403024030244151070740365074018011086101d00403149a16001d01040980ea15000b01d0050301c3e0000000c2d4807480c25401e0340c0284250440410300d064504140900c420009002c542e0949800140c4440d45042184044603040e94040c40c1c030302059400c0c07080707002400051083c580c3c440d07003240e44000340382046803c5422413040a8070700e81c4501e00c2c040700b00159200c4402901c600c1c2d0022503043c0c5615181000c03450851250410042d1610f143c880c0074000c1100720b5020a01803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 409205161 1250 409203911 409203913
    0x10c0302030f13150b0118030f0302070b0a1b150c0806131b2303250e030d050a1206030503070507080d0e040b01110604060501150e061608040f06090503 67
    0x65100c143d90f0403a418a080800b03444985800c40c41c01803140d40e83c01020403145d0603d04095000100b50140c50925034680044410118a00340941499410000040a0101408c08502e8030f069200064001d882c41e8a400d000700504518040034417284096808812000e2441444101a0300d400244140000c1394420720483c4402c604082115144c0f0030301c0d210b0360127800303d18401042c2031410343311118500c1425100c5919402480d00002c0c0100103540150310300b0040300154031070a1003d071031808a0400140800c990a11a156242c2d00051406103809003801d02d04c3d65065071103011504d07001c6041c0354603031a03070802ca0300104011000006043c06806102603030b010303a4a584505803114900e010789000200c2c0e8840b020820320741079102001904050501e055001c1d09400002d00b490401c4030103030b411030398501c010450b05804c11505148a40603283c1400e01641c0b07000002d10a000d02c0e101740a0110840b1210800c02c8807074002c0390003401c2c1101401c1189951483c0080c96030300345000701802 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 409206411 1250 409205161 409205191
    0x150914010e16050607020d05030f07030e010f080f04020d0c051914010314010e07021c0206060f0303030921090628030b0d08070201031506030c11030705070e0414010c030203 76
    0x81c007140410300b0000e03584020301a0780342032205d408100d1b507403443c06001e640e107000400081000580040049c6181e900c00e860300d0140038501800900300500c0540100305000e08081040703140340702108400d0b401503040360101d802580c45c0c1820705a221071608419040400e0041800c101c0500380310f4002140c1550103013152503245940110143c40000101164850000c4014054a510228010b50200a9104507140400c01d42d0000c0c411001c0c112096001d40c01c51820b004260520515004c1d66102c260019440d40c10127244540e9503c0c8103210200401003402e03544144500823100300c900816000f40b5960b02c422094000310140d03502d1080c50300400b007100511103503442c003901441030500c0c00101424a091196103c2c610945c2c8040b81c200c3c10141e50b4403c1200d682040f040c030764050f00c03950b0390004aa90f28000c0207011000c0d9031001144a5100f0b0095000064000540105950a0046c01401c0e900c40789000b082c1b1011884000c2e5065080400c59a605645580514403c001054050340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 409207661 1250 409206411 409206433
    0x50405130c082a030303011205190803061809030f0a1809020a120506180403180306060504110c030a0c0c030b04030216090207050d05090a0801060905010306110412150914010e 77
    0x414808058060f903010f810a01c01009046c10303c40607112514001e00030f031103c24454151039001145550000c9603224408000d1081c02d00305004490450030300448e400005c0d04110704000d5032070140c15052150a0800103c030704400d40710701e401280c00365400c0c200505250700d50015201075048010711000080c11241c00e10720300c28207401880e000300303405001901052100c000940d1b0000740140182c051011039200440018aa2501030005600607440010b07040d0400c010001954980d8410403400310040c401c40c4100003010088500c0c1c5415030428841080151821401c51581d681c07025003400329100c104014590045140207800082288a1040702d440e65000c40403406501001740107540a07008142d207403030295004214242004049800d044d50798048a42540e4007a0031403082d00791980010020080746029511000c003c80001ca070416080c824001d0420182103005040f602510390b804002c0b03d01a4440340340e5a40008801200030b40a85959001c0c00904081840030310075020b07484 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 409208911 1250 409207661 409207723
    0x12070815070e012604060b060a0e011803020604090b01020705180601021615080c04170a120e06030406020304060f1409060105120709021b0d02070f080a0c050405130c08 74
    0x4000003013442a041e045030503041409000d03100050003190b026558507203507545940e2300c2001d015042d100c2e0781d41905511402c0c000400380440308184101c00c4580e8030040c001a9900816030301640c10280000445d0421000100c0c6800c1d480d6014541004171002890000d400303000070503200307040c01e800300c44645261901e105c160075914401c0c940074828030a9600102071190f400308d600154031440035800c090b220f2001c0c094490903a84a503400d40e000521400410220402c001c1e801102810034510b80c401c00e0010490b2032000400040410760f002001a0400505901002c02010340300020480c00c7d4000003a090306401c10f039081c140340e10545000241910b841c1184040403020381d4098080a450318482401a400c4200c068902d007140800c078020143c0100303c80d00e60b114003680105000d500c0c0406039240781c101038100c00c4d20382d04842c01e000c0c04104046201e0080300c8054400084c4e0b540c0e041644a020607100000401f14034400100180f503000018101040c0c1410000e2040c2042142c0e2080d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 409210161 1250 409208911 409208927
    0xc021c0309111914100807180b0a0f1701150804060f1407030b030a02030304050f0f100f0809070e070507020409020a03030906020c0d0203060f04030207080d080a060b0a020c12070815070e01 83
    0x8000034102c540000d01f558031444480408480347e0300060b80c3c040d1104040c01c040d400100ba4200007800003030101e0f006580c45001308000a2001c00c1041c40da5043c082802a41c50544180301c06210b000780100b810003e9a0344220500e4900031300070050b151200304400b80c031020076038203440024206803a50106103008a5042e00b080c1d4010000e520345841c0000748503002c81e8105526521a02950789168544c0700c1241050b031901d0940e6030014124031044026003a14001b90140307a06da0300003601400320819013180b00c0d4000c101801e119440385803510015018042a001c0250403d0390400004109900038003a5400d076085a020b5420a00c1c04c0c0c070a201d005190018042d6044e40464080303280208030b034410035085402441654101a11005101c2c034103000c190301c00300010041030400c100c510350351140d43e020b00303100b21a052a2203444c100080da140c0892201038810f45403035040c2006078404100c5000248910016074a0312000000400b24121b0203c5180c4c012603c03503000d1042c250302c10303542 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 409211411 1250 409210161 409210189
    0x60e0a05041814010902060c03130e07020a0620120a1d070506030703151431240e1803030403021207151e0c021c0309111914 55
    0x881c441c900b010384601404242865140d071142d5665507442c0d002d6200c2d00001e0810541c00342c02543c1d28024070010b00b1050404e64017942090b020305091219941c1d010441c0429107820050115102c10f544004000c00c448034181d9801e545000503c0c603a0040803040ca1901c1114406001c00c0002c28802c0010f5240382c0100000802d03400101051005240c800d010b1500804649030015000c1030030050442550003d40110441e15841c0c0d02c80151841e14000004001c0c180040000d228a048003560704140a089900c00c2c405d500c070b00d60b05188071281d5041e41d090900301c5070300d61003031a41c070700582c068624250340e001c0da0b841034540003080b46800002200c5c0a00d134554010074205051550340c6046800450084521095070556181101c449001d07103140500c02142c80152070040f207c50310111001e80c407603030055420010140b03051150440c809004401c49041c0855601a9450103603000c201403886ca69114401003501140c0c00490b08005055904001840640c0304141041005006c3e061035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 409212661 1250 409211411 409211441
    0xa1508120a080a020d0203010f090c2a0302151611010216030c03050c03041401080a0c02060117150703060510030618090501021608250206121f060e0a0504 68
    0x8903485030756100b544502c2d8008003031240141041621040300d400c1e42d00c2a4003801c44100301d014140042c13140c0b032023028280c8040d810503552145821404811511202080e01444880c24411400349402407101c4c00204000e071441d0509450064088043c0100d0381c501d440014801d950040c11410b014400c0701c4911180c134050403038142e056601165818030400e0b04504200050006505d00ea208001034009480c001d0205c0c510240094001405540014070340e000081c1000380e002101030300801c42906454880c0581940740c0d80c1519564a480d03c249110401c4006540411002c07983c10b0388401c0a550049482c80a820004c00c4220291282070190810820312460401881002c66000c442d080744250005410300450a4102005100c4850f06030744400c4c000502204034030301410710034042001d05001204109150f004106a8003c0d4501508107000c1803012802c0070400462083c000200001841419502c4160051010340b0100b01e45025680030400814189002c1c0586024421601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 409213911 1250 409212661 409212667
    0x10617030f0307020a060e03030601080f0f010302060c0a050f071d01080d0305061f0905090a090818030a02031906060b030601020a12030e1e0705010804080304031805090a150812 78
    0x481e08026400030f0405002e51003030b20400e40c00218039002c1c020308410148040d41e22840c0080014119000080120389141c903e07408101044401c1c4078030905494041d58142d8440f0f044a410b140303401c181010240261089113107224113440d00083d60740580c4e0340d080d08050708003035040350504414000c0c01000030b41c2d000602c1002d906446030307011507802040204400c500e12510381010004403865540c501c00502000d105008030300b0821070050b0003a480d60010402c5422503141c00c4c40b13034082c00065a40ca24444131090140795810070521004603002002c0d03840d4000801c0758481c0584070f6080403950780c0c1c01d0035000500d030070301c80d000d83c3c2c8140c0042e00075002203022941e07408180d4108031004000c1c558ac0340080b08034950300b0031001654602c8a43c9440510300c00c006440d180030215400641084420070405c00001c40400c20f80790480d40c5402d0460840782800c1c100c5210005507000190054215400c0004034682500311014500540c00e19030391352502d90000c1515006c0309040350490010030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 409215161 1250 409213911 409213927
    0x405010e0a20130f1d0d050a260108060405010f2a030e0f0708100506181b07080d1401060503060d030513060c050d02010b0f100e041d01061703 63
    0x359050078400d80c2c002e00c0340003081400070721101107841090004548980e01c02000042c41548003190f04424500f400501e075060381240001d04510400368203100b044000010b041c915043c038114048001e404140307615880d80c40f011015511001210309032415070820a20010503011403081500c1c41610305584a400026640606010340100068400701942c4401d80341d0a00810300c00c65108000a8007d018410701d0048503500c1e124a841500c44201d00e454107101d0b4507500d0035000a04481d42e1520001c1d607981319011920605101042c06200420015402c41007040601c01028981d5402400301305040c0440f80c4a4103013202401503601041701000070451030700d41a000404428880d241443ca0045102e4084c01000e0140e8030400200b00000402d4003081070038024041200d11501c000c000c0e401036440092500a001402c2c035000f01c01b100c444059841c0725000007140668050014040e1003844103031940841400c45d1484800d502e041c0010500b00c0f1560b40c0708800000b07190046041583c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 409216411 1250 409215161 409215203
    0x90203060109090812040b100f2621040509090303090d030e1603051509030f031302010e0d112110020a180b21090d0c170f030405010e0a 60
    0x3c110300740c60702801840441800d00140d00c9061003140704000c03014207410a2100c0d8503004030280c100c418201a8003070188281101004c079030180d5000544640c0e030303100c2d0004030a13050011301800740c181e80986402514049502e100240308503001911005000d5035003296564413400250750a021640202e49084403140c07090308070715118042c54003130350310701c0004511203540b0305800e50049030039812000e02042400000c84107aa072002825010303500e421240710044c04240300041c41042201c80312118081035900c07801800400003005001c134082600542407000c005554900c5032072280590091391445225100c0444221440443c018000c204a04403164082c0d003002502c07604020311520a0b03100307030b480c542c4003000800c001c0310540d50386c546070b40c5606d1140c0020f45e0804040c000080c01d04c0710a220002d8035003108155880c0000b041c040514100c03010300d0f4031007401c0c420814080380010001890500940c015031161000704101310549154503229000741c030000e000300c03c4010b907000d104c5107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 409217661 1250 409216411 409216421
    0x71202071a04110d050f010e030c06040311071802090a1a0706020708120f0709050a03030e13060801050a0c2c090a091704090c09080715050403022809090203060109 72
    0x1c4110040d078692036002001c54a036132850340c026911130b1300404110714104800c0c071070903141d5079000c2c01451400c1c0340402607a5590383c001d800101008bc5445102003807000502c21070018020100806503030b00c00000d80240650840d0600c240300740b160100006108201c114031140c90301c072103400641081a661251300c001d4102d440b080c1c0b00381c2c0080003484c4002c1241480a0300c20701c50f500d0401d84905010f000241050441c0d000103000e180201002e0000c02e8010180800007823044484100f072030b14070403e6101070000ca0b400b40b245503003020184400d10009400490f80c0c000c1c9541c481c0e2440f041040721200e110302c101b4020100d090f680c180320b039682c1841d4007e15840707000030101081c0071000d55144003400460006004003108046424030000107039001d00d0b510078400b4034060940d94141030410361100c0d9140b16814141c1c6804032070750006d9025209a0380215001045040c002c40d030420f03040700b54400b2414020020700c1d81e20001c243c000d0700713110748050690060f005241c1a030800001d00011301c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 409218911 1250 409217661 409217663
    0x305160c0c050d0c150306030b1513020306040212090706111f0c0c08030f101401020c04020306010c0f0605160212040b03040314070f0201020c0d0b04020d1704030506071202071a04 79
    0xb4554240c0802d001c5c4241d200910410340d40d81d0001100307071071402c14031040c1c01c010b4a0a003007502d482184030499602d0703c03080c0c0c0c030003500c045005903a134642c0300018000348140b0503c0da15420311081004200c02d008038008003185c140e921034140d100340c400010340d1540c20f8498211020114652140341d40d14081d803020070b00340307918200000c0c41c00507900e5580468004454a4103031102c084100b104944001280500800c081d000c00304200d0000c4001139105c80311070030303107038092070b4003000083d0300c1e030b115900a03440d00350050071500c092222802d01da00548802c8172141021132042403950340f003d01c00550b40c401d0540001c2480d04250500075110755940c0007a0040c1c0400c51304100741440c1d41c12210080a2051041d2852246e1040c94400a41000070302c80040d441000c2d071212450100711045921540582d0464026502150f0b52405040e410349100020900760004900032080100020740c03030b0b004005603240e503500410100c0340321080e4412041c0041c8441c0030014102450020b0f0501da84d009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 409220161 1250 409218911 409218923
    0xe03040f030803040501020c030c0a051005040807200a120506010515040623210c030112080d2003090f030f0703050a02010e160e10030f02060c030d05070305160c0c050d 74
    0x40808c030901071458100e0080d00066070400c02041c01046010032190325000070300c040c14003842c54a078880fa40b01e40201300c000780c103c440c5200109540c2200451401038103900400c0c4045250321000d800a03040d250304d504803954881c1c0340c00410309241c0b0010012164148041c010328107418103030100c40d90031a0115004912503160800310305240882c014102c0e0a503030104a00c0c10b04440002c1c1445101d01a04260002101b0801070180c0031000303800c0781c071940d003005002d5610352040d1603030b00003001454860303100ea44840700035009007004500214050001c8104980f01a1340309903441b502c1c1c1c13050702191100000c04000c460700282c041c501400181f0300b03074000021060031288a181c00e110f091040c00300d00c0b192036403040c42461480055641c104003581c9103030519030709581c1c17921050100d0301d9020344148404180c80341251003c03c02c581208030358010501650415a20190141c007040c0d4005031194503108070840010320412046908680007041e10410a1508050014000111070181c0321 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 409221411 1250 409220161 409220167
    0xf030b01150e03010501030f03030f0b10050f07080f130803030105010c12030e100f0e010218010320040b0331061e020c03220308031f05030d030c030e03040f03080304050102 76
    0x2e10750702031003454029402242c0d00200c0c4400303490f000f000c039904c1c2d00031030750b103503240c600700b10340a88400041001011107801c00b90741d90074501000c0181c40c010000b00900b2020000b94002c56a0540f4024200010384280c02c1c0c1c840680300c1280703507140c2c0000d00035940001e04030508200498083d080c8200030700590700b0001a1844512415400c254071440c468002d191900705c91046403406120311200c0000301c031b00031800c00c102851000e0f001c411181001d81015124080e00701d41c5d1140c80c8080c3d030440f0701c42c9101540c40380d903500f07695929041114102140e0b0682480020902d24143c0ea696040c00d01c609030741045d0020750381e801c1c01400c150001030300034034000c0c1e600040348001d41300a00160f0603107801182c4861505081701c0031440b08240d85103034102c10940410000e00d121003500d800c1b080464030817400c0e60125030102042c43c0c171948034603454800c0e44015851641c00d42c3c041402c0399240e0b80c09004070f41c1d2400d50740b031341c9124900c00c0420506283c00b040011403082c00281d50043c0c03080d00050b00d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 409222661 1250 409221411 409221437
    0xc040216020907080414010e060402090405011103100f0510121e09062a1713060212040501060504050c0d0b03032a06010f0e0f060f031c090f030b0115 66
    0xc02c2440885850020421640030300003800000c00071440301e07402c910001d0044401490708a520f444025000a000700308103408a82000000c2d0410801d80c44080c2c001c0b5160301d084560865400454401c0d400d20b003c0312800410f09090040d200c181070700301c580350f1310f42a81c1c001d041e140c02000d014000556001d59018035502c102c109018082d00580101000310729051011071032110084440042071030200c4043c0043c0740c0a421040c80e10011030100081c85e40c6d5a10780042040d20031080350000e0044c4d10004240c01d800107680b03402030196001d070008024103038a400501040f103000750b132000c0114005100c05074040308180c205100c402006400d59092004070100070031410710f0345100d10318800c60302003440344c002010806540100184000c0800f00740c42d01d46c1c150400381c03020349026222090f40000440d00e850700f440d4000107420260860f0101092a6203038032043c4000300110002449905001aa50b07102c560060242c0340c20124100c0141d18000400c00b00325503142d5040144469121400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 409223911 1250 409222661 409222669
    0x130f02040609080105092d0c0a09050a050604090201091a041d19090f030804051f020307030c090302090a0b211f0c091a0f040909050c0a080c04021602 66
    0x100007814261140840d140c240f0406500350f4800508000480c0d1180ea01d20003103503e40701c030885c1401c21580040b022640c100d18805e00300402d40b519190000c0c4e95643c0001c2c54031659100b20720403150300004101988400c41080250303401c169019000800c8148240481510f4003004e00b05541190b0b052441e280d83e4004030a0000f81503000c0c5551051407004001214483c000348030710f8488407000401c0056050b556901c0204a403074005010400c080b0006010000d0400807010344400c41d101e50040b114203502c0700c0300658002c885443c0080d0a110061084030b0040c903161040e41c2c1e00401412107a074622840a00601c0c01095442d8401940f02e0340c1216108410050880c1da540a005441c08180c0d88a1044c42d0122168106e12884c1c42c00500f040713840e078030584181c00d039014a4034410621105103007284190081002e0345059820000e0009072901c2e2580c040b40340d09118206665418065400b00540300c0c070f20384a180d0f000e0700f019060b0006460198000d2480c41c00740c2c01c0103208020190081303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 409225161 1250 409223911 409223917
    0xf070e1008070801021e0a050412060b0306040606170309091609170303010509010f030b061509060c06160201020c07140612090607080c090105180d0b0906041703060f130f02 76
    0x22503c5940c00142200d012603c500ca40c0058821260300c1c034a040f0100c14000d18a105600c550303511a61034641344010041d003900203802d212401000c03a005070400d03042440050a1a100b03044000c58043d07220035200c4800710554a0301d220081581e0001d030340b42224401c4d20f100207914201001b4a002e404240340c81125101e00f44003006900960300d030360420b400d111440b072043c0c10920b540c0701c07104d00410001e500c0f00b610b154009416540320f2450820b00c01d58003224041d012003154001000300e0341501f11800055030604c54019140010000194010280d08038840d48400020a41140009101c1e40080d84c03820011000050a91464500c0755000d45405500c152070001043d04a5420301c000540e0040c52107410400e110b61551900309140d0010b002e074030803000a00300300c0c3c1c0300480c1017086548001100041d2078100ca8141c1446c5000c00e00b41e602c50004803011601c0e0502d0840484c0c4202c03c1c101941c2c400e2030b0243c07411603214039102c1002600281e0302001c1c7d40180d00d9401400c1340b86940c1c005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 409226411 1250 409225161 409225169
    0x10110d2406110c03030316030c090302042910020705010c0f06050a0501081b010801090c1202030103030207030b070207080712080c010e010e010f0e0d1b0c031101110f070e100807 78
    0x64003000340c000c240b81403e00c04800340c5a40302c0d80c400e000380a41c110a00d240c10ba5100310700e040003d801444100240d407060503582c8042c0d48280341900c00852201001c0e20b0b010803141910040d01c00c007125904001461218401350310069100d08418006540160300560070680119101b40c00c0030301c15a42c1c40b080e588111740c41c4d2985074649004200d01102041803210880d2140300381400c810540000901c1d03208148200c6141a0b1601803030344085000e03241042d141244e1000955503580c41e0704010b50f0710480751204407504910200090809407010426030207031001c240c0a010210b203808040c03a8004009070094900d1b110030020758074010b409110310a0b509001d0000410b031400400d42403400c490b00d040079060305a00307224002c9100c2c0404a00d903149929142809051344098600c41145400d040e60010074031304500030f010047c003861682908105101740d80707c41c8821400b80506d0344400b103804030240d00f039102420a21900d078821001d50342c4418080b108044450395221511301c5d21000b684 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 409227661 1250 409226411 409226417
    0xb0c070501180606060c05060708070c020a080a0b01050108010e0a0b060c030309070609051509091e010909020a1715040305090a0314070b090a0306020c01090605041410110d2406 78
    0x10040200081d9025144c014205414031986103010b030f842d410f0315103500800741e004108040d000a11001d000d000030940c0b0640240030300407900e4231120301c9507441e6103103071040d108a84040c0c00081c1035880790300000c3c10780e018540580081d071200b192210141807020b49155001609124042c80c10340d0400203103100b100c101005029443c9044d0002e030140d5400d03007099000c0c17684540c100068001020844d5400d160640c1c440d5919613035240003400f1034210069203940c4140c6074000080719545e0f500070b104502c3c001c4800000040e500c0340c06045005004d0740100c1a90030510f003460342001d204074020f43c0300303001e802d12625114000c00020031940076a041180e907804c042a1020800204000709000307401d00b40d04452900d41d00341d00082040d0303030a2000400305600024000c3e4992800e400400640ba130143c820b100c1810140b900180c075506070070b40749082c2d100c0e03125114540c603064043d07071040c20403980790310340740040391040440540f169403c1411201210788070301800b14046641d03607001f07008a507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 409228911 1250 409227661 409227701
    0x14010623090402071a0c090a030308042303030906012304050a14090a030311070c1a04081902030d02070b0a030e07030b0a020306010f170a0f0f060b13050306130b0c070501 75
    0x3201405140d80203401a401b80e1030038007040c8683d4940c0d0300958140c035014105103080741c0da64a060503000d00f11038086030482d038100c51048a0410000b02840c0103049400540b54180e88900d200210200751521039144040100000b00d10350500f9070150782c01c465500d0000c28040451001c8211070981921203804641c0300d40555400e050349442465810648402d40f2480c0c41d000d521020900e504600a4980c05901c4c146004014000340c1c00322001040600c0c01d540d00301da001042030340c10440318041a4040e020f444040070400303101065590954070f05d0490326050130f004031811001003820154544452040b0f0034044045981003203064401c1945d10785c09641d0346080c04c001002d4120600307011342880002196611081d00243c8490b5104508030000601c00d00d4503074000700501070800d056014645003c501141f1a46000c005080c807180c1108440b010b5961072051642d2004201c0311038469041411050300024240c0b40d0003074000c0c3c4100700c0306040c002161900c070b08481c05217118503190340d404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 409230161 1250 409228911 409228943
    0x150602031c020306090c16150c0e1f030509030705120a030b06040b030112022d04060602030408060c0f1e031e0c190207080a03080405011401062309040207 68
    0x41c00326056034010312002541107040c83e9010622100c40a450700b00a4080440c0b514884d544030080712100710340110707001d415100f41c500c0b2440200b84184110b400a4802c40703556459042c80d15a034036003280c810001c5a0040e1080c00c0490082c40050003440f814041080305d0000310704108080144029446c2e201c0303503140041a405030489900c5241c207401a50140300800000b4456000d4904480e4185440102c070310261000032405002d18058443c1078401850141000400f1300300751030308140a550401c100c580f0746100340da036401107118490b050b034849000101c0c00341e004805000d0120001e10b1090074103000310b1000024201400c001c03900445c000c01004250b9450340000441c7c081c0304000541c80e4108001008041e12481c0c0d40d800d241c41d1034407103051407184200030740c000038035035801a1520791405150040928806941c240c07071030341c06c003540000d040707140c550071074103c60803900c0c0c090070301c407209000c510558103001c5101501e03031060100b60011303111800240b01c0c151103405a05002411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 409231411 1250 409230161 409230187
    0xc06040b1b07080607080402180a0b0f010206242407060b09010b03070e0f0307180e06100302090a110307030905160f14041107030f020601060e09160315060203 70
    0x40d0121160180c2e0007000700308540b0b07030085038080d00300f003640c070340301e01c00d940d56001141b83c0e52242240d04d0702100184040143c600e03103a522401c8a200c04941500d0b07003416403401260b0f1040d00391441c1e14000b000b00096000b0401713b96125019201c00782045000e1103c1c5000031009194241d41d040b1801d0001421800b084494803d030590004111417401c107550415411105a000081480c001e2080d0449881242d90317505224032030b4000014202c581c1551078141400343c02d60200f11007400c5604240b504100001c020400324820030300411b013050218136603020010740440203444072a0442ea100c103c20582c2188400451003414240c8001c200e4070800d00c1d003240740082c0b02d0703100e8000490ba42000c1c0212018a01074030101c2d04000080e101c070407003e80000f0014550202c0009007030100090000030160041e582d0b4241e40307015020f5a0083e0703a12241a20303460513420429600c510642d00140340101543e80041031882c0d14a00003070a10080884480100b0054018001582c000308113036010250b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 409232661 1250 409231411 409231447
    0x204140a06051201050607140a05010204051c080a0c020a080a0b06090a14042037031e0c0506031e0109090807140111030a0207060b0405060102060403030e0c06040b 72
    0x40c65242c03042c41c000c0b8081c01500b0005041c06801c0c45000002a840140440203010005e01280351050740c2c0c00140614045000350700c14444c0030301455800d08072082c7c4440c0704516006482d00b01409130b203006c0c108401101c40b1080c03c5070032640a5089100411000410840d202c2d03283d205820321403075418a001001b2114800514042c0020300340007142500590380034480d40c00c103510644804460001e5a98032241148012515801c400709001c41480500c1d12001d47d440220340f1280055100d01c041d0310050300d2202c1e0302019043c03a9800c012100321135401c80041c00310301d0144090801158030303580082d030280c2c019951003110103180d10340e20301e1800031120030b1401844a440204400d0b00f00e580c6440f441d0292003400f410400d00b0f0703095400c07003070401e4200c5c001c03c0c044002616030320314203042074a00a422011050b21008e1810051000c035007040e00c10b86000700c0050f0002c0819aa2b10b0741c0440280c1900c0c00c8504040c060400c00c0c444940f5040d000c0e00181100446598035000241c00c2d050f40c41c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 409233911 1250 409232661 409232669
    0xf04051504030e0121020f071a040201080f06040605040f05191a01201e06060109062a020909010f0e030702090711031611010e1516020f040204140a 65
    0xc031404107000000c1e07006461040300680030700302004100c14400c1e2a00b20000040b00725224140001580240307286010000c1c40847e10620082c400740b241b400605031160411140203020a06400204080e2104804050303805003000b00046082070300d940100b400c0d5038031014000b11803501c0340103100303044050005403240f20350441800c02940d240d00903250054620706040e43d0521903030340001050400301000010040300724004a690802d600b03460a031301840780d006541d180d80100000700f155903201740781c3c01080b030b2000d80d28140c5910b034080d9480510306d01c05004a0b0700e440c01060a8005840300702000d80f040341c9550000a075818445a15000d658004070011100d030000c0121000698401e01002e07004180b500e080c4030800010380841d40b562182d590042c2c281507031044103000300000c404030200e039607500baa0703000c03460110300c0f05000c00003004020b2100b00440c280042e2a14140c040e000c0138400b40002e0255010000800100f0200d0b0300503006514910002c903c41509802c01c426480010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 409235161 1250 409233911 409233943
    0x30c09050105040b030c01080c07320f12180105070f0c15090323070f0f03031d010c080d090b01030b040614071e0c02130e0d030b03030d0b180f0405 65
    0x20380020b0000814079400140280c42040d00412b00f501071048945c40341d50081528168800b0400b2541c0c800b61482d10a44c04010191044200d01c44d0750f50310101d503007107100100c0300b41c10f4141000180781a0b84c250320581014100401400500c020075440354056010341e001d5512180380a040c08014130701804014401c00a11241685c00c20004022101d0700701d6214040b21014804090340c8255800c00300755610803c9a440c80c00b82c0855001c0a8003140030860f41700e9117459040b503041421f42003204051400290210702851044c40c0490284002800c0c03c0042c28800a01c06030b46070b0700d05400300390a13001952610403050810081003038502c9180741034030fa0200b4a0f1514545448010100c003916450224801804130020301c04d24007078a114100c41d47d004150a404401403d014402803040045941040c450303908449240d074000d1068000b21403018000e18504014451050060f0003169442a004a410508120700d01c002034a002d008012505840c1018103090410900d041100c192510389 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 409236411 1250 409235161 409235173
    0xe0105221d0d180e09010b121b0a0b031902090d050717011517010f0e030901020c01050a092904060203040906060e18071404060c050712170310030c09050105040b03 72
    0x3c54800c00615100319850b1088072070140d03464240c09405003000311b070841c3c1c101c0260004007540d4000480d07c00d644c078040b01c1200c0c0c4c000f01034108003c0003004c1c40c0b1540c1070700f980070808510032406240c030345000c03481c41c09005403038003c400011503030558030040c00780d03181c1c0c000c000107000350813164100c98600b0301c0b00310080c04401c9640400701c0d0120114411448440040d81d285140c110742900100c040316000001005072440e407036012a02c9078440c405450050203001d41c0c0c0455580640259a11030780b00f6514031a0705820610480c1e074012440901904100074154600da6403d40c1d031004201400c0d81c1d50266856514189140c01076a100c0e42010090040341858000282c03508a001300280b10740581009542e205ca89055561041a16a48002c00c00010340416044e0304000081100303445141112107050703032194075504541718440f004041c01404803d8103800c4013040081e5402604034804146200c2e941da07101205184c2c1607115488154a03400108460b20b07261007840712040f820707800351030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 409237661 1250 409236411 409236437
    0x19060501090c1e120c0905031606020c0d061b0c05100603030c030f12150501090512100b0a0e040308160201200f120c0712090e0105221d0d 61
    0x10b00c6000e01910002d0440070f2410007840e40b10f4001c1c640c085120443c10008250300d040c4c01131281d080d40c0103450103445054020304000c007000c082e0f141120a203a02519010f01b07200108060869502e60547d40310b5102c40d0841c422001c100c80e814007a001d0768891003c1c444152424601304038040120644562602404001003508003600c2c0908070350518104501000ca400c00740d4080b4092a000c5502d40e01d0030728009080920100d00034182c6000742c90f02c403c9540c0d81d07801c00c83c15030141131030081d1980003041e00c0046040150040d07070080300300900b41d10700c0c252500303070b0300703008a00c00c030303003d90014070020140030b130f05860382d20701c0303510150284000d003c00c4510380e0301c8180b00818074189106140380040e014207020781c5d2409403200a0381e50610802e190805481044030b0703404c494400c0d50081d141e0302c80d034040f490180000744100c4220100300e0201e60319203802c02282d03e04462020301100207103052800c041d9018440c201800e0381d4480f8028000b1088003640b03207086260740a0364140203031086685 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 409238911 1250 409237661 409237667
    0x1110a11010f050f1305040f020a2f03120a140c030f0903090409060203040606060c0c030b0402030c060703020a0507080f100203090c0d0b010e06150703030c030e19060501090c 77
    0x44603035602801c102010030340001007103a0f43d03c503404100b9007000000c00d2405209031489140b904949045509100e01d0502600e1803080b4851a41e00c440400c011340a00c04502840c4d40800203414045900c910354020b13601030300b80c150b0f80040f60485d212020312080000420841c8582e000150f0f400b48241850310300034852595600c0054103814050510400041c80d403a0104104c07228118017030002d0004414618020b000b80d04191030440c2c0150a04a011410611961240c21266040200e120b0814610f44516404100240c4141d0305030142e90000d0b40981c171144010041d181c400d60003499680f12501f0160b0812840e504070000313035081014864803039080001ca031300300c2010201c00140c1d2070302c40640e207503c1c00c48000042d580001485100320213120940300c020b4100d81c0d9081c081c2017581e41e44420008662021606c42072080c40612440380401d01c03e50100c0d0700001030b41000030344000b0340c440361403801481641400c442c207500c4100e042000b0043c017826004044800b0240100c0c1d001003805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 409240161 1250 409238911 409238933
    0xc020109150b040617030a09090b0f0105070c0306090f0614070504150c05060a0204060801090b2b0b0405030c0c09012d03060c030f0b010809061b1b0303040201110a 72
    0x9a003400e5102ca40840c4980d9403079100c200208902407080056005005105860713410080010300070440660002030380c40c55a001e4420581c40050050b85000c0b01100191110340000c0c03020354400d041d0360804400120240301e5a0700641c05004010791a219038649141650011100078078800795002c00d00ca4500d4000c8144c0b015510585102102e54002d43d804665400704844040c18a11510003400200c20003035000703106440e00c1d540c1e41c9030703560380b04c514000a0b200c40000c2c4640000d402030300040134446030302140b10020910100707940d901c071158442d400701c0181550190707103a4000042c0c4145401040023038501240c3d0a407403640b850740c07405900f8100c0b0556850000750601d034690144030540c44c0011404051584490104804020090000d004020608140520354030300024a10b003580528403103841032030090020142c50351040045802041d0400001d07007088000d0020311003000041500104981003d03000b181c6a00d0207000050402a0030303681503005030400951000443c010145c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 409241411 1250 409240161 409240193
    0x20a0c0504050601021516030506100207060e01050904090b01080c0a03110f041b0c03090911030a0908040803040810050f0f04030c0203030403020d0803060306071d0f190b0705010c020109 82
    0x240c0d981c3c4240c010b0f0709000c030708120003002d00c3c000010004420b61030114510025581d990821950352418140b0401d100e00104910150f80f000400300425807055046c01900c407410b1501c107043c4440080072405540240c0d108466800907080184060392040043d18059001168240d01c3d07e440e50311990224074181342020b0280307200c440109441d4075a50800001d08200c501164008490841b00801841140c0400c40008031078120020303502d03625004440711401c0c040745131451911000752000c000e10803003108591f0000c00b8000040c4199081c0041d00003400e205028251301d072500c00103e27040b550014034143c00420f42806011011004081160f44240e16003030224492a150000270b18500491740020341c070030505039110301040a16409036004e179a06801710384540d2a5480c00340d40e207810b090010040e400c203c40c000800381c03901c3c40e100c03030360084081d0110102e202d030640c0000412126412000000900151640c2044424490803141000e188001c02c501c80840c2c1e86c81d4500c0d19403101c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 409242661 1250 409241411 409241419
    0xa05090405090c09040c08060c071109070c060501090c0e031902060703050f131706070206060d0c0b030702030901020d05070807020904080d0e0d030f050606160804080d0306090c020a0c05 82
    0x10342c030038100b000f40010100c0f0041524440e03151901e00401e0f400b070b007070044015601520010a1254844900740d40381143e00a81079010714502c0402d021030076070002d10f90010840000320345008106d041c490769000e030003407684c08079000c00d025402900c43c40c0d0281043e0300a90000780121804a05801d40c0c2c01ca2650440340c40d43c1c1d8460a003021100c2d40946030003280d200b04001404003255908841a1044410144056200d1180d000c40c03e904c0c0d1100726011005a045200007510f240b0744094140d003214420100700042c9034a4003052034154100311158005070b440010450450b60701003120703504000ca41c1c80c03c107284c1452562240f0240c080e041009000b8a09100801e04102460060350b5000f154181c0420850b000d802103507651780264410100802d15100300e042c0e90001c10700415114501c05041c040c0313000480a12004030001e50002a90610000c0c4004900f0324414026621001101d65001c00c50030b090800e40d90860f20700001d6141558046c44001d00062400c01309802103920480b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 409243911 1250 409242661 409242671
    0x41a0c06180709060906060806040b0a03020423101d0106050906030709080a050709060f030c03020d020a08060c30160e0d150e01020406020a0807020409170d0f020a050904 75
    0x240700c64034045040e00011201400d0680101d00e20b030240d0302020844086a403400d000740c441100380411214400c20a9400c600480300034005420b240c1c006030840889020b0074801352000c00c0b06084102c4050b075520a0304c140c5030300c0800180c40c0b00c90100c0040942d41081d002d06514003640274065100f91b00301d96010705ea02100013211030380130350381c191300814000f8241d03050104180b030415211205405a040c90600d4154041240300c0068985001d407940440b104041034103640811600008105080340d002215407004942c05809209650181c031503600c1a071340707035044139888181030003566100c03550101c003144410140400c0d0000d0326410400a2038200c07460445600101c1c1d030000380c1c501c1c003a00b00803410f0551041000780d014400102c00c40d080e0403c181c5c907100080701e0a070702c11841030400681c0004801000f2410040c000c241d15407000b44001911441c2e503460000c06640c18940c081d00b00300214050801e06498020340104a5060500318540304480d0303000351540c0100e40019001d03681d40d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 409245161 1250 409243911 409243951
    0x1407061103181504060e01021c090308130504110a11010b010e210106060e1804030c030818150619210311070b090a0f0b07020d0323041a0c06 62
    0x80c40300c0c8205030310f00d1101d5607500d0341c680350094484001d07a601c46005205001d28060140c5001030680d00c3e008070766889070381c0b0174a03548410486070007241e55032500c0c240700740002945030751320303c40c0d8103450440c1401940c4a91241c0c0c405042090703614203120080e410306282c03901513a8007405a1510348011103020302200c501c50102d0342c1c1035075001a5201c0ca503282000c04601e8641003160240b000f60119000d550b841d03541c2011100303e8006441c028080399510000a000a00825003580e1000501c07006804e0254866902854a00780e052903042c01590b0740c0900840e03042c5030002c642d11080350081494000e140030303010301c000103e800c0c488012003150b400783e50415224130031415280032a8012a40415260a40c0f51255030241601c80e2040006520010f0030b40900382402080f82c50b40d03c00d10782004610b400f8000000241d00049003040b4222483e202d00700880c8111a050003a008090307516a0700b060344650f03081d000d810a5a28148041c0035003c0d0300c40d00010055842074246071120501080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 409246411 1250 409245161 409245169
    0xc1b0819050c0f16050312030703020f0706060609061706030d1d04090c05190b090103020d0908030f01140303090915010212070b0f0105061602090c0d09140706110318 73
    0x220448820580645100310211280c00034401030700b88201d04c4c2407403c082d0344004140e5144164a048249840c00b400018034203400307a03000c0c141d01019810128945034240c1d80300300c00c81d51a900440b003c9410701800340a00c9900142e40b80c01c544054880980c1410190700007540d620301c0e240c840b020030410070b01c801c00c0b0004d1096909441c1f10050030500003480031745001a81217075517004240c0a500c2802320300f100c0100540c000c02c219450400a240341145007001113000e540031000103011903071202059400102c0020065100f0500260524515410702074002901c900da15445482a4410f10812000d6650b21200e5900706822074103c4000540e000300503400e10404500600241001040c0c160501140149040c0b080e0034140504c141c81c0c1c0c8031401c1111034010020341607503c06d40780d0b000340010f003800c80041d03810220301450a4140b00314800100c0c2618500b100c1111204502c400c101a8003008104c0c00c40503009505000c992014600c260a9a0f4059039a02100c400326150792524036490f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 409247661 1250 409246411 409246417
    0x51006120b060d0c170a05060d08070512030f040204061e17010e030309061801060b0a032c0c0301320c040e040b0609070804031d0a090f0c1b081905 65
    0xc0004000d00c0074400110028200048001140712508175003000101c00f28118402c1e50301c42e1200800d207032449181500c0b0003c285d00301d9a41107455114000d140c1c00382d0146400514410100b40801c460703549003520521060303507025030051050070046882c000a00208044080656490b000c2e052000c50302031142c180980703c40300d4000140d01001050082c0c140b40440c9030392081000214030b03d040c005d00250b05080352a40e2046400d080014481510414440d0700410307510b15074000d01014244c500702c41ca820a00c0c1d1811410b4a541c031480c1d20181505007030243c6020019445164103618041d07040800ca02c1d0710a0307000b001340c805200002245c900414050780c01030451814a080d1514251a082c800d00c102954040c0c400c154510000f80507038844c000e6940724552581d02c4180e8405007020703002c0000801080303560301c40540311000c103078140d041c41510800e0f440c1342c41c0072940300b8880e400541460f000307200813140140d5513030260020031864021250144403c00000c90503140040b400c0300c040c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 409248911 1250 409247661 409247677
    0x4050603090a021809060103060504020d0219082a010c05030d02040f17012c1e030a0f050415080714071b050402090d23030a090603051006120b06 64
    0x185000c8140484030800244001d4064804d507200940d40d49030b200030840c0304208441c00d00442c0e000741c0c0180001001da03084180c020b8030141c29803421704643c0d4001940e00c2c084450307440d50700c00000b07420401103800b00112084c885619081891003588645524090000c01c2042810f2000e62185842048410000ca42401d040403000315101c644030300d4960f058106603c5001c03d042941b8280c6044002c042c031030400e484192102107031145c1d414054001c1c49050441742480d940c040c3c050300140324081d00d1541d00480420034040c5039030700b50482001c0e007080002d0541408000091005102c1c4501905021503400341c03d091150711540c4a50080320400386020311106010f1000c50084100120354603155803014105415201a948480521040f401401d040540c41803503406850041414103402864091103082039a0941941c807880c0c501d941e00c4007440d2400100d001e1010082140d0500c580307a00103000300c0f40340e04110314200000f41491604030005120659501e244800340d44c5220480d5011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 409250161 1250 409248911 409248919
    0x3020628020a05121206041a130203040218073207080a11010216110a0305011b08060307030f0818100504031b03121b05100c020c03070b0a0f050405 65
    0x14002044000d4450b10520000c441521902e03100c0c0c0040300a07042518030303a0703500180da600030b6540c03201000043c2502d95103c9005048003000b40b4260f444080b010001d0710940d440169507130410348140184048040d803c0071034907000c1000d000250b40c7c400320000341c450360441d107204180c41198801152200c2c1018003000f0020006025080280c0c56025050300502030b02d900841c0c03c0c451445500740e105190070f05018516044242c00000c6000d801441c85550180010003000d031a175a802c0e084450a8002d5800d4500013a108031840303030b0080d9691b0b8811816000b81080034919940e600c4403074110036004111040c0403681c01041d120f49101174043c81c80041c42c5002c4808800c101602c55801804203885608001d249840701003009401142283d0741301c1050900221800c030100c4181c1103a0841c0d0401c000f6a5072502c001c83ea08108403202e4103210800050b0804000c04040d242c603441186480c069049030008111303100e0143d043d210300f0303645420070140548040300115024480c42d0802c940c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 409251411 1250 409250161 409250227
    0x1a0a02041d01090c080f07260c0c0f0109080a08150d060e07060521100b030a1505030a1101081902040807080c0a141003060e0a0e0115060207030206 65
    0xa000c08100c1c03624102c07582d1900401075030f04212021281c600c0103c4083c0ea103103508401142c81140300703012410000c003880700b0340384824010075110003014500340c40e580c2d001c03400802e001c1c144810a0000c60114224400204001f05a69458044501405141c00103214040d00000c3c03074040c2248011501c3c5c03900138520560100c0034500742c8000c00201500d21001e2203150303030204880e07014504545203050011200e00291445d01c16550500d00010300c0a0000c1401700c900060080c4440301450050b60b58280c0440c0b207840d1600502c01241841e1700c9541f1235030201501e400803036211550800106028a0300851550741c1c50100c2615680c40c4a50103210340c800200014a001c001c207940341079440300e0055550300400b41c41001195070080c050054912059140100c1918040b07040c6c10300d01e40c850801107000c55540000040392101200c1801803281c541020340640d02e000c3c4a185c2c811400b450090741c4140c20000d00a40e904994007000f401181e000130301c980f02c02d80785810304d0044013400c401110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 409252661 1250 409251411 409251449
    0x2010315150809010f09020603010e091515090601032702220f0b0105120c0901020a20010e01030203011508090c0303030103140d020706080708130204050106020a0201080c04031a0a0204 81
    0x40542c00445400e4a00e500e81504040c1c1d200c91030096000c02a0002c0c650380c150303400c1c1060144403980192048415105d4001000124195041320038410042324070108110002401401484440180024101898205c40f0020900e01e490b084124290003a00c07100303811802d202040140f03094a8581140003006c5001c0075042c155504626100c0d0341c604000c0c490840080015500c9004448900300c00d030206c040054500344602025001540701441103c50104541e1280e171010f10b8041212501000d10b013042100a581040050020340c2c420301e411851580b419a200300450f122035020020484103070b0210394a1481040528078000e0010700340c0340c1d0f03542d481c07514408034100d03a101200703030303000f05406002c5c03281c004a441411100d55031076070040341d03445c86411288850010114007102c0310028030480542c5880c400e09001e01902c1d0000e2100901900025140010003000814100381c10001030001840c00c964201d2a005050100e10150f00c5008001c40a070044d900304840c40020709038540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 409253911 1250 409252661 409252667
    0x130605181e0a090204050d0206031308030115020c030c03030d020a03020706020408060907140a0509040317040b06040e0a05030708070f080d05010303030b090405120a02010e0304080105010611031201030201031515 93
    0x10a07140c0045070700a1a02d07a0310403510041c0e001e28401d155200c0d5003084a0009414076100455200c0110841c060359401d03a0340d2a000d01d600283c200600d0082030864080d0480c0e010490724900050842c014081c680800c0700091b90b0340300d113038500c0b29010f0700440d00607801402901501d01c095840b0200395104d0780c907003110a035240c50460340c0010501c10140b0000d940f0208100c0301c0c120300000750800d500142040d042c40307010b82010700704078100f01d02c1e8160b1142c0d410f24500d000303004501c1500d02200da4100300741004140d80036903080308126001403800e007002030400402c0b10801c50717100c016941c40750743c2800c1c80d03540340d0f240c0c07000507200f82c90001c0e1200700d8603982d43c0900e0503203110380c0341040300c190720800b4000c184d102203030014003960000802c080d40c0d200240c05421307820001c0c800410303d0b00640d0760250a64100b0f6012603140d070746680050080b01d8001d02e074007025061001c010350030465840c0305440c680806120282c14035030b407030004610042031455004003804c03022058400c4001d50312401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 409255161 1250 409253911 409253959
    0x120a0e1201022511040203130615050f1008011e080a06050a0f0203041208090c040c0c0b0c0c060f0901020f03010303050324010c03120216080705070b13060518 70
    0x601e003014255542c0f10f0002850304a1880160b00400203540d924040750a01001303500150881000031903159100340003070400e00031030014001b85403544000505c0c1c4130074400170020301215140300e00414003d50820a03031000360281111074032804105c02000e03000018045003810742106449000d110341500a11100d5004140900034019040000703000c1400360404a01043c0c078010a59039132981120003503849080a6904503105206a6002c0c248000008049940030f2900c43c0118210186030414000401c1c44140d200241c1502035180c52401d000880d2960801000314000310f480c0d90104140d40001d5050307505001c0514091545c95850341400f41031500200c992030724000304d0a4100c030000c0c1c00304040b00d1041406071541e4208500d83c0e82e080c0c0f440c90a585914000319404e029078001241d01740750540c1600e019035001a03450740c2d02d00b00541058000e4101c600c24070700401004508000c2070030b407001111550704d40f1a44070904031688040900c600c6500c181d02c440721804001c5050410802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 409256411 1250 409255161 409255177
    0xb0304120504180b0f220b03060f01030f14060106030e0d020d1b060e0a210c021806031c030c030e0a08040b070c0e0405012903120a0e120102 62
    0x1149241141400c5460b0711890059480c01e850101c2032410524994128140401c8005c201c2d940c002050408503550f49601603601410240304544817940d545a4030078940c54220580c00303445036107405d9002c0080ca442c18031005040d6100240c42c42d00f440384548070700c2d40090041d425600556910076000300a00940c041a521030b025060700201a075000250542c1c6801007511401480c0100000b4819216819101035a0440d142c5007514a401424840842500c0c07042c0b02600400310300450580e0303034680c4224401d0501c10325450b4800942c2d070700744071540d0020303210116080599a03103001c60b084c401c8a0a402001c0004404030200b0540c0580120000e0301d02607400700482443c8031041996801042005488075030100030500c81c1c00b5900e0b0042c10310600844d41c00c014581e585000b031b00740c2c08085409403041d035950707030702143c02e40c2c468015400c04541b03c1d25078007240c2500000003600c400c6045503288840713800003240008a4050700c01080001c00040c1000d40b00d091790030415010750702950b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 409257661 1250 409256411 409256423
    0x190203041b0e13060c03021335060103020f1f0305090607030c1209021206090309041401260106090603080405090702030c122d070c06030608030702041d06010b0304 72
    0x81040042d800200344905520403d48a491041c0d0b01e5190003440d000f4010810142c0800c443d01c00c43e094000c14074000c005e008501561002114010400e15840d868400b46485146810520401000072080d0540c0d4040314003400d1000f401002824843e020f0925119031000c08002c40501901588002e2161030842c064414603910b8150032400c0b20b24120a0070081083d201150701d40d8485a4010014644050444ac07880c02810154900d0203130115000b603616400000d06032000d0070140920b0709070b600740c828601d8040d410240001408206c0605000c0c11746800e01c1d501c00c601c4000d4002a0003040745240801185807a0b0a0001d00d50344640280d601540300031002c42c030134610001c110b0380c410509001811548035007000007001c66000140c2842d43d114550450b030982d08085044444500540c0300c101e0b501c018a26040548141e240d0004082c5442d11000b00b225000110403030306800da040742d0004400011100346503229001462000e5644601c800110320942502c0c025030285001c1d1b2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 409258911 1250 409257661 409257713
    0x8030702030936070c0b130501020c060a0e010218060904060306020a0e040b0d03020601050105070821160c0b130f0b15130e0d11010e060a02040f061409060319020304 73
    0x2840a0a2070907068980340c00090021051720302148840920a4100d5014204d002c507002441d191a42660065544440c1c0307508240e0501036200d02394840c0c0d083c000920310007542000c40f48211a401c070307075000e880c49004480011340c01c070503569590301c14805194001411921036824120040600178a442603500841c508a9a1045403420040b00d440d030b194140d0040945a0a16004503101d42140341c080b5040c0c3c00901190f20100300c41c2c0412610000c0a14681d001850020b0341001c01c3c00080103010b05101410400300b0100f00141d004a502040e1030380c45107070481c824034000c4607018003050060440c0e80040144842c100003500300c15046101190300070700020703a0050380030445190b9100b4030426880904100d0000e03005d03202401064101000000780340d415003000604100e000c82d21303820301e2640010244504a40450b000700500030a14080b645c00790358810120035485034080541c40b40d180407002482d81844860802c01031a00c2d40c00c00c3d9120b00349480c0600000c2c18494500c12186010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 409260161 1250 409258911 409258999
    0x6061e12150902011103040806070e060a0e09090309090a09020405010503063105062701060b070f0602090307090501180209060a0e0312121e01080307080307020309 72
    0x160300ea45510541003000041400d00358040308000704a6900120b040c00040e0345003100700359003803010340014582480a00f04500d03044800401074812140003070300c01d007014051044030395408050004070303003403d0340c4040080d10b038100f00368554000e10060350340c06071483d001c00a000741582c0250008034820746d004c0c4002c2e601d81c1c01701034444000700c40030060701a64032454034404960350141040641d41a0303c3d001c00131145e4075481d0414400b140c1c41c0b00c161042d00e4070350315100c0800c2e0680721a85280c4000304070301400c24821010521400c1c0014041c0080243d814060040380d80c122100640020221780c1116503542c1843d0140500b4400c40a94403150b86e09100300c04654002c88003000300040981d0b00d0800c00c0303c01521406040444140c043c80b0b201040701261041d00c00030000703200c40d240c0b910882e02d0106080d00e20030b200ea048040743d00d1500d00c010440101c000043d9504980d210302c2c20740d16030342d904c60200d14600540c840c00313a0007089500840d88108400d1014442846c43ca2000f0f0900d00c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 409261411 1250 409260161 409260179
    0x1090605090408070204020d050727060f0507050f030a1808030f0a0c060f050a0b12160302060a03020d0603141005010b0f0706020c030c031312030f0e0d06061e 70
    0x94410150090960000240007881403001440110320040c40141403054001032241140c8044880030082121050f504603030700c008500340c506145035404020801814508001c1800c6007261030a814048081940420080f0070701402d1a04128401220340351003901c2c03030061503c0f1342d400502d00c55440340b02001c505c00380d0104c1280c601c0800d6404241c80e1001c4444d00b1107000e0000041038950981d41d1a0140d140209802a54090752083e4400310386c01e01404100b08500c51900e1140130240d0110145415040d582240c480c100c9404440d4161648055034003640684140301a08603000c2c6400030100821804881e44194810700100701c03400740c500141104100d038420300075250140703414003c040b0040404001440d2544c81603001604081c1009011450341c1c010102c501100d80010031404840c00d25041e03003c00402c204070300b009142c5020744000d800c0c0101501c042c1d04000182c2c600e44500e44515007040707c13859000400700040c035500d2004981e07800001c0314101031003202600000e00d00d02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 409262661 1250 409261411 409261421
    0xa020403030905100201140f0a0e06190c050c0a29102d0e2d0a0203070c021201090b06061c0e0106030c080c010207120515100902130e0109 61
    0x68582ca45003006401d0008000625080c025990304644d261a07103a0110900300d00f02c070340244400280383d8035900b410308078a02511404041c0004940c8010100000c400b03a0b00410212025403082c00902454030380b400320f5041c86010b5164459104a000010801081c010007080d1420325131703075442c1c03980c0c0c8609400b00c2d0380c401134417248100e4400600502c043e40d0001a107a4016214240210b1651a181031800d0f44620303e600203d100f04443c800c02c02004200b403081c00c51240d000c00c11841043d4210700c200412040078000b8a501079020000401081c0604628802550020801810154005041c50107882c028804460a14100b03021881724241401a00d8402d0700c4108200f1032000d8000d031101c0105004505040550748680c400004980ca2841c8107000d0140b0101420201c00000c00191910300a540b00a5201d08601c0ca0400881c8022501e0481580c0c0d661800c0b001d515001701c6400808460b80041000c940700260750041100784050070412101d0426283c6c0490b85d0710b20500c02260 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 409263911 1250 409262661 409262663
    0x703020a0c020111031c06030606090b030613170309160608190f020f0316020c01020303012102030c0310020c070807060c080a02011806060501080a150b0d0e160302090a020403 77
    0x4039507001c40001580144126440d80e00c3c1d003401c0b82d0801071102c0740b0001e409014501340100e19074820080c0184203045c00b602000d0300e4a810184032400c50700c80860303a284001041c3c86001e651600004c0c0400102c0000c401030812000c14043d101d0030443c00700d0382c0f034070070304400302c4000c2c20a107030300044190003000c0b598422001c0405040e8821300c07800c2404040c15030003a14101e155400c0003807140c0c54800c4400340d4051440000200e034243c181c0070300640341c0350103007451381c0c15940240010041c01c4075020865a00b000c0e8903524046080607807001c646450040707000c0a034140140c1d600c6840d030b04081c8ccc1c0a05514000507085904072036513544030316111680750043e0740018501689000214113450b00602c8000d070b40d03200001740704400e002c54000405207001d0440341c1e00d8441004208030369003c4039058100740200000c000c0c0b10450700b15030100216a01ca00d024108002c0f501c1580750b80340394021954215640141c40f0105994840620030b607900e400300300e2040446501003602c0d03014500c00d940540b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 409265161 1250 409263911 409263917
    0x150e06030106030203101841031803010b03011109042d02130f0602030a030c0806011d0102071814070c05060609040c0909050d030605010c081218240703020a 69
    0x1072040d012140c014103580c441f21100c80c02ca050760000000c06904c030107080280c4483c2d4000010100080c0c80d8000d5901e15418003024400214419600c40d000c0112070303a041e01c600e400d0b07400d40e04440200707001d8000008413036415460007802a054a44a00040c5071881d0211002c0008003948220140d42d2018803081040041a8401c1004040b00550060202c1c03411801113003101c0f40d40d100040844041c03600400016000840c0e141181d03a01400380c090b8550260600810790702d04100000c0c16040411801c0310500004054038081364000d12014000c0c18004402c407841e100000803507009415024800c8402c580c0d80300c0007038a0035100301131040d0704a0340701010700407a80781c002c1088419040504161201005094001180380755817080481c00f41c421406230084541040e000340c102c50703c56002c5d0341400301100041c00069410421036111078101803c2d1295038680f00c1c5000e510300451140d400c100e200b00740050204030f0551454a01e00345282fa0a640103644041040301640507062652000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 409266411 1250 409265161 409265173
    0xc0504030209130b18070f120b0403030204120309080c0a06080a0e24060108010e190203130f0503070b0c0f09060306033d0c090b1804150e06030106030203 68
    0x42c54901c2d582c5400206515420306442481d8840340e01d4000140c50004105518141c6072607401c10501140d0010818a0000b01c0301610b8481085085984000700a024204200010b801c0500aa050b540070700200804104441098540030b030940305640a4696a4812402e8154041c07518603004000e682c030310b68a0482c9903e0300002d01c4042c20b0b580d45000c00301d0280c00810301c60200306803808500010000b0308221981440d0001414003c010380041c0302207201c9274204010301c89019002801c40c100c4a00050380da03510740000001c040003201c402000840442402000e0010010161120502a00185c40651600d000440c0346104100c480304041d034051003e84d401d403070030001940d8000009001ea80408a42201003407401c001402000242d005921203400c9500c04041c944150301340d000400c01c8110107441c40540f9501c2c19208504482c68000359041030840980042d0b400824090802c2c030840071080003409040c210380c0102c407680e002040000b0302900d4140150411a03030080d000d40a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 409267661 1250 409266411 409266413
    0x515031219120908030403050414040605061914043f06180b0c040f05030a0206090f0303071202100b041808030c071707020906310603120c0203010c02010c050403 71
    0x3a0512420740300b880c440d40d602a441c01003081071005611a5200c0c1d61440d64560500041501c1c9a40301c920450040c0e240020910146c0c4404084420012855400d10300c111203c407021181d01000b07045042440320080740000c0c4081e04a50058071802408801c0803000086215503403800914038645052086950700c1e03c004034103203600400c0003600071504880c5840e4a5240c0300c0261300c040d16024106400040c0801800070315541d903101400045020b04441515500000d00501850880b9072041050b5103003200c10380c0d010021030703ca480d404000144640742100d0080c0d200c1280039003142e5110f0515000350b0480ca4076128460b41c04035203001841c2080d90584850341c050b04020240c030305902d01001802c0110320740c0140007450141055009586910381d2040c841c20341000b0b42020700610100300e04a0030740c00c3d400e00d107055812181c4031a09090355407030302c0800035012950010b0b000c081001d40c602c105a5000c11680352032402a0024050302603d000301701c1c202c9089800b014009481804184 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 409268911 1250 409267661 409267667
    0x302070b0d02160f06050a09030c020603180d0e03070e0f0a0c0e03100504060c050738070e010801080d0e12010f050c12060406030308010b03040c090515031219 70
    0x4044a40d5102006003010510b9803415840f00c0740e48819903492401d62661010442c683c0106035202030040014002c500250703a000d002c44460510091150102000207a440404a04442d5802c2c400208032501c1c0013548001901004100c0303121800790180c540041402040c100c1964000c2c88011b01d0a00d1b503642c0c5581010082c0505070042e0304000307092001d40659034040000c2c03400400f107110000303514101460100102c4159900704d105200b000d200c844080f0343c1d18881c0c0030f071441002c855199000c08d0658160f0f15280c900403800c41040c400001e000c202940302e84450707104182038031002c0c4566280d441459503100c0c0c00c520320300002c4200d200302a00342060141c5002d414124000416209400d9001d40d0590314100c1d113088065101291035050a0100d105090f0000302c280d400f00942821514002c1590505002e003914503071780040814100000e80002070300600d4010010030450a00c444c0a030180304104410703e04c03911544080101c0414040300315002e0044510040c40c0c1e15070159000c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 409270161 1250 409268911 409268917
    0x70614190c140d0c03090506091614060912010b04140405011404020609010320071119080c0f01051c0203180303130b0402060706062402030310090b1c050c0f030a0302070b 75
    0x70408141d106c44600e40019401c100380750241000e940a4990360002c402e10b104001c1099200c0c400120102d00e10031001d0312a02d08440c995501038030ba040071000980c003290301610f10782810796009450180c040c503030840342c5802c60f8040e078419402440441100242a5001d49090702c0c0a503114004001d20f40044d030203540b010102d00c0c02c0125180e400c841319621945260000c1500b03446127030140c400340c10540341484c4044908200008100451424596904d60f625401003803075001303583c2c000700740100ba07000700e05070b403000c182d28000094078a441c50006070181d0010794140241c01a1403050f4140580040180c900c01e040b00d4080210107407651316070044482010304103076040741c81004503802040c2e4074019413000d00450849013005c0c49201c004100d815034215404011900141700340710409a0104103079080700c00c40b0b90017142c202c035400000b450314803c500a0420b8004c039041c0740c8080220104900400150403180ca412204036041410745491292100800581221600b840071f60052406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 409271411 1250 409270161 409270181
    0x60e0c180a061806080c01090e072d0c060c030b180a0b090901060e06060c030306130608030d090b010b0705070611030403020d051c0504050a0b070614190c140d 70
    0x4042003255490044030000e03c00c580700c2825094860209001400040000c07803016002840d1200c04546070011031495040050456002c21082009100c800025501c5184000d16441c00c44510001c14020143c0311468007001102c00364140056452218000d00c2201c980a41c060030300d030101c92207407444140fa030354005d08803150155160765480d281d03281c080c0c0e02403048001c200006809410300b102584007080081100e4420350081282d800241000b100380d9811640603a0400b0420f140315000f0f00291200b074210464510000c10b4016440b6810742006912900500e80300c000d590f200c0610101c50720805001500a502418040003100c0c03164000c5540d00f502241543c2c10706032640d0014100e81a1000103950551081e030040c409400b00401d800080000303070801c1480e0501c0c0401040c000c1040384202e26024070003140340c4e810700c0315035001158500800600407526203400161400350482104c04440c0103032404075803110b154042c2c035840030180a06c0340401e04061907800ea80018100c1a10303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 409272661 1250 409271411 409271431
    0x315031b030f0c0612020a0509090402130509010b090a02090f10170a0504020117060a05060901090906060305010f140607080c0a0506010b09121605010f020f0607020a060e0c18 77
    0x6001000c9108081c840c88454452021107105504c1c12100a100c0c82403811181d60051041022000d2140c008044039103201041e1011b201275511400060480391096016007034242c100406c00040c0345040d4025944001d040321848103039103800f4011000c9004243d400e0b60058401015014a4504060a00a070400c07511780318030403100c80c03c414105d408040e00d500404588400c01d1004540c0c20007030980d4490610141444945482e600007404a80b040c420b07140940000200c0d52000d9100b4110500509055182444015900c1800031b004007400d1080e646106a0020045000010301c00300d0446400002c2100c0c2c1040c82c1a1a503107050b0340585000200b0303109124604001030b0042c040c40c0d001b40319801a945d11129500144036403d4030260321440d80780c104000030b0484d00e940c40800070644e1428a00210302a140310b10907031805188800e452011300c1540704102c5000d9002850f001440d104d41c01c20301c243c56181c84800c0e07a410849024a0b071260a140840c0000d11f103402090350312905110b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 409273911 1250 409272661 409272713
    0x3010b0d0b0307081603030e0108060306070e010c0c0e0720070b0a03092909030c0a080a020106051504030204060e0906130203030904021308010501051503132102030307030c031503 79
    0x78440e03c5c0920380c035500030f2018160f203801c01c02d25030080307101c0c8a030034000e00301062145000000a03482c1c0100401d1141400203d4008108991040740d1405242d5849240c1c554602d484440d40408950300300e8000d40040d00340200742041e1750034800c90140740c4080c10000d01040d4201186844180c201e117485c0410541e130340d01800c0110304555600f18440c8142e451042c48070030a000c0c0040b45c414024801706940c0c1c02000010359604002441403000c5400140080e1100710804040740582801c0e4070899001c40d11500d00c4d580c01818800501c12680b0803241049045c0e55420050340000301151300360b5168002c20005076200a22004e50540c7d684000c090740c1c6130441e50340010b001c90700300c1e00404800300f0912000b030003411800d124a50150a00700d07022154991144040c68061000030409400301d8441685074080080c5450184900c1e4110442890320715101c80c8000c0d03598004403424000641004a83d0074240d000307104107000c4114000f40300300c0366425034903101c01e0200603504c2401200c200c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 409275161 1250 409273911 409273919
    0x1202180109020309010509010612150204030204060e0a0c031b12110f1e03060d15020f030f06190b1909050a061808060709050906210304091103010b0d0b0307 69
    0x8910250203441d11060040c1c0380c0c103002c28070908550000741071180e903070301d8090248003000e001c520640c042075111401c03108540342014400060700680d40300a4002d403d110f000708000c405d00d04554032510404408001c4094a0741c0c00301c090392400c95103200311208ad540c2100c400b910601d04400c806004100105120000c02d68182072948500c20901d003921000c111504070003400c0d41c0044d8a03440d035808103030550620b24005015102003420080c00d140a110002e0503241c1290144c1e600016910000364403860000c2081032640c6085400d58031076110311051b000841c1c0119903410607541c0c141e805c1e908001080100c80044c072050781022090280882c0001103950340c005103040a0300345640c4100c2c480302101d041c54541e44060300300d040682c0241c01040400390780041514102c440840303680b812074491201080e00008901c813005145111002c08216000d80000100100c520a840070880001d845940e44031a001c2800341d0b002140c01001500341000e80354020350314101e4010300b40d851555903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 409276411 1250 409275161 409275199
    0x524030c0a0806061011190201020a053003190209060403060608030909011a07060b0a0b0a170105030a0203100b010e030a050114010e070c1401020f0c03091309020a1202 74
    0x5240d100502d55440b4108001c02d80c10416501c0442940b94104801c2c0000c4c4201c006803a001c5129030f02d0014440c0c403009100b503a10810500e69180c1d00402500c1149071003100405000551802c0344441008c140e6885542c54200e004907480b41c00d82e40303602201d070541300545201950040302c20a03071001042c000440400c01ca40f20303000040c07584100a40ea18200703030061020881050740590707000d1502c980f0b11404540400700f03c490507035000740c000410410318400220042c45540041c4003075100404d44007501908182c00c0b48d4041510008041c507030780c1e07610425036511400340000b074040c3c05c0107400741810152038015000e00d04050401356010086e02000c00c0ca0300c1c80f03a001c26036142c3c2d140c3c2c00441c02805c0380b10003140948003080c1c0040300da2a100c00c010388540f0421100418982600741c1703030840043c0030350684070054401281c0a0f5900b0403103507425503079001201450f103e041d800f285100400c031715204090b4007075405854501e2540c582400700300c200780da107141a604541c0440c2030b8001140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 409277661 1250 409276411 409276429
    0x4030e1318050607050301030f11010212040b0a0e090603120d02040803210604052707091b02010f0204050a0b0d020408010903032309060a0f18240524030c 68
    0x16031035814100650080c240b2500d041d5028042d0410710100b0401400402c59030b89481d401c035500f00640001c02520840101e00e0100709a03540003402d4408503010440810381401040700a0003903175005400c480c1030003044500d500960740a1341c154400d0070503001450420001e8042d44c1c0c40d0742401810140c1d5a203607203040d9400009407000c41d0b042d03115048000c007030202c44e0503045501a01c0c1085603281c440040b01c2480f98402040c0d48682429051240b4aa000c0104001415072120300340142001442400f03500b451031255900954242095104012503500c05c1d242100c80062034207511503d02850180140e1003041707190722803a02000003041c101402d0090881075071196400046007100d1170751071115024090004640082401e00380845407000040030340e0400145040000c910003542d000d080104141c011810341e8608030812030050011f800340e45808291001d02071009101d00f2044c44044170000c075541c0c0c1c21442503850401400301c182e401e404081c00f0203402c481d03082800d4000569000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 409278911 1250 409277661 409277681
    0x1e03020303010614040803040303120902030f0609070e061f05070803010e060f0619031d060f010305010c1110021809040b0a0f0209010207030230030a08060109060804030e13 76
    0x40d1000004004065102020050303001d01c41c0c190905190400c220a84c6a106510018040282d2030b004103500321315940c4080000c590007821100c2060100300d040e40c4070042280d2aa40a0190341c00010b41c1204222006e881458028040c20300c070150000382c005500c03031003880307002000700038405030b00010380c900000e60207000b24140d600801d01d40720007000b001e039021040c5036000f0082070001001c0c98201c1e0032400282c0c60182404684203849210003c0c042c026040081303641d1241c0020300105e0380065000c0c0b8180e902400c020f000301c0f100d08074151030308111848004010742c07002c1106000d80c1a15800b60100800003440000f001c40d8400000340d800d41e0a4505845208005d001c0c0700342c5035184d04c10140f40102140d07042d403c0580c0b02d40080d45814881c400a8001d80ea081d40703c2a02e000f90004001003003032803404100190764011191641c0350003c1a50002040079100071989079030040c40c030f64046400560340c08009540d42c0c2c1e000c40300700d11011b1600b5000080510000081e08a40c05581012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 409280161 1250 409278911 409278913
    0x6090513140c131a090d1e0318050d08030a02031509070509090603070b0720061c0b060721020a1509030e0d020d02150c0706080124020c0d1e0302 64
    0x2200810480f040c2c0001c15400a4101120800400c240d1485039090300e05140003154608650b0201d401d2012035400c044084500744e540001d90380c2c04054208002d203500c1c11000d081c189140391201c09002c0008c10b0341001038804882400000c102180340c5e0000c0d5400701e44080da01040c0e11042c00480c80100c0d050710f0500c0865400300e61271101d0704110f1040c580c0810210001c0200070b2404405044a104019000c4c1c03140d06d81541c1c0c00c210031b20749041d0550412024010303d585c1d40040c81040c2c0c58141030001d0004403420700c00d0b0320902c1e10380369060f80c0c41150484490b04450078020340d16540040b080b18030800b5402059955004a105450f407400030100421011440003403500e802402c4855004529101d00041043c5c0e8001d61550300400d80d1003030303040c1e595842441c40b400c070307a48441c0144000c4038000c0c46545008690a40e114032594100c40001ca4170110b103000c0003c0e401c4400844008801c010b0380008405a1145800d2482e87c0005000b41e4a0700030f51010103103440e60740d0340d07444026005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 409281411 1250 409280161 409280167
    0xb1b03040b07080d2d140f2a070606050a0807053a2004110f070320010605010e0d0b07140904060308121b0a0305040303022a0606030706090513140c 65
    0x5218664020301b0701c0c0080b80000890300b1318120401030648200903000e010024220042030660b103115101c0c4540021210b0b14494483c100c0c0d00c0c040000e00031070b0181038021140c0940000c0e010030300080c00802c0d075030010422100096440c080000310f841102501c01d052200040d034a03d00b07680b2104203440a03000e94410a110b07800708140c5003d80c90084044c5025a2a02e61005181d100c440113036020f00c00e9207106981e503801e440c2000c41d0481061901c94440c01c103503103011041400b055200030110b074000c2e21044c0088126900f080b01d5030412590240c0302d5010b003c001103280d48500110486c2c01c0143d207600c2e08060094002c9002c4442603002100d01c01c800140e144461107201111039400400e44642035078046c400f108035400c0c0d000d480500c00c103064441011504060281c1c054417088410000c00c008040d403038400f4102c0c80d440140601840b8080c0708007013100b60602003040c809480c2c00307444818410740341c441404030407081c1c558207078052581da40501d13110400e00c90001d070084220b0442c0c03940b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 409282661 1250 409281411 409281491
    0x2061c050a050105011b020405070908060118110412110102190503030f0c0705030f090a03120c030f1115040f0f140c040903080601030b010c05010203010b1b03040b07080d 75
    0x4842c0180c0000d814082c6004a804181c0018090802490340c103850200d000d4403110810380b5401820707004910340d40185400070640c2091424215999080d483c000e11519081e1030003801d0300d1085004281e030120f8201481804a40358130094003508506104441c4211401c030083c0e900704c0a5400200c0300d6030000402d010100941001da25048081581c015140410b01e964080d560301c500900446d1030800032519040130703641c49460400454110f15201000e403449030b001885000005011401f040c0c0600c0784102c1d071807151000419611402009201d0854000300c280c850b01c0001f4012607120b41e1640103903000035803070510904954420300340c9003440f40c1c01c03070003444c280b14503140501d000d00d02d42501480030035844091240c000401b030030005850454100100c464245500c0c01078080e60000000041180514004184201123107030b40146012940702a161170b40b0607445002c443d058148410000304007108014214040c1c0c040c000554401d0075103c1d000900d08274145c030240c00401048501c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 409283911 1250 409282661 409282681
    0x919091d07080d1b051606030204031401050c0405040b040b0616120327030c0b01081b0105070c0303030b130507020c09090c1008130b0c040521070b0702061c05 70
    0x30082c02d200c40103000290415400105441034000c4038000d80f103a64041034060201c01e00c000c11401d1414440e40c80100d4540e680580694024407040b60803501d60078040c0c26941c4184943c030b00030341c40480c1c942c0c946898101000045c1c0740d07046003203502a988100ca0b884590345d9100a040d12141d45006120480103401c02d0701d0742401a09030350702072604000b10048072401802c1d201801041d002c0899046c1c00c81400d0442c0c280c0003507080140348425840000c210004000f079544200c00048150024804201d4011100790046800003092603100d0002400020302039080fa0580c071101401c02d81e58580706442c0c203c141c0d8030030348400c0c016030407a459910315418150542c9602c004410f005010303d100c02004100f07800714404110040008400100d0720114602443d440042d401944500050a103142e4160f4030340e02074842c80340b00c1c120000da40256214562800c04081c800c00025155440c0740c0782d041c0490754030041040364002070811186003c8940e1000030188101404000076103460080c09003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 409285161 1250 409283911 409283923
    0x20f16030c0b0f221e080705031f0f180309030309050402120a0906020f0c010e07090e030a030e010b0d05100501090e100b030f0d08100e0c0919091d 65
    0x18080580b00f04203440440b51581c0c115003544690380300100c10121810b642c182494040d400611140228903105480f00c0226040c90301511a010150380f1000d9a070130406596080f00342242c044581d101c2c45100f40c40b10f050307010a0350b140d5610750224042500344442c5c0a10000b40504801080651005006140d444151500500700036a4114030780010303000a10014000104002c00094854041d401000415010350340c050b2009250746d0744425001014070b01030301c00e012000d4018421154001089951801303001500840c2d42c010310316000701707000300b200a400c442c180764107150340783d00b07024101d074a0300c1c10720090150150300640030b80380c4035070b00150a40c1c0069200e40707005030408242c03481c10403021607803010031000c951002880401000c0802d0410080703e120940900540b1130000100d500901c45600c941c80e0111401801a242c4c1204a1902800d40f4142c624903010304c8400d0f29828110841c0d1516000c040c0c0320443c0c980d030303080c2d924240c454251101454000c4072180840c01402003180d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 409286411 1250 409285161 409285169
    0xe03032503051015030f06090204031a1006180e0708091c0e0105070f0f05010522051c03200c0d020105010302090c160f05330c0307020f16030c 63
    0xb031102c0e04000034850307800d900354080d50b003d00740e524131a070200d01e019600c0440c0c28505900103101140d625015040250020303c000da44281c04148680540701c074181c600707440341c442e000e009100c05060403021100381031a965040c510480001c4003096480702102994422921a0380d000b04615001c8842c0b82040d5107070090031030b40c10718034034000302164102100941c0c24501f86070094075a5094100403405010400d0051f00d10f003ca244060300344001902710b60b11540c20950a185084044400001d6000f88002e01410303e80000e04400c503c12400c1810a4012442e441c1c00f103181482003c140b007107060040c10140c2e015034001003100c045002440348600c031411600003001b82e58510f4010403e095002032880965010004684101000004210131490307044030044540c0d51051030160350b202243d882d010060101581c0c40200c0b0503076002010714070384c080f4405c0e100c1070b143c030407124043c0e803c0500000154040d1000351000340c0c204114609680700350f038030b50140b03152650030042e540c0341250b00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 409287661 1250 409286411 409286417
    0x8030408280915051606090b1807030b0a0219030501032603010909021915171504090312090c0302091602030418060f090213050301230a0e030325 64
    0xc01c1100349a0058445800c4507240308188900c2c900b4030f40c04584610640c10f03a2404984451052024081c1d294440d142040c850045a4941d4030340d0080014040002e02d10580b540d84005010701c00074221001c0a030300140b20300c0001d420a200e1120742d08032240e82d60308010000355100010028481502d0380d8034110825024840c0d00c56401800e000700d184014054201c0785a1101001d1045440d40800c92910340c140c85406640d82e602c0c1c402d800b1001410703600d81000a00071002c00a15040c40882280c041c04440c00754140c3c0c56114818040504801034041c0c00b4000e684000d51a554a00d00810703102c644202d03011042c941c00c510403c464440050841b10340058081a404102c54001080300c09031488101e6450f100440541154068500b9402c50914880001c20000f8402e25035000b4007640191045041a0252100300f811300f20344200305900040000f40c0034545085400500341a08401e41940c046607040000d02824a10340c0217540500482e100d135541d41c1c440c0c107942c0755030351004005c41c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 409288911 1250 409287661 409287727
    0x1080303090105150609042004030b010e0c090a050f01090e090a15051608090109050313060f02010b091503010e06010303021507020606150c01020c0610050a09110301140d08030408 79
    0x5010805e180078091005019a80d03440a94400c400040311040d910704400701170a40e41d544038500318807a40c20030320420030364034004d03004950f101c0f501c003080d200800c2c1c01a1000c0000351078041000f030407a18022001f418444050804107140200c80c0200707114010784002440309440c1d40c603044010708030703502150302214501010701c078401040410160080c00c0301c0c5013000203515020103080c0144404240144188400248500d1441021100e6000c03181c00e61511248452907a00c140e00346e400b2018060340c0450f140c00010a00366484030104080c00d0040c0c0009070300000d031404140340c08800e820030f41c056800f107a0300d03400c072030808840c0c940c0c46012031020f8111030820b000446d0903042035484140c5003180100f51340e542e104c0254140d03400b07089a00b00315802030504c007003141900e400d24011940240c0c582540070401d19054081d68070070381450520681b86030302e0700711048001d036200822a5440107000c50020f0108101078003550040f80503a40d01941c07a001401d44080720305802503186040489a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 409290161 1250 409288911 409288951
    0x509030303010902030601120c0207050a08060714032208120c071203050a090b071e02010b010804020d0309033c02031906150306051b1c0c0504090501080303090105 72
    0x300689045890341040035840c0d80f80c480060b114003422800b6820402e02e0069441c02c100c0e40091000102c9800703a549843c016181c0202c0364494104031307038900110320100800c550402c1080f004507448050021561400030f502a0940030015441009640c071940201d62140c07500a0108041d401c903032003001003854101903946060584000f01540000d05a541c0006002d00a080d0007050311140d200036520240d1400100283c81042061400000441c010101c00d0696005100e030380c203840416100d03c43c0030340d41c5070308001c6000c0d0502c10880803c20012400000078843c03030004215884d40000c20707008141c10360720180344001040070102401c078069104401584000c03c82c921400c07e54145a00007a000d400e103400a400c0c88400c034050842c58400000c20b0000301e03404580606d076841d5071035100141d40014005903024000681240d82120386000481000c2a4400207104400f0b0402505107941e6122420403034900740d00c6040240c0000080100c0780400307204903984403402a004e0002140b00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 409291411 1250 409290161 409290163
    0x130c02060a0507031116060b040b0d0f020a09020307021b0a050f010c111002030c01290607110a06030b09130c140607020d030306030b0c030c03041113110a020c01050903 74
    0x190004001ca5640d0000c91085446a0083c41404590100c003e81d5454940c0c82d044001a800300140c030000c0c07070105904507600e0301d8040c807508407900038244098402d09481b29403040f01c2c4000300700e038481e514100009085009001441c420516074004d001da0b94850440e90808084102c8840d104880881d001d10007130350b802c0c44441ca00c1d8001e01e013940c5024503600d0414900b4400246180c0c0c00610341190742d004550000084c00f40f0035070b6130001d200006035030107040c0c00617001d020301c0c45840d0410903511a0600b000000307002c03540d004448080e044022040842c0300d420947d000100002d0301c5400702c1c40713103003441407140303800400245c190041e402d0280c850b07104282d102d000300420840041d4600019581c0c40c810b03100d07560f8004203c0c000c4001186030103001080700c0d01c07080b42c107450314500280f182c42e42402030700d1040b2480c81c0c40c50f2a40d500c80e540c004000c5100c061300ca40c00300401040b540400c286118088009610482841d907400b00c200c4041c0c584403040e43c1d5103040040c10440b010164130 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 409292661 1250 409291411 409291423
    0x1b0f020d05070609020915012309062214010f021c1202070c1e0807031109060103110703080910020906300405010204181107030c030516050c130c02 65
    0x10315241c826200c030320354035001c40a46242c0c24003a60000c4241d080c00f600751260f5001031100c06090700e403402000414506054030880100780302a181400713200d140440d09140c001085800f0060300301c068241490b031400c05000d0840c1c1c10148000c100c40501c643c6558004114500e801242c0c002060f5140c3d07210010348280e821300c01c11000f0000b401e541402c560f6880c0d01515a0154042c0c0e11105481d240c2040c0d501500030007084003180452040001181c01001c10f00d003003070341c1c1c0100c1200700609050f410701c00d15810180c8960f042540d2508807400c5440800040c102c00c1e4402d5441121506110032103504e0b0076400305c5020310182c410068015683d440300d0855047c1d0742502c0214101180504881c5e0741b06000c80103030240001501c2c00c000400c08113500800541d001400c070042c4209240b4141022500c01c0340111962490030051000428010300c030141a1510900c0c00301e1900380d10b070307909d6406a4040d240841d2507030b124a200045625081080512030f02c0c8a074001c10000e0540c0e030300255520 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 409293911 1250 409292661 409292683
    0xc15020a12020c0a020118091a0f010512180a080304120f03060810090501020915130b120a0510053309060a05130302031b010206100b030a0f0209040608011b0f02 71
    0x12a80141c7c01c8640c14680d5040c900521411404004030111415100006107041d0f090030f2103103035210b551061660080042e9020f6181c8580a0855039450f207001c0311031340c0855030a40c0442d115003914030b800100e40364020340c8118803c4d80d407215012800c1e0005020902800400003e050624505102d941b20000703201c45107a0260a0200c0c4807019410924028490106125040803688162444039640c00004290703078007201c0102c0c40b4885c0d0b28011402c8502907509620206030340000030035192807450304015000640c07100381008150342c400000f2001100086100c142402642e580800c1c48150b00031480313540c0804200c1071810200707000065947c407802170504c2c00d00c0000b15240e11041454041c0001a69024045a416054148200d810396140c890391500501c03806c0002198001c000344071100300d50703c5c0c246450440d202d020700c501c0503040d58011081c0050342030140b0841940c0701e0103484000c021340000010000c0040c01c00648190045101d80c041c0003100d0318191099a0008406d0a68 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 409295161 1250 409293911 409293917
    0xe0f060d020f1b0a05070905090c01030b040f0c030e0c0109081207031707050301090b1c030305130c030f0303140f0f0c0405031533100c15020a12020c0a0201 69
    0x16048514114805000c0e0680d1141070508410300c2c1c4825400000302c40800174021800c0710507007076a8180450070b607a41100c081c1c1c0581c0005662905650198004400c5454020310105004009103042030848a1400110340043c2d120300355152900c01c01d00c0301400c0c4103020728110120a042085460341c07980c0c00340c4103240d1114001001c005142c03107442480a1101d00022881031400d004c540200142c0083c02244502458801da5640c10305d056059001e261268112003554500c43d07440030380050600804104456440c041c5040004030a501e0220140d48a070035580c10520325414010111505915050700d010241e03001d00c5400e02d088140c141d07000a0120764012180e4410b528201d840c0a941e00407a018803982e00d131207000c2050451002d1043c00c079000d01d10708000040394000b003c9211400480d20b030f002180145122030810458200f00d580ea0340c248440d20364140c0c8e4a061340b6902001510400540c04501a0a6545c1c001c0b58403501e501154029030414001111041d03e50024220003414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 409296411 1250 409295161 409295167
    0x4110a020a081308060a0209030723090703020d06120b090c010c06090302030f0c0a12090f1703092806090e0f063712170f04180603030e0f060d02 64
    0x4840c880078503004e04004001e48080d0300380106080c005c3c3d0061104a41319010361880866410034250b0024496540b4443c40d0032154421000c1c080000c42c080c2649041540800170740c0c41e040c181d400b07140024001150014055121402c0c0b00d4100d100103440280030b034011811035005a81d00104100301150403000015140c00d061800b40d00c0c5d0311802c010421200700c007040c407a59031400071500400550240341d008082c0340320b404c4225400701c040d006003a04a2200c0c03c00b400385d400c044000702c01522650b0100d030f20709070900c00003403d5a103075800f07136a2a00003501c200c802440c401040b070360018403140c02d1032003601b410301041002c41d00000f0040810120f1110002d0310341e0307032845200c0003003100e00718540d09080620340c8401291035003c04040c0998503c180000750681400c1d001d00d000d60380004484051000140803900345a00c000c2004050040500c8085015001503d11041000c002d01000844501e0352401905081741c00b42028401c110701000000315890342000ca030307800e054644005907 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 409297661 1250 409296411 409296427
    0xf110403031b05120304140607122d0617011a0909010227012303040b102711070203060105060f0d06030809011103070c120c0b0a0c0204110a020a08 65
    0x5480040b84001070b002d0300c10048000c601405030001540201e004e41000c0c03880100d20000913988002c04d445d0320000a840c220312809161165110918035000c200b0f02444ca11000802036001445069014070749982c0e913002040300c0403e0313004440d079011141000341300301c809407614155200c00c0d00c81c02c64020b220030400a00c1140c02035044860b100f9000700303000c40c20068241d2075001c946034805202c0c0031440340007105890001c080c2070b03c14519001e0b612540381d5a00c9a5911250382c002800e158102035006201041031800350747d03000c040e89a04014001001c0d0300444250980f070b0081c24641c801c910400ca0400540c40100b51141035801c265070300340c0d40303021710a030030300f001e00c1800c1d4009103a03460107801000304003165005200d01707442680e88a4518800d03030501c0d502c920600400a03d01d668001c000c100b9030481040c4181c41e9805841c0c04400750780d41d94512002680091012800a0404c0b849002149458030429582d00c2d404145035082170142c0340065500c440c105c3c8050800070700812802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 409298911 1250 409297661 409297697
    0x703121404090c020717070e0c0703020a14060a110903030a0e120a0f0b101203030504030315121b06020c01080411060a050406090503010c0f0509010905030f0708010f11040303 77
    0x50010718002d81c04000301800542c00a48665842c01080c0140000b900310018110002883e2401e40d50b124552440036100d0201c119040d40c04818218154010810310348086048400070700241c08101d40585454901040d45030200e0b82070840044064a0034003107081c2648000041d19905009411b140088144410004244085c0240903180500c684001d0504109210300c1c01040188104099121500c0d40c9034503c0c0c03061035038010b0b500380d810f00b444000c0c00b2910039009660803d0207401c1c0000ca04030b03840000c0d0400c0440360400048860542600410042000c0d07011016420040e0400c07121400e00800035162645148007074100100c62000c1000e04c001465204040034009000300d990700d0220303d01a10b00d0b0803520821000caa40c00c5000180b50034180a094040d040b240e941224103a48400295180e4001e221501c0c10030915800200d0151010440c09034010b401e0401017641a28140306c0a003940d6050030148115410b100c0101e03001d02c50802504c0650740d142c24400c00f40c1037500b03006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 409300161 1250 409298911 409298917
    0xe0904020f0a060507050105090c0d0b0a060518040210020a0308180f0a050d09060e0603060d1103060a1b050909040201050703110d0309330e0703020915040c0207031214 74
    0x96030149a4074030008a0a401c44c00410403d88900028402e581e02d40304540c0d25040c441102c0c0c0c0c0c00c6543c0c13521600010b5000c607000c660010100c4d0002520684600200720341c040c0c0002d0310031801980405000651400305200e080b1400984018504142c0aa800802210b00a0800c80c018a00207003050800f0744240003002204074002c0850b01d1781000c90510ba5a6044007260420102c0d40300c04000c200b251089200200300344014008038915100c140c28801c032586180001e80d8420b940c140c010980355400e2210034065184c0c541d0200308640380c58000241c41003101054024040200718400440e15001c60045e4020b409007840d0b03859140506068900620400300c1a42a001d0124600e11440c0c040c5d00c03226485000d0041c1100202e03006203003069094650a11815004000c100510080d400350003d4005400341001e0f603114036641d034007160030700000361020001c0c40c00d000760510f01402d042c440c224049529100070802135155445811500e20030b200303260100440c064039070074101c0740c2c0811 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 409301411 1250 409300161 409300189
    0x17090102070c17010f141509010f0e150409060506030606010c2d0b040506011a04030b060f030106171b090610051305153106120b06040e010f090c0e090402 68
    0x4148038161b402c204d11138540c42e08803a50280001c003810304e412541020340c81607068640484000010b00c2c1480c12400700345c240100340c0034000780788170300300360464481c2d006206003180300c7d150116450800000305810141c0c010040350400c1546006480810b10301e514546030000b03c0d40180c60040381c8144003241c0d000000901a03e0948030005002c1089000926203040303c0d03540320561485244050058001c0c410f034070020b019004d03c000450498901138030355822843d0020000078032643c2e1594448500da00b03860091407150400451800215001c3c46842c01000d4129440c090750b140850004401c0c10401340c602c4200080403c1c00444202078803e02d0018180041011241c2da1032200c007001c0580c4500046808107007000c142c1e4041010381e1441c80720000c1c00d001c0c08100309085c03100c2228000190100700e10500c1d1281046032581d210342e03000f003010380440c2240a1301c0c0d60402c0e0b144460752100c0e91042764423520304446480002c0e4440c1c0d0402d00d10f001125600784540303032070000440c0380c80e140c0d407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 409302661 1250 409301411 409301441
    0x1912020d0509030c0c01020105100e091609060602010e0d09030b070302160b092b1803080a091d060a0909052406010e0f03060c1b0304030317090102070c1701 69
    0x70500500d290004003034030080101404a0310314070000300c0128240c800070b4410024040c500c960511601c540041440e5001d03801408940300c0c099546a000c007541880d600c208420356842d101403003842d80c2806484901c40c03451006144000e181361009114801d640301c06081c0d81c003102d01089400b442178040303441802559040c3c84070aa00c6050012524070142ca100c2c0852143c644c00e404c1060800e0910300c0303010b0082c2002d224070018003d0a0304c000170341510369162144008004400108600050719102c0c003a0354501d0700b0941010100d00c0c080090500c60b42d0520700d44401c100c1156104c01180d070617500094004900982e451800501e007013404100c0f181408280c0c03210580c0102100441c0380700f280d00b640c031000c080700b014042c0700100d510480b03415050b42206c8006032520b180c0740014414400c1c004111890b0240c002000360454200360400c800041d024108104a034900341e07022a008240000210b00e0004582e4812240703034614440d1403c0e40382da1040c0c2003240c500a43c8840a6031070780c41 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 409303911 1250 409302661 409302671
    0x1030b09030d090503190827010902040e010b010e010824010509100c1104022a030910020309090a270809040f050f07020a0308071101090c0e0a050c1912020d 69
    0x3181c83d03a1031b0341080080b0314100d4031170030785019800e00c507800c40c1d8040d055078040702081600042d007903140c00e078240c003c51025640702c541080042e181d42c03281d02c0020941c3c00001500c01e01403000100302c1c036208d916960400441005120991011646c840707400041c0c050015142010080182c07868052450841e030301080c07600300000019082401e824a941c80703856140100010501004105e0059800c494903150a1180c0114010b404e54801d61000460a0440f0f003131034000d10024607005001c40c04c0c0801a00040303400d0b0039a0130050202030308007200110034480d2404a001e07651244111104c85048419901072440c14050840221800c007100500240658a9020300070006000f003604d403202e9078561000061a541d10100d1911000ca03456510325080c4d4407584001c0302d582070288000a002d541c0d90041c2c03800685a8600007004140502110701c0c0c625003640000b0854100600107000c6000030010800c4250480600c1e4a0b448050f051000e07501c00701c0c00450000f80143c0c800c00c42050701e89 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 409305161 1250 409303911 409303913
    0x60a0e0c0a0905090f190308040219030302070317040e06060714060709080f0a0803130809041802090702070b0301170718020712020109020a090c0e0d1104150302060301030b09030d09 80
    0x107403c181d106a4001003214041c2d1103c0350516a101101500a029904d801c289100001d200740130300d40e00640014084407607200020313a0301034054240c4d413044015902c03180c81003040040345a5010451108402d14030300b014605551004501001884c9502c1450300291104c10459031102113034140b00c010b8111041441e000e10090300d001d00500407210180b050f801d0500000304002030188580398400015402d548a12408900020303100c001203035803200501114440e921140f140c03500144044507030700c1c1e201e1514014482e003031b40c2c0505140308640202c0e006001c40b0f0344010803241154009414003c0c0d12000309907050130058140c0240a00d4510401c41034940d42664001e00030041c0101c07240203002c10956016401c0312030802c4025000448900104080503440d802046a240e40d401e00c0d810700104840040c44481c0c2c60319003101d840582c1103a029590505110340b02c02e040c2e00c81c44015000b429034000034058001488000e15518008001407000207060023682c1c803c000b03c940c00d06c904000d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 409306411 1250 409305161 409305179
    0x2060d022b1a030a2a0305060f010906051c030815150c0f0d08041112150a0c030c0c080c070f061d01080103030c061a06070809040e060405060a0e0c0a 66
    0x1410000c0742c18060340b61000a280350202e060410340e80e001c841d80f5032036254070401c528925071121038401620410000007011032024010b1a10035a1031004415466041401c041e04a42c0140c100600900c2c0681030018184a182c4540d11055010b0410380d05a5541c0314400c460b200010811542220003511b0208442030807801810928188601b516403160702d030400c0583d00c500441c0c0f4480043d2144011801107000241c503d01d450b100600f0302240040300c2645a45002004015540c0c1041c404042216000b0584501044091a45800d01c00c600d6848402070260f0351560014104080005406d101c0c010200400002410326908030512140c0d65080503011448541d02842c00001005410080d0343c40ba01c4201d042c1c1c0ea16844100d2520810780b1080004c1c03030140c103040110800c1308500e0034203642ea4070103032034401e00c5203604550301c8260700140010b6407080a441b801d01c1d0f0115050100082001c100b06030b00c100703600800124540c0784104640b0740010400c80d40c4c0c21061078103000c00e071a61 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 409307661 1250 409306411 409306421
    0xb1012060b15092101021b031b03031b13080d05030711010522110303030109020703030605041a06030a020f0304030804060c08040b070e0f120304031208010302060d022b 74
    0x1002c840203642e0410856240c1c0042c89041c0401c1e50080c0001c946a0080901c09600c1000c014410001414241b211010500c440d0200032006c00c994004030310481d14110b602e8001c04240c014001850550408400308000c0c1c030104001003010369800303e01120b0f008441d01120b03000b01000801c0300d480301c0446001804d00c0d841562020b001400f909442400104140035490141c4c800c0b015400001d03d5000d116211210000800c6940342c4400c0701c014010f603400c1010354081d1160480044c1c1d180d03034030300c3c01400300d400c150303c0b05018a080c0070706034620380d01a000c0c22080200a907107040d0740b942c0740c07440540284a00091810401d8010092005140e4810083c0e4400e5205090030040c051800b08141c42001c01101c0c0145128152000151640e10030084000102c201a085c0361040c0c6e88040000d00e5404900c41d04265035001150400c107004c105d843d0071048510354104111203505680100d071713940c492040c1c403445860300001c812801d01243d00c1e0710782c0c0308558170561200c285280968000509 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 409308911 1250 409307661 409307681
    0x60d0203101e0303030b03010b040501080303072604020f01110a0b0103020901080303240a080604051b100e220e0a0201020c01051c1104151106130b040b101206 70
    0x42000c180402c1c254008014484003202031000d040c0100e10b5990110041e21010751b1240e01035490f9070f02c040640d00c031409510f01070b158240286490b85040030300201441c2402603036000403020007100d4011030100a64881c0c00030b4041c0c5030201e0b451140001a40c0c648a5200181800d00c15481c2d460184818002d2040c1030301d2080768039140c0c0741d0741c843c0b24541c1c0e400190340070007805801e17410110004111525044541d040034000c40405580c1e00c514604002084501396050f0b0428160301050804a280c0017544150485031040044409040100b540b031100c48468050900700c100c4000108070480200c42c0320040320410f0007020100700c4007513210202404101d0243c480d01401030000c0d030080d010344983c2030410301030190100d1280500e4000e040701241c5e400c0884010040030031103d1112544642d14001500c98035030400e41d0070110391078540f0043c41c0c1d6020300c0c401544d42d40000c402050450700241c1200702d20403d500c070085424420910b076400008207500c4813941c0d108005058005030002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 409310161 1250 409308911 409308931
    0x2120a030e0906041104321c1103030c03210708010303080417030901020706060506160602310e1e0c0a140a0221030f0415090605040c05030606030115091a060d0203 72
    0x3e9400aa45152070040351f661080c1d018139540b01c5101401c0040000f444510700544003407660301c0074040482e04540c011005100340c3d8000142d42d103040c0d1126100701265052500c140c00c000e180406004020001c103000080030080d07440701003024440d42c112049072000591018981d681008034600c0d000354004241101c0c603a0500b50002194034020381900d8088402004800f031004036981e4080013903102180c0314420204000b242e01d44540064501115254142c440c204040d09141d2003081220000300104400a007021228140c0da01284916801100034400e10361a00c240c1d01080c2e85030350000c09044001034001c546074010a0740000c8444450406008010701d81c0d84008208010b844100c03885110580c0e2600420006124510524026902c1d042e0008100350596145016180140e03416140c50070515024801c80c6001d000e03a42d007080c4100c0080042c000da030800d20b000e5100c0c5210b074030708581d55070412025403040c40c810904027050091807107030343d1b00100c0728000003034100780c1301c1d4965 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 409311411 1250 409310161 409310219
    0x7060606050424120c090e070504031a040203150411190f0603110f070c03060e0a030f3f1e060b07050c06250c0302120a030e0906041104 60
    0x40901100c0d0056000e5a69641508080d0403008a50103004082038070300400011550010749120b031142d035903008048d5a0703221644ca5185d0708006400c03508413114140f921005400b07000061703070009096904002201c0c2c07003c85070784d12402c0c04a11501d030000e100f5044000250008090700d95506840147d0b064030509051043d11110201d04489000c081040c5105081041007103101070707140500101c0784a41854025241c07640d035a4002d86400b100c407c10154400340d00181010b800428000b13601c0c20901d4200910b18021442a220b90100b0008a0689202040e69041010900c40313402c41040b411105008002d00c458481c0780c021046444210ba26180504c0414510050340c2141e850301e400a00400504000c042001800c3e40030200401031803500e48802c140b035010b030f40e5680403200d0180d5007641c915451401403180ca100700c07014601840e040b016440300041d0b000040072072508410342d019032003560344402042c001d20244500b00170386c8102143c00190110b41400c0c80030100040d00b4071240d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 409312661 1250 409311411 409311449
    0x40902060d090f1e020310020f160f03091202090a050703021b070905060a0605030a0b1306090905060601140d09050c1c05150f010e04060b0a09060f0b090105071403070606060504 78
    0x310703d4104c40300a5268211090b014040081c40c0c002d040b15078003114200c1c0c44c081c00e81b6998240504035100072562034141c00700c40814075810001d090000d06d10742c010700ea010744096000407005540208501e034810f0361346000c540c51500c283e068a444040d14010328884070080c0c08490f031394050300d105483c00700c1d0074000000c80307070f0904000781803c48446032a10350460f140c0010040c0a81401003c00390040032495510900e040c081c06400010040b0001c002410b04d00c4d800c040e41001d6000f0901c6040c0f10400701c1001900c1109002c9a10f009481440014202c03603070302e4800d00b0000860355045e4443c031204034a891074651070004002c0103104104480c074048001450441344181103d01050316600f4800402ca0400c0380c0b10700650141c410200000d21101401c0054500003140e0003e08074a65180d4050007400145a0120003610a0440c103e00385032940d00003c00500c5902001403020040d4442807414003400c00680d800c45900403024064035468500007807894200d8481c5000c2400c0d00c040c105 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 409313911 1250 409312661 409312703
    0x11030316020301060f0503151302091e060a03030207050d020307090e0f060a090203100902060903010e0616021b040207030c1205120f0f0403050c121201050406050915040902060d090f 80
    0x45c040744c83c040d0203018010029592004000002084000c05030480c52510006a4400030020f200c0d2034182d00b40100200036510040300d00c00000e1010340520303103c1c1800c0c400f19400044200442e201114070b180040d038035102103801c110075a80048099428201c0c0b02811002c0400d8100b80c1181c20340417500a5507038003168500341c0320202030180d00764010200b10f42d03a900c250b4000001c01c3e40081d01080c502034000001c40d084075401c4503810590341020080c0b11303010b040540c01041449051009100c3c841e0340c2169500000895800c0510542d4001801c80030140a08010074000c0d030400c8003d40142c440c82c0000d0300f640e02070f2107a00f2455000d4400900e904440c00b51943c0120402c055030310700360f030340c1d40d40c1500e0b268008201121284201c018052803000440d00400e030126420340480c4003545400e00340800d580b450b8000c2403180c0254020130009030300d0024180341801e01100c000c14140381c00d00104103a0703c10840f03c8000d250078514031000b80100405680e82d1079100301040e04040141e100e00c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 409315161 1250 409313911 409313939
    0x22060c0e0a0e01050402030a1415010206010f0506180301200403020a0e0411090718030303061a040b0f130b0703020109020f03120409020912011401062c06071103031602030106 77
    0x2180100300e40b0740040c003017414958040c40d40002c02c40390018a41e911600604000c0d0421a06403083c9900c0c0b078400c0300c5650f414802c044c0140b103402100c0321030310304000000c1c100b8040c1c074142d05000c170f80300348000001d0741d42500105030300d001504c6c8043c4058032201c0070050365440350100b60f0140e1401c0c900020b440c07500098007441a90041c4003004010240420031049550180020040203038149108104102843d03002c401180b00ba100081d02c14a05501d000d40c1c080e803903015416000048c0f000b00484900e40e070848081406030440243d590380d00381c12a15500b01284c01004002001080403000c2680552000251038000c5410030200041403040695881e42081c2c07030480c00030244810029801c40350080d1413005001040306001c3e2644000305030031100c0c1d01d40400b015800240c010071510b600480c1d81c0d4142d1850980c4032503400341c104040ca07942c4440c4101c0b00d0080d10000b4208013400358100100c4074454004041d81e036944040c24450000248407841a4460351a060000070b90035a10042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 409316411 1250 409315161 409315169
    0xc03070e010302030a110d02070c080a0804060f1b1202010e0705100c0201050f07030e13020307080105010c02190f0603060b07051b060d06060314060d051522060c0e0a 73
    0x28244414a891004501941015200b85d1010ba2600303c01161280c5542c0607002142c50588010b0725081d035400d210100080715444010107410414850002c00c1003402113509a03049801d290549151007042180c8510f1144601d440e1030300c1d142d0b50602040083d55800066000b198000c2c0f0208a51103503254030f40807217104140d0300418100c0041841400782410300025401414810705010a06051203065480b8081c220001002c1d01c04080182c070341078090350480f02c80313140210308500d4055009040c04034103015003410300009030144800c640d2442840b142940000f01c0e0740194a030fa520210040002c03074051400401d08019001c9051000d142c01d8800050b0040300030103a02040424040d5082c0494842c1030300020108454400100140213080082c11241e400203168240720354486009400503001910034202c202e4440301060001230100800040303180c828219455107030038003072481c602c0e14007680c034000c01e00c3d810340038416107034031000b0750207590f80310500d5110700002002414002d80c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 409317661 1250 409316411 409316417
    0x20717090a06080a0204091a03210306040902040e0102270d031407030203040819060f020307050a1805040c1701080619020717030a02070c050105160318030b04030c0b0c0307 76
    0x904101262181c0d0303410303400c500034920061416464141310400e807220388002064041c01c8d4241005541010041d85000c004c0c01000c2c50071100c040b0071021183e20010304100d103d107413128442c20a55685500c0410443c00341d01c000c541c0d034010070014140700112007001d05014072108040c16410b04280c1560a03407243c0c144e9814410142211348030315690003c1c20181c00b18071040c000891807510420240740242042c1d00c0c861440c11049c98050262140b414280e2050f070300500c10722030029041002d84161072024182020781c41c2141a90030040865a40003950007420510340b0000d4503017101c6080c8000368280c0d4128517980c0c0300c9212030741d100703000e0712074118100703022882c10445c20300e0364003419180f446a244111840c41d454040c040307079001030f6004400f90ba800102001004042c1c80044001d0000b070900c1e9040c01c0d00c101441c40001104200038007840186c85c0d136080f002c07c0300303a00c0300040e5900100e0788410f804c00c1c1c24028076203d146441100d803001400f002ca8524180304060b2072280305195 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 409318911 1250 409317661 409317679
    0x5091005160522030b1009060b120f06011103040b070506091c080c0c0706120b09010b0405040e03040803070605100f03170703022b090e1308131802071709 68
    0x4111011240c0710b0440300c1c02c8240d64400080300017083e60303c4c55801000501844a0002d080000440440b00b01d944103d5100c00c0c1003000c1c54a42c1040f42105a1041003004020010f03a50307480141c580388640030544070140000500070450074074400c041c024960064003100d101e44e503801c0b0700c956107454010303030b102d0302d00c01d10348000e044035115100e669444416011118180100c86030311a00c2e10400750052400708031845e6030840481e0380c038442d81e000c2c05000c544c10f5107694940400f440705c034820b40c0580d501640e05d440c1d50441035142002180d00400008085980d645020304013800108400d1390a400300356005200059045482c1480405582c0c00ca021403120120110491101e6071040f81d044066004e6080e40304021030b02001003907000d544104465500c0e06034000d00401c000300a41083d0b00c0c160000044c804601c1034a41c074a510340d9401007200b07a880e107c12403c00e500e8101a8060450b8440e1007a2820b5030000c0c179005460050300c505034201c180d9001e180f41c900503010301c41401760080241 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 409320161 1250 409318911 409318927
    0x8010227130507110d02011a1806060307050f0423060c070501080a1b0f09320102011104030305070b1608070f110d11250e0403050409050910051605 65
    0x42d034402d5403c80c5550030585160b140b80c00102e81080504501040940d41d205400d440b1f1400043d42104c500170101e406030b0303d00306d82100c1034031042c9024010794090b000c040b00080159000381c0840c1c0100c4524541a920b4540e900d0b200200e003107442e42140708080300e88000c05041c0c00c10310282e48000840002070030303440d0b08000044900400062128143c941c6035000b403030220020315161500080f4035511141011088600a45044580e50000407849003d41c855200d0b04441d0303001903583e403941c1920f01c980036050380040b40500340c010388003910b0710000500002010380040040a902d4420100c507000c5a954200e2114484100410440800d841d000000c05040c030680740c011021107d410410aa54481c10b00d6038a801c0700300a00f079001c40d00e11000c0798404542040082c0000c100c420000c1e0000e450b4008000707201407140300d03188921040c000480c0806024070155000b0300020741f820045403606410903036595078004c1040703034458a0080415154600364510220307072800d5450b214901310390 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 409321411 1250 409320161 409320199
    0x5061303030603060c080a0c020c01140304060e1504050c0d0305030c45040b060403080703020c360f22060f050105090c0418050a090c08010227 63
    0x4650118205540c800c0d012001891a00c6062000b0b00c140c0e845403000e00c1e10407111400c80b000a1a25000d660241400c01d010342e900084c01c07940c050140301c03806e440c9c2d141c1d860004080c00b800d100e482c03900c0c0603c00c00800304010611160b841640030701c0072120820f801d542444066800d910010300007980400004044081d000700800f0f1005070500c1503030034804803e091003190440c18402c3d05c2502d1460103085119070304c566101110365021103040080c0040d55002411602c164840100800004a00c0e03401b4075000380815901102d010b480c06c40c110303040c201c40e40c003815240280d10158104160040c1c140002e0036124a1180b2084880817005440e50368007000300961508000112201d400d500d000054220f00904244804904000c40c41d035040500304411402c0080090f01e002e80305000400c101c500c0e0703080303a84410814400000d00c94841c22003040c058800741c0c2d0003402640940358001101e03941503004103030041e4004c1403010020307619046483d400000d081d41c940d2004100740d0205440301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 409322661 1250 409321411 409321441
    0x625050708090910170c0a06140403240509030901021209190b040e090a380f090c15070204020c0a02091005010801171c1407150609090506 61
    0x4007580392603041c0012040040c5078854111480b6060800c007140030881100c46005407100c00f100480901655010f45010031480c1100e84580001c004032200c4103040c0c101e5020840d005160419209240c40410003911008002c01a005078091442c1c0341c0001d10b421404002e1f10301c403180c140e01a00140c900c0300d0b002c0314190010700c0c0d85580b040e00c5007000940c03094500c00800060003150689a155441d180030310290503801001001150814810400068004090b0207500040042c0385190420015420100541460b0088082200030000d018402044003029440360f40300804a4041d0604001803110b0408480c0d07d100f68800c0030b106030001403601e9006464040146004c680e8000c0a0b07400241c00205d09441c0340c4500410800103019a5070711690050250201229901354408501403141e034170350981580c510000d201c0c6000e5080b280c401c100d46454440c081101e05d1b110551801c0039448500348903001e0504503e0702000103503440d50342c01a50410f42e00700000d03000760f42c0c61910009000d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 409323911 1250 409322661 409322663
    0x50712020306090f0702010f020d06050a060206070203070318030f03031425120e010203040c0e010503031602130b10090509130b07050307050f040906090b09061507050109020a030f030206250507 85
    0x15403101400c3c44c16406601c00307410505460080802c4bc18900b10503c01030b002c06402060843d0400c80c2007205240e000002c864070316905150584008101d180300480b81c402e241c000610100958451506040d8160000030345a00c02080d80c072104c1c0c40e0446070078100da2100301160811140d4040c8803070824040e80c1d0403088100d82c80d00125510508110241c01c99200f141c085801400680003032040c120980949400741405400540c50186142c1d202200c00c20030f03032002481000c0016581c00c4805c0960080c0180e140003518581040001c2d030741c0980000c40701d01071240076a0101c400244000000044142020740020801100c0c0d25412030859140c0d10044c1400c0611034108800145480c1d020010001400e61040005207242081101400e0720342c500c40ca9482a0504020f206043da0703010188298005a10341e107666030509854024050419024080c0d0b0020002100005010b403030402c0b46020b40c03195007503079520b66a0038200344010044071842c01e440050000c07000c03640d9000b40c0050001c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 409325161 1250 409323911 409323913
    0x603050a0902011d0310050c030f07032a0509030601032a0b2a0303040503030a0b010309051b0a090509011b02060907060c020a0509101a07080d0b0105041206050712020306090f0702 79
    0x403446c4030031010030380301c0c10b44800d00792640000400c048540c11800b8143c11180c2071800f84850030034003451203000c05080c40c2c03041d05441940d4100c60818010b17070859800c054081d05440103036a503410252000c03148801c501c05c4508511952005128a080403401074841e000021800c20183c0b41c040080c60025850042600c0440d903000c86000c20300b0806144103601c0f80c401147d41c0e14002e40d0036419a00b00b407000c10b05140c1411610b00004002107190198810388104443e8102001400500202d035540c2c0203d0600346408203010704d41d9030640140340601e0940c10401c01c100100e50049a44190031203501d4019040301c0702c24048a4450741d4041921400109640040c58035400019032407101503811840c9a941100e00b00400030407542ca82c0305e8500c5030a0324504040c0b40e5140c07980d0341d1140c000203201c5e03a503541da103003c0309a0080c400d4902401420240740845016172800030010503081c2c80714030110740d00384140c403911040c5d8000c581c41280040c00e0132905482c0c1540314000000050114015 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 409326411 1250 409325161 409325173
    0x7151709031c0507020c04092f100203072901031403040302060307030510050105040f0b09030709091a06240702031507181205070506131802040603050a0902011d03 72
    0x182d0000700c0084100880e45840011076080001d00030780380c02441840140154203020340240402d1504005950190143c01d080001c4003100c0d000c8903200c000c505025a20404031054820000d81c00400781c00c1c1c052140e00010150403404200010000d0002100c000b01c0203850018000142954030540616a040088906060702c0354001740ca65081150040000303965036003000b0800c00e0003108000208801c4c01c0c41c921f400c0c10200195000003490207200d80c2201d002910100076241040a50010003040504102040343ca103000c0c489800100420040b82c0aa1004110180b510302c1030f00400102c50085c0d09412803d034085403046801c00301c000e980c50f00540c00703d00e0030b601e030451641788110b0322669540c0104144040c180c01d480e001d07401c0a02440c2483c1ca510000600000d8400f0540c2c0702145d09603160000040c440c0c4484115411840c0303400f00106142017003454030380150040e1006501c01780010741d18900c180c02100e403146c41c06030000e2124141c2d030160060840c4202000b040c0541501d00b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 409327661 1250 409326411 409326427
    0xc050c04020a0c060b0906100309050f0709091a090d110115081c1e180b0d1b0f1403060a05060304080306030f06090c0609061902010e0715170903 64
    0x4102e812103603810340891003100c003000c104611889000b48110081311000404d04051011403451000d040005081c107984d1030310039050007020400f804039040e17440d0443c0c078480d44507031400f409400c01c02403c884450541603110801c090204043d44101c00910040071701074040d8000311101e0031840c141004035541c0d990805d0503030b200d060700400035109000090400200208510307188159018150040040316401411807190403400103c1035805490080c1d0264010201c5108942d025405141e003d10300042440b442000c5802680d00402c24020030320703202c03480300c9003615030414030001540010040d07900080c0d094100b00185410040150204103290740380d0010030b000e5070007524142e50081d0b0110410045140402c4010210080703d000350150b4103000d403040b940e41041c001418450700c404640060940c951034159004907590b0089101c28408400700a4000e01c0c036503561811030301540301d02080840e2140104030680011303596000c200500c0300c480b040f48030b001920540ca14001000021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 409328911 1250 409327661 409327669
    0xc050c0a050708060a06050603060d060e0f0a030f0804021f03060503010c0c0204110c100507030f0203041212020f0a03050603032b14070903020d02011806020703030801080304050d02010c050c 84
    0x14010710540080030712a041c084020700d424070050622912605004043c000e41e11960141c1c1c2e001901550740c0400c1021038a802006008421150201d521403040c502d05140400103840101601070f0700d441031303026000364081364078641c1100d01079008004004610b24105032900c50017201c1c50146070014010340c03907c000070309540c3d8000e00d440c00142161100401e500e0b00303100b001d0302d000f46040d440e0b11300b6000340e10035919404490002c4868660f6a400922140e019400c80302d40710b82054011907a03450240340400010b0420340302d200002c0c0e03041c480f1002c0024548205c0b81c01c40d140c40849424103628820450183c2401070000f50180030a00408070345080301c48100e00c4100310104003540d60710507030151008031620f0f0030154041010306824421041e81083c40d042c262501910b14540c5d42d0030500041e0380c58042e500c0640600a4001c40000d065640401c40c0e8040d2403095a80445d0359a9501c0c01960343e0259020300d0f980b000d40091281d0041d8014410100800e1080c42621080d0009000207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 409330161 1250 409328911 409328923
    0x402060a031d0d030e0303010f0302060f09060403060c030c2c030c19051914064b070c0e0601090807091a030f1e070902031807050a08100c050c 63
    0x842c40da8003e66803402d016405000b841c0400c640b00004504661618480c0c40820015202c041d002c0c03c0c0001d074008111800000701c1e90140805082c02e80d03503da580c5061001041c2c03540d10000081d2034250714060039803183d40d0142500c1c00c3c01483c62020406e000c005120034003003d41c01981b500c2034078052a81a100e5550a24030705145030000e07800e49190009000c04006000704880ca44200880c0500803004c05070303030f056108041940d0703482c0c6504120076042010746242113024a04400c102c80f2003c089407000c400215818448240000244c942c4886895401026801401d1080054080c00044071540c890707907201c04145005d02d03100c0e03952009582403040c1c0d5040545100d032241160b081091400300b10000b802c20950040c041c0d41000f402450b15034085071001c06e8448550510008070000c1005500d000c7c00801c8421566420074258004100e204821804164000c0e4000007410b0310346001000d0488940c2d002800c69030642c00d028030003d0002c8002141404801d100f0807024840400071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 409331411 1250 409330161 409330211
    0x20607090911220321020703061109060712030605040605061803150106021c0906022518050a06050405090307110303130e0405060c0a0207061d0621090606090402060a03 74
    0x300007140c02c0d401c000d034440240341c400f200000245c1c000080203035800640d01007260307044140000d044a241d68078030954814400070a0780001c010540d0414401c503e051400d9080594804214103642c079424030054450310b00c1020f80c0103206210031850700410a01003000b00e8401000e03181e4400e01080210100c110a0b00403c005911000c006200d43c040352403050340040c0720307042100e44a40307080c0c8025600c0010400d00f03401e4aa24606051005141ca4041409003820140c20880c13484e401d915a030060100710382d603542260902c0c1c40025103040c140b003181e0051079a0006035147c4178841e11043c1990045008050300741c4020030205850003031100807840642881940d0841c81d041906080c1d00d850409050a00300100c2004130743c0c0c0d51a000112602207400f1070812000600d1440301d100403950702d11484c19000f0380002100700c1d882034030020801c1c0c0400c840d610300200f51172700035070180d5403241180c955821201d010007207401b601d403030400b82c00d0000461a01152525030030207003e01200c1429a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 409332661 1250 409331411 409331467
    0x7020610081009060f02040e19050f0103060c0e0301020307050d051815071809020309060a0c09120309030b0705070212120405121e0c0117040b0a0905030f0309030d0b01020607090911 80
    0x100f0309c003d200741000d481d1070241c581e4800344114241200344074a140d1048c84010301d5035a42d08540d180f514083c1da06d81524002c000d000715180c0c03034038040240c03a40d0302091a001c0c1d0030789400001041e288004414400c2140300030010100700d0182070b03d0300d01c04c42000e4094020700c40d40020030a400b03100301c050003014202d800d034096180d0400403040e1b0f1515001510426246091010340c0680a520100c0c0c2000c96804641e83c031000b9109050564860416400261150802c0c0c010046013580220051a985200b540c0018a1040395084181ca9596440080408107810401005203181c000040e000c40e42070780d000e84022a003601c00100e0305000325541000ba84e0091102034240d50f17003020a82e560b5035598100e9010030300d4a039480d0031403420014001e008541e6200e404105111040040c2d0b4031440424403d0b540e681072520305035640e41c102400d200c00746410010a90201c3d4808a5a6070158511307858081120b03040c220004060124490010404c26080c8098940d440700202030310034100504c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 409333911 1250 409332661 409332689
    0xc090501030c080f0c030a0b04050a05100b0304150c0302040b130302090901020a02030706090804080a0506062106150303190c050f01020406020607050a0207030f060507020610081009060f0204 84
    0x40050280c425200c0c070760b824400c15000f00a810b8048000541d4440c00c2504115602e41c0d5080f150300090100c09449500035140204000307001400358051401809a469100380041da6000390018503c01101c0040c005850380d1100021208660004001019030741005400c143c0c42c0c0c0d0b04405140c0180044c2c15001da8002c404200398100140d125030045039000c0294038007001c1c0d0750040c1d03603845444002440560b54000000a1010f80c1c006d44018000c0300007600c01503a030b0341c00d01c1030303407000280c0320213100f0000316101e21a42454840640c401082c0c0c3e201400e039541d84c0510448080f040e005805030540800c00203054000101200003401103915160f44400c69401e040c1075282428003004800d07140e10402080c012103800094035030740302040340b8100b5690308a2060490a004461b40020810b103403007415007003005500e400292103100a82d00311070896a40341a43c80400315944121015501b000c8120414901c440e040a08100e000360401305203040712042103c03c80c1d00a6008041d890200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 409335161 1250 409333911 409333919
    0xf06090330060501020c0a06140903070602030403031d3d050a090801021e030a090510090203011a06191701030302150a05060a09020304050a0209190c05040b0703210c09 74
    0x242c4184409800280b000f840b60102c10b8000c41d182030307240d01903441070000000101c01d1143c0e606044441080b00642580d040740d42c0c469020396650800e0108901040307002c03003103185c0d6a04c03101c26202c40c01801001d500b244030650080040d0041ca01e400b141e4a40c24203c1c0c6895115001c468091070b10300c050307440558075002084000c02507407140d003002d40641d0042103c102a038024007400d40030107001d40c040903501d880e004049801444a000020035501401d081381e000203c4c60b84c00500700d40d0003a8001d112002c00340b050f440e8410702d420300c6c0a138441c1e4144810790103980c0040c190491a03400d420f06800c4041058001c1003011f109900442c01a44003001d0100b44c6280b1417083c0b501720004540a002c6810b00c80000782100800f40103803050154080006001c0c02800c0151458094024003500c1050030100409541d903064104e0002541d401e04824002c1c091044048400301ca050911860402985560499110b0180c00000e07984001c4000c4030340d00140300707208580b5003008540786d1803081450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 409336411 1250 409335161 409335257
    0x504030e0310090c0b090d0b010b03040b01090c02060720010e0303070f0203030c180409060c0e0a05010507050307060f061502010603050d0806060a03111e030406060e040f060903 78
    0x5582142c1041605182c800c2c000101d0707a40c180025070f8420000320f610b94540401040700080101c00c080d11181e401000058180e40700d400940c0079034000e8240000b60b0307807070707004200640f8482098400181d200c54002045140325000003107412954901d844861175044020701d007950b0302080c4183e0203401c00028005016009800c00310f5aa116001640c11480c0c22040c0340d0060040200d988881034000c0b005848583d61540a40d01c0207920900410070301c07100050048c404900c0c5054907015080e80040801d070356000741c0560380c803203501c1401149000b40c0c40da0b50b14040e21403038001803003154481c0e2001c10321f80d420300e44d6108040241d500009a20381b540c00c0c042c0c50000c0b41003d0300244a000702c180280c3d070f118041200d900b9400c604010449400c034420f6201284581c4110f88854040060746280703d400c9500154015070080405200f83e58880c129040c1e181e00a80340105080981d802840025025800c410360290090401c1031080e42814190011130818240d00003601e114003030500c1400c0c40c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 409337661 1250 409336411 409336423
    0x6030a1d1b0f04200a18080c0406050102030309190609020423010f182016110a0605040e10080613021e030d1107090c0e0127050f060c010504030e03 65
    0x1008880501150340190000040c140c284a0010184c0300d000420f07040c4580204607001690240e100010742031541d4852983e01d031400c640310385214600380f5100207615071000050381d024002d0080035001240103500d48040c0d000107184211229600c800c3d01c403000d40d84501c5080861203554005410b215814030502e48074400c145c00021020500348130a019040c108a10b52500740320007640004c00114203105410001e0210a40c8400c450f0001030084200512803640c03041e0b1841020340005444001e403c1003075902140c06041c0000d0001c0c0800c00c40400045041500440608c06450241d9192600382c0d050070b80c11101003620108102d5800c0450900c480c1c4000300d0306030aa441f11b074080c0388000098445016808207070810040c5028144100400e1007140003d24000008102074041c40602510b0040d20040403404103209045e50b1801812540245000c0c00c1152445a22541040f080003010030b01c184501c0d4001c1c00a0003441509070003445198040c0b4045d443ea80c81c940f404e281090300d025 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 409338911 1250 409337661 409337689
    0x9050301061508010e01080a02040b13090c170105090d0c08040f240804020f19080f0601060315080d080a06030219232d030717100b06030a1d1b 63
    0x458003100403c407c04010030300e001c80580c1140e012802500400c0050554203600b040860600d18241e02c0d10304100c02445210211151801101707010302640c0d03112030807258126484802508440082c2c40d41502c9440301403015803003655401d0500342c41d61803041103c0c3d050b40204003050034000f0140c08840c4ca03102c1e40c6900e24142d01d0030901c145072940c0801c01e13000e91500494050480320925640034180600700f440548040411104a282001101503071a1000e21900010901d040400d50507445800d405a06a4a4080040040219004084815034801040c5440745595074074080b00694070b41e50a40c07205801651541410ba08140742d135541e84040400040d5a0284407000592170b03201d03860012540300e9078803006079001d0104100850759920038440540c1c0b60003045004100c1c8209040005c8400a002045400301030006402904480403809281d6016005000248040344c8507006031000800c40c003014210000f140c903003940303015a44444a2890f40781c46e0742c0301c2c0e03060400c090010222 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 409340161 1250 409338911 409338929
    0x10501090b09030d030f181b0503010902010f050d1805031207030501050d0602071103030a02070f0b04030201170a0b040e0a06050a06030b0133200610060f0905030106150801 76
    0x1103018000042d0350350040501c3e04d400e15403a110451030900d1070b40c1c041321140f4140b515020203d0007500d0103081d03246140c900c400d4801c40101c00032032103040500c14884001c1c5e042e100d40042182c0207400780c81a802c4081d840c03c01131b0b02e03a15040300014540d440c294800740320341c000350307105c0321886030151100700028511810503162030010807069640342a160300f0341d038101c0401603543d105801c08410100d0720795400b50700b500c40010300c80d0a55900013240d00c1158451500c01095940750540c00400340301d1840081c0c00506048505001035408680f061707001a11a80005181d000c0c00001c038056402d510081c0105420440c00b2500340000d0b802001c0d8040190b601c01c120705030650751100c078405018050044075041e0800b020010481c0014824545449170200c4100380c60803200c0201003501176400c080018004400d940d40c60340c4006038686c00307410400710304601203081030011134a40c170100021904204280740002500d0300c0070700c6410090100c0500703441c44042c0002015040c0e61041c2d100c4240 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 409341411 1250 409340161 409340167
    0x501050708090c060a020c040213170105040f02130b0d0c08010e0f070b07020d1505060406081c030c050405040e010501170d020604030c030c05010e1c0309030e0906180f010501090b 79
    0x141c1d107008a494000c10f0011980c8680b102d0030490100d16140d68140480c0d0440d10018030342c205060003222400441d0342503190300b0020083e0011107030986a082d03400400020602c143c80e001441c05800d0300c3e90900340b80c0b40002e00a10854009500240d88502c00d03900c8500d21807080c400000300380101101c2e0007560f0001c14185a00140265a8170700500c28903d01030340c0440e0400440d074511081c0240030b83c02200d0190000e1030010320400a120980f203071031203145844000a07940b80082500060340000710300002c4d488138134110940140803000c922310108202008081420740c1c03640303e0143c03c1e51000000062035814412030358003896414030741484560000900e00d030150360000300f450b0300c03580c90700d0701c1d00039803000c0e182c1610711100c060310040c01c42d400c0c42d0785605448400102c0701900e0940700313850f00783d13201e80381010390072901108009400540c0b10303c0040c10a080654495410400160922699040d821031500c0c4401054880c00c0443d02e034040100507541e13205c3c00c240041e03c4800046d601d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 409342661 1250 409341411 409341421
    0x150d060507020c0d03050316110703050312070f120b0a050d06230402150c100c020102030a050709050609150c030703020a1416120c0308191827090f030c0501050708 72
    0x100707d01009129070300704020408100310191080d901c0d2808801c4040448d0010341d168a086a141e801c801d0724854448180000500707040e20464600b90842d9041e181e50207003489411440020342607c0b0a011b03000801000c000496480b1501c10fa408240241000956070015030040d04200850003410001ca00a400134000540d544c0d01d400e0070400e00314220381e0340d2106128511400e2009035420594805e1a01d80d00c000300507010340066100ba50b920408104654481009448d60343d52030281c07540152043c0050400c900b8407200c04038800c802001c0c00c50608100d40311083c90355116000482c01600724100000412030310920940c00003000d10302408151007111482d088040700340c40b5480e140c8014008110602c10300090800c00707160002000e60b83c8041d0f1946006050f2000b04c40400050b104461408014030210401300c1950a5072110740401c1d103484010311025140f840e09208010390383d810000005880d0080c8031500c600c2600d4601000415080c00da0031214001d0950040c410301e41d003004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 409343911 1250 409342661 409342667
    0x6050d051b09090a060f0b03250f110115120b0f07080f070c050f03031b0903060a09081603031d0109050c10021006080a02031608060c03150d060507020c0d03 69
    0x40c2030204180c651000f1980c030703030000a0281c40c0c6640400d00320702c031140c80031800c81c010030300841c41850281d8203658115000f05890003218000c0d0344450000721840c0044180602c0b40c40d80392101b400c8400046207860b2840083c4c02d003103108d50300c480d41810051540c1d00c200582c55881c1507200340f490500503010301e004100540402c20040c1090746010b101000034036028040c4c215100001d030400100d40c0c1070788450035815504c0d4020b954460a070100800b0380c0107422000c5d41121320141d4041c000c5c103000e8440d40086400380c0031640046465020600458840100840408011600980d808103000d9190340050300424006400701601c0e9044c80a860b012510004e07014521000136100c0742c0c114030341240100d08201c0c24145141009040400004000100040205400380214251058940382e540d08416140f040c3c82010720703c0e00f045001401e03c18180c0040d56111450403d0b14141028030343c0010b1000c0c11025045500e80e980e2401d004685504001c40746c3c0c0090140c581c4d1001c2d0601c0c0c4c8000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 409345161 1250 409343911 409343917
    0x15020d0504301505061f02030d1805030d050103022419020c03100902030606240702150c030a030f0b01050f07020604080f060a11040e0c0c0a0b0106050d051b 69
    0x410710140c102902e0190902106000741003103400c2161020400144840d98003e000c0c10740d5043d2041904401400d6207869600c0440a1030074036800452400030741004c1d41014020030202e01c41d401d528a1302c920080791091005180200361100d00141942c154410000e650b00d00346501d1501e0300a000d00c1000703c0b0710710800c5558841e07060054400c85103005a080f85410b005d4022540c06004e41c02e0406c003070b0251030300f01246151003182039071426600e950a128402c800740040010151704074050341c20b0b101d06403004045040c0040c00c0180120400e2114015580c05007564a10076440020409040b940c540b0130a01a04445042030001030003403000249140540d210541c0881030003c1c032036007190350310320846004000160a81e04018410b90300e40b601c61004580180c446414103841440c0400850200c0d41500c10000107550540c49490341c40d070440d04007154030443c1c0d00c21145140046490303998031500820140d40c949940b410007206800960b00c000e00040e01c8014107110440c10b8001520035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 409346411 1250 409345161 409345199
    0x80724030531210e03161214030a0921170d060f0b070218061f0314090f0d0306080601090b0d0b070c0c050f0a0504020d0b030715020d0504 61
    0x991403402c820681030100d007050103a00034441c00000381d01c00d01165250074805001030b10343e2a82906104548107144c1c651440d000351942d624070101c02407000961001c49020024055051003150801010800d450f542c042c954171408152010b400300300030340c1c403100390050341a40402c5101c1144020f56440600010035085082c00340c00c0806c10030004034083d4401001406160000c40c4910fa072404a1040780d48054001c0e0f01a04403c15100040c08000707420714001c000151098176480d5003000b81742102c00c1da4203039030002c05803030702001c414a44003c80d200e0f00900604006d842e0b20819400c1991800700304c20001e006050074540304001d050340100e511070441c1c1e040c0002045680805002552021001c04001c03c0041c4100c140700100d5407007180c601c000b074800c40c800c1030b40305d4413042085070b0030511621155004404c840c080c4124201600545036440700800c01241e54807903000041e0804684c0c2c3c000c2001c103541c0038138220106034100001445d01d5a1424140d00d06814080c1c1c0d0729a405403d20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 409347661 1250 409346411 409346461
    0x602070b0f0c0703020a0618061503020913050a151b08060f030a05031c020f0a030c080f01030203060601110f0114061806090a1509020301031a0108030301081e01060807240305 77
    0x2020303148032945003005140c3c9e911076410000e80803032315207408042d0464081a030003000e032500001c0381c0c1078100500714445d40e002401440c04450542e5040b074480d4100c0d21070102c0641381d22202210031402c6050704a00103850715501c22515042c8144801c2c5058140d0251203640000c1881e000b04001204a0703031070072100980c1c250003040000700c0001070b1189405c000400b40000a6050300307241d0550100000b034a8039900c5025546400c0c0860502a00a0102940c550003013000b0800c0c66005103040e10498508a003919101d02403039180c9801c503034035401d403c1180c040c1030040020524110314401c0810944648070790541c28958080f40301d4031070050040100d242e990744010a1704d15500840350040c81c29071003d40d903e40c1c4030b141910101d4400c0c50007040210100b80007080170f030300c04015607050b140b10b0b0008000030002c82c6105c0341d104a903651100019540d40002207051417045c8507000180800701c00d2080c8580c0c02e0302c4403140004c21213415500b010700d81004e2025145502240d00901c00c213100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 409348911 1250 409347661 409347671
    0x9030906070b22030f03050603010b1c0222060501020606030109030801060f11010f0b030d08010302060f0708040b0f0c1624030b0a06030b1507110603130602070b0f0c0703020a06 78
    0x1030000c12201240f40d10340b40018041e51080d00f0141c3c8400041d018007040e039024011a2a0001410b0907100c4421040358020050000c02c003c201d071001d00b6100b0180006d22280c01003040c03e1009010780c3c1e03c940c14190b1035032215014031055804124042c1c000c48190004c210182080c0c400071b02440e07042c0034010820003607000121005216815521911001c80d0003004044284000701000b820720000da0307806409030ac080a00340a000340750190480341c001d0328191419030003481600d090350006e02c046402d50b6060102007112581c80303000c1c154402c201600d03582e4070908003042c2840c01c080c82113000c40d4982042000d000440607441c407100b040b04a254101e0700c1c41c41d5a1030540181440410701500a0400302c1b00081c41c0d07505420141e00c0c004107840340204220031402220061145c16005030891003d000b88a045080c420000c41c1e0100c448a58913000800b181c0c0e410040c0e038480070003a070b07490050b0001c4c00b101c90100d64030980c020310818800f03441c05207140d802070348440d480e40c8040c0440f5914 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 409350161 1250 409348911 409348921
    0x2101112010e06180906150603091c0921030905090702070b1b0604050703030f030b010c02060c031611040c0504060c390f05060412121209080a0809030906070b 70
    0x450f240691254045080d00d42c2885d12030000c5588100450740581c00407000c10010740141012021a8000d4881c20040c000c0b110b1040a03410f84400801d4150040140303810700090260408802032200440b140c0c00503800c0d10150a0040200c800c94001030322a05c085414807007140e03000140b410454000550341d503150740f05100208000324003000c030007036903005000c01c0004200d400b04014082c4c9100b512500d03007543c0c05080c12011100c1d01740246011804001110026142c0710016055008007041203030324041c0000c800600402e100d4404407110b012181c441c0c50300f450640a030240d449250718185050501c0d080004148203e550000380c10007100e240e01c4848280f4004c240418a820002c840100f400300a0540c4003060841c85800380301200d12401160f0784ca0050121422036400f85030700e070380010454603800200114a500c0b007003030002618104103514141e009986019015099460316018a40d030043c090300b0000303014144503002004688510340e200c006982035642c203c2c40b412196039403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 409351411 1250 409350161 409350169
    0xf0d18140a0b0921030903041d04120509060d050907090c0c050c040c0c080309031210050112051b0f04030206071b060809120a0e1002101112010e06 65
    0x41080250440c0954a035a04426800140c9100030034411400a201c41e560a03982a40301c1c0020490000707620500113507030420041d014080c642004050060b645482d0b540c0c5503080c8001144414090202d62a008010510855140c0a041ca01407801d1080c5025a1280060018030540030100c4035682d0318808110780b40003c2000354064454881c0811506035202006404034110b5003080742c01c0d10521071285151b00b02406414440c1d007964955141d40d070a19903c40b6600d0700010000c0460348020310a40c0d0f84451030224040c000e0303e0742c100407040142030100040c4011000f0b01d2002c2c15504060511110408043c425012660f40310b14081e154910364802504510890340041d41c1302c7c20100d462000d2100c1a140040c10300c1c1072070618485641c1d108030696504504846010143e0001040e40c0c4081c2c0340480203040601140c03038032a500c0c41210b00014900740042040307374016804400e400e0500ca400b48a08010f00420401c0d0a08200b5500414a40128140605040d004281003c500c050316 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 409352517 1106 409351411 409351451
    0x90f17060601030506010507062a050901080a1104050604180e0a05030a08060a1d0a0501061b080a030b090a0504020901120308060f12070308120c0f0d 66
    0x5207020055000b050014011410b102080200f000002c074140f142840814010880c010b80c4007000086880f14a820703c004410700c2420440640a6038006103255440048aa400b00c2c0b0241070a000c4844e600a5910260b0040340201e0041850701740304c039620840d105408010072030180307440c103295500c40c1a1080602250010464001081e1155800c16400080a442a044243e40342541d60305192214441062801c40205111220071907015450040c40c4928103440c040d6003003020044201c804001c014038000c0c3c00641c1100503070003900030b00c195032802010a145842c001b032040b4040c00301210704a1084031204004500f00040030700400d000c0e60156505031840d580d020034044222078002a20350300c0845018406c805040400c00500598403507103207643c4610100641403d5188041c0c60b00307651000a12142003001c40c80d400381c030302124184c4008101013103070100300103c5903 = true := by decide +kernel

theorem cover : BRFrame.Cov 409172661 409352517 := by
  have h0 := BRFrame.cov_init 409172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 409172661 ≤ n) (h2 : n < 409352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
