-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5282
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:21:21.311911+00:00
-- url     : https://prove2.me/submissions/204a870c-662d-45ad-a853-e4d61552936b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 949820143 ≤ n < 950000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 949821393 1250 949820143 949820153
    0x20a080601050a09150f080f010b091509090703091704030213020327030a030b04090c050f0d080c030d05010914041e0203120a0f0207140f0d080310230d120201150e0103 74
    0x101d9040158880b108d0f4070365241020304207190003007140711882480620302801050741700b40f040380c4a002d0040e003984d001d860464406001411171410950781ca0030780c4010141c560044108440649600134000c541103090104500300a41004150441e01c000000e20006451b4512540e0004d200102d00110ba035040720100c020142c0e00803240c000d00541c1481214800104045688001c1e5030050b544c1500d8001c0d020002002402c0ca100c01902e60340c800500980383d2140400201990342180c4020302c46a41e031540d00d00708480215510b0803204048401050020703c5841000b25410142c11204150601030f40010381040041c9000ca00c00b0030000031451006500a0f040780c451420600180c00e0040c5004000311072458440d80003485101c03240c0b1045265601e542da400341d2281c018003200c3d00c1f4034050307001d81358a5070b0502820881c241241202152094000c6590089000142002414145a54540c14400b04114103c0159500e400e54488800a20040b8100510010b286601194954102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 949822643 1250 949821393 949821407
    0x21803010b0324040501021201090606090f0b070f03020f10050109050603030f18040227090609060d061e1b140301060503131416030213020a080601050a09150f 70
    0x190310b0098016000140840764418019140d80484030364202860391285030080c0248122117100401e42444070010904988652041040d5a8141c80d0b641000b51500c4403440c15000034482c0080d041c908200d5000054202503000741194401d0044440983c00e0301403050904011350b1424050580e144010410b0108a00403990441010380180d40b80016001940b0030070301c14544407a150449110851000f40c40d00d6046505400e00880a03042480c45030030080c4a003032a010203144118445004500c0d545800c00003180248002030003581100b0b40740c0d40303540251151050801031715104a0765002c00d02458080c3c280800301d042c5011410200f00c10010305941902c0303822042e103000030303c01400710a4000013200d401c40c0444031541200c1d059403174140014066180d24414600402c0403d0803a04001202c42040c1c9102329046142460400010700c12401110f4003200050340c1007002c0f9a40b540200000e1134201a5860841d82c6140c60b07410902c14118a0400540010b08000b5910f0b0115480b101e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 949823893 1250 949822643 949822661
    0xf060f1404090c230a060509010513030b0f04030807020115050103270506091c020d0806060706060305031e0c0a0201080414030c0307290c13030b13060b06030c120c0d02180301 77
    0x80c0100c17030a0030001c00818038011540346a040c080e000900346280c003048008c81d00196070100f0480c40b140b03031a0941100b0403400307590441c0461080c0b0301060b03001e07006000345070300849919160300701d543c81d00c030045000e0720340140b41078007581844060350340f00c0b80d15422050f18140107400400d410300340b1080040c0341030701c140b6031a1f03c0110500052020154041403005500c1410700e40005991202000984c0b1441078140080180749010030000c00c01c0800310242000300101c0894400700075000c0e40c0d017030441c0320302c3d1142e04e0243c004810000c01580541d184607001402424000091500000c01c1403a640c40740108910b90340c80410042d0802125060303410a1090801840c00e88140229032841c0d60500031b4644260440c0101d08080300300103112107040155044840c202e5a410107803200d1044a40913181035500500704045290142030000859001385000c2e0b4601e458455902e1030100740c00c101a000103040603081018070b608050900180c072002461170124103410820404050842d91030700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 949825143 1250 949823893 949823899
    0xd1110020a03050306311a060a1709010209030a0b0a2a08040602090a0e040b0615120c0409020d1505041b0c050a0b0c0705010f060f1404090c23 63
    0x40785900000340c1c400c0c1641c0d00100c00b503610406000c0c4103407002c610756051101c031543c1c09203070b8001c0700c0d0f80710b0a0f0341008208160f0140d401102200f10800e2004034881c406251000c030755041c150901c84100c142001b640f024a4900050400304100006410558040019180f0b003c40c43c1c02e0000c528000c0c032405030310b1500c855852008203c0e0b018900090086003d00c0340c02e018030007002606002c5150100c40400c100106a401c202d41c0311240076a00060030b0320181c403489031071400228503040c01c880514011043d4a0f0040c20021407010404500c0d0005061b04030807071040c040091000c9c4140080c007038541500724041040b100400380410041190b07404248650f042c40400300001e032155108082a80441c0740c2003103100200d0034964507100c00040b0040443c100380e42044010404480a41a101d118200030b0211961f012418000d40b0b40c140644c000032a401b0b9410042138800500c04045014003810100316090319445218102035658020348185041d103d904240307002c51111880100401c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 949826393 1250 949825143 949825153
    0x110f03030f2502011b2303040e06030c010503040f1703150f030109150f02120a05040b092a0111060c22030803010504050402190801020d0501050f100f030b0d111002 72
    0x81d000248000c40c064615030b143e40b200e0b48281d081c4400206500f0501401206c4101c141d50030100c282c0d52a84030344603c200030403446000c50711914001c074585200b504140d580e01e0031526203440e001c0c024088140c0854001e00b42c40988a4151902070203584200c0c00114200300b100d802406001c2066480d01c0e60300d01c6079140c000d81200041d00001300d0009034101d2800042c070f10078400d01c000c00078803c24600f00021602c840030050b020344260015072165104402c849155100c00781d02a42d50f500804100b6024405040401052203440000594001e0145030903031106000d0418141480390649002c42409000a00b041801150000c80032280289104103580c1d2803861315411040e00041c0201c40c03140341c44401203015555445020903c40040c52081e0003034070342d20110302e07000b5484440da81c9400f504207000042e80e449c000d103a541081c0009012940d200b12034410480306401d04140400615a40d80002e5140b5118890007030302c0e55101d500807400b40209072003080580302a08282c03004547c84 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 949827643 1250 949826393 949826467
    0x50604050601050f01111e2b090605160206090d0609060b01181a03040c030203030309011401120203060f060303160b0a1a0303040b07170a2613110f03030f 68
    0x800122000381003520480c01c4e4105003840340356820549242c1041ca058691005108010075042c44007030507180f0951030b580941a5600d0ac01c4c0c44500a14010440d440312015820001d4201071000342901000208406203802c503030340d1540200d4103009400c0d200d583d41ca90030160746580050006004214040c44511210310b44115000d210121210795080c2040c04004602003103042c619840143d1f50040a03a601c07071501c84d400a00a0449292019116046500004101c01079035000c0b00d80c0f58010300075202c1135840d06104003044030040e044680502c020494a4541607901c1240391780684038404403050307400c14681d1042a1a00301c40024101c500d00031903004e1a64001085408032210700d528140c44408506120b840c1d00402c03d0000030180300000c40520003036006075908289400c110a1140048802a00c0e45041c0400c492140d002c0f00082c2c445401702d44440826210034000402c0f0b081c000f2102c8012a0540e000701c01d407070031120000700d000716001c10390074011221400003064554481007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 949828893 1250 949827643 949827677
    0x3040f0b0a050907210b011503230106080403110318040e0f0c13020d110301061e12091e050606090a151518030323030112060c0c050604050601050f01 66
    0x10a8410b40c01c080211810b40c2030103045c802000010b003034000c03090041669440143c00070306810fa00721000041c0c640301d11242041d840142c0d1a4a0030080500804a80c0c2000300a4400c110054400e4081c486500382c0d01a00382c60800c0109451003a02d0303681e40d07002d1190030a00c000c0d0b4081068082640c0c04c040c0d00b146000c040040d8014401d40c00b01e58440c1d5412601d00c1c40340c024451110126903403030800c00100d4251000c40025412203003903586104542c1c9900ca4109002240f055544000031800440c4050116082c1c100d101014010b002c5d0b0010007107202c2c0802c81c0c08590a0b4100d07019080501000007030b28144800c03a0340808114018010643c0c0000c0d00d1a55460a0141485800c490120400080e20604100c14600722070650303116555160f00303000d80384400740414010002c01c5408606000d14441003524102c0b4031181040c000450140e0b5600c0103407000e46015020000780c000c40d031010417020481d4a002e540644c02904242d41000144071219080ba201c2c90306100f07244001340e0a4030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 949830143 1250 949828893 949828903
    0x2c0f1f02010b0f0607390501091e1503110c070501090b0403150c1b0c0302040608030405090105040e0f12180607030c0b06150c01021306090323070b03040f0b0a0509 72
    0x40e8429844407100c0d0a01c0004506c6040e00d18007507413400883c480d070405c640d03128078240080da035003600ca8402040e40e59001d1001800c4407203550151680082c010031040202c0c0c0d20141a0740e81c14280452441e08160300c1400f59040341c01c4440c403583c4506020071155030072015131001b401680141c54605400c40c0c8427450302600d01c0d091030003e03540d5440f82880d0940b107004c001c005400da0100c0c000d94502942080821001240404e03032086160840001d100040001264120344000c0d1600c1d0480e807800c1c082000400071521861418060301c1944212090103110601860a20301d900c2c0782c5401d07402001625505520b030b10789010b0b10b420070046010a8000008011083c2d00c0740c0c907400d2a95401c808220110051859052800404a4034082c2000c06402500301c6100030000078100c0d50342c0c3e40003160480041d11020f0100e00c204c01041d20f0441c4070011181002030940c007207800b141d90700d5001d00c11641c401c5038103032a207003a030782c88290401c10384807a91a0000042001400b00e4100301500310303114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 949831393 1250 949830143 949830157
    0x213091a0c070c0e0408270102010b01050a0f0507170c25030b0f130804120213090215030907050d1415040b0a0b0112050718062c0f1f02010b0f06 64
    0x20f03c803040006020001e1070001c482c000d00708122941040c7d15002c080300d80710001e01c00041d0165080c8401c10810303520681c01d03075101445994900c20a8401d050342905e00750300480003610400810f54501d071041d1015401000c98000c000c004210708505403106418001d0900e40300042c0060b4011708101040744c0c0441c0c5a08541039108241d146e442d614041c4442c004200b000070514540424001100c0c052024800c035818000d66448501d4040c030210402140e0400c54020750111890902440940011002d1584007114170b08940c4401e4488000885906098004072441d10088406c0249030ba410701c8440d0804800895000441c101a074070150402c400900c0203100300c0d0340394181c6015a110b5100200c2c0c1c044001c0d020841401c21080080202da201c102e400081c1c4111140040c12511a04114200a40c40c1245003130b0035031032141c40020200381c40e80d1550321469461881000d95a0700c007280082044841c107203450700341c1100000e82500c00c145181880b4511458000340340b51616401c441c58 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 949832643 1250 949831393 949831409
    0x10312020a05030d05070c02031b01030f02091c0305071a013012030f050f040b07020a1713050306130605060f130f110403060504031e050a08040213091a0c070c 70
    0x2855a46c1801210f00c0c200e00d400c0694140b1074260119102260356640820488003039a0900119000a4180c1d091307100d41822160000000300741039020b1603620f901039001300d00c00e18003245412903c0d16945036078501880890302e000c03c2c000042010703015603491045031030030be4110920321754490381208035400c2d169071000d40135a00444e00e00f010644241d000508041e54840e081205080c41d103502c01c1102d01c01ca0307046400710300c00008601200d000141c800c0d841c661118240c00c018441420f06074894001007038110000d0110003010507281e400380a958070a440903881186a280c00b810070000380d9001138a603d002c1c0301c0f0a18440754640724643c40b8a2072484040000c03035144a40844000100740b031000308000b4a00202e801b004000c601c5c1c00c0280503901030750343e4001d5896040352200700401c1100d118004901c0030068a1011800740c3e81c0190b00500007010706c00c034264116034480603070340c81e468100d8005d054840d0038010110b040c4022500203000d140c100c1c0c1012174540d18880c100c512401b983d40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 949833893 1250 949832643 949832651
    0xc0a022a0a0644370c1b17040b0309010506040b0a082104050405090d0201050f060f0d060b0301020d090b130302030a1803081c050604090203102003040b010312020a05030d 75
    0x460004524100361003849410814072030b8801001c00440078101d140701c41131046040403101e200251007403507807a4140c2c0e0212462801100543e035040c07403a4850b400c003614280c00606c80014040da080001c1c40c480c82c449070000c6024a0080100011149203003820b900c6010014030501614000041c1c1c40003c00818020080341c04000c80004007500950b408140e0040c14607080010f030391390110385c91186c603005400034000c0da12803008000d106c100465001e600201c0c0ca24103420103291020725145028000c1c000003494a1500c00405d0980e813000d9403508889403904403010410076240c240541c80303590300c00704a1281240382d4000751030703129040014003084810300030b08508611080c4102c0c0259404071007035550300310126040303d65103441c0c04a05101071502001a985040a01590300210780c01400703080c2140049402800820700316200709440414950003404c0038a13807200850149009107018542c5614610b4140310a00364101311004542003202180c001400c00829030f11500d9004001003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 949835143 1250 949833893 949833901
    0x4020c010612052103090a020607030507120e1009120809032e0606031a010302031009050c2d04060c080c010c090e0c0a022a0a0644 58
    0xa0141c09076402001c0900104101d000410800050210a8040c0c014010b09641d5100d0a07852040c0800c45070404140c100e8114a00180f4004004045140c400d060141c01c0c005592a21007522014825101c04156241c070320185501c0e010011060b02c600c94600741d06102c1c20b007500358080602440c401090260b02080d043c8250341c0c14001401030201100c0c001d0364888940d00e00c01c03029000f04050180c40c500c0c240b008030f00240300703003e078803444548580e1821480300c4000c01100294801051000c14400130a000316101c6450702800340102c445042064660760340e0031200d01c0f20300c901c3d40d540084c2c0600f0f080e0103c2d40c400b07282c2520700315455410b08420040c4c160900c1740c800d114460146484d075107003900c0380035105d0304a00c0ac08161405060300c9009070f6114054010306129500f8042c02607844103d22804080c800d608170f03441455002060386080084001080340c010799500020041070038a01900c031300d041d5625841000008200d504070202d00010440d00c40c2191610b400c0c410240000c00203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 949836393 1250 949835143 949835167
    0x510090f150615021f090506060112061701060f0e010e010b070503091c060e0c060d050604021912050a0207110607050c03030406091e0303080c03090a0c0902180a0b03060402 76
    0x2c80040c040310007480411841c14000a48569284101905108600b070301807402d18030030b200b50002e4540c00001070074146c03120f10040d41d486812403c8860f43e15102c80000c5442c002c002041081318240000114605003003961011050302e4982200002e510181c004010007000d03c4003550441c0c1d0b54601040daa21400c0c104a800c5202d100d88407500122500c02c5041403107410360308000e4046c0900401c01800d6a5441055101c003100e424042e482041400303c1984410036038007054010700010300041c5400f40046e1443c911040740c81c07201002c2210403c80305100380203401760302da004545250461601c0da00e503a07003c5c0e00b03200d4121200e0240c400403498008110081050317000103100241120f4079143c2c1e82c800100000702ca401400c56851f801c0c03405034035011002d04100b00f9203501d901d814100e0340e078982812400341c00081c01c6561502c20008900049501d440c80f51001e000c0726180503a8a15141c0c0244120202d42ca2059004542072a01085030110719025681c015204903000740e03a920851141d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 949837643 1250 949836393 949836401
    0x1603050706022205030f010c02120c1509010c0807030917070f060e06010510030506090f19050103121e020604121404083306011b0803130510090f15 65
    0x2820b0346103c0b0302c602011600d0750407010804507042101158031541c0c1150001e403d90b4a00408071000d81e010140e040010642c510180401c003240c0000c55840c109845031002c840001a5288442c903590740c00d84811241e4400c520304da024031b8070309050009400c0c0355151002c21104000307d0220318008918001040440c59034000b07925040041030000c8044c4400d03003034840e4020b100ea280b0420f030f203942160f40503010303015481c0306040040c41c0030584d41e01c03402001d4009100a100d41c00c10741d81002c2803400c0400c0b6118140c003031401104102040110060043c0990010300c244c2501c0000c5240c004146039400240e859119500051898043c1150842610324005500e2900381c14000410007041ca842c1c006403640141c02c0007003603400c1101c1c0c0603548001040503030003200b05041d40c2c58000748040d40a1212102d415410314541445540103031070741d04803a00280c034001aa640c503000c481017400000c109954002200640030003400c0210781d92081c01c01c00e0010020009840f02801600d0743c005684 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 949838893 1250 949837643 949837657
    0xc03170a0f0207050d081506032212080601020601122030010506060c030421020607110306060316050f040212010305070303120903090605070f140c15160305070602 72
    0x1000790740721291484c2c05502c82100c1e0301103000203182e410000340c280b18521920001c1c0301001d005103107503443d030b0000c6096815113020360f007410745401000080004d490b6207641c000034225580300021b03410f014000905020060b03200e00720421480c40c0d14000b045505480301155107091104082c0c416803400818a201c14680200f201c00301680c80c2010301d6041650b00242803030310000200000c1e92034400b00280ea015000703001c80141c0c81840b040c8003503030f4141100c00e02d550400117890354001d03040d40081c05603803213404104c6030141703070b180c10345114201003280c10341000045025080040104035118100b003070900c242d910a8460054032500b1743c940d64115046c004180202a04d079607140d003402c4c0d98400444c071085002070030340046048450078621070710344480e915a4980e51003c4c40c01c04110382030b0b080800203854550300d411505000503140c408010a444207000503080034020f010402000485501403004c07006000c12001290480e095044881d840d490308145444d203c2c0d03810000001c0c0a110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 949840143 1250 949838893 949838921
    0xc0d0b0a08031201050307060e011d09190b0906030d0f0509060705010c1206080307030f031d100b0102060f040f081312121112030901200c0d0c03170a 66
    0x20340400d4801d0040b0080c410400c0c21101000d807640e03141d050541d903c3c40340c0300700f00008a85400340c5006622400703400c0301c00c02c20140300d045400601c80c006032481000f40d61146582c000c03805000c42c5110382d405043c45404040390001498582500840e44078038011502c80e042003514005141c00f103000740107545a442025145036220841032a1842c02802c1041001010442d07041040032030031000c0c00b41c2c1e001d455902c0c0c081d50900b0010759003940c00803024a804000d064607a00b1000c81c0c640c1c014083c0001040d000001c3c5500240c0e00004030840741290380039070441d00000c040266511200d07207401e070450307400803403202c11b0581420f221f4258041d0b4402884c5141215200040341c3d0014107038184240e0085408071a048409101078a80382601d000014564004149942c1d01d852100d01641c0d00c80800d5001003503000403483c00d407410201500010360084004038046e00404c0c4104595103034012641080820781c0c2c41500c0241244050003034031040000c0c40f10000b41d14600d80e400120b8103907001c2c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 949841393 1250 949840143 949840159
    0x1e03091a06040506060304081206040e0a0b0f130f0803060409050f1b1002060615090607051e03040302060415031b0c060c0203030c07061508070b1308150c0d0b 70
    0x109a94019114141e8505200d1401d040108400d4946081141d008a501894241c94a044100d0003030340d8050003082e540d4415914800441c07050402e02c1041280e0b1701c41d078010a410300c0c02800c0106007a00140c010081301e8041212640001c880c10001c00c2c0058100c402c403a101d541e407900040240a03c160020164051000e90b00d586202c006010075103c1c85511490040000c1c10702400100b0341090348180050b40f000c000305000c0d0900d103120b0f104460203244054a44950103011a5096015020803039040d0710000b441046011000190a5201d140c00081d5141900d150009010340c00385014103904d121a4041510445020b6440175101c00c4662680c001060403644003d0070741c501440307046c0c0d125410b090101d84000e1011085900c1003246141180c1841a5900c89400070030104050804144003e00c011806000800000c002030840007002940c416100c1900da50054007075000610b12740c028030310310350032650400388140c3c002214060f40f5150b850003a1250003400900d02110742003400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 949842643 1250 949841393 949841423
    0xa090e01060504060f0e06030a0f11151b0606030c0a1a0405030d090602060a090c172d100e0d080a1503031814030307080307020717011401080d1e0309 66
    0x21000100c070403506070941440203030387d900050603207440302d8000c020510150030408100180c40305610a0240401070700d000c4580d24902050385041d40042030707243c03c4208002c2d900004400c104991a40301a0541c054140004000e021502e00c644501074003c0f008506603c405d103076001601074400802e80113080b102d00c6800c48102500900e0140103110040c050030300010b280c40120f000d1310040c0b50788071035180c1b00c00d45400c1c510b4403080344000c0c020709180142c2d0f02c103101c0f81224004c0003159900c0300e000016070003021845d16150a02c02d480e00800141801c10b0720071030780310200700c2100864190901c82607a079200e20008000b0060a03500402c4070080340760210a055000e40218441c03041c07840500166074444c022819480b1410503800c3c0e06601c1006402c002503026000b841d00503a00c7e0044403800c40d150f80d50f180c1c4800540355000c0f503582d0344c4e403411100f041c00d0b204298014140741c40a0250700c00ca21000800d40c0c554004103002c00000814a02152446584480c0c2e105420890940040d08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 949843893 1250 949842643 949842659
    0xc3d27080a030e1c2105090a14030f012306090114100e0909062403100c05070b130615180903020c031623030613020102120304080c100b0a090e0106050406 68
    0x1803039010003010300308100036140c8664010700032101f8004000305415016842d0050000071482a4251030360140240c0c09003e4901400340201d034200510041500c041d848201d80152005600a003240c0c82100450010410804986103203406a4419200c10400d0991408142c4040c0382214465800c4540142003085e11400881c6040c040c6520400405800740c80040f410301008101001d194140c00c810041d0084000c56400020304403100c0c103040e4144102c1e522014a039600444541180c0c10100c0c0c241001c10880d8480d40e0150320102d21015038050620000c58016404100c00d441c00d10b580d000c100701070600030020120148401004c860002208461924480c8200e108040704050501d51032400e5101d24590018908000340050003190307144a146070002003980c42c103a0550099065020100407050021071003a07010f526501c0d920180c20751003510300154810552591b528080800d8000d585540d0f4170340031600c55400200d44040030703a4071640103100755446580d120703140440000c1c10303803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 949845143 1250 949843893 949843913
    0x102150108010203060a150912060e010510030501150e010510020f030f130b09010203121f03080a0f140d0c0306090501090e0f0c3d27080a030e1c 64
    0x4003507651b00d24041d40c900c1e1070120b4002d401c80e580041006104184000070384059800b01440c0944400300d0040f0312030000900b11681551030700c1e00903101140600521409010340502c0b58290310b06001200c0c41e24840000c1e1007411300510388640d03213074030074000014400c202242d14081100300f580e1352854000d1440d0312540c4010110300b00320707040d0040044d40d4075030481035401280d01a009546401c0d00c0c0e04450000d201c0c02070000a41d102848017248008501c2c2098901a51040b81016501c0e6601300d809400c1214070700c0400c0401850030f554803901d500b004d058030b440d40055000072a0304000c0e0391301603000e4240d513003002004920b000000141042150400c0c440e055010040d0340100030030340d082d02e803030f01c0451189503007200280000311419038440398801400b246030911000741141481c98520141440100e81001405070f071880004e2a01c40d6401a0011380e050b078408000624000b1800d4450061081c0601403198141c0c4014154603249a0044070301c00c101e0f02c0c0480e1550310301d4510f03895 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 949846393 1250 949845143 949845151
    0x90218010f0801090519080f1306110303070207030201120b03152d011e09140613020a0818190b040303110408100509031c090b150a060e0102150108010203 68
    0x104034402000500741d4018404c60300341d070b41c002d0f01610007402c000a0f4540300c85c910000860349100d01f0003c45151351349103c0540410900c0c40f4000404624007000282030400740304a90a45800030401d01c80000d400080340421a54282000301e11040c091590000078007102c41003c0c0c250040081400e21825801c0c0070358801c1c1c10320490300e1500030313080c100c4d101c0701d6040a0203864983c00c090010b12401c001b041444810a4a808a00c0099911085c5400c103886000ca80100044071400500106103000600e624640104100440c1081400400106200390103046104021048000d040e0350401c1403106140c0044c5140c00c0800301c03030031450030034002807003128203500007407070480b42c84800c804560840b0212030084e0f0051841130b004d09a0305008240107000380384140302c02c1100050801400706080c1007262202400500050b803800d29100605008114060100b50b10502c0503140c1d5440c040442960380c14601581d2440304180140e1419a0b03a083e1880b03402e580c00000144400e05400561003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 949847643 1250 949846393 949846409
    0x2040e040212010b181009110a1403060f1302040806010602060405010b030106120b250201020702010311040b04170a2102211905040f03050c10050c0c010c0609021801 73
    0x10b415030030040b45081340e00d03a111302a40b041080404401d40c4100040740b9030042403402c0c20501d441c0c0d079441180201c60a802e541042c240300172601070b05c8590483d4006040d0b85036000c185281d46006000506031410384406188150341c0001d602c8a000290790603280600310040882b0b410f541c640101950f41d61084504640c150f00b000601145424103019503821501002e521112540307655a074100210001410b071900d41d40c0600c20010411552080707084034060030f800042c0e4030344203400014150392185014440705001004100a01403a030310442c1e04845e0084405c0818950b60040d481c200000c0f018090018074140303060304210b0035100c801000c610f446808035085841624006016054068859801c0c04030a02c008900003000304504281010545060b514080d00c03112450740c1c012590b08103030341c182d201c80f00e502114144030810a40110140c00e0541c03d1080039a040740d924001400f00d14100807600f40c000c820005150800158540e00803d01007221114040d4003103403000910859036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 949848893 1250 949847643 949847659
    0x405060a02160f0503071503020d2a0801140111070803070b01090b0103090b041202070b03090610080604120e181e160203070b0411060c070f0609060f031e02040e0402 73
    0x3d0602c410700c8910304448028024001e018075040d51040c0d092046801b5406051f000c004100f043c000911920030403c01e40f06c144100311903420340c141c0000800914060510808034010b0114194070b80c0c1140230b8041c00d103000340d051140070040c00c2c10041e01d40e01041003440b0105604c010070462005c0e150680c4c052000405c000034011340110184c4500c00000b80050001c1e00200d00800c2e45041140c2c01910240100c80380c0503a51141049942e1041350350804c1078104c0d1042c000f21248140c0b10f03a00905031072004000c2420691600c0300301c911043d0b100c0c0280084803001d00400e8582d508603904901e41c4021080d05031070200242c03500c0c103d4892040003c1c540e410006035003e00b66000b03a0440e1a0ba503401181082045e982d4070300c0c0c0c40d40150080c2c900412460080040c2c0d42c0d550000c158101d1014050113003a403600803201c02010391900b024003400304007036040c00030951100e801d8400c40194a000719618407a60350080904041658108245000041c0401c1c0404003030b0f1058001d82c82920104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 949850143 1250 949848893 949848899
    0x30307030504260a030e070f030b0a0c0c1205030a140c0703030e070f0b0d0e01110d051b2b0e150c070f02011d04052e0b040b0c030405060a0216 63
    0x8864000f60400d6143c190750910400b0300251080d4030101503510080122002c085e03d801207140400320f5540202c0e4512640410400e0608103406102c0000b04c90741881c4c2c0340800c1a50300c2c00303a07440c52107010000300000400040c10b0024190001c110b0002ea005445045040401e80d8680c5035026a40130f41c00700f8203158500b82e40c4107000a0341004c507000b41c1c02c481d810b1400e194951089a10030000b00e0100c0e91640503010381440288140c05803450506a0300e9078860100e540c050650b40c00610010144600030fa50f002c664056404842280031544002000c0800140079107442011009140961302c0c509549182c0200c000100289406403440a140e41035031840444001881090401480c0d00301b42c0044c000154020720710034170502d103600304c051300a9036508086000c450007101c408020b00c60448a0b103c1c903a81421110f2214006404502910341c10a0301ca41c513035218510501904800000e801c0600d108144141d90242c00000c2c209540c07801d14100080d5500d500c1075094840700391040c800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 949851393 1250 949850143 949850183
    0xc08010c17060d03050403020301063512030901141f050d02030c1005040b1222260f120601030e071203030b060c01050a0e1c0c110111030307030504 65
    0x2022808408211807a159440206200d241e81c1d91407401c0b402d0080c00c0c080800160341c00c3c000c000150010700074140e142c41850003406041204069442d018091852507008a4800070880140150a102c65540c1c1c03600c071045490b0040c00e100c0c268111003896441441028140540c600d800a003202010f81c92080c3c40d8001c0242c43c91103210f00a505500000070490302c0c2c02c01c00240d021050311424518202036442d00c1d06441523200c400301494401454003001200082d9107828072105042920041520015696814241c010400b02c0c0002e205404400315510580d00d08039080d84401528407a02c94000d0014952041c405450031400f007400d201c0072945502d0000341d00421a91b11143c148041d503c661019001032280900306174204804102c082c419410902540340207000d09107000a031004640c60300c5041c0003510844400c500c3c91341303001e4201c455002c20041e5840da000030841c0c3e0b00d100014016185816000d17000000307404040200007200d50164045440f4500801d01c8200003400f80000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 949852643 1250 949851393 949851407
    0x414010c020303041b050603090c03100902240d11090a0602240907030f0b160518131d06220c060513051c03120504051203130204090c08010c 62
    0x2008010703801400042d02140445e554003000c5100c3c2400d020f07526480e10301140c030340c0c0c3c0111a101410341c804150031005081c00c00c00300c920048500410050307640c040e800203c1241c0c05441120710100e0b08840820002e500d43c00700c601c45000342600700084d025003030b56400150005c104c07692282c14641e0001402500218111211615081101d07203c0300300540d82c02c0e86450301038804a00b038030070607001000042690101c5980380d401415840c00d00e14002444042240c0e50720540301c00c2207801d10100079100301c01490f1501d021000c640c194500c0980b020504000c1c603100c00c092031001b00c40d0304200020b00c40070940324010b850800c88001c442d28250950014006001c1004146078441c40041091601c600040c26800451403c1403001c180d032100081c02c103569001009039595920352605040681140d9519a6009060710501080c9015242c858903102c5005014800b1a000030001d840c0c8400078a18010740c07640108100007060301428521b81d0b0420701e01030ba210700d40c0ba124914840b00e00540c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 949853893 1250 949852643 949852661
    0x3070c06050c190804030c08072f011b02031f0506030607050c1507020f0a030201020d0e070e0412112a06070b15040905010204090c0306050108152b030305041401 71
    0x1d441c250b10b443c9074011214204001d0058042200c08003104000443c075200500c5414010f0329040324207101544880c0c04007001e05902203040e155000d981540340d030042038840304080b4002032041c9221850020a0410700d94a1000307000903501900c3c0401586248e00140c0501025812a081da940d500c0c010b40320361240003021175280c0c0c051074029000340e460f05a12507000304036106440c0d194400701c89140c505030400600700c025035004501d0340d004240910130309900c0e03c001340080c011070385008091820054003402c090030401c008880744200500454541c1c1c0c085420f9001c8a003032103107184240c00d032480007400381c04804010000c000a035180401c295061542c000000011940741d501c50b1243c104a8068480e400a440d1141000412001c0c4090001031540e0b80010806991214004044074195008581485600c0c0306000c140704001d2010b0b0241482528004000800f003850108100048004003406000c031030590400c1640c95007140e4003a5109110786440f402d1900f05560031396403590 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 949855143 1250 949853893 949853917
    0xe06190b0613031e020306040606031704050a150908150702010b0409050c041d011a0a05120d0e01050d111c020307050d05130b09070e0a0218040b041103070c06050c 72
    0x542440440c801d02d002c03502c81c11004c026400072504581c007082c1031400480c0c0944400d80d8980782003050182200240740a0a01c50310302525050030003001030440c5a50b4080e03003c94034543c03d50b40303c2030350044001401074410b640440700e00c4900c1d0350404240900c201c80800055080144400c42d038281750003008841603010b0050a1180502c9050000521003a08180c000003815000c1c400e100350280305846003803205405000c0800031450130710030540d031542d00c41c034005d6043d060005800803000c41e030801581e8039481e00c0c40e400040b0400407a014080d5500d142d0140b03103411400103a2540701401800d0050400030311046010030715010204030b010071034a004c007040003002588444129684500d5002110780703400d00c01c00301140c07501c52160f001120601c44580c04550709000a51051459035400807c0c00400d601e02142d1032049982440850000d5006644071044c0303074169580c6410050440660b142035503143d18020134024038101400c401a10720070316200104000001c0c03c0111903070780e0010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 949856393 1250 949855143 949855177
    0x307020d08041709030c090108010209090f070219082214030a03020c1918020c061f0b0306040e0f1c0e0d030c0c031a0a051503120c010e06190b06 64
    0xf9403141d26902282d211503040c060401e04032025502c456500380a00008400141c503513240364180322403128003400c0b0041c0740012504120066a000807820340608000503d08070064541c58840310780d0084260718400360071030f110004001509200018121109542504084088941070503180c0001c2940900140c00044081c2114180421020389050b0150328039084659124143d80c02080c000d1520707411160001507500c6605402c1002d2500886a0900c4401c0d0720904134018000380060310515049a02c0400012415a1503034058004d1074800c00940e440e0000312144141c940b2040201101100240044040700c64495120041e02d1400a48140d48030015034a05031380c000d042c0102207908510345000480020030b07c00c201c000d418003404005e4010304107254080c050b03800050020307402c200b031741005014079900095040310300181880c9443c0d43c0d85850240c00d01401015a0150082c4106802e00100c0f0b090100c2c50300540150f0441007160240000c100f0115210b100a801125410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 949857643 1250 949856393 949856423
    0xb15041404120f0203090409050a05070512100b220504050601091116020a03081305090a110d090809030d0c1205090904110102030d09080304260703180305030f0307020d0804 76
    0x1c180f020120406130044a041451031000502a11004e6400301d40b1600b00750516000c018040205601500c02100d8440d401c852010f605982d8080082c04058000d40301c0c07107000910340f00c0050041411013010200b01a84410300200c0014103c107940803580c40c0306000000800e034031a440fa8941301052200b0840c0781c5041c480b0300d44246103202405980c4100004000400140d180c401042d1b09058018840f00d0710780b501d002c00402e40f0b00203182c445100d0500009058260921044076007808403130300d00089503000703070402c51100e0061402058240c42042c407c10303445a00504c1c800520780c400c207030121800300c01c03d0013103d440c051407102a82280114000c180020815500f9030302c5960107104481c200000429507800b519a01641a6003d010002c21b00c41071206c40440440041114201d2902159085481c080769205e41c0b10041e0410a0b40d80b81c9003801c41c07401c940c0d0f400035900101104c2d29000100d40c1303100d103540250340d00e00251040041401c1043e0180e402d880c821fa4102c2c8a000403000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 949858893 1250 949857643 949857647
    0x1501060e101110060e0708010b0702011715310e06010b0f0c060f061207031203090c09050a02130801140a0c051c0e0f0c06041406070b1504140412 64
    0x20b050805861a401105180441403116206420040140c40010100d0303050890b001f07020010180c0101d10010020424030700541d81020560003000c00d07886103c0c1c2c4507a070380400265049000a0419804819010401c5680c56200403420a428905426030062464140d11008907000034100c00e406030040801000240452000f038500d0b11100c50300380c0e20f0b21701000c0456040c80c4c01114501ea4014410090089a0a07c01d681102c0005804020082242191076442400c2d1012448a08158a50b0050810080024035401c01007c400f1014001030034100d500310041d4210507650240f050260800088100f4140a050214105040c8440c0c6a0712980b03120809416408400303000e03c5002c0241014200d000020000c80ca00c0f90880000e08600035541c041c100641c40e440e200c561b500c02d240c82e202c60703607078442141d0490b012400021082031001c00072030f14a0084c070001400041e202d0040000b4040380c0c50b40c0000d219422101003005001150303030410401000e4030040d007400c001c0d40d50441214 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 949860143 1250 949858893 949858907
    0x21c09020d0305030403050d06060f080609040c050906010c0f050304052d1912030c0219050105040510090e010303080f100b0a030504062c0c0402030105011d0d0209091501060e10 78
    0x113000e4a0304034039119038140401d041d1081c9d68003e00004440030b4000c6406070b4400419608158215840300c80350034030ba00e440c2c4440d1124082e0034894000840030030803d1f800740e00e030f904100e54170440c85118881d003400e1558403900144a500d00540890503a401080e01003110403a8020a202c245800911240140800201501c11f06840d0a5030144045407a59010b050289502c0c03096490202041d100c0c0705002e010341c10080b000e0710b01880c18000b400561780000594064900960f411039500b84100e40031030b90071a080d03100648000b2050008001d16a0180140c1c3c0b050020484200c515217981406107000380c2548240e02229506000412102c0d11039008250042e000b8400403402a040d40603060016442c01d4110b00c155600d803c44006030b5030180300f40185160220340441c2590f24000028241000c0040c508161081c030304249440c40c0d944510345121140c0241043c0614a8000040ca640b900c003200c4184102c1c0d0320300000102c0c14441e146460404601a010b0b01c000c81c43c651094841c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 949861393 1250 949860143 949860151
    0x150c010614031908090909100b09060a0e040203070f060c0507050f150c1f090c090c02210c030d060320062a0604050d0f05120708090a0510021c09020d030503 69
    0x21310003c0150340600d0340d6680501d8005e4250001401aa00c08000ea200c203c0788803a51140c05910072908120b030710360340e45552130308844c1c071072003170406990396480000d0401000c2d400480c4c50f601c1c101703400704442c2d0b4884200c84006104401300c800c01503c80b41004160505841c02d160320085424810024214070b074050107402c440c4804a421748400000800303a241c0649415402c450742c2c1d030743d90406014140c2c210f00c00900070320004109005040f24001d440d19640e00388003600716003074400219503070b0044084a00e1a10401c094a4840240f01210806850588001e844401500300c0e4036007000c0b00f600e801d6110802c01003131940303040e42d50900310800400301541c6000c0c2c01d031603003c0c80303142e80300c24001e8501c60384c42100506110004071801420705072100200008102003440400d60300f0040c01c1c02d01381c114102c0c0c103003990160348030140c141c905108483c0042c03103400b4840c1c1c2c0200306800707600034251130303034090a1010000e1860b49282c0101c442d4054040d60141c180410180030a0185000b1500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 949862643 1250 949861393 949861403
    0x5120610030b030a081c053106090308040201080a14150d08132c0a1a030a031e02010218060702040b181909082205150c0106140319 58
    0x2c1640c1d000203040c640c0c010b505603524400040e6840809268010004c80418149010051420328036450518952454401c1034401407204d00074400c6000a000349a92035032004041c0b0000c119880c0080001d031050350200c4c045403203600424400403103805488021071350140208415980e00b510711030740c2c02d109030405401100107081e08002c82d18600003444040084248a074499160203002c250001c204005000e040944200c141540c542000d846a00a6031014010440350500c0103082d001785049000203515215803500780c4101500400d4240040405525102840309044804d03802e030701c0703403018001c01c20041001520309494824007514001d400a803001032100e80341c902283c0b4095600e04c00001c1e0101c40400c00104582e840348240074600307400400d110800c2543d0300c880550040d2004844045443d120b1400e5440c010081e07030000303040040048a424988002c1549a540300c1c0300f0301e81e400c0d400d01c100455100c44006050311408000780040c0103030010f0f200c039400144174200040711 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 949863893 1250 949862643 949862651
    0x804030f0c021f02060615030112030528020f010e010501181d0a08071205090a050d05150c04051e01080117120a03061401170c0903030c06090f0601060512061003 71
    0x1e00340c1c24040d80f0010500180c00034641401c00c0703810050080c00150001303290b514100014404421a01c00740210b043e4103042454440028420741060342840100d1840071032004e8100a41d032590024060030403901090080102026000702c0d6400c0e54824050b40e2461010100d071101219115801030310468020200c6050002000450600b070105804041d074540303a01060b14030601004103800c0058080e1414140d18101c50740001c15800d082c84d11075544a8114060702d041806410700024801340e4900380d0089944c83e000303441c4038594009000303580c0264455074602c3e040034403000007400c0322481610707804000ea2801c0c40507403209080d280d43c010b19019140042010318035540252001480684000c10003a00700b180d040c104c0c03074a40c03507454100521109079801200c9040f03001d5411100d40000d0964502c04203000c245180709802c40b4000603c2034a041000103000482d03038240c030345440415154181da03500d60484075401400c0984402540c1c20703010800c40d207000c6180b181d01520605001c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 949865143 1250 949863893 949863919
    0xd1b0303090c06050a02060708060306070318020405070504081014040f02150d0603030e0f281d0a05130827101e0c0854010804030f0c02 60
    0x860310303141c03980c80070f80842d80124681e0b2280d501800307042e41c02203091506521600d050b90021396281805801c6030145542c0740c0800104404844007501802d03000343c030034800780c200882d004085900910034003101c2d0003085265400050315003e4001c0307440848120140d03a890315200c48400200c2c0801c02c030703032103a081306051201001d050081c01d10801c61940006e0f9107071031810040c0541c1142d0a11500c110728a040301c2d1200c0e6901c80004803440c3d1102c4540c030b02d841407840c062904840c1900b0440c10b0114070115030700c0e07414005840c58420a4080024400c0d0f440e40719030001d000040f0f9900420040e000d0050050140c20034400c00c18041916844c21500c2420b40041121456800b6062000422203c0390780c002e0307400c0d600d0f0005c10755803914000c1c80b4250f45441e080107502a9004000c000c2201b1081030290a4401524030302e003040b1501401840d0404041318480b140c0c08892070719945508a0b40d468156004582c4244280d8150320755082105000c80304071004100548101d0b80105420081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 949866393 1250 949865143 949865153
    0x7030f140114040b160210060b0d0612021f21050618100e060a03210f08060619110304170c040204030305120403030b03060a0902040e0d1b030309 64
    0x58000d00410303a08100864014440d42500c200c0444120032020b400309110014800b0015154030412240c081c1614076190715080b8109101d030030525030301c0303403c0040100320340d03103a4001005507001c00407041280c030342e48504c1203c101542e034001130740c8500002080c048030702030040711030280182850840589040481c0700141c14200d1000b401000d03a8400410030340c2d040c4be03100009000c5c1000a101d03102e290000c0804605100c0380112241ca000c82008134845444140340d0790007860340456001c0c1004200b45109036a4245208818001342c7c2d82004002c1240c002d0880d1409508060301c0c031351902c12040c08181c0c808440480c06020807013601420000103c041c4054800b07803130141078441c440038158880320b03e0000354a544900c118030400040000940200440314010705d501c00d804490b40d5a4101034004006648c40103030180502c2040001076040d80e4060094507100712000c100c01003c0c3c0603500c1c0e0b1080302c6100500841c41c494004400c0c1120364070302c80c035418464500842c44000356a18 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 949867643 1250 949866393 949866413
    0x13060b0310170f060a1d030c060405070f0f090b03031608180301020c06070f1b11010815030a03081b040806010509060102030c0a0b0c0f180a0603060303080609090703 73
    0x601082051224140305400300007040c1c00210241000504035007503c02002522140040c0018462964440340d00342d80c40100f4010100b201000c0c800e072a11030320000c40f00d581382d1a089804a0f610b026032100802e40b0b50308604d1003002e8070706448000c5203460809580c000109800c8007010b500d48400e09c0888a40c41107407600c9411a4490115030341c071882ea1400038002c0000401156100303900602c2203030008100020501d60181940c0b80c525003802c1000c2055032082e61200c645100420101006814007215180100302e07888283c1c5c600c0003665444c005800107a01d10700b0a030b581904081510004a842000c80c640c101000b007a184220301383e1000e6a103002c2d031060340040c3c3c0c150409401003000d46401d0807460380c841c0080c0007440c90034040b11401600d5400081c002002140c0920115000510081c00d540c6401030010540c0e60350903140440000c1507405204c158072441e0f1420009c141e05100b030003600c045030750544415549440300810060807182c0241101018825244008003090110304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 949868893 1250 949867643 949867651
    0x30a02072a05090a1427060c0a1716110304081504120e10050a140a020a0c05040c0f0302071106070b010e131112100606050c0601090c090513060b03 65
    0x18851500515190910443e584002c00e80c3c5025880e0120318000c0e03000000040f94000d848103860038201890007218140e031000030b0001c550b18450701c0200035000f2120170080032419459101c0c81c0e41c941c0000c65845c003420003112110b14010458107011703a060701903001c0342440c1229030107603420192502c1741c1d246000180840b10b803001602c0340601c001d101c3c1a800300c9608009520388a401603440d00c000c101072614881140e401c0010000c0d500700c40910580141c48840f0500600e80d60b81c03544440c0003940c40c0002c4c17030242c91080a403400003d461500380300d05000c1801c40e80b82c0c9500301142d16001d0f0000c0d0000642070701c0125040302c0140d00340d590140146003451151083c001d003035040560804121000904841441e0702050000313020030348158440b1440c00c0c081314403c0bc8140503012044c1003416004108007854204000400d0064001003d4807070b0001c000120b80d00351380e135240001d05880614101401090300c524050100c3d0030141424072507900019008503403581d89451a041642c4115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 949870143 1250 949868893 949868963
    0x30a1202070e06120d1103040902040b0c01180c12030e060d140117060c03041a01080105180a110d140f0604020f100e041a0301050f100e0408030a0207 66
    0x4609221034441800e0050304240251801ea008010b980f00103031740c481c0006046011711080000840d900d0400b0400c4030040c10000c882907444599a24503512180c105810303090040d424001210020b054007054030590300c2c0c1150902c003a403460408d440c91380a525003030a408100c1c0310320460580e61242401010000e00c40400040c0c14240400c2e5003c0079001a0400048400d29004003422038000148150700140d42d40b46595980d101c0380f5140ca1008a0402614041500c0000010f81c400c010342c49a0f100b20201d80c1202c00c903030080d6170481c0d00e900600b1802070400840142c0321086081c404449400c0605c903102442410841d11401da151103003810522401e60712520820046060683c0a158940702c03d541804d00d00b180d5800240c151098846905d000d699103802168280c211880000f00c0c00d400940200b100d4203082c400910303501c108031010f510a2240c0700001695000700381030700344101e403c01c950034219100c88045001035400740400351481011003a014114031a0502c4081c0e0b010840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 949871393 1250 949870143 949870153
    0xb0a020c03091507060b1014310302010306060905031504240c12110a0305060105190509040b030f0604060c09170f06150a18023c04061706030a1202 65
    0x602d0303c28186e17014484124041c1c00f892880f02051a04403a120318201070a42d40d441c0c0714001075100150380c81d11000c0d81c0380028420071101ca00070205040c00c8003980c0c000c0c0d0b024400283c484400380c45000c410701c103594150b4452001c1c44500e4080d1400c0b16049072164100300c419020444281e85207107074502501c503107190340b481c00083c1d41d034010888100a204091007400b9401c1140c20f98041c0e40a101c10300828107442d4070000310302e41e00c81c0d011941d441c0302104143d441c0c41e00c2c6070300082080d00500d1a0900503468980d002d1114a4001a9458110b40001c01013010f90741c1c0b50341da440a440441440e50610190103030100e03440224010620a01c2c1a07440100019030300802490b1910501421a400300303c96200e04403c1038880d0300780c00040c0e0307a8500d03002101403020700d0300340700030f108100c40c0c4451150004c08000007404480303a00c81c0900300c03503848624076425001b1500d44d240300300e11606020400c012885841000c8580103143d000c600141901c0b0800780c00c0c0c8882c00700103031802e0520010313048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 949872643 1250 949871393 949871407
    0x3071a07060203100e06030d121a03061e100803030402060a09050a0e07120e0c0d080403150507090e0907261023011503021e040f0e0901090b0a020c030915 68
    0x4044016800302d012002803c0b5810a50005412701981c60019006e480c1c0f0340d4080c490903d0260801e4011200240c1100e0072403402e00c0001e05805072070802601caa025060120307040901c0c0404000a440c40c44000d1840d5440301c0d0300300010750348000400720034806682800509541c811a0b0100144200510b59211380343c0010020070b0803500c040b00905481c903045403628840c200050400701040c4c02e44070080070b40c0300c078282110b25003e01d030f000902020401a0700503403950301c1c1d08a14000d9003140c2381e49880549034541c0e40c08881007162010010340c0460320400040b000a6000d5040a06031801c0c1c03641c0d2910f0f00c0c05981030003007032040314502540f60a50b4a81030891101042590181841180c28070750400425000400c006000042016000b0469403061107400300c0c1950a6212514465036941e500c0c008103d2016181c811070604030700e4180040c0c2c584506004004075143c1c4050410503c1d501c0d80014002504030280391200752000384440700442c1c907080100c11103005103801c84d07a10f07442 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 949873893 1250 949872643 949872659
    0x1e120b0f0703020c100c0309050a05010e0d210c09030b040b0103020a0b040803031f0815070f030b010e012d0c0b0604020403080d0b04180813060503010503071a0706020310 75
    0x40c0c00340c81641054410400007a01401c082044030000c2410100420303440c420110480140c40b40b82c4028019008041811040210542c0300d41c103042c40103000d503007407071146010aa81c833140740004501d00112043d00c0179010302e1260b001d10701040e00c5040144038503890b5203c242d05000301f00e8044501034800e20041c0f066261950200d03000b4101d1011061a1908083c145516400003070103d20040f008005016400080070080a01421030300045540041c10301120400c0c1210070384100001c0f40c204c60350010400e10078002c3c2c41c64400107840b03c0e280c07030000500465200c0307130003400005030360304010080300e1034202c56200c1c02c01d144c0f40303a842c440c0980860414028590300944034611841c8100004c0000130b14042c1640c16070b60825000042442c4420081009048107242c0c00340080142200e034010004000302a02c034205842426202440d1100c10658461101f80115a41030340500c504000101c944428982c280c01400c900b40d00303020440d5203080682c0c10a43e156004801300c02402e0001d50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 949875143 1250 949873893 949873921
    0x709030c092a0c06090204090b040804150e104a09090a08070501020f070b150f090105060c0f0304090b2b0602030423011d0c0603011e120b 61
    0x302c401001e105070501070341d018000a20100780282284e440742611825541da1750b01c40200190040600c003440c1c9460b242410711540a80194620480c6202080c1e000c50301c07400d81040076440141c54445480d803050815070701c00454441001e4040041559488034060104041d00402c4c1000c6c0d40030441c01c12898079164442c1c43e203038454002d510702c8007045241d560009024a0300f40c5c104404c40c1e0f85400600380726000e071081c0d421a2825441c0011884c0030014800e211520401c150009a04c0c0e00a48a0420030040d5410190584c81640d0348010301c12403034080014060b00240504891711680d04e000100e04507041980000b03106507640c1c14080b02d608003c11260401c0245019444151110707100340d181d0b406940d00f000d000b2a5011000808004182c000300c0003050070010001102d8004140084c007030415880555450006521001e101000c0010641104035004007050f04603030070000c08110603622840f21407200c0b040320030002150341d0680d9841c2d481c6070140c0740e1030720507161442c2c408880d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 949876393 1250 949875143 949875191
    0x30030e01020c060f0a031509020c1b0301140414030d0e0c01140309280803280204050f0f01020109020607050f19020616030e1221160b0709030c09 64
    0x240c0b100308030078013401d5490400c0f84c42440d01828000342d41560491035081e580519001068124400514414081380000e407807030400c1c161200e03414032076002070140750a03900c0c5011030120460182001c50001240c0b22500740c032811403101202d04220f9180c820500795001b498183e10341c0d40081e003040c12556440b518410a40400c0342d8481d2440c00d0444c2c156580d548020815114002076241264840200c600440e0005070000c0c551516414841031521401c504800034100754408035400c0e0103440c5050094508580d80101003204901784c4005000d41036555012450440d5a00c00f50072006a90342c0001d03200c000d005000a100d040ca100710407e140030f401d030460700450301400300040010385c1e030a8129000c4901413603c1c40031040742413800f5a905c9a001e00c2c2207a00403a455080c2801080000d030b80d0381c1000c0b0025021b01400710325544d10406100d4082d0701e0b121003045410038808039400103482c0d034109050745407030348401c1d58030b4690000103151900036003121074880380603280c200d040360900c42c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 949877643 1250 949876393 949876399
    0x50606101b0b0a0c2309040609020415030b03010b060906090d0c060513050109031113141f140d02061309020307030209040515210a12032301080730030e01020c 70
    0x517451a81200003202d01e055200366080c0400680f07100d490b2103a0300060020080d119055454948070850b445030b03191202512400680381090078101868140a203420300100605041d160140100030301c01c1c55030001c1000c982180815000000090160746a83d00410b516940d841c0c0b10b01c00d100c0c102001c2da03201d034011410050000d41c03d0000c1030310283c0413655028100e902415003295103a034180030303000c00c41d9000c08242e08402000340f024140c0d0030000072920001c442c20401c540b5003c032015442e690145607034201121002140050038074200401080070180e03072400089641d90203d20a07a4001c6600c84002500030a1149043c20540070b210342040080480300035000c851004500034098541c140c0c061044078480703c000c443c070140002000c40c3c0d001084e00504c0c4c0000d000141c0039140000c036502c03020b908201c503c9440d00004154030f060301c107680d020700351541c540300b5060007090b0031141d11001d845e401484000d45445007420201914401d0729501024500d040029050000e4100181c1c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 949878893 1250 949877643 949877657
    0x7030c14011209020d300215060d0c090929060f040f060e010b0301260a030e062106010806100e0415050604061205070c050606101b0b0a0c 61
    0x22103030781048000118009081d00003ca4041500000e1401425810b000d001c048640050101e00c4d41c68071040003c0e40c0400000c00b10405202004a0380d581d603214019001e00c0c40a408241c1030710b0440340002c50180100e0b4004003054644960b00c0c00c82e900014201d031520003045e50107441146071006240110a160000441881d003880460b4018483c0d1003010304c47e5075035401c0302190080c580d102c034014142c986602c116660711b40e030354a00c46034420700640180001c41401c031140d8001481e41504130b0b082d0b00f005007000100d6641d041e0b581548003440503601c18810300001f180340310060b82c94500c20580c00f82b44441800c1c20303c0050902d620140010b40148111100741c1c56007070304442c070004654020b03100000c0311441003004120401c11034003d290b003c00e0020f00003039140c4e4002c8502250903030040d020001500c81d01010364800d4014240107180340c00c10b0001032542d1821548041e4101694206010042010502500805c0c00d001c8111906070852050005014881c840c4282c10105800d0800c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 949880143 1250 949878893 949878929
    0x9020a0909050613020420070c0e04030f0f03060e0705070b010603021e0306120a0b0f070f0f050d0f0f060614070f0215090301050f1936080c07030c 65
    0x9480f084028411030b41d070210040039404540791035000d6556020343c0d070306090f80441e442c50114201d500500c816242c2c1c121244001c10f00f4041c00c01d00074042c42c2d240e15420310b0310103102c10664260031031030030715028550307180000140448401318491107941c0c55510b59555041c28a8a010001e4048c0c1160041500c10b000d6a185040a28001c00900281021554403a500c2000040d1509002210384205c0c0c02104044403c1114550400d80107290441c5c0300101951144411180c0317042c541c00c2c0200090742d4203a803034450344c00783c0c0080581c04010900422032000c0d4126005c144c4230742d1042d802a107a40c0d982c3c20801c06034071600800d02c05000214052038101b0648609028001c601000307446912a690f14155018184e0100c54080e44c1c043d0081c80540340c082100c1e42c102c5011200702c1c0100c05440c1c1c0d00c403040c800c0d500c031b02c2c0741d240c4402140c0c5407002c1040c061407034855510343c0503000440d2415550340104d42140c003c0c3c89000c0d004802498944d04600c2c000c00300358401d504c54103511100140c02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 949881393 1250 949880143 949880153
    0x609011104050103021b100b03210706051e04080a0e011803031412040c030209070816030b010c0203030f042603040605030a06030209070e01080c04050906090a09120309020a0909 78
    0x20307400c440b401d10300035803607421451103400c940303100c02080b0b00c4511071100100c102c1e103e02d4225014a480032026504042c0200d81998102c440070130015044a40400600380040c1040c2e1080d40c020820b504d801d0340e044903102921311101c80603241aa030062020482803036580d817014288c03100040a2902102d9511101d10b101d400d546036001c003c007807010015580170311940101c141d40300409107510501d29030615040c450510710136800261b0060614000040c2d140d4081c0c088640982d400c03070402e04520340c01c90000c90003020704548645c10405140c51900145e038003000a441000c00c4250340d25903591402c2d0348914101d10303002c40054501038046d03100036403c2020054808a0b00070f410604d80c0d03583c0d00b00d621401040203410003035001c84d031182031211003a0b200c0e00c00e006601080c5c903020000e03100c007806560035005601c6143e50081426000401c0340c10092201da4015810120104c1e5a090541c3c43c0c4a0b280c5400400c04000707581e070981e110a5182c0364038101c00030501000c1c00c000110b013a07121 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 949882643 1250 949881393 949881397
    0x30a02130504061107110f0108011212020705030a0605010e011502060c0307020c04020a210b030c011202211e07080a02160c0605090108100f03021504210506090111 72
    0x8200480c0740e403400041c042c042c0c55004015103410400d003c50380c2d43d42d203180101d101008040080d0144068101c0c062041d405460480e0694800e4040d200c2c104900d0340d01c004081004215203030442c01445800170340c03901c082200b800fa140c801c88000c10b40d0f604060303414030250710580c0720045a402c0901d1094916801143c601c2d00042c4035800301e65a9501c5d400f05901e4400c0111003143c200b1b100003090100a40e0081c5603082d036204602c81c403851703c1d140c119400192001840310980c1a0049a80c0030100e6005058a0b0b6441200c05405820166241040c110b00703e09850175042c4992440100702e241c414800342c040319070442041200c0b45080c80300d00102500e00040401d80c00ca5800290030105440141e10f1610b001d901c104201c400c140ca07032034000c0050b000301014502244820010484503a4040390313800a840400b1350a440d05891034080020842030040140b607000000c01c40410401d100304048810484038509150700f0035000d1419a1130044000e000010036490001c03003c4c2440c0414007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 949883893 1250 949882643 949882669
    0x51e090304030f0b1506030403050c06070206010b180f090a050601110a0803070c030c050604080a020705120c0405040c17060103030f05030f07052b0c1b03080a090c08010c020c0f030a02 81
    0x40b9810303203507600070412175401424103500c0c0d4414008000c000800d58090001c1c607540f8100b50580712940c4a41d0000d80e5594020f00400f8050b2406000702850340761020403401e0881c0703000348203001a1042c034000c55000c000a48040c0303009034031403040040a5030272110081c4c002a100300246811411901c5608182c00040d00c900300300541c150703160f01890b01ca950b0100743d0b59080030903104503080501d006041075100854000c09405402c50004a600e4001d06203500b544500d0040d20f104c18507501000003c040040040f0f0f4071100c091004181001109105c00c01c000031031004111950441c1006850b00d10400c1002e800c01c00e04000308940c00c0b5120b55a82d07040070060410613182c4034800c4002844c0014825080d00c030000c0058000100c1d00c0a4025040020301610b405200f005044551400c80d186003a000c1c020440354030120340c04d103c107a0710600e41035005a02d020412740e00c0d80490350a5540c4518001c00682c0300382c2d0f039001c0710b142c10113064611190131001010408000d5000c00c22100c00c1031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 949885143 1250 949883893 949883903
    0xe16180506032406040b2106060604060503010924080d120207020d020108280518010903140c03040f15120e0d0305090102071205030108010c0f0e0d03090504051e090304030f 76
    0x850990b8840d504024082d040c024005a07d1200d98125500c140c0c141c0224400c5506c25400402c07140d041c00340481d400d5800913a2054a5a800c1c00312400c007800390040e0100e001c0c0030199200200600c102d00c9031000c0c11450300a82141102c80c24010103a21024280013900c601c10072a407001a540c1f44103003c2590350a09021555507641510805e1070313000c0c2e01ca030503580d4143d040b2041000c00c0355886107106500913400e0750502c4022043ca20301300e40a1600003801300d59020080e01700301c0c42901c0500400354164044138a050f4495681c1c010541590740941401a442240d106d00c403904070902d6078640f40c4591007000001c0c803003a2aa66500c0c041c00c03142091540c1e03400802d8102000390100c400035900041ca03214000c071804801040e503070092140100c2546400718035100d140c842c1d5945080540c0b0395840410100301072040010403841600c00714103200e2514800100c82d00c070b50080a01c113a8580d118020b550a00440e0400c80800c024280c60860b0010132051000614400310030000542113 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 949886393 1250 949885143 949885213
    0x7080a1a131e1e050402180c0705030d0f1a091506040b1201030b090c1807030212160909060305070e040c080609010c0915020607030e1618050603 64
    0x1034a980300600e50740d5810704024a10b812181411140c03a0040d4110000c0b58025070808100200d10304100c0741c0c01d4400a41c00309000030300c4d03036001c64035403400d68001101d02e200d03a00e403030703c07541d580e0f8a594070070340c0200c80301c1c0e48402c1c401d0081ca50074800c082c50082e4082d0700407010403240d000070b030300b00b40300410303421107180e003645002c00648841c426500502125061640d8030149503414410340700d806d01c41100c0f0716456000203069800041204e412284020f41022805079110211010052008000e4000c2590a0001148162a4074403160103490000220f0b407451003142c030000c003444501c1d000300b0206402c0000c100001000050042c085800c010100c2d41607480e540f40141a800c0e081c0c2c840c603020301c60034050010640341907001c00c82c1c200b02601c03410301c03442c2d81d9900e54000916101202c00560004400140050301a4100100d2144201d065803090100c18603000c0c890035450304046480b00700701c0300c84050600203204941c0c00c20000c50003000161111051151416000030341400a031501d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 949887643 1250 949886393 949886419
    0xa15170a02090307033206010302090613020d1b020d0203030109020f0c030403030f031407210f090809031002190e030a08071b0609060e04090f02061207080a1a 70
    0x2503042e110034450040550305042d43d24101504242d0800000e02c04441074005c8900e20301001e8048203596051850140856038619020444845e1740102000d8004802400740d8400c51098401840c0750f11081d240001e046500070040c6a44020460544080d1b6101e650034030001074001042d607044a00c841c0707016075034803c100150144c034000c1c100c00849521010901004040d00450b10240650844e68200039190b9100302100304141d090302d0003c0072038240c43c05010304c00d01c5810703541a220340c858404204030301c0011001d030864010303d40680e014038020840b08000d15060083c2c400300c40c03080d2815070a2120701c04a011050440100c2d90301440744507403c407501070320f0034000b0b07004c15504003803165298a4107040815203a4003101052070701c40400384001c00c1c010300400b040740645544c2c0d80e6200030302c4104024800140782091081e6a4403003494070035030040c0d481800814000868210500c035a0500403c007070850000035046502e601d08080e0500385450141941d542c04450448281c10311000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 949888893 1250 949887643 949887661
    0x1f0b030a0204060f060806061606051503120a031118010503070c0c09091b0e0c16060f0e06090c0907032a0e010216120b09030c010c0e0a1517 62
    0x280d10034000c0d00942800d800141030341c03a04420408681540d19421501c1c1e880c0004c01c0014031680c4060341c01d1030f00f14039428010803d00d51003c0e0b07000c45440d0720407076144e120000003480d000d680703094004a0040018040d2400d507150048282c08106580001e0902c009400e0440c6241c50004140d41005000710000b20900c0c03241760010079141d0055030212541c0c1c0c0701d807074410107001804d8003500c000032034000c1340060000c3c5000b0780044908044180340700f612010500700c00d40d480311101110305d90603020a040860007500c00d03045080803040c000903600900d6181c0743e052150080445101e80c105c3c5130042e040e9120a00b40c2d50f44a02585030010f000201500038000c0b00e080c410030340003081d42c02131a90282940003e00c0b518449400d0302150f0b050f06d03260509030340d84039076401164018800310300510009400580c501d41c010003810140c0f820949400b2005003141c400000d242e00042401c0041c4440c0c0c207000c1140000741c0404d034201018941c0c5124042c0c1400310401800c80c0368600c1d000091700000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 949890143 1250 949888893 949888903
    0x70302160b0106170c0a080610020c040e01140603030c120307030603050607020a0327031101020307050307060b2e0f1119051b010f03150b0403060c111f0b03 69
    0x1984620710350718030358403440004c003100c0008403140d050500c124007040c0c0008160b015154600c5041d56400b1701903451806000705102c0c0d255810095225401402c00281d0300c1d0b000b543d0200c0e40d03001c0000f444000f510510520040040c000900942040241021821000c41c0c0200c08c0410402c403950f8945501c03401301c005000d10b92003e0614041d50091200c2d2503404100307d0a2a8003d64621155900d044820900d0011000096101d0700900c241040045e240028600000d241401645c0c04e000a42c0c0b5068110f40c00500111411560ac10903603142c0e18100d21704440011150b201200203a0000182c80c0318840300462080501081000250100c1e04ca611800000003c02c02610102d60402c81100742c4560101c0c0b040322035019516a00c003620a4410300e103910543c05a481c4c00c0c100301c0b00c7c003050700101100225070b80d6206460001080d02e4400c0300c0280001c6100f50f90001d02da08011b400100b14515110480205030080d14000c5046640b80a904180306410031000610201e1100000d01d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 949891393 1250 949890143 949890187
    0x905060336030d0b012604060914061e07081f09110702030c04230403050c0307111c0b010b0a09091506090b0301150f02030d060312090e0f070302 64
    0xc05140e080328044800210180590f60341482080c4802c003403030030041d10300c0385456501a20003081180c1030f40f040c0740d9240416422034046e2200150011030703601d0320003c55003004c80284a0340d020708140880c1000b00030040700d046071032041101081c142300c04024000c0d10041e00c3c1c00d03014a001e581c000c8020311014400b600600b012141040880c0c49245220543e40150609038464011140c01d0f00c56418540103a000c0e251754036200d5041c00c04003043c103032103000014009504000003400140c1d61020104001c0090500074001002801c0c02617007001502d2605994560042d80c00c0404040042c2d80a18841c0c10744010000050f19400400d1040340d05941e10b80c031000b0003e040c0a0313090400500c030070300801a41d4699644824440e12841000c160748020b00c181d9034000303124080000641d201700da0080388645a032050320310741010404154140d40300e9400c245e40001c05028080030740f076000100c1100610028400c0411480c1072080390307a4003800104410b09142c1c000807824a0260042c040c00d500c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 949892643 1250 949891393 949891471
    0x30c020a0603151412150a0b0d0c0e0c1204050303010e09031c0b030c0a230d05030706230a0501080d030903140c0a020607080903061302061902030f270109050603 71
    0x11884285075116650405a1f075004001b860003034100407504104101d070008a40080c43c55080924040c55406d600400410000d00480107010b040d0031030b80303a040c2141c080d80c007801c0119101d50409102d61950030000c0c054400c1603208200c14024528422126404501050000121501d0900119050030000700503160b000c0c00c417036008201c3c1c04111090443d03003a0000300164070701325481c1c10f01258141a42b4080e04903801401480000303090354000303007a00603401e0100c0c1c40e14468648814003001040d101415120b40312801440a11410040c00724403035050301d0103006004444c0c401a20a01030800f034002c40c08400030760b4528102040200c03440355603015019955490b05030070001d1b542d0300400b030302c24401d000304d00106481c10031103004825141d40003406c0524040458482044694107040307c1411b5010038054241183c2c4d010014001d40290003050580b280c00c0d4100e2031a20000c290b03100350600c00c2802d01403000b0b455240917658490890940b45020398065000d00c1100c140d81503440781 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 949893893 1250 949892643 949892653
    0x22020f010207270f0b0102030d020d140a0e2b1103040503120a09050109261c11120f0415030b03190b06010e0f010c06090807030c020a0603151412 64
    0x802882896203060841c12801010000c184d894052441502c8041c1c10b1980180d0060001641c42d11070750303000b8050a0482c0c58005481c90500182c1d03100c000c3c046a0709802c03036076114142e05240d0014850a09050603a0004502d5001c030b14501144100c0c0e1229950208410094500a0190104108da0190000030210340650b0401a505c0c002c542c408400100001c0320782100145175401840e03000150f62140030036000c402402c18400f0031208140804031814030480d0700401000d000412a60b10003078007076a074607041c000b10482982c9001010b2045108014080203130407002070120f070555042d21485000809c001e040e000d400ca02500700c441885606000d07445a0742d0444500780040c40c0d0507441008035035102d6958030015581c3e20002c0780d4540d0001e80d41041d01d0200d6101c0d184644d00948610b00000e424203081e00c50701110342100d041140414044040003095281c61008040106214a42880b041198030017130745403182f8500c50855102481441c0664031390714442c59a1980c120a81110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 949895143 1250 949893893 949893929
    0xf2406030b18270607080a230705090a0509041a0601020f12130e070903150609091a0f0925050402070309090608030c07210f0c0e22020f010207 63
    0x1a40310f005000301d10001e0645038909102c142d9000c03c3d0b1038400c01d440e407070700c003003940c0c81061210280a401640f003090845d0071603203030b45044130800d00754000c09240d07072a103807507004240038042c001c1c0d0590061881106440100f02c002410320008040c5c103083d24006445940782d40c030060f0304e449680c805a00300340c01000000360005904401825600035210107041e100c55458a00c0f4a200d0700580704c030030005404020a1011441c452030320144403441d0100041c8140e40c40000408a881d140d02c1200c0030a114a80745001c40c0d48580d145801c41c881000c03180071410000182e66079079004071f042d0101a01400990050360441080c40e03401860040c0c000e40d40c0b10300030b00e002040744410f8001c0e140c000746040d0f0007061420000044e91009803002c00101141420304411030341031034099040300c100c442c04401c1d410008400d00114103032548512004081d41d0b040c0030349641410001402e609000210103080219440b4444d009826250140d80007403802480c140100c0c1410004d41007104c840c2440c3d0101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 949896393 1250 949895143 949895161
    0xf0f030503190e0d0305090f1e010506010e0108040b06030102071401050a050919170f04060c0b0601180303110f07060c03120e03030c030c040e0a0f2406030b18 70
    0x8500c10056080703107280e40b481c520504012144100001c440c19800000d80c2c3c11400e01940c803260300031140b1421a855461061440d603e0186010003004803080c0110307c0c491804024003034150424000d082940d032084000000074007541000300302034003c504000104002c0c0d1020340c1286c1c42250000d0302200c114081070700642c01b0b0502031300c102800c2071412000610b500780214121890300c0c035610300c02c414000e0719150307141292981c105103040c016041188440b01ca0b02d01000b040103000b19150000c07010319500703100c5c443c00c80040ca854140f0007081709501c0503490900a01d400e0341c1d498105520041750089071a07140c00d56a01d032800ea0380c8aa5a404a081074020400e80c020354803d41d1072144d500e40d01050a400d9807600890a02c0552051000c01c0700c00807040c004c1c503848100003c105080c00e40e070b00a4003100c400306032003e14101340c0d00c1d10100308071406c1c6c1c000d4920051140c1c010055101100800344445119440341104050780c03820604032076030311441c21803041030092581d40201e041241d48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 949897643 1250 949896393 949896397
    0x106180f1406280605031608071e02160801090c06050a020309120a02090c0d06231c080310181a060f070506040821160807112b030207020901050d0f0f0305 68
    0x4d602d2000b280c000000e245c1d600c5415075609c13420740c50381c59034a070a804400406003400310f040501d040d40210329200240c0c80b4020701c404000d2516070000720301c14910717041c444401020354202d2020000f00700884050b6580000485407080015101c10700d0814106050500704800700c0303002988509002c050120b008100d03400741842181420301002029a10150300c0c8084889090421040e0103030380e0b1b03800c0c0900c0c08104941012006c28104004009280e444110740d500480c0c6111460a00c12003c1c031515a03e10402d0100340d0315000c040080c03034401c0f07212846845071044068400d000005940368020740c0841a155031590100403a801400c00c1d2400050681146566684035582001c20091082c4040225402000d6054603004003c03a0102e0803564514024810418805190103100240e481080701e801c60480c1c10084a0303d52070003140c807041042d0110348010801d40140b04100150366090480ca0460b54100c1791441820918a8401000241058041e00d15850003420a09050b00800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 949898893 1250 949897643 949897651
    0x1c1b05040911011b030e06090a030f050703120e0108190e01060e0603120405090a050402010315030b0603150709140307030602030103051506060a0e130b030106180f140628060503 78
    0x131038101c020300700402d005865034030500180001e80b0a85c036a81c050306048005042002015003409106920380d114480040c1c4255411640c503409040c1c204244800050300d1810402030341780040b54000440002403049001806005000d40800948a41c013070907580320749080c94a0500034044250340d254200306211040352080c0c003c3c0a01011400c8950005086400340c89009042e000da03034032410010401003000070000c1341415541c02401c0044500303981044015403283d55943d046250850a0500b0116041e181e04031605211042c0800940c00040d00c800b550b0031002000c0381b00c280c6900203898074469078000761601c2d1002001006014000c901034562944460304484a6200d00e170070f00c2603901c2102c00c48030002d001d00c003200000d40707001c40b07040c420500e14050105164072008006030840b03842da80080200c021720401150b1813142409080410305800204100c0300b10140110100b00c0c030700520b220320551002d11600c10002200120114408121101208180d143c5801030210352090b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 949900143 1250 949898893 949898897
    0x513060c171e09010908071502040b1614121813020310050a0803070302070311060909010f0501020f06041e03090306020c010c140a020c041a0d110f1c1b0504091101 72
    0x90300240c00f00d0414090903807103643c4580218036010540d01c030781c0d9903000381c1c03048049940d808200002c0d1210b00b480152034103907101c840480c0740c080a890000c0d401445c5403000c03540f03900070000b11080d0416000540711034100109180a6248030240040c0240b900c090609050500c04024401210782d00054a01521021b640d548055a11081801d54a0040980003001a406400184005640e400d540780020030060451400d0041030700014107510000d0b0000c400c0d19080b1203003040701e983e040180340400217001025005500745615030004011101c1801030045010b4240f40080510aa64200096400440c210744401007208294042e20209802a0000d600c145038404901a0181100c1e206c3c2010b40003004041d012400b80f0002d88404a403807150305540c01001c404603118022088102442204601c0b00034010344100b0981816140b2145d010741c01c510306888180764031b4680501c01540104000c1510400c1e610072100c0c0c2e0407070f03030405034016082202039800c20042e038030070f22440b110903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 949901393 1250 949900143 949900201
    0x5040f11060d0f05010312020703050d050d06150e0102060112021507050c060c010b0a05060a020c01031109060a031521031b0f050a020103050a18080c01110304140106090513060c17 79
    0x215000700c0c0e0309e03062800050401e81007504c01c407401d0b60084009204904004c3d00100e01e1035a1100c1c49001e0108030f401c048080f9483c0710500c0300c0c41d80c0c10300c07036580580005012034428034103a8006c140c03c0c1c2c491611004850100107141d000780b00040100400b6020000c0c0065941d0342040b0506010b48807421103640142001c8030007085134a270400c1a101c8510750b40e402000c03150744400c01100070f480e02625810029500b003110070403a40b01c035070081c450401103447c00308500c840c40c0c45548081c1c40da580305200e0003040c80c0700d070301c5181802d40d00320500c55050300c6e00703207202c4e0500b1944070307a43c0540d580001c00c80030600140c141004404504140c80703a000340c82c100100e0307076080420000d03541408205284504000c0000c000540e4410103040501c60120000403210380400240c211544140c030140c0d020070340c44280d503505600c02d00070340c0c001c0c00c1d25070410f00c620300702203526081d900c03d80800101300716140c04c40403010030305ca6402c8a803d14040380000c001d50911305d005a074030710102250201c00b0010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 949902643 1250 949901393 949901423
    0xd110403050f28020f13061406070c0b1308010c080601170103030f0c030504151128020d3002010f050f01030201050325120f05040f11060d0f050103 65
    0x1c07440070511003980789000d412408910511020a01c515012a440051020b101145444440e824014000100780007e102030420b11501c0d800c00a041c01103204100811400c000103856203180411100103c00080e212000100b4641e2118840d4200405030741c6811242011190f008081c03500540b000e072610110740e80901600aa80d88003408041c0102c1d2158925809451103407802a500c6030107031401a06181c3c403115010700700a009025500001c0c000a00684070500c184181c406c00b60103000161103158182009144022404801921583c603407000c000501188400068442e50200d402c94404951055010020245c00309030134015841c010700300c035801901d4421140500341301400391100d41c0c40d650044075a03034401028580e200c0d810090048045241c0110800c00134244e8a1303280718240c40c82c0007842101c4401c4504a80c070341c02d210500011559101d103145105801007140030540021300d000c075010b886108104124103241120028850b0b49641c40681680d0ac0781c1d1190383c403259 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 949903893 1250 949902643 949902673
    0xb0a0c0c06050c062a040305060f070206040c051003020f0316231803032a0d050a23160803041106030105060a0509040603020d0803040c0603050705070b06060d11040305 74
    0x1c80b900104a603000c2400700b032612000c00950500301c038403000c1741252400d4000d5a1289038001d0751044540c2e50020702407221b40e052022400e44d100c3d00520080c07034240707059200d180c07500e1103500c02c0300d004084030300c50f00008038030940494694001e440d0156076a4200341c1680400c02c0002d00105002030400d8042c541d02c02140500240c503104a252054144a8620480e402d2407c14500855051208005044c0208004903100051440202c0c1200004070500281030a00a0440c0844c0801c030041004901c00781e000700d4003140d003490494088180d00d085103c1c3c2d03421031140d81044e800024241c1c149034208030580c1c00851140e480b480c5400f94100c0d0760000c4c00100d00080c011250f00c000c081c89044002031041018203a207501c0100081442680e0b60040396903400f480c04262281ca400000300028800a100b1010040c580f40c0f40401a9141c2400010207074025840010240d0100313001141c0d00c0d945203001e41c1da2042c07000c00200418540d82000394032551107071000701d609004505420038864 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 949905143 1250 949903893 949903897
    0x2360a080c010e101d040b0d050f0d080105150c0115270b0117090c04020f09010809060402060406050f130f0e070302120103110102150f07020118050a030e0a0b0a0c0c0605 75
    0x110140c4800502c0e40c03100d1000360040d40c10b128102c2d0847da803a105075216580350030901d180140100050201082c00b51107030707414591007020300024405140c00400c89515004041e601e500c080555540e120620101464054404c108034500d40c2450000f001c00d855003201002c0b1980c1e801c2944000c01d9100d410440070507a131124045901081d48448140c14082c1d06d80700550740495042c0c142d54810150400040890700200d105e56214035012030f260b0f61a5130059007590700074400f00000d0100786415400540f892255015040400c10007080860103902e40c141541c41e0000c018802e94403060701e58040800c450340500c28102869544008035078454020310886600100c540d201144070b80c2142c9850080503100d4505074114401c4c040c0044c0e4080e590306009006060700e0034012110b091560009007940c4007400030075210303810341800c0c50010f200004c030190040c3d4107041003a241201c0c6030000b886030045a02c0a1060a000941c0c040103036402080c0d90301b00b6104a0b0341c95616070b210001143d0038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 949906393 1250 949905143 949905169
    0x90b060f0d050601090213092d05040209071d0d0503090a0b0a02061f082a010323060d1b030c0e04081c1d0c100302360a080c010e 57
    0x79403c02001808101441d8008101c4046490824a41c180e0f941200ca41111000320566078000540f41c0385841845499001480059680c6014001402d00340c002614140300030306518140843c00356000c0e02011088000000f400c0e009140c00700089890908513145d91160754180d10840b806d18001c0350350590f1500380c50808006500401c2c1b150f991a0250f8502d07003103d044115a02c00c40040050040701c10041c284184007031503a1100403240b401e14088880038000c1d500350626040440c141c061071002403030311100556106061800d030f107400000c05d003011710800000d0142c400c3d000d90840c486445050745412607100c1c65801c90742a50300e2407120400801941d0081c070716141040109101101c103203901110f40032109001800c00040c056558181514402c106855000036040c0010352824000424481005090a514000701c0303d0f0000c855003400500c20a181070550305a900d15031104010340005440034100000b216202d0b031045944200381710241d800184c5c090300321007c03800c1005c0c174102c031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 949907643 1250 949906393 949906403
    0xe0f0f1017070207080d0f121d0d080c0d02090406050603011e0e0c03012303030a090501030b041517010e0d11010b1012020904150314100203060904080705030d090b060f0d 75
    0xe16800c0040072034203060f400418404001030040199442e40082c41275040b16017142c04c985050308101c565250030f216000c910032050210700c0c020004101455030072141052520440140c0d144009030004000b848683c000d1604204080008160700e80541780c0d10b13064a030440718018000d969482042103040084901d460004070610042001103298221034100c00c2100359000c040c0c11113140828039541020040c0c9001641c195010009175030181b040394007060042d1424400c030b03004604a502000d040e071040c1012280f144880803903400d000e62000c6840e6040c0400e480d030701c0d02c142c0d0000309001200740070060a5486c0404003003c52400c03551890600020b5115401000d00c6010408029000b603c4600d402c1a03c0b0740e22440005404404407000d58420683c508141c00c680d8425403414204c074400c4100a8410130600c51503544000c002d951141e882464a5600d0700d0350328140f030650044228500c83d150515060a040010b40412140b01e00c10541d4490a024480c508104011000b014040c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 949908893 1250 949907643 949907653
    0x8070f0c2a0801021830101a09062206030807060f02090f060c0106030c0f0306060b1c1a09090601050f2e021c0201060e0109020403030e0f0f101707020708 68
    0x845d07082281764481c14403403c040b025010724054000c2c0c18056184c0140840d203401c003c420f000c04407181d103c1d8240c01c04201e0230441d800d00004002c144400c4000c0c000c07038801c1006c124580c0c815800400581d03034142000343c0500180b0b030f482c070300380700c854016140840b003107410042c089d0032088951090f50030080c0010540c3d04690f50711424810564000d002c007030023075502d90b10084081010105200f004010180c0c0b80c00b011441d6040910840301e640e001040001c2040041186011f0507110082d020505000005038501300300c0810b0141e14503400109402500c00d400f00440104081003050494400750b030ba280c01300091004112141c1450002c0000711500c0d0b0340c890740c071540010b51113968140640121541014018109055400c20340c1d00b890044c0c2d1243c1041c080c20a188542e140100001e000035800c00d030031581e01078425454290203500403040d08086603007903aa601030041d03102c1c0c03020b0000303080b510524400070912150a6816508a2110b00109110070710009909045403080c40c0504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 949910143 1250 949908893 949908937
    0x2e0801091a090727030311010b37090c030e010b0f0a0e060d020409080d060609180b0301060b0f0c07050a0e0f04050f060106171608070f0c2a080102 65
    0x911103002c0f9088a03148000e856244260352038107902c1300c2c0c0c090350094450b40c840400040440c0d0940c0e0061070b841d0b00a40e0703006901e80d5502001081041421a8081408480103000610140300600c0e90302c400315949c02c04000c82901605540010306c940040c00092240440c09130500c172141010034011031708030f10680010003606410780d034560b42069006100e130411191a400160649081244c1a2038a0038000f400b04802e00c11807040100802150900c19441031501075001c41a801144980c8041612850b015030180c0c2c3c29404180034280c3e1825060321941c000d000c001c060341007240c05007028440c0100104242c035103480341c102201c003207581403040f40c1d03118039100c0d40b0ba103005401111588941d03421540c811700d080c411540680307030f960b440c0c06054010103041126000064007072981003113400c81204603103910224a83e4091f00600301035a000c150241c040b41c0380744100c440684040b21501050800820041000c0c0b0b00020100c0710103041c81c0c940c00300d14202c1c480d10028020380140a2451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 949911393 1250 949910143 949910147
    0x30c0f020304140103020712090e13050c040902031507120c0201061a070f1a04021507051e070308031005040506120c09040303020c1c0327022e0801091a0907 69
    0x4004441010305d07000d0f0605080e031b074819100c0c190442d000400729150703030014005607084000c00c0d60301088907120f06081d15160340303920780c50300c1c2c1c0c40314081d0040351245065002c0d500d04020b03140c108a8901034401c900c0c903080c2e070300904d4607140403280c1800c0c6080c40d040044542c4140611015100b022605004083c000c84503203400e80c4c0b020504541c00e94001d47c1d48004287c200c80d100c4590303061414200842d141501c10081d45401c940c0b201d00034a0014420007001c03800000f812421002c010000c0208200134440503468140187d0004280b82000020804d03414008050001180d00035107003800701d03440d01c2040041c00c208042501421b507002001038400c5282c260f0200b604035020b418010b18140c80c0d00c454500f82080300c480085403000c40d4601072010365251094041140c03e40c001c00000403a0700e07000c00a041e0304100c002c5c1c405c2580b00001b0b4088100003600b06040100240440d80100b80c80e940980004401d10806585515000d00c039940010205d2000c0c4c0c1c0c00700000c01905c0c055a40f0202 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 949912643 1250 949911393 949911419
    0x403240f140f071b031205010e0f1f210b0702060103170a0c080a05090109292208060f1b1207090305060a0204050f0a0501021237030c0f020304 63
    0x1541002889107051003907030007080e00d1500c2d00c0d010f17603071b107000d00c3d0b006000d101c098600c1a44484185c160030010400e01c102d4070300c600c540194120102c000380d09070400050080c0d0032542c1000d02400c02001154442080e01c28174802418070074541c41c01242c0e150401030743c69000900c40030b0301002a94a0b002c003502080f4004145000c8281014600c88401e621000300580000240101007840010040340968204584200500001501d150380c920040c840c024609118024100d4403c1e0220324903240440100c0d082849815900b40c60640710b50342c01d80344d40c1d9003000b501d10065400f0044c0100c0c00900c206040210700100741341c080c620702161140c061400c5c0768001d0031042004080700b4080b00060045c000c141c010181018056112420001005110390ba82182280700383c9021000f044140d07008102c4880c0c2c00300d10f5806d10f85481c04101d4101c1d19134800440f04240510406482e42d82c440c10302d81c4901c2e41016a501003140007090203044c3c8041c404000e9500150348203100800c519910070705 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 949913893 1250 949912643 949912651
    0x18032a10020f03040603060306140c04060c060209040f060501080a0515100c0b01141203270a0306050403050a0e040b0915010c080c01020703180b090d02060403240f140f 74
    0x4120740040d0510b0000c07600f142c105400020000c0e855050400038070a95000e10030800095110685850408004110740c1e0f03c154400c0c42c0c1441101100e0405004459041d5884081c01803c184512091118040700600e268092940841c0d8640e011a000c1c5003244541c81c0316060000600c01030007204800c005440c00031441c2da804020030403034035000191460181c01d000384035401c070340032030748500108000c0c000b500190040c000741d000784115540610346140303003484961070f84180d04400802e10042072040641e0740024040700c1c14a0180800c140d4460300601c9030190350b640e40501500b0709820403040e110110103940e804a0140085000c1020b280310480b10620141081c11800000c0d981e492003a80040b0040a0b2503540420140709164000c0703690001c280b031015140300d0f01820484010701c0c0f4010760f481540104581420301c4119100c0400701c3c1c0c055a0002c03100a5440c07030b15540c00452600d01c14400c01464204452200d01c182107009058034082c507581195400d584404410f089450020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 949915143 1250 949913893 949913897
    0x3110418060e0f011116060c030e030c100b06090303030a0b01030e01090c170d0909020d1104030605060111030a0c030c020d020d0c08250b13050618032a10 68
    0x1100c0100001e2841c407030949142055009040d2600742c610380e00d400c56003060b4901d04906010064003101d1000b514503504a6640300380005035012458204400074882142d0300030040c40300103024408284005400d50282000050612041e0540800c0c403540b0f000b101e0580f030301548144003060003402d05411070400a2030600d00041c00104e89100c490940307200b820300b035500f60900d850034810342900c0300003000100c02e440c000704021101080e0041c00f07034003544580c2901a60201e6003024550103504014440c52003441c48036255078681c1082c0000f0401a1003c60204000441d48000b407503001c410b80d201c90246454902003814113442c2038540343c045820403a40034616181060050343e80b01d03004c107900303401003140c48149401d01d0a014903086121408140d42d03420008004012490034841c6401d440c0b503025441d4940928400011400c003aa4100035405000031603050400c00f801c8280220008040b4103e6000198401c4c07150b681110200d50b400b00c041c8a07900003120781c00c000f08405d0040840e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 949916393 1250 949915143 949915181
    0x90b0903042d03023a051b0306040308040c1e050423190b0405010b0a140c1c031506030f11071a0903120f070f0807081b040b0c07030c0807031104 64
    0x320301c00581000101450701021205c4040d0b000744002007118103562600704241030b10a40039100041e0391040700400c0202002400c1002504002a035801d4800030240c1000b0320307012802040700d0080580c82809218041ca1801c0160f4001e008203031540103140028000ca240c1903211030340208149401a05e59000d86074550110074180d17180c1c1c0c42001c4c003c04a1401c015200c13154081d000300052445a95805100c030240700313103600d6280100707000c1c05c906c85c24545803403600750f0401d0503809041e040e03480441c00030480710001000c5416820842070003840c00d4041101e11907511942c0c090f4040c1003405001c050b00b0745131031001000d4010380190001c1101049a040507101e00c2225060303d0225403032044920f0002c14046002c5e04540250002c41c41c0c1c2c14225801d1802a4005141c041d00410000028945000a6070440054011036003c2d00000e1120b50f43c98201c0036480c1ea4074552480121452043c150000540050100d40d0006803588a9010a081890502000301034500c60020341ca180b620 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 949917643 1250 949916393 949916449
    0x60203060103061a04050102010c05030f010509181014060d201f05070c0e0103031704020a0812030412030b100e0a09051e0105010201230901090b0903042d0302 70
    0x192100c1e4a61136881d0f20f40041e80c4034249030009007511100000b40003449824424441c01317116500c40641922800c0d00c1400b0550b5903411400801441003d9620701801400030100100f81541c004a9400e4a02d4064540a0f120038080c4107922002c030a004c0c091000360354540c42101801c103099032551500400c00d0804640028200e1400910704814030081080018240200a886a0098002c0020900b082d5140d0b14503180688000270b001c1c4010302500000002030215038070110440d0144c54004100e9061500c042080d4a556000ba0b4040e14000107014410402d075100740a0500140d4028002d010803901803881510030129140c1202d42c040400d0700042001d060501c98544500d003618115005600d2240c1e44401262068000504590401180180c210380038521150401c200c22000e0000f40e03690381e8141c0c010021004014806601102407114840c0c0010240050300c0601e0000210340c4484980503081d004a031100c9080f42c81c080000304094070f89082c00c9040460309044078540d00d41c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 949918893 1250 949917643 949917659
    0x30d1503051c0e06040506070f170412060f09020315090a082a0a0b131e030302070b090f060f041109070f03060506030408030406021309020d0c0e0108040c0306020306010306 76
    0x24698028002c8882e816015128659000004184108003910910b15042c00c0c01c001ca1142c0c49601b201810141300d11140c40200141ea0008035004d020140301c2603160781d112401c40c3e120000c00c080940c1d0303441c00c0a00054520156105a203800c5600800600c01d4140034000200701b5000206402c10f0b50244410000c0032031101c00c001c0c01e000800b02c1244414602d448242c1d071400c440d80600c01103550144a0074030014a88103210350300b14032200c028142c005842d2030400714140c810051100341c1500c0410120405405401600f1401d21803000c16500790740d9114000e541c0c4640c813040e0f108a602a6021600f401d441840c0c003500f090140e8050711400c81e4410125041d92001e4600e003002544c0c0f204150811549807203154060b2100301d44441c65410301e925910441d00010b000030703281c19800203603080c1c05046a2100c0c1c0c0184681401951100200e118250040c240c2006090204546042007803040d0f10030b04021788210703071102000d01500e0031500c400c03009400007005070f81070646d1003201040100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 949920143 1250 949918893 949918903
    0x114060706020c0c090a0e0d21021804141003021512090f010501090c270f030321060302010c0f0212070b0c010b090910200c0c040b12030d150305 64
    0x441c40c800908a0b400b034101441070707010b0011b01802d003640c030304005442da42402041050100c803161402d1100154140c0342401a0004042d440e0a03d034030000d28400803400c070007a101141c0c80100c808200b11054041d80c580d1268044420011a0741c800b8024001442c26040c0104013000c252982420512041e2170802500010360310304a2036405107481c1c00ad43d05007401014007502016400307022908540340007a090075118070100c0254021141c2000c1d104042a8245004080c014000c1c02c80b16942c3c1809408903020300100c201040941e404200d01c9607203401072200b02c913070680d030780c540108071034032099018804000300300c1e41700c4946401800121808c2140c1c0c1c0103030142c0b801d419540c41014a605c1e003101e24541440d80100c44250811482c1840440c80b4646503440e10004142154052a90f00c101001200d85581e12180405d0010818400141100561038140e03020001c084101b4204100b0407510304503108030307a20030800390080c0c02507a002400943e02a04103d21000d840f903542c14142 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 949921393 1250 949920143 949920157
    0x1b020904060504021302040501090b07080d1404051506090f0a1104060513050d03050708071103010603140f01050114120a060905030324010801030b1f08010b101403011406070602 78
    0x205032902c1c180b20035031070a5040310030024501c04086203064a40000600060840e22480300c1000340854200103100300b10044458603500c0a100700000398010348261707000e0a00340d07016030703041c1308071801c51240221181503240103840c0101000d06961300e006807105821001021440050744410720003040c02c201c3c40140000d01465141c06480344407003e072040c02c2e108180d00c00d5215000c840c1d400d1001c25004411104a0398000c000d0350f40d0780d143d509051400f2103200c0000c03138056280100c000f09100791184070030390511100c1c064511881c0440b80c3c030307402e031102801421410000f01c000040386142404007000043e501c01306641503030002e030701c0d0740c0c0403903032020b200b0790b01900008200b14000c2182221a05603003d2245820b20140c181f9000a200b030205000080c0301d490380c035000c02d03550842000c803100401070004501150725100c2c0301c403501901b00c41103c20b0184655800400ba03090003014403080c0750b90f82c3c1501c10f0540e860038105400d6000c40003807054100e08100505400718603940014015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 949922643 1250 949921393 949921403
    0x51005040f0609240b0f0d030c0c0b0d050702010b0f010f0201090209010e090c090906133813080f0901140f070c090c05190509030706020f0f03070807031b020904 71
    0x100010714140711003080420f800104c081850124203004541e9502c003900b001c45400d8507484103070030312880c1c00c0d80c1000805002400a6142900014407925058000c10044082020500c429198200d080c1d0130ba134050680c15500c100030159185295121300c000d001d00f11503510001c6a11041a004626041070a81082581850b40010080c4400c0200820307041044240c1d461600d038a0008540350712040040c01825141c42e002d07941e0300901031200502660880320b210050350216036000101c0900c2021240e10f416a0700c1756002032000741103a400c2003032141e00503014605c1e1810441c2d50f901d8ac0d51080c0c0225041c400900b001d0036503103d2280141c10303404e8010083c942e9507001c40c10f01a8403940c1e103900940a59041030311245150341d005c000d540b0309980184542d0149440340310f050364580282c480c0941c1500c104040024119030026203880c0031403084050b12988840c24405a4481c03290701006032079080d0820240c0e000030b00c503400c4100c0043e000805640005203a500050311554140c8041d20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 949923893 1250 949922643 949922663
    0x19050709111305011403010b0903030f161101030507090302011112030106022a010e1201110c070e090c030607110a02150703120506031f0921090b07051005040f0609 72
    0x1401031802840c80c00fa050900303040c10584d003c0c403640a2907100c14054000a1880403448650a0b1420010b841c2c50400c050002c5484070348400c02501c184801316000d40c1d00044411200c144c5501070320455000f0501582e0f4020003d0030368005507069118504400c810340b0912012408101c107070000786010780003c1d0f002d4001900442c003103001070108500940c40d800040b40b003500c0141c0e080f41c030050381b100b015034059040d030310301841c098010300c00c00180c034030703072010009100301d21038070200700c401c1600c807820202034440d2035003210b45907640070000f035058043d03000300d020a5403a8054103201e44000c10300c1c0101c800502142c0d0101e81e40c41144030740c2090012001c01d61104158101c40d404c0010180b5200070051072501c4070010380d42c5d19008280000481031601c0d068a081c4564220f4800550008001c41040481e001d100700034400c0341c2e2035000025441000400c407800450f04030b0b4040750b000402013100c0b407a15500e0400416000c3c00131103c4a000b00d407420700095442c06440d03591801100380750 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 949925143 1250 949923893 949923907
    0xe0904031115060a090f020d060303030501080d1119020a0f0306091101020604050706080a02090405011206060803120103021005090d050d030c030e030301090c0905191806081905070911 81
    0x80e2800d90b801440c019480c03100740401415484400b08242250b41c03600003c00d5203a08840054020f01c14600f034242582e003003e070080b05068054010504070782e8101c080b02c02d40b61002ca801c0f141c41444412222517a00201e034a0000c4000d10503803400303030a000034504050301c1d0b41d4043c59951407189500444104e81c6480c600e0003404844502c07000b040c402800501510b2400d5901e0316111140c502580c1d06010100c408940c0840c9140d040e00d0705000040c00c100950b5845642c0c1c15001640f00804440c00307420800301283e101008030541d4a9004050390120059086a081249034124081114104201445007620691350380c0384440e42c3c1170051010b000f400100e16001029035940604040600d07060981c0c085a002c400403c5a04440da04080002c0c0b10041000c102d450507a980e01c001d61141c0c215035000c02448031803d20b4002c41d284450000300d45140303c103c0c80141c506a200d0700302280c0050789126220780d21000c0c10800705119000b42c41c001601d644041080340d10803581c05c0c148100214140e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 949926393 1250 949925143 949925177
    0x80d0206090c01081515040f0f030c0506070f140a0602030a0902040b10091421031c090206090f041d070f081c0c080f07080a1e1209030e090403 63
    0x150790b048080c40c1c40c00c000c0c50b100c5e861080340b508100f40f450040c0c1c039070307103080244040c52030984016048030f5032020b11700766940c0380361421a1090300094803c000040c100103460b283c1801120000c55000e040100c0e0b0002513240c949003a080c2451002c1503000b410700a200141e02c2c0e10043d0b200d07040c540000074200101d4010700046071026034400c0d0003030420460060b809034001060130300321131990025507400c04038400072500507071580c4800580c26581400d1452400000303c0a01615034000d100c240041080e2029107007501e692440107500018208040d80503403e14403194001403030040e202084d10b0750020082035a99181d04240d448640100001307008407582403000d80c2c024a0302c400208501e41410f400c8001d69109010801c003401011006541045082c0099400b8400d455000c5071b1101d00c03a0500e80400c0d84007030301400c0082c000c03100220009011600344045100340750b4a94141c01c94070101c24004001c0c0a02c25400e0003400c0c03441c4003031542d4040c0c4281c03050384256a0880c26400e40c2c101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 949927643 1250 949926393 949926403
    0x409060b0d0e07140f0f060a0804210c11041401091d060402030d030b032109040b060a0f08100b18091e0613060e092104060504120804080d020609 64
    0x81d5540c0d400209080115404c465140c100803101241d068403900d0034100040e06d0010314100940c1c01c0000461180c50040d0003400366442a0701070748170021288050004403070400a07288070b002c0400c065810581c042a16402e0150304458040e0002a606c08000140c0300040c4090340006042c6440354041452002d1040e0940807204e200d00c014146401c0030390009071140c10a0717210600b019502c0402030520f0743e0401181c00c080c007411018400711580e0f280301d2000c96010500250159080400484403402c6c41012200b100d146542c0c5c03407140c0700307079a4000c0b01c0c055000f4040840c4076a0722a00440c88198003030082c480c0107103031a40740c08912a502d0910054920080400c1038500b26003640d0000640310002c0e05500950441d1030550304604200d004004100b19005107005814007400c0299080000a0951018102c4060703c0454024502e0503c10303403146000b50030008800340000c00c21303100d81c44881141039101c0e200d074a007880e4480201620b0301004000c8180140d1040090107000007003840 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 949928893 1250 949927643 949927661
    0x151f020708070f1217030915071419030e0d03020418050103020a030807031407110a2301030f020f0c030310120807120e041b020f07080607050f0409060b0d 68
    0x501982c901d81100d8040e07441151007050406081101c466041000240303c1700980c09500018035220f0401c000910340d80c3c0000c4001d2004010300b00040f603030150007924150020006420b03118a420280000350582400f48811002415169030000b0440c0009000001c2c016402e9500140c9440c9400c190040180d00d1000145179146130000500140e10341c000b80b0015039401c5200242c1e184054542103034421071800010800d8800807031000d081001000000c0d140c084c046421445243c0c0324060b409401008012107440861040b20301c0d40c80b075000e03800ca0786490503203020040c1009521503040b08a98440380c104041da400001c104219200d4902c0d82d40040c0400e031001c0842c0307032101e41d1207503480d1107615409854059082e20074030742b252040359030071100f00d009801880312908001841c046112001c1d0100058080c50725903007000c10000036110b08582d06180109000e803a811800e072201c0c1c0c4500b1004581010070000461071071990b014070002401c808003480d82c0c640049080740c044442c960 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 949930143 1250 949928893 949928909
    0x140a0501030507211703040203100b1f02030d02040e07120e100b1201090803071202030907060c08070b1014011e031a1c0b06090c0301060503151f0207 66
    0x1030002c41c20009404003501c078031001e50719030190a2803402d4106008944002c2c245a502915003813106041e038050b40c0039071b10a80403500d1150140c0403210550710000c8455401092040744258010a5141c4035444e100075030055901d17264182080c501170341c2c015004403c60b800080148414503500404501c800105400308000317814030f0241c0d07580c8400ba0600c481107150785901020391281d0b201452303400c4c7c0c1c14112008015100051420304081d0b081110128081041e203d10906010b540d402103d10802d03405028080b01c9051000a4400401e001001d4030842070510044000841040071103009109003000c1580052903d190700c2e01d8110ee004100d4100300c580c40c0082050742c02a20110744119441c200824000c440701180d480c00d500c401640b40d800312088454402d040d0b00303803007010350040c0560b111119a03602c50050007541d00e026601604020b40400042040c01e100e80c0c051500b082d071901c0c0c2c0c01c400098a8000401c0c4124542d8139450260706448001049501005808001c0c0060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 949931393 1250 949930143 949930151
    0x170d0e03122d04060213171b0f13050405250317121612020a030212100e040f061808210621010b0d08030901050108010204031223030703140a 62
    0x74000b0501d0300340180000b0078843e004206610095916210300c1d0291174506110704c81c00500240707440d0b69403504140c800d00c5801c55064584141005c400c030075003855001d80505800e14024451000403d0010820350b0703a80502e030030000c25020041e200b103a610401c00c0d400c40416040d420300310190b04186d01d04000382841000401081061030801340cee8000105034a00c0c2c03007005450815102e07425140b6001240c28400540925029003544c090405048168140700c900d079500c1140000386501d034040c5c4184110360800040009414600e440b001612850001c6903119a010020310054525202100e42c03250114081005034804031a545200440c2c0f5240801d03030420350042540440151400e64590340c441440c04827014003500440102e0030050700708021a030050030f0114082d081035490041550901d000011081814000e84056a40200b0010355840422400740c5448007036030140c1c20310401101651040d0046075024520a407a00d441c04519403080d00540112501c0060a04070003900d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 949932643 1250 949931393 949931461
    0x3060b0102160302011b020301020c010f050a0606140f0f04090b0f03010510120303091b0f090b010e1201150303030209040612050a02010804240b0913170d0e0312 71
    0x2d8007500100ca40a00342609540000082040d038246004c00c06034266000042d03121010f03005520454071030105840412080e2245450f09003500c81c5486950001000030981c5580411404020040c8402c0190303158500b04011304c0c1d0040c180c102c2d82c040d800503036461120204a040c48040760030103000c12002000030b8030b804901024000054029001c0d0042c5220248082600030341c025403005402c8040a510840700e50303080c00b8841203e014191020001000028880c13a4502401c11010070584943c0c0d82c00c0104024041c90740c114607205180ca640741d18100c0300102d1100c100d071010350b00075035016036144e0b403000c10b01c070950342150301500e85482d00401d0714001c108080b408414182c0c0c2413804508645550802e003001d5041400781e0b0500b0440c2c1c0d140794444c0c16156000d040c41d01c2040c0c81054155844041004d0603a00101d0040c20a0100c0c40c2d00504880701c90300200301c09c07102490006040304280303c019103150400b400b1710441818800070700880e03c0d07041442c00744030303002d90141d8195048 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 949933893 1250 949932643 949932673
    0x605101d04111923030a050c0d0602040302181b0a170403030b0a0b030106030c090608070e0303250209012411070b0d02070c06020304270b1903060b0102 67
    0x400034409000403280c0d0722154410740c1ca0380c4984010403031400c030101120780c642e06070515034402c0d0305228604d4000c908941c0c2c0d0f40d04000c80c010f00b900b038104014141c1214480140701251005450440358580e0030070010005a0303509039203440c081040040158240b0707140404030060701c447c2c08400c001880500c09046025800149101480f05103009c04c450380d202c2e49415005001d0a050301035100444403c00300d541c0d0021009035040b107560b69410310840101c02c1d800e0f41da13440d243c052480002d0380000000c01c02402850442c00742e40001c0c0c11070303141c10042101008061071440c141c80424950321b04084c158600403205071b01600c0030002e000e00e45508888101c41406420b06114148004039080704c90b054824000303000204107034810296240d802800704c500940c08000b04656404d00250081f8603588000305540a5841043c03c0c0b00350855031030201448140d01d208580341d200d07140c0d40e07812419290060610704507401a0750200034103082d8540b20f000c0d5214401120f04551100340407000b521 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 949935143 1250 949933893 949933949
    0x804210f03060b0f0703120b0607080307032301060e030a060e0d0e120304030f0c0905070f120b01080a110d0c0e0307090b0d08032d09070b03011206020c030d0603060510 74
    0x5c1d91609018240244050042004d400d090301126482940400c050042c06500d00056101301402d60301000fa5209411200c4245400404070340b916045200060003080c0c040c0740c0c05141514010100ca03060344480e079070041a140380003d044242e410148001d0402500031101c424110070465942c8100e881c0901c0302c958078015440050012400540040140441301c0500070140411030380910282c034040308041c0c92070919643d09070020701522081a0031202d1031181d040030350416550144951203800d05003000d0405da24100c02c00705010400075074280424408d8103c07070b0200b52200302000da1041d04150034a0650342c04460342c98203044c0c1900f015602c1d03903030a030001f6500641260b12030300c4000c104070260f4001c0909a200480820700c6000031011406111322400c0c0d41c408840c4925181c03c0401d029010a11640c0c110406054480c0c0c0010801d4001c0c0020a8111088a0400340c251070702d181611141d074010380f0721569401c00e01402d038260303104c118054480215511319042c4d920145107048 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 949936393 1250 949935143 949935157
    0x10c0e04091203180f030201050103031202030603060f191814070e0a02070f12080a060512060612160605120a06080d030506010207090905010b030c09040b070804210f03060b0f 77
    0x141c0d8403141000103595600c04e10a446410240002c0185428a4041c0c0200741c20700040d40840c0d101e000d461a001850300849101e2071010700a414141c403007241d03004144001404400000705075402c6c02044441920030940c040d0099904458103601c54107100f2920542e007401651079805c412014401c1e509840d590603048948032000583e12405810a03200b0081d0801c0010000c0000c00802410b907a845403015000b08008070080203050303945c10400204405150310812140c0000c0b000074458900400007208604149041d030700414101840c1c0e84c4081c20940111001c6400070640c038400c208107110700381d80040711400400500d070410300318a540b910b6542d1000201600c2d0380020701c83c0e910901000005140025003070001d8481e40c5481806000314040003030007407188081c54103492a001408500442d004070481405403124502220444401402030303a0142c40010740c07444000310042c1d50030a854a69440c0da800d0f00c0d80440c01401e8440030f42c0100ca00c5c410601c540010b8903011400c660700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 949937643 1250 949936393 949936397
    0x1060e010302040f17010f06061b020a050d05250302090c1c0f0c0e04090209131e120e24130308130608010e04050c0d08070204050108010c0e040912 65
    0x1148a400480281c0b280760440707036064008000000b1200303002d1001043c54000f0000a114000c444083d0008581c4035100d5035002400e1051443c8000e0700c030722902050703903001900558515489102090360090500c50807030741030f404421849400141d10423107004403522215542600c9140d9000182c08400240080c1c5c0313505800149a01d112490b40c00c0420109407800081c4840f003444100d60700240408015180480c6048244100c00d14013441864080d560062102c102500c604640c000b100e02110750888041140800c0e680180d0010380c075009005104000362113594002d410002d0501e210b003000d03a40504030108032185292451078401012104289403280c48032452a80400b001146500281c2802400540f503110b0316100900401901c10030b46481c450b03641d8a01b003c180034541158040c000750428802c500140c40e00c64000c000c4c0034014100030b41000c1c0503400090440f00c0a81c0b1184140e9920210811340b140c006a010490540072103080254840544903828101e410f0410082 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 949938893 1250 949937643 949937657
    0x6020a060b01170405030301290d0c0c061518090b0411010c0213021207020f0a020402071502031e1b03180f160608010f050607120e03010905071406120106 68
    0x751592140042c5030040b01412802e0860b810603042c0152258020f01846c0445100c0b01059102c02c400c010001e81b0341c130a034490940c54844100004402000120700c003d040181031858200410f045001e070742541c0026165041403245044401d0724201d030844099400e00b800c210320000461300f08071070298003a40003410741009230111401281c02e980800c400a500020403404e540940c1c105034040c00031484400320100c0aa00c40350000eaa40d828803441000d00d07070740242c254200506103030b00a80034243c480d11408000d440c02001c007000fa80c0040f10f0000c0684694210070b821294040d000e0381d0060b01c03d2100d545000801e00300c65001c1c0c403000b004e80c000c40501040d54a5080010000411015400415600d014004031281c2c3c007540007506c101d1002440c440000700d052a011003011044640c002d1040d880c0c14a19995242032085082d00d2400b4004c4000640000341c50070b0080501981c46071003d0002141491150340d042025a0742c140d0140009024002800b07211142c214192821420050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 949940143 1250 949938893 949938911
    0xa1b060e01080c03070e03011b081f080d0f03020909040f0204050708010b16080904050c041a09012a1509020102060a050f28290306150d020328020114030106020a06 72
    0x7e030151076032840c02c5040600004040d4103543c1d200e0300d9075004029019410b005800c1d01001120302140034003c4d20001d810800c28114034900414880c0c10b031402a00b0003500307181007103000030001c0800312001d030340d031603600006901140382030301c1803d034401c0440c280301c9034650500701594842c1c0a5100c09402c0001d4a455000a02c049001034030743c0351500034000c0c009803410b00300c11032054000b84580803c03000c643c0030a5401f0a069001e4135102101070b52a0081200c00309410302049070070510020880c0800460480070960058104100044ea44000303d00185240300082c901480200144825482c000501043e68650082a0741000803104c818240391000300d4810f030180300c0c05000240b0549880c0f504011400c010074a04094600e02d082c0b00058111603042c1030b260081121509000c40910b000071041d440c0c401c40c00c04000340080c046801001c448100c0e10360303c94a101030350882c0c030610103541c0110761348003102c181c0c0392109805050565142001c046e50b0703081c000c14028200c9889c0c0d0308007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 949941393 1250 949940143 949940149
    0x3030403020306040f02100309110906040b0d06021b03030402061801090f030b1e06010207030615090e01020c011d0709050408190815060a080c03090a1b060e01080c03070e 75
    0x610055034005095070240d003005d00c1c2c0281081941082240224002c06001c03070020300900c01c03240c1054202242c4414208140204100000020b10781a4410307604c1859036869103600804003c0a07103d681c005a54402050b05c40c500348000c061032441c994410000c01c001a15140f0a03900f02c92001e8031409000c4021800584100d62250400340c0b04151000000050012104a444c00317851205225078101d080c00040e44524101210140d016901c107034000c10000c0e1080d40015501c0e2408101c0842c0300741c8480001c41075404c0e0b00b21050390380e9004641c640e4035036000c1c03041282d00301c0711904008091100c0c101d9681c0702d5285115507015182d46d05c00090a08c010030b021240411070030800c649606051740d00240c034842c0c00341c86401090140910540840c01d000049904e50b400300d03103400f02a5500c0c00070300405a40010075680c401e000d0941070b10000b0708414540c0d1202550f4030644d01c0d00d241070800017420440041c2d00c0d1810440b080c0c0c18048036500080c112038101400340740241038642e5480c08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 949942643 1250 949941393 949941397
    0x90613031e020f060702151e190b1009080c06040509070318120c0b010603180f1e0506040b1608010501030b040b1309020909010c02070b210c09100201060b03070507020303 75
    0x3ca003886029074020800c0250b40895007000300728014026003034985a51420301081c14031501558200c40d0803034045109015030240302204011903400100708203150710003141142c00120051008036902500c1030102c45414007a0098824003990410704040ca8107000465904010302043c081c180d54040c2c201c42c01242c403801541041d0045444000c00490400080001d07029500580759140080c0001c25001e01c2800740408501408600d03544228032515028203d03080c0010032a080181451030b90500c00e040320036070340e806008001602813490030742400d0283e0f440041c010751046000c100c4148101d604031b0851819500b0a00e40010362400040106000702602c0b950300c3d60120100040c404c0e1144e00d50001000340e44291002d2100703848880256099510031405040940c000740001d00c43c28220101600300d012100d0220048030603101c1e040e10807500c040d121400040b000145600f82424083c0400d901d00b80d040c8002c1054510300000d180d20741c040030b480e640400400103214070a641d01002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 949943893 1250 949942643 949942663
    0x12090d0c120f14060405030a11010917190e0d2d0606060f05090d080a1806030c0f0e09070e030114130201021e07050112060b03040605090613031e02 65
    0x10103a070a160840c00c00b400502c2c0700c0b403012511110401007003615001c0104195000c4e50380400154148003402c101034400c0103107800211401e40d078403800040414000300d6450048100003a01d0b03035503000e600d20000c01c4203840301e18240501006000901d840d0310340c4a08500c3c1103802c10b111401206d4590002d10b0071150540c1850840c00d22a804001401800d40c0110b08850312611190602c400d040e04c1903a140c01401d03620340e40b05940050714004070780441c0040240e010300f40f9001110303056500400c00e00d80140e4002500003a50755138040412030300441081407103051420418a120703901710004000c92001000d9000b0040f159660080030f0714250070511944040c194001507a150501d00a000040c841d0400c1c0c2c010f119166140c020b0340c81c00c1d41c80d1084400044054011141440e005583e20070200f00fa5444013513a8800000b5050b4413980614000c510406000c507060038080c00c1c641c680311b0041d00c80d0340841d40c0c0e0b03440c3e10b000075044141c8902d0007291042110099a24010981c1001e112203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 949945143 1250 949943893 949943909
    0x609130609030e030c030c06071e051b03070509060f04090206090a1710111b0c06030115030f110d11090a082a061b0a05011a040e12090d0c 61
    0x1d151030200340e00142d41c501c050409504075040d05038810205580c584800c0c2c549600716000b04030203070104180c1c940c101205510380c001c50350402210b5544a2810b401415100501c4805004921003441d0500a10300140320071034000840d41080c50000311052140742e460351040783d50303c0580e42152507071000d035856010010400400c4c130780d490416281c0c11140e01c180030303000c2c000c1800000c100032051244000c03815040089901b040c0300340c0d14000c2020f20006c0e03003048900c100e0107a001a951580c0045018001c120103103007400002c000d002d0184c6000018036000721381800d510440d000800c409542c00c00c5500c000118618101140d82c42c107900c90055070540000c59000041040e400010b51484100c849a84c140646000342c0307030044003000c4501e01c40342e20420401c201d02c8848103000301c08090b100c2403c00e40d918000c20395901421254200d40038202131002c001126218501446803500c044039480140c80d903d07046a0302c1c031145102c0e10072043e00ca03400c2c8126650601c0404180748020781540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 949946393 1250 949945143 949945151
    0xb01030b1f08010e0403091e180c18240c0c03050a02011d0a030f02031c02010b0a060c0f02060319060b03180109020d0b0c130f0306111206091306 64
    0x1c0d4140d20050550030041c0e00410b0350000000340c00341211442c0f84c49a500340da9200310352400e02803500d01c001c2141d900075600d64800d82003c1010310109200945440000030000390703181d01e41c10060407000c008040b16850940d040d100f0401105481104034210021050300100c550307a804041e03440e0404080060030007155044003100f0171100050700107106000762100310b070768900c000c0252462803800d84c030280c0010500200300002842011402c914070700c004c3c251281c012510380d1b0015040380f034100d11781c0140e444020201d986d0030031081410140800d8a08040303000b241e0340b0790003e0360282081c000c1c01380d800000041c0c095195202110300c5800401000d1041a5942410781d0043d0020b076601503c1840c086a0014000014170175440e03450740c064808551181140c90f030060703400000300381010202080000005014070240c1c0100030b40190113201c1d400d01c0c11030508008440c040f5221942d8a0b50810110303042c03160f06c00308668040000c41c1c540072250760300003404a0081d2480b000600361818 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 949947643 1250 949946393 949946419
    0x203040308130519150e060f1219061a07050307050d050a1403010602150907091812030519020705120304060902040c030618020c150702061e040c090b01030b 69
    0x403030392a01e411910201d1384804001100011400c0d40e10940c45421501c0d40300c9041c1040d40b5000d522000301850009154034245820040000c0300c0d43d01003200740c2810b4083e80c04001586180804902100d036012900b000a01d00700481e42094403032280e141210802d010680d41e04104003003048070029944a0180c0d10004010036019042e41c000340c0154010411004140c4800b8103250140d90480e1204d0380144100901c481400c0d40301c4001410180060003007a6020441e42084c2c00782e241000f02c01841501020081e052040c08510802e44c0c00c0c080600388400d214807070303500564880d880340d082c00d030050b519040c0d0b1905c14036000c404082c11740401404404c005c01e000b200d84c07042e202c59009490a204807802c070242101205c82c0c81c0643d0401801c880d000e4441b0600950260000c11014802c64603192514507510064400440350040181e2081042003a012600310005a809050510091550a080e03032540340540c414001c0f01c00d4035540d1440c000c40c507807180e008194101005001d204001034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 949948893 1250 949947643 949947667
    0xd080c1e0d1b020c060a080c030a060e1303021b030a03121b05220b0a030e15180f0601030b01032a0b090a05271905161e02120a0203040308 61
    0x1559482d00d00540265200100c4074104030f01141d8140e0010361ba0000c6d159030789aa2100d0b9a000548800c1c00c5507680daa01013000000403107142e02803d00c8045e00c410011a42ca0000d00d40700c00044007180207150440c407025603440004802d412a50315040165030000781207500710003803946106035a05010f240e04c00701c580940101c000d040c4c0320b500803042e0300d201c00b2420828444001d0f9225400452008200b41e600b00f51090340044c1c41341002d030060710801c0c24041000c2210000c245d4018044840c40451200c94110400001c501a8002000340c07007113614584480044c0b8505101c06021414115505040184900350318518041101203400c1d08a49800510095402440c2524000c1203010008203042c23408040c501c21580203164810206083c0c46030020303010030081c0840d41d861880c01d4005028078902d024103440f40e640012400d50018400301c1c0200f0030b80841c01d9030500c010610040c0d1a08507170106000441031207801000369a80b00b000022451481a82c0c00605103034000305460300541 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 949950143 1250 949948893 949948931
    0xa12030c0c0906051002010e1507090302030a0c05011713030309082809300305070206030c09270a0902150c0106080c01030e0d0c03020a06060305030703020d080c1e0d 73
    0x81080d104600c0e40c4d03112030004c1c0e089505523418490281e0041c00854241da01400c4510340c0f005c0f00b40340007800c055495002c246044401042118041d080c61800d010a5034040c1c00500850300310404c40c030340d90900c995060442955a100a020140c803502c41206100b100400c03205950b80c0c104a1601107006050200c18002004854000182c1c61502c0021000210040d400c0804080031104a056400103002055160b0100d42181800028000000940e0f13808001e51b2080c0c1c1000c481565940c0c44804000b40c41e28284100c0741e01e0181e0641009404650394849a806060110b0004403003081c0d00003d0750041324000e0b185000c0200051070355030b03e40c2c10341000007201c1007c02103461481e94900150151445502d0445083e030284e040c0d0354507184246090b0803950f01030b005070b4203c3c0d0000c0e01c2d4030080d00c3e1903810585030b650001486a04050381081800100100c0d858064074a0501c01c981c0c2c099031007600707982c4081401c0c0d003405007048000102110b01807070440c07508010715502108800444 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 949951393 1250 949950143 949950149
    0x70332070609060b120c01270b04360203060a03020303310e06130f0525090303271e05090c070503030c0315030a050106140105090a12030c0c0906 64
    0x903c0c00e0600d1104c19040039804a00038984184c09000c0e4a42064011204405a40da803580b03001140d03030019407203011080c0100301a20780070400c50b990b02c0c204040401c00e10030710000055103c1704070b0307660040480e011f59100c04001c2c1103480542d503074650301d001800241440c0c00181d0725000005144e10103c817042401d040c2a400c07083c40b4540c488001411160034a29481031144e070b00c102100280c0103140c80400740040e01d0310850006400340c1401d604d001281c0c0200e4180000140220715a01010000401c2415005c1b4910302012210300b10f0b034008090400a1140c0c00c01149000c540034458404841c0d80c1002d007420a105400c841c0c07860303a089410030854402d15025109410209030740b0f0000d8000c81e0070450b0000019442c6032a100340960300d9901c0202010ba4062182c42141d0140d40c05201c0b01450300c1c0120008078400341400c001c44007100000320007038180b080403c510300c91900c841481204551911564500e045d82a04040d104032010350300080041080c048042040380440d0302031b00070303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 949952643 1250 949951393 949951403
    0x5040b010f031104231009140919051005010303180b16020120061e1e040b04030c0803070201050a06060c0201120b01020304030804240302030f06100e0a29070332070609 74
    0x802340680d81000e02c1e0b605480d44112a00312140c0c0c0704c5414030149070318a68078411000c903848220910301040c119070b000e8004500180d002e030703a4079000f03400024070701001d0640c603072034945800e0352440322400244075180000e0601074921038560030445004007008241c40c250341503450500c0c00c44112198a44a040620200c011000220b0b1141c1d09516084c20b2655400103c4141500d0320b449032200180700038012010840902101c1001804100165006904603000480c81d4203101e4080e800f62003840d080b1100f0400301c0241ca50160f0b038001d80420364403030030603000520500c3c5040101d045101c0c981000d4a080000100007031802070002c2c0882c040c0981c0c95103030002d01e48000e821000d034882500d100d400d455043c4c0100710b683c600b00007074410085075402e2180d1410380c000301160142c64954004040800035002004e040080c8040a0000841184ca20740c40c2007020354024103003a5047d0b2085001d210fa1020b207103000e051841480c048203042011441c0c842d90a4a01000600000f10003125 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 949953893 1250 949952643 949952651
    0x603150204080a15060b0703020a210903020105130b0325051305191809020102060c09030601060f021f02070302190c05060a180905040b010f031104231009 68
    0x1021504520a94007520740e900064600d80100391103000303403414903041522075255100000035040303040c440113054062080c6c002e0442d0b88200e007000954101017001d0115041d503070400c07e440c01680f04020006490782400c01c2c9480b90020090708440c0d44543c0c001d900f80040001c244000403038403d401c0408514549440000c41d01e13440f000f1120b03405034590542c20541c0c0b2600a204525090b00b40380c1700b5149408203024565035800399212070512140481d00d801e80c1e87c036860400d550341800030030350009840c3c94030b41c0b4080c08180840d903101c00c148039030401c020008820348101482400034105e42c082129801c10b100d6040000c15009520070031040b405489403580c0d00390500b85105040078400c1d00060300c1322100c1d2500081c0455039002c82c6080040148a130011095803091803c8075020304405800000c20786401d10b058001544182c01c109008845a207003000021106114800d03c2e000a641c0803c0d10046400340c1004440c0c96080c0c414000f4464041014220034044100d0407a0310b8808140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 949955143 1250 949953893 949953923
    0x906060206160207080304091a040c030509010e060114060307020a05030f030a0609180803060105040b041401030509153715150806042a0f020c010801080a140f100603 73
    0x11303990700698801d030b5025030000d02c810032079030400364403000050070300103010074a4a6802001408841c4d842680a0110b40ea900c140500a0b409100b101c5610b11140f00500c02541883c4011a049051014a80c0316034400000125154424001c0300c0c20298000200c0e40c4076999452010259001255507254480c50400002a440d00030b004050147d450f0100200041c2c0554a078010250310090440e81070240c10840002c03101d07056401000100b440c2d9515410320401000014283c0308040c0090681d5400301d2028082e03200e0100045402060341d02c24505414203620344e002e41c6000f5000500498818541d02c00d0298000750000c0c00c00140f0200482c2400c2c3d1244407958082c0b060244050001e8401000660300d0b040c207030f000d442c00460704070f0362040c0c4100828244401c03000000441c00040c0c801f040d10701c2c1c040d0301000108003c0000b4201190258180030455549103142040600f5500e41c82498012100013441988244094441603800f0303014028801c5014000d244002c6618018070820a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 949956393 1250 949955143 949955147
    0xf09090f0c0d0e0319020304090c02010504020a09020310211b18020309100606170a060e0c0912060a0905070504051e0a060803210f01080c060a09090606020616 70
    0x116200e040c060058034240104030b0034080080494000c0440e481c40300304003c40400701c049003210491200c1e94010f680c1c8a00349403039442900d8048040300700756810b16003070200680e0307815001e2050301e442e204016125954441480c1010307640e6805a8115a4503a141c00c01140d031041140064502810501c1c012800155031103e071040c4a116008a080700394a4482c1020290740045400907100c1c1308032009040e00c81c05c0c1c10100c0341170f90300c040d0202d00322a048003003255004210b50f500003d165000c003d420700e800b07441e40014500030204502510002000700442e550000318010180201080300c80d54030342281c900c0e00408981505941622501800103944c0c0b600f4010749100e1207040c0c40380c000e48040702d142d40f0707001c68024008142c10b0b5221207021800c15020405802141e40340b0010300380c04080054603051003400070b00345c2401ca07000e030001407046000001e41e81030705e200180d1385a41d4031740c80c2c2e0310119101c58868121400050404d400001c040341d00184640c001d2240c03440100c02c500f482001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 949957643 1250 949956393 949956421
    0x30906070e10050904061503020a020d05270105160501050a06120c1e0305012306011d010518030a05030301050306091515060d0c02010608070b160f06110f0909 70
    0x885580701c0c5110030b14800d118841d07809410a850050300105506444020005603401c0c5c0c00701d0b400001c3e90106800c0c04041c2d04001e00c107190309590401e149001401d0313140c040d100700c0017171395640160741448145003281d2280d000c03182582083c900403803030700303031245070581c0648000e07194140360608124022452004a1741400c0c0e940d40d010005280b42458001b24400400c400132050418094103080000810000e008800c0307824004680c1c00912060f0b04945140400082c202a040003442e480011441d65070500c030410b11202401d113940c40d00b00707070b607414040200380488081d05801140080d03010010008091410385404a01f6103550b0b946107a901550340000c85403441c5108008400f158019501040c60900d0880144c59103242031072107510001a55107501d8001f005030b43d206410400501e0034845403000d49100302034540342686000c08048070740384401028111380c6e5960300643c100400e03036100b014050b07d840d01c15900d81c01d2864840c2c0d01504802c2c8024022a0f207100000d959644041d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 949958893 1250 949957643 949957667
    0xa091710061e0e04020a05100e010f0507031718071814040c090203090a080a08150108090d1206030b130c05031504031b0501240902131205101103090607 67
    0x1925048914128a80c42c040c43c002c1d000fa17802c0780c201000483d56481c0c20300501036104040e16080c0c00c194254000403c000d4000c0c168608100742800000c000070350100c0c44901c400b1442141d10b00b035488400c0b000d0300301c07002400300c004948035200002800c0401400311704c0d003060040c40200301c20000100b440344030a508807401040f05c10308203010700004c82c2907400703035402c00c03a0359084668400a540d07034164558800c840880118111000700044580300d07030440809000c081c40d1602860601013030f966540c0704039018140034015840251001c0311300e203a10560040d40c00012030500c5080074240701d00580c0716500140c0d4445000d0b80081080e04000840304005045481b07000e6070b03075031241c0341140c80c1c40f0814105811031070441402000f0803000d021b40814480c41001141d03400d1600d2090807001c413415400103900e20b0040c0854032a180441141d2070440300350442100054203a807820501300001884030b85162442d107040320750b202010b00c0141d0f20428000d01181c11030b440d9804151200c03e030300a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 949960143 1250 949958893 949958939
    0xf0a060b190302100203071703060f03010c020c010e010e0a0f050112061208070602073002010e121c020c0604020111011b030b190801050f0115020606060a09171006 72
    0x140c810001801c16003004404c48003144152414817040f640d45154502d10400242885140030090108500d0b00b5000700c100c058040300200115541c0c0c110283d100d0350100e40403411700403090740c0f104161b40205a444281701c3c004201c103001703540f80c4070300480c0c4844601070140054807400c801e1039000428401d460a584070550f9001d070760f26555903900d01a900400c412212290240508000503511004405c2408500c41540c4445150349929416400307807417042c8821a0f040a0f8010464031000c60a10f10100b86060010b44d5010144000c0c1040c00e404030240e010684000342c80c145a400105959004a100f41d0711035180030395026500e07080c0d5410280482040c508405200740c0b0714005e9008079216140a41b0320b87c00001072514848440c1140d80c0a01c2841c0d444408002d650209200001e000d400011140b0349000c0c604032000f9a15107008003514016000019228105401090243c000b03021500b80e07440701e820f500c810715031101014401c2c0b120990401c0e030082051401e0384070343c2c4050b20041c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 949961393 1250 949960143 949960189
    0x605030103260d0608100b0a090507030207020904060b011701150f21140a0903120506060d0c110106170307170903160f0f0e0a0e010e0f0a060b 63
    0x1521141141c103030a400e00c1e03000d54005090b0740368450707550002e4005505010000900c40745005206801d01c084004c0c1103000e9031070301c454280180d581c00d40d4a81030305c03522100040c10b5070715000164005e205002c006903100c004c030307000c200812006d500181540c58083e13940714400110b54181d590700641c280941d003400d48083c8501c007041e603c90400c1383d4500000345001079500741310821142400c45510300c8921403584500c4a049055a0410515006202004100040042c5480007440c50800f00700d58010941c544011a446a54100980c1c5000074004810400110b244401400f03203030840803103840325400d00c040061081d00baa44603070107090074000034514194403555108001c400c401502a4403030b000348003848480d00e04101c00010600d62200c04640c02d401d20700e031400c040f01c89a0040020352200c1c82d007030000c1d000c41c03600f09800813603121380403440c40d490440c1c250141c9481070014903d441800040004802e00185001d51540136030010007000300204240821803903e1100043c2080c49 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 949962643 1250 949961393 949961399
    0x60804030903030f1205090c1f080f18100f0b010801030201080c0d02071203061d04171b1c1b020d170c0f0c0f01021b060a05070204021b0d0906050301 66
    0x28081d0481351114510342803209040d1428003204803401a608418207038805031241c0e0f6541010310f60121016600485c5401c1032514a8008058000080c01c590803090004017240c9000c40c41d0341b81c4001000088240c41e68140c01880d400001d06240225000c0710f8100030381031100d54040c4075941d050f42e806039595880355603044501c00d5140e0110624201040d820000440803940c40810307041c40b00356a40c0c010034103d1800504803030500c001d44031010704190700c10a110010303405040c0d02c04071a402262a07600c0302c1c0d41e903502030398181e4825090342c0306015101c030642c6080c41004180c01d1040c0b036a200d0f45401440544144004903c01030001d412212140d41d040100d25090a00c40e000b000454000c0e00e0b21a5003003245003490340f6800f100009901c540f10021551610040b041030420080c0700a04400700e2501000181451141e403681c002c00300068020f030864411401c8a8180340c0103082950744070001080f680380d0b050b181c03600c243d190181d070507034040e05481b8a280c101120b016a88090469003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 949963893 1250 949962643 949962647
    0x21020a120b061c0f050a1b0b220801090302061b04030305090f1903030f0807050f03041412070c1a040b0304030302133623040f2a06080403090303 64
    0x280c0c004040c2950f03180381d850440050f000c40301c0411094401d201403d2500c0c0d803894504841c01920201c20054580c0803170070300c00900242e085e681c80a8001141000c40115000005401025500401181d50a01004101341900000c08501558000e900b45020103100d050030041c1c1e00030350000400081c0100420b600604c0c000001101d100001420b000f10401e09054000c20f107403c45d80110081060303010781c508038981200704a58426101c1c20010301d00003050034800003912000384014203010800c00c4403d9940c000308000d40c101042c508115645280604110640b900d81d80304010002414038a0001518801c41c261400c80c0c0314040c101d410f5895541cae06a010350002c0c0018a180e80d410200021448145a1030035021030190001e00c035480c49000c1500780a100c001d00109115080c2042c0310300c0c1c184400d01c07000c144010840346200700d403104e180001c00c40b1880000507141944411214044040d200ca5410840f0a800d80d0002e0080c1d0300c400940313060360b0441c1c2c00740108101c41c0041003c64 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 949965143 1250 949963893 949963909
    0x40c0e01050d0605031e010e0c1c06060902031003020a0909020a0e190606050a12050105010f120b03060109060f0608040807080c0a0213020a1106090714010921020a120b06 75
    0x29642d100c0410829211004689800c0c0e00740030344003079046000e541c03031055a02881062a821102406006034502501c08102d48038551074820b020042d542e0401000d110446d40210040c01c0c40c00e40556980c1000c00c03200d0007603411400140c0c4520504c640000c1d410480e41f0038690406d130b02906005a081c80c00004c0008054010410b84c00303410310601d40000d4185511961001e00030301c1d192903480d1002c85000034061007203090000040c6152200601003683c000308441000310092402c0000c9040b42852500034007555041d00d0703050b08c1200008a1001e0301d5802031015503c1410121065a43c3c84408403900c4a094030301800b0410100b00d00720102d40c60301c0040120301100000c032000701035a98040b48240d00d0310034001d203038654003290050000e030740009005a000c0f1020000c20090406e44511a102ca03414810241c541809115400803a401039030040000d00041c00300c1681501103012030241c40c014032404901c205a9418049090f03d90410f02030f00c0c11342c0101c140f100325903514090000d02 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 949966393 1250 949965143 949965157
    0x2406040207021311130509070914030304030605100603050c03011a1b031b01060801271a010f09060603020f16080438070203030a0c170d0b010e040c0e0105 68
    0x2c507541440e800c4003c143e40c015141070242540d40d0030ba88840c4061011002111038100504c5150f0050900c0411a40200c00e2802d85030291441e500307050003400024039621030796100800f158100000c100492000312501c0080f1101d0351014025980d41c41d041d180c40348003d000e81404100644142183c7c405004060035030748142d00640c2c61440032111795a441c2d46c10001e20f40100603800110055000d0b801c1c0150341c010300f0108001d1142c80c810710941d804840000810315480411801c1c0f0506118200d0040c40d400708817010031908658454018407800c0e90f030350240580d501d09101d00050781e00d120340300b1110324880d2014800e09100002e542c1d4000c1012101c4182c9280400740030105040134200d80d0400c050006940700d248551704030500280c4042d080c041c0b101c030000144245409624040101d0f90301c400c0b94500303070031851007516080d59114803100026490303a5010852046079656a480b4448080b802d0700c420120b444858204000d80380030401000008004144201065024102528071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 949967643 1250 949966393 949966399
    0x3010f0b03060604331b02010503090c06120406180b0406020c0705120a0c080303130f030203040305010527070602100b030709090602070c1707030809010c0b010f0602240604020702 79
    0x1500d03503601100512100d500e104131042c0020841c2c0011440c13080d5985500c50941c1d8144408150340082c039006c0e40da480c104029040c40400000100020000c0c040399a500b0703802848180c0f1442255011503019504481c1251014174144000100c00707022503190300582e50025521003195a1aa1080b010b904600d402e0400c62284035008501c030707610303200b08032a1080d204000b003022031583d080c141280c000c41e038001c050a400070401e01200c1107200490f040150340005000918604924003207180d0b100f1648041c205500e00030502c40d1000a000c282c0700048014a820001d150306a5216070b21803c1500c600000359200b85a04c0101c0703001e540010300c03054801410f54013000d40d03603103110b800c0d228040e508a90056000440a003001201d0010074054581810f1002d00c4a040345042075440c151808081d0030301304045080303004c0d0380c49a59241e900c80e61042030400d2550f500d00d6400c2040e50075020700d0001d07020300d062642000e9420a2200310050000c4a44841626010203000080d0701001090b60 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 949968893 1250 949967643 949967647
    0x120a0f0204020715051f060509101407080d09060b030f0a030807271707030c030305070606050d050a1403090a14010e03030a0215061005070308280e010e0303010f0b030606 75
    0x486040240b007017600c24142c010341c1103c5000032251a400f07000683c0c1004040c01024072181550342c0320001400c241c24a2414180c1000c2c584011021490080a000070040a40003400c400e22004035040640b60740e1080000380030b40c1e80041c0416072074401c0311410344090b46c028024040880d21600610350061305500f481c01021804003034404188144100386600c26448840c100003055182d404e002d45a028280907107840360650b680c01d039a1160754440a0104040416040b052042d580d0102004140003024003a8050b40c615180b038031007800e10b0060b02c0d100c0d009518008800c0010040700c5107501e0080000744a0b41c00e080e0813000702c4e40707445080382c100200c80b406c11186890400c0100362030040da400400c11800698040d0741d22560040115018651402000035956040f8080d0b4424560500b003442050f5102c8207031454008110568402e01071002c803264030041c00340e034030040391208898020b001003010404803983d240b00070300c103401da000c1e032056080085c00c0025000d5504000010907942c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 949970143 1250 949968893 949968923
    0x50f090a060b12040506090d080106050c1f0e01140106091a0c0f0f0105011202010c030f0c15090302071715041a0f061906020c040f0615020c120a0f02040207 69
    0x2400c0790010f1031119800182c03c801d01040c07000c20000c00b0340c0901580010480c0030302c00f80300140b81c00b6040c8188014404d0108942c800d11400340f0407c0620b62039684145110107128210402501c1a504840035039481c28101040c1c403441d034840d25050f00d000303455024455191600c940344007582ca260044c00e0b00030600414100300340074807a10000075100781c001c012400d20300904c40c1c2101d0060b4000c10840125024250050340c010710101441c68260420302014920704000765400d1010200003071803d03000801004008680390b00c00c0b841e03103000e5402c440d8015212109000c118001c03030402c1d070b040d03480044d292585506c00451a0351092003052100d01c074003a0590a44480c04041c0d41181031009004104612401d009138620b100740c1c90381045009041c40c0020207501d510f82443c03954040d0b44c590808900321113042d041039008101d03182d08038102c6003510320025256081d0309a46849a40989030f0780140a400045455000c3d40024500c00f554041c0d80c01c001c029800b03032004031518001c49200c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 949971393 1250 949970143 949970159
    0xa18030b0403030b1203270111060c18030f150910060e061e010903060506150f04081e060a0506130903081603090f140102220501030c0306050f090a06 66
    0x80d40a50310940380862000c88681c1000426008903411001d203600a0080911000b0f00100c1d03000c821040d44020100c01d201c2400403180702c0d05000184c02248901c1040c000c5100356400244000c801d1350a0090320490b01404042e124205c0c2440110740c0e50103580d103141208003281e800c40d0450a0765040b54000054607400c001070380ca0aa100d4a8041e902c13804105640c100600143c804400f1804040a41452400081d00d6003e1300c0c0030284c140707030360703500002d80a031110740c4041e01d814007055075140c894911604202c410751260040c00b1150283c484180010000c1c40d100e45c44081c0350002409103a511882c60800a0200401e071940c420040c00040d2818040703407003100c90150099441151514243d01d0041540e00d82e220312404261a04500d0303404240d10001c2d6299066002c658949018042d07106540a0b01038001d484400c1c20b2803003144614403000540c100119002a20103020109810384140c0c101c400c24825940c00044400c1030400c1032900c00f69941d481902107200045031f0b500c429074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 949972643 1250 949971393 949971413
    0xe04021b060705120703020702060714011d01020301090b03070b1c0603020a08030a140f0403021201020c012301091a0904020411040603060e06151e0c0d08010e1b0a1803 74
    0x1c00000300d20000340d111074445003136544542c0200181010341c6440100d40c0850018441c03184003a0981d6070741950071592100c01c0d00032541401540d2151300c1980ba45001c458001d602c28840c0c24600d80c60046111003500307000c500002161500700703509082c4211640c0741c1c480310421700281c00c5c0690f6030306400310060782c51101c1c100203054810004c40e1102001c00010780800c0e5003110500c0c24050500c40d40b5074100280c02140e083d6581940c0003070781d00c01000910390182c05040000e1440307500340300021906a0f4038495816928014400e190510b9a9031032640c821214940360450449510b24903440c001c0c1040c0071003a4000d4806031001480d2440e010690403290040e0300708000182d20792200300300344100c082c081500075808903070040c090314040340c15284520445c03404406d1158007640c50000000b80a041da4007814026059138001c2c005000002d1078500b09014408070004580d0103c1c1c1c02c00b5100010fa440d1181d103004191070303c00c03034402c103840400b10312440e4003001c02c84450100000c2d42c1c00035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 949973893 1250 949972643 949972651
    0x20d03030218151b120403110307060c0506061c140601090c05090904031407050601270209090105010e041d0c0102071d0103080711030d0e10030c0e04021b06 69
    0x140050b1103215070704040a002c0c0421038994030900c41c000c940c003082e188400480341d410b01c4036a05099000354002066085c402c0c45107451031200302c00b0800100b84074007010541110b1504a0542e91051307241c14080d10101c00120380580140e00ca040082c0c52070800303c04486400a11032100d9810303180640d10501500400c0c6100c4c1c01c02e41143e0010001e12009019125080c80d050034100c0c02c008503007000c035514010081000d01082100d03400045050300c10300c1147d440030342040a482c0a5a121080c961121151103020000d529034820001c00c080d64901c01d982c1d00940040080c06581d00c0d1200458004032500718955003c0e644035490415500c1d469034201c460581c00000d40500382d040c20001e03061101a50003141e45e24a8090b614248211010250341503e5201042e2603c0e01c045080a910b146510404990103114140f54550b46940108031900007030001c450144140038800d108806840e00d600804001c500081101c01c15841d240d005030610190741c1c503a446540e0a0303c6482858135105407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 949975143 1250 949973893 949973897
    0x30307030e010605010512150d050d030605100908030703030902031f090c2702161e020a0b0405010e041113150210020412060b0d020a0f05040b030a1a040c03020d03 72
    0xc5060110702800b80603000052100342403003801e01181541040005000a00340d404c4624031300c440c810646da4140700d40b00d0450f00310040b07503007104047c00b000e001000c030340c010603204d002c05e000c0c118607180c80348111005544404000c2c1d0b00340411640c0942c0a0011028100e0b410302624040d048201181800000520000280410040740c0c5080144010300c0c0d41d007015000c24002c240020550022001141011611100050362103c0317080c0c0c80a007a001c000d1004141800301c41d15407034a5040080910b06280c0211141c00c1e05e283d40c1c4120a4051050303201d0345010504034105508a842c042d800300369541c24041c8030904d48560340721041b6804030560003c103000480c051100c0c410036410417040841c450a004118501420103001c892840c0341c8190080c06035459143c03220040c0c9920100350109030703010300408005900d03191407150840d12805400d009500d042004205031a0004e9011203940d000002c075500d424079a0003085800d04020701c02e403100c1c502038a0000058881d42409000300e8069 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 949976393 1250 949975143 949975151
    0x9021e211e010504020a230a06090e060301090b0c13080304090507120e0a02060c1c09090e01060e0106110a0f150c0309051c12091203050615030a1d03030703 69
    0x480159010704115101d45201c80e8941020040180c5a0911800c1075640071980225083c01715802441d40c0d4050690041e0440c03200080054903c1e041003180040d0b801001c054031503a41c44a007170501300c0322440c00190160350407102142d50342d45c6847c000c10b003100c09082c446c610b02d07031500c150910391340c881d900c0320798070b03076030b00c42c00c00c501c15a1042403021010802c0c0300a02c8011240602d06a0340c10f160b420183c8241c500041e1105001d1080003000c104814222402e2240c460704240504940054030a00348041d040100c074005001042c4640030036506d04c4140c8149503401d0190454003d00c2c80c580d241d030140b24181c20741000c980c42c0300d08444a6845146029481c6c00d12022490035100c0000c140418103050803902c0340010004142c00009502a42a9100d40368601800311005e030500c08400d0046850001100188114540c03410030040030b580b010321031a1550014040c550545213000024220300b440414454441c6400803100600e001405110403800e280e030403030665206485180100ba0380e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 949977643 1250 949976393 949976413
    0x5090a12050c1c12081504050405060709080d09090e0102070503040e010f1202090a1a0d08030f010e19020703020a0204060b1c2d0e0a030216050409021e21 68
    0x22201012884101d00c10324040e41440e648560201c4402213240d02400442d400017090f4001c59142412100c0c8000c00c2440719080c41d041c041d894000030f68415000407440304010640d14030010744560039082ea0350b106165103190010f407000030f0104205001455400300442404204200007500280c80c0c0100f662196501d000e2800d1741520807640400d0703500c8071180c405d10250f03950300740160380054103100110307144201456a42c0b50310310300402a5030040c01d00f980e03103040c44004009107214859a640744035460742c8420341903c8012044070b2440302683c0e802c0c000c0c2c0b00e8001c6900a00f44441c4030340102c410b807050b503500050545041e60400410a800460b0b0619200b407040b004074490401000d0405c000c80c1c000d210700084851003001401c210340c0d00500840d1511300b560058441e5110070090701c1c482ca02620b0000d40f40c442000d01403541d4985000046014a0140704000c402580141904c41801c1520103400708114043e107629400060046840c20313030001485c405035007803000c8011b45040d8103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 949978893 1250 949977643 949977649
    0x90c0a0905121023091c1e0e120d030b01031a031c11030a0c0510111b19050d0f0f0e0d03030b0301050106030b0a080a0f060207050712080706051305060705090a12050c 73
    0x5c0300041d006d081188903490450120200d4112414080c1e140c81c1c0100400c04400c046503a0200783d185820b05481140380a1441507071603404030701c030320401340d0b014402c6001ea40764400010014880c256450b030403907042c00305000d11216441c0d400d0709590400f50400394131071281c41e040d0f80101262744042074140e058641040300600c00c40003207004070081006082d0142c25608061b0140c0491001c1c8500e0b503009442410004200000b0061003141003d44510090b00c0e0154803900a01141c1c008545080c9400051502038141180300229603919285600762038020003603600107203c0d06405059480c0401111501e0a026240c042c1c0b22546001c19100030850900103146203036171060341e16070048180c0d40006007002c186040425000400980c8986803810710300e042c130206500c60003092030042c00800c1000b0810327024003016030040000300b00c140d56a101d401905040d246000f442600100002a0098090030140c81c03003000140104507055240c3d0752003409024003140a0310598045116640346203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 949980143 1250 949978893 949978933
    0x5072f0a05041424060c07050118240323060307080118020f01032913060302060703230a0215150607060f0b090c0a090512102309 57
    0x281603504010464031018500f10415000c0c003040880f020f41c8508900013010a030010442210007440755a032036080c51038980d942c00c070302d04c640fa01042440c6100c3d1b48210850b9442c80032120300c9540161140d140000c005609041808001c0a142d6280f030100100c00b000194007510940d419554101410032804140ca0f004040e0b00c922582c1c0c4c104140e41c4607600e02c543c10040d80310350603554044c0403940b640060700a0128603000c2003814170100000c08040e00301c502ca80e0040e41058440c130b0380400b02d181011040d540e107804082e4000c0002c000090010740318242110703085a000b140b00303052509844100c28240d01202e698001a403103007080350410349000400c1034008000400c225040388409000c108180203140020709842d503281716112a05881c0c4c2c200c2e0141c14001030940c1040d1902800503041a00700049680005491110100c0c603414024009200c1d818200014105600003081d454003400c120206051040c51800c00d1280341001100305d04d02841c1d43c0806000440c0503140003040c0c1c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 949981393 1250 949980143 949980149
    0x40603240909051e4303060f0207080a050d06030c1409100e010528090e0c04090308010b090a08060a0e0d0f0504030b06061306050904181205072f0a 65
    0x75601c1c4e9030300206403004c002805680c40015084844011004001d280503c80c15201896122064035441800c025040c41c80c1c9010349100b403134200f00343c070144e08100e0100c2c022948000d00b2020f04200320301c1241e00a002802c44140b074580040fa0301da807070340d8541c0390b140001d6001c0041030740d001c02c51540742d2421140f02c0768000454801c6182481c90814058074141042c41201d005046004c070401c000755240c1c42004011035035241c0302d0740180c0d850b0712440040c641000150440d0040004a03402450f01c3c0c041c0c1900c203a050ba4036154682d08102c51506582d2001980680c0200c0d018000542c0f10360034460188121060100040d039101d40380d4071a420042071040150411644a44e11000d00c0e82002c00c2e58240d94112490f8442541e0b201c002c03500c00d100d9404078a0031441ca412001402607800030007001544001d880030f001070303100c640c00c500d61045040c0005060350200c01d030f282c00681c410f4000c0c0c40107a0245d00301c2610441d0719010345201008615010284240740c8414080c0303410320141c00c0b001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 949982643 1250 949981393 949981423
    0x910091101031a03060601030c09080f0321091e0c0a09060e070813060207020114190228060e1203010b0409060b03060310090311010204080102032a04060324090905 72
    0x8082c070f521000170340f103403c018410b44c1815951030300e1440e0702d07224205040103040810b04650842c0004400255250482c081d0b4540188003110b600c5141050345c41c0c214040c0407a640144010000d822103411120f000c1d080031500c0e44140c0100e092a5626480020010804040300250480c208424089052001026501846020380900001c07020700c2c1c104040701d40c0c000c4401a25588240f004940000404400e084104030210b040007542c94100c14020041d4816001c841c032594460040b02084c5142e026404800302c034074110100468800d0300070050890901050740d21101c50f000e0031003800c0d0400c2e04424045200807a003403004800307901c100c0b0003034501c0c1880380d41545440400039903284d10080380c0c010820b8440458004060050341580440c104d5030000b03540303850301d50048900070b4004071005001c0e441c4480440e0305078045050001520b25202c40354600d020b0403c00158003074440480146000c50506903c0304060380c2440d41003025243c4000081780c40007a40c106546040e242034103001c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 949983893 1250 949982643 949982681
    0x80105060312071109041203060501020601060203040e1b041206060b09062a06072a0f030513050616030323190b06040602010c12060617091009110103 66
    0x241c0c0d00040c094003100c8852120300c2d9540001c0c900350b200c40d080604d0654014080300d0a000c20440b00d40300403030200846176010420720b650f40d0012039807284207100c1c02000d40c00401051040c00500340400da03024584074400c0c800381c5103020650480f588168040c80c4c4400154503464200300c1d040c092319000301080180c40b0704002114002074034a2198414841501c1e01002440071440c00c510b04015103c50800180c5140d0728008202034920491220701c0041c10240207421005841044041c0d01440e800010020400140341d1b01958181d1007030301c50a0b400740c1285d90010749030b03649000411102e10b00900c010000040c82c60003405030350b900d9559030852230100c0c00070840302c0000d010255000e00c81350003809031000a214044020003103030051903080b038000100843c07a00d030150403465421920fa40d80204c4440c43c40400d5044030300d54092b5074009844001c0200100a5804c40c01c0d42005035001514001c00f8003140e0070044904002c0700f2601030b80c80049401507583c05204d800203849a10700c0703d42f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 949985143 1250 949983893 949983901
    0x309140906060c0a02150c07050301060b0a050a2106061101051506220803091f0203030103020f060f070308011e06020a020d17030711010b0f09040308040203031c05060a080105 77
    0x280d0100005101600461021441c0d001c01c100c2003124074189500031342a8130340298580700c10111580510019500e03403003841000600b40c2014800c500840e0041080141000c0f840e031400c030b03082d92000b0800001c010f56a800b210480d002c210001c00004815040014030901d0f001d0050100058a01d0207140750340b410040014020040e0b11150402034115400d907542d11150194455a86514500c02c64411400c0004103a0070f400000038901008110b4050842ca01244903071016a6141050440144c106200410041c10041844000468000c10b1641441409058600302e40c00946083e030010b030f00d1800400800400c1a05000d50140b01680c843c451030900714081d5590301d0481c1c2c028001c0c5141d50b40c203002c9c072107503c1c482418250702c1c5441076078900f400c050007025400c3c00003124510f9440d000754122940b4000b05411030041d00a13004400b1079503142c40684000c000180280c0e01400204070072000413407450701c16035208010350b40000e1503040441c14411118542d0700070345516850003081c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 949986393 1250 949985143 949985149
    0x90c0f0303070b09010e01091406010918060e01020d020f070309171203061c0c06090b031005061c05071d030303100e0a060806010e06180f0c09061b0a030914 69
    0x441c034581e00301d09103c0c01034448412450043c840704071901c40c1c40d445d0071501e00402c510a4007501c1f101c081d8104603240341e40c075503282800b154400342400750591481070b005400581d01d900100b00e0314482c0b80005080c940d80c032a144090742c0c03200e4070a04200c07000003020001c06800c00c1381c1101030040a510b8003108070000f5080703035403409000080e0b11400c3d004400503100b40d9601030091041d1710001001880403c0d28501156040f05a000300c9001c580040004a0a103641e641a01d200e42d0729039403400403035403030700041c01800e52184c070b6000d440720300308418440c1081d150300800307000704529660991200034020207011500c2c5c00640c4c6034425002042840204804081240c054400c038142d00d00c0c0b42e480e000740090081c103403070740040180d0041e140000f0710b10092049407882503038142d6080307100341c034a0441c100807294203c80081980c2000000314100f80550406010f603424060a0240740100018100300094083c02c03082569602800e591002c140c1c1c0000340000400c4503005109030000701c1800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 949987643 1250 949986393 949986397
    0x3030705070203010902131b020a030518040f0509100e030c0a0b0705120702060a0b030a0c090515030105180c0901270f1802010e012c06070b0708090c0f0303 69
    0x80080180c04a040030940d82c007907000c222882c1c0c0c001d041f900b4900300c0041e0b8601505889410700010340209011400d007600220740c268030141c0c140e561918144c54400425254144550500e400a0762441904000c0c05a48502405030413200001d010a481c8241c0c040c06a4400036005402d07030b0414003216844c00380008003104410350201214089584103103088505005500048030f070642c1001c14480758580214a03030380200b01c226010700443c003405007410754401c01e0039402070240c00e41c2c1908000808031a0b0206800801500450f000d0700280b00019007529002e66a003440b011113105200742c1190700304101032a00006488145040d8908040d005030004210651a10b111985400138002011640481d09030800041d040082a0383c1d02c0c5070021913042d5500c12070104404000c40c5020b907006040c81d5018406402d46544078501d40d022100780800c042440541098090180e2000504200c00c101e11641c0e42c0e039a400710714546507490038a0142c05031001401440b2040224001d9100402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 949988893 1250 949987643 949987651
    0xa062d150914040b06030c030106020c0f01120f020c0d050d06120503040608090307021002010506091f1701140c030714040f06081f120201090e01050607120e0a090f140103050303 78
    0x410003445070700b480100b00a800c40c0820903910403c000100720011320884080c5068400f65421204500b00350010301c2020664010410b0108500f04403484c04c01450350001461110910000f5081190149565240c50031074074a410100b6801f240320b040014640c440d00c0018003040780c0101e100b58091700c40035141d00c00d07030240c3d40c01c1240030700025412140400841d841c1c4c590240c1000300005072820028000c0105840c501c0c4a080004c004c41c1420540e01c07102114040503800c1c1c50200340c5082c001c0c00311514040d900102d103540303070030480b050103318005180c0b150b0062941582d90f490b0103c0010b1801f01c07026844414184144030a010058021401c1401e80f5a103050542d1a501c4141d490848821450321011514160304400b14114041e030100840043c403c1e256405810380300d07201d03c60040d00900515800100520490022540308580396081e09410f0904444070002e190124440403826007040c2ca217580c4503614449440043c0c031640340030b8421440e095034694150b41d159900c030302c0060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 949990143 1250 949988893 949988909
    0x20a060f051e0304061a0307120203070e0903041a40030507150503091b210607200a030509060408010203040b090d0f050901080a062d1509 61
    0x4580c05200d5010790101c0e00d112080215010300c00007040c1d554009680110390444100e820200c2d01d818148040c210401301e80001005440384505000d05014204404881641e06106035a0001242d9201f0010725004a40315000381d40e076507080c40e45040c003862000004280010003084040100d44461801c0f042032208080c608a98804d18103243c6074640d19251a060411048a800010054000384540c1110f01206030000d04000050055580b4001120100344540021903907403080d428245030030411440c001c0c85c0c54003c004081d050f143d4810030040c044207541c060001e100a050300a6800e124060343d030100d009401b010001003580f10520601c0080c2408008a04450240d40c0c40c410b4030301602d4020002c54480c074013030600458500c3e00756030b113a00074002c45807030000040c45650b8034411901c0b243c0310940f5000d800c4004449030400280b50101403645d13500c0c081004480690003c49040905011140e20030094182d828041556404180011400d0031a018901e42001c49141160201c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 949991393 1250 949990143 949990157
    0x170a050d0f0c061127151c0b1f03050106182409180504060e0607051c18030c02010215060a12050f06130b0a020702010c0b0a09051204140a03020a06 65
    0x200203c00c55000d0580c00d0000d03e0030140705d02c4142d001c5507181c20f061035021244100c01d200d0362030180c88107200c0c64030380b6080d0616068070b40009524a40001c0c11000b005000c480c03031035107448802c141404440d265400003c0d155001000207507400084c038270001007010400d0b804145468900700300c040740c0c80c7e9843c81c1d205068480031203090050301008010010900315810044480d55890010482100c5c03c07104540341140c012584180015070030310848258550ba4504001d03c0c944a003a1044454191119616400b200d06e00745c481e281d4504000b8426116203200d01180e10001e803c140b545040e8800e4290b199042144c1603131100800c0c400c49540141d03049201445091182c286504210710400070b10400b01401140d120914501d4051070141c2100d5a031900d40f4000b000981c425a0030103800a0501501600490408580d064203c0041000003900100315525141422200d4100312000f882c046010000f40301103a41d41201c035030b8101d58204101d400c5500041d0405010b010f603900b00064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 949992643 1250 949991393 949991411
    0x603011b210509070f14181503010c200a031e031b050310080303040f033005060102151e0405030f070c06090b130302060a0306170a050d0f0c06 63
    0x2402000e4202a081c9800d000901e001001c00b80d403450300c0d02c255129407035050000198011621010030301010000c3c25003030040445e04000c44010b2028180000d072078a24500c2c01040d03602441910124141500c58103e002e40140009040002e804c08610468220214400002c1d5000222078260301c1c14400381c291489007100d04034018041e9114500792604121003a002c0e00303070014041c600c5071000f002c081c4406500c407014a0b840c0d0000750340c0103041c0c5554410b900c00007802000095407980c0c001744003540001440302445a0003e0b03c40344003014554442c00e20010b5641070000b00d18248a0380f460716600e0a01d0000f01507807004000809001543d01c8000c18100402441120b030180180785006481d681c603070412800d10080c070321070300340415180d000005003118040280c4c0c222900b0345080b81140d514503003d001c0b03964422540c54040594071800032950b04440304518901241d01c000030540c000107441c0051401c0e07610481d203801c1c00401900c0e1110b0741d500032400c6c00520b03403040c008554422 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 949993893 1250 949992643 949992677
    0x106110a2303040806060f0a03080307050a0e10030501090e0318042f09032a040e120409020d230c0903190f123f1103010e0603011b 58
    0x80d40d0010020782e00001800054580300011040d01400d0100e0301d00d1003605140080003095a01e500c002410480144002085240150003406406403e0b00b00300400340811070004a10251802e200000b00380c1d1900107021610551060074a424060f000451070702203000e00f094501c0c0c0d1140d0a0b91b02c1152a041004180c0702c0000100c075045081054000c09c0520295085141d5044200300902a02c200c01204c031220070b003c4d28000003c0080e010154004c07004905000103040002d44c01881d912031424012003444880340100b004003102038005840702d070910503c1c02a241345d10382c25801411141540a0300740d01360505a5005102c03440000d941e040c1c00c0c1c010030f00784000c034030702e2000001c00d601e0b03480140b000d001c5803e180c5501c180c0c892811114061015118150312940388009800c0d40210f5102d4408030f06178403801919004c11210f00d00114119000c00d440101c15012002c400100041041201444560ba08600100e0082c00100c181094038640468101b402c0b00801c072042060501e200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 949995143 1250 949993893 949993943
    0x1602150706060b04210c0b0c160611100e030307081503010903030e01140906160207090204030809011b031d01051c0b01090e0108060c03180319080106110a 68
    0x3030790080c000e2044580d036a41c810b05903001440b4035030880e0180714810310030140c2941d05480e000c2d0710205001d855400c0c10824901d0340c1000c50381200c9032164880814004244d609103900404007941c1c0e4000c40342d40c2d6105503060141c4076030703d00441e60821a418041e000c020003581c0d0f1001c16460026040d98405014010200c4881c01c80368040d46417a040c0024141c0c1600f15074100a8044001e02039545c17801c6496900729001c0340c1101164002ca408074103140c1d8111988600021030384101e80400303868400f02c10481e03003d03a20440d4a000b0000c0e06201d0b4dd40c0003145022811881e0f60048280c00081e18042c10006011100700c0101c0c1c40c841da088516030007042030300c2180103a50340c3c042c030005c400224031000340101a44680407442c00f600000701c80314501c0c8098183c0355084090140d607207800707564240e50780006e42249068a000d800030220050100301525000220f100b104a08440c000c501809041c1c041c0c22100400503092000030210320b00003000c004156001c0000c125022880030038540403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 949996393 1250 949995143 949995157
    0x1808030f04060605030d020a03050f09280605040806040303020f07060213051903031205040606030212061504020f1902030d090c090c02030306010c0b131a1b160215 72
    0x15004024800c403040315844481c403403071041c1010090140c903001015901c8507248104001a80718010740e01c000fa104c0c0010341000008a41c82c641014000e00001d580000d40070745004d641e11100001c61110b0490360304950080c0458109503152038146502d007034491400401c0a8241500050062498481081180da100e904038004648402502480304401c840a2181d10b201d02c0d0302070f604866002203800010202c03685904c1d0041c40d09213140c15000034210040c01501e00a50701d032400400758540c0f50784104125614400b5110038a0f020102001251003410014015441400080031424548080b01d03012503c6c0d07031800000c0c4120034130880c9503204030031280f69880d0929000c1d1041101240c0c80d4410b940140c1740c28414403100c200708aa490204550460000b894107030004082524401c0c0142c02400b18034048960503030680ba24142c9124161680d0b080c4140c501c10400c140e040540200302c007031022100e1628220003100c85c0c01c58500e24141c082d2040c02030903407290210004200719915 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 949997643 1250 949996393 949996403
    0x7051005012405090d0204051b0f0d05091b0d0c0803040815162307050a080a11060105060414010513061e05030108060703020d021b0d0f0302180418 65
    0x12540e1104404082d2107904071440040340e451100c119819801081601c11695001d888080c16078001e0f001c120140502900300900c0c500c155001c0601d100c040c2c8001c0c600902c51222803075462021060510440b00b004203480f1460708058115000c102c0c0a01c800d0008290403944c07807030b58040f40e04143e20003101c264000f024034071000030005070f006004240c00c039182c00049074184c496500c138440d0f0700114801079500c0000911211418042c60700084c0c4c01ea00f03249a031140f40e03080402c5695014503000300030f581a00e603004c000c11090341460f4403400100b00105a00090080d41d49032401041d1540540d004000094180e0290b0380300b03d9201e1419240c1c8260016200e0360f00c1607440700060b00e00d84202480c14903844010820300e001e14080d4046074100c138401c03c01820180da41c00012002500011402d10000c0d40801640c540d0350703940380c010f1080d031941c0780207000980100d02c0042e1500421a1900040c9801441900b000c0c0700e809180c465998402c1d2808907800119200400f0741202007280140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 949998893 1250 949997643 949997651
    0x3060402180d030f031104050303032d0403030207020901091b0e030f120c010b010804030203180609061315031a090709030507170607140711011407050a02040b06030f010605070510 79
    0xe01d944041d90110000c1305450800c0a0303034080d040014148a00e001e041c2d0554004c04c0490500084e120f41c444400d044400404101880e40325100124501990705500007070700071441c1429442e0110035a40100410035040019900c41c90700c0748640501e07a049102881030552001c400f5440c00e210035100342c40c881e03056400240401d03204060a8004c0d4660a1096103400c110380d5084d4042c40c1903078040c030f4064008601708581d502145200d800c0d410100da8000109101110311529900c0142c00001900d803501341050b4182840501103074100c0d00d50740304150400f160402d001c04402d0004000920a54026106603100740c0251a048202da000409a2103180000a411241200d03c156032401d014140c1c1c0d01a119800b01b10b4501d48090a44041c000080101e030b4002070596462041030001810503040b12048080300d001c040e00585010340351500400d00d400c1c11850984100e01000e5003c903010342c154203000d00383e0440c80300140100030500000290000601800300045e030524280210148 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 950000000 1107 949998893 949998919
    0x60904080d020c10180b0a2705190807143702040c0c0204060902030c040312020f010204171905100c170405070e0c0405060306040218 59
    0xc6114810b44d084080003c3c9240a040040340041204003c1e80a2504204104090040507411a6031070101c400c10740d641e80a1260880d1401407040380d404a03080c0ca05107251210100c801002d0043c400407000410020700002c090701c6206000341c500081e4441219940d401140c1c80360800e00034584010f194031140c800c0c4500070700c9500521010031143d0380d0042003c03203221881c400c00203007801030b100c41503042a000340e10050001090031840e51070406110135450040d40002401c0d0120a1505000c8604c2049210030600b5000003c42d600c6039194021000c3d8010401446040c1c020728000d46810380130b0098103202160003401401c1030820154005000f0400e0359040014072070440b01d140b401420301e0381d041d4803a0b031084000300101c5007070150054a103031008110a06184041005000c1611550141c0e904500240c0d400744c1c807106114a20010380e0400103080d1b8010250402403 = true := by decide +kernel

theorem cover : BRFrame.Cov 949820143 950000000 := by
  have h0 := BRFrame.cov_init 949820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 949820143 ≤ n) (h2 : n < 950000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
