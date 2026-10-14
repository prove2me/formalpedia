-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3731
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:31:06.535805+00:00
-- url     : https://prove2.me/submissions/2489864d-d6f9-4dc2-969d-e245538c597a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 670863309 ≤ n < 671043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 670864559 1250 670863309 670863331
    0x402031512030306150a0c060e0705032a150d18150c090609060905012f0a0c06080609060405071106010f0810020c0303010e07030f020d0e010e0706020d1101060e 71
    0x80341603c05e008041503541d40300c001d5568100030345110b854000c000030001c03030f4200c80d000032080740d2004410311b4400f00e80c2241c0e5143c403d50444404c0ad5003120360301c017000ca56002151402c22006000d110031480e04000203610503505024860f892040707603011000d45042c625181804164603245d9141100c48200120012603c500030a2421900000c000c0000c2107149000c0905601c0e004004010704001d0003218100300782c0500070035145018030b081c0e00c00f0b0b080c41c1c1304032042d2036079a1404c1035582030141d00c112190b00100340e0010301c0f0b50003401002d00c5003c002e0300000d000d030b4031481003000400005205100340201000038002e440720801083d4007908050716070b0114a4201440f0600c0c0005070401110b8031801005510402c8501000340e9044400c40c90034000c0c551030340752041d8040c1c1001e104c40740340d9a201064598801e84660082d004d02c800c2d00d0003c001c00c205d070b42d44090b00c50020707010303003005a0310641d000d590b0303148a84145610010424000a07025403a03e03200c0c05886000d580e03000c104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 670865809 1250 670864559 670864561
    0x1170703121e0c02031f0e0303100807060905130c111c020c330c0a0b01030308010b07020f090711060103061d0a11220f0c0816090504020315120303 65
    0x810444802422258190a12083c0005594000381c2d44141e000303840d025403104900307100b510300c072940c001c441240d401100b070700d440c5c0c0f40284158042100c18428803070a80300701540011b1030345c0244e448500741c0300d01400c04002c000b903000040c40500f001020310b00c10081e0170410440300c204184900c0007140b40c1480b14020380210035000030318018400e08410310410841c2c80020b6003507031142120290485003108418480522580e040d030794011421048414010f20340e5010801c1086000741e4140c0303100780c80b00003403a43c071007841c90f55600440ca0002e4001040035103083c140d181601d80d0942c41107841c40d101c0c890000042030681040e0080c0c0c0100c910980380c074680311000908420260032818060700a02c4203c2890300c941c1c12000c032151106000f42182900611101c00c0ec40d00b0400c200d00c1000c0c240700c00041100c07110000c1129018940015a81d44042208188408010b04019400d40c0d00c0c001000d040c141040001e61018002c48200340000480900c81e44400b0300712070300d1586a10286480b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 670867059 1250 670865809 670865837
    0xf040206250c170106080309090a09020a080604050d0302090117150607060504050d111908130303050901030b010302040812030a0b040e070e060a03020d080a110601080304080106050a0e0117070312 86
    0x10210341003040f10b440e4100801882207a1000054a4402c0000c440c011505d49034100c02e00020224170102a400540803100400c01e07110018a01d401988114225500400f003917a0840403406148501c030700040c030903a5191076204c0c0c65026990056144000c03810b400c1d031024001038145d2321240d0101c885503112804c02c42404024886d40144050904011071000d071408945922007102d1384120444542e810b85c0101445506001c0d500d440d07803070940c0c55041c15101c0c10301820940140c3c0c21180081d0404920300007552282c0265803c85a0503c0202142910700c6189119604000d0082e180c46607a00c0a41119540700c0c0075104414420364050407002d400c0000344a1400703401030801d4011400030030300308010307240c0b0805160110f81040ca09622140c200c0c50481c0c0985a0400750191485104c3c004503400c0d0012004104a4070b000c0020010907582d00148000c401c40c41c8103004040001c640100596015440c545190014882c242d5007210349035561890610081340c0c0300e50002d1400083c1100d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 670868309 1250 670867059 670867079
    0xa140301061d060a09030b0415090309030b070c081801050c01061202180903041a160c060906020708070603020c100c03020a080906041101030b040204030c0e040501050106080f040206250c 82
    0x3030102c4107a904034500582208060129070240c80020706418a100009040c409a90030000081180e040284031104031424000c18030a440d000542d520440040031554850180000e1402d0f10b034451080c9050515404c50003100c4151f00381b07014140003041001c6203e0035804e100c1c2e00d016182041c401c0c10030701d100b40140141080c1d05028460034603000e200b406162207000040d00c0c1141d12101c0d8044525500728a418003501440c09824450b0345c0f030710510800c20090300c00b01c00640b00036548007070315541e89a10032a5148a1481250300e40d820100e401d220300ba21036001090205014000c852003403142092680c1181e280c20040800280c0c0454000d411650108071660030000200003004641860340702d0301000720300f0780849814941d40e5400c1d003006859540649004540182c489454542d6502600300c2040e4100c504881c1546084004074a05001d2202140110881c00d8401190b0b61154240426a4810302d2244d078488041100c05c400950104580c214161180c0341c071010309498031b80200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 670869559 1250 670868309 670868357
    0xe010b060406020316080409020d1e021305040903300b060a020607080a0608150105041b0c08030702100f0b0a080715080a0e06040807030905030613020103020a14030106 74
    0x1489160108010002c4507400000e0700c400c2111a24200c114641030324140c003482c07065910990ba42030012611820002907076002c02c0240da000c600550030141048443d104034440d0030380903155009680028409820f040e4024941244a410a400211010307a841803030860a546220600355144040e003100500a00400034a92020703142c3c0e41c101140010069181c1d41c00804070020000c0120005254030544c0e040007008081d00b10580b084603a0040010104800c00d006480c0141d04282c1d5802c0c0310b0407182203440801556503104108180e0320765a02c8800d50000d020581144504900382800060382c0c820300c401050800340c009007070515501800306001440d4400015504800d0081084001094621f07012100501e48000c0954500c91040002c051007512610781d84141c60401040041c41802031180d41d01030b446004146aa0b041055541c0c0e208640030000d409400f0003850065000e500600141801030400480148081904010700d030400d038084030008000020015589007800040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 670870809 1250 670869559 670869581
    0xb0429060306010507030f020a0606080d3903020a020310051f06020316030903120c150c170403030e0a0c09061d1b07200a08150a0b0f060d0e01 63
    0x11500310b10700540042c003640140c490240078048a540102c00062080c40202c1c14160700080800c55a07440d13070502075880422001400100d8200300500000601e04000411450074009624034a01d0012480701c280d0760082e60b048055104241c40d100069400348540c0345400c195000005007840c02c16260480d2030201d500c03204414050304810301c206680070084540405064444600000040c80e0407904003c4035440906402000c80c00c00b10700325841003030380f00c046000c2d409e404191049a1440c0003100c1d2214042c501140610300c40c01020700560001b182d12900130700b0009a05541d40c0941c506041070b0364402c541c2400034000510240b1071502c580c40c05041e68500082e002c2c000701185903550000070f410f040101081d105151a0081e0b0710b002c5580150f80500005110710714100115044c10384801054802c1c070138000040343d0090002490040403010700040c0415840d403240c0300b0014100c41d24604d421011982d402c51298403410020001c141100704000740444490f00d030903007144c034180b980d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 670872059 1250 670870809 670870819
    0x7080d0606110c010e030c060d06090b0307180c031e092f0d020a032f090609040b09070512030c0d0c080a210509030702090105091902030a0b0429 64
    0x52000e250b002907800d01240c000e0038020074200e41d490001c1d00d440300a603038055200c2da000a402044001c81e811010454088610030f20000080204064885485d4000c840707003441011240d980142054000c0ca1400b0428180050100d0000030161140401c46e159030030100c0d140c4240380c0030400b24400400c0200ca0f0b1110384012002600d552a03200d030b0545901b01d205103200c51046d019943c0710300546004541c001003003503524882c0c0003840c0c0d1030481c1071240200342050940710412803d01c20003c611949000301203184940e10b942d40e518040801400c0c4118511511502052a1f101c07074458411041210000310703260a224603405140050600d01301b0100504483c0e110300080801094502c4d184c9681031a8005540307040c103404501c116108c0e40d44106040200b4411042c4022006010050098880070a107a80714418000e00d070358295071020800035161245a10b4000c641d001d160400350404002c200040c4000c00070701656003078035860241400d4070403068070000c2036030321a0307206070402c2d91 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 670873309 1250 670872059 670872077
    0x9210209010f0b0913111219110301050d06060b0309070e1503060105090c0721020f0d0203040b07060902030a030e09010918080c0a02030d2318220207080d0606 70
    0x101111031030003400611360080c403140e000d141070540b55420a211800d0000c2c110f41c0c80d428000070f1102d1189041c0c44510b02c910ba241020341012807a40a007102003036894a40c0c44c41c507417801c0d05001d21000c02d5001075078002da071001c000c180ca8882e900110701681c03041004041d06410a10320080c0540c020700b5802c54280c0b174146c00a11500d011440d94111001200c400d209a61445143c1d400e601c03c08100610020b540c41c3c0440204203c814003655034156942140d1914800c040f031180c3c0e5000d131400b15005a4418401004201e00040c014805140700d80c07000720700d151490380401d241144c464000c4010600d20003c00450b400e00704141401003445060500c500390342c05241c00c2d4407450294000d00400030001e000e20142ea07003000404401d82d0b015085072100c40201c02d0013400040c071068904283c00910126a2440949134103560702e0b41c21266030281d02400e12000c12109481c0100344401a040c030880c1c007a102c03089440076250320741c0504174169503006040f1040040300c15507008a014020b842c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 670874559 1250 670873309 670873319
    0x7021e0a0c031b080624010f021506040e060903030a1838040308060108010501180e07181403070f0612050c09061602090606030705071209210209010f 66
    0x61800000c40b07030081e805403400180010f404040c3d10080c0c00c0443c0ca0300c0f03001c0c02d00c100a40003003081141d07581d80703907a0748400c140520011030340c544021701c460340164081c816401205200250454022034000e00020303003450881c1041d401c00b1803c03503910b0b0480c0c0000c010401000e1b56030040b007407070740400100500003c1066464202c401c030780021450701040e44841c0461100d0b14108500c8110901c001d0140c1c0c80d00d05807400400d904000c940440c0054010b030000140c45d4040c4040a200c3c07211164042d83d200e00b440020030300041d0080148041003000207001030f8200054602501810700c602084481c169100240341c5030805907070004c048110002c1c010090701c0ea00a40c84040307004e46040c007048a4842c140068280d02803420316a0b40700e0400221110f140c000d440ca84c4004a1082d548007005a0b15807080003614001100d00c40c02081c006c210800c0080c401c400400a00040ca0801d20300e00b940342d1100b00024180d41d9440c01503120400203030000c2d0302d0031409040c014105144482166824030f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 670875809 1250 670874559 670874573
    0x1401030b09012007060b060301090506040b220b0f09090303010e010f060c1103100f0207021804050337120e060403020c011404030b10062d080c0c010507021e0a 70
    0x3100f251600c006020415200300095504070701c4080c00f00405558513561142e01a0004080949601d8422850030f00712501500b080403100c20464018101102d41807520a4028050036813502d00c143d201030043c540d188079541f950031041c020200388004581320740c1070440156032840103070018200340c02401020400aa481051110910791107451202140d1400c0c010918040a08411241c01810b01700100d102c00990303400380040710b00840d10520721100e094036030707003120038260f4001e85540c00030441440c3c2c05048014240c04020407005003820040c1030101c0110500d034004100d00003400b10014650034262a020303802e0b4684000d40648218181942d0103590303186d8014416062007104180d01700b0b4000054280c0d4015074000c1c0000202e89440401645000a5801410045100c00a600e500b4585100180000e01d40c0c03480380d020325100c514025a5050b0b070080403111817200070400382a00300002c1c041c2900900c03582c0c0051015491300020b551070304020042c1c501d0709903c158150000b00d040c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 670877059 1250 670875809 670875851
    0x10302120a2001230910030204031101050c0f1207060b01020f0705090907081b03010e0307080f0d062103020601060e0607111f020d02100207020f221401030b0901 71
    0x700320446014100020040e134240c0900c180400141d0084840e000075059420000d0100c0700b001c0b50030814240004805a04a0150307000180020054203503001c0c0550240d03008010740055402150b084010039400c0501c2c0201d03440c0b0306880c445000c01c8003010080075000348444580240064251040c0345800340350307511900e01c28103204170980030114640180501034030025200074400d403a5028034840c1e000e0b2680b010312002e14000e41c17900c01035109240d000300544108650201c0075500d440c582007001300498008121a07449655203410026046000600c0803140e2a1300313003500c200d207003840d0902a090940503071148052000415115920707644440441c2c41440d449482c841045c0c80000c081102402c01c203005060204e074158444003040d400040d054038840752542140c800350091401c8900b41e000e0404000e40200c1c1c10300140741c203440e0020703403030386a034003030a203400b020f440c4000540303055401d903240c00c440c01c550450041c0140075840060551044090000307000001d9400342c100e0401036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 670878309 1250 670877059 670877093
    0x20d051f1a01120f1d070f05010f030e0321060301050c030702100e010b060a02030c0610140d1703010b1804020304030801120c0305101e0b090109021b0601080303010302120a 76
    0x1040f00740c8014500d656510100300074080344401c220a2000d1290310b00b1244107910072004500c16100c0c0000c1d03904450410f0410f80d2010795603d5a042083d100a0780581054054000c10780010f200c140c0c4003400d9084d84005901c401032043c0700600300300040c1400c50b08058210b810805081080290b001e800040c8070b001070100105c001400600095400d0042c0400701c81c130355202d50001104403d8590000c054864110404151090303600c4201e0b0303001c0380c01e80310710802c0303c000042441d0240c5841c007140751500d103030b0240f078100919010416054481c2e034826003101d2a1004045200b404601250700b1083d80d010b0103860443c51420b081e00c0180c0a01030520a449011281c10400020880419008001150311108031400800c880010401401140201010041c40461119070403100d60040e030705483c40181c0201c135140d0070112103202a600803101d1208081c110052440032020030401d40d4001d09245000c0c41d129411031040000114003070380c515040ba48003048190108800145003100d07a5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 670879559 1250 670878309 670878317
    0xf0e0f0c130e010609021b06010501021e01020915130e10120f1a0612160618180c200c06070f0203060f07080601020307051005090703020d051f1a01 65
    0x184500c1e046000d8088601450340d15400c00e2030000b8424010f40160411403840301c0301808107001d86100a035180001d1040c680107a006504117007004002f0750b0201e501c4d5000100140c82c00c440a000310780100701111400e503102e0400504481018510b98508002d415281c0e00040142400da0380c1b40c2002030b1742d010b110f11040b20107606130b00304402e082806d85800e0307010a5038a40c85480708143c2d810240100c5101c0d000d040300810440c41c03420041200041c40407000c107440e00090030484100c4034030001800c40c1c0703c0741e2030000006c5140c01c0f9221031041d041d044020042a01010511b0050800d124a0002180701c8101001040307609070108106103607810940d80705441e01400c1c02c21822011181e40c000c0e40600500041c00b0580c4200c0704454461509901c0c0c86041d900c4440c0126601e120f43d40010f40650000350300304034101310311303040030fa080003810b81102d4100ba1070b030b00056010748420f0700803145580078001c034002103040c001030062115058101048a090711601d015078200c0b00c0a017060401c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 670880809 1250 670879559 670879579
    0x2070b0306040c1b0c080601060509061204060b0a03050105040c0503070f0311010309020604081c0f02072711120105011403270607030606080a0626010912030f0e0f0c 73
    0x105200350244c00080404603080340501c0b09a04100100003440e0007401d4490007190004aa12400b50703049492001014046501e422a2035002950310030f400341085451945507240fa00569954507809000355008a00009890601f40b40c0384840079460740c07002c0d000b604408002c00501e01d84030300c48001c403904001d40c4104c5441c01c031300490061103095002544120301040c00318510700e002520352003040b00641034401015002e402540d400b04030118100050b4004071040c0004039180c48608226142004400b000100b0ba42c105000e031050301d01404c0000e480842d07290203100c4821269801040c083c2445032034080d1422038411148402400c85500d0284510300c500c4031100304c4042007200740302505507030f0a07051402000b40504424800e00300001c0440000c81c078800d05a01c030340400c40302d000d1030715160046810030b004040c9104c440d500300d295699000f401c003c6444400e02000c21103050790000764072003520000208607510f20740d0000140d44601c5c00014034410014554200210880d150f05003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 670882059 1250 670880809 670880831
    0x203121009050709321504091b020610050109030605091c110111090303030112050a050312060109090207050d0e0a0b04090f0b0324060105160f03020d02070b030604 72
    0x400207948004003080c5030008100010703520408010a403640100403817075240440c0304135400740004004440c102220940071814510f40805101c103d11039141c681400c0c05d6071092401c049600900c1c0c0340101c1c6203d02c0b03010800c282c0c1404100da010b0084000304c1901410840003d0100c1d1030382c0030052285035214041609640c00b004600780400304e0b502c1c0d2200e41c80402e04d000f8103020f040d1307040ca603896090041c40000b0b08401c03400e45142c084090f00550070b41e0310b0003040c42c1403030480c118250381d54041c10b526000420f40900040600040e41002200c050402500040c0303102c03035642c000061248140300210000d1004240c03209170041d903141680361601e4007000205400c0141d804040b008800080010b5130b00c1c0250400c10310704204d2101000418500b0b800d06803229000096515140307807141401c00c0f41000c4544103030704558189031079410504840080410b0f10070048007914040508007042007019810003a0a0b44100144090705001c4c3c501002e19a15000180ca03840c81161100c41e5054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 670883309 1250 670882059 670882081
    0x19060902040b1f0201050108010c173d050402090f120705061b0f030c0604031b06020307050d0b03030a0c02061e2205011803141f020d0506040c020312 66
    0x90b90100200090400c1c41424502882071144014030f0b000f55003004000141410180b06404c4105803646900740703e0342114007441c42c00f04004042203c1903001d0001c044048075660040300c03024030790031194000c00782c00e90900304100106a1003d84554010400382d0542d4441d840510900700054802622408070808807a0038203249410044c0c03c200080740c4491042c3d1341408444d80c1c83c031244151200300500020550300d80c45804961091a030118002c5400203216000090310301000341400c03219141c00d541c414041c0e9000f03441c424001503010134082041c01040c420b800074050b00702c00851400204440141030455a80c1d00607204034004500000041118090400d1681c00110b0b0960f5500409130468034030000c1d0a800107807600410400b0600e0b50103604002c0138202526900030b4921b00c0c690b540e00e43d4507a600501242405200042c4040d0080480c114a500c010700300c015031240100901281104c0005001501c10ac1c101400c4110b42d0303401008480d0420000e60003070130a82c3e40d50f50a90 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 670884559 1250 670883309 670883321
    0xb07112407030c02120c181b03090309030d050a170f0a0209031609091e080d0e0c10031e06050904030c050304120506010e070201050f0c0a030e01020d020702040e1906090204 76
    0x650080030711100c41719032010103c3c800c01c500301c003241e50091070b002c01c45130029603070340c112801840010040c0c2c00e00c82c2804014043c5500141c51400c69260810f00b4001c0b034100245c10038400086440031030b031030040d940c10511b6001c181c04008003080d003a28040d5007a88100b0b10160450740900d50004116080c1d44051005030031000420901150f025680c8403c00014004c0c6070042d00d98001c5400000042000380c6d4402414642003413090b07052034003454800000f40a8008a075261348a422900801500d50b0647d10100b203007203440008031528841c40c40900c0f880358200c0c1c000011f1408a05010661b0f40c0000c05030030980500c1e140701e00c2a0f0901d80540b0f148a250050f0004035100d600c20801c1040c0010f9581c1070f5002141c5451482d100e14105900380c8905440d60540c0c820401c1c0041e08943c0400082c1c280090149000b1628022400e10142240d00220704050a242c0000700c000c25801e260040300da0081c07951000300240404d00c0b15080f5010440c00005003d80d8503a4840011b40d500e0b030b0029 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 670885809 1250 670884559 670884563
    0x30705070c03080a030b0102030a090e0606040510030e010612020a090b0114070506150f010c0f081b0105091b01050a1209020603070201050901050121080c070f0b07112407030c 77
    0x9481d612400c000e190740c2c2024091800080c00c000300d550903940301100380e0741003501c01d40362071380fa0714180001103541620007001960040414007002a043c0d54000360b042000304561000102007802e026420709640c4980c11003503074010500a0200181c5a864004040b18078284001640b2820440101ca6021040403810300300390021401c40c041c80f902241040c01080c1c0c4c1c2c10240000002c031001c4c8410403c140c07001c54046104d090300e0310003041c9045402006580b003001114a06805481441c070098055144503410b41e5444080100f1020304000c020b100c01d4440c101d07003481094200000f0f19070b104c0c110f0000100502800d0b08182d203241d0b80c10685100707500500440d182c0c988884003c0c02020f0071211b181d540d6081800000f50384801590f00a903420070300e84902d0320400740c0c0e251000309a2003c46640078501c154000010301c1c60761401f206010f001001d80d85a80c88000f810b210701000740c103200c0148514040090074007501c400c04000c1012942d08401d4503180d040074107064600000c04540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 670887059 1250 670885809 670885823
    0x40608130210090f0603060b070803090c090a140c071113090501050a1a0a030c051e0306071808031c091509030809370f0503070b0114010810030803070507 68
    0x3890a281e401c00e0710f860035140c28a269640496903150b00b141500d041e80304a0b504030904103e13410108810500071640407084004495100309400040f403007071281119080b0140d030340c1d000c880d850002696440c68200c03903451030703070350500c400b07a142c031545c441c4080c4c041842504001010204212107070404c0704826005002042036140806c51040505009159120003443c83e4000344090310300008404152a081141d030600f15040009012006000301c00e9008a0901810064100c1d0b608022161007414550755420200104510510040c038070b82c0c100348815041446611500062035201c40800d044c4c0e2400402d0070f4829003000d0f04003103103418442801c0c03401c140c00d00041c540c03c44603050280034444120340a41e01080078580c1c4848801c500504500c181a03545030281a0a03030405141030f028003c18070001200d44d845c5465580008400c65100c06a030004002c05c083d40c200201e210030382824030100b98a002c0c000c80103d2000c03400300030030003100800840c20251040086c6e42a99070701040d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 670888309 1250 670887059 670887079
    0x603010510110102071a01051023040503010608010b0312070b070c030507051902010912020d080304140f060604140f0402011d060a050c01180b1302030111120a06080f030406081302 79
    0xd05005900c03c8005410300160100c6c000112409c00201d0400400c150759603114110026548905500300140101c818050040c40041035136a0300780b183c003004000e10400080d0b0700000c0c005150420740c0b40c0b81e107152180ca040c031049020407034070383c1c2156101c0e0a0703103050a0307507003220b180c29190350007541008ac0585c0b04058460401030f10b13401090300814000d0301c07102601d69480c813500400240381440250002118001240000c22510145410502c10041c01182c19030400400e4908200f40c03811f140243d0090741030001c40d040c00d102d0410700c6030855030b40f2900c0380b80032b0807124003084014200a041100c00d042c0e04a1444100341941500040100b92903035801d40984010103d40000000070029440c01c0c106614080c0138070109a0400d900001d603103002da803002681d03100e1021034201a03805548403407500d000340c0f0503000108491002048962001e0801801500c12101e00790085515075101d4000d5100f220030010689049510915000303034155a40e0f030510f000301c112500d0080d0440980e403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 670889559 1250 670888309 670888313
    0xe070c02030a0614040302100e15060a090507020303011d010b070311010f15080601292503050c060906061525080304120302042102061308010227060301051011010207 73
    0x201c200d17028034020740c200c0d118501d0030a103150807210035080d072800c41e510100d0b02c0c0d8810380d10307019841d40c8503070001c00e24008a070391503448400303a5008542840040c0c00c00001803152800003401420b124446005c500300a43c1400d2100c603003440f44072400340030300080c441e82e810fa900094201030950526070750280f0076801d040c820400394004c00d0180340c1d107a005010012800320030800e003207184c030381d401807040d100000008400400c030742c00680400c1181c0c0b024a090688001540600c6240c648207076280d80e0740d100c180e4200d034109500039004503d241c0100040c8107030f955800320f56041c4620352012050303848080031815140118804070303203034880b1243d203018401d025008010350300c101e001d10413801c25990544000c40880c89107006900c85480b030114001d980301c91440203618414401b400d254640302081c4041701d0081c0140d400345c100340e1b400150030350f11043c600700d0886403666030002040e8903402072000150580014007030640aa021038000d840180d103e020500c503001c4035100215138030207140c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 670890809 1250 670889559 670889591
    0x50109060c020d02030c07060c15020a0203040f0b0a0212090406030f050609150f0103061d03071b12150203040302030f0f030a060b04050d060c02100606090f0506040e070c02030a06 79
    0x12400700094000d50540100c1107001208035800040110090046941022026a04500600020380e43e00b005015400c01d05041840140196440e45e001992100c0c9840c006042d001c080390000308114805000c1e00e003e040d00000e42c0c0901c0f8021502242c1c840549201080c0180a0360b403020700806010601541448004180540a8a130002c1540c0c2c0503070310307003403814a0100c003a202d045140500c02c0040010668980c03014080c040c070103510f106401c41090311a46141c0103c0011343c8c07888030f03200301c0911066548031148014050f441e040a4001d10b6512440d55852139841164540b680010006040501c2031048030f2a00441c502619207900c030001c60901c0541080f1000e141061501901103100501c2c64140c6044403402485212455000e03034404002d01314880c0c5002c150310502c0381d000054403130303030207144094415607071000c11980c5012202c04890703026501035030040004010520190210403030440d0700a0180c10209040e81e50703880402e10348036400c0000f40c14540381c034042c16214800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 670892059 1250 670890809 670890821
    0xa09080c070914010801020a0818160305150702070812181005070c053a0b010605071b05060a080c0906030f04210912020a0906170d030b0a18020705010906 68
    0x50034000e000c3c16a203074030410b4201c0c440d050700c00001c42c44013000140741c121319581c020280003048065a85907804813000b200325650540040b103190f0014030050390f103408078208440e4010b00600c010101c1a1500b070b10283c492a40f801c14100789040003600c0c44140e0542030002200c514003400c82a0000741900c8002c1c030b42c0d006544110f8281020100000d21752074a4400d8113546201c0901c10302101c1c08820b002400340e1940c03000040b0101c100c4074040701142040004900800882d1035860351944207140ca03503180500d10007500107603128202c0512440d2501c1003a107501800900744915540c858042800c0180681e01c0500d40c000400002c100d120961519600d0003548a00e0400d419002000000500081703240010000201d1103a03040009940c0e05018621050002e080b41d0303101c40d04c0e81c03928401d03074006800c8410390800b2014000c100503030400c101c1a040109243c10070814049000040300c000d15803007105800d031a4a0024807003400c00c0d0b41203d2205074050001c2056000300e01d000d10103482 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 670893309 1250 670892059 670892081
    0x7140601050a0f060806060705010f1b0906080c040603022206120f1a0f040906020c03070201020606060c0607050a1b050105061003140406020a260910060e0a09080c0709 74
    0x910b01000007401d40703090802c002903443d26141c2a103140e40d03c0c1d0600c00540c00c010f6003502c0f10340d240c080542c0d8146092203440c80010007001f2045042c029800042d03c0c6c1d1115500020070080e40c01c2c100000e40220505035400da440c0c0d80307005a655088c0d15207502c094074000d510002d01003c8454006400c40c1c11907441752603803003200c03018461102011098000c0350316600300c1c4034903003020150714800e514040c1d00c00142203130000c000182c505019124074080380c01c003039041c6c08184d10006070350f4250340e0100100787e40642c040f52000e02e0441081c002a44803200134103418180500800c011445a009500445001c00c11b2071848034001b00908049000c0e050a0b20060f00641c400018081c0803880b81c050352054415640841400c0e44455543d03c000354801e1000d10300b0440d40081580112900c455080c0c064010402844140d08142690504118030030b080003550a140a80412200014994559025a0b090000200305d41030b03080101c030030f1042c02c06020031401803a00100f442601a401009400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 670894559 1250 670893309 670893319
    0x910050c010c110604121202220f08030f0c0109150f0501171b04091a0f01080606010c0605100b0f13050f030c0607081c05010302031b1f050714060105 66
    0x1103200c2915202041c0140f404150000d100180c0464011414041d0b942c040c1c0c170304410b00009100c0003a0481c0c20000d00041c10b40c0c101c07500d0720306042610f0b80040151035039035020a0000d180040281e5280301c4d81c00c0c035004005004c40c5d000d1503043c0c2940701c10b040e650094688400c0d0b15134694160010414401c0c0018a1460f180000c5600002801c440381d17508104001010340030074002d031403049198a0100c00d54400e8a441c0700d040058904241032205504803c25845035040051015002d800c050708800e8241e8440300400000da0f910560040180380c0100002a01307071218040c841410600343c000030030b0004002050007a40318000c0080080422080c5c0e071100d40c0307480c1e00810900101c03a600540e8180e000414000343c502d402c2c001050810310a1600350700e08072940b10a10b01c1040c00c1302041d00301682c1c82e801002507040501c1144081609256148444210180040e00400e40710091400410700394a52000300c40c0508111208c0755001101c040311814486156583da00d024040c43c3d01030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 670895809 1250 670894559 670894571
    0x1011010b1305040b15130f0e0a050721020f130b040c0e0a0f1d2502010f0605090f010e3607050d05250b2110030b010b0c030910050c01 59
    0x144001d00410307500001c0042c80084095200c000110180800200c00307c4050741d00c6921243e1442c2c20410a03000c1031085018100351403403c3c5405039104011a44120250b04040c00100103980311a1605680c02c412100e42c00c4400c82070210781c00900d841e161003a0060320700540d0542280c0c0051800001e80ca0841c2c0410b000c5441c0c2d9014a5068620b21407915007400d20310200d452030290a4490354060310a5171401081160690b24009945000800c440035035981c180454000a86001b200c0c0600001c2d0ba2030b04050400d01074025075003c1c140729030860015890089140040b0542c03107c0ca840003010040001e580046100051040e80c900520709248510348001650f07041040c00c40c1000d80e00000903005203106100340192019030b00540a0034000040404200e205c00140503103c0c50b00c400c0a051622082209489180c0c1005040c0c0140011904000c2000500e408145815200e0310546251203a04004a103461400f81c60661688452040d61161001d036210015010042801c4028844 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 670897059 1250 670895809 670895821
    0x31b08010302041b0c080924070506010e1501080702190804090c0c050d0c0206040504050c0c1b06070206091c21051207050c070b04080102091e1011010b1305040b 71
    0x100705000d8402c0020540740c41d05800410786c0b60380a420381071009000f29402c1503c4254a0b414540d84aa102c0d00c2100701092110500008220302405811303005182c203024140403401d2030203076404040c15410041d8140006030420b20a1004e10166001c80c1442d80000c0101e1500c1d8519401030b0007840c40c120320344040c181900d84100c80410740c03c0e40041c00343c0b0001c0da4052080710b9981c41e010703059030000300c00c010005141d200da10620f8858106484210f88981030144003e0825065210f01340c001600c030f20070030483c2d585a500b11132071550304a4070995900d880501240e441d00b103411641c0c0b0b400914144d608140700c9055120708a0340085001c0840c2c1c0251480250381c2c50203040c000c18003103c02c18000031405401403000f80030380100e800494106942e0350729850100d034896003003d0916500400d442e801e606000c01050a41030214068129590a02c0b010a00c01502003c02d071003002141c1e0210f01202a0a41c0541035103100642050005d0b4040b8080748040c000c01d8804860484c894400100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 670898309 1250 670897059 670897091
    0x311060406080115030e12040303020d08190f0e0d020f15091908070c030311161d1819021804031202090303090a030b0703050907180903031b0801030204 67
    0x159651911882c60903420014410b0140901c40344083c18117507105540950b1880400100140005200d107840c2c0c0c40d0304626000703087c13800c09800d400a111004090003020f0501c1c0c000484416a0b0240004d07200701c3e03208261014000809a02c83d1500517204500c40c0b01f40c2c00702d02c5080040c0740400300e6100c103840e00a015840a407c0b6031040c1a600003c1e4407105209842c1240100130b8080c1c4032050810120351102946503071103600403000b04501c509090242c0c0b81c1888004a0b500e9400f4549000614100aa503d800032958a41d0308450fa00c40c001035806002800030100c01c00100d044035000b00ca100d50080031000c0c0b00c181a84500980c03144074001c8000e401c141c6108591550b40c420030900c0d0f516804020f0b400c42c44056901d03000034001c800c41c5884a12024000310301495550103103013813111000d001c41d100a0000d4000b0f4101c000d091101d4044c0d80d0030901218a41500010418102d0400f1401000055501c40e400d12101c00300c008000d030300c03030003140c1039a000300d80402621401008400b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 670899559 1250 670898309 670898317
    0x20403030e150406080604141302040501090e030306121903020105061903120c1502070809100807090324020c06071107050307091a090103050609060108060106080a05070909020f04031106 82
    0x2200c2e04000500c140b81c4903030764042c0c20950190011540c403500c8d039162900c0b503000300c0d1031441c0c40540380788810562401d805807900500002404107c020103c140003a20b034800107000c24060300507401d500000b04010085403400489400b0341075401ca45914000b400f0340f1041d14298131030051440200914541181140c0c2260307440700c50010700c0c40300540c1c2074a0103444020259002c0180900c40103141c841d42c001003201034400c000c4540d60f82c0c01a402c0090128080c3d010f10f04100840301001491604080783c0b10940c1d822500d5032000c0c0035007500704603014003100c0810882038000704d1a45c0301c4040000e040e500071003c6031148100b9215140312541d076803c50307100c0d043e4594031408040140000640c42640c4460f00d6262200364031042c00e01181508600780e104646130350010082046100e81440428050904600a41002e5140040081c1681d00c06001c21141c240d840021540044c0141c6941005081140e402c2d904d0709101d00c002d9600d0740041c0700035038248049100c0e40381e407481c2c91002c0f5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 670900809 1250 670899559 670899589
    0xc1e141b012f030709090b210a1b0503120d0f090f032622020d050a020111030f0a0815191a040e0a0b0303130b1b030711060309011806020403030e 64
    0x440045440c00c41250f002d1f048440d40d01d601300d1198400ba089036200300c3c6c80305160048940060854080074a4813800600d008030280d0892a40400103000a58002c140c858400344e0603610705840b01500e0315034000a000d515402c1d44124a0704c9100010000c140a46c6000c660207925002c80d860b40c4808006c141f61100d03045c00c40d009500d480001c5080021162800030b5003618403641038400365690105000301811031056495520025900d01150b81c01008030300144000000366051a91040c5c0b041d041c1e0092101031401e201000c1c00240021001c01081c0a414000408100c0c1d10292651903e4140c1124001d094094070286098030744c1c1c0010304222000c650040e41c900380d05544000070f20000300802e40b032595050004104502d5101c0d021070682c0003600700740c1e84042e51642203940802c2084800c0400d200c1a0f0000c2c40b140300440d800140d03010180c841520380582d030b507403101805401004400d409080000700c40a0104c2403000e130b503004d0015680300e034944010510071303081000900039070380f50a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 670902059 1250 670900809 670900817
    0x2010206180703200907090308040312030e011e050a020a0c0b0424061d011214070f120b09010b0306070c0309050d060c1e141b012f0307 60
    0x4281ea110151022215841e400e0055800e0076840e540c501c42c4040240008614200e4181881c501a20b010311440d60042c2c400d0030034595503403442d03940310500d008500c005001c00801ca1b00d5849000c4c040e410802c960783c01800208508040468212032407441202c0e440d074414503000c001207503c171040c421100002c1c61500c800803090300c16501c0340c0c0760a1b00100206d54264040c040c4c1c41071040080d121100702114858041345182c1400c009403100004450404040f1581000401c05c40d281a400f41d800503411540e41c40c95100b00c10b80c503c0c9400702d50b52000d11303081c20300400040c90784180055542280c0c0300340c3e140c0010b034580c0084079003a18071514138282c0c1904000041401c0b1406445003da0f051b01c603013010095103a81d90f0004400f00e8010b0015261180c880c00441c0e0f415a20403403100c005140c0c1d00b070001c1c3c0d0100c0c4003402080301c20002c0b1074100700c6100040d440c040001040790f41000c0d803103407802840a80c109055140701aa04000c6a0590010000d2015655041141601d128105c1c1c0c2c1c0e0307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 670903309 1250 670902059 670902061
    0xf060902030a0501050a051e0d060203100611010c1407050a0b010f24020d050307021c120510060207140f0312130f030b040b071707030507171902070c090203041209050103020702010206 81
    0x104608d403c0d14408050303500007105480307240014402d00180d0300c036250540b90a24411316003900600b500f8150841207540340d2502c1f20701c040d0907800019800d032030490303c94055280c469500d0040c1c03401e0100d040150502e44a5400040d0442050441205172208003140d02c211541c2441c0c2c000d000c0448000030400f507000f0f5070030814403922440103141c1c4040309104641501b941c280088014500c1414942d00049040d441000703003c0250050070f80003001a181c03081c901c2d01d010002503d9540f14001c0c40c0403544101580c958654890b10506461140101a00e4002d16400740521283e403000d6210b2122034090f00001501183c2e600000e0116074100c1daa58000303a4030790340c4500300d00000404181c240316104141c0c5c0c03111410225407600c42c0d03401d5140055a4107007000c010700180d000e2414031100e200c600c01084203099411005903980242070074090b885124070701d0010481407140c5c2000002e03602c00310400c02809562048503040f01000e44510104c180c8900c011400e82c4114400070340980d01c800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 670904559 1250 670903309 670903339
    0x8010908090f01120f0906110304020d0b0601020f12070c050306070207030303020d020c01051509060a03020a330201020d050f151905130609050606070c03060f0f060902030a0501050a05 81
    0x2074182c0035030b41c014902400d1111a950030001201d0349480d00303e062641c0d0303000c01810040903200300001c2101001e549800c61901d07500040e40b00c044800c00800f4101800082005a4000c00c5865000c031001810303181e1000341112940d008be00000c0c0e0031755406034080c80015803401c002c501540a0720965014042090454a06038080c0d071040e000310f1a9941d0811042265100070701c50580588407006a50644078881c400b007203090030010705000e102d00c0d0b0020301040141d0780c81c010203049850f43c81c100d084c0b00d03581c0d5a440c81a1401e0008034040410402c500d05c070398680c1075000780005580305000b042143c0350140001a910030403030328170a1140c2061659016442e18020750001d4481c04901c0c21b001030340324004135141c030505500c0603081c541c03541030a001516641c0100e81d40604182c0d940360801d079036512050107404061101518043c2d90300c842c2ca4040c80302d034000d4640007520700800d101050351010500000d5004035222403516207044000b16992070b102d20302d01704170788004000f030100030418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 670905809 1250 670904559 670904569
    0x1205191e09032604051806010e060307020a0303090c0e012c0106090b161e05060109050906070c03020106050306180d08091002090109030b010902090108160903030806010e03070306060801060801090809 88
    0x240340400d043c414248070000c3d040c0c0d2503020790040d0840d0314070014150f0600703500240c40c42c04181205840b4010a1042103503071580020b03c5036a0503050300e8042480c01d100d0400c51200ca1994011107460038080001050690003000c01c140d9a5003072410003070b4500541402281c8800084c05082d002540c503c02c100211401c070f0010b042d0b00e90369030400001410141e03941c14080c550425100d4100c000301d00002c01440707010b01c00c460040c0b61445040c800e92400656036512000024040380c248154100e520303003418400d502250240401a04031809410a035180390040710035a55403d0030b5101d050b501d1680c5074401c614040c01124a40e004281010301c0a4981000e5000300e090780c4c0c100000c01c140080816442c00200380280341c3ea030001a07403071048100042180e40001e250220b140c2c0045031060351294401c08600845c0d4051420321865121140100c81c10081e46440c140c1c580300700314021051050561103107044450200081203216a034070401c5098172000304000d0040b081c24001c0b040c1500300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 670907059 1250 670905809 670905863
    0x300f090a17033601060911071e050d0c1103010c021c020f060112060506180103080d0906140a06061103031932060607020303071205191e0903 62
    0x80300078030455a210640318041c095040c0e007a1280740f1000d50700e180454075000c0c4200302c054240d52006002d244c080744455040e612448800078018800c080b91150255010f0140d54000c9a1107400e48898000c4904020702003590250142d80b4213842c0303031900c40e4030f14052103a000320100540103440c51079425841c0d1584401e04142d01c03002c2d402a201651208070040c080c00380680b008284000d6032903598242603003103400c0105180c1c0a0083c240040d0544040490a5811a50f200c0d51007551403a29080c07803005410f082c00002c111a09200301440b0040c4010656841941100c108004c11982e40c00200c1d140903220740290000d03002003020134061200c00c01da00711040c041c280082030084134064a401d0300b960a000014011024180e0b110a25a41102294016108846507070400c03060b80c0009440f40708101c8001d1072540c80304400090140104150f0b2102e107000c1e91601003510707000401500381100000c07021840c41180303640a410b0381c0111114010b50380c0106c50301c0c440411101d00d00001101d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 670908309 1250 670907059 670907071
    0x1218120303111b06090706020d0c060b0406150314060103020a050a23040b041a0405130905010b0a080307031205100608091c030209190305060a02300f090a1703 70
    0xe00f00306140711283c4081c0924004160400101503518003103035810b003040c0da45e420030702c21034200c68565420540d01000d90545550044000601d41c499580042c0042c0ba10f40e114490b2600c42a0840300006d40550000c405804094401a02a999080110102e210748805c1c0000300e130040c08000c40e181d104266083e880542040601c0024003544907403642504590300c18021160002028071600040e2003a68000000000b03100d820942441d00049454241902c1440c45e65900c003500410301c0707000d401012610002a000201242c2c450a08035120752200718281d005c52090b909880d2404154801c8600c41e41d0343d02c0580326500e0602a00700c845003408fe000032214810062403415a08406014140c07520706030310300681d181186c009200741d0700010a425440740d09020303010808501c02142d0700390702c11904d1500581d1504940804408004500610440382c0c5c414a07490200c0600c00403480e00980e100441c501a40e82c405031025640d100c01500105010000c2c00740013001c40d058805542c02c10307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 670909559 1250 670908309 670908341
    0x1050106080c1309060312090806010503120f0904050103080a020f061302040908270f101e0309080f250f020f0d02030f0a0b0108070803041a090d1218120303 69
    0x6581c1c40f034a9045c0c90f8290001d85401401000076400b103034112840783c00802c04c4c803000e42415071410000945800c10141c00400544000483c884851443c40440f4481034000301300301700558503414003103600d4000f0403c0d8000f51180107180c0350591b60001da10f0344555030711131f0301880f02819a428040500301d459001c840c2580d06201038204800310f40c01010000c01d600d8031728041490744500b040311042c400002d45014010454008030000e0340854855554501400400c12001c0551000c50007004010f80280c4901c10104001a45d1848080100f50918104078001384a016409091110b01300e091001003208074000d1002c03005041c094001c82c45007200070300860315a0029008282040d0802c49100b044d80c01c500b026000b0000c00c021441d0140c61a4001000d1460074416100e45d648510f00860424100010b00401242c41c02c00440351500005000d0034900304a510701112140060802240451860450039690901c00c1c4118400c07215040719013009003006032826401007a003000010790031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 670910809 1250 670909559 670909597
    0xa02070302031b030d0504030b070e0a05130e0d02240c120406050405100e070302090910020f04080d0e0a09020714031306030e0703020a030803131a1801050106080c 72
    0x5a40e00303003c81001c4040740c6607100301003080c00c000c040c28990194030000c10f00c10240000d00208403038000c0aa0b2010395420407080307684400c00060654600d59010340c2e40100040c2800c41c40c0c0d022900012411058a822516401003122048ea214190841180ca843c034000003444503101c209002e082d0001c000c1e100e041c1c5421402c0d4480581e1110448043d036030640c484081c002000410050310050030010942041401e00d00100e240d1902010302c0081c0c03040c1c114201080703032824103100b1420115903440303045517590b030710600d0400c0740e400138452111140100e00c540c00b06203000301800d07107408500800101c001c40c10041c0300f000030b4008160544006001c14402180ea0b401000140341d1503039000200b01d0402d140000c02070076a0449800399120f90411902000161100c009031019030394045900c0e5240e50b42c4800e204254802824003604000803010314445107500b1081c1c0d5030003458824601407500082c001d010307003070319020710420300042c141c0800100c1e0614400c02030030a0100417603200b208 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 670912059 1250 670910809 670910813
    0x3120204150323010e190e0615100206070f0815031f0b0103020705070e0601050f03070c020a170606010f0203070602030f10121703040c05040c120c0207120204020a020703 75
    0x14190241c245100420303910800c4040d070168200c0307040c0c050140c01600401540c100070b9500e250b04006030044503140001401e00581c40700f10b81050500071040320031034801e407401c2c1110381c040000141815000f000030184030645540b001c541c0e21301c03900312602c3d50244000e4280c0211201c0c03100900300302248030004c51500e150783c1d085c800d001d1001981500d510014030785107441e000300c0304203803d100d06040c070402100c400910046800000c481079001c120b031041e5181c800580340e51041c813032404d024000000820a010f80c01121941d0050300130b8610801d810b03101e141c01d03900c11b00c40707060000081c3d00c0704000603520b42c81040c8109203000f180c4140c0f818480035a40d54816a041a560810400341e010108030a0201d4411007500604900000541813509620f0340488098074840d2038454140c0000003d0a10940000b00402860003030310800c80300120b42c0006145180785884c07101c61a003003811107001584001003600a8403440503d48000f15401d0742084003e6000c20213400950140041c0000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 670913309 1250 670912059 670912079
    0x60a050324090307020d0204230a020409060e091c120c080a0e070e0a0b0402120405012c0d0c050703060501180605031c0e221a0409080703120204 64
    0x1907620186030000c007100041c04080006031030000d203035140c541e00611401002d6560303640c055029540503140001d000014214800e81440c0c1c0030400c5601c41d69003001d20442408980c0144111121028100040c42e240d12410f00500790548252490740d0016103241044040421114807215003814a954050040f14491040d205d50092600c0850304500c10070843e12568040e035a2140d200c000070b011120f080c03140016000001400c0c1e105040e41d0b0b18903100c4180c545604440d00c07c0b007040c3c4948058a1b041c030f0618040c0c00e2000300040080e215034000700e01d0030710a107450200360010001401010b0200d000c1101c1242540c501503403107101e248000804119944200c03030292503400d104140260004189000351042584040d019138030045035150b80182102400358101d01a29286c600b0281030000118050310308036052014030352000417110400c1d8298000c5c0d40503d00728a01d00c1840c148030b000c000071500001e4003c0d140c02c00810404002038130900004803401e96148005040c5504c0d02c000300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 670914559 1250 670913309 670913323
    0x20a090306051503010c02010e0111040305151320130623150c0d1b0309150507051c090807030507151e08060406171209040f020f030f071115060a0503 66
    0x40949d55442020324078000a01a4174108600b14990030f150514613a42d080c2c0c1d403800102076040b44540135000c500d440d90862011031684e508089006640c10400c601c0c2d00c889004110214412500f0710500c28074402d00c2d0041d081281d401e03000032405408038500c0180c0c0d10300d49600e8981e01156500e428042c1ca074070369021341003900ca002c2c0103000c0d1803003180d4007625480300d506961098104441d05200020361180121080d684240c02901c0200741c8080191550b006002c0020401e0040d000b15214903100808080581d420035070f00c202c80c095a9018050f183c0f4268000900030b07801c003090a20a0002ca02c402c44142440c6141c0780d040d200c49400c08011001f007020801d40001c3c09007040c01104d00d0680510000b41c20414050050301d4801c030281959010b49003618028000082548030b003540e036503444514003c500031030940d038800e006034000055900840344c0d4081c2003c500045005913201e00c00401d274a4400c50014940e14078142c2a60320380260040000350302c00401d03131020813141c906000ca0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 670915809 1250 670914559 670914581
    0x50601020331060219020d1a0702160b09060313030c020603010914070f081302040f02120a0e0f0a030e0319150b0f01230d050103050a03030f020a09030605150301 71
    0x3210103a90308110074682d03021507900c45411540f10b9160303c050072a0340d0340f605c5c00d1964100d8000035040740ca03107020440400b60700300c1b02800301001c0f070800855036004620f00c000000c4010b00d40340b280340c0b1a9101601801a626502d403c410f080c40068050070918005c00c9801d0301a0401e00d944030340a60000f142584240c01803103006840302a40d9000c00c0400d0021390300180a41481111507081d02030040070810001c01c864004000c0c0c203071000135520340e84c4c000c820b40c500c0d101003036644e001d10700011806203c00340c85680341c541c50900b025291a1b40481c050121480300f8000d00b02200050314100c410903502c8004941c14026040f02d0100004000600401c141c810a8810700c01c42c0c0252204048820300c01445024045210394400300e03a9116200940380828a80c40314030416000744041d200380990241400300510345070000c0140b010000d02040258441d503800d00011420300c603038400340e001d25000000420703038244c2c0038400a03a643c4c2140303600c41020440034080d20034107400642529580c0e061 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 670917059 1250 670915809 670915867
    0xa1407150203191d01050d0f0f0b01120207031707111009150b0102060a0903020a0605071e05190e0102031327050c07110315101503050405100506010203 67
    0x1c0240040303200303c8059004502410701c100c04940d001224141c1e4014558031504106002608042d540000e2340a009080e003042020003030400702800031402021404550b40c0810260f50410050303104500864100c5549507661100200300110118071035000503003140280001c6000c07641d6185810014110344100000c2e01141d500038505006642045e04000c00c070782c1e1400c001c89034650382d800007005904022a0074000075654542d05040381005d01c0342e4401020f003810141841480e5500026040c4000600c1c904402c0d0a28001400e48a034454038101c00e101402e40e54200d0f06503402104c1e41d0000e0070060040c1c074500b0600b024180070507240c0350030402114075485c504503402e40082380d101f0344400c0040c00030005802c1c03140c0e070007440f401071100051110b8106c2d0802e042c9034500744202c8014200b031100c00301e072a09000d101c0c10703039450242c0201c42c0710998415002d8a003501c2402150300a40e00311024180e031003400d800312809860300401450644c4410000c1010545041c03910b98014900106 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 670918309 1250 670917059 670917067
    0x2010f14070c051f0915111204060e01080108190c150c03020d020304050105070204020705030405272d0a0204181506080103020901090203101203111507020a1407150203 74
    0xb00440061620040382c000e041301d003884000c054128920f0015107072920b616050710b040716881105c0441303105404408038080e001030301105d054000054016680d01d6150049a10605001180c0d601d2091280c084203030720018404102c044145810b00d40113006d140d03041030881c2c5452803600030740140d17102e00b00011108000320040c590705202990244403a8806145031a103000b0000b09507019940340684507943c00190a4104042041114010301001e00065904070310702c80c001c171035918540c00c500807022860000034080c0048142c40d08080c01c019044500400200000b004030b088010241e04e010f990812010864a0007200e0700c8141d010b00b10000b2840180c1c1601c05890240d2540c024001d011203c801072006039103080100d8113507102210016102d503564140030480342a107070721027074a00b468030001c1d400b41640b2140c012110800700088465041107030480c00d00c2c14404484070030042e0400e6030031400007229800e00400341001c0314110790309580c03103800402d01550901f88010169200207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 670919559 1250 670918309 670918319
    0x303020c0c21071e061b0b0f01031407050607140114010f1802040b040b070c0506040603051501020c03100f11042402121222050607020c03060603070302010f14070c 72
    0x100b0303d400b0b440307035900b080c4190610201100012840707001d114140301d6682e1080b60b51007030703d24402c1c081d0360300b0108504003410102c00d08040784400f800207580714200c43c0b500030540d41d00004d00000f00c0da0003502040c500013894460f6018201c0b1900d40c1a070319500d0300d0702c4498100902e0360850280011030751402925180c14501c07851149850710518003180140300400c003243c4503409413000c54088c800d6850307a80b2841c2c5004034000035207411499011202003000f0a07040d07416403090b4403800342071500c141c0c03030707045140103990780c0a04203103542e030580c001408004203094a4000e0100500c000030041040903c44941c5602900603800420452414040c8681d101030b40000f5040740c071020703001600c18001c580c24842510b1244090307140340204950302045d1030704442c1c02800040c00100c802100e0075081443c040307403101000d6464200600c2001d4002000346000300701503028202c018000c2000d00e00d141d00640300c40742001d5089050000381c45c8a0010460020000d2032000d00c80d48030b6aa02034104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 670920809 1250 670919559 670919563
    0x171e07050316090503060f19050115111c11010608070b030402030106120812040812070903020f1017151c05011a03062406040306020409140408070303020c0c21 70
    0x140140c2d000c1040c1e01a040180c1d0700c0104e1001e402684046201d08159101020005205102c1071503400e810b01d840c0c000102c0c03003c084543c140c4550981e840d449070f04031420324a50340c1c04800d10500c08886014400d01c1d2182e00410718614101c1c0c4100020401580d2802050700b000b0369a408100c1160001040004518082c864071000d000c400e25191480a040e0b20340380d02c0c1d8011a20f459500803900d10100b07003071046080a0300c1388521101c00380d4a981c90b01c107130300403c04415840220300a00c0780100c486803529210500310030b5080183e075000c5010110f00300c034840d1803901500140b1018001543ca444d01e85801961901509218016070b003000c00340e00c2c01c0c5084610914045204218071403501010380d4000c241e017a00200144101040c1c103290884040001c0f01c240c41059208000040000c0cc00801d0f801a00440303542e907404004020303110b82d4014441004030703001006624204a1000040e000781d015160143c0050125a440d2400001051400b40b06108505002e004051145540c100c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 670922059 1250 670920809 670920841
    0x507170102030a0b100801120516030f020909280c0503010221010501031a040c020c032a091605071505010308030f06100e01030e12040303110601090903171e070503 72
    0x81d141c50f00407105e500002029080b060040042a01d108505002408401c0201c41c02515100000c0c004c016540d1030201061001b200c0101d02842c0720310006040708101003501c4003022442c03107d01100d103035140b00068900d015800111846804001c000c1b80c0c0e0745003440541815109121111034056040c4020780c0301460580c00941010700346085088042100380244120704410b0300d01044042800000340d0915980542031905481400011178107042c0301c0b01031803606c0100b100d86242425100702031007500c0c2c0d012105100f4401c8401d0b041c0da18144210001c02c201070040b00344003107215004e4251400d582c000e07842518150000b00c2488003030022440b54a07000503048403100448030300c000c4003403e281c0d96415018103145d511120904525001d100c1940040d0410007059981c075100d00e4050107100c803448041c40702d40310341000406d0058140c0b00d039201850b015114400319600d5101251714a2100400c00c1c91000e102405628040001d00461401150143c9600e40c61b450800e04249146030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 670923309 1250 670922059 670922081
    0xc01062d03021516140d09060c0b1f0b130e0105010804020d0611120a0903030c170c090a12030c050c060f0d1d15070e011d0405040507170102030a 64
    0x21061080005030782d914844002c0d21802e52103e620741c0400d402d500c1050a014030007a14035216000111080c51000c207850000c902c085d20f507a20901d072a41b008969003c5411402012205000d02141d60b007040d0311111001064014100100552101d4402c1e446400031812601c2c42100c24200740001030240d0003d80c00b405c028a041c00c018078080c0c001510900c900040075120031b5985d881700c1c085c03840c40002c80e400070b100c14800564034104050241d0040000d41d40580c0000d24202c20402d005102e4030f2080d5055a020f50030a00c2c3d82c90301e5040781c5941c1d00c030b584c0d5079501c004000c400103010b420001102200c0d9009480d0004038402604103d420045248801c5100e02401c01180c03a2840159040d10061207102c00009409403510107044d02c00954184880e6462281c07942c040301100840280c00d00c240c4403540c5206486003e0700040d14482901010b0790043c24600e0740c03480003810907502c5254014020021904500d550b07a6038814012404252074400740d4000040200715480741c01961420790b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 670924559 1250 670923309 670923389
    0x303130b0702032a0d0204150b0c010501090204180513120201020c12090618030c0603130510140105040507140d1a100816030b1008150301050402030c060a0201020c0106 74
    0x20003803500031482031142c0680605c14602030003d0800d54455030711042c80036a0076000d00c1c01d415129400c40700181c00c0450070b80480e40c200000490030712024000c3c1d50845404000112120207907103040000381c940104500505020115100007107442c00e010440d1820070f5800042c2d80b4485a00d200d801e006040328013111200342000040b5064548004490740c10b2440c01c909040242c000001904209050404941c03120011042c4403000140c40c80d0a0041445101110101500341242a01307881100d00510350308201100104400d05190304072310380c08503c1d45814803625880b4958200d50303810600c03031905050359034180c110300004005a00c08050b002180e030b081142c0c0c11400300520750300e001030001c0e002e41c84914a2403011030017900b1044c21b042004040015040311040001d003000307401c032443c0300580e44140cac42c0d45a81c01d040c8a46030260741c000e400782000582a505020b0301d54090b6081c002150750030441020407981c01e10030b110241992011610340d400b44151a1100c2d00f120781d4000d680c02d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 670925809 1250 670924559 670924603
    0x80708060609040c030b040c020304061812080c10090c050f0904080415050706110d140f07050c0c130e0c09090619090f05012004030b0408090303130b070203 69
    0x350303115025103a050300203e0300890702166000381240030b0401d40905540003801c004d0452145130300072000d0400d079945581c3c0c40f141a10b0071180d0030341034040707881102121650b0006070004241c4101c01000d10b001980d00312651400004090f0341110820a0191007a4040100c00d01441c0341140e055180002c003103403240c2d120306141d21807400c07601c500d11440101c000341d00b040708c5074903000c0c02c207550b0130350340005080000c8440c40b603850340036601000305a13410524000722246032540b1020941d0190280340450802c95a03643e000342c0d14cc0e4414580040b843c8541c0ca035001c8983e50f40043c40c01e024001e4000494090140c80b001c914091511080b40c2c440e0240c0400c002e0b06580005855a001c980104080308036008002c1140c01882d8544d00900704a59090908080c0700303054003c840c1c10103003920782222114542e558001107000c3c40c0001048011030801140208600d0000b40003140002016a498020120328002c1b01100a50021402400120300c4009500d0240003030614a082d56480c4069 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 670927059 1250 670925809 670925821
    0xe07120603020d20040908031807080303011e06050304080a180b0c01140a140a11191e092d051903030e0604060f050a0215131502070302150915040b0601080708 70
    0x107400010f0488142648181c409c1009090030032a140051441d80140c96681d6112401888000000844401c254144400001d02284118200ea200d41d0700285014240401c14030101e5405002000200706141b06040102d54a01c2035002014154025400043d8001f013088100104410081c244c0540501d404802c900c508920034403660701c11104140010300b41492341e075150300d074090301e604074800e4080801884d4001e900704620500750713110b0401031040103264034821616140d060240a940340100d00c03c40034855414203101810408106001f241d2075100e101041001c8104000200f904442d45010414960443c02d103600380f60098034071500d840c0c103140c4050305024164a501041000008039810318030700c2070005840380c40901d092071580c0d05200140040c61417480300e082d900080100001070100700e0a100320b60903076600d90098000895545407800c090007004102c00c10a0040d19100c00f88141c10a490710301c99845071b600c0c400e040c20322100050442c90010107160034044410f05001e5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 670928309 1250 670927059 670927073
    0x30b1e0d0210030f02030c0901180b1b0c281d06010e031603110a0605040e180f0706170a0b030703080a030b03060c0903010c090e07120603020d200409 66
    0x4041601a516410030b000da00008030010503030401c2186001e8400303c00c0c46000c04907000140041d0000340e845c0c04001258a2200301c1c0a02c0318821b05113001710401c15403030441c4400c81c0318040c80c0d4600c020b603040ca02c10007003c00c22640345590300c1140000c1808818858078100101a005800526202d0f00d0980c40c54a0410440c0b80250400e41804000815901942da08204407456200b400e0700340382d5a01c5d80d0345804240da16003100d24cc0c0c032522040300f01140b402c1c410b00a5034226140c3e50214461a16482c0e801c80c00011841e0038076040b1f02603104030103c0e52408100d0380d0010b020660b40d82d86000e201c0911011000c9001c1c1800f14000e0a00d00009915640010500192030f00301160b190758035070401e0294010306110f6400e0b605401140c0c2000907982410f405040c000100b40e0003404100e2001c7d0046031100410b001c0c1204404900740840d80d00d0380b0500009034600f1881c0310004110307850340c0000d0700144c080c2c2001c43e1010000a910b0754039180740e0b04454030000f02a40d00380044042030b0764401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 670929559 1250 670928309 670928329
    0xb011d0d15060e0f090d121118040e03090604150203120403050306010306050f0d030e040b040f020304020f0612160507151b0f0c0204090c0306050903030403080907050f1915030b1e 79
    0x2c08200613a04002510384803540050023041c24415140c0e40e60202c480d61420b42d820900702e01e44924908140503505003404030031031b440d0900003002c1e40c0c600350402143c400c44201c03021000c0218407051015032110124008024066030003031704c0c2d10b910303881c20400040544445400c41e030702685034003030800304540b12001902a190f5150800d06002e4581030302040c0145182442c1c140d005050400c00320200050754001e41c0214000d03207002e0ba000c3c0d480d009200d0248551034401c00c603082c10310b0003e8a54a5141c0340300c2ca80c0585032410301d2802c00291039000e0404040740500120b103076120111a03103628600c0c05804000c100e41440744c41c9141c4403002400c0000c207008041d0207652104012810800c000b5030860140d5804102040107082010f20795959803c21241180441ca2010100300e0001c40015440121075004001d1200300c4081000e211110300302c002c43ca4000006c0a00c00300311804d00318540c5d084001c840c1e900040300e088030030810030300030b400b640c000c190807079206184651522040ca0030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 670930809 1250 670929559 670929583
    0x80c12040f0e090f071205010f0501050f130e0106030b0f090f0714031606032405090a0b04090f0b0702010c140702060a0215190605040b011d0d15060e0f09 68
    0xb03442950b1000040c504041e152248094140100741c40801c0c0c00c03402040007890b441c043c400800001e41100e1340c0344110781c0203019280d804400760115074500c3c60500e210844812005001046406140d04143c0c01e5480580084850890542c00c00141481038004158841804402405c8428218440544800d01805011340e00401d00000c0495501c04102c00035000790314100b0b514542d40c3da60f0006000341081c2c2c0032b0101103006038015101b0325903040030b18010782d40c4c01460f01c25240c54000428005050f480f41a84c0c1054171603031901d011409250242c04414002c00c0d91580614008c0002070850300300c08c080c0000d01c0711050f10500880744440513110b002d40e0544040765500700c2000107a161101d0610320031a084030060400c00320b9001d46031007525108041c04184000b82d2900c0400c400d58042c91300c564000390390980c030150382d401c00c0d141824080c10050b042940b0780d2030945035000f07507444044881c204036440b0401006442004006964401080b01007200b03541001904d1903100c281001030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 670932059 1250 670930809 670930829
    0x2070914041401021c0509150a0c020706020d0906030b0d080d0c18060e0603040c0312051809010302030a061a0301111c180f03140d0b01020c0a12021302070b04080c12040f 75
    0xda40301a003000f01c088d00000c01071640300705191113170000c40541401540a8014043d2500c0050b18500016042d00319480707035122610183d0030410210001c0030b003078140c268031624100480c0007040420b0010702c07081c1d80501c0080340c1207100d81d001414030b5921508140c4403c03146801000090343c8042078000c003000c00c50b00c00390b5a03211410190086030058102900307032244207011402c3c20350844010415102074015080900344d4260030042c480c0402d110294040d007011112000148180d40310345403181549004410100085020908681d074001288880030740006106100314180200020010100034007800007a801140f58081440f00480081018036082091010035001b8180071111401c140c2030b0a1b180d654041764403020340b484070350382805402002ba1040942c00c10b20100e0702900d070b4508501045407200d41c2130141c86040204050748180e42446034000040da4549018020340c010400300b0f440d88038603038019080c50010355081140c144c003040200109000c00d41c900e0203d03000c10700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 670933309 1250 670932059 670932061
    0xf050115151b0503130305100c0504120303061e031502070c060f0306091103010e090c01230906040f0e0a1a010e1908010e0d02010203010f0308070302070914041401021c05 75
    0x30060b40c0b5641c190074018000e00002c10000c900220200740a000c80340250111451080815594000c42c0c140010503400120204000d120b181d4030403141c22500d520038907002644c25030382c400e201000003c0d038241001e201c0c1c11600400070b00041000102d804c60ba202c1e421031600b0b440e5500c0c0d0f040d40b10248030780e0040c04440c6a001e04800e0007580400c000b050161030a2010700c03800024a01d199009000d0310b423141c1eaa50020401207480003170303043d102c0b0704c040e16070385110b0012159844183c00c0d10000e05080220070000a19541c5409002e170000f00240b0032044291400c180308281c003014014030790401a45045200301e20b05070414580b500c201e000703003803840300202100041100030714072008400c4000300d500d80015149405521604c04600e0400c143c0c4c141d00e9906008038240c0c4020300c120305503048c1005043c0080b5134a24001d01c011840ba0040316a11a91344d003040c81910240c00b44e400d10402d4600400081c4802181010b144000c030a00842c50100300010120044a6100c2c4a507d841e0f80d60f4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 670934559 1250 670933309 670933337
    0xb0a050d17040e0a021e0a020c061308030c0304030302070e0c090f120303090a0308060a05030606330d06060819092f041a0916020a0f0f05011515 64
    0x422a00540307039000740c1d0283c502d40522030740061b501840c407007030722001c0d80128048218101000d076400007405a0180c07003400c24041c20040607802c007031020407002c006d200c070000320007800304001c0801020a002071500e407451400e02904010540c0d121a5510038081c04102007642210220340c40d44104848102c0c3c11100c0d0004654454000c00c1080070b1403200005019415400003001040c1621030399031406150348038414800b1a004610505805a0180010407081d14003008981780140c2c0d4581c03032502c1a0600d150606540250761142c183c041000640d400c012021802040c01808842c201090a4284101101204400c9040c1510210390310b1011004000300300c1d03402c502801705404140040216459130800d414070200e2400d10403407a04081104c10349222110b200c4840004054200070340e42d4510200b1081484002641140507900c480b400040e10360b004405014010300501c0c600013070a01d001821642111071003801d58807010800c005003204079104101070001d61a20603c1c9900d20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 670935809 1250 670934559 670934603
    0x6020f191a0c090429121011070b072c061b0709050c0c0f010605060f070606031203050919080a05070c05040906050f0106050a0e0f0d0b190b0a050d 65
    0x3942201d80d1007405c0000c072810030440c0b205264017440d548030030310503541484070070440c2d1041080c50714001e9400000020003142c443c0c0e031001d140d0020303c40306949060340a035140103800d40111041808900074101d084180100c401c00c0146008a44c00c0e0384482d41400000200f141c050b100e580b0703403400d0060900040032001070000c2001000180c0c414069030400a00340c011a41103038032103c505100d040c001c000b03c46414000d950171110007501452030301c0c08140e407081103540031180c1502c0c01616a8000400150740c40040841d2070740a50f800121401c040784030500f400500040350102528003c01407020070000b1003201e00908007410410340e15192854200304c900340507030100e44e1003494030b48075005011442d00998801c4071a8280e1680300c0c0e88840d001e403035a00607030a41400184e100e2060620f80c0c2800b040490250384000c0020307a0076030140d600c03e02d1041d03044408040004a0301d40c0915007044500030070000f5001240d41702c9503581400c1c08a0b03072024240340d020703195110b03220201c0040312038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 670937059 1250 670935809 670935817
    0xd05010e010e0f1506060a0c1b090b0108091f0f0e010f02040302150f0d0207030519030b0a150c1101050702120c0324070804150606020f191a0c 63
    0x286030300a102e101c000160464554044a901c08407034040c401102c4d00b03260200d459680703d0b80c0b004100c28200100100304840c080745680c011100140c0c3d4096120156090710f4814006100c400d9000ca040e07190900010311310a07000d480188a030307001c060780e07104082459545031010b03c201c002c0001c005a0700124140a410008410420365203007e000c80c10902940d0010000c0d28020f66802100c1d40321015001940e10402a64840b04c81c01405603d0310681c0e16001010020702a00d0940e0030000001d0780f54412121041000b00869600d21034100c1303909210f80d92000070b0044258240d0501a0001c0140940c40304000082008141ca481003000c0e07800f0344180c0384000c1e00509003c2c0302040460013196219011001240700b44522440c040803200080304c0c08582481c4901c400d4490f4070760600595442e0310240084034403203912ba00070703407443d4010712920000b070115a0041c10754421207001c65081c5207560401071110340343c0300381c0c070004110403028404507800030400c0002c0d150b4429040380c0302801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 670938309 1250 670937059 670937081
    0x5091002010b0d050c1203120406020a12051504110405131d07030503070c09090807020420180a0e0403021903230309010e010c0f0c0f1704060813110d0501 68
    0x11140c88190f0074080e0006440344046000d0340c811210403d160b1501d40c2d01c1c021210030030b074812682800680001d031240c010303086524042c20040b003040007440c0c00106542003113502c00103090180f801542145800d010304400328051a175054941030810001c41c0303001d040c0c100d0800c48282c0315102c841208108801c06a111100c0e801614106a283d1400c00e8aa5124910a40d042ca03103541e0081686185446510926507000c124186000141e40c03c1c00003501182d100d12408810a07002021003404000041c610840700f5240c2d02c510400c0c074020459000030603001803540d22100c0c403c000009400050066812031544101c1245241c03610301195440540c0b86204042d03400d8540e15690f54140801640c06080f05100900c040a604000140ac07504024031100000701500769201c15203024901f103d0741d09000e9040c00703000c00e00b075440e1100c0f0501e0300446032107070b0031000030104103d0380c1c0320010030f81004035694032441094450701c1e4060a078041003110351040e50083c6a00d01080025440054a48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 670939559 1250 670938309 670938319
    0x2301120c0803181315030b0c091e0316050d0803040206190203040608091c08070c050304080a0c120f02040b010e090702060f13030210050601020a02030708070f0f030305091002010b 79
    0x43c0d0b41031400980125032811a01a05441c4254a030f048058080c02c00c0c041e00084245103442c1c95500e462607401406440045552001c00961040c1e44404849480d02011060120b82c00e00c3e40030149031410003000c8080c1e00200a031402488bc698a1070710203460f0b2a080f044a40c2c07292910300000ea52481401c2c480b100041d02000c12052864021014000b107070901e4490340c0300390340c074102696254480840c0e110140c0c84000640020741c1d001d83c8000d5004100c51600808100103560740c04d166510503080800690301000c148801c000c1d8a000750360140108490310743c0e4500003559081c51110740782d00024400d030f8917401450196407042c4d040030b44007200200740f91954201200d01035100c00b03090396950752000080c4000390300403841c100c82580c215419402019401ca03807440782002020b018018a04500501e0076010160781c1c10407241d4050314249005d04040c0f40703401081c40400703000303a03c4082c0c0444120710401c0880c0e04103007642d41c00301050700c200300d68040a41c0c0c22401041c031580403035844 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 670940809 1250 670939559 670939567
    0x215041503050a0f06080a02041d03070c080c04060b12070c0b011203080105040c050a030b0307050a231f0c0c0512030a02060606040f050d1502030a0902042301120c0803 74
    0x81070741038020b10700940c548041004020310703081156042e104a80250800780e4098940b000050505500400d202440c00100309a00700e4000c000c142568010b40043c0c2d502c20781c400c400c0c00f0f0500e00b40101d1100c18000c503800c0003200d141c03290116450280006035460f411803c40080c10300c0d40282c640b25010340d0f2064815500d582c40d072020310103040c0c0000e4164005824a0004641400c091040800d180d080303403555401c00006500403400b9082c0403c0994241c01003902c0014191561900c0101412001501301c0030801c0b140f1040603000c009044e510b10945420791400d000a910000c9442c000003549004120780c1c141e03080070b040107001540f2560700501100c82c0c60814440c0803001e0100403480b0342c00c0d1030041e11840300f0482240114051071000c02c41990081003035140c60070303c11070803500c24180c2e001d04020b8551440104e0300100c0e84c801409032244a00c1c0210b1910344107070890645a041207800000491907108134170b070b80500500800d1580e900b552003c0c8480d50391010020070f42c4008907599 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 670942059 1250 670940809 670940849
    0xc120907260c0f030d201e10140c13090207110117060d06050a1b02030901032f03090a0f0b040309061707030209010909020c070504050903160615050316170118021504 73
    0x2698400a042072464040c1c01c205200e1903003180100e0803000315501d9409a980c503511102e801503446401c607038bc2da4804e650740004444030303580043d240003030084118080b8400c50303100140c5600c103100350105088a0800400810384da032503c400503040c2e04203c1c006026961502c0c41c03001080c0822141c0103000400c000c1c00c0c4403581c000014140b180c001e0b602400010003040054030038040c40705d003030200e00b19408180c800308210305018540c0701c0071140455190032520303259003040c0300c060101036903018550701c00c1000345900180e80c0d000416441c0b408030041128503072010100b00004e054a0205600007c41021983c443c521001c080c218900d400c41d0749449141109a03104200d105007805103003800002800440003106403941d040500c01d004900c880360355945030003412180e001508000704903801007a80d460810112905142e42294a000319080004007000c401e840c58240346141e0504690041048403114010006075051741c010b203081c3c0c0b0540049219020740c7e0000e1011010303214032000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 670943309 1250 670942059 670942093
    0x30203070c02032a0d020d0f0302190c290a0c0507050a08030903060c0a14030c1b060a270b090a080a090f05090c120907260c0f030d20 59
    0x801c1c4e00c0c1071420f1904218000e040c0001c180d066507000e980501003e00d180301050355091981581c0e40b0910503a902080042042d920b602d0560405a0301104075520504c00c040d604003455000c090b01c4003c803030351103051243c2100a03108d0460704c0b40800c034500041c0300401400700110405004010070201070b094807042c845547c4d0300314044144c420711401d00810b109521341d504890120f0501c2e5104901104000103007044c030360020b0010f00304008100070700b910081c0681706400c2060803d030b02418450801c44c012405481500c00c5201b1010a24100300c20444002c2042c1c0c150558803540c1030156030303508600c1e142007144108000d00054800141c092900c2e9120618a00344c6240c205802c10040d1a0800c1c42403003002103030045105001000404081d010744000140d00400324012191042d40b11103140c10034002e0304070b4080301e025044040c0b840c1c00c4030620001c5112802039440b0344800c00081c00190340c4980050007a001d0120128000100c2107210100f02010142e0804551100e468008140703 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 670944559 1250 670943309 670943353
    0x4210320160b0a0503010e0c090d0f200a060e0612040606050909060906010e0604090c0f060e0d0206090d0201230a030e0615040c0306081608010b0303030f07030203070c0203 76
    0x1d001c214100225010201c070064968148007582c940b400d5a00b800a14000060094a0310303140c0c100c18090005545d440c044140c420904c90703100b9104140b41460030035484104480110f00d44015000c24403141d44445249000b1a500d40c070f0850201c3c00d40c0c40200e0401d2007015400d41c20908890100402e102e9540c001c0012180265804685a43d695548503240c5000b07484140310380d0442001000300e007680002c2e05030407240080002415031440d646225a0120a610911540790b030100e003008160703001004983c45004c2a500d21405030300c1540040ea01d84211503040e4400e104039904801503920500782810354180e007105c081c1210340000d0700712201c0d4000c4400e5000190074900742d5034029401084117400381c1c2e030080e07c0b580110903100c00c20000e081c5880d41d40741091341d01c281c005240e540c200a100541884100392141c2d86052048503401e40341e50341050f9000382c0c41081440b20010b03401c41701542c0a0440c1ca40140c07a0b4907404021103000300715540283d030502c030b00c428650701e07501002105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 670945809 1250 670944559 670944583
    0x1020c040b0105070614251b140a0b010504050702030403020a0e0a0b0307240c0302210d02120a0b030105040b19021b0c01080702010e030703080a022b0e010204210320 73
    0x1103035400303024549252400a4070251000081c44490200c07403404481030101c0c00c0900c1027400d600440c1904440c02d03e448070f8001c0550307504c2d500100411060829101e59500050390b0310140d442d1504540100d40010f101d03125441c944437410002031004407040c4c3c030070504658020103540f1001da40e00804901d00882c0c6901103040001e900700c091401e40a070ba1454451503154020b072201c4084242c660114500c07000244c9407580d41040034040651043c0b000b0803006140240545443c208881900200c8207201d0704180260300d0b1006220100b0703020300d40181d004a080c203100c8100c2c3c6400240030081c1c00b039900e4850f401c0701c800c06800c969100119a00c040502e084e42c415a0681d55040b040b0b0aa402c040001d15880e08100180004203204a4141d644407581090142c98103168070b1030500ea80ca264a03c04810142c1c000c000f40c0104582d00070300c644044d40100a604040c00c00300d21011140c401c00780440c49410705680c5004140c05854480c42d0000510441015050902d0030700d92160070074856 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 670947059 1250 670945809 670945831
    0x809160b0a08101a092101150b030106200c06070c060e041505040902030312040c150f0917011404060614030f0c041d03130e070e01020c040b0105070614 67
    0x202e05001d8604601c0841d840014200000040581c0390181544441c0708070360061b152143c1070301c1c0c0f460100d0381d0060440300100005403405074036010500b400f15a40045482c100c0810040000d5540f020141482058500d08003a401d80204205483c1c401116841600f11901007106001d0100e001d1042c002c940c800d80380c2030000031000003000200c90180c454928146d512210600813410142d00000f10144003404692800c4030400160301038101c100c80848900c41d290f407040c0031060401200418100e094101020138440001d406040380009000c2c10600511b07a5800f0000c000d003d4106e28110607030103118154500389410312401030030450041c817460002c1031105001c03074100000c008100300d1010010342500040c40041202524804070340c0c1d0b034000480346442034600b105200501a01c2c0060a42400c0f9501d071841168803030000501040501501c003000e0009a41c010a84840c3d6074012540026402500c01c010703103050142d103802078821441c1803280c0d640d0413405254140100700e5034030307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 670948309 1250 670947059 670947061
    0x5010b040b0f0109090b012006040512040311130204150207061d03070e090c030f1614060d0e031939060b01050d0c0e01030b0901060507030809160b0a08 67
    0x2080c4410074400e880c001d40040c0d0410810401485c2603801242c100350145429440817100f10011040e240ea107000264032a0000f405000410008220521075001501000c03400d0601d540c480001810060300402e02801c0c0500f0174010103885075040f079003d000c1145030f0004904045000039550700541c01754801050b00101002c00100c02028501f8440d48014010040d040c00d0100c0207444800140c180c4540d4400c1154000751903500f808944050a00388000384080c50f103e5107500c010200d1580503080241c1c5d1045034900a85a0404a500c1080c1c1c3c41d60100c0c0c03071301c441108546140306100c00026000100000e80f008203611214105145045103034100c214041d0703260f5030080982e0304404007d0121040621000920f5a8000707149558050500500b03200c030780d0760b0701e10546084804880000b001c4103103c2001d0b681600c50a6a040401e0324042c80139030401c84060650310502c0405070038004004005031090100704610709401480214018640d540c0d181540072640040301d108010a034014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 670949559 1250 670948309 670948331
    0x1051503011e0b0402210f0c070209130201022a010909050907060c1103120d1b0e0f12070905091e1903020a0b04080d0c0203181002070e0405010b04 65
    0x101682d40940440400c0d1809615440190b80c0104104000e154020341c0a00920380d4200f01c185a0600c00790203000c000b5070380d180490082a40410041c50070400000912660b80962114400706600080e4803410281010880c001030b850070b01c404410400f05a131841503c8003e56006c940515981d8080e02c4540c2510b40b07c1e60060207603801200c54228591040004001d07140c0302d0700c03205080d00e008a44820b44030ba00e240210381401000340540f025248001240004403140340300c0d61000f2240b280089090791100705004100142100038607101e01c541422102003555800440d0500c45c0d22002104c1d0000c0d500c4000c0c1020340404c45a1003218001c0348480b410300d40705e1035003100d0b40200600103001c01508490008110000c002001d400314030440e9103c0f40052144101d0b04c0c01140a8501c0c2601d61a444044106a541c0640090700b150003d0007c4040c032400900c1030000d0324011034011194001e40c1c003049241c00960b501c82110010408103000030f020040d400000c10900a44061103014441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 670950809 1250 670949559 670949561
    0x20c0f0106080c090601090803130312020615011d030f0f0f0d080415020910030e01063519031205060105161103160e0f060a241e020105150301 63
    0x510402e001d03900a00007a00307043c5001490594080814145061080e031a20005459500503c91105e08580760900c24030902c040f00c0d444c04440181c0307100402992a00881d04041001000c05850520086a1052000c03110100740e20485003405411510700c00005d6007269959101131490040b01d000f55003161614081c0450250682d20715512000e0194a0740c1c1e076042204075094160420240d070074003180c411a070b1903882901c4040c0c1d84d540d000c184024000b460300e00f11901584000d10242c0104c0c003e11a1272880d0169603005811103814818074103c11041504200103400c040a61050392003040c000c054115003024210602900200065235402006440f68410070481c40308962100450070006440c0c403070012a0392030050b095401d91909440469142c403003c0c1c0100c225410050100518100e400601c1940840c04840088030030b8508148022450303019520b119804881d40c0381c000410b4099102540780e082d0300107910707010900400380280244001da9410148500083c0080301034981 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 670952059 1250 670950809 670950821
    0x80f01090e0312061c0510051807090908070210170702060403081311030303090a050c0a0b0a12090c0b0712030c1d0f0a14010219080f1b0a06020c0f01 66
    0x8104002c61401540b40005000b0311801045694404e0103655081e0a20340b2202403030203010301c01c400405091100d0a410000d55100400050704085031020300451403d0009910044400030440052005400e0400320454811814065000b00c2d100491902c180e42c042c0440a007000520758003201c0b81c6403031030220303225038066502500083c07507074000c0341c030020040c0c00b40120305210b0102c040d10300000345c021a0a64004881044083d0011000041032107400d101040460004880030b005841c10810300441c42e000301c11000080011038880c0c0000c0030400c0d40107411140d0440c041407100d40d40c49a41080c503074403902c811280d01c240001480d01c00c5009014044401e41c0726118000d03d000c0712502c82d46514030b600c2c000c0d607002c1e00e0f002c445040358582814170f8006e485545d0624021000302400a4504040c2a0118224004881265011440440a41d108240d00c0e6004175510352442075000b07203184141200a800e4000d0301501070070000303541e004200e66070b01d00301030302c50400f4041011422102 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 670953309 1250 670952059 670952081
    0x402100f02030a030209120d03021c0510090213090e0a020a060e1e0a0306050a06080d09060c0b191b1209050601091d0a0302010c09090207030e041a10080f0109 70
    0x20040c07241c1d0310011300075006024440000b8010042c00224540d840e4a0180c680e441c40340400d1f40080d4003d004200390110020441140c9010f10031410320303082c40d00600c90180b06082c0709031b43c04030b00180004c07810041000101121070080c0140c0e050f5000a1752244000780080b4892140321100281090050030b8804910500404204820003211000c44070100c0803442c25038020318201c80840003480300e1003280d000f500c4a40e00013500d01d04003d981c603c1e081c0341c81801800d11640e90b00c101700280e440301c00c520025138080101509919102000c0d407c401c06501204c040b070b820301c0e8041c20344901c41445000c107913141d076075444484009801c0304d000700c0326480c0e0007a060750042d400500c07540e00a90020400d07295449000715501060f92241c50500b00740d81001c41c0180d4440814040140c0d000401c04c025141e00081140f0f810550358018000048404505001d19221001c411510385001031441d00c0c03450150994030404c0c10a64010a14201114580d003849089400481c0e043c91910407800600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 670954559 1250 670953309 670953313
    0xb010501030f0b030d0e01120f05090c03030403020d111503010303080912130308090d060905030a0e0906090a05070212040f050405010902071115190e01022401060e030a0602040e0402100f02 83
    0x1101108040f107072a8900450341d414403984509123508001940705601c0c1d8080e04031000a100d00b00102d145041c07000400915210f64010300c000c1c0003690300d034a50016501c0d88548548000c0c1c07940b1000c00c00704205802c1042c491080840004285500158070900c9240130320140d03404840d4014000030240110302d441e540704659100184001350a00b402002d400d4001001a40000e0941d510841a40c041c3c220441e41600081150003001d50001c10490541034211041c200b1031800e20003243c0c0c0b5840041c140c0d035aa940321004101004d000742f000b1200034000c9004103a0b201e80300c000d07001d240d50051040a0259250800002c0c514070b0707074400e03030f5110b82d8080c0500c4661245030b030030003a41640d04c0c0c03c02c0d4180e9004000a43c51300140201c0c01100a03041c2c1c075074010450211002909040341008074060400c1503c262640781b10002660905441e002c1c00c12441c5903031008082442c2106142c030092155100040101da00c44000344035134410362088a03007169405440f20b041f5881d2655503d01005a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 670955809 1250 670954559 670954573
    0x105270a0302060a0c020c06030705190302070314030c090316051503060d170c100c030b01030902030d080a1d06040507050a080c062b09021f050f0d090507030b010501030f0b03 77
    0x84d4140d0b401c20301c0310821910413210702080740e074009549503006440d40400b05000203803a440c3c0d54149440984c144400c1d0401f1810039210387c4004d0101c01c240000880527210010000b0700801401055560500c1e02508a03400380c003140c024020035249901545100e007803141c4130444121000340449219200c0500303e40c8000109544400c5000402100c05002d034070140409006d18008000c09004441d0a02010075424848180501280c0c0d040400f10304140c2003404000c090307180000c0d00c0d101c54520f46010709990340c4400c5210010800038444d00c003d44a4050350f103659200000740d5034069130180059602e00b5994004009901c0c66611a104494101d8200307050107240040162055090140d2191040004901c1d050180c0ca000840c50001595504050055082c90803520340c0d0200426500c054040c140b0358050007500980c9040419042c0000c0c02c19559110740d0010360b40298003030700710f600158403850300500310074007402001d00003441d003001d21501c13101902952600001c0540034002e8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 670957059 1250 670955809 670955821
    0xa09050f0c010c081305190e010501030e0a170f0c0102040e010602010b0a09090807020406090219050c0c0621071205090606012109150b18010803121003050105270a030206 75
    0x3d42c1c5c01924100c0d425401002c8000b825403140801d9031021503c004c842c20481d824280c11008104c41030300100c0c105441c1600340301030b6850006100c9401504100220080017500c1c1d01c4030094800c000c80c0ca031310020b001c5200301c10b210054019000351440c900722007031661b89650b0100d080f5142e02c08480e50100381480e0802c070b00061a0700204255015099892034000143c001c9800c0d00d0407944070400059000a90019240603040700c0142c401c1d15140c84c603d094800b107402c50385c4110080d003841c8550300c00614118060b80103c8403ea0f080300303401078000c052800c074801078150302410302c00b000342d1400c00001510000010030a43d11807141616091040201824498200b5003c00c40c50160265200b4032040804c0c02c890390305204404840c3c01280a034468018000400c98006841c91112441d0006200440c80070080d1603201c880c1c076102c01016580c040700003c0e01c0d0020f0740060030343c2d440c04051040c9131000c815013400c004035030100742658a4407000c226581e68640300010300103811080110301c2d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 670958309 1250 670957059 670957073
    0x51b030f040606080a210806060a050c0c18040203100504080708220e010602190b01170a0c03050d1b110103050a0b1c0b0c2d120a09050f0c010c 63
    0x41c010b030050000055941e01e4820745454094000d0060b2000140c18a0000040d0003000005920205a1504030f41600309130010500e40e00804410006004011401c0504008204201001a03800038064403a500440d181700d0394030b050550701680a030042c800c0c140000317402400782c0d900807130b070128500c0d24007615525040401e401001e48400006e080d18951050358440c1003c4031701070810400d5541442d490300401a01d0600c2c103e504141e09041c202ca544007150180042904442d110008480d0f051641c40700c0b01c0c00c1200c403000007400c0140301000030080c0b1000140c2042404102d031034031481d44046006070815295441c0700242160103440600b80c155210307401198000c08403a00104070040c000d8000f4001912650741804541d0440c6242011b000f0010b0801fa0400c00c2280c0262030030f0200c007120700c3d80c4e00f0f40d4050007801c080300f542d883c0d0303802c60b086007200e588584680c1c5007501428040c2660300035000d16042550f05205401d00d43d03400c1000811a4841010161035800c1c1c1074209a480344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 670959559 1250 670958309 670958311
    0x91d0a05150618161e12150e04050c0a090908160c0b120a0c090803031b0f040e0642120106020109051e1b0612040f060c0912020909120a050706051b030f 67
    0x41c409038200e0400050603146d00c000c1501981c2b04401910031181c1d40810301402d0a0b0513030061443d5070826144e0f00105520008545a03030891005013100d40142c2d0130b01c0300c3d8030f0700c030b0394003203051907500003410050901240c103484e0103440800420301c401c00803602d045032004400e0060340b001e40c1041000c508034090030550749850000700480782d410156050080803d980250344000314032403100041200034585052407105070308401010180e048011100d80b0030181c94040340d401000c2c0d000d5040c81d02a94503605070340a204001d22038144540c2c494900a0182550a004440e00d109103002030300b0420f00700c007120400810041c000c002d6408091524216525400c00c0e20382c11074001c200c0c0145940034401901e119070f0082c19900f80440c01490402d084503070b1102400100002c448082c0180707103032900c001451a40440720aa61500c51800443c00c144290740000c2d540200041c20520b020b4021000e030200310701560b401c1089a6681402f03210075100301046c640114802c1000846d5032001021075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 670960809 1250 670959559 670959581
    0xc0f0307171605070b0c061b0901120906050a0911040c0806010f0504080a0b04031b03090509060f0a1415040b16050304030804091d0a05150618161e12 66
    0x818a4440e07220a404e01002d034100b005d224200140c0c402d5004801c10005401510f80c0f90103103030300c460482058082e8026109000e0401800041001781048035400c00701e5415000001041f007800e00f1402c0c480240800d1804803444400425608800e10701442401031143c2c2c207481e01d620683d1030700011a2540100717440a401e000040c403010403000340401c41108101c0c030442c4100c1c4641001d007006004100171180203a51907a00b40500310010f43c0c80440c4c05c04944003907a100701640c641500146803015070f02001034000c2c1e030b18240001e615020401c4844242d50a8480100c4008410300400c803610407801180c0007240f041221544001c000c091180b4210f0040060761f040a49999400405170b110350302c10080c00b03031502c1c0783c0c0a20090f5056290086001c0100514244c0348035a41c035034890318103d40e20648842400d000800c10345440450320900c05c680305001c002c501d091201e080d08070329000319100004d0607280c4200301001040c250107248003040c0c1c0710394118454400c10a8042c240e542c0503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 670962059 1250 670960809 670960837
    0x2307020f030304050d14040f030303090201090b070c05040e010e0703110105071505010f0510360b0c07052b050c0d051506031b0f150a050c0f030717 65
    0x1448810038010700c0030b5802144218003402c07000c250804010005801c1900f00316855208002c100440002d01052804480d40750401250380c998500040c0c600c0e03c269408951a603034005480c03402c0004000f15401540e4007220104607000a1030b68845c201e0301c040d5691401e950001c441440400d8544840c0a6101414545130f8500329075a9148420b120080c142607106a46440060210040362128100a0310007980e9494007282210300003450051b010001c80c0c020b801421010034241e94a690106802c000e4031120241c41c0d55030010425940e001030000c2c0400d001d94000801c0503e0114030034400001c185100030000841c0380c1000110321040c000444242c41480f00700c0d842522200864070b0100c0c0103101a0064602c507050000c105900106400d02c070741c02640007061001030040407820174040544003001c030350301541c3c0842c8020b25034201c200070010022525001013540000281400e418040555a548ca601c0c51042c0c1e0b6401240340040c2400d0310200d40c400380000120140034000b00b5121 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 670963309 1250 670962059 670962073
    0x82d0f04172b0801051005090904030909020a05070606050303040308030105011805193303020f0904060923060603042901060302030a0b090402030c010309080d0e010f0b0301230702 79
    0xea1039040500034000000c1d500302c1c50709070324010340004020780117010694140f041c000801030010320302d01c900900386100c1c0346c140d4040703800c0c188034140708006040285400c540d60102c2440140003900480c1e8200c961174109400803c65050102c04d40c0c08582d03010319000d04503420b02c0c0065804403000740600c0c4070f20081b454002050740e150000030050242c0442005206414240424040c480b03a90f50441c4000c02400e0f9040d21844018191140030078030303d001030310341011300a84c6800d4070405403240d1f0302a04000000c13810780c0156000204411322a01400000300d081d0b155150500300c01c941c4554800820310004001c20720007204da8400c0164000304a01c00e009680d0002e81d03080e0203803c1900017030342c08010480d0724403c510401085001c229000412864182d0010b07a445c108901c85504060701d4a0420003001a50001d841f8000c0a0078428803140301d00f2014070340241450040088a0390508104640c1410184038081c030440440c0e64802001c00d5040400122007000781c4840e04510940d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 670964559 1250 670963309 670963333
    0x415030c03032a150c0c051e0a051c0e01090f050904060204090f0506015c01140609040f260a051806030f16030207082d0f0417 56
    0x520343c1442103114200b10303ea41d8110310440c0040310011201d800c103000500c12208007050300018400b050890303031200d01c413050321880002424860280c00003040361080380d140b25030040b0741d40c0d501c40015596079a03c04100d80503e0044803a0401c601c140c00b40d0300403041041c003081c00c01e0701c0e403a40d0103805104003510301952001420115910040340b004480c1da220140300032581d005458009590482502400130703641e00000042c0808403050b0001c09410300c0f1054903000c01900c9500106d061510780c0000c02c800c0e4101c55070b028000c0c9018070303142a01590300040303261812000c0300f8050f580010300700e0f480c09402d0f51141510702c0c10040b071078580401610509402d144180007040400344641d21203032105182411411610b81143c6154070410040c01004001804000d106902000d0004840007520803607906800a1041c1000609040c500046a40d141c2e0a007100c1c100d600483d1081d8a04007144001503070f0302c14010a08503912842c1c0800c81000f14011000d41d02003c1d000e64820b94510708041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 670965809 1250 670964559 670964627
    0x10051806040b030c070209150a120c091d011512110315010f03020909030304051c0c0807080304030206100f1707120c06110f0a06091b03050c0415030c0303 68
    0x11652200e03584d01c000741400031410302146164100c000c50118618141141000800070407142c002c801641420281c26802c1c00a8081c000b0300500e49801d0821542c4901030040b400d041c5c191518140c0c075070038014041c0f00d2030414142c1c10202d030481e40707010320302c6e02c1c0b00c2da903080c8043c50480c2c0032079052282d4401004140718100c680380c020002c24064604043c518810301481d090000c252424a170428030410010400100702c0310031406020368500c1349402c3c444002d480100740300d10054206540401ca4508005142e402903000714000c0e02182c01aa840142c0c20300101580d009200d10303104291001c114102848420899980308070040d5440103881d41e03040d50000c0541e0400340c0d12580482d60400031076402501c1041c112070700c040a03180d1000d400e115195110941603006150300d558207054003d0100840f81512407860707000d414864a640d0f03003480c03a501c841c1420018822880c10701500da030440c50b204001c0c21280d11480300100302c0c0c910340b8250b03100195401303580c82031000403412071001c81e02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 670967059 1250 670965809 670965811
    0x91009030f020607081b060a1401030506130507080601030813150c080d0209130606140301030c12060204030b100305061302011d010e0a08010c12020c300a02060405060610051806040b03 81
    0x411b03004181c40c0c1361004281d8103070341c00110b10b0300c005002d120051011510108020340d00040b00c800b011074551041ca005803030500075500c00800c1e40078510020003001500401000300d902e8103c911210651038400c1d40e8401095050071030301140a4520304400a04d100005d4640c0b00c2c0c2e0820010304203842000071810070030400311924507203035484506121b01a04580c007500b241c10fa0741040e41c02c1d0741c1076544d1a0781070750140c014140b0b28148501064100182501283e002e9a480b00300d2051030308103608030b1644444240400c41344c50284000062480d10344007034504009070160b6030200d1807201c0350790b07401000c00407403c2a8108601e0000500ca1610390380304280081005c0c2000007003486408100a001039401104a541c0a0040145222503040010b4820b0080d400340111000c1c640b072a8100c008110103e640d100c00e00c0804038406110301d40210702c4030320881c060350070785400e03507168400c1042c3d0007030169040010034820b01c4080c01c2c54503146001e4000240151019240c030751144a045103c1d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 670968309 1250 670967059 670967107
    0x1704080c1e0105011d0103030509040f020711030f1b0105031f03080d050603011a0f040b09010b07141204061b080301030809100e0901140f040e03091009030f02060708 73
    0x1c0d2804080701500034400c89004045a000e4143c02069400c94600c03852010300c009420043c01142a2415035905c0d402040c43d641702c484210340d54141ca00c0c050000c00242c090320303407090017406121039588401080c180b055584440500304140c89960065a1a42003c0c4c500303103018a100c0400044604907681000c0071310b004403e4292212203040b80341d03044d2040200780c28000d03410b002ea4250801000302c010648030030b04944c442410009440410002c1000c0d041441e40042190000584140742a008001c1107004044154080c10b440d11000d030b55400d186401001c800d400c101c02c000c107601c940442044008100080b61a000310794a43c2e05140d0805c2e001511070120000350222245840114402c03900c109003030060a0484982c00106501c8051003034409031408101e00c8070303442c0da441034020701a0030010700820000419405040c1c0e07036000800c2c1603001e101c1c209070101e640ca001c0c6012400300c0780d2001c99000b252040f6800c1c040d441d00404001c6459820501090689861440c0c0119182c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 670969559 1250 670968309 670968343
    0x30613110f0c06070c0203060621010507090602010614060f03071e0203040e0f10060f0e0a0801050603060c16061806050f0916030312091704080105041704061704080c 73
    0x220603207200d0f400c1c650060404014081c91100910061f00c001c50096880b220413901c140b40352840c0203104e202c5040e1901c8110281d440c210400402c99007040350031050310080e90081000755100c00013030109180c80c0700c48640c801c0b001c3c40141d504400080c0196408034280c5440c0c42d188042c0c000e880105440041d4000250304045800e0018002c1c01d0a038a902160320340c036000c0603003003079802d288200c403140c080c40c020800e00e1030441d000c03280903004030449120007404080015590b100007600925040c0c411a101c3d000315070200310344400a5081d10f2040084400180b040e010307913545c1c2c0300204561303101c040c421510f4030400c42c08141c441c440d0f18820400c8001508180c64486030280c14840320140019140d5200001400425403000880382401d040900c0050b01d880c00b41170000a04013604012900d80c000001d0100c0e9004e0190003003402103104000c0c0240000001c2d01001842c0a103000d05070020382c20503901388c841c8054690315904a80289000c915020b52041e8503820030343c0554402400c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 670970809 1250 670969559 670969567
    0x90d08040308190f0c02040e011b1e02121209010f0e01050723040e1509011e0902190f03060506030c0c1e1906020d1b0f090b030613110f 60
    0x50a82c90810b121040f11034504088440c0300103101905c00d054070440a0b0260391303189800704004100b5444905484840d07040804144107441d0000e0800742402621801b45c0c2d08144824403107400050524004070904603814100b000000100401020043c149403096480300000d08542d00644900005100041700100e0180f40c00c800180900c14034801d0048c01d0040c80c0c1c2e5071050151302c2d606890603203000703d00c0035000d600d41c24611b07001110f407951031b01e620006140c0009002c104001240c0c171000881d5000f4801580d07117014130022030060491001c503c8401d108160a03183c4600031101342c07260b00d0f003070003d5240d4030703a0041071440d04101d418829001c0006240d00d01680200405484480460041c1784c4803548441c0590701c0c0c807100e2003104141c5100242140c10000030360180e540b41c00c0000810030402d652100c0020301c04080149150100d045810340c1d40c110380c400da00800586020000b040c0c5541c8801c03050140c84520b804001c980d0b182d545c0082400099518001d00d82c29441d04d203c0c54031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 670972059 1250 670970809 670970827
    0x13050610271203170f0a0f0f02030c0703090803040f03121125050a03261c05190e1b060f030c040905090d0807030513060c0c030809071208090d08040308 67
    0x210381038000801e8205500008006002c175004425a0380224444c0700403c40096442030701e4040d0a10000c19412540003008101d00f010050015203101d030f009545200010b40d440703002a8481c41940596103640248140a0000ca60300c0c20464020112a1903d034444211900020341040f06003070120400b80e041440f41c41445904612043c0605011205c184060b451aa02c0d2403101c2d42c0c4c0810119902c00520a6001c130211040c2a54000d91244c888030340202d01c080c0d400401000211500c0c01140d002140000d414402e0380b044c1500360303049500411240180350004080c58020b140142c0d0b02c0320b010031050102008950195002d819a49a1542c03602d081c64100d070161040100180c100764410820745103980c1e840045190007002906000480e80c03600d44401c00d5011500300080d05003403e00703000d2140154040b4a200e03203540203a0f01d800258441e2109242c649140b44034409030146111543d80114441c0c030001c0004910003822900c404809039a040c0301c5411544c03054540590214002c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 670973309 1250 670972059 670972067
    0x3090503100614011b060908041a0a020118230f100203060405010803070507030605040c090c02211911030c06130302070603150608090109061a13050610271203 70
    0x303c03e803d091030800c4003920180c1002c0c00e18000c20141059407110441c82c140603003d421200980001100d074401c2c4402551000341542c000d103204401507107440544100d1409991011036130550100181c1301c094041d40c400000720078284840b203064014540240051941007002d243c500c01c10000260312841c00307800b000202c0714140d1103260207402c100468000a0000300d40201600da108038002182e40b240e003000900d0070805d4211034041031901d81510000c43c1c000a03e000b62035601840c088507074070000c000795902c1c042c1086800c000b44158415881c050700a10034040148507240440e030801e80001c44041c540b0f1020b4aa0a0b1603110840c40300c0c09240d0f040c0301f41c101030049414148070340c51495400c0c251482c600d204032170411603500c0100300c0b48a4213402410a55810000500041880c522040c1c04800000d80030fa126101008040c50512000d029003803203018001c080e2002171514600c2691100ca1002e00380034481088074080c0c91031b02c100509007010344440196200540740901d0054 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 670974559 1250 670973309 670973339
    0x80115080c1203190507061e2a050a0c02040212073c170405030319090809040b0a030b070e0a06050310050618030a080d14010e04020607030905031006 66
    0x20b01507462600303501c40182002048851214658450561410501d0002c55603030045040c01401c40d82004110454442e44a8480301c001c410a8000c00c0720740140341c1c00001285000d05e092880003080d420358100300c0d000700080d140e41042d0703040800c0c0d149820360000303040342c0c0151010880f0060340014003007100d80c40800740c2500c08030003840c04102c0b8021550f0761410000c15038120b080c1d945007400010750610501140d29034401c982461001818203141082e222f1f0811107614010803804680c1405005940c05640169600300d440b1038503044003141400007a140e0482150f0b00900242030000c00107840f40300c041d120304c081f950385c0c02c42c20307842c841008030900c0513070700110400c0070900c14840304840040c465802c441c0708461141e41c0303480300401c2e0300041901551859060191116450520803e0b90003004846880c2004101040d00d4100f6103a40c07075420300881c484505003c00240c0141048001001803500030b081c1611440d5513100060310b0203031500a0010600c0d01d81e5801c0107141041d421b00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 670975809 1250 670974559 670974583
    0x1e0d02120118290d0213090b1501020703021320030f09100b090f0601030f060e04050c0103140a090206070606080a03020c01020106060e06070c0e041a090a15020c010608011508 77
    0x10b0301144880f01d400900e603680c142c10034850100c40c0301c2c02d8119a21202521032810701c404040c000109103080c8070400d007804950941190704240d05040f819840854885c0079250300070a0804213a903400b95031170041c21a00764816003014158807007410029003001440c443c030350920149405141813042c0038240386481e9030f0100d10301d003007022000e003d640750741c00c05601c03a4980031500850b58440d00120080d082920000fa0800c0c54810081806444803540d14400c074010740403514440d00c901d004404484549000e121802d8601c004074880051039040385c081c090006102d142041c4031900c600c02290656809005c041c0d00c0a440e2000b0160140012580d4a6090000300203d40c54106c02400018804080b20301c5132754000b40400401201c818144050040d2074003940081c5003600e410166508000d403402400c0030240001500d44100040c4000a0356110b00c40044104000588101940045800030f03a9035490700808581d0301c07000d01c00c1d40c1c3c504543c003051156442c0b501c808281029101d82e24 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 670977059 1250 670975809 670975841
    0x2a0a0305100f0603020f0d051e0a020a12110622060c0b160e010c020406091505010815060f070609020301050a15050906061911060717010b1e0d02120118 67
    0x100056a06d42d000e0494505059400c1d500801d00c51400908020180030040f0310b21050301c00040d0790303000009801f64054820303035101a02540703400b0210511b105da400d004002c0c80035000240300600303100010f00785070011140000c0f0104911072103144183d80b43e810800014131110a2041840302000c4401d400c21038080d0302c64085829418010310448003174922134103001c04a0345103011500c81e60722481c020104c158003048030724401c004da82c58142d000e2084900160071440401e4158a04208c9084070030b00013000c00340380041072010305485421240b810b0314500e9459803175402589007809034500c514401000082d040211109200340c20307080340c04c854002c2c1010400c0201c561202002c40340c1340f4050340444061861228422103a056510a41c8a050300950741070003000c640040602c8401d00300240350005680e200c0f142842c181c044d40268041103022a003a801c2d5441d0400300408505003009400752400c040d49030000c84055003039100c40f1301c2d0840701c2c9101e0309501141c45130b01000103c0e010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 670978309 1250 670977059 670977071
    0x30d05010e1005060c0d030c050f04030605010311010908060402190e2517060f120703121704050312040309050301020418050907030b16030f0c110d112a0a0305100f 72
    0x400d84d64900c446e668000616a0710704000c641580500c0c01d40c3c1440c10300664131f030b50f03442e200d00c0c12002602c8284022251003000e01000381c15980030310900e0307041c4c49503007004100f40c2e81e6503002c02204c42031422007008011440a0041420074480030035174410070b4501d03014103400c171401c5198500030304072640340303001c00259685c03000d400c0803036100e480d80128044170000340ca0412030001840d51161522000300700e100b4508004108050242c04008296151316040e09603030071a03002d040e074044100c40041c4076402c100540141c1030208070031590003500915051000340e4070b9030301007401c82c0d116801c4425080c0d81c5d1a0050507204840c040c182c2d021380d580003d009000d1440d582e001004402401811421154a020b40090b9109038800404154000d4007070040308071020000d08403028428004065005440001d40520f0240c040c440c40182960028951820524200c0542d04d56840504a00e9481d140014249035540c0e101100614000d601804011110800388030440c0c440000403455241492 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 670979559 1250 670978309 670978327
    0x15050105190507290a050901060302100c0c05120f1b01140a031e0b0f0901230301180606080f0604080d0c180e090f0f060117030d05010e100506 63
    0x2103807510003084505190740c44100da4035102c001d04507101d060340c03402c541050f43d000810314007800380f50092111031010021078071411401e03400d0350b01900019401070001000d00c0b0006118062802c0182d0007440c003c90000d440d0780018202c103030350006d00f040b180e1000a030703c034883c1d40078010394200310521300440c1e04506210001030041003011428401800001c1000741d002c03030107904130443c0e2080600601140d00b503401317039944c02844100004c078014a50f0b010b2010310750500140a90580e4448075a44911107240c4213507107034016030b4a141582554031400c01d02d550159000c45042624401c0f179002c906d40d41041303581c030f2502c2c1903101c04c07282507440b90062001052451048500086505d1340c04940d166070302c00300380c0b20030030440b0020013466010080054642200c1b041240500082c606440850a01078046030b900e55110752081190f0308108010440500c1e80d6000f6800d0414020641e0f0030312100d07407512070849100340e0080840c81c41c1c48082204130f9000c0f111303410203000c040f50402d080172801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 670980809 1250 670979559 670979587
    0x603061b02150601050307140a0804060609020307020a02060f090d0807140d210e0607020a030206130c050f0f030607020601050306180604060e010b030304121a0c1606020906030a15050105 82
    0x2e00100d05021740080031a42c0a44510400d540c1c0440000101c0d565007441030005080c00c0c0202d80648065140c10800b0070480340f50f0003201e0081e5020740c01802e030300d2032940800185600c02214168180b40c1040016131a4540c041c0317528100707000780b0703010383c03100c40c80d041040281c2c204003129049608606070900c84150855100900c444c6107a080303000803400070003070000800c02000d1904940c400e40080040c003076030000b20440f50303d12070b5013a505140c0701d04c14a6130340010700c240000d064610104080c0010304140d450140c01000090071581c2481480012a09045040e5080301c0180c10240040c081410100074490304140880022014101d2201110b51607010240005102c242c5403410361007040700035000301d00e02181c0113094a33911551104203401e803140c40c2400b15980d540ca6007410342814282c01503d482200e42440b154036003920031141c1000e0719014070781192074990a02c22503002d43c81c0d1368040c61054450110000d00503a89402613043c40065500c582c1c1000010050072041c0f443c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 670982059 1250 670980809 670980811
    0x503070e060a0302090c030406060603020412060b1302031015020c011403060f030d1d0a030f0f050a0602070804050117040c14181611190f02060c010603061b0215 71
    0x4030310404030301e480307010014500580c140d00203944400040f0030b006004070704800443c02244200c800f0030811b6620603081d001d0340154421860000700300690f85c40444c0c9160071070380341000d00800405002400110b00c0703080380c0058912980c00c6c03072011001d1042184000030000410424001010f1500000b03000804480c14446524480300300031000c03400e0ad45030302e00c40c0c41d1680e030014240e60345801c601c00b0040c80046160521036815910100c41025810840001420349401400052144d40c1c1a203c00010041c820320886103403140407245804200e007840504070f504e03c180843c0780d42c0c13841c0000041c141c040102e0481042c803106010f02002442c1c60a0070802c56000d9120300c50004030201c00a00d00c2e4188400782d40c0c1d0682c4002c20003160503106400d4105808030358540700d102942c0707206d640d40c0d1603c06e00c0c210340315560f83c00c1a00f0003051302d440d803649a80d40700400d914138248010510b80c0c01d41d580b80d0b208445140e1100440391480d403110641644441c040e100030701003082d80740d10998180300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 670983309 1250 670982059 670982069
    0x1506030601030609023c0405130303110409060902070c210209072c1903240e030c0601080120040e1305032d03160f0203160305091201020301050307 65
    0x4e40c81c90b00714115115910030a80c805400341000503844440014600032101044d110603107891403580782c038864074041c4182c900410180f2403540440c200c558041c0c0c010300654031555080c0c40140000107200c039a0707019960150000440142e1200341601d4039114031440c1e50042a04001c8140320040c002d009a15020781c0c1c00e40454500c202a2a0b83d4411307201c1c41102d00300340041d20207000480030780404280720380aa10005030b550005851601c0b400784400c0e50940001080c110f00340907040403410044041c46520507618000254006040035094516407001111006035002100104200402072280e0306100c44007407510700c0800c0001c03a4030056440703103014451641e000a80802e0402e0200c001c000a034079400740859070b0b541d41d5581030113952400482001080000040709049a0303c481041e24001c5000300422808010400c1c020303250b41903110410350451000b440b009641452144141091a0003908c40b6503490001e001401031800c40c1520310b014a0380104010005514000f80c0b40d0110b803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 670984559 1250 670983309 670983311
    0x1090c050304200a0e0105030f01062714011805060609060a180924090b060301050f0f060a120e07050a030b0705070512030f060a080c06070c0b030a0207030215060306010306 76
    0x2400000b000d0143c041c2c800310a070007045190004c910310000e04020b50590308110308942820664040660030b8412500441c1041d0f15407088000c410042c02e0320100c0340702c0340070f640803610039860490080c2a8070301b44d00c040211241000a050394904c1c502c55140c00000999a6a1600041c0c1e80450001e1050402401c10025400340507000a48441407820184c00ca02e03c051100700d6440030402c902c98014161a040d0780411800010b00300c08522603c00b112501a08190a5030318042c100007202d200c0d02d4040350040c260388940140d546e6004001c10089001f0380341d8401c0790085121010445082542540041e40b01c880180a00ea03946da10901c1182e520280e00191581c0741842100c3d90302644d000104544100c04c00c0d000d02c280c0312000795210345034034210000c151b90780004120041507140f181c803c3e603402c010760010040c14107600030b180441c06024804d410b1980d881401c09968000c032811595160702082c80000c040d4140512054004031003281c65407800e00300001383d140c0c041032000502c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 670985809 1250 670984559 670984583
    0x60303051603110604081b0a0209060405090a151a06070203122503030225020a14060906041d06120304090b0a050405041b080f1b0d0f12020601090c050304 68
    0x10b114610030501c106003403084e90700303a05162402c80c8013a00b151030050406170038504007040e00340c0c00048800406400030b10007201038540c401800300500c0c0c0544840344a0080760000300210307035040c081c0f0080713084075900020400013104c640d095540d800001d84c3c0c803440040220001598001460361030b4090200c51850355181900001800030b8000010005880192910701d41491b4143d03001d0000d65201c06c0041d011450110850401404a064000c1d80802c0501e000c0c0241d00e00e1446030042c03400b000e0b0000c1d10f0200342c0d2000641c45c0c2c01651041c1c6c0d202c100c0ca62066038540380b0356440d80d00803200b03079801c0b41410f154000b060b03264041c40c09000b0b80b20b5595142c1c25079503620340c8003500040c4001ba00030403003402c09041080c80001d04114030088484c200c3c00001e070b441c40014181d0960348644d0007034031004200041c0746000160b0051003547c000500c210b06804924141400d505c2507100d020143c2594596205c040e0828505a004c441100d2034081c1c404041600242248d0340140d100311a00c6407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 670987059 1250 670985809 670985813
    0x705041811010e0d08070b0109060b070b0604110c07050f12030703030b0f18060114130b0904060e01080d030c02070608071110060801061404051b160519030807030603030516 76
    0x1840f4019190360301c4044020718200784a440401043c181d40103400e00401a0389030703100c10059a2541c481c10004140400c8054046114001400d80040000308040b0300c0d4149003003035956541100385032038245d40080b02c0410040c03502d4640c2410300e074802d0711440803882004084e60b4481c00b0700d0f170002c0d0030705860f240e51002c140e82e6500102c2004030010220000c01118840c00407441e403048400314080b4108089040104215405031540008111001082c0341d040940300e03c42600400b03440b40d00151940808102d125210050070b000e4800840140500080ea0710000d0a8814456041c805c1d5086083c1c00c0c000c0c01d502040c41640249a13091085070044006d2090b460310541d6071101501e07034649400400c4091064011400b10340401e440c482c0402200300420003101c6040c0c4207860101c2c038617600101000c0c18007001c0d2212129550400c440112140c40e20b81c107108032046c5084210003030f00c540ca010503422060040c0c02600515041244038250f66000d0a244940b0785801c2c01820002040c0003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 670988309 1250 670987059 670987067
    0x7141f051302151810173d050a06020309100302030402060a0309150c1d090903030a1d03040f06030e0105040201200c180403030e1b0409020f041508070504181101 71
    0x149a91020b0841500c40351110b5001b0300342205c0501511a80c8000c0e03010038500d030038001140394040c1e0900d0703800c1001000303104da218503407882c4c06800c48034200c004800556661400380c2500242101d8016641c0c80c540c1004020f141d81500030800180b500c184203010140e100d0300c0c1902c0d89003015080014610065080441d030f20446500e0906403607040c440e403a110550b0085c60240c4d114448034520038230303200c03100400c003118104494651680c0d005000003101c14425400c2480c1444454080c102e0034001001501d081d42e0064101c480401c21369582080070030362610078140407090100007000103003420740c002230034000e070310714510030340c0f107201030310203a03130301080c058440080c9004206d140203005d00d04400703aa1140840b400d40101b442c0a59214200d640803820012400e10b100082d03120450190401004000c010002d076041b129108282c85241c07501d1003058002202000380d103005038600320722a85829100d0b00618019414030304240e409400252102009580c0003001c011240501c9004031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 670989559 1250 670988309 670988347
    0x2090607060f14010504020c0c09070e13050708070302070206161b090614040b0a031401060e07032903070308090612010e090d0807120207141f05130215 67
    0x2400d114580781c0d107a000402d0315841444000008080754016030390345c8003004101c0c05500b42d0b100068222061120f11894038181142c1d200249003400303511200044042030517400e2018441d4484ca80c1d5005200342642c20480555000300c017403030150301e8001c03c0c0c1e001c60b1403805811502c41300041e628a4130400c1114100105500314030400c4844402030f1707503a901f040035180c0d52040c10403d07a84111001c00b207037803d0058081c0d40c60041c0442100078510b9981307483c142e4a07241002c080c0e540e50b50002ca0301340d285160003409000d181d44c0104540c1c1c4d004d144c200c618080c100308220000118404040035407000b00d540c4040381e07040040303aa2100d5090010034402d1060303540e045012070410001051040540f20700c9406003841100301d0340028003040307041d24811000c0e1103607404180340e500300d03a0004640d9001004207600c10050450306055480d44a494500b03141110050100206103c3c8c80c608010b10030390303600207a4480e92154001c526004034002c4400003d1811102c000014418802900208c0003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 670990809 1250 670989559 670989563
    0x30c11030f0f010609060b04030c15020114130b0a0501080d030c1b05060f150102060a110c0604080a030c1d010c1a040602040509180d030c0c0803160314150402090607 73
    0x28404001d10448010300030007407401079171121440e044000c140050355205072401e684d4400c142c51800750601d900076803414007c1c1c044200b190748a01e040c514000885108074001c08212803400c03c0d210107868980c0c04480005c3c03000d0b602e42d141100420000f480090701100e010304e203040010300c000c1c0742a01168008103010108925060910000003008400a82d40740b00c1c6201180408168a8483c0f440480c50024280280142e0198000c604c1402c0300d68841e00da561848d007402c4d0b00d00160901c402d4200701c0101e030191000c9001140900c030107038140c0580c450307035010383c50b040d10f16039051140c0c080e43d40001e180381c6040000d482c92010030032003500e0100c41c0c166009880c054080c50180362080103035020b400745030301480246020030510408005240300700100f1a0140c40a1403a60b88210b00418036440344908220702120b020340800c3c0c00c0d800450003640c2d21107942d40c3e04400140b01805031180340c0700420b5030300320b10810482e8801143d11900c0c5101e004880150b50341c0701039000106540100340740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 670992059 1250 670990809 670990813
    0xc0c0f0b0709090e03120709030308151305040f0516030b0f1e090607030f06060e0108150d03020f06010503060405100903050d0f0f060819060b150c0a1e030c11030f 72
    0x1004035210000405450241d8012103150b03120740c0d51130012070b004d0400d40b00040c0840c2d01040403507034540c140ce14850260328040c02015006910010a80554005450540d5031440304603ca00c1808002d000ba000e403002c24000200c41d00e4510703641c08c140110010107050b05040c1d2540480c03801056100b0542c90718421540341c4015040403128580c4889040e50300344003207032506411008481e190f0040303400300ea03840e4864400842c512713001900d0b821001441100001d04c07403400400e03070303541d200b1030190f040e40640c0c001c01c1c500e0440401c552a000041e0480c0b482580702204001c00110000740c0c810b020601030304d0211303024900c0e142c240c56500a429843c16168140080c1341c00c25906d5a000502e030380c51580c401e10286503180265900d410138522029912042041e10030040340c1e0f03a4128908041d00039000e90441c0c82500c0841c403082e040910710314032680003021180240b00c494003c40c5001d1101c00d5120802000b01e5401402d180c07082d18004240b991072101550581d5000c0c8800b01c215007210b42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 670993309 1250 670992059 670992071
    0x18200403030f021504080d18060e0c12060c0406050f0c010c050a30151e0305060709051008090a050f030c0d020a1505041b0b07060c0c0f0b070909 64
    0x14000c2c101040c000d40d224010b21135101d00f42c60821407282428050340d001000b00c0c0c5498201700100003d00700200c0c1219903810800030b10f4001440e00d1103501c0d007a05410020300302201040742001441e2007060084081a44248280304070044050300701c504485190500c5541c500785900224194001c0300c1000070b2551030011204400c039080710017003421401550343c0f104a10329410800740c8204042c0080f0810604508105081d0585507200c0c2d035000c5203404105032503513a80c01c120030302c03401341240f0032040040c16403040040102c2045075540088240c140754000b41c1c10714000c03c80700d90b50201e000c1c040126100104403003141c10f001e05c040090700130040d40c184107a190012aa41d500507021140a40708420741e0021041c40070861408640d80b200304d99942d140d055500401801001d8801c1e5a00b0341d545803a0b1400030180c00709400181030124001d03032aa422414104c08807540380d034000c418007444258010004807001d032010320040d030000a250b02074072181e0080701d01d41c800341c0040290a241507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 670994559 1250 670993309 670993313
    0x30606080a1106030423070305030d150e01142218020123030f0901180c08060105062d040915030203011a180a0209040204090c0806090118200403 64
    0x12a0900a10340500142d50700c09100c40240686403100700d502504030744104001141c103d2500510815840e40c4004071580c50340ca03601c40364110340c841d1401e203503590b44d01e5141741d10b01110000c0c3c010061a00301940d500c80c0d898071101b030410300f070301c0aa014860010403d0b5002140409608000202d5006001700501d4007844040d003110745980209031301040d581403c2e070780e40e40c0c84000710003940082ca896542c21901c40452041c254030000c1c02000c150f54884061076110680d568117040154060601041390600c0c103a499810840c0c1a08658040c000030407802e02403232181003003002a42400c0c0011024080c0c80c11003510540501d8002003041420403000b00d0700000c50024500c00d81c0d008070000c22001310360904e01356901d00c11b5147e281d0401a407105645800029030b030300c0c507413000580e50054034000b50480000c1c01c070390058004006681c0c0d00d50780c2c1509154040c400c540e004005403004280c030350411140c24018a580c204140b00a13480b0b0b8003034440007031900c01c000031803240080c409803110b03264 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 670995809 1250 670994559 670994563
    0xc02180705070213020405030304120204020c06070909050106080c07120e0310020705060c040825150309030e090601020c1219081e0a0c0314090307090501150908121303060608 77
    0x560000e9110700c40c81380f04103a445041340b080340c0032144014002e5140c5480c00341909032070725507840140c0e402907090000d0040d8401c20b2020500c81c050541da0190914103110407001200c1040c0c01ca00100804401080940c201c0c5004580d21940c200a010240c1480711504450a40d501c09000fa00340c0155840000c1441881c3c000d0101c45114100f83c0e050769480303210040300c87c01640f1855403203922460806d4039941d040e80f030b000d06000300010885e240c1600c0c0d41426441015400101c0d0000c2d94804131030007416807010001c29128011a480c207035901701240002c0d5030390a070311041440303510540c1e40c070046640100001640100c0e40589511500c0443c00c3c40035094000d8000c0718051840010800c1e8041c0d0345000f110031945031134881c407449107030300d031405c4555901400c1d000100340380030070100015503000c000500080504c080c01041944c100041081d01d200d41080b0f8009202440700d041c818490086031000003581c08107056500da20212511700030010f1507074000b8004524201c00828113481c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 670997059 1250 670995809 670995817
    0x80c0d030506011407020a0303110f0a0b07081e040b071b0602040602060705340b0906150109060815040612200d1112010f0e0106030507170601060c02180705 69
    0xd072200d40131007410395920300f064400e50b50f0003580030304c031a8030600000f03000c0c204080400b0000c400b1106440040c40314135103000d05a80d002c0d10040300700420030001561024079a6400f6002d4803a00d560450341030709148501c2c6014100410070701503000003c003090720500300d4500e124000c0020b95038240c103504000d0b00a511500030f0744014010800015080c60180b001c54485004913010a860002034084110894183c81081a168259032442070003195a19603054000da10000240440d4200f04034503045146c11201000d05010b1150310070400c90350050900d59201c0001410100c5040503140020000e00064200c90349101a94100c81c0034080c500c00c6d003d034004005000c90055907400c0c0204240c0152240c80201118080e600d0b01003a820800100260000c0a50010407a04440f940c0e00c02a952500c405410603036648004005004040003c00000e0840500e24014505c0305984581c035081c1c14007c013010b01c0b502c584007070b0441d142e180c040340041400c1110450315080410009201e544 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 670998309 1250 670997059 670997071
    0x27010e0106020d080703020702040f110c0d0906050d05040624080d2c0301090b1501020106050411071205040b1c05090d091202060906070309051305010807060507080c0d0305 76
    0x1200000104420303000007000c0d0307031074400b42d00c0f001e0b0242d4030854214084d52003108120b801c2500d0341c825812482107406854500e8004080b4103440d0310607208103601e4240c03d40680300810842100070810a50003004031404960752840218240d901d90030207501602d400700021001c51950096a003c00503040c01030f10079078041c0c00948482d002c4a080c210b8401006900360465521051180407412510a855019160300640040382003009501c402111750302c2150020100c00c400c1c0d0080340307a0340e42072054002030a41214100948941c0c00b0340b0749900c0c0102c2e88010305846515107070141c040e0040003070354010440070440c4c0c0d0741e848141c240545049840310241d800d160a00002c64505c0034003290328200940e140d0b8804030900c1ca4000c090300c0c3d0621030041640c000300704005009040d2282c900412400d070003511121145880d000a100800203034a54495a061800005000e8000c020605004464072464a603807140b98a0901d0700c20392086d000d016006101d46040700861503056040302d84a20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 670999559 1250 670998309 670998329
    0x20105040b1008070e04031e02030405030706030203010b09060c07170304091407020a0308100b0c011512170702060c03180310090317090106030b100e0c0901050307030b2701 76
    0x2031035407404410000310b1402984581e4004000901c2140c50b0a9020f6901601916180d030504940a1811082861003400350006070800542840300b401c0400c198030040881e850114590740c917054448141d4091a64a28843c3c40001a000c5500c41d003000100b01030403282e01c084c0c074489020150242e0b298003602c1050740c190304000396030181446c2010307524824111034024203034031000741c1d4049418081c002c1207100c0c0d5544000e00896466290303000b402500c1204000001c543d01124203032501880568019440f0402940031400014250402882c3d44d542c003109150700c2e550a413000032441c4c090103681a0181c031003c1006289402e01804c150b640c01c1d0140c0a0703600c16030000c5620b009850701d20764081e003c1182130f0550540c0d9801d1014007684019090f0000076411b031a503950404914081e80c1c0040d1101d1010001e101118240003c83e0b008520f070000507217020302c0c4a00103082404001c2c8401e05059031070324003000f280c84403040b40b4070002c01d0444a018070f001f0802c244100d20300130f0007200318003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 671000809 1250 670999559 670999561
    0x309060f04031d0a080d03061d070c03120209090c0306041a0f2107080d03050115080109050402180106020102071403040f0b0c070f0b09130603081e0c030703020105040b 74
    0x14040c21282500458259482006803c60302140c0c500c3d400300c040b80c4541101141c580000c141c8000d0114042403009540c01091040c03030140e15818002000240c1e011072001d90091080b1540c01c2501e42c40902c0c6e040c24404100c20300d08441c4030081c0036003408a030700000b0000c00c2107480382d5040300551203010211010411901000c2103d200c1c0c0a0302d800d95030f0040000c0058000034940825080c03000d205c19550038161040c0300041608088642c0d001411950041c2c90a094040c0c0600601c0c1c05021002901c0c5262021003500510754141817050348a0b1555400c040f07070564a40c01c144842490084100c0784d15035a4ad044024001c0d03000ca032041c0c0e18202424051a1010301c080308490860b48500c074406103090030704019a0060380b01c2110354945100e40b0900160040c40d501340c0c04000c014041c3c038191143e031401c00f404001e101e40c44203081c1070351801d00140700103082c0c2400d179500c85403040799607941041c610507034200a2140500d800014803010502000300f5505401032441240304000540032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 671002059 1250 671000809 671000821
    0x40906030c2306220302150a091e0b0c0307060c021605150723011b0e1f12020405062a06091506011b0c0317090a03060908040509010902030906 63
    0xb40c070064080350f901c4041044800d04150500000c2c1800b08612000201c2c03090784c81e4009984001819070b520548940801c0c0e8400c003640041f200c40040100c400c400051301d4034070107086003a00440c0241c6d2803002022402094041040090320680f9a115600300100e90961002035600c5241c4859000419041d120119140c180400d01e44500000c6050050034804141d980d2454544146807500c10519007e103007000c500800d000701c2019070103070b001c9190600303c0420010a03810000c1ca0003401031841c07100303480200c1060219220031103107510300541c00d156030700f41001c0030780304946c86268010004a0b4420500321414a2085900c03820542c1c4400c82051201b0280c940000b01c0c0e14600540000e0410000c441c60202100c0c0e1100052501d040c2e600d220301c81c0c00017520312509060700c2b0f060a694043c0208125100c5401510200540d0300b42442b00c1c0c1c90000740444000d0000414044e2148815020808144155809030100810301026582c4a00200c00250000c940e2508940708140101b28 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 671003309 1250 671002059 671002109
    0x1b03100b0a17090c0a030809150f1801080c0304060903021204080c09010510090b070c0f092c07030212010f05010602062d01090b0f04020a120e070e061302040906030c 73
    0xb103641c00605213240c482d11b15115000303e0b8100051a6802850b5880900c5052980c00700400010f061021010380f558803803100780c60424001170301c40b4103014031001400b03180134803a07041d42d03403250748510046240313071351864204d0030702c0c4155900d034426580c04103003c00c13a0403000c2001a02c4503410b598901a61381da070002c114000c91501c02080105600280503c030642ca11801004054000c07503c586403903607211a803030550b0384568480313000c1c2552440d0589081e110200403001213480d0307011150940320311502e03141c0c035840c00b8070000348224441512440301c20001e401004540c40c159004000540e0350300c202079203481089400100054034400100100308080000c01110081a20340008584c00c088802004000100c0c05a602c59074030840380400741d507140010440010581d03208540e244030003c091307041d00d015400008054111040920414960360b040c150300400803901d688080c85102c0345a00203220780e402c210407240c1081d5010003402204007251040380c1d182d0406030302c0e80801c1c0c10010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 671004559 1250 671003309 671003323
    0x50f15160807080903090d0602040e0709080d031e05130c0605030103030f050a030f1a0111010506091506040824010b031005010e0105090d0c050f03061b03100b0a1709 73
    0x404901c16401040c0854464400c8543c00300e030240403039152882d0790000400e9070041c19000c88515800040511406800d0380da00d540180d0581030021700c150510320003a4480d0540b1550030304040d130b01d004081580c008502c1c402c5564015400c10062400e0113075002071045c010340d00903209811a201d0004189100d40200c0341201c0c1c0642c0c03108216251030740100c43d00c3d1320004183d01015181e0038070b1101104903200d134181d94890301a8040c6000303004000580440b030a2800a00c00e03034075140070044561100300c6100d901514860311020356008100005006004a80011030144225129001c01c00b100d182082007005003041000d00c1c070b0b0391700d000c10340961104443c15034094004903030400c4a9401802c2d0030070300201c141030540c00c041e030301400700b140a07842c00d0040d0b0b0303100701418081202d42007858100300e42d12002e4000d007520385071250104000408844c051503000100200080034003130400c101d00301178a44a00d841e41c0d03440103484000c1c40d00d50f000c4401540100040c0200d444020009114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 671005809 1250 671004559 671004601
    0x9070f05010807020c013e0106120b190207140c0910140d05030d0216060c02010b061204020f04090b040605060406050a120c0b040f03060c030c0c0b04030309050f15 72
    0x10025507101200444024060b82c50040428003a4118601c003640c1c0140c0101042c0c420100d082007c964800131a03083d2070150f03001c1044800c0005603000460982e901d51540203862600c0400303c01c01d156040c400034414580b0192010600030070000308408041440c42142c0310440303c41d01c3d261248007003890b6509051040e002c1c5501041c05440e1035040010250f04414003842c25241402e00b4180790b40240c1e40f005855180c01001d01c0300072410843c40740326003c2c401089100030058042583c002c0380461280e00a8691840c04001c0054215910341c40d49884420303014005020650903403415080c05d04040d50b08039a00c038207200001c0e070315051a00c101d030101c0304000d029200092401a20f85020144a1010b451110b034000d00442c3c802c100c0f0b4010300040403402c0be205d102900d94100b03601125400380c4040304140c00c1c0f00881072215803058038550020381001c020281b549481c6021b40082ca41048000d240703004040d040d4060a1012440600e2450050300c4028280e40c0c5900301d0a5030705104041c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 671007059 1250 671005809 671005813
    0xa150612020409060b0405090d02120c03030106080a09050d0e1f140901020106030b07110607050301051011160e1b03010b07080a02150c071101021603080a1709070f0501080702 77
    0xd103402614168008030050b80c003451000070f0500f20f40c2c0c0400e0548000f15400001e5a001240c61014540c4c100004a00780703118034582424001e203028155180d100600c10342c070801403028081031200b182c1e640184041a4007400725140d46c54800409041d030b4500b030203443c0c0716840d0342c070707e80941c0c01003c44680030320b4000b039550755030404a0900114060f0041c4040e141150f50b2100d01000180702110b50314011021760300c03512040928454000e00e800d600070300c1c0c0410408213000400440d15000030402d01c0e00940d0500d0310780542504859403800400a1855040200c140400074601440e15013807030040e808590310941400f07281182119920081c030921120010420081d0041195031020300340d0720703a007881540e10310340418038134000d428001d4990101420340000c46000700801c030350406d07005c8902800a030100c900e6a10590350304121512000e0401da50010301d42d81032074420341c43e02904400c203010188140c180038207010b6840402c3d016a4011381c2e050a40800d503503024108842c840e4600d540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 671008309 1250 671007059 671007089
    0x20f060109150e190b06070b040201140d020d09050705010c080702090a0e07080102090a0e070f2f0703060b0a050d08070c05060a020d03060e011d180f0a1506 69
    0x140d0040c44450150900302450400124004070801c41c0c25010343c40c8001504544c1500c120b620003220720207540c2ca84030f401c0810240700011481c10f50503900680900f030040711036900e100804d1180c4142c0d541044107502c000354078140200030b64000d074681c42c0070b02d00721001c46071210019100d22045003c09840c0d034030107010900040c0b90011840b5846100c1c0c800100744c030b1082c440c20606d800b01076002032220b07035001704141e505400e00480380002410540c09110103400c0c210070107010465103075882c0c6d003000a840c056003c00b10342c040e05407041c0d2601400b902030700c25070101c1440d100d03078440c0821100541412805d21852510240c060241d41c00100b00806140140c0e031181d1555110b601c0444800182d581c002074150348000141c0138014403600075114103081d141d8002c088074084d40040c42d41440c1c680050120030b6080c2c444c100341c0744804400d4403403620380322401d003030200d00d0781440d852a00c100c0107a681104004910503a03268400d034168880002080c80500543e91240901000c03a03000756 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 671009559 1250 671008309 671008319
    0x5040501180504060207060e0d1205011a0a020a0221010f05061011070b04030b04061805120705070e0a1b020307021309150504050105010620060403030b1914010305010501020f0601 79
    0x142c06181c100d403003102d00519004003580c0e00c006842e0070b041d035041c094020904041341ca54204a141002414919040210f58113000ca001c132101100300b82e480c0c1e01d4401044100340d00e402084884981600100f20b1220b050300c03142480c3c1409ea90160261580d4200240904845c95038083e060140d20024104551003129010442d4406175003c501100c038811014002850601500140b002c1d501450614503286040d041050649500300000740c0c080e00c15509070004a840403072404002d01030091015603409060420514150f8103400015180e04102c4c1031010f003001c180c0c80180c8480c90300ba0b442c1e0040030220800e0b42c80f400b4400019400c0300401036028400802580040e0451f41f1482150b445103050002040403510220740469480e076481c00103215060300051000c6500414005c81d940d07801c154000d00c0d40312280500b000701031640b00c01c6045074654949010403c003410f000d0f18001c1c11035a90801029640700765180501081c50240041a107500c04604450041c4030080100800d03449c2c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 671010809 1250 671009559 671009561
    0x10030308130b0702060103020f03030304031715120606040c09032109080105070314220204050601020a020d06230609150310110309100b03073012090504050118 70
    0x103100365400d01e8011820000128070a407654001c0c10198003d0889604601c1407041c500c03080c0081500c280d100f40100400030f075200d50144070000d41e24400c84422340382c050144003c0368a06801030390101d191000802c010f040001c0b01c900c1400110b50901c100c2c1c1d03070360805544c0c04815003c0907200200400d2600341040710041c200801e1200c0d4501030901c540c0d1020107030b0031140c060380c1d100d0000ea202c4103e081c1d0212240b00302a00321580010b03080d0044001121290030031001c080082c002c54450b030016500d07030300078001440c2c840e4002e810750881d050b4601d030980042903009071115607040782400300c016450301c00151600c140c0d0094900891500e078105034500d1141c03122407903a414844c9880d0151144090b0150242c03200340019099181c0c1061403a19003000d09071600c0203001843d00f8031301895a940041ca120880d000c0b144010080c0e210460400d04400703c82c044d480c60a08540303140001c104522110f07102003a51940c50800c0d4507110170410068440a00c901c417441e40d04440003480458903 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 671012059 1250 671010809 671010811
    0x803010308030c0409110c0609011e0b0a050904140d020307030813021f031d03030705040303080714040308030103051902102d08061c0b0a1e0f1b020610030308 70
    0x11103da003019500c164000070784100c0000e001c8501c101040707092500d030041002e0340d00000c201000f4050031240041031304d45240509800044292611030305ca40e0b1ba1203005180b0060a4090400c042074541820000010020b44807540071501c039100c0c2d0310407810301c080141c51003294140e8612031075854000703003003010840303000707060764404c1201005416080741246002464820741e14081903505130119004c81070b900c1c001b21192203401c10810410213940c000101c500b0742e070b410b040c04c0c0c2603600e490f41d049074111816803840384900000a40030082c0801d210145040700d21a104036525642c00d52140d000b0300c10340324402504410300201109109000e80c024643c4c5050320b035155400c42561816080030750050508100200f180d52003400303038a0a04041111100381c190010300b5200c02555101c0c0e07100200103281c640e80c540e0300c00c82c034131070401480c1d1400c240014680d030511600400e240e80380014041d080050b40c098448200d685001030000c10a0381c07041030354a5403503a030f039899501c00b943c07003200c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 671013309 1250 671012059 671012071
    0x190b2a060402091e1501090801060807120c0e010807030c0801090309090c11120304050106050102030a08070509010e030102070c0501030507170c0a0e030f1c05040803031b04180207110d080301030803 87
    0xe0355403c03076202e484464007140300b0f00ea03800205c0c241244000000d03261403600c1c3c010080c02e03410f00c00d092004000c0010908100c5201080406502001d800d117070005102d2904a0404c60050000026404070006a07250a8a014003810440599a05400d0742200c2c0d01010080c0402d0080800700617034142d55000300a10459420b00083d660342d8000104d0500b0580030881e40018404414002800005d1082202420083c00154904501980d01a210900c000d103032400300305000502c410036034840d80019140d86406402551501074603c0d01b0502c2081a0248900103498400000d549178460841c440b050002c04181e10f45035101ca211865030750f40b25450500621641c4030610074a92402c00000000c0041c0e05e024080340180f001c0803d01e00d8140a2012003081410300051000f01400b1040760741220b502d0100d00c074503166500445215010b1503000f9141d0710602000100c141030640c006006161181c1c40036041100b900c3e0410101c1d012291018103000302c01d200510004802d2401160010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 671014559 1250 671013309 671013331
    0x10e01081c0f18050a090e010f0c0c06050601090f06051e16030809030f0417010605010f080f090a15060e1f0302130e0604030c11012c190b2a06040209 66
    0x40e8540c1302158240c2d4080c0d020081081d075802ca0307011410760038850070602544041061040751500070004041d501c808002405041c0e8810124007160f01489203e401051110b01c4d105040d6a208000740c0302c0e8212401c8119001c03a07000320300005410000860728110b044c40382000340102c940c1c408855110300207085a00c18441004007600c0c1218081c0500000d00402c1d03080b240072408184c41a0942e441640034032f040c40303154004050415001590581d1100c47c01c880c0e03098599480040c1803034100b1100000e804111089003242034040c3c0c64000400350342811040801035260720300c8402e40408141d4107030162412101d410b000611340b109040806910040011030503280c0e050242e810300805550480226144101410401140ea82d01860f12103003424001d440e05136900000d1001640d00341004122500314285600c117a40704e50b0884400e6508000081015450380256410350740075417007c096000c242c1d0380306070701c0c0c2c8024041010900805006030006841c2d0350b080c0700706500007a200220030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 671015809 1250 671014559 671014607
    0x203090618073c03031701031a0702010b040903050d0b06090604030b0c07140601140f0315090f03030a140609090c0d020103020910030903030501120b1b12010e01081c0f 74
    0x82d44811036005510418200038803061131a602d0040c0503410300e48549075900505e00010000700b0080403d40080c0b541c40307002c5644c240d50303a0004a00606034035000c5a44186404064418141d00c60040d0081801c88201080702d0301c1d0301d10400565014090001da40725900f000103000042603142529013000e00b403091182851020381c0c40000503a83c0303080c0300346d05901c00401045400c403c2e140042c42400191007103141948854003103a2030b115074034025809484d03110080382d45071008000d00100304014400b500d8403410a51840005032054001201c107050050002c10308030324041101c14026510b420003420341c65407240520040850000003641030682c00c0c04001545d4a0343d00007640c040e80039503030000c0c05050b2898064125981a0002404010301c0550800080c503d0703001560403094005c4003450342c40c00450262043d20414404040f0000c0c0c942c0001614980d603c8001d05a030003800680d0301d92280704407041c444c208942c100c800001d10072490b40401a00400a81420b20706c1c0790151440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 671017059 1250 671015809 671015879
    0xc041211012120250510060308130509060612040804050909011506020127060b15030106030f021810020a050f0c010e0d260c10020309061807 62
    0x30601c40c0100782d880240c07525614105040303048a510340f0700680198890a080c0003624561103209280800010443c2c20640141071280402a4044e050100002406015241c2c0380c005816000f8040d00351503400d007250f022841d45450030401d489840080c1102d0305103103c8005050360a68050710568202d01c00300000705040e1140348401d0311465040e0008229904007071a0b0303a2401005500c94411a4074003040710a4800c2540b2454409000700c41950300c00c8102c505029005044800b980340e4405001d40b11656050704d41000746040300d4003510100038245c807205030f540680c801c81d08003101004a4000c4040c0a250110f000c15018981d841110700c5da421982d07a01e45440b458407902c2a4990050100750001d680c0300914041940301524140544c0d00c0d80d6442c3c0c150009200d0303001e13010003542030b1a01c05180c0140c083da102c20428808584403130200c600e14070003d6200b41d4160036030740502000100ea01e2580c10000885618200003080003d00d04415810000184900e58485081c3d103071038103070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 671018309 1250 671017059 671017097
    0x804240219081501051c0209030706020c0a06050301080a020607241b030603080a081306090c0f0b070c0311040905070b0901021c0e150f1c050c04121101 67
    0x10980500c0361601e548440103100681512001411400351010f008440000c41e40d10030140c40141c001e0614038000b110402e07001001901a41f11126098414107500243c02c5a0010712850a10000d55240ca0070540701c6004880c13600c001d0040c03030301d60340c8000d41c00401030130712078005c01c101c3e0700030500f14031a00100982903903030b00c1d254520206500d88404241d00e4004a17188141a0f0070281c1c04d01304109032550360b405007139004860f2207502b80022800054001300355420100d000a92188080020b007016140c8107074001010f005140e208500c001d400b040703d0768510202c5580c1c5070801444810342c2d14554924070389000c9071910b02d4119032501e01c7c04002601c100905800361283c00d0b0380c15264184140024605a210380c0701b40806c82d50040502e00030364008000c1d4501c02c400b682c840480c0030076200214020300c141c00c0d440030b0702c503000600307001c950b01d4415a060300c0c01401c09051190340c450103c0c0c0c1e0386900541c014040e00454921510b00022101056419030403c181094a000708526003180 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 671019559 1250 671018309 671018317
    0x30c140105040b060d0201020c091015030c090b09030303060d0602042102091e360f101b0e040b09040807050c09070c120e03031b0c09010608042402 65
    0x185a91180700b070100700149a0000343d40320800380c84041c1c4400c141d4000075a034045e00c01d0311901520a01021a007050306091514029200c41000c0c0000c01c031610328014010901120344500180e19100c0108142c5001000c41c3c3c1020002802113080d40c03110400c22602c1032074014200c42c123550030400010715501c141c1c100140780e20800c20340c0898008a00501440c9000102505181d1030003405c8480700c03685150040b50002404c44681c900341c00c0e07070701101400142c404003042820a208035222001c5100050066030004c4000540e407210021907482e030b060701e04122500700010f00310b003803a00304036104502d244a058002003000c00c031100c044010500d0380500f1783e02a20121400940c41c0184402000340d03040503c002d860211561815460003804c100d280000208500c403050743d0305200e64814480c803118848002d081d00c0d80d400144190344079485072a55254428081e0048403c1103250030841d050481e015500c5121180d603a9a03134101401c180d048401d009001100c03680e101020a0703102070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 671020809 1250 671019559 671019593
    0x260706020f0c09060904081606050f06011b080301271b2003030c0702011e260c16030504030501020f0301050a090b150c120c010207030305061f0c030c 66
    0x2900070400303054001030506000c0b180c000c2c0200150020b018164490302003495000d600141d0b01622905452000862a0a525000752455080c00300b84542a545201164002d81003600c610f250002c07003c4010b4005010010068002641480104401c003200d54101c0b20440050b0210503007000c001a0700401c84c1c20802403248040f40a403113001040d034205501114440d0340c0c03c651501c8189002e03c0558902c00182840c1200002043c2c0c1021640501d103e0314081420341d01034074118400f12001000d5040480801e8402c0940c0d5a050f24482c000e4003429002e11454002d540c902150740000305d41c0c0110000b4100e0400c00c0402001010078000e00c00341240725410140c140d40c0354544420892a181a5000480c90a02c2d00030a001142c0c1c40e0041c4650304c0000b80b100740d40703450f110708540c0d003000700260811109020000784800310000c10b50081042074403d031020002915044140000819102c203044107881041c420350181500a00710120024807a2071b000b406048181e4555492500980352 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 671022059 1250 671020809 671020813
    0x5010905090c1e0d0204110c060615040f0b03041b1e0504020c03070f140d0519090602060718050409030315051c240c0c050f060103020a26070602 64
    0x140081d504041c02981d1410900301e89008010071440901c52940b81980c106070712400314065540e0454545400c030800f201d03803950383c0c81d489011580501d03403941005c841880c03141c0d0013481d80700c00c0340840e101590184c45c10640408a06814481c40c0051980301510685a440c40c0030340010b06191003a8803000500300c15005a40b08103840c5a420000d100242c020382d00c80e50042c0b02c08805a81c00101752581c03250800f41c0060380c402c640c00d100403203921104201d5504d0056403124003800303420200a0026509501c0e00307001c04810f40e80c049450100074021100160032002c00b15a90a10409070404200710654841c2511035032400010200c55103070000b01c0c00b003501d6101040c074100340711800100a180a40701400100c92100c0e45151341010f14500800c3c0c0100c12080101400303070980302c0d00300164804000c00039005040000b8002081c000c40890700c500c5240c1c50780c1c240400c081649030480303502a2020350180e0604544402c10741c0400c0e510b15440da1044082c1020090810401c0000d000c41d0300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 671023309 1250 671022059 671022061
    0x8030c120108070618150c02010c061811090f1810091401150f060c08040503010501060e150408120a260703180804060302160f120f0f0f030b0604050405010905 70
    0xe406825085c50700b507182c11503101303224100f1175400c0c0103a9503103500e43c1d43c0c0740c004e004003020b200503190f555607040b01405441c600f841d24104c10180010030603045002d00d038a402803014620420000800481d10a4040b811100c003180220030004e88170741440340340b041034603035110002071007004a0345900750984192410f00f40080c0c0c1c10400380300b4101a98098840d011600741805140b5940c920307a07228040420840482c044184060392054401034031005000780503d50f51103200415125583d41c0c00340c414844401441c0110900b00c0441c0d0803910a5005041038018108150300543c0003c90000d090014002621103151301941e02a071190000702c20030b00c6203042540000303084400c2c0075120046038607100c00c0e01002c503684038152401c5501900d805650350240c51480c203126102105e00410000305c0001d20410000e1156002c00701c4561a0390720101072013900c10032034690400c0d10282010503108a403081000d8826044192000c1000d003003140b801e0703510400310307080341d03000d034484074200fa6140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 671024559 1250 671023309 671023319
    0x503010509150d030e0301090c17120403050714060909180105010819150e0d020a0219050f0f06251707030504060318061b12020f0708030c12010807 65
    0x70a0503401c40c1e5070075094001c160301840400d1080200340d2000c0c0900c105000001c00555003504013103103642d4020351060580d556030300004e6440583c580c40c000e4a010740c007a404582e0444009442c1200c1d00440240200c1c0d00e003910341c5800d13029506266422081c00c000190305510791340006e07401000c0c00300d502203a00114010040c2192010307008411150002c4102c0c80c00125001c0354400c01c030340c00520300e59a50710000a002c001b80f03402d100d00d03207150250040d010036030342d000714144503001c0c002e4400652a2280c4440b112852066008480d0300613407400d00c00285003803540d1030a83c641c0020341800d00d071280d441d030b078044028440b0005081600d41c421490041200102c074600c107000d440c410060034100e0360340d0b014000b401540950020180c0d0707202c10b154401108502041210b411041c1040a00054100082141b428215180115000200301007039070601d8400c070390f8010b1441403c80d0070b007141a0341d22503065002400c1a0038285081c4128109400e80c480c94500a1120320004c0c100d0074a01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 671025809 1250 671024559 671024569
    0x60c0204090b070806130c0f031509050c0a02060f0f130302120d0f0e0703030c030c17210612030f0a0c02090109090308250e060d050403030c1d0a050402030c160305030105 75
    0x180030340c007042401d0401300c47d980c075080074119004940504002c91441c060400b100c0c4800c04542c03040958500300000e1055401c2468024020314100784c0c00d4688698070105240b016003019075942c0003020000000410180d82e102d10007262511038419101b21601c00301c40c0c8410398000b850b0302407a01c0d40d0b400350007038109014031840800d51801400741852070706d1a1401750200650b90405000d000c20f0358004002c1048194105c000045100d4001ea03d0b801c0080c0400c1c494284010326000011042010a4851a10540c04003010840390015850078440214450003a0040700248082c410714140781401030359115003541c0038080188001441c1107650038001c09011001d800200361500e03109400d14000710a001f0a01e4110b8541840e0f182074251001148480c0702e01c1400203074039454041840109035041e000b200c0c002c02c00e075813407400891100c48030007020030a8104403944184c0900c401c2207030b41065006958400c3d40052800d0803d0704214406a98100311401100003039030020050100d8504 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 671027059 1250 671025809 671025829
    0x11010f060e0a0f05010b0d020c0316080d060905090604080f0c1912140d0c050d09050703140f060a200703030f050f0c12040611070516150801060c0204090b070806 71
    0x11240140132079450710b15061568412500c20554241d000500043c031074008100b11402c1c01c055290042041650313003001c003026000b003080c4160403030410000095440c294050039004060340405000e641e03c4664034a0195071013032602c04442a0140035907050f54505102410002c01c40c08010514180d0320b242c022805d0503120418400c0c0312541207c6a5004900415103051032000440003907030041640b000c0d034207402111360412003035041108070010810089081401c80b440380c5801c2151141a00d030203034030381092141b10907150344900c000429403c01a0041816070070344016070400405400c5030312003660300c610410790100e0b40b1440300b90401d8005101c2c540d4032601040c21800c45041124102a46204403240300c1d400c0340109000c6000c9c440b9650003014810b445401c002d0b40e41c40b142c58081e8407140c0f107640c0c541c41c09500040018030001c0b003c0e00d500201000d90b68441c116030800e40142c03204c208044050360490b40e5440038400145e1885001d5000f402d041d00c0343c04103440c0c10001c0103682d600c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 671028309 1250 671027059 671027081
    0x5060f270a140106110a0c0303031b021207080d0b030604030504030b010e01050a0603050915011503050c12061c0503030a05220c0902070809030304090603031205010f0611010f060e0a 80
    0x442d080c21418400a01040281035032001c0c070745480c1100f0b140b103081d07241c0b44500c8400b800040d01a24000200341d05a8460140e100c01d000001c8246220303418141e81314401e210440c00340b030604010721400110540e00031300944000389000a024400c59010078a402800c03203046002c83e000050074000e00503441e2100380105080c0c0c003041503e41c14140410009a400d00c520401e0503160004241c008800b409005940c540320f414800881d82e603410304c04e018100b401800400700b850700d40881c400360490400c65001d829080b0302d0501b075450301801e101c0300c1d030060440303000e59601421006002070320078401180940360804001c500d81c1004001c0000c0410380c9454a5840281e65400c4070000d00e01e079075100c0481d4910080140c030344070a07060500f061b02c500c02d0200d500d408005400700f540f200d00d1f40100f085d43e000350380790075a8242030305041c800c590b028090700c81400d07004201040214440c420032407130306441d800081840710005031311a0590340180c000e940200404002c0003403100c00740c8180c0908030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 671029559 1250 671028309 671028311
    0x50f010506131e0911040c0203090f060a09120303050604050114010210180c15030b1503161e020a12021b100e030709060603230a05060f270a 62
    0x4180680000c0b01100d280011410058451030742a4034401c80c2c16058952000c0c10354240508103181c581800c00004100d19a4030452508017041e40141c400030030f58108640180005038044000e008120590b00b004d488603042201c111000329009000e00f02e03420029201707440c080368900340407041109442050b04074409100059107050740030303a030000c0ea03406103041b070400000303240d200038680506409855402510f800b00d41301c40050014003000000c4800c4660b07660801005811b481000800043c0549080e006003061022a01c1d008021481282031803c5003400052202c0c6400418200c01c2c0d00c48010000da0042e20509040c000703890910041d0211610180046030001880900e15410811500303016404200ba0003640d90300922846110410041c204c6420968507404000541218046e000001c2e080c0600801e40400d4416004920380e04148200394640d1031080007401001e0080c8071691091945203005003a4441e02d00c200c1c40680801c403510b1800040180d841d0301070002605050708a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 671030809 1250 671029559 671029561
    0x804120b010f050108091903032711060702010c140a0c0801050f060613140d081207141204110109090e0a061d0712030306030b070507020f01170c070813030b04050f0105 74
    0x821001c540c401c0341c074a948981f602c5d07007402801d04034000c100096000b0644c50840851440c050f0110359490042032249052900d014030700001e026481c000ea000003070100b041007190100058881e41081000d0046808803840c041703080c0c0320140840d02651010a46965407414040c0403881610360660144043d03448500e04610850b50240202a0703100f410101b41c20a01c8142d8999144030003503400c0d5070008800b58540c0f0503009102c0320700380c00f030742c0c150040740f044000d441d520b1b4064400e42d01c80b80070b40342c2203410a5a5a499900e000f051605610f810407401413400302d558865845410003e26155000301040d8030740780341c14001c5411701d00310500b011031006007122512000052000682c1c1e10f80300340051607402d070700d000ea0103048542c000500188081c410404101d070b01601030320000e0700840700502c03c10318440040d960400e102d018002022000c400107440d808110004101c2103202c1c680840c40c0c05d1010300d42030706410154104070350b40c041440c140400d10a040001154224a0000810071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 671032059 1250 671030809 671030821
    0x100912020120030109020c1203070504060206180d110f010f060f0e0c03060f030f0607171e0705180604080709060b180f18071205070e13090804120b010f050108 70
    0x2c0341c0414070548646680019415400b064103010802e00d1000d0b44050b5a160304000e503002e8028ac01c280a120014440c11000810481c0b14201c80c071224800c000250685881c0c100c800c80d08080d03825241c0c03219110304045052200d03424843c1020300318403e803000640c2410b05031145c81d40446580842c20000d5000c052050081600044036000720046806081007500c200100303040508200c40e042450160400300811160807200541c203807051160311121680d100c1d0380190032240c06801c00e126052030000042c189a02450060104044501d8100c6030420103400080d5139501c05e80000905401920080003a10018000d400240403070400d00c5081600031030fa04021240c800d0381c0c03540705580c002c0310f654041d111144101c006850a600340c0b8030360b20705140090f28200205a012031054913160008005500c1040d41d40c01800000b4001c50304906684801409404d01040543d10903400700800a1b80c01202880140c00c24401c3c00c11000541c5405038040300180190320240c1408603d00c10050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 671033309 1250 671032059 671032121
    0x7090c030c090b09030c0a14030c1c03030504030516030905030f03161704050402030112050c031605091e0f010807210308181002090a050d080f0c1009120201 69
    0x25030741c240486139140c0c1070101c00246004a040c0c40c1c1a00400540c001051800780112241408041030b821900c0e504060b0702444200b452100c140582005180d44940020b486900701e103402070b00030319103141420306a03801d00420f4200f80804801080b4a040f0803c000d0800340040c90003800144060750030b06040901c188448140d14100a02e24a020451400030101450545000c0d00e00a08215102d41c0c64007001c1800c0405040261654490741c600c106082c600016840c2e4001080c1da10b0303011986c505400d04c40d05840c0540002045031b50503600c03080714a00b280440384100310141ca4844554940080c0300d04144107900000c0d54600350802e041040a014140301c3e030324581c9071512800b66a954280306101c8149410b298101e0b001d02050041c040380c0940280c4002d0f1001c55040013015980e108004010383e0009008012070014000c2c0341030803c0340300c0640070071002501520120081401007100301c42418100b2500b07040031035004081ca981c2480390301561086060848003440211076860 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 671034559 1250 671033309 671033327
    0x518030c0a15030905010c0309050c12070611010902030f0601030c060504080c090c090a091a0a080d0507030908121905122d27031204110a030f0507090c030c 69
    0x50601052a551880b2036446680018900c0350024020440e14485000080241c285900d058401d4400e4480e450000d02d000d14544c030319000f1190052801030700e030110a4620100c0021011415560fa080110140e241841441d40c01c00c02000500000c0d811842c0c041d840c4009a0880301c00c005090001303005d240400980803c105400702e80894860ba600b01d482d842c01d104034004c242d00001c107a800040c061049400201d880c4941d80c0c3d074541c5d0f004400c0c00b40070b5083e1092040d15942d50004609011040c010301c01898014000e142c0940e1041e11921814606408a400071802c900002842c44030114441d4600c40c03c403806143c40e514002e004008281e4003c006089008480713400002074005840041d01311a182012101c98022450301e40d034410034a42a038010500c1041d240c600318201300d907001c0304030307201c05009040001d0181c559885802c4101c00d0a40055002465040701101050030684003800d07151242c00208405402c2c08604010b03551488011000d05062210764241260050648 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 671035809 1250 671034559 671034569
    0xb0103030c020607060f06150516020409060b0a14100309020325082509050f0a050912030108032a0a0212010b09090304091b08010e04050703120518030c0a 68
    0x1241d100d50380c00058594455513000600d900d1411072401c00b41030054100800f1181da02c0f606007100600107605403003034170881407078610791080c030559100145002d500c0340c40a207004803000185050800702140106005400040c040324425600200a103040c429001e1040c010b031400f03222041c00382d0b01007592810129441c01c1c800d041d88000f003481c12005c8100e68010b054007400c6808144005041c01da0b001805041e1090b040180840821511114042c1034040c552002503800c1507a10b40c03c1c3d0000900c006420101d4500805e0000f19030a4850b070080c601800b401000785540c0e00d860201c18103200d00540840c12070400d0711a003003464045c04110f540c61550196505901e103005121518018000383c16984d03070044000c420f001c00600000080e01c02e03900301301010007072042c1100c0010811501d2226010004140b1801403092040407116aa0494130480c200c0d034140d9242c2d556a800e034458540c10070001800801e0400c100005002440704c80c200c207401070031403400000040343e00c8051500903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 671037059 1250 671035809 671035817
    0x30b0a03030e031213140303130b1e0a0e0108130201090b0f0702101106010902090303090f030c0d0b22050c0423041506080102181c17030402030d05070b010303 70
    0x401241c1e500c0901007165a14800d00c0e81a917500007410300c40d5020000c0c0d003ea080074901306203041d00d80b410300008560140c18a5840001001d2804c2d240c94419031001e80c03061012a0f89850000c40d4107820400703440f2149194841e84a0200e010b000140300d900002d04a45002400384407100250340c0051140c81078a01c00c81840343d6030404004085868407640038000e401a040f941000c1d1429803000398901051107803000d44e4042e99841d100c0c0c0050f4055441010f90540003000445002e1400d002c0009450300098140e41c9550180ca001880030310402005417101c442220400c40170b451101070040d4020b21465a64085182507142d2503500c0d18207422060040350f8a00c1c00e01106a4525580c9451011a061409241c03905242110108440a48100500d41844c401185203501030080c1c4100c00c00d642c2451036490200000c0209a0414a03260b400c0354510555550100e545000d114400d0801340084a50301d05051060614003043c400c1c001040100a0028200088011200e103044a80601d8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 671038309 1250 671037059 671037077
    0x402090604090b0115020c0909071e08010213050112020406021213030b13050105010504090503191b0c050a05010801030b01090b0a1508100602060610030f06090914010c030b0a0303 79
    0x40441c00a18000308090000d41c0c1c1800001542e441241030303101c141c03005509440100303614074188a4003200039214012035400426050040030140070180c25140908100010b0f070540c1c40a40c9422680800390058a84400e0413041c411540c000324218000c2c81015411850f0900d480402911407c0b1031007900e01c0c081c400130703100c544514601e40e40700145030455008200c0341440645802a0000350400300c40c00c1d4204800001c06181900c126403030f094000000d5441d1042d05103802d43d041c0444030010050040702e0141c01e086c92a48407007010a2485442c6000c0300c036040500300042c6405990080703040208480051000820040040c0d04650389580c000c21105402c40014030542802c0d007103005e1921000e12a40001c0c0d50040c81e4a0094440d069040308040e00c60780202d071103038000c6a40d10b41001803d2030b00260148613521003001c01c030b101100051031179140c9000100b941c40c860002d843c0c41340240402c1030402020310541c4045005420100244400440400c103201103510016040c811808 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 671039559 1250 671038309 671038321
    0x207270906020705030a0801030b09071a0c15090d200309010507240203041401110f090103090803090d0f020708120a0e04050406050a06050f03100b0613030b010501030e01020a08040209 81
    0xc0c040e110340c968007030217803a20780d02003510082800400b40320690ba606030010100380048404608182680c84841010a081d4284105104250311100d00e101240c800d54208240901224400074010710003c001303403c86171502180141618442c5409045114580348a8518001c1c00400c07621074074420300304140c0744c5a40341060a48100301c66502c04115001c1d80b8603620307241060f0300951007144215200400c444000c0c01690888501d540513141c0c0000c01c00800d554802e4010281c500000d052501113440102c0e95512100741d0400e540d480703400d9200c41070701d040550f0030880f40d0404440610003081080e1801070402e5503201c46d40e800c1210000000341036851144108068070840f20041e00030301290038a40780c541c0003004101d5182e5105860a4800702c0c4614000d2005084264001d0040981c2c620b40c4014400a140c3d12050030b030b06c04410800c401502c5003003103a40005500644c4110110340c5414005016918a910141400d910403c89060110303040300c00f10360401d8040e1211f01c001e80d244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 671040809 1250 671039559 671039561
    0x5030c06070804150203040b0403050306040e1b040c0f0207061214130203010506030111120a060e130c0b04060c060519020f0301080c0a031a061507030f0207270906 72
    0x1010652290003000c040100e071542080695004901c60b01c110003041c8810305818040340420f8030002d090024440200c0e011030700c50006903400c004d0040c00050481d80541d9414a802c51060700c03025049420078243d00689002c1c0302d01da048a440b03080407800140c1f40f2800170744400c0c1502826080c0136081e050781008000c1944004000b0600107071190040c1080c0240030300c04140540120321035800d02d40014010300f418040e03c000a11841c0c5024100485850015034091006091481403039072100c00240110000e54014082c88048151104040c42c0f800c010501800360380141c1e6025038100b0042118070360055400c0d80194008030002000d80340c9000b40d0b0b20304202d01c0b41e8002e017507001007400d48006400100440c100c91021046a1002d40c02600b4440d4900032484050800d80c0514201810401b811800f19401100182190408200c800b05c00311280c220140940c00a03600f61301544020781c0420031040a007241d1543d400469a0010014191680036140c25407400d4031000d010003000341c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 671042059 1250 671040809 671040817
    0x170604200d08090307060e01090b07060b030625080402150a14030c04212301020d090c051c0b07030b13110a0f0e100f12060b041d010e070c0503 63
    0x1c0410700708890604000d041034004810440c42801034820010f92507000f0101d071a404001a124002c180c0c0c40c0c40b90300800703504010420307102d440e100c03c600700b0240d034244041403144500c142200315541c5d04000e9201c40c01c44103401107080c071800605010140e503c25200d201d6010010141c10f544400601c0100d0b4814a0b940741f2021009000c024050400141c0d4068016280740b2a640146d22000020600102c502850003a14031028807003401521032092000f4551081c4010015140c095003681002c111411610141c407240070f03c40f410700980c5410000309003140d80500b00b580100d000ba0b1682803810070060201c80505076101008030298440c0307590f007038030003c04800c20010038021601c00c106641c0090740030400510450b220340304650085008441c92400544a981c0488515030241c640c800311050400034803d035100ca116595400b80201000740218401c950f413214a0038404000c2c1c03507100b200d03010401001200501c030381004840c0507039110707009160010440c60642003e03415482 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 671043165 1106 671042059 671042123
    0x3051914180708100207031e08060613170703060b120d05030a1815060614120a021b0604030e010903031e03110a021006170604 56
    0x141210760003044040900c121040c160f02d40340f10350b192110290781352411640014024007095401949940f21000c0224100742040c881e07840505420f90081c8018010311001c140451b00143c00c0c49148020708010b100c000382e200c0d03241c011a454680354081502d501e4188202c181541c10a068501d24141c03208010303190f003c0066808131501d6002070110000b1940f81c1051301e03189981c0c0c0c6071b42c070101031040d0050216403060b07215141c140c0d080341e80020b00340710494071001c048001150071100c02801c130302c4100710720380d5500d00060020701841400550b4200040000ca0b5071140004003070f0b00850090301d400c070321900d14000440c2e07080301d540002030001d800803159007104000f481040610b031015041c04107142001503098440d03504203e94400050740414408102c0400b248142809403c8a8010340080c2d2801c0248640e6048090002020341d404004107030110030816030034002241c = true := by decide +kernel

theorem cover : BRFrame.Cov 670863309 671043165 := by
  have h0 := BRFrame.cov_init 670863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 670863309 ≤ n) (h2 : n < 671043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
