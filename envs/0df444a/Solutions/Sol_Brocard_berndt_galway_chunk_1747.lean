-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1747
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:31:51.683812+00:00
-- url     : https://prove2.me/submissions/a5fe933d-e9d8-44fd-ae88-7d7d6cb4af7a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 314028776 ≤ n < 314208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 314030026 1250 314028776 314028809
    0xf17090703050c1504050f061b0f211e040b0d050a060b0c0a02011101020c0a0c1401080709150207090e0a0b0f091002280207170c100c06090804 63
    0x480c5480a241240c1c0e028114544d14400c2c5104100f04860584800707603118441e00400c680400c801d44a580182c95240c1000c00c000c403204c050114031448440d91000441c2d04100b2040d80701010403440711340094044808200002c032300d0b04110035614070340394090314440c1481e40e40c1211102651105a441a806a568040002607000c62090300c001d031401006c05410b0203200700040c0d17550705424001a0500800c1180c44800240940450301464500c030103403400c120f080c0ca491010030b00c1c0760080020603074028501e40d400e548200400b511070740032650340000317407803400c1c803110018000079080b4000c44c060a200400e00760150300525015a010400410740180340c6c1c100b0000081c4050441942c0f200c41c88140458400000392511282d282c0c20001a80c401018400f0301d003407406020380280c00d03c84a4080f25044c1c1d004035401c0101c80c880080040c2208000074480c0d02c544c00a40c02942c8010424910180e55202c1d02d40044001d12651002642c0b03420f9495a0126400c10741c450005107280d17100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 314031276 1250 314030026 314030033
    0x1503010314010e0106050d1b090e0c09090c06040e07090e010303051b010908041a120103030903021509030d0c02031516090f050303040317070b07020d0e01110d0f17090703 75
    0x343c1c0ea007078002c5100030850541000c0010744020f01d030700005060b650380c1000030130030700b00305000d0302000304240342e0304101c90545420746903110b84a0896043c0314240d00c00000343c81e25004201d06065420080c0214981420b1544441c3c1c01400500701c54100030748410041803941c90114800e002e18000e48075951a0000d18071140d00c5c03e00171000c0b007225a4108580400000d00d00d0050b40e080d1200302038031041942c5500515246409141103610840d2000800001416000807905081d240240c0d091a42414908003800f20f52003507410701c139003584c440e05103440028801c1d885400d00c03910060540700c1c10700c039540101e0b240c10002d80d000042d5a01506494031119041154000107280d68100b480515107054000380d203038050352202a0541d050004044130000c0c1500c21168441d50001d40c105143c244550021340d200b02c60010f51002c40c40d0300200040941c0900080b40f030001020000302401580100b040311140b00303982d402014845994510250380141d600c3c454400c184c80402000d42d5880d604 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 314032526 1250 314031276 314031281
    0x90f070c1b240909020306040929010e01080a0206030c07050d0f020606030109031b0203010603150212063708010e0a05100605010503010911090901061716020c0d02150301031401 78
    0x44a0038245400000442c0207542c1001080044a40340140140c4079a102400b0501920070340000a00c1191400c0100c032a1035212000301104a001046001c15607803200204420604203000c1c5101d01c3e8810490440145000390096900c0400c2c45d00c254100640341e52032615007011200d20381d010901e001071503601c4135810400e659102e03c0860083c840800e090701c016224107201c0c0451010400642062021354400350055002550f115040c4c600500300b8142e51002900490102110380320000041a000e24150314550b0803074000d58500c1d0040d4240c2010030561000714801001e440510f0705000501ca0000c1c0709280180300640058660403007186016410006507281d280340315842c1480501181c1d07845400e81c1e054800451000501d03a06031003104210b40156454141e0040302d54002140c82030b401031821091100f40340c14042d040d202c0e41d000b942d40c0e40c0c800c1c24480040e030281031084280d15101c4e22604002d800503000200441d8268400c100d03e92090300191488002000312189054092 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 314033776 1250 314032526 314032559
    0x30a02060a0507270509042103020f03010510030b060c07090b030304080d050a02010603150606020d0e0108060f06120711150126101b110606090f070c1b 67
    0xc080000345004000900013081d07031360f40140600103000401409103107054451001d00002020f0b105685031928040c100c447c0172050350310403031031458080c0c0c482500234000e03201740c1040d00d2500703400c1d41e00f05020700401c01e032400b80c200200f5444ad41084074944543c4001c022480641019106184c00c0481c0c48099440030605603019900400c0104090b480118a11440002c00d141040d500c0708031007803c0340075104c2900301034010024a0303003040c48030089a125604aa185030291010481e48000c06d0311304240e4403d049010030103000c0040d46514107070503102c1c410b0900500341814148010707101c40710340d001190540041103012001c22240c0808114070f0898108009030f10100d58113104c0741d48540d00203840e003080070701403013804100c40a6080c0030b122030408004000b001840004905056507144c0a131889000c00e0b500e10b0b248001d030a01142152107076001900210f00d03515018184000a540100300c9402c0003550701c180390000746207046c1d00d01901c0e40d00b030900075843c0c101048146080501d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 314035026 1250 314033776 314033791
    0x8031506040302030c040504050a0524010b070b190906060801020a17010f0e0c190207030303060b04061b030315031b090513060509070803070602040e060303070c090b0f040e030a0206 80
    0x601c02007005a8002400d500c0b503001c181c4000c2025110b510b469807511070110345c0140207002d010221042040440740c034440446180141003100c1c1d03070303401015440c2c0c810310350701501000c03010300091000c1c40d400c002c0100106408400069010054841104903801034001c0810340e50001000c0c1c10380d950115440c403c80c000c00103503040070b5242c241c000b50050103610070a071a007542e00002500400703180c01034807444a088a0105040c0c10f68410003902d40400d400110046464401e000c01d6121401c800c0d101681c40c292503413543c2e032000c102c445603d10500c100890400d610760701d030400740d100959075500003540300b2220880d9158113170084040e00b0701d280c0c2040802d2440c0104002c04100020b14102803290410000145a101c0e00e90880c1000d030544c100c40c0d950301c030015844007000b105e640104100ca514104128058641c181095100d00c540c3d4006000182c098109121083d0b6580c0f011451041c0100404c06582c1003001003800d4902c07660421f10305070004200f060302e15030103001c181e500c82803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 314036276 1250 314035026 314035039
    0x1060f0f1d04170d0e150a05010f0b03090a0618050c09100605030402191508060d0b07050c0106091a0906040b06030115050d020f04051c0c060f05090d080315 69
    0x1000300c15441c01000041000d01040008907101c02c0d00b1100310308450440e40c1d400c100344030341440340318159500c220080d00c0c40c00c824a4180003c1c80b06400341b00700390695990360f030802581d0b80b414a40e651507070400b44c00e030174540c0160440000000c1e6140320b0002c50840104403901040c0d05802e1850815503a80482030041c584402000b0282142644801c1601c0d8036090440d00c1e603c035400803d031184030740d541180a2a140b04004a50000700c1030394000200410381d1490801d81d6001c052000403a55080b00806103c40707000417825850085003c2c03c2d03401c3d114000003d203140e6440c580340580b02ca81c0d280058594200c0607030820b90508201c40da9200800303a405000040a40011070000e00c414810010b411011000e0104076070b1140c1308507a030b1400034a000703540f40e40301040c90484940c090711615100310744404914416181840e0b00a15068000305002100c40c54003500750340d120a5298400200082000000c0a65647c1c03250803151038000c1940c02e443c2c0c90800c400e4440074a202c8042c1c3d01c0b518 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 314037526 1250 314036276 314036309
    0x1903021203011511010c0e1302190819060b070b07051603081806090a03030b0d051e0d090b0708160b0709090b0f060906070c0b0d0203060406150c0204150801060f0f 72
    0x640107c0c03c8185900c0030380740d0311a82c4290044c8600240140d03818400800c0103107d000c2c40d200e500c224098024401801d1480e00b00c042a6119011240c00d803141c1010608240201004108400c003c0f035801322441c00c2c15460701e5107410604800000b9414110040341ca03070014401c3c00207407589010184461840205804e0a041c009036658051059000b000c050300c03080810340c1070302c0704d6102820140e071010490f8051050082c0103510b800e4803400d10240c3d48103140005554502c90748000040700c4e4111141803820782e0350344540406a2000d40701c18148c03c01c04242a00148500c0b112901c652015038401070f90a0410641c0003d0fa018441d566116107401b5500d24482e07901c000c01c40c1d411000c21500c3c269558290b28016212440030303800540307143c1001c20000c0605203250000d40c0703d10303c21a0100045916940c28845071901001c840c800a41018183c8005050980c414000d07030701e2020251300301a035a1035480e802e41c0d007541c10812448920050401207107403c240d490026003141150210100c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 314038776 1250 314037526 314037551
    0xa14090609060a06060c02090603101812030b0a120204021209100c0801080d080a0e06091f02030709090203071e020f011a09071805150304020120190302120301151101 73
    0x6c9150040192182c00c0003004511144d40810032800001c4807a2030038460604081da40298159403588281c1d1413075050b00007288860300c01c0c440c00c80c01c0f4030002e060400e083e080180c102031060320b003101203030415030030040900606a50900b0030700c00c0341c120004004101c440100c5e201070f07070741203600c010601140b540103028001b00407801e400c440700645820718103951603070031040103001c8010141849000318018840010070110303c900c0d02c9540c04036000200c0c41401e1150301244001c0b00e03080005415120144200c02007074000f90b8000109151010103241030041c10304030200720028400169020010700d0060417030030300500c458164558225020107404102041602000518841c20844210b8001c00301e8590311503420050000540054110440c0320700003132103030340151001d901054003c0b8000c041070401d5940441040241d0300900001d84a10140c1c1200410074070080701507000e10001d00c09002c0d503140c080c43c02028044034151102060640c040c1c03004942c413402c0101c9034108500030158 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 314040026 1250 314038776 314038787
    0x2060112050a080d05150f130b010306120b010302151201090c05131e0f03080d0e0f0a0b0a0e0105070225030f0f030f050f04030f0c1d0603012d02030a14090609060a0606 74
    0x1c4640c0d042c0c001c1803821527000102d000700040d81040c4441c0c40051440c900341b000c00b800540c140c0e4401d031050a800b01c21541c440c003650042200d81c50b000c11001005003c460195003080303400c440a42410b90400500425100e000740c401d800800c0044102c0180c0900446a00b090f0f10042100c0228040e0803030a503100c4280301d20a94000212440d15000c86100c1c04070100600180c2c03003118020f03103010000601c2c0c400d1b0340801c181e5241c1091810060b0000a501c0c040c0314030f41c018a00e58006242c411210381d54402024003501c01d55012000c41c0c0310000c003240080c000383c241070b4822001c3c031019000718903020f0403480d180c0300400e08000083c00050144000c8108650550741c022545a007030701200d1a0403021540e00350402c0d64030300c4402d0510000c601c0d20103c5180155001c5000780540f469154040e01c54100760807401c106000c80b01501440110b45500541c1c104415110214264024501003c0c9041050352101c08a0f0b2002c401c200380e00c0001d0040580000305000706100c000e04c1c040f001003a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 314041276 1250 314040026 314040049
    0xc030c01030b0f0613081f050a0509060402040914160e0c090a0909020a09020a020607030c020303100b03060a09110717040e0c0c01240e0a02030702060112050a080d05150f 75
    0x10340f00003a184200400d1001e9900040c0076000490b07413070841c0c0e0300416964005a0341d0100c10642440027054903107105e40240c5101b42c5e01c400040429548035000c0101908401c00107450210803c540c0282c0d13544240541140d0364a41a030f490001403414426240000c001844225100720a1020801a0751181801300858003401c81c04608001c250001034080d03000c070750114084a1001589018194001c0307105c910400d803a0720b0800000641d038000366204d1004440400350b98400309001c0c4408034411020f035800440180400314040e8484c15540c0c100e440c8402c0525140300003080300010042d0505050b07503c08140100c850900e4689036440b80404800b80040e0200701001c5a50790000c40c095010603019818840c440d448483c0c8075510f201d60389800d00941e501201c1500025100c48010f0080702c0c020b585950050555a01e003180071007000382c5004049840c1d0066500c0350011502c2200501035000d440d5000103a9401c0c21903404400c1200782c842c00c0d000d0380342d040018802e66241003040e00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 314042526 1250 314041276 314041279
    0x1020c03030c0c07080a0606051008070206070c060b03070605041514070b0a02070f150606030b06181f020309270415020706060b0702040e161a0705030a020c030c01030b0f 75
    0x161a80c000083d0182007500940282c0071a1095401d1402449680c1d00448122202550003000ca04580c83c002c58a02000b100c41d4400b580c07021001c550b003071f40f0400010346140d008074800500c401c0c030440080e04000d10b40c1d100030b000800110313083c410716425825032000300b0320600703202c02c1005604200110502a05c0405019542c2d440001405040982c040b0781e4002d030b00541d00528401d082c585400c0d282d0118040748015858041c020132000c0c02031041c11820710009206da404e100b0604482d200003a01c0a0f40990880540320300c00c804520440c1e040d0002041030380186403110022818040c042e15000d11008071540e9210b01000461036501030560095006004009120860b1462401910403010000d060614141001400c06160009001c410344221001c0c0b0031030309440c00040d07413140380e81004401c01a1004040060039a285110101d030306021000030305250043c1c88090841d00402201405a0001c0b0400b406a1606000800d000b03002401c003040b60040020214900100340860705 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 314043776 1250 314042526 314042551
    0x20f0d0c0909030e04090c030b060d0c051e0904051b06032521060306050c03041a0901111603081b0d02031909080a031a1815090c04050102060901020c0303 68
    0x107042c1131040541e49075015020303009125038100f07440c0141d4040741e1407005407000145000440c14501e040e02c6105480c0750401d045598040c204003c000c1d8200d0001d60081282c404d01580d001c007038a5104200b8807890186000c0c0441900611425413101e080003521445070710304204101c003040e410040c1d117040d0b04d040c1c010b030141c81341240310644010701001c0e00c42401b0884071220f5548d006003034100d442528440c90003030207103803a00340000740c0c1c1c3c1c001030310004e0036410078072815001c0b200102e69859010700010000300f0b0b80d8110380d002c6900c0c1d230300803c0c1640050414089000c18181c00c5045a904440d0100c0455402401d0325510045400703a400032000342c64000020a80442040c000550000d1405204114540070751130a19003a41c80541e00c4c1000c24200b603210008551031844141c8140b0010f051030f40d107034101c12011110039000600d152208502c8080a02c01c7d070301c0d040c1d1124403d290900840d640c5605180001e49003000050031701c8250fa004110744048420003000b526040300000101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 314045026 1250 314043776 314043791
    0xc0304030306260c0307060c030804060207170a0f080c09010f0207030209070f2c010804020d12020c01020f06042d1b05010e0105130b0d09050303040f020f0d0c09 71
    0x1200500410f82c407520f54501040d0009503409086003030310030808072050407104803140f194141615490244200780100d03580001c0f240200c2d01500c8110345c460300c540d00c010f20704000c951350405030b0686650000c0030f4910125035203004940154841c444294a41001503461514203200c0503244a40b00d03010f81040000107210103e0360080002c90095a801450311540b80f03010394000f09103481a1690000090211441c00340c0400d048169940e202c3c0b0065114422003007400056500340f2003e04102e0300100e400c12a000440c42c001e000620694855004d0103803040f15200081ca002420f9003103d4590b00703e03030148000a076020681c0808107581540c15842c44070618a4199026480c3c034006e8110071912014200c0b02c1c3c40c25224409aa200344c0759042e80c07403014401196240200d144840360b54161040a02a001034100a80744c030041ca5680890540415903406041d42c0081d03d0894801498000001c2107290078400400d5840055500e24559440c0c0d440300c4c0c0e5485041e100e000e000e543e643d8103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 314046276 1250 314045026 314045033
    0x30e0c1318080304060c081303051911030d060501020618031b010b03070f030c0906081e1f050105042003070507051921020712020609040906060303110f0111030c0304 73
    0x100e4100300760704203000039107034a40b80c14040b0203000128010710000d107001c0300140d0807020380c45a601034640c16a9030341e410f043c0316a0190050004603401842071009450705402d142c44100300400281039112000f04946140c20000782c64548090108071a410204140c0d082d170041c00030540301c40c038000070f1206049442d178100c2940101840300602d50103000303180340818010003500043c02140c0c071600d8600303d090356403050384007211030758000e46130700f41c000740c00e00c0c5190303032a54901c0c40840c0304a8040d07074008040032140450480c44450300014480e01c031001002286418402d0f1404080d08101d140c003e00c02c660203085035444001c1c0006c040c800e020907841c081c0001001280f40b02c2500c981014a000f58038100305a041d050b0303d18040080c030704e01078100940c51001c11b80c00210f82c00c0010006420215908000d2140c001f2102160410b03504c0f0b02040200d1003a0044800450113502d1340203030391481d440000e0a01c2600c401c072600a0f03051100d010281c480c075404899104504030002c503240d40300e0b0315 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 314047526 1250 314046276 314046311
    0x3031c06050a0e0711030304020108072706090807090c0c020d0602130b0d051003020306070c020105070b0c0a0210050103020f0114090a03060b0307090e0c0d1b060f030e0c13 76
    0x40185421035500e120100f041070142d031095020f45016101c1c00c0d0880c040824842c2d8070721007100c0090006500310041840700b0701034624100124603001b50005c41c400340e8175055684102c15442500000d0480100b04800141400f00034094071051000f800082f81d0307000080d03c00440c0c00c6000b801a00a01000014000940d0548810346542c100b24802d05540d030304542e0072500082d0100240510b02004245980f841c1c40b0300008903540500a8103042e40c82d20019207101c40940340503410b1000400410001899500f400d5109406400c083e50301c50700306950007450300411022070a81c642c5464014000350380c850140e00320300c032001d1038104c51070000c00c0780080e418050b074600c1a812a02c03102001c001c2024a802212010303200303030201d41034185d9911504042e502414481481e41c2c0240d8854072207420041d01c4500c159019494017100000d003d880ca58820307010b07500c190005040b04e02d501041e160716004401c81e6004580062150703603081d03000039601c104c1504062016a40c3d80b104039804241e0b29 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 314048776 1250 314047526 314047529
    0x40e0d1d300304030b070906080603070b030901143603121b13050f040902061902010e1203090d030c020d0f110d080406050a140c0313080409020a080f0603031c06 71
    0x700a581d01c0701d03564501210701d0725080d6074041c0410480d600c045106882010707a01d1060030000c0003841a2480c184611025a1010301210495500d6442080031800c900300c000c1e02071020b403464941da9007540d541000765100e1030710442d8089030303003003100141800c070020903500350184590140c2c1c1c071a12051980100290032045080415402103049208140d0303d000e00c104036181551000068208c0204120442e5405d9200a50048091005e02c40968a0808403805501c060000180c03080007490801c1c80e20b05040c007100c0d070500d8004204030001c0d809024515503110a410184100000e01d44040e4171410151032020420a0400210080500c1624070000340c00402080e80d60070310210034000d003012411142a03400508000204008140d180325000f0b50300c2c003405e03c20400b0740741c1502003035250303001409d01420b03260008815000300300c1e00001000107003102072006a840c4024103018125504c001c0c100402e05183c242008901d440200448210441e0b030085040903900540e00f010040016 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 314050026 1250 314048776 314048869
    0x1090c0905151002010203150a050d030e06091903050c01030c0f0f0210181103070305060714040506030a02030402030d0c080a200303180609010c1b0201020c040e0d1d 73
    0xf04101d00c45034041d8011030252181200b040440c1d5007890078805202c00d00e106194200c40c2c00020500809d10030250444080802000d4601d08031100d130000301c103481c49840c99040b00009000800c01c1103c2000080322481c000e003418801d162100034094003210f0405000403e001c0c1091200700351510078020610084d0308039200304104010704044904448100304122401c200102d6108207074500041c65404036a8010000c0c0300940d240c0c001151042c080c2c185000a07082c0910021490f40e8030350340614030441d80395000603101c1c40d10340101841e2000781c17408802405400c0700d118011442a00450f51281c0842c18030703144070040340c510941c181c5200d0381c02020900001c01401020703e8440340e1600c100034000700720380c0f5507200e5080c0d2900701d4001c1609140824074030304500840c04400d820323003c0c0050050040d80d503030390014004203083c0c0d19081040c0d240303070308010601200590400b102060315882c081b01002d00300e0112000c40c007030081341500c80e01184070084038052511542401d504d0304014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 314051276 1250 314050026 314050039
    0x11250603020a0e0a0807050a09140c0c0a0503030a0902010801141f0507060501030f020109061d0d02011209110307080309010c110d0c03080711090c071101020118051b010201090c090515 81
    0x30740e805d8803a1205043d0040030311898030702a0000d0031610034001c00603030340ca041d00703c0c4200ea2140403100c0841e50100220340414000c401c40080030035000e002039803003944001030201e01d819081c40014a0f80e48141c1118040c41400042c8050f01d4552541140d5007140d010044807200d01e41d0603094503e0700410354018200c9003804000310400480c1d41240c180d05100380c891300313403050b1245400d03200320b43c10380314100c440c1d4500464038403946000b4654611705070041c10000d5074076050500070015103502c1c0320251024480e21050080d2400c0c01c10a400003024a01c014508010b10400001c20000205c10080c0000b84600d02d0305515a8905941800030303039201026114641e0b803417030940c0c001d8100e03030000d40300361804c070180f44402d08001103100c0c81000b03483c401c01d24040040d41d402c3c5610310810f202d41d0441d96148059024003105500c116042c1e070284000700141c940038407500702c0400c100a04941103904086405000030b00c00700c0741030300307644400700080394170742c2c800e0715203211481f429200d95030007034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 314052526 1250 314051276 314051279
    0x30c0c0f170c0a050d11060f0601030615080702070605090a091505030703151404020f130b0406090213051c0f0510020d0911120616020f0d11250603020a0e0a 69
    0x18000840321520792061342035900c011203420040d80e9118a5241c0c03c01260410030014004440a10b20540d00c14014100001c0e51925100081020385400d440301c404598540d080c00011901007109400038a1146403103442c00e0308080c00b00f10f0303140030f502c296420941c4400502e204541803104140c0900000b50881c2c00003a0340c1d01700b00d101c460007201c02718610340c40c200020400d081043c18a602c2290043c004003802c860320018040c01e01c02810b908504141d40d00144007803a5201c0c058800103000d07501c2c0258903041c84010300703440000281c3c4a130784110304620400c003890740c844d00604203039600085407446c040fa00381802070034690310326512010307a8030020b68003050500a91224a201d40039105220495448106100c1910414003004909034060030002d08654940b103080d00c0c125485206441401000003107080c07400c18841c43c52400b0030710404039090110400c00043c030108025590b003420b1684021501d4541407084d020f100105600040c14070b5605020702e1400b110708a0181401c00e24a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 314053776 1250 314052526 314052547
    0x8030a0801030201080109050403170c07021809100203220215040b04090e0c0d080307031103040b1501090303051207030902060333010e040e0c030601060503090706030c0c0f17 77
    0x2003400740030803804201d00d0000031810000911584d8401d5606484080401c280c400c1050950310004000e80130070001000081c0040c4c44800d000d1a8440e41d00c1071014090900c80240780c2005203ca581c588007600c18810001c0341005140d1440d2103c03070710320103000205014008640d8460703507640504011000000c00003609039007000288210b43c800d50702082034042c154a0302e6103d545902c00a60302c20780140802c000700c1e01c910029900704072203040000341081701101d142e040d500110b409903010100c00082103e00c46901c00074030580c11707091900c80d03481811650f000d441c1e4040e400355080c5a41c41c000009007014020ba000b8001d0030340040a03070351240b40c0b20030f07075094540104011211104a1710040b001b0160040310340701000790140c440c00f040c5119102440003c021a01000e01b807882104c84034a810b031410300005000c1d051590300c881d501d00e043c0b85040c0c6014000d038042401c25103030031503110b1459444211040c8460b48007408206800326410200c08941c058801c130800c2c0c09000030b94103101d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 314055026 1250 314053776 314053787
    0x1c0804080615030c0f2404050418020301050906010501081812030108010b01020f010b010e04051306110a030b010804120e01020c130906060f031a07270501110615120708030a 76
    0x42d0701107045804400207941846224a00341d81e07565044060181c01251141001d010750b070343d07006100c881500b400d540d04000b46c1920100030f00d2400000813000700600b07500b428044d403a40550f04e030b0000d100759450100000e05540c00141680c880042c0081c400c151002c080c0000a4607100f0500c1080e2656101e14245009080751805240507100c0c0200c1b038114a01c0c180180303490500161201000c2d2841e02042c08041c1c140102500140b03020405144005181480703204926510314a10036154011218041c089404443d00c2c9414441c2c0d103030421000a0044140c1c811059251801c00c1080052100503840e0242c05460240d01230902d00c0a00900081030f1b005074643d9001e0242401555590002110360206034040a0720380580e054440c6401c00711003403c144c218100d885c20300b03013104643d0301d401045181162448404403c1d4003080043d0346e80402440c0a034030013280903002d6820b152030219101c0c50102a02d42c0a501e032141040c01ca6001801600020250002035941c1c0f4040075800509 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 314056276 1250 314055026 314055061
    0x4030b100504050a05150d030306150818011802040b0f030a120201060504020301031a040309120f1104021810050405030f011508030c06070507080c01020c28021c08040806 75
    0x620f141000041c800c0c4001d004080c0034a804000841100400c1414042100c0c590801942895114440040c05c642e0520504000c1c64480c0d99018241c104071010040803408460518001ea0502c900804080440030401d01d034298112800207011308801c000c1540d0680d00e85101c2d515010718a85d038024081800303131141c41840c80354020885140c84000700f00c2207010a000240810018000c50148206184032154115000303003401c11105ea962606400122030304c0408681d010407450390402005500303c488044c15008840235424110076a0300490b440c03030720a40e990700c2a0b0503005081740203401001100d014100140965071420040ca00d030300d0203005c84804010300240b8001001488420120a0b55804040e241c05406240c13100c4004560540226000b9655014200108102c54009200804e01001c200014004d0b980b05204800c2d00030366440c82408856440d400d40030010b030780d0641c0120b200618051118010b000a080008040c0140d4224102c03520a22092214240c05c0480101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 314057526 1250 314056276 314056279
    0x1090308090a08040b180d030e030d03020708091e190302120619050c09060c1501050a1d0a090f03020714040c080f041a0703020927190204030b1005 65
    0x5040c0c1c842030340081d51000304040241554030180004d01692a1400c0184103501c00c0c3d9a018600d00e040d070000a0311100301003402c5000c60041c0303200c5001070800384503a2490340c00a082c2142403000da51600261842a50000745c801c85620701c80038081001080d0917881100003070700c15082c01c5089881c1c07442000840c001a803107850250341c100506500060301030700c114507611410000a138222010300103410081c1c4132024260381404020441c0d120f1002412503030744480020419080ca41d0100c120880040c0c2020740140322221050040d00c50030f080080d5072440c03034140a141982c5281d440f074000e1079070000c02044d441022600b0404e01d41d00061070000e840d81440340700700c3d9880e020200000c032841c1408a4003c540b44100041d42e48100800c100c0e80f0901540c00046404800707070307005031102d0003254454003103507000ca900a41c508050102c154400544a4041090842c0e6540103d00c041c00406040c0c0002484860070201c0800ea01585c0040d90702601109250806007200c0d400b04c0707064001c09 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 314058776 1250 314057526 314057537
    0x52817090606100809070503100212240d05010609060803070203060a150603050411030601300b0406050711030d06030b060603040f120212040e07030b1f230c010903 72
    0x2030340c8520042019070040e000280803468280c02d00c0c03420341d901c8000401029440c01800000581e50300e0038450340040100c000ba005070f5031503980000c1c03000b0080c082c10105648150480d40d0750000d1b00200c030160b450004490540b00a03885142c034078050009074000c1c1100c1d909280c000951040e000015000d907620840130365426a07102d030540b078100ca0346010301c144142800c00041000c613029030301464204d40581c9060041810100c0808e291500c2a88046e040040142c4119150084004d840300d085400c02c102c00b45541c4551141848242c000e1700181c0300c0c030360704d0f004203040c18000d160340380d2504002c00c156501d44003921816001044144006d03142952681c0005040740f07071103402c0301c1c4140d901000454140003162201501040c149000900703521038030100010360410b65000e000282002e07040e46080d0f140190000301907c404000c01401402c40c0304003500c5004940003051350304003542c41d00c1d4030b00d180462441291030001c800c00511100000900d8158814103410804049010381c60700b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 314060026 1250 314058776 314058781
    0xf02160818060313081606021b0111090303040b0c07080703111c02091618090b0a081c03020f040512030717040b0702010302070203031e0409060f0e0106052817 70
    0x5001443c0700881e41000b002000c0c0c060307a0001000030004e441026042480d00d0b401800c103030380d1441240d021b01020f5806101c40350f1944c151b040c090054070f51800e80071500710704001d000d9000c00e65038004c0d4020241143e1012a10030400141000ba95000304004030031580b44aa903400c100315540c0845072014051a5100e691484140c10481514000c1d42d014101c21a255036880006040c20f1010400f0b508001742c11810f120612030b07910500c0302400f11581c0000da00010802000421543c0764804441a0802d000003c0b0380b0305500f051440c20304007410050390312504003907409401d21898000c0c0d90b2102c03622501c5607184034000080c0404034400c0300c280806007140e1489035010300a501c180d1601010802c28540154841c0e00980720f40f40c13014085030304115816008803103101201040c0c04403004007190400ca20f10203400f0307c03002001e4030b859002855051100030303103980c0e00c14045d010522600040c08010a150000384001d0003084002010410180840003000c00ca0401222490032086a02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 314061276 1250 314060026 314060029
    0x6010207240e040f0f14160c0f06020a0f020c010c080306041e090602190503010f140d060c0203090f0604050f0f120f06100801090203070302040f02160818 68
    0x54003800d0340c0c00d01c801e10756120044030780052541245840801042031010035120180c6540c020910104899031022072400d20504141044950441300f43c0d004481c1c04050102520700d440c104286090765141120204e006824520f2240300720f1032006064920002d04c052070b442c0e2008503414440010303401c1d80d801443d5480112441c00e80b0b0080a04044c004102140640c07401d90710054044510160503550150390315800c800320790041d001520203517000103981c2d802d485082c1c0d101c10b15403e282032403800c0d5410410b0b14400042140281c122414184040884660b9883c00715100d0341d034070a00501c94050091002912030b008a0607003401a052154850010f180910035201502d4003e04000c0600422004000404000d804201c1d0030045072100c03081244401e00520810486010040007541440204030702d8811041d4080e0350140d2402c048900144d40c003050070300c1241d404481c0802d101c80b107241480001c1c4920524404d890002c294031108001c540d201038450681350300c03200e04201d6040070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 314062526 1250 314061276 314061283
    0x3070b180d021209030f07080312060d050d0e010309050607090501090515030604021b07080a02010909050f043806100e03030d230103030503041101020304080a0f0615060c0b060102 79
    0x340c0060250300801040f40880079440042c000c40240142221015022032000a08001e21508007000c02c0d000050700490b042d03109446a500b010050701c5c107405281c11070701d801e0b0316071780388043c210300b048460303003c40700160710940200b15601e4100c000d46050b801e000138041e0401ca0940702d822701045160000040a14140c09684840034150b0b140c8d42c91680c0c0e0b4800c02000351300074808200c040104050156502200304107007400741100b6401404107982c580009030006502e40c0c049000c85003080700b00000005a6844c4c01d030040c1c0e1014650450043d140981102d070080030b19448031081c0d80d1514240c20a20040f1080d0240400b5181c0351410915014215080ca402c0003440ba0581d00c2003044903000d01b610b900140410780316100310a010407030001e00c01c003441e0080c0d005600052000c010301003232040041c528114200240020340c40c1c1483c00d01c2c1203488004011001d0071105050800c18240501900882131030080798018a2009848420141031026034080c00d40d03c840c80200000c05550000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 314063776 1250 314062526 314062543
    0x2101103070207080607121508030307050c0c060f0703050711042c0114010627090506030f0d020601140d060e03070c06030b090a1a12030c010c020a0b04060207031103070b18 76
    0x81d51039001d151480140348019001c441c0c141c00c0c8c048a0f1000000f1143c4042c0301450244c00d8559450b1703a1060f0110f200c0b45028060981e0f00c1c4984400c014001c2000c103900c045550740da0345410f1490b00e903500b1381400e100f03200c042c1c01300359040390422650b1981800d0154401a100041174034219141d42042441401c071b4841c88414584042c20307000620516004074004038002c400c101913040c20300000c08948450584641c40341e19025298003d020319860180030203281e40c0900c0c1e004092100d038030b5900075942c03541031159050200310700008165a403620080e56039555002241804040c810500c0c542d23407680040400c0c1d841d05002c50021455900c00e015a05842c88020090249515428101c0340100381210b280c0c1c050220400301e21b1296240d82d01c0070344031500414040c42d1a000503400c41350944000b035001c0811504044410380002e502d003001c2139046034100b500181c0702c034114642a1005044d0810603080c1384404181c3d007041011080c41c03544100034900303140c125150840d00c0d40b551000035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 314065026 1250 314063776 314063791
    0x18150c0912080f0c0109050601030308130302060c03070e0405090a03140f03040308060d02270703062114060114030d090b030a050907050d03030e0c010f020a0b07021011030702070806 80
    0x78151084042601d08001d04071032034059818034540010509590b00311744122134100c0341c0350030034401001496000b0741b89a611015241004030000c0e502d07a0000d451310002003010800500200c0031402803441201400c1035a00050010041414641c2d50f0558400035801c085000828550040f96004000c00c10390b0600c141d4105098295121941c084c0c0d010728004060940010011200b000944d07a420100c00d130041c2a90000001c1d140142100d15004000a094105241c00e142003004121409180c482c4d6640040c20040300c1d80c0e42130701d003c00a4800e507040c0c1603040d00c00c900011031034070320750305520307848580c110101c6541d15050701044d202015903200ba150310344028800255052503980016900901100566442079100e80c0001c1d031501c5064800d4001a5035140d01160300e41c002c101d20080c860090920040010741c2c050029501c2400c11402096600c1040200d608140200149800c049480bc002d00550303d004141c140b0079002242d000d801480303500800100120080f803180d0040c680d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 314066276 1250 314065026 314065049
    0x714030c27130807060207060b010906020703030c06020c160f0801060f180b060d020c100b0319080d02040303030b010305060907081501090305060426030903190318150c09 75
    0x505801c070325203001c4020505900d0042c0308000b203001074010b1004041140c0f2620300140c5030019400c00604803001080c00905200d40c40005000d001d40018611044139850b250922a403100782c500f03240603004c2e004038111507200c3c060720151031851008180307054034003084030070401c1035451071401d0a8860341e01c12200c5803100e001d401e10030409018600000303501c003244042010b990050214426920003039504800590200741c42482481c18440c041011002070000d00010380c803c0e000948030701200c0c0b154214014a1031a40c010808201c003a980c1c2d5240c030725000c64480f42c0d03909000d0040c081401c0e10398002840c0c000060340c80d14244e6405806401c003983c0d841c3e0341d6641c941c801d0009050003002c90b414810400300000010300104011446203203d4241380080001e101880c0c924801d82a0240410034070034410801020b10000030b40d0244030a1021702542429030342d00940003001d160308281708000c00c0344498400d002d0107010f4403540500c2d820003044040e81035070301200e094445000301041d050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 314067526 1250 314066276 314066329
    0x1606050a030f0e0607050a0e030c0307090c18030804030b1e150a0e04080d0e070b0306060918070201090b011a09130221042f0108090f0714030c 63
    0x703210707a22100004240000004191003070410191a201c070450740e07a40007031400142000410b510050080204200750018440c40440100103900e42d036190080300d140f40ea5503032103805800d1050110350000303c0384100c50b03081c40740c8a0801d50300d540d01901050700d4034098900464800070703404050012071221010060760396203441049101e00a04420402d40c460700070000450180f910b00d01050207144a500d0f001e680d4041000010246c0302c0842203c802d542065000700580140386003165030000c4215102ea986421050000754a500760031070051000c0611401c0059241d0158445503403503004130341c00452aa6900206001010b0700ca081c800265004d109590850408c110f060465500078071000d41421015004861803100c10240f00f4141c0c14001c007803209001d240f20380c03080c186143c403e2035a60383d00c110043d0f20300c104180852904010b11000010b800040038003054105075800c90a0ba0400ea54405e070241080c0969079035a80700e07025980282e8101d02d0000906910000d010030101e4440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 314068776 1250 314067526 314067547
    0x5190201020a0b0613060f08010e010203160804061103041101020615030705090a020c0a0305130b0702010c15060305011e0506100c0305180a0f08060f0408031b070b070305010503160605 81
    0xc3c10040c020036045501c0a210b40d60403035103805644c01034004e11a10780c030280c1c9070002c16400c0d01c0c1001e1410586900c1041032002e50000d00070f45003c12003440c10050b09503103592404400400b8941b82d01075284401000344000c1000071110741900400903421200c098945500d080d403181d80100d480780c2d150f400140208100e0610310703502d0b135124491071001070910795007504480c02c09800c030208900180c0f00040d0012a0040ba01058015000342001941030004550000e01301d039181d00d402400e182552540b41440e05081d811400195600000a000e8984482030b425041035190700003d01072410400010201e09103070008102152656862812121027602c054581fa0302c11034812001d485403d420344c42c6500d40c1c00320040200302048a5508440c54000b4450429001804405407480c0500910020035849820b485d004030342d64104071403510640c41c4a0a4920071300380001c060f511680200018541c05901150481d40c09a0548a07400176004000c201540c6600481010507014010030241 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 314070026 1250 314068776 314068793
    0xb030105041109100203030105011404050306040609020d0215040f08060c07032d0216120c15020109021507051203160e06160507080115060504090b06070b01090905190201020a 77
    0x82c0b51149100520b0016020046020704030700141043c0076a1001004000950340402c004603e502d495960ba4101030814000907100c0d88090400b40c03201f03440712014400e55a075080f04c0150300f82d00900001518005450b540c1c056007051041c80b03221121110002501070010450310320403040075206610b001c180360f80503a01900041102041c900c0881048215910355103d034034244034458000348249120004210108134064005054001c034480c16503000801c041c000105a4500920713030f00b480b00090a04a00411409801075401070821014035101e1041c5001030000c20b01440a4840c1000c020307005140522041d9007588080c1c8010070407280302032045000e030009003402400c003440d03c400b01c4241500e601140b00b00f580c49030000c244c208110b032003d104501341c5c0d440c124040c5906616203000a0300740d0145106851715591110700d0100380f038ad0b0b58000c0b550f51542c0413844a643e541c461030004028280000100d41c20b20444e4102030f0050362981d10380c107905a0507801031032141c020b03999032101c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 314071276 1250 314070026 314070041
    0x1c0e12030405190e010602061009060503031b101104050f04110f0702040b042a0f0f030e0a05150106020709140105060903280201090f240509090403270b03010504 71
    0xc00f03110b5240042407003002c1180343c6009011650041c110750828851141c140e801651180804620b0500200440e032008019114501d400401d0080b07103001c0d40c0c45860406c1c1c1018520123100345480c1c2e10110b039900c40000740003600c43c00c0e607403040c20005105c144070488800a01c0c03170800c4041131000301c0030350395000000d03e4030b184003400104030181201c01107020703032f41c07248140030481d0044a1074900000c1d400c11904503508452030304e68204510103d001c1c3c407019001c140c560400d602c440745882112000c01003502003580c0241203807a016821802d078140100280203c10041c003a025000803025054024003160b05980300d00390103542d2a040800c6401e40c0040c400c15010700420761452100011940d00c038035642441100905040150b00c001456994a0b400850749c02e02c1c10341c828403422480740b001032800307850071180741c4003210201010354040c020808001d901450344002c100816510154800941c00051481001c19607440c69100021030140a8102c0c0c440040c001009985404d800c00744 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 314072526 1250 314071276 314071309
    0x51507050a021905090601080f2205070b0a121512052514030f060f0405121306080903070210050a050903010f0b09060604080a030e121c0e12030405 65
    0x2100304001d94086510308400d04143c01d05411800c03400c0125080521070f0a90001013444d15040c4c6203405141c64000c010f01500b50403e0424582c181c2c044100b2402030b01480f40c1d005000c40b4a51903031418024110343c44010b000001032524440d1482d1825140a0404410007510f91084a9400d04210707901c0b8121a030390680d11489048031224140b00c2e081e01c02c0c10020f2240c40407001e0503050210550b0540c559002030f50003984045920718a100011503c260480615505243c807600d5904005242c48c245141d140342c0d0781c0c80055103055402c4130031081c0c0308a800d030381c0b540340d915a651190903490b80110480650040c0002d400701c3c140c1e500c100d00800b000c18190800e182084034400c0400d0840760b80c0701c11004603607620710681c0454075000410942c0210200c44403458207042c52040c40d1030388842100241842a07212140702e1540e1810490701e00310740300d041110444003a40401c88241c0c0e2520b606007011030240c400c01d00140c10080103040400755000025407800b4036240501c04a00d01ca19a40c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 314073776 1250 314072526 314072533
    0x1808030123040213031b0b0d020c0a080a020604020901061115070203210118051303050901260f070201050106091a0d141e010f0603020c0114091f050105150705 70
    0x24840d03682c52000e0824015540d221840305030652501c2d00607550324407a000d0340c10109450421a800703200c4200c0d4086820007001585a4a00e81480d81c40d00e108110000c5c80000080f84001c0000d90002e03203144214022a011105641e0325982a242c005d031202c107910703c0380c2005100c0c030046080060b206801c0781c480c3c41200d1a054980044042d642040300e0f00045090074007004210035005003000d80c0e8154040700d020065800c001d000d5501600d0700300002002d00901161003485680102c0340045482a04194407400c100469469004004115400030600d0651000300c2d080c540705201c1e181c1031364003a0712054045400e150703400550340c505100140105000300642c2540021502540007648148a02603050303091003100d00d0480c00e041440c2210705c1414400404c05a4012400b00048580702e040c0180d07135131110282140500b180c15409500d4258940038024070341000030b02c01c83c2d0850943c4500c540d408030f4030300000a0703e801780f0030107501500040400c044d44410500400c0402d1191044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 314075026 1250 314073776 314073839
    0xc020f120f0307050c060c2121041511220306020a09170c01021908070f0507090c0302070c0e061f030501051f0c140a02091918080301 59
    0x10300e01d42090808505825040401e01a041060030880b09550180c11180f05013080500c54940c1e503510450502d07000c61810f060300c42d03103e0088010850705403110107429400f8450782c00d94020210202502d00b155800520007039610109094441e081c3e0140b001000c0c030b403400c5103d85038240c01401c122103013170001c840d4000000003c2c0c4944001c107409852910b80b40f04c2e0038900b0100456880d400b40c6d003801c182d0001d10b207040d01c0e0f81c3d020071181c02400c03c00c0040d5480842c14140700d40c4a0003111030050003010710b13140044c04d0003c00030300082103480b03009050040c2858000c0440c00e81c051404010824180e0369000d02c4030354001c42c04290b012001901c41c40141c1070308015044a1407400c00d401002c26981c41c010b00c8241071140448100040c0e41644204a00f120381c401003013480f0702e1802416102104102100018090007002c9181e50010301100c03844c20101d0540803410f0780e140c49421a01c0c070700b03155260414208030a0082203500700354001d0850303280070080646104003c0000004070000c01d035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 314076276 1250 314075026 314075059
    0x12050417030601121b02160b03040602180d0c0e0703020915070201020a0506070905010f0c120c02061e0409050907081e011b02060f0f0c04180b06161203020a0c020f 72
    0xc01e800b50a40000100401d018010040e090030302a0007d001c0c0e88138140403d10045500700700701c9420541c0b021006940e0b03030f80c00000402804210b4041c0e075114644c10001024880a14064000c3d111040e2a004040d12148000d504a00c10003a409401010540c9099144040030018044c01d82c0180162481200355035541801d0900858011000c1021208144001e580c800d09202c2d402000303042004035014661240b020062400c05198204250020140c00b1521440e00341e07991503d0248001d10f01c1080070303000310700981090090416280c900800106442c1c40000c403d001c030f90714040504404c00d0580c1c040026149540c000c40c0c01c0b992140c0c0c103070081c112550107690203000f66602900d1a8204160810701006029052a004004190500c030012505100301d40880700d404580c07003d9444500e9550000d0300c0f0352524154403903004036500701030040c4400d1844040c2c0c41204191702000d015a030540403406080d48500010749a0b0094000504203040180064a80184181c10700101000b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 314077526 1250 314076276 314076281
    0x180302061c06050103021213110301020408010e101b052101121b031212110f0304120c0302030d1d0706030e0f010b0f01200102191205041703060112 65
    0x503091500d0344511118280c01c0c5640304100c058442481c2c20b6241401c08075079105c2c40070001e06004541c03201c21501c04104220402410b48004000d030082d5120380c1d464028500a015882d03c001081c0200100c10740520340c507108400b10320782c00042081e03204103800001c0380e45800007280c03031604100e004080784020383c841c0da200d8001c1c2012041c104840c0d40a203000c1c9401129110426481c9500c05010320029080d0440424011518a04040c0d844000c88000001d0030601d003040c01520320020f0000b80e541d54103c002e500c2607004103000d403d070003190304c4111410f55080354040c006800c14408812a000c042d00328454880c200c5102d01910a2007407207150805c0100d074001c03004646d81c2e400c1e001c2c2c0c1d50b400388810038141141d00001c001ca01c050f100802c950b407006e80001810845641c5400a0010300385c022a0a000707034038002151036200d0301c20b07140b024041c88407840c404101d07409515140050345001e0144030301e0b80325a090030210030303182030f03940c8540016000a040c007190406210b0903e41a1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 314078776 1250 314077526 314077537
    0x9050604020f06070f0210020a150501050f01090b09193c0e0103060f02070b040804050a0e16030c030209100e180f040305130308030c0316020105011518030206 70
    0x1140a09810300341441000400c00c07401c10001e014030340501a850200b2200c0600d049601e80642c1c904540c4072621100f03e0901075048001000ca03000090380b444506015408141a110140d4081441510100055818040d98400c074551500104280041400d10003001030035030f40c61903140e686030b40d1505044401c6030310362150f040c0fa42e40890552101c01e448200030990707600303000c002c03d8841e0742401843c210258050001803c2d16856029900b503090107541160a42c0d9045555a00d081c1003e207061a000e50251051520451400307001142c184080b000b41401440541c01c90043d20151080903000340003a0307640302c000d042c5d09100c4516551034402c000d18440c1600c1e40d42210a07104041040200201ca0403041c00c101c00041c10840c0c0c070b061040f01c1070382140d00350410b59102c0c20041d54060a403003681e000281412008024030503009005000f940c040c2000320110a0741b4070440700101d0807504248141c18001d00c02110001c0418094008042c800c2c01c1d5580880d140c0e0780300d0b000b20700350b41e004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 314080026 1250 314078776 314078783
    0x7090c030b01030b04060f03080f0702040518060606160b070216120302100c020a020d050102160b090c042007140703080c06010b1e0a02010915061a0918090f0109 71
    0x40d0020401c0540e4075100707810b2680c50865003080611704090303100201b07289a00000700140c100080220107101007800781d07003020750300034001e00c000c0c50441305400c009450f40c2084d8400d442050041103040c5400401eaa00d03000035054044031412181d2035540380540d010f8000000d40c0584c8028422103801d2003807440c06003141c010104419042c518000740303001c00001803c11100e00e41643c03058176650200d1194442034044441111802e0b0390700348540240705102c0c03900700400c1a5400001002040c42e0094030507224136003507810800000c41400300f80c0c0d0784d58540c60141d0240481501c00403079201c2c090a0182d02800f0341f410307480a17062941e803034a449500305607440c0d800403c0200c480d8400700009409084240d00a41c1440c042014400d51994a0742c64481070050207c1c60b519024401d502c1500829000349802011600c4007002000401140c012140d0781d01c5040c401c044804051300490b5040040944003241e0703200350007984581141c2c054440300c2d01d40504010385921a20900a244a4900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 314081276 1250 314080026 314080031
    0x904060311031002031501050a0909050106080a0e031305060a05090a0305060a0624030c0e061216030605031b0126070f03090f031101020f1c0e060c04120507090c03 72
    0xc001c042520b00140c0400181840e4010070030814a1800d64903a41c03581c180a0a00f60340341c0100110590b108210340e004032202c1031034400000703500c1d584030000d2405200c4803070040040c40d1030310420030703140e115401108104004a40040015040400003008804c02c0f0303107010350804110100080014070103500558507540004244010388199200b42c0c1c00901212000102070402c3e24030031941001610300c128103240c3d440a0840350341e40a00c034014541003000308030725501c3c03841e103e001e90070240903102c07a0819200f03d0700d851a054024410a0140c0340000c0c000c19030485030440b19044564407000c0300d03041200d0032098261060081440030203a20301640000a0b03441d0030300740109901c408880d41c4041506015060000c981407191582915805150060b602c1210101c800c0c0a8841d00809282c03003407002030001c0e400703100701c00e1044040c1a03003a01030003814403214400b5521001078441d042c03010030401c020400d55000d071119852582c4950b09450b91150703240200790455582c4544500884e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 314082526 1250 314081276 314081303
    0x304030515100608040f0203120f0712211d010606020619150b030405070b040801060e1b040512150c25080d02130306020406111504050a0b04030509040603 68
    0x8034103080c1950311101180b5808007852520070700900c80b403406040a041410b66401b86020364070207104105401308407024141c2e40b005244240c51040d07200b940103455050220031010660380c0309211102074a00700e0761140007007a01c01c441e080014020302141d0304503a103528078000312600080c0550f038020205c0707802a26240ca0249003900030441421141e040c0c403481d1001c06850048149840e2013580e844051951301d030759440c07400900e0210b003508040101103010400050782c8005412507000da030300140d014210344c1c50f58010b680d002050600070303440d070003800c0c4030a01c210b09040481d18017a80071075080756074920099803c50030040050316010441c03e400108803828a007902440c0140b0a9200e40400b0404001d88441c815401518061040c094002a00c103001a04040d2408017030351300f0002c1150b49540d1064041d040c003800800060703240c00f540740d01135038602591071100d2189803c6405001504074030761f075080883c030700148101c0501000341305454954442d4400c080246104002d89840c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 314083776 1250 314082526 314082553
    0x20180106030203181f0914060f0718080c01050a020319201c031505030f010f06080316030f05120406091e1109040317040501200702090708060f0303040305 68
    0x2114610500301d01da02003200b05c10600b881c5040d0740394903280340b403000800032403034134003107403055030038182029503210394400c1c018410480c014a90085616444504c03d60394492210045406188104c20064000c590b01c0041340d400341005050744a15032040e04c0c98024900c03010b81141407003550040c00a80c10091113114140c0700700c041c204801980c4020688031a4002072003d00c044180d112030101034559021b004491042c0504c040a404000c2c00d540c114400903001074000c040c46285104100d0030501e002509040110171a1601707155a06e00c0351992205450607130b0403a100c1c03105c0b50308201c0b0420802c0d800503c1c000c21540120b11036180840c5106c01c6040210004081600ca0802e003800d401c4044001824590b081c41c16141c02c0c1c0304141300e030340d4504040d01e0ac111201c00701c000ca100ea810410080040641c0041c03000541c003540f0740810007001448541500400380000d41040544012900160040d0001a48000300401414502010310301007415034206070b104480d503901c01105400c0a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 314085026 1250 314083776 314083801
    0x50d02060a0c0e220b2106180a03050c1f090201170105060d05180f0604120c020105040603051b041203090b0304170304030c081215010c20180106030203 67
    0x601c0b41514000c184180c02100181d00c9102d9440c810040c0d030b82095907081080708540180e440054014403080c0008918480385031000c801c514807401d00d0040c480026811500c14070480564103042009010b103444582d4141c0d05940005000b048520942d440c03114070010041d4110b8000c11105004030b58441170b8030014102c001c216041c00300c2e0300120760041c0259111481501c540010300200030406071a407409403c3d00816125820000303004910050305026400a0080d016030f210746064501d040c0040070403100f84c1da20220090002d901004200b02ca18881d400c4140c101c0703c4480100c00c5520880c0410529030300c650700845141d40700a4040b0b045c1a04841001c000f8502010910b1551a180d078903005400392a03070201182c03090104c085818103114120640712180e009902035590881da60b05e220a4000480c2c0a49028004010a01403548502100c1d048181e000c010070781c44100d0f035080300c0b100c900c0d1401940e42145401200c10840d0320640140d90003440070380c0340180d89051251000a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 314086276 1250 314085026 314085041
    0x50304090515040e0714010f0e1003091a040f06020a03180320030403050c15070b0108030702130c020615060708040b0a020c01050a020d14070501020310140109050f1c050d02060a 78
    0x2ca0303410141c0108090030240722641b1501c0000d1030318002101c85624242e035185a4a041c0e0f030381100b8812012000700d500f40d8044040180079605070640c05240345072003d10b140c01110000d028145401c50301c80002c2040d00944030880c52030402060010104407094495500e4020a41c006840d00b000d0f940d041103d0388000c5000c81c0c014010310718050071512416582e8242c44032460249222820b07c0c004184140192520b080d404003040d525540c0d58042c0507070303c0e000034205034468400304100c400d441969200b050703410140358004e040c1b5540d4402c1c05401d1200020080c981091080003518005241c44e001003000c1c1154a00054a03405100d0000749801c1c042080c440c10b100701084071070180c0e900021015101c4070740e071400480e012035240041c0311600420400400329800801440300b1660745aa0b000c003030f0b4001004d011a18440b50004440000041c490544c100d580b9581004071410603d602d403242801d18011000c141d01244d40301481c081030f113080703040183c00075030910a400c44079001d01d15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 314087526 1250 314086276 314086301
    0x1209150d0504020f0d020d0f11100504030b07030203150d14150906091615030f0612060f020f1209010b09070f0807020d080a0e070503190218010f0e0405030409051504 73
    0xd05c440e20301e9000c24544442d8100181c030111f0f511400c4020410324005240380190050b100001c455461000500b0f15081400700b240c06241c090005102c0030310038800c0d688200802c41c022110a090041484580c0e0103400e02607450301c03d142c0500700003060421800450107650540708045180080002e420a1030240040354140c20050001030b80c00c00c00010101035400b407464048662a03203c0c0c09800600e0b403070000015071414680d0004000b88040d03c0c110009000381e000348480400311450701c08030b1080481c0c080405c5d4043c000c4080c040101782030140d022800358000104130014000040c1d0050782201c0c1a0b001640b10450748490547c0004640d8000e00743d40028505428601c03405070200000920103007410f1366911080c8401c1000704400303001001e022341641c408100c001c03503000c0726045100003a0b02505040303881c0e61031100e50240c103d04903800070030010600781c107210300482c4174a00030340309030b81b00d02c000e020105014210303119050051841a81003102040309209101c15642c2c03854010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 314088776 1250 314087526 314087539
    0xc050421020108071220030a0f0507020d12060914070f0302090102030a0c0201021006080f0f0304030c05041e060906051c241517010e060103051209150d0504020f 71
    0x40c0c0181d0b0000800c5402101c02c2c10442c02444102c0c2050000b00480c0c4001c01c5000c40d001a40c0c05001e003500c00a6019400640301804542c54600070700e01511016a5250010380c4501c01e00740c0141d00c82d041000c6008042d0001007440c0e030303030340103c10140c0c0d03c20200c115800d0b03044000e22900e0340e08400c01c021810600d041c03e50401803400c1c000703505c170f004004564003031181a089000031607100b40704480e8813846844003082881d4031002503aa0b030303582c000c031402581d04c544803096020440c004250390859500c1000240800d0034041444060001182c000250310210000820981c500e0301a090141001d04000503126140408100724183e40d110f1414009032a030040e5408034014a0b801c00940307011041c601d205000580c410801800c82000d400905090740501069030008004105010301015000303200d04c20709490341c05e444403000c0c4402030107a401010805491041d0402500010800415100d140c80e00070302c8940b1554440310742002c008d6910000c0008500c0c04101c22070104c981a14071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 314090026 1250 314088776 314088839
    0x804030e0402130803030f1b040e360d02060f06060d0c05160f0b010902040821040302090c071b27181505090c0906010f02100c0504 58
    0xd0118a040e1480501454000070b661000c0d04070003100d0b400410f5030b08200c80e0341e4601006640d0700d0000c00c1e69603451502000c00420513148402c0b060341e00341c0303408a0303804006840c1d05034002184201c3d80001740c6c0000071603160311a0248400012964001950f001e00131206044070300908010b0000c011304a011901c209000150703d95034181e401030340c001c80c8006400410f14409951501803400d91740103030486c4d801154100b155400060003078074071614214a5507600e41c104041a4007490042c01c24540c030411000c280030304210890401d420040040c146400c1e202d030089012400c00300e44495541e07034009148030401c440c00e0040c401c5400392180c582602420020f03400941010349000618500c010752040c0c04001d620390060000019140c250718405070030b46849007826a00020980d12246132a000030300c1c142c400300d040c030b0b0007200c010003c90150751404010340b13182c80c480101e0300c2184101e4118030458040707482410540015903d485450300c0c60140000b01060340d4411107411610032404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 314091276 1250 314090026 314090033
    0x302010b03060c090603100e010b07140312160908070905090f16061404180b01020f01051003081b0607180503030c07030303050619061e0815270a02090a060804 70
    0x16101308040c100d0700a503603919004060a8041038942220708051202c0700001a1148940010226980f0404c200b010885100c54455100d005100030b60042181c4000041c180d1010101642400c242c0d278100030404541b01d01010f482e043d525005441142da0752010700c500c841c400c10400c0055035000c0014100c030002e01c175854032800c000e44a0f0304180034040d0f1503440380360b0078402940c0c0a4511800c42d4083c10414802c80c038080e000c0748108038094020b80c400300131001818002e052050403802d08494807240307155609120340e8015603040f141d025180c4080344080c401400310600581169071070000401c2c88031000c44032144158400d92095201f0400100d00301e1000c5118011a501410001020342d20b000100f18410701061a0a0306241090004182c6903080f28440140300c502000d01502803110312010340e400842580c08100b55080704455080628101c6001191040c0d1078060008200a07803003520000e2805880c0d0051540d00822540050700b01003074000e0007000b0b00d1903d640340c2d00f460745 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 314092526 1250 314091276 314091301
    0x30207110613063005070801050904080403020108071215081204030c05060a0c020303121b03221104090b19110f130b070602070204060f050303090103091a0c04030302010b0306 77
    0x204020500180f04c0301c02c10f15048a10000d50740703030001c010110528a2079907143d80244821101c071004580345000200f0681000100c0c2486075034002c4080d40340500719001900c00040044c400c004018490b00c1c0100300088502503d5040305000180f0450107090295190802003c4110381d03e011106100400c00b052403090341404680d0150380c00e990300c000701c0034200c1ea0000340c010083c1d0144030010300300911001c0a45090311900d2a11290342421000c6101c034002c0c2e1006a41211b4004c246600c9000f22a1500e020713074840310301c10b802c20041d00c4096400300e03082e10302c102c00941d403040c0c80a081048454000100b000c881d22451420070010f01482282c140390701035828400c1821401150fa124400120b400b46030140c03c400300801d80b40c51061034004040c3d0710115080b0b00950500600144004940ba03411090f600004e01550520030034a0045006007960758054a286000503840c108454035107024900900800510a60391819410080d0170b480c80102600e029920283c1040441c60b01a03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 314093776 1250 314092526 314092529
    0xe0303090c15070209010e0708090a08090906040b0a060509011106090d0f021510031b03020a0911130801090218010303080f09030c1f0b3703060c030207110613 70
    0x442c0d901200100009240d0320b01d0084200094010351080000300d80150b40410702c0f072050b01c0d0796440c040b09070f40d141c080c551980301184e0001e06045050200c14554a40441141d0f400807020b0000030306520f04000042c0e203138010380d1045c0041100002c1074002940d100f03171a003030842d00400040005003003a50603180e507000040032140030004010200b0380c00f6482400022040d0404041604c05400d00001443c0401e00602c8100d54181c0d0103455080790100c004c1c00340b011a50000c0041101c00c0ca003805c802e015100504500003000300c20050340030151241002c41018000340300000a91000f50305c1440400c41000720180203801031040104000f80d0300602c0d1691189903040c050186071240443c49186002c2c140d003203581d13409064940c003100c1540d400e40f00201840c1031001d201c05d84e552010310065041a00c1d140c81243c07207410104a03886a00c25200f4031100250505200307280e03032074641c0000c0310b01e0080b4020001341c0004500c000d00031400035040e04040222540c910f40010f01c45001480d2116 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 314095026 1250 314093776 314093779
    0x20d080c0a350114040c140d02042117120604020a0e030f2b02030301050d08161113020f0702010e030f0f071509081011070212100e0303090c 62
    0x2180381200c0440000010014140c00200c0b581c0444100c000042c06209000d8040705420041900a4514060240d4a0140c841d074658a007280e04c00100c0411581c8a0b040030101ca039001c001c0014840e05020701138080c080080070002d20061f00d80391035100500400c581c0c50800d5010301c003107a0018210401035800100840d4016500d4280100c20703610682d03002e000390703418015141c8800d0058408118003d44220310455012400711402102d480500202d103442e005074003c1c001441035061081580c6841d6004010b078500309504d1034044a2680c01111048450200c1c800d40c2651900344408a682440d024040540c18401d0781c882c5500107005d9118081e041008490b10b22556841c1440420502c2c241075007070b950640d00030000c0b5583d07024688984c031800d01e00300d8041c1c00440d1041c94498243d0350580064071050f0840c0b0407141c09083d4551001c181590304010000069075001d00c4229203420b2540600b0399a07001184610450300840c403540060b40080080000504011078001d480303540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 314096276 1250 314095026 314095037
    0xf100606080a0216060c050304051015140301110c0714040c0e0d060b040203180c0406050109170c0604090621030503180c040e03070b010b1c1109150307020d080c0a 72
    0x30013201014140340c00d02010b801c2034900f601403400d04ea8808019407142e401102180c2007040f003654a202110056a4030116180071040d0502c4610103401c042858003d00500200710000d04403060f50f6150702407a55038450f580243d5042101c403640d0348d100040b5400031141000f0407906550301030551400c8584680c03083d18510112720811604e81c1c004440c162016000710340301d140c25012107e007030b828154843e50a120785030511142d4038142c010741c02500c1c0c06940301d003421841c100d10900c00541c04101448075001c0c65658101948031000608010203d07420040340083c50b00e00301c030055521140c03000d904217a0348414280801d40200c11130750009007620700f1465508a6001060509541070102a4010304255504151600000150220724020805d8030300c0e81c0d0740c941146405100f12081f0103040310140e100744c030300135046520080814004032006860894480009814000d801d06240440311001c014040322542c100401440140a07007001c01560901c00b002c880b0030301502114078100304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 314097526 1250 314096276 314096287
    0x908120a05070f03030605010905120a1b1203050702040c030c021e010608010204090b0306060d120e040e030703030603050c19050909070b0705010614100c0201030b1f020f100606080a02 81
    0x1c1c07080e42101d2405410100e01d80160190740740003409002c6a2082ca40003c10b4844d001c1114070300010344e070000c050004002e0410b0b500781e50340c11307005039118221492401d882d04000500321261072144140140b103a40d8817a6104601d1040004640000c406903040608d0b1044130700d03800d83c000490402701d456060b080c2c0100f030b0f918941a40900844e03081070115500204001a0400c03151304130548030141241030350202d03035a41040c400c083e5a46d0381c0150480302c00125012201e0301610710f15400b110040c1001c0340e0b00010042c11444c42e841800b007100000d075280020824000c0070b01410020407402c841a00581c1c1c0848540500b4000500850303120b900b40b0004901c200300304008007002030481408564a40c605401c00b14000c20b1607102e030a413101c068100001d65498070000d6240b5141140d110050810300c0c0d6001100100180c0310359540000465045055403d0b02d1800c400418000303070700030b01c20507401c51101c605110341d001003003007139904104c400d121140e000342410703601c484250001601d44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 314098776 1250 314097526 314097547
    0xf260f0124050117191e23010902030a020f0a0e03060601020f0a080c0309150406080106020307020604091e020c010603030318021012020906071406060f1c0206070c0609050a06090812 80
    0x154042400145e0a62820340c8080b0600840626548144400b12042007003032546040e0201c07224410340340029580007000144030304840d0358041e6070001c3c01c6400c018181091510390242c0c0e40d1151030140e0204000981d0103095240404c007040e84034000f0b10281030f000308000507499581d054684018822480403880030b415110400684602d81d900500030303000302000e080418190341c864040c45c400580200c001207241030002040f100031340c0e4094409032a2916002c8890014200d118a0600b12241d1403503201c1d8120b0a4000b0700100d102a10000600d2132542c90b02804a03450080240c5680e0b0300500e901001da6903000310302e9144409070034004442c1c0c848958890081c801e61107443e81c8800d01103802c405003c00040e08074001c54807041210305c07640f201c40811161003912864168885500c005480d140c0c0510315006030309034405025141840301c05d603104141d021007a0824800241f003c5810402450800c04070b00080506041180145047c42c010039100c00c202c00d50384290200018003814803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 314100026 1250 314098776 314098801
    0x30638030c0a06051e03010e060103020d0212070e030d030605031b0d05060703142505210f0402090c030c03060f0d1a06011202040f260f0124050117 65
    0x20240020003810110fa215030b006000d42c3c10a0024824034080742d52601602d0340d808007201e05031103201598801554031240118040e603c229072602c640ea4003480204111b416011005019401c191500c070b440c1c2881781d050520b07225035011100c080605003101044143c50100f81100d519007401e140075545441c62001c250081000c403030040003886440d0410403c958507900404280c1c1c1d42c400e401030ba54480300b4204213614101c42c11520700e002d062046010440c0a100180340d00200074006901e441d80b0901001521003049804d0303600d00c00a0b00410085107000140eaaa02420b40c005150841c03c00060900645c00020005400b0b0140c02015044a90740c03070502c0901241c1c021581056240181030b9045e101c541030398807501040100d0801c40e601c40950084c1c030240c1e0501c83c0c4031400c0c40c0c030300740103150080b8485800d208240d40110301c0464821081c00345850400310703200082990504840c0c56201031024410005443c40c40e02d20a12007170703a000511480c3c140e0f03514210541500e07445002002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 314101276 1250 314100026 314100043
    0x106050a060203070b01090606210605060a02070311010315030609030c1e0c080705060a03021c0c09030c05060414130b03010216031e0516030c08040f03063803 70
    0x9000d1240d180000c0d10a500000a100130340c455000c0b0040e50f43d82d881c219050307510342d000b4800442c580104c2a40003600c0c402c0040d5400c41c10706004281240d85a000c0b0382e15a006c3c10302440160407096090050028101c1140c03034119081c81c0801c0a645401d44a18080d405070100502c200e84942a5006242c4242d001c22401c580100d580391030b00600c844003440c01c05825a0407902c2d158400c6000032460000b10300b100c100c0d0340c09460f0924003440000304800030341c040c0c1e164400f103940112042e815001c180c41120343c01c1c06c4607111a0680c40c211b0914022403070035980614480c0030b041106101c0e8000400102d4010002503070002010f18207442d002c0090002c0c1c3d4005601584007150610081070005c1d550900c0c43e0207610381001c3c01030501d01c151225400854103101251041140d000d21075000312809080c07031301030314028100c0c1503103940700015903129a225040d00c0d40c036044c1c20320601c1124440c2c103000e60345a10b1420305000e170803040c441d407090540c1030840a000c1c000d0751a1010340c605005011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 314102526 1250 314101276 314101279
    0x60319090804090203091506010e04022b090c1413230f010f06080402090610020307080304050d1b11010f051c06061b030e130609051302040c090e04080309010605 71
    0xa880c0c070f4035820f6510094204440c02e80282c860042e5012031005100d07619801480c2c181e642010303040c941c0b010722002c3d40c00340d0f030f01041d0500d508076880030800403d150464103416810700455800f1603810400114483c03a00542d410f4031108111081e183e80e0a118080100e14402000c41d1444198be01100310202c0040c114010300080d07400c1100d1146080d004a05954a80200001a80d1290f104a4808008460082d000604039011500c5854500349070a1000f04a1048902d0241c29550300c90540e00b050b14200c400b0f070b0210183e090200d0304180b00542080c0f03090280c1d00f48060317075140c1c00c0035000380d0400c4506224442602000242c41107044448210000291034501380800340840000d01d0b141c0b10b068001404017042c5601425901c9907801400d800d941c4091a400802080010348613010500d4043c503551080f0015540d4401e00070a0b211700440f04456102d0859401400140c030541400402048598032003403250140940751a504141c102100e00d0b100d584040f0a0360040181c1e03005113 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 314103776 1250 314102526 314102543
    0x1030c1239050d0509030918010602120a121e09050708010c1404060509061603020c130c0203040623030103050a060b0406050f0607051c20070506031909 67
    0x42500d090300032212031001d00700030310340350204058200d14981495540950700004030200801d00a00701d807900580c1c0c1168555017602d10b4121010001144900d881982c40203a0741c0c8200100015901489900403414100802510384916000000c10421424102d030100e0b85e600c0c401c80d0200990000314015010002100300814001400c24030703501c178064403a83c900f42d82040c52141c1e43c588182c04142001c10701e425094100f5040400540d06a0400d0ba40513402150901c031f5444000180c031000d50b1041d01a40207088074410000900c03481500d224000c1d03060b03034100248d181e410340c0d000040310700311041c44c9480b0356404053f2501d02c1c2d98000112807a1000c0002000110501c240460b100400341d200342c200300302041c100c00c00d2100b83d410500c21268046101d00c1206a00c2c01c00b04010810140320340180c452400c07862070031214199268401c100010030711000d01c0c42c1c4801051502d034410055100600295160400260300c074030000740603054208400c0024410552140c02142c0e2290784003812 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 314105026 1250 314103776 314103791
    0x1f030914010618090507120f0605040f030e010212040620030c0601080d02010b100c020117070809010f0b0307030822140414040203060c0f0705010f020a020c031b01030c12 75
    0xe020b0505070280c1000301a080744184144001031159803800f56001d005441d40c545040540406804800000e031590000d01c0e00342e1001505520407244160b01c600e003054080041800c005007120b14140d169410f540c00902010b075203081c3c2c142a45d08407159860400e5002840d140004090709000741d00805500c130215a8001c00312001c00c00506840d2030750103d800b03c030f109820032800d03241300400242e007128009c0200300002d4810100c21401e540103040c0099040003400c3e0f48280d1020844050001030064818000388490a000c0d5000041d00103505102401560001075143c0b41d02e840020007940c3c0018021079140f4400e41900c540804040c0c12509203587e13600549001007034801000d1280c0d10f0024588000d1076079071941401560050010420f5985200c0400c0380d55011030300850381d0030703014406400041c0c0240142039580c000a030700076031500a0001c0103840c001e414012141f19400010fa030403980d204035041c005c0a11400d103030110700000e6580003542c594990710724172032095040044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 314106276 1250 314105026 314105063
    0x90f030303100501081608040b0601030b030a03030f050a0204030b0613090206030901050403020d140d09030201020c011a04050610020d08040c0306110310080712080d06050306010e041703061f0309 86
    0x1070b04001c0741c8003a00d540d4002d54901e052a007a401d24190b4610110b0392810100b0040703411403102a6002c43c041c14002502e00154001a02d0f10b01c001c17808178006500e840170209940320500404d500901d2243c4290b0a107404c40d85c817440c061400405403402604090511070412000d90003002079250054035007541c900b0000741e424060501140d056016109140d03800c0c058510034403100456070380e00c0c40000e0070848092059800750605c45000c1c1c0c1153740900c24011809402c1c49800345541425001c0140700744140c091206a4100621061140100c18500d00b01c054010420301d8402915140240840d95280307800034665016802c040c000c2803503d080404408018402075014502316410820342640d16a400b03656070406001305500c500f42d17800044001403480015048142d1720440100740d980d100c001007890800240d0103013a1821144052000380318102c410259907400e4582c8544ca145810f0000c0f600c4400d0000448402c164101041800d0034031035030040100303e91056140800e139400742e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 314107526 1250 314106276 314106301
    0x206130609140618191d010b0f04030f0305040e040b04020315060a050f041d03091201060303020309130f060803130603150501080405100903020106031a040314090f030303 75
    0x18480104441c0751000c28125020b281074500000c0040c032484c980703081c141d650307050513040c1000e43c0d40005d1203130004000b0b84101ca580c0000703003111500010b01d550242003039162511040c2d0003424942010440c4240c00b140c000c04031400e881d0003490001c2c10008926080b110352107142d120500e0071000005010403c884d0300f00d6540124001c0342154030b8044403070808030310104242c80711a4420700c404c04c02c1265003041042d04030740e40c03030007040002e02c0b9001c074070000d103641861661485260000910311390700d4900700a088024440c3d81000f0408581150703400f9580c0d100380e000c140d00c20b07644621744c40c1d00740c3d109400c0001030400170350062200d1961204943c3d40c1e500b10070a40040b81c0c8644102040042c4284100c200000c480c2d449149003500c1c00b001582c1d20000a401510b40340100d2080000d92a00d0f405030381510303442a0300000c0c03511710358149082402e200d26100c051036600307400ae1201180e4410f200f80a550708000301e03e6039800c030740390000300b00301100c407412901400040300b04000b460300302 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 314108776 1250 314107526 314107529
    0x9031c08010e0106110c040e0a06050a0b03161404020d0b04180213020a020703140f150a110309060417160b100f060c12032003090d0e0a061b020613 65
    0x490b540743c1e62603000c2510618541c9594901541c030401203030b00c03585015000030000640d0300f4280c400614158484006544089811000075a120403100718107040070000780c4031007001d0a4800307641904000f00b4034100514450914843c3ea0003207515045884c00340d004d040840710040c01040b01c203502100d104928420b04005900ca05d120001c0b00e02050024021100e001343e140c0e016201c06411652662840107907100c0c06102445603030392038031240c0001c02c12000183d41c20f40500300189040302c407017000c1c0d8856076454031102609100b4413042000c0018101c0c0c00c286d00080d01c4660940a007075400c1107018000d0003400c601c104011100c28041440c01c0c441c0241e040c0b103581103001d42c80b03040002032880d05c0d20500000804c1042180301088140340007034a407600500c0c011950340d82d02c64010120b07640302000303114003205c00810700132005030030400c801e1240e00d1820148407420f48200040c880349907900c110b1080c031800902604218803000320640c1441c1d0300030510b640b1a1083d40141d85200d602d0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 314110026 1250 314108776 314108789
    0x10e06040c0516031d060a0503090105090102070c050d050f07060f030b150304080304060906020403060b031006081c0905030703050703050d0201020f1c0e0f101401031709031c0801 79
    0x108680040781d540b0400881e00c0e00d64201c1815005824550313800c44440c1a116000e40855020b070703002031425901c03a0300501b070300c010326035905882e814581c101c203084400141800d0101d0384100311580000314074440d801c00711042100d20040844441c102581041c0b05460200b015028a68012907a140c10140d1400030034200c1e0740800401c284041880b86070b0751803a00010482809000040005030050300540e4040e1054001155035840c960300d01c806e82c0c000360011220a6100c028a0030780f07003001c10106081c0040d1050501010345000b40a6440340d00d20319a0074000b907940c26604d100e407030050008000400c0041c0440d003016680b42016926001180000c590a004204030061214414025541a8209190440c0c5044291203007000c0c02c5008096611515888040d4184c102d43e041c0b0031002d0340c98003540507020106c0030100083c2203c41119034442000030b20001070002c203011040300100219041e2540c2d54402c44c04001a25024600580401805200740c0711540a82d024030018101d405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 314111276 1250 314110026 314110031
    0x11010c060b1201271707150e0303010504180c090b0621270c0d020a1203030b04050603071409090a020a06030903090902191211160b0106020f07140f09010e0604 70
    0x150070301810500884000041c1045c0da15210303241001400000510210344240303203108a02003024562800c0d2021000907145035000400100b200d401c0c5030181120515050120b040b58030b015130340300c18070b69080c0d000b10007013607540d00710046040c0c80e894100c0f2880701c0000411a00c40c0c00c010340548440404840410b554040fa04104c040035510f4040c9080c058802c5000c1d020b2134095106110410031500d038240c1c0d1120055800086c640e1203882c820082901940c1c01185449041c0244020780c0ca001d441d8600950203100c0800400d6a00228061840300442c1d91804503140c0d43ca03c5490b010000c0c5011b980240c0f02c100c00104c054059124546551103511410034180e6524893300490042c49008140d1100061846032168480d9042038130b2104065030020306007241100c0e0705d01c99000400030b841b0041c031600c17200050000000c00240104050b100500c3d0f101544411980c541e01c1620031810008101c01d001982c641d1a40d44a80b01020041d0800b50703290303510403d800c80c4201c1a200e05016a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 314112526 1250 314111276 314111321
    0x11130902100807020703080c070e13050106060801050d031101020f16060b030105040804090f060b0c0d0801080316171c0603061d0303010b09030304032a090203010311010c060b1201 79
    0x1405484520f105004035009004940e01e035856040740707075101a003041d5850040110105604200d90b1a55024160000d03040c68426400d02e0020b007100d0240d04101c00f0b001410340100b00304d503141c0c010402601c4d03140c541003040f100145901c1d80640900f0180090751140451980c0040c41010340c2e80e0340e036031b00a64090000000c0c05040c0f608840c0c09542c09007400804020a010700e9660f40c100e03407400d10b40620002810355840b108039840d030b0002c0f8156002a044010000360040e0301c40415405400350074061454040c021201d01d9041c0c0c507441e270090008102d40441080e150100f010b50f44001c03425007204418000780b04c01d1700000e089501080b82c01504e0411070800100140c40d50700e49840704c002c0110300d10303420b0000e200b50036041852141c1e81840200004800101ea8000200540400c5910ba04c0748181f0726040f540b107002c83e0342114202c01c5c81403004001103909011000303105902800d19005400c0c081c140000546010a803a58004013442090142c442055000d440043c441d96802880394 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 314113776 1250 314112526 314112559
    0xc130f051c08392a090432030c010c080c031506040e01030b06120a200f12011401060804030c02100507060213061b030e210601030506010806010f0b031311130902 71
    0x31290004a83c0c000c1d1400c800140058243c0c26141f2105d201c808226003400c10203503152092640300e115402c22a0404103801003600350900130000c4101507820002c000380f80a0716240316500004180d1a00c180000d840105241c540000310b43c007401d84400c1140c3c10b903071030303052604036650b045c2c1e8218010508004031440460010940c105207690210030604407480080d14007558032054000690b10007510f828185071540c1d9520204d05071440b81c800843d02e40c06082c401c004144e0160300003414041100d0030480000c1d40b2900b42e9403140ea0459a02c40044091002220036000708180140010b00c00210b101050810301001c00072511181c0e03410381107806211301350b41002c0031803c005011803100c41420b1440e01d0228501c0c0799520b48400101741d848001100f82d40f40070b03400e0340b00703944a410100c0103010210041c007011b809407809101d004150f030b161034a608504d1200a100358260511803540c0d400304524552981e42c2800010700864140c0b0005017400c0090540c520124031808004000182c2d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 314115026 1250 314113776 314113843
    0x709060302030d0c0606080a0501090204060f0e13150c020c0f04021e0903012307091a0403030e0d020a080705030c0a0f0501080c130f051c0839 63
    0x15241d01034090003100501a1082c4c601c0180f01c1411038100e070310b804011520010401c50b20388840d00600000c0f40762145070040c00100c0d0f16070b4001244107094100c090020300b25019200c0e400c0b009000202e02e0744c00946c20b08038118003082c141c100c405400c100440c401150300240e150152903003201c1c81c880407410722080100f01e1040b140c0c40e410742210448000b10000d08400a442d0301c8030043d002140c0c202009080c2c045035001040d0f20a2170054200500c40d40725030000542c1c3c09844901c0c543e9a0450b800b5040d0950f83c0502d1100408102d040e60214a154480c0c0c511030740110b42c080c02e000000d5440b03150594868015004c2c040c064420306c20048080e20f0103031409412100c07081c40c1030013a1030400380111128000103284000402042003c201403d4102041c0c0c0c0040c810000059112070070501003021060802e43d030002c83c8400044454045440c000840354070343c2000b110000c1d0b80c4101c800c40e81803021040c0c0c0c01d050341c0c0000040c08804680c0400c0811400683c5040081d8400b00840400b14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 314116276 1250 314115026 314115029
    0x3120807080c160506040812010f0803070f050c10020f0c010804120c1e0b150103150e09100203010b0409050903040b041202010e120a0510022b060810020309070906 72
    0x1440340c001190b85000ea0794010500c600d59240c207019910390f940c480504d8001d0580d402c54201c580000c4841049507011001c9000d03000792440e07802c1662070248103a580e0700030090040d12415980c4000c00c00c0000c1080001c03070360032002c0c01c06490b1201910002e51218014a0a1406c0e40210341d00b1303203025845022002d03c03a82d40b241c0304032951a503075101100e9030349a000307045038554192001300d81c0303441d80385107002011031113082c1c9031b00c3e1490460100c00404210500c0c8078149401c04d114551990001c901d00c5044e14a441c04483d15640c64240a501d090041e000d6040e00610000020940d414420020300541c0c1c0041c00501080c0c0700c0300b084565030310a91142000b0480248024001944c00180f141c44807801494000030000f072500009548111100405c80340d03078092031404007040b2040c8055101001451030441c2000320621103900d508001440104401c11070400c0c6060502d02ca0340000c001d440044115100c689104481200943c030a07600300040d4031444c100014200514001c0c6c0c070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 314117526 1250 314116276 314116291
    0x7081003020310050703060f0801020703090e01031a060a1d01050307150903080a09031505071202031e0a090c08060708011a0f16080c0d03110903120304030905090403050301031208 79
    0x19840d0030081c81d83d03000740070241090041580700c100000b81ca0002e50300c0f00000e01110800103a45070250318014000482d01d0340011020034050b001080030407858040c00c0850200c10020141e56560311001580b4842690403102d104103c08511041c1d281c184408581a10025400c81358070300e40760807480001d005415600c000003030000030305000041c40c4030090300038040c40b0b0600020b8607860b5a501843e0400d4030003010246030360344042020842e40066010b01c460b02d0100114510704082200400301100c1e40a01d09a40c01040d02041c2c2d80c039841c4d40301c000300c1904132a1042495441e40070482d00c0d940159a901c0000747e9071000031416141d20980c160956100c1e601091620b807144c0010203242e0400d01c0c851782420150410030021441c0400100302d0541c8000117030110b201d400754094110380412400132400703141403103040c0068a0001e0750b1304c01c40031180b008503100d54a0f0b04d000c0700c418000b500000d42107800003003400201508103004d90305a9100f15090034040448203c00c4441a80c2110701c417 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 314118776 1250 314117526 314117533
    0x40e010b030c100e0324070f05090105090f04020706050108060f070f08150a030804050a08191e15050105010305060402120606030c131401141e09060403060c08070810030203 76
    0x2452840c101403d01c181401c1c6050080d10500c0f0000001d04081a003904001c1d030541003500001c00e4608142c8982d40045181405071406002c0c1d2030080860246002c0181403000000d0300030295134074500110050500103000f035545034054034043d00508028400c42e8039501c43c4e071011420034220511524417940040e83c4d490080c6145c58411503003a01c0240c010261000740044508164851450440140d8007401c8291340c2c4610b098180140c0b82015406901150012451110560005c4012034075442c1c0180d84006042010114a0341e0828240c1004000320b0704405101018000342e0040303412a9400d803010881c5654010500042c2d202d000101e00844010000041003443d185001e540c016401c1f41c550340c281408404100c200c515113030084001c2c040c0401400e50b41e580c2c04505403079110480c044203030402140e8000c01c00c0d44940c0741c84141800d0800b0600d608207403a4101a078004582141e8184480d803100c0300090003400c0e09030740c0da90014040c080000d03024428000454122a4080c00a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 314120026 1250 314118776 314118793
    0x230105070b0a02030a0e010207050d111906050a060f120201080703090503070f14010e1e01020a020d030c210507090806131b120c0e0106030c120b01090e0114040e010b03 74
    0x25074009510081040e03405c150394404000040409201400c40c4131b02c100e000346503002c1c008401600c84e903001c4452151a5029180d0540109880d02d40354015a51210003c540c98840c003110380041d02d62500148464202e180b800541651106880110b482c001c3e20340c0303005600c502400310181d40c1c000801400d1a4003c200078000070b0b0790340a00751400c07401100e5404555030ba900005003903440722580e400c503541c0300034040300380d07190014602001c4410100003103181070740101019442d40c1500c00d0050034160345071144018a07001c2c0c0d00b64440a80205000344a4105006040f4001c01301681c460b00000c40070310001c20802c00016a0300c2c000c0d05c10000b003442403216580d8500346082c4120300e06151000c01c0b040040c080e6025211810204d200e244c21503c0b00d41400342103402a10143d01210406050091501407640c1200d40c0301c3c9030390452200880c0e2458500c0041c1d80d0006107a1110223902512800003660205110300750102242c219014440e85003292a000d023600d14500c115036154105050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 314121276 1250 314120026 314120041
    0x2070f0b130b0409091e03021e03040305030d140709082a0402030106020a12170f0a0207050d1806020f0c01050c0f01050f070e100e1513230105070b 65
    0x20300584841001a41d000c65150502e04040c1c0d000369101106041d2036440003030400c0700c080f0383d103c01401d5100500072003980c5910b00941e150360b01000f940c003404048182c2c0c0c0c40705600381f048038091500300c412070b903880b001983c14000600c20941041302c903142410205450b507108078100002c4580e0b100042440c12200c645000a04000210980a1620f00d200480c0c00e901c03103001071402000a03401601c009a52401e25040800c07605055108200003c841e60441340700c9041e00e50f1304010303480360110b1a555040c00c0d140003441007010140c0310344030324201000440e5100e410400001e000e101e0504a055540205a90310300ea01b6100340d040d41c100c0c0c0c40c03000c241d51003140906041d03894841115001c04003040441d0071200184c460001e00d41c0f010041003903983d003120308540c90500079659098043c0090704020280d00fa2030040c1e030f01c12980e02c8603e0b0341d4a140780741580c132001140c1c0c800c1103c260355001c0d4290601c90a40c00e10400d0380707442106901a40c060001e44041d075400003082d21441d519441d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 314122526 1250 314121276 314121299
    0x90103080c0a0c030605070e120307030e06070b041b0b04081506150d051b07050d080c090a2718150603080409020711031207020d0c0e13110102070f 65
    0xd51400c10701c0360300c03180302c041000300000da0f008500034000042c1c681044070b80100800342e00c0840a0054501c00d64001440300300200300ca0b00a9090300c0c0c80c811a060410000b08075110f00000902002e007050240014040c00c0040404203201204890485c140c1e640d010b40301c9400703907220300c2d080d94000600c50780e2903540c0a007039913911a10003861100c0440d01e21a650074070380c20106405802d82e6a4608002d54500084400c3c540b080000e140d003400d040c02a9111036450140401200820030a54046000d1000b40016281003900041c1041d107120345402800320740008a8007480040c105a60703c003440c6115622516414102501c5040c08171912600e441e102901061750204107180d0b1a4000000700e402500980301406401401503950003050030308460060f071482e0045d03c240c204110410109640c4d504a428807941912140421009414424032201c42903101c44030740d025090400031031028100c0804400703131044080c0d10104d400f807001240e60703003a075024503e54000414420303c4040d1178070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 314123776 1250 314122526 314122537
    0xd020c030a0b040206040503060403050a0306080c060a0c0c081903020c040e06040f1704150e031605010c020a030203010507051909181a040e010f0b0105070c15051e090906030c09010308 81
    0xb80003a40346c55964070120b89012412142a00000d0010034060041c5526016410041000c0c0c0000c2c15038004400004440e44507441102d014000705401003410011408500f00003020038400740d400ca012135124101d4203110484044006000e010741280403440c15101d411042a2607000802950b0790300d0b41d880e030740c0304130500c41030310701001c00f1017160784000d03442008101600705080c420002c160301c01c01c0901a070301d0400c0024400c0d00004010074451a214030322000b112400d2900031000b600c2400410200006500041c6d055400d220030042c0c1640c00400820f442011042031441303110751010300f280c101c0200e0080b014000c0c00c1003001c4a20302c2c120781120843c2a6a2030010001000d81000a400c0720b00d101d0425219945a0303c40c125501d9440c814060b50140a00746186081043e548194920010b4000c2071800d0b06520b1079485601d1040f000c2d180c41d0b002440e20700c4145400c1074800350194004080d921b1003107100100180d1103060204200c004050060008200c0e64215515000560001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 314125026 1250 314123776 314123779
    0x60a18150b030f0d021c03050712151703031f030c050613081e0d17010b0a0309080307050c0105250804021f050d05010f1a0d110712020d020c030a0b0402 67
    0x20403c112a65040034800d015074012150020b0401c40c0d40352400c003103580b004121000606190408021449030000c291114544031041e000880743d40c0041101d1803e501c603080109200c4251442c1c00b00e00138000011402440b0945684008407501581d5420070003490200501c0440080d00c02c011905010b00500030b00200c80c1d9410183c40d86912001e4584101d11041711aa44003000410b50f04840038441c5806180c110b2401042d455800030410402e04810b1080e1103034040000740c0546810700c2a4032024407e0351207040a582e0f424030200003403031600240c3c0b58558a5103048007152408411410b004824865010134500b9a011450f0642e0305010060080c0e0b0020840d8400e04000081040e0310740440c010398458640754552074092104a82050f00110030f284038040041c00219503c141c6030007480c0690070302a5881104075182c4000d0060040344000f525004561501045039918030001148c0e107990844040d280d20840880e03540c0e852084454040d000341c21103001003682e81000c44c0d4050300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 314126276 1250 314125026 314125033
    0x207081209012906090d26040f060c170c1e211b030f0d0f0527030903010204060e0f03060f130305090d030309031103031e06030c030f060a18150b03 65
    0x1c40a02044020520300b01c100c45000103487c0540b012003803400303100c0400c0040c503041c60070f240c14008052401661800f5100034003c01101c01030800090300d10410402501d0840c00b070f00c529005c03120b41d9039980002c0700ea03803001c11600c00c12021000700003407031407012800d800c00b0a0481c85903000180d2550025000c0c0700000c03076030b241007048980100000c0020400300303035404e5501c00314084020120707100d465001d0102810a0306000f0410b1381d0a418050003004140b5091500035512082490b500c1524070300340d0554004600040d606400c00c00042c101d078800d0f075061480180201c10140c6139030044074444841c00c1000c010408003a02e410811600300e109060031460251300b1400170300c180311001d004400017038580d0981400c0550080080b003071580803100560071410940400320031300c1d501800b100c4800b844100012915603040103428a00c00014007542d400c40d20b2400c101d40c40e6002281c0800701e6504010600728040b6071b10002e5000b9a8005252040421034041401c01134120400d9040d031511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 314127526 1250 314126276 314126287
    0x70503220506010305032109030711010909051510020f060a0c0e09010f090c1103070813031506033c0501140a0e0106060c0209060f130207081209012906 67
    0x74001c1000c03c0c040d500a1000b9030711042001610071215990142d902400d00d040000d0106100d400420b65080340d41c0145102c00c62a542801250760034079035480103040c20b04010510850034080b001300c00781840181c5401244d40e043d90710582e40e400420301015041d52140300000c60307004451b031041c3e03106461840c0580c070581903400050140c20081c1c0140c8450640100708000060300c41c400c5002c1d00303e86050518001d00c60300241c50b22801000e00152900e4000100e0500f480c100c400800080c603171017243e200070030404032003800040c9114003088488003c030200c0c1c0050452411100c0100d551400e41d520390072640c1081521031109110400c4070250b483e90b0b14000001c21190070684100d10301480090044240c60f011401d6403096070006040c48440030103100541c0b10a042c0c0b544c00207094520306e0364698003601080c40d150107450f603040b1461022a10908100c00d0200804e4443d00e61601d40d0602c1d1a0303002038600303c8084c0d494100e4407124a800070742c19865244414804118020000750070174 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 314128776 1250 314127526 314127533
    0x42d0b15041d01061508090303040f05151519080307060e01062d051504050f0d05060705040302011106010e042004090303050109050f060a0b0c030c01060306060501020d0807050322 79
    0xa64482d0007020070741d441c0c2c5800d00111840b00c803248941d850906d010149414000038251303c0344009000502031000000c1d80c0800d0010410030201001c401e403240d600b0a1400591442e4200004100c01d0310580711600200034000c0213090305016a005400903514080305684c589000704440c10ba010750325521a100000c1022106003503184d8589241c04c07003444206906070300d112110040d0401131144d000b0116403000d20340003c05450581d003045c1c0c1e2000280c50707500002016500c0907040100103100308002c002a09038880094003ca81c401c1e01c5450545c200880100d844c1c2c5006d0080b008105c60006c0000d001c61881000803c0c10f1040940c0210200c180030045826100802c80a6000c2600c643c01042241d89910445600440e50240f444103801c0c01000074003186111b1007180c18004010a8030040084280111296440c01c8402001104d94034504240076014501c10203016000f03040c4003d560343e0049860f00e20800c902d5480c2ea207169940c0310f80481078001300814550f00c5540f444030300d000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 314130026 1250 314128776 314128811
    0x1d03030a0c0302101a150f0d0c0c0b010605090a08070506070605070c15140603010c0c030e010504180f060509040c05010c030504080619060501090303121112042d0b1504 74
    0x26681105c4000040d1660390040c00241040b03070300d10940f43d60b01006501d5845601009641ea0307c1213600380840d11901940084507a07910305000548265107000001402941110003080e401c402074681e407488a954041c04e41c4c50f04064030031140c00c40030400c201c3c0300003180c41e4051580802203042c02d200010060710b0f00c039003018060354640e4400390380304a00c0401c4e2155100207680302d80b0031002400848004400101411003e82c00141884a1585d183e40280e01440555000e40752030314060140c1d4118940b800050894000812051031a100e400b03d0641002c1030010b1140d60030008468266181900454075100039000582c10060705020126481d941441180e00408000d140c500309408200740050880340180c1c84103060140c82c0f041000002d410a415035203082241c0d10000300c94903c0580c6211078030503e802c1c40e92801e0144100401c000c590700c10080031070582c452000030f50185c40400c004120041d04090004c0d49400000713500d151103940071900e0100085e00c04141c01d4001159482e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 314131276 1250 314130026 314130041
    0x1f0e0606040e07180b0f040329040803060901170d1d060a120c0801031a040f21030b0105090310050a090204060e0a05010e1b09010309080408011d06010e1b0408030a0903031d03030a0c030210 83
    0x10400bc0010501045280c040c1300103002d015410f40442444044405140c0d030780b4440c00c80c640074030640705103500441428900003980c1c180050b00f140e0f51045281001404600303030070400da074050301e0180107200c1d4602c202d4401c0d058990010000e4201020035001801c1314000a100f12222030300d4040013000110800c0c1100c2c0c1d40710b80741d0a04183c0d040c1000004d0281c03400300c3c0000e41000028441c140303030741d50000741011343ca40d450500028a5200e0381103d0700030b0305960001a4000303041101c009103012010414034428140d03002d041060740d0b00c0c1c41541c4002c21040c0d0700740e1a0001c0b024034090541002d200146940c0405040010f6620103a07990102c4542080e40048100c0e5510190f001c200b00a81150070b80e01c401c81d0000d42000e604001c0c501201c6100607154000c0c02459040644404404c041158050500042140d03117454841000a20500702404201c1c00112000c4845d11020480120441c4008000b4080c1d814006142c00844920b4442c503004e401b140708000c103440b00c86030540710307145 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 314132526 1250 314131276 314131283
    0xb07060f020f0306031b100e030a080708030103050d0f020c1c0c030c170c031e0304030f0c0630110f1605061f0e0606040e07180b0f04032904 62
    0x140c80e454400101402c000404508a00440c11061b0108056503610000c1c110200309042c115003940314003010a103001c1c51540020804500001c1e46000c1c00b003c98051412a0300c540100d443c081907208080b90740400300705e01040540e1020b100300c0802e10380514040d0801300070210180b000d2400b51103114403942154829203841a030941c2c14004540070526151039803803d000205038520486022958400902405848040511a910032010002d204a40080d5045141508405050b00380283c00c46da0902c80d04020460781c1c2c55810500c802c001501042400070640078070188904441c08000d40700c2074509951900080001c8441150940050441c0010307035403002402c8640f81c50018030f0044040d00c0f0314094405203600304421101902000c0a6403900300a443d4292900d001090281c0155001344140c1580d0b041048040d036404210020038582008101c7c9000e40e03199000510707441000c0b010318042d4010001400070170890304c005000300020b03048806940c090032202e200010070585045 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 314133776 1250 314132526 314132557
    0xe01030f0627030305090106050904060507020f060a020a0818030706050c0904060f030501060e010e041103011e0902090105060a020705060318030406081f060f03090201021005190e0f070b07060f02 86
    0x4400b0703d941440f600e03034410a010300030840c19041c000062001140100010803454a4000052145100b80810720041e80860229091820030700303c80401f1303401407105000000c8c880303000102d04040201c00b4003401c000301c5000d1450558944c80306005040000d0150401c01c40c10060390394161240c1c0f1502c001050090b1010308100d0551400a007583d2082c4d20120300e440c15000140842c000302d10307402d0380050344219800968500d14002c03d000d01911403400b41c039003421544003031180c2510340100b203580303100f1038040d00340380e8840e0300b0040c0d0750190100043c01a4000441402681014401103030408900002c071441200340304261031444e031007900540c001400403014410100311043c00e01c0803041e18000211034081c241807004003040800c9251108141e22a0700c5e40e015a4020b001381420411010f034203100038038040c4402240c1161021148400900d4290031400c0b640000c5204d0a00d20207040152400701d140c00c1703130149290030a01d420340c0c48030b903501030601c41c80b40c0c1440245108007844648 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 314135026 1250 314133776 314133851
    0xa0e03030d0f0501090e2a0904080a08071404061803050f0c010f0c080708070312090506071412060904140d09150503131e02060f03060405060a0e01030f06 68
    0x410b42035070411385c0000011401c20406048851001c1424030044d80c2c1101072408104a00c808182e140300100a0581c1010052040c4014408035200500701d0710700c1912111403d031281201120741d40b148a1800c6001e010922092001c548603a41050381031015104040708151a600c903079003007158080200840e5071042c0891212940c1204c4d124050b500d180c14040e20781e19050700c64211502c2540401400318400203640c404060051003180c0b90780405250410260042d4500a660343e84251111808506016a0b00d555140100101d6407115400f880c2c00544e074450401388101c03114050000c891013028001800030288080000009104040d030320003c42510f40207090b440000b1900382d080c20080100200690410281c6031494003c2c2e004030b003201030152108440310a0110300c50007d600020000721010f0154041007d107000307507c12142013120352180b00400011513118480d17190002000001000454003079000c0300e00b036034001d05012541c0e41c1041c0d42c3d00115003501604142849880c0f44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 314136276 1250 314135026 314135051
    0x509090a03030b0901030302070603020906190f020105060402071a0919050c0a0509071b031b060504022701030b1009110c070b2b180305180102150c0a0e03030d 70
    0xe49070f44018191019500c550564070001d40750781c010300400040c15000a000691a141c90003212030241c80e0300341c0480d98030000f4000800c406125004c002c019030034103002c248280340034030841c0e0380b2030340c809400301ca16041c0015400d071901d00188103520901400d1034924074000607901594103184900040c0c60220008400c00c825040280c1000c2e01031b481c0081002a81600241a01110038580c0d14030201d48919240440d280c503c12040c0204202499140c40100a6039800480c0150301c211030710802c0740015040316070f9045c41700c002d4a00c1049240c0c010404078440400c080d402124000c010b100c05034403000540255203240d070b6026040880010204103046051119102074a24000c403189000400d400c2180030185506c8240ca02207046c00c80c03000000c082d540104840c250204601e6102130322403c000d061500aa401901c01a0180e140300c4400e40c030108010444e101c0003a207402c040e403203401300101d50360402803118084c000b400400c44031558080014000e81c020168011507003841541d0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 314137526 1250 314136276 314136281
    0x1410060f0206040f02121f200703020a020d030504081e06090106051011011512031202091503060f0d1203060e04020f0603101503021918140a0509090a0303 68
    0x40d0002103421007000c0c00009511314102d04401901103a08400c05c0c0ca05241c07442c10903120b501c01d000c9111441d09600211031080e00024041007016800004100c1058500080392107074070f10040040e0841d140c0080145449004101440e00170710b41542080d1f1508002c0785412080ea4281030945c0403040704074050001000000d500610441c000d126580c07401c4045150010210300c4e01d001c1c080b040744550b000d558250b1140c000d507049040d940c001030355104e02111410780d40b56800d070001004001803005048541c02126010803028003603622184524221040c9604041c003421303400030005e506da0010307a40b64040c2000350350141e031808004640150b0301404441380c590040804074801400c0001594a001003042548001c0d12856070701c0d560101c0c014000642d50300100c04280380c0d41c02d80700000d40d0640c040c080903003414581070900c80e002c10b1f090f94120000004105243c21980d800d110ba00d204105a60801ca8040d000f4080581c4400c0050300303c0c2030841d407410715030740510030f030074103050307060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 314138776 1250 314137526 314137547
    0xa17031006030e100b01050d0614090609070f03020f0c0a0b060915090606130503072904050303031b0d0c0503060f06030603250f2301020303150d0501141006 69
    0x505003000a00d00c8005030f640c544101c60031940d03503141d6a40c80a075090340513508035021145c2e0300c2d07020020a0349600e0640d00700d05c418084c4600480c0c180740000c0407401c0ca4543e0318010f44581d1079840c0da15082c5c000440c080c0d0b20818038400000b009219041c5d0000e42008481c00700c3e44203401c50030140c640343e41408500d40c0001c0400f1000c1007101400303401c80d1501013000d90080c40a803615561815008460710040c1070aa1000e030b01403058102c0010310181c2075081c05151074441090050840480b02e02e08406d00403806626810782080010880c040035103040c0d409000a0b4505560800904400900071900e9040d40c0c4408a4000410010b61f8601110400840802150113504505110303000c0383e1354081e68000f09050034160001e091074080d84d402080000c03c542e842c448080c6468003040b681520107032600c2220b251a440241c1a558008000d50b482030070706400c080c09103e900d41c200704040041c1041903804e5540c0301d04401400f0b18101c01030344124582011404480d140c0600205000540b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 314140026 1250 314138776 314138789
    0xd05070c0b012418050f060408150f09031206060715110705160b1e0706020f07020f040606021009030504080601030303021b0c010c06020708090907020c04060f1508090a170310 77
    0x460300003c41c118281300340c50954805540d42e540c4a0400000f041d014416500010000d10500c40f02480e100c0248c0c00e0b461280260081000f10780d29003900081c0d40f07000d1600395005500c10980012204e0401f04003030103d0a001e103442420303419510410408844c40c4802c90b103540d00000400c88244031007049039002002500348503000141c50080d0f01600e6000d59454000905054603442001d2028081a030f5038450300030700215610b0744108072040d515405124120301461555002d00b02a10b454450801201d0441d00a09042100c1c1c40246000340403d4100710148a8184008240b07074508204a502952090702c005075105c42e044410400102040035075070700359211900540d4603981c049414000203600003005600d07021645000d00c124050109002d800042c030204101c40140e000510158403007081e103080100c0ca46078850070f0755505960042c0381c00b1120710440c3c2d079599440358100a0f80f02140340c0a6a0110705032359107050b504405000e5083c915140801840301169a008800300107002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 314141276 1250 314140026 314140037
    0x106020c060c0309010507050709020d06090b040506032e151a0f090d03110a0308010306060f081911030303010945020418050609010c0807050d05070c0b0124 69
    0x1d0078100329528404c51031868104800882c43c042041030811441024240c091001d54691131415052401000188107030f5414504004400c121800c0c82c0c0314280c000e02000d40503000711850780380052400580c03040e10312800c2d5500d0494500b4500c07684640829174480c50b0913512414500014038454042c045071111440301e041041d4801450740408450310090240c40c051721010050600f40c540c0342c4c020320038090303d001c1e41c00e94a003055840f41c6204d041e01c1c442d03102000003948a0801d805040768038000d030602c56003c0d43c0c00380514000c1c0743c014042c0324412031610102550b0000400c2c1941c00a9002d009001c2d100c00c04100c0d03641c3c010b501c0c504106401c030400829881480340018003044860400d80c1071200075000708056440350f411115144400c42e80c2d8611116180c500a50b44078000c45d03508145501c0c09440400103441940300c2c5003c0c0c40207640b003504150340401d45030014800900200244004006030307500003401d000441d03000308882605220300d5030340866822161035400f501c0750304004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 314142526 1250 314141276 314141287
    0x504110118031401060b040803090109090501050a03061e0608030d06052b050f01111308060105010e1306050907050c1b0901090b130e0f1e06070c0f02040905060106020c06 75
    0x1c0000141c50100d03508001d4403110800a1408203005008503009036010a600043c00318182400200800107140280c1e9618011980d03040320804032130084c06240d90004101c0130800c0031a15070303002210210122440001e010005c90101c00443d40326134400b1405070404903404468803128800d0200410301035a07080003140500801180d5104418a44030038140100e00500034040100150004d2400d10310080205000c004048462a00728216008142e0b9106101090f1000041a0207040f6403041e12031001c120440c00800100c1d0407500000da045030356999000882c0d50351440a603000700703015180d09644025403850141468155654403000311001041e00816844004000781102d041c17040c0083d940b1801c4000a58250301c0400110880d41031220740c500da10001b00c0c600504040c0503080300e014400844e105a101894000f1001c11908040300140c1e107103001d4030f08030b1302c0e4921a103514400303045281c3c0002d04440d9a01c000b40c84c5580070f0340042c4841034040041ba0f290f03010031960bd60510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 314143776 1250 314142526 314142557
    0x708030409050117010e1f0f06030803060a27020702060c03040b040e24040c21020c1c09060f03022101030302010501080a08030406150e09030307031104030201020606010c020a1805041101 82
    0x80c86c582c2c1740030207492000c000280b10307147c079940900c680c0f418040003488565564108140950025601035124140441d00001e200081c0343c010b440c40844c07140d200c0084100d6403e42c6000350001d003c20f0ba000b80c000c009005400006100501c0a014150001d540350b0b4200220030b240d000c0700038464881030f2001c1c00c140b681485201d000070254001210041001061070200312900481c5012101c0503001940011049820304d80182120a900004462034040d460101884070400710816802140039100207001031031084200001c0c41702d46d070078050728180400c554580d020702d40015007800001032400500403d035080c09a140100203c4000303101c0c039001c80d01d82c01d241e44006803000701b410750382d00f203503224040303801c490750380100b2b20041c00e014945008000d1076102c0c1c1c400c99030040040d1401031905141204a03056a0a41e034041e40103000c0e50f40d0320030065030b504010600a90303001504000014401344a0015217040760740340701000c106402c00389000c0c0910701003030001d503060001007543d00314107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 314145026 1250 314143776 314143783
    0x603020903100e011d0c041a13020c01060b04090c11070f090905010605100908010c170f0901090206220b04050d0b0a0e031305090609071b03020708030409050117010e 73
    0x60203002000250580f140700d81500402612100010b40c401581680c00c00c03040100d0303061300800341903a05020b940d980d00003c200a8032104101680000d400c0054840121281e014058201c111000000c40940ba082440060341099000111030f9490b2620314003070329070080022021184000091003c03500385448410710201c24082d8a50140e030701ca03050b0317050000940060000349070251518868030100d0b1002071191190b806840740c1e9600340381c803111945102c0c01000c8082c4080c02080c481d5500c4031344040c0c006c0e840241c10091190b48808007580503030b4031200144580100d101000f40041004895101c22802c40d03800323240d028074140b10400454a0309080000000d42c0981000000d5841c403840100418203004814a10701c03000c944c0102e8203c400c02d0b0101554001c69a1a2195807201d04001c847c0e02c0c215550b03000505243c2c01c900301045506007002e940c5100e401610f039102c1c0c890446034550f802c5940b042040b161244c004200300d42d0f09041080e40c0ea20f51200902481074440c070b165030f4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 314146276 1250 314145026 314145043
    0x12090602100b1804030e030f03120a0c0c141f0b0a060305040c0f0308070b060909100b01020a0203010f0b090702070b0712140c15070207030f151b0302030406060603020903 75
    0x1c22a4403011590115558044885000858200b10f480c06052a040c01020100c4000da001c2c060b20507580c2800050b180082902c544104000040c440303940c0b50000c000141c0700e020301e40c0d400e01c41700404a50007e5220000d40182c030034054003d10a2601c40d1360b20703800320400c00c419295407034a840601d4195885081d005400d42e8114100843e03541c541d442d01032503400041d0f00919035515010343c04403c0140c042d00424440b0f01038003011703410b900e400040210280381178500d000c0540c0b0404c1da1410210f030f150003440744a036050050340e00100e56030300030034203441050440c15141c655030a40c0d02e030145800c0d03807080d80106061004194050611a218003288100310001d00143d11410220017500d1148a080640d4001e08800b19201e1560000441d5250b14a00c803d0604484820001e03603402d1002500741c00302c03900540009503d038103070b40300c042103d40e550741d030503400c035894102060740c00c44055011035490f8800c0e603005950703192a0500c2011100303070f43c00800401d401009000440d41c0d0009803800e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 314147526 1250 314146276 314146303
    0xe151b060a0c050d020711091501031a01080a090213090b06030601080303070c030810150f030c0503090a0f06020c03070b19020a080105130902040e03070303050606160b0403020709090b0412090602 86
    0x141d503409117040c41e112010ba07000307d240e400711700e1000b0854012507007180251283c1342a00c051181d261507103142c1c124011131f290001d002030803007000201c851016030401114180040e14242102c2d0703c40c1d08510030341c0c0c003100003a07540000000c140002d40c2001c011890040030964003035410750a182200401b10300c803c01c80078041040040214409a025806481c02400441003541100950309000381007080d04402d802d021a1a20401d041c50301c1c05041201e100e80050b50180045100550f500d0749904020041610720940c01d00c10014030050800084c0a66406890b4010851030100703080c038544c0c0d200d0680128807134010311411315031640084030141500d00844a843e03004141d0241c407801080503003c080c1d849403c04186c6009007101000a00d0101e001c0d40d004e00459654005221461041548402c880302d4540c882c0300c0030032002a03501303410a100b0300c15a481180d4440ca128141d520021098510105201c02d00c0200003d052401100b4841c0c0e00b4804405440c15a02079203440d00105400d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 314148776 1250 314147526 314147531
    0x9061507080a09080a030908010e0604030e0d0804032a140f09072106050f041406210f062d0609060402041a13170a030e151b060a0c050d 60
    0xc400f03019580d418090401c1d80100ca600c442541801422202140720340e12081d46001080c140424020540074451074054440d400c0380c0a192040c040f590f00d010304140c5104030306100200000304d614046035003042c2ca18880100703000d042000070101c0c0d8080c1c0e1040c0300d4a80d05205145007512900f1500c1508401103078a0030b00d51b540c1e0300058409480f4110648402051000341c4450200c4a42c02241900e00c151004820018258188421141540c0180311010002d6000602518001c0c914032180d284407840300c60f080c0010355240b8a00003089499890a030405010086151080406450b000c68100e10001181c09203154041c0071800241440340690215800140f06440380e0f01214020001e507103030040c0c61102d4064600c000d03048003407030000a050723480000440d5001e60340243d8000790040058042d0005e250b4040e202d20b6400c4441c1c5800ca1001140b9524410030074010302002e03002000d0f01c0f604034140ba9a42410800700a08081c081450032600da607800d40e00000345d83c520800e02400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 314150026 1250 314148776 314148787
    0x608031c091401140121230c151806090607030e01031e090515011a070510060303020102030f0f07051605070f06120f0501051e01030605100e0906150708 67
    0x411000d145031205098640c00e0041300d001103401c1061130b5040b034000b02001c03507600e034081075105882c0348800805010400c01d8406441600010300c950880086a41c0854028036030490106030302e1840c252980c003800101113600d002000314070090241ca00011211249014100c000082885c0500300780901000f020b0300d41c02015034001d51041c0c6003451003102c002c11803c0f1080812018041c0350104540303601401103900c6c4007403280c2c40618103840d40c4801200e515215036040714000d07080030a080d12644940d00c0c5500c203139803852040c1e030050b41c026070025950f49000114810505006001d0402d80c41d840c10820240a6016094542c000300c2c1200c01c200d41d5100d810030529011040d0007402601c50098000100e141c2c102983c07540c2d01c5100401800042d50156040c401c44900b48202900b240041145481e290007036010111030400c1410f0010b180343d15003010600703000c1d41e9961503010885c18403443c40d5520b000800a031f4005021520b00f41140080041c0d2281d030f0040d14001411a030010031b0303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 314151276 1250 314150026 314150033
    0x40510060c05070f0b040302130b0a12110d060b030f0c090109020d02040503060c070201080c04051f110d05370e0d060504050105070905041407140d0e030d0608031c09 73
    0x1c2030010711084400c801d10b00d40320220101703242d12511080740304071200515001d5028030f03406a0050500014118003e4030b01e441e5008104d40071a000488042ca2540c1e10190541d4803d8210845a4010080010f1410b0850141480c005050700340060a9201300301200c0d5990780e20421034191000341e031025880c0c0303059404040c060f0141f5048640e060048400300656040048090b000c1c65000760b03541c440a89070070070680c80c9031045002d141c9e0005c1040307100301c01558482c14080c44d1100640b0300400c1c8a01c50300446030800754220403240000f400064034030b807445100701c0001840f003105845040c00264100d041c8062001c1e5081d800e041c8406401d641000380c0c0c5141c442c20280740c0040050103a490a0301e072403402031208071010004503c3d600300202e103d0505100302924100c4041403440140c8036010b082c0c2c0d50542001d8811000d000411604e01195400d000700b50085015a001315103400c4078202e40e070251443c54010442075841030000e8890f14042c84c92a030b005450307004000503800340506 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 314152526 1250 314151276 314151283
    0xb0408130503150406150e22021306050a09020a0e091e0405060402041b0e12160806160516080a020109240c030c05270d05100b040510060c05 62
    0x91100d6032500400b50301200da074110009140c401d0707100d50340c10080b8101d408440e0500c8902801401090724070301000403108c0450081400b0f07200a007002d40b1100c818140c0c00145020071645081144544403001046103003031080156018003002c08095082c11403683d0000e22004100740420301c1400b040c00030500d004030f0004807070100d000c1522002090b01d8141090f41e80e454041e2812405286090040c0d1041d250725000c018500075569244a90701c11840200028000c1d00e11100a0900030031054043c0324035500c1c41107000f4487d440c042d12084c0303428518850b0001b448101c000c140401007104900c1480110303c50000b49502a00840d1190b02611089004190882d4000e0200401400b40340301145002c2d0030b0400741100350b105018000c03034040c040301510b03092108100818400e01c09845000b40203412003000c20300668400706c6000c03000c400100b1407076000c0c0c029a000d82250b843c0c6504203295014066813041c0940b400e200c942020100c03841da00880d40700b00d03020403100e515070004000e400d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 314153776 1250 314152526 314152529
    0x801141014162004060b04090213080105150301140f0f1e0a0b040b01020703110616080301060512070c11091e070e040c0e1c050a08210705070b040813 66
    0x241c6039030b400440a2400c0e40c88a403d1265900d078201030301250310790034070b454020f02042c0c0d185064683d0800e441c20300b9410203908200703265003079216410740125016000748241e03403003240c03958000410401164145421902d820090401084100b800c1080c045848580941c000600c8002d240d6150741c0e140441250f503000691000300f0041c90414021125410781203011340e608115010400f00c50700f0030059988850900c0000d041c0c0c1d014092804207840c1075000b0b031a031502d911210742240c451966503541e069100340c000c80d010400210380301c803c10020703019055001c1090700348020701e00303410380310a1354100702414141d119950000020b009042400052501c2000403822220071307041801018109510a400541c000d030300d4600c4025641e07124080c11a440b0380040c0120000304000c4010b0003410343c0c004001d944600c100154140001d41a10040c01c0045c101c842c0880c08502001e884e000400020b0800410020144200720204800b402a070f900070350b01001c190f07619402e000d440807071038156 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 314155026 1250 314153776 314153797
    0x2202010c0605040b040311210901030608060a0f06050604060215040309081507110c0f1c0b07050403020f0a15272c04150b0d0b0c0a0801141014 63
    0x2d02c01070000700580105aa40500d00c030307445001049201c8030301d0540d5080c41803052004441500f504640c60180480100001d00c0306140104603030380c031400386c685002720030380c1c085041a982e05d0b030194400741e05220310000f40074121009071419241c00c000940e1410314600003200320359200b01041c1054002c000c43c40051025100342c0d904000300b404880c803c0a42281d4000114201c1c03985020036460102d04050088230040164440080f4031003840121100714400c480d0740c80c1038070050404114880d000600c2281c3c1030303076616542d0707041d0b2041c07022400300e16030814002c0a80820074001c0c2c503020620100340300701914007440c1c88454108503081402c049070104070118000c5a000c90700076081801141030070848950101042e807080c007180380e554001c8402800c044002c0e9440c1381c43e104190405090488000c020101c2c5241c5078442042901e8169100820b9040018040340d0b0280c020744010b00514448941c004106403a00c00310307900f05039024a843c10000c40003660340380c040070002650b0b00710f00c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 314156276 1250 314155026 314155031
    0x1d040c080604050c03070f0509030a0b09100e01090803220c0602010b0a0806100512010b03030f0405030613080d0e10050c03040201080f0709151e0201060f05092202010c06 75
    0x501511144080e560307503000da0708010003d8030950300401102c0c041c0c1115501c0c500011490703e42200d213030300724034a0130b031741030084000f82c10100300c005543c20b00030802400500300d48000c0c040184200c80d0429052030f03469043c0581c0c100419410b43c241c070341c000104620760743c122601c1104401920300408004000600d115000300e035895055208089810b0181c0b403801c1d2580d21910100c0da00c103400c4842032301d0307100d04400901c0f15081c0382c40c0880e0069800f5001045c108000340000342036400031507014000f00d00c046030030801d901d420003a0315000904480240b420040980701e000e6148130714102d0300001600d500300e103140d401040220040a1071401806c000c00d04010124421981c01503509030300240b503504c04904812882c44015010300450745410404a152048520171503d005245405001c20441c150706207200000b91b0b21481c0409074000110107040802102103460a500618002c1d13001d85c1c100a410305417543c084104405c0c403d1401240c007064801254100c1c80300c20001c3c403550 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 314157526 1250 314156276 314156291
    0x40201030b12070501090f0308030606071b03080a14180f0a1e0302120607020c01032a0c0302100b010c0206090a0b04350c010e0f06070c08010605061204031d04 70
    0x40810700354141d03582641d07406d05403030350b60090a0003c2d16602014014500420218099181020041004d107104504c0c64881c0a00c00d02c0c030a40054060f401591010400948060002e60007a954a8082c1c69040c000f401e0210070700100c0c0e011414075100c00e005d0140da000500242d951220804000c11b02c640384000b07004040e000d19041c4000522041f406a03142d00741c200d8005a0200d801032107480b00c1d600421007130f88440c00460181181400c075010f800c2070304403a04000c4422000a40840440343c94004152150780f60092030200109044041e0903e06040c41d42c4a070b07400401c140c10203404482041d215030b0214001f030f0340c6104a91040520100c00140014021000407a05c0c3c8054040008001c40c41005500780d0840301d51014002c05542045222450315030284d5443c144421002d021480c00041e0a400300d40581d00603c403d40748541d80325410440c0380c1d02401028090202039480d507042141c00c021045440602074802400e2007045094810083c83d21031072626407460080c000e01107807 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 314158776 1250 314157526 314157559
    0x2060d020f0d0609020702100309081b06090d020613080c19030f0206100b07150e06090109060e0c0a0e0c0903070f091d072d0602061e0915040201030b 66
    0x1640b001200c1d03070005040c4880003c2049840c42174a9940b5005020340440c0e040004045004050000c000c891600c0180a000340c074503a14203410f040303030b00100e0040a1a00705030a1071407a0114a42c17105046600034000c00504200c800b031184042680010724585401c000440507041c11403540d18005503150600424040c950701c4011500495065001e4506a8a031101c81c034440d91051f02841001d16030400203c000620b00380380008210100d54030005d11040e16035195414580d040d00c5460850703444010307640502c50319216600c0160300d1840100014455100850585241c038420109007286c0000001d0381e103186502102c02c040401400e44001c0c94803404030b1030074001c80b03014499540d4034004141d000c0b01100000b0318132a050000081145900d416844038947d510380c812000007500e03a4040c4800c03c08015451006001150040c080915189040c2d041512000d0680c40c0c40010a0060280300a00800c1c000c41c61480c015854195075560300042e0050194420700350382000715a958031341d80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 314160026 1250 314158776 314158807
    0xa0e040f150506090112080705100b040f290d0b04200609030a1101050706050406052d1b0f0a11121c2004030804150906081302060d02 59
    0x140c0c0c0c031550100007103540da90341441c00c5500807203000e504000d5160040c400103807800f009841441c414206145429059074626052400d81c940e02c0d451241c80e5012010203151a0003406ca50414141c820085034440781c1000d01100040c0143c0c4000d0002c4110900440d03d60681c69101c280e0803040028190500c3d290480181c4080032400d03851801100400c1c54600e4410f044a5003030600a000700740d100c0050b00ca020343e5241d400561414040d0820000c00000c0f0b003805094419401001c00050038507101059203001070080d10141040216144824a9841c2003800c0c240c02c2400c01044500c080c0c0000c2d614005e13441290090750480e80007040c2e403180164042c50042074070400c8030640344000b0301000f28081c50b0240c3c0720042185020903054592100312540032064814803400e01082c0540d002c0b040c0e0b03504d0380c4039410564071001d00113000c1c0302c001c203401c44420100074a0700e007085086251070002001c6c408054040760750210703000c1c1040d040d0340c0e41c0c40544000100a203821562202e00a014282 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 314161276 1250 314160026 314160053
    0x4020108060111060f150d0c0305070b0901050d0c020102040918050d020304080a06051003061503030e0609060f0c120c0c01090b0f040e1e070302030f06150a0309020a0e04 75
    0x10311100c00084a95100d026407500d8641c03103a00403c003c2d26032005070040d20b04000c00c0352400c0e0070140d01a008568540700005440350087e55880842400c41c1811414421180c000c1841c01908201602040e46d1017022101f054041c1400010310000141040340a8440e5500c118402d80c00c01c0c02101c13140451031045a0720a09c01c0080310850304049000b0780c0c0780c3c045c51003001910340141402c00702142254204d5a0b104a01c40447d03421261296a1a0f0443d0486044007110140f06a024020150005a00315036520308460341414207031041c002401c02e101d1781c092101c8100001c203100d40b07160f40c01c0105002000040030a039403580c00b4101c45039601c1c1c61030b030256400140106000540d0088007000c0340c40d05048a205c00b440d15003010b40c25012450081d1045800702d400c14880075106d03840d400703241d008409643d0096600d0800140c20503841102030000c070b1040c804401600c80440c125800c46c2c40c041000c0c20045040e4003513000240105c15039a0200358100d100400b004100301d040040d468 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 314162526 1250 314161276 314161279
    0x613030204060b1b060c031609050a06031b020303040222090b16170f0a110c0703051b0315010905070507050304120b07020a050601050609150a030510080c0315040c1502060402 77
    0x603004011242469545c0100356a810b903020300c204080f0740c148103203c180d07a042112904001208682e1070021401c410304030f070700150000c0c0e91403d0b403880c2d1110b49220704103041002d01c019410341c1010b4001580040200041c1603414846189004000000b07401455003c2c2c0c11400c84a02441e0142000360010010f0040300002900d10303410a03115421240040d00960880f0544c4407996135141c21382005010031100c0128140703040c0901d0206c11401c00400c00035620505c0580081c502d440b0000300d0110190000d43e03c29041640900d5149960886107070454100f0040860613441b0302d41e05648900c41c02e08064518000014041808480308501201030b5100c1d100060140c1c0d264030040740c44841c1c40000402d01d03080a0010000c5151080280c6111607000301407800d00c5902d0314105150b944520790800110340c54030104109400007443c2135004150950141191180b4140000d45903401042c0390089101e450b80480c0a000e40c481d02c18002d003c00680c140c003500098940a96501c40c1264200d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 314163776 1250 314162526 314162557
    0xd3e0106061b24020405130902041401050108280606020106050319050319021501080a1103010c0909150b0f030414070f060302030703090501060b130b0405030c0613030204060b 77
    0xc0340245a0550044500c80d040342042c440f5915460081031080b050f07800c0c1003102078080c00301103103d035149440580851030308480000c1310400c5205000550760107620804040c440748004008598100803402e038082004002c030010560450913a0076803c542c4041002c3c1949400c4000c078005130154000c070181d6604070211041102004008494589541e5006007250024054800c4290341c1d40203204062415005031503403046080041e48101c4000d030720030384160340460909000c3c00b9039a042d401c074144082e0001d01c00b541c492800605074117018800c0011702640d030f6002d00c0b40d07a408000004094003240303910755505d80c00000420b400c7c0e0000d03a0b040e41c803000b45000420501c00c002607140221800e00c0041400c4900d456804e070020740005000f003007850b8603590305200284c0d081c40350b0f0010b00341445c003494981c084230808141401d80d0340c00441c0952002c000038400340d603002610201020f000c0714255a603030702c110070442d440c6020354802900700b814283c020402c005024090401421002540e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 314165026 1250 314163776 314163797
    0xb01180e01020c0c06540a170a02120102040608010b04030b07051c06090e0d0503090601030f0302071e0302010314060d170f071101030506030d3e010606 67
    0x5041c200c0c803d400000700c80307500291500c5142c0c10600d000c1c02d002482901141c0d80450080b0840042d94005021903a0704c107119180e81540c0d81281c004000c2003e0f0064545802a0a4802050a0342c01d94001c600100c020303010240c00282c420413404444650140081c44003541030b0a032180070750400d004007008950600c00218060842106940482c0d4000104030400d4840c80c10598840d401212503d611006444210342c00d648a402024010714182c80d00042c8141d402c0c010900f40070002450108203c0d00300280002c4040002e2520f05581d0400f040044240719464241d24190103640000c40032400701340c3c0c1d02d512481114110701100d0003a2420301001c4450011404014002c94286502c03030001c0404002040c4247c01c2d040c1542815844149041c0104c2d0359000b1329088102c0855203c2c4136042211a1035a040c00781c65003004059008001e07580050902420703411005801c1104c0c000c40180c0d41c10085121440046030008010045089000d9018168041e080078051a4086040c1c0c034034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 314166276 1250 314165026 314165051
    0x609090f1b010e1203070b06060903010207050703020103061409154501060210050901020c0a11040b0324040606050a15030c0905010c031206030c06090e0601020a11060c0a0b0118 78
    0x2041024120800a50302e0510304c1c7d55100b1010740d010389003a070018000c0c0404152910244000d00400d40954000c03c038540c610310004096036540d400504c8904440d9413144481d458015845070881c556a0342c02c1c00c3d00c07084001244291401841420010715614108102100300400550705104040d00c1800c05c4042d0108441800400381b09010050f4070180c0f558442c024958461a0855100000989404401d070700355072070044956410365079100b512040c010503280034410803543c010207074090701c0580100241004d820070302d0082501b01413140c00000b800c100650b031201c00074101c020024600152507144014400b400c3c034070680d0100c0d1810f1000d8068501600340f0108031071050359607040800d190b5404803120b20842020a41080d1900c1c0c022002581080e0300f6400f6000b240e580c1d40c0d10f24940009800c1001002e07080c02d041d900300b0304074240414454004482c5000c81503890079a500f4404c580d640c50b0036062840504604003001c000705034402070801c1c4001c000709908081c42004600d60 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 314167526 1250 314166276 314166289
    0x2072c0f1519030b130606060e0a050d020306011e0504090b04061a100c06020706050c0c16080c210f0c01530108030a0f050703080609090f1b010e 64
    0x4603034445815000b01003000881c180c18103944842c101c2c849420001d6559504001d0315129000000441c81d440310811103401c14107000c000401c3d040300c1095006601d03030007103600d074401801003812154060316410300c0c111200c051880100f002401c10402a009030922024800042d10116130311030030f04080c03000c6003c440d1102d55100900405c1c2c00c1c0c4400042c0d5041e02c904824071800c0b101e4075002d1101c2008544c0d41c2c420244940314440005503100d90928a05007054103141d04c80d8480b413003102c014031004500041e10b060142c0240e0f036410303800310719690f0041038504001000b412886564006080d00e100443c11901403031082c0c031500e58405270090301101ca0714040940c1600844074081d201e241407240c44034042c2c000606228107000340340c0d01d81c030766100040076009007126900003d19612203c0e8071040c0e40ba40e070000340c03070041c0c1405026036000304001c01c00781009204104a01c00314400c250244615042c0c040084100c070002440246095109481d114160f07001c683c2e03034003040c41d41c1c1c20000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 314168776 1250 314167526 314167549
    0x3b040203150105090409020a090c02060609041505060103060b07030309140309010e040c2c011205060d0204090311010c081501080106270314061b040602072c0f15 71
    0x11800c010701406400c0119a2a0025006264030546400003540903844110588015100100d40818040041040039250600103815039000303801e00b03010880480d5421800040c8615814004a559211500102c0107881030703400c10804048001000800c2682580c45690410b00c02c000b8030301480072000485440b03020710f44d00135010071a0002030120519040c5e010744201c403080c0c07c0c940c18000b903400e01742085041c44001c0c1e8010f40401540d031519036030007000754200c29003044814400f0746442c0300814545624840000c0c01030307490303582201c1014000d081040011072807a001308000b0482c220700408a5a06480d21a00c8820b43c0282e407005500c1206054140d07240c42c0c0f10181808442d00b00e1007017446129013030b00b0510b2008200400000c01c420700c1090b4000300740000344828140754607043d81c507100e100041c00600320104006c114061300450002c0c111200010b208074502d500800100ca82d030005414a0000345e280c0f410001500440c500c2940105031191220420701c2c141004d129442554 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 314170026 1250 314168776 314168791
    0x270a0920040807050103050c0c06010602070e06040b010c0323030c04180b0a06050f04050a0611010c020106051c1502030406060305190b01050d061b02070515090a153b040203 76
    0x30f100501695010b500311030f0700070341c3d07402c40c161404024a918904108003a044600103070800c540802c005284c07480e519400030001c0310104a0491842c0002e45440d04800c001400d001d100141c1030020302410380c20700300c2603442c4800e031591391a11a086110030381c0030f40a1095002c2105d20025010001403203080f0342d4000c0508803030811070400c08152019000341c840c1b90000d8204000c00b06468071441007030b00041c81503488495106404929503402c2d2030008052104680c5016004c1041c1d94403240c10800005400c80d048441140c0b070305004400d1448401c0d040c4a080c000407c0c00204403640d03105104581c092029a800c180c00b0400c9072030340340010180030700090403179001413025161040c459200d1500c1464002a00d0241846100107603501840040c05a000300ca020030082c186802220302850fa43d8518034600700200d80007138215041c50196001545499080d9900f040c0142c1965160100c0902048403240c0321348030302c071004991610252102085e00040040d42c0c1407500989010703088 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 314171276 1250 314170026 314170033
    0x216030b010b070c0f0602060703061202030a150204170d1e080a0c1101090c08010506042003090f060103260306060702090405011d06060a06080705270a09200408 71
    0x60808102e11a0704061001e48125140490000d811410455608001c000d1500549041e1070544000340442d00545e00c0045016042042880140d0340420019090741c0d222542031128190380e03030004000d00954108001c03000040390b0908010000040591014034141c1d944000e80c1021801c001c000745002507848041800d070000310f01d4560140d042080544a00c0c680244812245ca00140c25145078110070359031107903a80300030311030400203004141e40300d0016141882075136040340703151010311f00101c08003c1e00c0b04d020010070040c01c0c060100e030311004030b801c00b1641e1550312410030341e241303c42c0d040c0407020200c54200500c1700c10200310107580c80b808005260609040c800d40034002d40c5000184203c030303070303560b2000341401601c9049414409544400c1c0103094030f2170810240001c80485403c12420b000d0030740700b00412240c1c45000c071100320480360040b1182011a90840220780b1030081010b40c40307a8180c40225640b0341691000d80b2007680b07101c803624495404904a4600d01c0747d40100c104030f40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 314172526 1250 314171276 314171279
    0x611040b04080f0c0a0605071a010e040201030c03020309070e060a030503270f1819150603240312110a060f0b0f31060909050706110304031707020d060c0216030b01 72
    0x1806130018204071070254400709e0741e045031b40402c40c0b00440d007608140c000c002c41d401840190f50f071620440400c000a41011491400c1964006540d01054400e1001d0320a0000004655407591800318000390b52101c01c680c1c031950344000300c0b483c0151701d6181c2d440b118070a0b90380103400c0c034050010425001c2c010700054001c1c4c07111110701d05d001c00010854840844141902c2c0c81b9010184240300945154002a801d40790a2100040941c0c403208100a42c000d100c000440b08111001c001004407580051303850100c841501c0140c4814141c15824100d9000d0606000d0074808a50030040181f200443d00300f00d140752500c20000705020b40c5c0302547c0c21640d40150901c031528809244c3c000b00f400f951044040b8803840c9040320540e442030304501078079500c884038a410003104000110280c4010706054420041040410740d0f24091484043c0164450051100050305080e0455400940107441000001e4030f50400001070004d00c48040c0041c07080324004412040104985001d0b6a130001100c502c0341d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 314173776 1250 314172526 314172539
    0x5180d050921061810020408030901050a11011811040504050a02040c030b09090d0e010207080d05091302030901060305060a0e07150e06030f0610050f070303090611040b04080f0c0a 79
    0x6011910070048403207007024603040205000c004691103030680b904c40d1001ca84406400b141050a0b203000c4204113030050005000e207800100580d84960000e11f08aa1103240541040382d841c00032058400c0154070b40a94185194420362007441c1d07140c010000e543c0e514405605200484608031001707045d50f0400d01d9118010329041e005001c00c00000c1c900030a01c0c0c81d0030030003e441401c007911a20560b41c80b070310900f0703051030700402c40d070004503400d0018000c02841c01084c185c4400002046a041150000351158241e4a0040400c008503202908540b2442e1034948580240050f00056840b8480d000000f01d08205a0040103207a661000141ca5071500d4040d0b0044403030000c14800b0240701c1d4155180f82d41e629404042c51185a40030780c0c070540c0d82410030601c01504840c1d0185010030504010b400d0560301d802c3c0882e44070b69414640001c1030807007410000000c1c1080700c0d40c00744440c80010001082642e0380701410035170340848155404203600050b056541c2e19044c408075007081d4031001c1048031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 314175026 1250 314173776 314173789
    0x10503040b0a1a040606171005090103171204080d05160504090b0d120815010c0210120608030f040519120b13050604061d060403080115020a06090605180d0509 70
    0x281c644070140d4501110301000060292051a08520005a2001c3d00700c1440050034107040d0700300183e8507000d085d50341030802060f000032050101400715840d0180e0910484052011500e07480e000d800c0e080b031540fd03c7e00e0b00700340300e03481a4a0246200d041c40046030000d02c85244404050406441e61417405261000d004090107002211640c030003602260040030588200900c1e9032030805a541c00444c0c98140a142803041c1e66101903030402c04074400010068503007a1500c90380389006d080501325080c105411343c3c0a040e0a4000100318000031030a000d1680e1008003900949204451301c00503010a0700ca00f030460508e900c51081d5000c03003000c0303040128045035542508074011200d5400010310300e49a00c0e1908106840480341c1641e10121400f1460851443c0742c0341c003850901074616800c1c20340700140302c500d042c045d480c0f0f0034009a05a8071542e00800a1405903a4460790500c50038100c0c1c2050b100030041214525503581900d5000d610004010a048601c4480368403803608009841c02808034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 314176276 1250 314175026 314175041
    0x20c060d0c0309020405040609050618030a05030619060f031d070b0a360605070c06030e0f01140f010602030403051911090a0b040b03010c0801120215180f010503040b0a 74
    0x52581e40d5103c0c3d0f0240e1118000c1c107101e20300840002c07840350000e02c0c25903d050401441504a108011401c60303912002000715200f10129150654407500d9080000d0703000c01c1d56070300700202c2c2030510100181454002c007200b8800340b940d49040184110a200c0d031103030204400d9484620307800c00d00040c0702c040c24940260046500ba807610420b0942a00441c000d051415540e92481c02e0303040b404806005405017844028000340e04d001030a06502e41c0d10300036010001d006000501d40c69100c0b1880c6c41904002c03441c42c00344418000c0c02070071100001c0703601d17850b003c0da000508040340c803001092150000040724102c0f9030200050407130419000b4040c1c52004a404201e6140b03612034039800381c543c2c0d90481140200381c040c00006010701c4000410040360740704c40c0002e0099041c111194440e54001506504550308809400f8002c02c90740700240481e447c05544400d50600402c0c9428100c850010b00002e0080070f40b00e0400125400e001980c45010854000748141e107448001200302c1d1141c0c001c001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 314177526 1250 314176276 314176301
    0x302031504061103070e040627110d090f060e030f04060f030216110a140d080309030d0509061506030c030a0b180a020703200613031106040b0405010c020c060d 70
    0x5000200f50844100c9a1080c2c4141000407a6151080ba0f185031a00c92800100329642c0302c00040c2e0446003070703903500407801448800000e59030300c5034440746400381081741c400c1071207141c0c02c0001280904d44400b890f4100501900d076203180c400846040080007080301c418414400c0071604041c50701c84c085480240703841060341016024000720320b4495070ba81440e039410b0b215a1242411400c0c1c5800e00502e000c8541c02004542c500c454040040d0f200c060300d2681240e0071100c01c2d40c0e01e43e140d20590f495481016030303450786030746460104840d515010690301d0041d0f8650880c11416400b1030208a01c9004c140c54802c4206810808101000c020303a2142c1820280500115403408464441f022604001c41d44a910142c000640790101544140040d04500c85c0320614021007040d9600ea66451030300a1499040c0b1081da000b030802d040c05000d0100603d14203000b114880c0c07030149020902940c00b44c608030358642c02d25071748544080c00803034031039032030403000d40b00504000c0a0080103024045818644 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 314178776 1250 314177526 314177531
    0x30807140a080f07120212040605090607020a08032503050301141f0207050f2202090d050a060b0f01020d020d0813140705210304050d060b10020115080106030203150406 74
    0x200c00188100e4080c00c101c03c2010701d40c64460072541480d40c08200d21354a005d0440d0070a1904683c5480c1d01d000351403e6034081d02c1c000c0d88408146000c0b81c054450508041c3d4000c120110001d06104000002c0c50040782000703080180380742140c150044d920098000401281781407006200c41d40182184500c8440010302082142c0101490300c289100301d000d071440160410001404a818551066142041d0695912440a9a00442c0070440202c100c601844c039400007000c0c4a0703595200019500e040d001400c1e141702044600e40940200058000d042c010000200074a01640c00441c0c400810681900039000c42e0b1002d01c0112100f100061040c16031030800c10652010502c1c0c000d406d503200b00f0600040080e142030408000c2c403403500004152007008814006c0d001e900010042d107040360300c01e503024500f02b0942e03c3c10034051b00440e24115003000350f80d440c5019103a41504650b400119000c1044109901e4184042c00c3e101240000394142e449808180a40808001c0455006010b00c400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 314180026 1250 314178776 314178793
    0x31a130204060207060c080d1112040c050109080c030a080a05190203040503010c0302032208160c031a0702030f0315040504030e0f09060a0b0c0f0106120624060e010e0907171003080714 81
    0x324a00150079542334440f444004806d110300d5802450341c10140c4031200061814044540000380d5603c0300807402484c100010401000041c012303000d41d080f1044120b000d01c815040f00c080203640ba00a885a80d1096080c140300811090182c82128080c20000c3c0d80346c1070749a120b501d08000c2c07500b664000c94542404115256110029041841540d8403888003115100d1940c10a540440b41030f110314144400030381c00b400402c580010490300d030710045d043e00320349030740d50115560201c4100c40e030201d40042c01c00b03003080101540850b0143d012442250101021074059003031046400c41120090f40280c059441442000c60f840068588000c5000c100e4082c2c108070300e682800d45d14036502021407414a4800030041003a14054489080900e0b055003030b40800e4045a0702140350644118400c3c0f241a00a000a0740d225080c1c0300721600001c0c0c200381a50800940041416104005d51003081c1c503104003095118904d598a80708603030b081145035050819644504c07180c8034450703050b54080d200d284036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 314181276 1250 314180026 314180047
    0x70c031809050c0406031b0c02100e04050103150c03061a0f0d0204030c06020d030e1f0f052e03050309010503130c0b0901120b0907031a130204060207060c080d11 71
    0x42c40d100b504840300d415100c41c0b52000c0074094403030220079081c44001703036007a025030b10fa40a0100c0f60f0158040311214003d08800205807542d40058104a0f0414100400030007840900440200d0300300c1d4200040000c201047c00440482d2480d006252410f0050040034403203c2d568030181200003410b821040c5000004c00144040780c2c4180d00480f4040c2d000340080210395010b00120a841e400c0d818103001524400c1980b64075020303140125a49001d49202c070a5100c50b042c0d000030380031980c003001082141007040542c44200c00210800d07440910122682d12a1141c46800c035044030740c001c0085051a98000065905410040903142c055030036a4a40d0007040202e81000c005001440c50682d41c3e541810004107800f80b8000500506802e240c1c41203142e40301c4000a5a00c560756240001e039000d0500c01400780c0e9820f000ea101c5e84001900c40032588810721782e0060080316455001c840d5855600e0005503408401c400001d0181441401016500304c3d0136000f0604400000002e540340450f0b225 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 314182526 1250 314181276 314181281
    0x81503010228020105061c02100c02031e0c1219111003090605160518210c041a060703030e01090b0703050f010f05060a050702030f03040b03041a070c031809 69
    0x4aa60310500342e000c0407059803079028072407a5088039064800d4070388030030403000d40e003c50300305184000d00503903402d00c12481d00ca00c2100d6840c025a40181551180210058582e4000810525604860040300034440c40361a0641000a02c590705402030900c43c2103085102006590b541c0007542d00c06105004400d455898007445206030b41d4507140060701c609503040000031a40c00501e602150541d48185001440d040000d0b104003181c114002c040701104070020030032004108186c08200e1404040141250300b012a030085e2801056808200c144a00041d00403000c20040d11260070034410041c4e040401d20a4104c00040d8600c0c100200d0b1a612590701c84801000448808002941d140240034240b20101c1d0128010044180a020002d003060700044880c030620480d6028860009803035021510207110781c031610a200c409072034445503280d1710102d15500488046400c800ca4090341c5000e51181c800d541d020344140e644981c0ea41c4016078040d10000c5030703040300e10803041d42100002801200d50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 314183776 1250 314182526 314182567
    0x101a04050303040602071707050a051306030210030c0e030a1e171305031509030d020711030604050c0333070509041109040f06030f02060714100203041e030815030102 73
    0x151300070806c0600e4841c0884c90030070b0340070344900306400a04040001c1d07900c810060f020b4400c12103041090038511030b12100100901d60000b9000301a081d01b21000d190154003c0109051503203601a407240200e04054440813050b0f4010050440b91504000f000c19040707025940e988070300c2c0b400401122403038480200303030403100e642c2d40420b03082582031059041c288000b241c60300c008a805240d90500c000202e4803401502110013443ea40801c0000600c8244120350102400180907112a42840e060064440c1c020000880c0640f060484040c1070754884d501c650761104054001b201000748c51180550003040150120341040740c20301454a45585074890a00e200d001c1d404455a039401d50760a02040c2c49010089051141c500b110410101d0391302c1c40e242100d0365045607a295142024a8413041e052a00b0310300842c180b090342c005000303610090b4015030066000e1507080b00000358070081d848080c0d258207030080009102c00040384c1e203070398074810300c28407000e0060000d4207201152010040c0404803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 314185026 1250 314183776 314183789
    0x20040f050d1709182a0c100e10020d0b0414010815060103091a0406060b040608010311010302040807060302041a0901020319020f16140111030a0f03020d1e0606020105101a0405030304 80
    0x6440005c403140719107241882d240e078181c021050408100030322568554420301c02121280b612800516000e01040c45000d0040143c2041103450300380e90034040000744606050280660320707080c0307180700400d416000c640c129a0708000800c2da1072680050b500c41c1145c045e00359070502d51074034020f200184006403d4803801058040d50ba82e945442d05015003a203044e83d1080c0c914450810040c8045079008110300d040d070750050b410034030914451004800a04c2180e000000c103024110010903259810740080007180c651042101e100d42c640a01c020b40c40c402d0001450140c1e00811848042148039003024400f2412401a218010300030300c000b5041500048414507540f2101c1018000150010b9600e01050820700e404050090450304055480c8512540c82c02800420304422016510903011202510ac00324410b201440c0345010506604d80766020704819182020400f1880c14814850326105200e8110780001e0f0320320b0702d40f140304d041c445901460310403202040f0108a5450410080004244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 314186276 1250 314185026 314185051
    0xd0308071e0c020f03031213031d0109030321020c0102070b0a05070801061404080a080a03050f0c041202030114070903021c050a0b0601020120040f050d170918 70
    0x30240d1008060124410a10960701e801e007041d62411a40149600211a41078540c0070000208100103031442c0541000d0790156880d250030044000e00c2d842400756064425160701c0b004c443d40c5299100301c40441e40c00b80d030004036009000c102180c420740c424050301c232891100312849000c1c942071200340d07442a40d42031280c0e900000c01000300f00681650341d901000c104410401401c010600810700a8184075100400a2138280c4440002e0460212307401003003c04121544513809240100b29600b00c81c7d90344011a1601c0d00141484a001350500c0c814070a45400c0d0b89068140503410340c40c2b03a1840c0c0140c0e007543d62103a00c070500405180e2558084c032044d03100c00d41d1b414507610402100b5141a0402e402d1013a4600510000410010b0740c0000c2d990f0014005549a1798140102d0040100c07541b500d808441c48001006c035020110024410344160702c01c04000130703031148180401a101c002008104050701d24049400400c030720054411020010030000000d40068181400341d881a00d019100f400d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 314187526 1250 314186276 314186281
    0x21e19081228090b070309020102030d0e07030312020c06180f0a14010b061204020402031506070f0c0f0807140f0604090501060f0c020108060f06160311010501060306240e0d0308 78
    0x40010450140c03140402d0060103801c3d070f10340d6a5200c408015145038245521180c40d1411a80280145e43d4410340e00e030800c000f0001121181070740c600084c88240c0104182169210740e0400c18000c42e648192604003e080315250411028080c203951031020a5031302030342187c4030418a013440220703c140c0c0101c41068801d580c042010382121440c0c02d0075846100200310004040c0303006100554400e070119801622a034951a20035189061540d902da404000080c55000308116014104900d81c01103110218250301c03056100c10310001401000e00c250300101d400c20210b40c4982400b08100e202a0208600310b40c0b00000c107440c0d8010750040c200e0a521000140403541e8825401003c190031407501d030015031203580028004100107044940900c600c50a183e180e9100c01c4125403140c040411109a000410300300101028402d12041403694208400052850b2007400390105655007040007480710001c80308510040d8100c200d42500b80442c2485041c1950b03038002000c0346c860700a850700c09562 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 314188776 1250 314187526 314187571
    0x40905090c0a031e0c17060411010e010504030209041106040611010f02041d15120c180103020102281b09200f0c030f1801021e190812 59
    0x710044805070140c0440d00e41040801c1c10308003d150b1043c00d814143c04201c030507091020060419400c1000031090040421300c81d04400940e040c4542d00401500e91140c0007500115400072081c042c1e60b002440501080c405403070f10391a181e81040c4600e091020740848a000b090403034106600042c007040c032124111030307600000e000303070260024902d808624003410020100c00350002588280c080ca034002c1c0003c0c0940c05204040301201c04014100004103191042203943c900f150140c803806000d0401b0000c10802040b1102030590754160050550b220070100e18a0103004203e9038190b1803082c00480c240401ca072203054850b1900418203640c0740d075042282c03050541e42c8854412031103114180001845061160581e406042c5080106588040002d0580e103140038070711840da2007050028000c0b103c82d00b445501daa52a0081e002d0383e01415007082a800c4201302d455101d10240c014030100498266402c0c480c90513540b14038082400c00c00e1240d00f60f100c2100c11120340991300a0748417200c540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 314190026 1250 314188776 314188783
    0x6090d050105180d0f020a030c08121009060803030108151b070501020a17060d020603070504090f060905071d01032c010e01151413020405060f030f0709050d03081b04090509 76
    0x1184c006040079070200800306130017942c504001002604004c0407181000410900c00100c48550500d40d00c0210142003411070300150078070354410781c0809454080300040c4a4808070542c0d04070382d20305010f0410b210f51810bd05040c03280080400020356504100800c2e9088000007401426002c0c0e000141c48a400141c003900700881820301b40090014042040130303d0361080c0c00c8121450381521040e440f600ea03441c09036014060ba0f0403694049051010b542c450700c010742e0044045403100c04060001d904d43e10b20035580440a0814142e00640741d2300c0c07500d01075000360041950b40a500c0404951009501c154445c0c20b0300c03c0d643c601543c0d441e8030b0200c070840e909000d0f074420800101c1d12444000d02c2e051005038541030f4800014000c80c07540807031403402035582d03040e10010070015002a0759841c14031012103030b40d401211a0f801004480340441e80e000e10400e41c0100fa1180030b8000310800300c1944098070006c2005244040304203440100407600d50120002d0002800d002c0c0b004140d5061005004bc103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 314191276 1250 314190026 314190043
    0x9051212040c23040c02031b1f0207151e110a03060b0408150c070f0515130b0105040203040f020307080f07080313060c080903070e060906040c0e06090d05010518 71
    0x1d007882070f0703045104024010300f54020300c11011500004c9100140c0d40030f9096000b8241c080d4560314040108a504503004180040070380301c20142c14040c13007036224640302240100c1e8409003d400000010b0800344d0456440980081001c034a8043c11130100311020081e25524110500681c42c04500102c603a034042c083c12005c0c00c20110903030f041c181001025640c8042c2d546001c103010140301d0101c0c003056914421070b900507030441a85013182c0c40e207007072451741c8540b418100800c0502c004001501460341c0c0340342843e21603110b11107540c0341c3d20300300410010f504054001e4500f000002c24040040e5000c100c10001815040003400701d420030802003a081c108554840e080ca03800030040c100d0280910f140c0740080d40c03c0c0307041c000c400c0065420400980d00409060076010321554001083c60100404054403841040781c295115995030018081030303514000030540807542ca03c400c0402450720802a007883d0602403c4c0402800c09501d4450030349071705540289103e80f50741c40011b10213105015408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 314192526 1250 314191276 314191289
    0xc06031e18060601180b0c010203180705130c02010b130f060b0c06040b040302030c030315040e0a0507050f1c0b090c0303160b07030e010203160201060f030b0a09051212040c 76
    0x700e0481001c001e95195400207060b030b070400c510450f00350805000d03d03070010040d10104020707903140d49106240c24000c0d40151009140d0b44138501400d480005c00144807410b1320400f07021240d02c1044100700070041c103684100f42c401e6540311144e615032034490025071841202c0d0481c000c00c3da01d10000c0e4003000c49072036400c55501014200007500000000161032034201b6072101c1c10301c81550303e81c2030407800c600661031500d51a01002040c008001031101000c07808210840b420003264030481440b998622150b82c00070010340245d03104005034a00403888bd0328141000c2c01089820300c0c2000f0505001414580440b4103034034a00600c01901c1042110700e06d06001500254a0310008422603a10b540100900606c842607100018524034442d410039404003080c0c00c001c0d502c80c107183c40c0c200d00d540c042c001d00100542c0f800b000000d40144590342c031030880360401003040d910b40360301c02030b40e0142400780f80907101845440712158401c2056001002d0361007004904441034101464800781111440d0302c640d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 314193776 1250 314192526 314192551
    0x20108060f1507030504030b0a050901050609190b01090b0a09210b040f03020c04060e040b1f2102030a030503100f0303050a0518041b1206080a0f050c06031e 69
    0x800355500c0e114500d90301100c1c0010b80c6900d40785580703012034a80c455a080103040019240a01c0800f00094000c4c500600070040280701c2030380c4007018004002e5088844590504d003030740505500d000a0361014103410410715100304140d86030013020301c580c1c0c401c1051a0000c1c2e05807404101c2c0d00080301d07924035079a0700e4040c0d42c2d91641c0580ca8803107240c14050006800c3c0000003a140081500030010140c48074000340041c00181d64a400c9501c0100044a0a072400d0520500051031888000c4050700b002c420010341c400e1003030410101d5540c00540028a42003188800d40200242c0d40400803060180e100741d480554a00d00800d2030120083c80d030340300d1010702c0781200c01400044d40140540b40c41003182d20785252514400500c0384035a08050000d030b0303000307407914515520542042d00071095844541d06c8180810101002d010200c0d2041d00c41c2c0140e58020200c030000184040c2150184140560300310790f00820440300081e010391081d82e0030440c0d00e0742844080d40755402c0d40c07070580d8058540c4450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 314195026 1250 314193776 314193799
    0x92018030156310605031c1b1a06041a091b0f12061009061d0414010603020309010b1c03110a0b0a05041202010b0906040b151801030b0307060c0f110d0303060302010806 74
    0x1001f02c01090890141c041c0111410008000c1038081036460019400102205c11444044907001a0032019584103004504140381c0f680010b060312084107620b00301414440c01c582c0c03680c10000c881d1092011030300f00d4210400c807500d080d81070240680031484030003034201514188071080201101c2a4a003204c148084c0f40000c20820703030004000340d001e00411403103041410b051000a00140305501c4052044541e9900100c1c0c9540d0540c091480381c0440c50081110003902020025810302c1020b00000444da900500301c0001d105030708996501e6529821070341038103a00d03962102510303000c82c0e02d00c1025a03120300300814040c602242e440004076034002000000400000700340341d19002000a030083e0f44501900c0e00c01c2d104d107448000d0302181081242d4a4140306c0141c00010180c1c0ca00c0180001d003080e981048518001c0b43d0b00003180c1050b111055051701a0351060707041005002c090303850650010f184c042030b4036201750103440303148a5980003032800d04501c00546000c2002c1c0c40c0c14081d842c3c0314070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 314196276 1250 314195026 314195053
    0xc010f02030a08100b130305010b04090b04080c03160b06031e060609040c0b040b040f0e0f0a0903020c091e0109201803015631060503 59
    0x115880d0382d00e01e181059580e5207003d507155041555a0009440d60000550404102d40400f001c01c16070788900003d0220201d000100001e0b02d6a804000d8002d00c200c0300400d0008600b000208010070308042501c1c106180450f160781030036a140c0d02a01d0801104040191070314041c4150103482005102400800c540c5048492740c030791000340303418000d000d10f20108040c003011409060041404002142c5e6842d11001190a40d40141c03040690201c0483da000c6100d1403442d842a2080c600400400c0c0360350b450700800005004849425402d501402c0c0c800003541d02c51101e11480740918100b10b140e4200141d91036540100141d0040d07030f0132440d0402d009402924206940549031501d00c9160712040c0321344040800c084840c820311762540ca0005200503000210500c011a56008690410381b54959603c0400701c000700c0c500244c0c1c100908032028000c07800c441041d00301c220b01600352001007142045029000545042d0002030203d5007407180030b140b00c1c600445003d81000d80c0a001110700d41c80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 314197526 1250 314196276 314196283
    0x30703030606080f150109030c080c0307080d080c0f070605070503060910060e0f01031104080c0a08030a0f030230240a09270602041d040b160504050d080a020c010f02 73
    0x30045c0c809905440700442841e032040303400e00040c540240c50400100d6403003080c1aa40d0b174000041d00d0090040402c006421140420000c011000b66117070100640c0e12070b00c1c040066805407000280114083c082d0701d02045241c81482e01c01ca0450310f0705036580c1849801c0000f030355402007015000c1d9108010a0207401d0340291140b440e020280d4000707000d051201e00607000b400c1071100c2060411408903000800301c500056201d4000d03425248010000d46840c2000e40701c2c0b01d20550709012503110034184044078070a81c000c00300c1d2415191006e040900159417088080780c00c41483c120200c1c014144a00010542e1a4200c041003210050280c0115540480c0c2010b0b46807203280381140c0c0d03820452149540c41e081e81012644100c5e4a01984170041c50120001c0d00640554040352003d1b030b03842102a1072041c1005d02071500142c0680d041d540b015098250064000001010007205100004454850038910441c0c98482d100c4503071181c0c24618002d1412128030b40c0341d8100041d1162010309190040b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 314198776 1250 314197526 314197531
    0x3050109031809090224070813150f08010e0c090306131104020a080f04030302160c1e0506030a1d16090b01020105011211041d030304060b01020c030c0409061805030703030606080f 79
    0x30f0080c1a258016014002c807036014150001e4040c201c000727212024a15140f59840641e44d10b8200700c0c2c21140c032036104440120012002501080700b41c03005200344e114590485500c41d00c07051210b032501c4014000b0908104056451200ea680600c8004040102d0100000c099500a4504504000100100510304030003c0e2140300c0e417040840c045010b0502ca40c040310084201c046a8030f03c0c8160501d07025194a243e842494160b026800c40d0302920380c94900160b046800041c0b800c1d056445150b40800245a051808d2240110510300c00550400c244810390301c00f40300c50704000e1030602d00782099040e40c00f060340c424116450031006000b03200d801c0381005102e035000180b0792020450303040810018030000d0024031050f00d40020710003540c28000000e40c0b0952080703d09111000001c1d006980d58200f5012143c0d1607040324008100600741580310440e19800341c1c170007007004829a40c6103018250409000e03190341c0c00c0055040140764050003181300410301c5203409041031400441c1c1c0c0c0d900c01c401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 314200026 1250 314198776 314198809
    0x1505010c021305090a150902011d041d2b0f050c031c090312050f01060c03120513050721060902060c060f07030c0c020d0318030501090318090902 64
    0x40100a42d258105090424802c1070400c00590818000842d925071640100b141c804a8400c0c400030003d0041c01403007415903043c0c4501c01455240c586c0e00464440500c2682d4105a0380d44900d558540010200c481c22030150020b8850a4042c022641003500c003088202c03502c3e00411407015041d5071060784081800400d16007a80c4400c1e95150590841c0301e055442d40c0e1040c1c101c00780f03113000d450720380c8145c0d4400d210703032619680001d404d4504010360348116004403400c080e00004010090143d10110b20b0644070b8640740c814841d0b04001d90003100d10070354503200c0c2c06e2040c1288408100007002070340040c0c040000415a81069103031194002240058001e000c99160b105031021900c4240a03035800c3c690420035201d952034204406100c80008803581c8000a00780350f40031034042d011384502424960007402c0350302910000d89003528015150f8030f07010060549510b0000101d2020310401007014466506c168811482d41c40100100380b454201903025440c22a80400682e140720b0345460003402c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 314201276 1250 314200026 314200037
    0x1e0e0f1c0503070c08030a060f1d0708060a05030718111305060a05040b07030c121b06020702010e1c3f050d0f1d0606010f030e0718020306010305010504150501 70
    0x4500070100c405813460000281520720110601c19000340c15000441520942c0e01001d0415940d40c0c400840901d01c40440303d036240c214004202c3e0340380b241114961121002e003c2403072595882011a151080c1030b44481078021000124481d803140502443d00d00c184442c181c1e0342401c4c1f43c86045030340300b2180e20503d0701c110310003c4d503890300300d000d48240c1d00100905181c0c1c40d00c604031402c0c0504002000c1d40c0c12203040400e04c040703d50141c0100c1d2250003502461450714150b405540e00c1317030001d502c0024203905100d50b00711107071100d5807440845002902000300044c82c46519103807002404284ca620002007902444040b01da1100310b07407020401c4104d0076141600c941d030114041c1c8841c4101112200e10358107101502c683d91045401a83d03504049041030012051000c019644407801a00e001740050341c90055140400c0c400e810091004030240c00b40e401d0165114203444070002c104940ca1605034010040001642e054401c032030040405650900042c500c42d00014008040303070041030705210 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 314202526 1250 314201276 314201281
    0x10e0402030a0b0f07020f010c0c08090a0806092a0603060603100918150209060304021203090904060c08060901030210050d090c08010203090d0302090f10031e0e0f1c0503 75
    0x40d41085440b948503040212540b090034098a50000284200e400c0805440707088004007030300d41d0503c03585001c1c1c0400d5441e420515003c2d5102001039024544140e44841550300c041688481071090b60b0188108000034298503400000c8602c0c8440d00352154409660301c60351a08041d12001c0c04c41c0d603c60401c8590a6903942c40105040c2c0400258000c00181484d00f080026401d80c100701e80005203014840d40b45407000c10f40030f888107901c10382c2c17006500414240007140c018181950300c1b410003043d90040c3c030f0910f90b070310700070450031041210140d80c03c071b03180c2111210b841d81190180d50030505c103490800c41503040d42c01181507036501903894010050b001800800705413140d40403015071580500303040d41060396070031002d02031341083e206810f02f4010010b510500c14081d02c00c0364820300b00904011026061242080031041c1c291880005040d10340d0305841c13420042840c040303942044110001b0758184203034603c6140c45002c032580030a0741d05c00b495655040c00c000381000d094001528003d507a9a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 314203776 1250 314202526 314202529
    0x3041703060f220e03090103151a0a091509050414070206070503090705130903030b0a0f0b0901030f05041a1602060604180203070305010615030b090f060a120c090e15010e0402 77
    0x51900c5080f8491071441c043c85104280070210090810400907a01885811150b9080308103181c40b034821031583c0041020701501140d401400b070704060b102c600308008500c0d903901204541d541e0821640c1d0000348280000c1c0100c0c9420301c82d001d502030380741d181805a45032030a8003030354070036010308030b50180040400010030740c04041051034003805000d040d842200840459050141100540460100341400f4001700642808170138035040300d1869162001e030340d140c042c5611455000340495410962205240c00900c2498003842e80124842e8030300030495500c54070b0030300b008103000c2d01e2022040c80c40748001204950014155030880b00483d0300250b0620b0140114020703031003054000b90580a030311000002d110040d4480d008650a5041244c1e110800003c110b0844d050351601a030f011840c00e02103002c5410031040c29034070682c00703411403020395281e9510030507000000c2400c840d034044120341400102d14501480c0030f134044500c020405020440002c4081d00014082d10081043d50030015055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 314205026 1250 314203776 314203819
    0x9030c030a03050a0605031906020a0210060314100c27080f0f0706082701060302150a12020c0d11010f180519030806040c020a080f03041703060f 64
    0x46480421030341e0300d805480016001d80300803039199140d00d00d44000021103081c081010429125400948140302c80c403542c43d40000d41190040b8001c6114002655030304040031700c9004050350041d1a05a901803998911900c1e00c003424001c1c10180703040007800c940703403174105920b5000411f0804104840c4803901100300c140c04050340c040d0f2018400c0507030a860506000c6414268120004155613a00341c407900b050312107840c20742c2c8801700d5900b225041c0400540900f90580345416807000803841035075a400007900203905582d2075a0301040021800c03142038001440d1100d108282c00c0070340c100101c2441e22902c540300144e0703403414001800c0d11071400784001c1d03200030000741e00c5103010000d04c440303500303085070540f48200111114880d040e085146514040b07400201c6943c19a00e0780301c1540c9000610001d807560042000540c0304100d250b0001841c4040135050292203094850385900d040e0070b00305e0203545c2c0c4400070304442404106020075910380d40c070f030800001001e4400785c045410700d407a1b0600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 314206276 1250 314205026 314205037
    0x605040606210606081501140409060e01060f0c020d0f050a03020f0c01090315050c0d02040305030d0605090f060103110c0304140307050d05120a050c011a133e0408100f020705030a080903 82
    0x4540000e400b107030ac0e403c0ac0c0e010505490800012412580c1c80b101d0945d180c050400718040814581c007141c50052504080583c02e1902c60f40c10a85068540e40d500343c0361070b51191086000da085106500503030b01c02001550f0a25109182c04071080c0c0ca1510381240ca0300c1e00380b20307141140d41c0710b070009200c0580100031242e04a070b010804664503a87d81c1080b0340c580d0450056814050304181000441e45021241d142c099200315003c400581c4400005400810b0110715041001006000c030f28490341041c4050401410304480840310040198105420045c20340c01c02c9114038103200c43d820114600240342c1d8060181d2001b170355030f107024a00c003d030b4550040d01c0100740590301300080a28040c0e0500d006c80c480040948001350600011440b400c240c552030580710804428420301701e40e912807805c0d0306003100180c0c0c0301d55403038102161103001c400350f0251300710a0056005c250710303180503215845020005040e814007182004a990303181601c0780720700c0c5585010402c030100400c545000c148100d82 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 314207526 1250 314206276 314206307
    0x51302030702120412050c0f130c020f1f050f0903030c0a0e0a03030e040c0e060702060306060d0c0c0b010803040e06060913020c280503040b030403030605040606210606081501 77
    0x10303204d5641d02424540d8000800045545002c0c1c00002c0880f4280401c801c2c441040080006011003540a0008001c00c090f0b00340c50110310030203c5490f03002405104030b001c180b410920b0130b0302d844a10700b0020b040e910054030541c42c20345d04400300606c41a020003a03907001016100050740d203c540790000c131000401031030101c0d4413840f0300340b000080580205402c10071000c00d48082c4602c51107894140c0d01c10170340d0000c0c5504410104403102c0140b0b4648011644460014100d0b401d200c440031402e0200c034150708000740803134023102131042440f04510310240103044c10002503142500340091382e0b6541d04044e0056000c0d0401080b80f66450387c400b038042e0130f2160b828404544481851212594404c220b150100501c0841d802c0703c0852a91806003002032600140210310b082e242c41008400da40c0700600640801d5559400481c85560358090704004292035510344a0313280c0c0400c090780c403003404400714041061070200b04118150b0445403c591140d110803c1814442e60f180045e10044202442e61 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 314208633 1107 314207526 314207563
    0xf080f04020a09090201021e2404020a0303030c050c012c0f030307081315061505120103080f0f1209070b04030c03060510080d17070207051302030702 66
    0x10130105441031044448048490004000d10880884180590380140f0075490441c100f810417480034080048000180d400d003580028030105941c48000c00b03141d01d94607511000d80c06403054844242841d0000e0000c0003003882c0c150312003a91001162950200e02546c028040c10019030b04c0025549034005503e9501c0e560b6043c1c500c000028086c0d02541009030b04000002c800d1003200e45074040b5524042802c0c0d0601014078a50002500e5200c1045024000c103c6013000e4444400e044a8010603429074075011400911020b100d420403c40e5030020014908810860b4882e40d280f01e04616000c1e50b00d001c7c0c446044c01c6031031040e8803002e420003a61030303014404240d0a43c0400d0f04103200350b0825450070755807908039082208890700503010410001511300644400f450043e848101032014182c0a0708140010b00b9003000d011030207000b140e0110009100b14001c118100100f60340c115a0b = true := by decide +kernel

theorem cover : BRFrame.Cov 314028776 314208633 := by
  have h0 := BRFrame.cov_init 314028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 314028776 ≤ n) (h2 : n < 314208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
