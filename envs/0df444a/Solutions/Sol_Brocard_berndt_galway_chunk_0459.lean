-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0459
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:55:36.762915+00:00
-- url     : https://prove2.me/submissions/b837d9cc-7bff-45cc-8878-456aec013770

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 82374102 ≤ n < 82553958 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 82375352 1250 82374102 82374107
    0x506011805011202070b16140310140d02061602040f02030f0708041103060c0306091005010203090105160c0902040e0112210c140304080c03060903070b220b01090606050c0706 77
    0x99080c04251070f00581445030381c0c0c075112075194088a104002c2954610603100c80e80e80010700c3c99098004108103403e50a00d641c028102c0e0000d400390700103108154840a9150740c0c0d1a482030040c560003464250f4410526500d81004903c551003207002c0ca00780b244099000c0d00a000b62407103000c080d000d40c41107948500d011686800043c0c401e561400b80c5003c00304c1c5603101071085a01c034030800d0298966034105503040c0f03e00150002d001d400041001c0000b40702c281e078040101d0707601135800d05c1c4c03150302c801003014803039283c21030100f00400381c1038441d400240512158003d0822144011621002070b80e98076014401855044c0c80101582e24030750b56203202c2c40b03c42060b030b82c412000b444c12900d00e4030b075a52503a144846000400c030f00c07984049010012031208024000041900b1780c0074020300c2c00c15050701e40c0d80f801103440061504001800044200c148070078200b10302900046248810f11352410400c1108070280140441541008408203045000710304490032060081e0003800d4051518104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 82376602 1250 82375352 82375367
    0x50a0201031806020f030403080603151612050901091a040c1e171605010f05120a020f130504050a09200301060801020f0405040c090303020d050a1209060b04050601180501 75
    0x40003508070b450a091804100f0a1005d045100f082d8a01699603040074203014098138401030403a03121f940090a45013208848400780d64100c0e11a1205860142e0b0310141910005400548407448074a00410080301301c805402c101221343c00380c0191076120194402d1071481c110101c2c5c4c05840700800000c200400c40b410110102c01807421521440310340d403030303158070340341c002c034048642d402c0341e0003c1c4040300c1c0504d600608a00130042420900c03419183c0c00005081c6006450112074032243d0b003800542000c2e0180c0482e8889400c81d4400f42d51104c0c018031881c3c0268490241500a40c40e003000904503600b9482000c070742d0741d0040003c1000d18412000004001070501105406540721400064401e0b0300340080d1620700c401514140e05e0b82d06103004c3c407003115005c4517188100840028201701298004c150340c0e61003406864020340e10305101106444c025914001d00a20314a001454014000a6441501c000c442100c0510043d110403004441906507003580e100500a007030010070440d03014151 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 82377852 1250 82376602 82376621
    0xf2c060103090b07170610020a0303020c0f0616090b090f060a020109050615040b09010b03130303060305060403030501090b01080402060901050d1409061006080c071101050d0e03090a12050a020103 86
    0x1804150b028a90b602d280405100340c44000106003c0c0180e0251006810403150384000c09561092010b601190025560080f07003a010f0b0525900046500c0000014404400001c910341c4c129501410312598003000b40d1021900a000100781c03c03004940c0c1d442c0c000c201c44581200515021070320074007001f004204e90081e150341c8107540d80c8407011000100d00344000d91141e0900184204507130b2a0300e0038030098900240d485071255003c20014001401c40400307480c1c0001d4081d0654a07092118941a8002c0c80700d500090524454074080000b010740c550000b40c10303903c00510030301c20b80340300c0c4006603040441607400945c0b100f02403210758215480f9802401011131703a0f02021501a001786818030039650280c51402894205000b042b42c0044004c096070028900b900d00a450342c80d20458649141c055a07074024100121b01c0300e4078070280e00c144180c1f5900a1611010002c0c0350200c06416901c1e4070440070740d0b0150500d81400112650710b4001c0b41102d54000018000c0d0008950045000f49003988 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 82379102 1250 82377852 82377857
    0x10c02061b01050a0b010306122d0c0b09012706030c14040306060603051b0915070203061303020606010e3a03020705040b041109010e12030a02070f2c0601 68
    0x101d5002400e003003400390901500c000302002400b004a03030b0005083d1b03007042d0000c1c90f0f41400801002c00150f8071040700030103504e083c542d0094003221460314055001c8a00005455078401900c0868503110200040c60700c2e810036200d207201207080308081030340344c107044914881001004c01d041000c14003941000d8007020702c515181010300c500d0314046029030856042500c25542c0e550080c4460b0703416108158024601110040d1512034100e05a1014440e421a59016516800e071351054040f0135001e0310052a030040076600c482c42c1c08040107400031000c0034198018030400c1d010900b99401a46c00e030f115564041e240e9070000c442a40320206020450b504410304107080c1808454140a11401b681e0540c407950142103d0b915200c02c000540b0261120345115510b410703401901802200d003104c80340c801c05e0900c590740549080c0000daa06c03441c16014805400300140b002d0210382d0102e10710040c1e85081d4000021207464801100712110b050002400c140c2c1c60020203051340c0c0c46001400d51050b03052 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 82380352 1250 82379102 82379137
    0x23030309042f0c070303050904110409090605011a25020d03020f060c031501030c0905130204060306080f1e0a0210030b0103291009030f0c050306070509010c0206 71
    0x640204084940d0045a14120102e42040103001210b030b20030b04408031031060409061002200c0302076110305042c4802418404001519100d41d2943e4000080c00d00030011400d843e2503964000030b010780444134003102e04903e00070010074200c0d49403d042c010350207240d0310b080c2000048201811710703980c2c00301000c1c0e4401004e440741c030040c0e1350b18005614161081e4042c00d1903266144841c0d14054019103006041320040c001c000c0d10070f00d9060303020100002464086102c024401090310800c0a5070060f030380190300300c200181100d0403500100100c1d00da9031b1b02004079640c3c800c4200d80302d01140c080448560003440001d018541a40c5ca0900200d1806080e200701011a42c005002c0c606440400004240c1f80d00e642d00d01580c0611500c40d401c0d41d070603c01c1c00f4044c012341c540100207008008061040080c2c40d8144040c5200f8005d040145a02001100c810401400c051030045c1c95446050302c60304c908000506542d21903001d881031400182c603140500030b6158200301c0244c120b0320f49198440130b107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 82381602 1250 82380352 82380367
    0x30308150a0f090e06010e04050d05030c0903060106180b040e0c0c0f160f0608160f020a05010e0318061806030c070204092303040305070b030a0e0706080105040510230303 75
    0x20b00c01c00e10083c05248400100e0901d0521085d040a00591010000403404800c00010520102c1c04441e01c0080c0e1500300d5403aa902028901175006580013950540702d00d00000c5602034100c0312003803802280741c130441d001c282c5d41c103a40049403080e802055404010b030b4010038a050f01900c09001c030196400d0030b8031541c88070740c001a8a410b54030840c08910321540c020822000000e0301303034140034140501d004d481600d006e6030b82c03a01c2c20f140c240540c02000540200b1780c1d921403003407028a00b803d030322a0007805a8141100001d03031382d030001451819403940c6200d56038500c0c60b10404072090249404003a080c9152040b0030820316400052000700c1c2c038a03041250301e0060755141310f408019441a01094200031040c840c00e55150707100014210150b000300014000700c0c00010f84601111312000303402c0d6480e650078000c6406440b40c84c03c80c1d9442e116031440440c0c03598000242074162101940c0811040c2d41b911041d441c21141c3c3e2103007190700d45141d03034003c0e2041030007501445110300181c1180d28103100c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 82382852 1250 82381602 82381619
    0x1c05030f040306060f03050c280816060503100e040201020c04050a05041505070507060905032802010e010603080906093f060601090509190216030e0a030308150a 71
    0x100c8038000c0c44103000060180100280340c03203032101a150003a580c2d19050305541e05c0319910302c80648806d2086050102d940d400c408070008140e1114065800090129628451f5540d19032a0300c9803102d002095440100e042c52003403064a20544015030401005440c0c109140c0c84944064401d0307046029465603071080303858a029150044d0b400f408006000d25082c10301c0f9400c000056070100c00142080248090300780c2c40f1081d1451a504654000303850411890314601d94810b902c030452030481921000d911181c11011a00c8160034250000e10030030540801e4682201c1c2c0b5070100501286040c0318644d064184000589008540907111070303412030145101190905448a40c1604141c0b015000603004203080c0200d14a0303400c0200404441c2404d0001030300080300c80c0281d41c0038070000000528980c1d00300d2014444a94070007011076a4041005805004611840003035000c22240700301800e442c20300b00752a90031241c256071780c070283c0e403209101511240c080004a40c0d1200c0d100c400801c010a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 82384102 1250 82382852 82382857
    0x2040e04030c0302010506030c0f061303060f05040210020309130c0c0501140109060506040f09230906060a050d1a0703020c0709060f240305131209090e030901020c1c0503 75
    0x24065141e10b000100149002401e4440042205000b0740001201c440030313486c2e0755407284900d84111070103a1104a80b15a00c81c20550130750000e0050780c1804516108030440c0d0780407a000e1402034038040f07142c54664800340d80d0780c420304014a03005012400080010300359580100030030300302483e001102d20202e40360b5a095034030300c05080e589002c0080041000c41c490b4130030b860050005541090034a0703d03144001c5200301c1a845500ca415031154014903d51014003c48000303644010030601c0503092103094603655940496207280030380c04416011405260039540e4031901584855103c9070619068451002d20740050903582c14503400b8020300c60340764014030010001d450b900c1030000e1b075545481c0515a0f40404e9034807008000601940640120281c9074000408595908001c105030712018800380708440160805401d56601c1c1044448042e4880c40700070031500c0108081c0301c80c0a002d142c203502c03842010403c5006da400400b0303000080c20008440c0c014032456000c407000c00d000c1516500e0669 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 82385352 1250 82384102 82384111
    0xf020f0907030507020d020f03070b07091806060e0f0906040b060c0109050c090105100c0b04020609040c020303070225170a08030c030901060e070827070801020a1106161202040e 78
    0x2500c40013004000d590400908200c01410310040503440340c580607036502c078400d003180034080800c042c00082146000e400c90000902c904102c403032012a20400712401004130b07000382000070301107407180c1d0102d152640c1014104c220080c941030a94582c002000010032031070f007050750041000e1000b042c44031028401c80d00c00d00d0041d00541119011030041061034201600024890140075a0840009502c1880348600c154001007640c0c1d151980e000150407800b038080300c03070b5200e0304041800150b00e0b8040082c500803c8282c0803540d0190303008180010200640d10b800075060341d0303001c041241003107400d4454007414032601555000602030720f82c0c9620ba8411500c90842c044008140100107500b4800c1000401600705090300310f05007524000c1401c000030b080901e800070f920840e1122601440040b5032403036510b004132b4400310b544032542c5010703402110b01400803803c003c04110400b08003203a45071184940103000360003604505405d41c0c2c100300403104001ca40b5824040402c401001d00d4400e03006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 82386602 1250 82385352 82385357
    0xa020c120c0708190506040305030702010603060f06060201200a0e060f03070f090f030c0b0a120501030507051203090d02211501171c0302160b0406020c0f0307050303040f020f0907 79
    0x4007814002c035140307001c444110313560100c0320043c4840d02080000c58520303041039061074096a00d0301d8040080340036001c15000036107440e103002c94481840304184e00880c2114860340080c4100c0000111076081d00d113180380314028460301048107a01082c8071340c00d01507a40350010007035418683c8622101ca410f4000301c42920100c0c0100e1052281150007242450041c1002c00c005010242560f0700e0075000c80c403030300c101d4880402c041038241c411400785800c1c1d00740b030024400400c205e43e03407400e203541d03612345910072140191101400b0780d5440c1e102204440380726001402608028a0590034000b0703100320041400602592030341c521405d01c00c00c0c003c20394101e400100c11041541440002803c103c144001850254460118017442041c031881c400c2400e0080c2c2001130311892420344001340c507001407400805030461182000108031580d4054400b0b00c0740401154064641c0d441002d540e8400d208010309141d0040c40001c0020b071420b0601328410748082c20b000c0c04600c0502c0425041a0140d410901 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 82387852 1250 82386602 82386613
    0x8030112030212131a1215090c040e0f0601030209090901020a0f030b0f10020f070605040305070506090603040f0807230c010201050c2709090a03030b0303040e0a020c120c 75
    0x516504001d03504010480740000d0745070124803100501060b40a01c07410100b010700d03602501c45c41d1400700a0343c400740403904c2800120b1800088a50003040840b91061003410f669000c00c4010080b00c017900c0c103842d525041650142c0764040c5404010000038440c60406408004e9090981c50340f007a900c0c0211034110001d40c80c0d03d682d901c040d181403004c0380c00d042010702d4080d014045594a051860b410a42034070044103160038144100d00f00454540b85079000e11480348006686507000c0000c01c00c407401401540c0740182c035001000918070600c8001c0307511100900114003c10180403441500c24841c110b118540121660303030626582c041c00c001c2240c3c1e44400092100e0382401c0c0506a04e60000744020800c2d0b1814258201ca0b9000d001624001000c0c00e200001344a4501003001c0640780c3f00400f20580d516043c800c0741c0d81e440381410210002030a00f00401c00d2350800205940030b8514501c0e1440e0705a44201e60300009400c03414520160b40304048010a91500d04001410b8180c0c1d200b01501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 82389102 1250 82387852 82387889
    0x14030403030f031b03021c0204060926030405100903050109080306090906040b1503010603050105100f09050c0313081c02090301180b04030c021219060c0e0a030209060a03080301 78
    0x4082d9144881a50241414840806500c0b100c0b0818002c070769005040043c0c485030100c480042e000340103e040d0503070a200150104803030343c100f00040e0441d44610941c0c0f00d114490020085020540031007030350503078003d01041c40a0326000ca00309200030101c0c900154a1590303a2205803d40351f280c0320a44080600001f07100b01e50404003110359014000c0802081607080c07641c0c0361038001070000c00400781e81101110b0150b1580d001c0d0040d130010340c0c00c5002480039051103116241084260700c260154584c10900c002402e403404e0050a1088a01c503688a06507a607815080840c010780113811503159a042010f40d005100400028130800c185001c010707250421030083c9801c603a0500402980500c12003400c2c0001a0300d100035a41c0f00d83e140c6010400d00c509840464040c51072140086a68020b040c0d0200e848160010201c126a010740f0301440004a841e8064422450f1240c01e240c02c0f0940d65000c0c80036003080d0484a400503405080c000c445070362a19003424603003081e08000700c4c0030038907411103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 82390352 1250 82389102 82389107
    0x5040f050d0f0806010e0d06050a110d0b0f03061501050f121302030f010b0d02040e010b03070608060102161d220302070305011109061902030405040f0e070b03070c0803131403040303 80
    0x564810300030300b44186c03203c4000000551a52507080003c02e07071502c441c001084000242c101c64204140108025120800c501d82c080203055a20240c0340281880c1442c00038510300001d0403802621045690b84035540300d1f00045605501640c0c201c041008200000c030721800640c0f02d500d1050b0500f0740d40a082006a1040500307098241000102d141c2c100f42000a080c0c3d2490321034840540d046030300046d0fa800b4000c040d03005d020420105036150040407000240c02d50080034483c400c1e4403d07401c2c0c80ca00b050042c130802c003200085c0121399210340ad440d011051030041c15491074008001805900d0550b44000b514200000600740c114010b070052582002004024090765a44034000f014417400c15840101240460040b40c443c001d01500502d000402d06000384102c03009444090f2080c03200325084280040900304492084140b8410701c0e070009981c0340a50150b90040c181e1750360364101d07541a511200400c3c1c03c080c0c44100c144260044c400002040e20100c0305c0c40188010245448030303c0d50501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 82391602 1250 82390352 82390367
    0x402030c030706051c0f11030a0e07062c040606090303080a05310b130b0f090d0e01030b0307060807120501050303190314040809030106050301090f030305040f050d0f 73
    0x2030303000e03501200080c001c0940040c15a5680d40090b042640d00e11070020180c2c0140400a01c003401542c58031940707109080321800154890400b803441402214440c1c00000d565524a20450000440281c00300303428240141a2071401b424134a8084d4000304000c00003403c941c015448140881d910b002c08004254001101301d6200c07001940030052885e000c4601c0c18400741154100801107102f8282d00012092a104a455150001001e28072454040c28a43c0340c19014001903910801900010320702c0c10035090214072423540d26014144144411070207030303101d0f030868001506260701e82e41c40c0c1c121501c00308520b5000700165039411b000b43c100780030058103a4161481900030709081078010300154400008450380f5410a1020303254420209034124001c4c901d603c04a15444c01c624103110500503044041c6c00c4510046008000b020303a607104140c00c0364212600100f420100e1442903000c24065409540d01078042c004c456a00321107031b945da5040010a0250901080c3e908030900c141e00e500003103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 82392852 1250 82391602 82391623
    0x1a181906020d0314100311030703151a030c010f0809031c02090a050a03030203070b071103030405010b130b01090315020f0a0908011805060406050c040504230a020702060301030f03020c060d05040203 87
    0x5a51801e0803d084400c0c17003041103000140540c805c040c4480f16544007006100000d5400190000f188840100c4500c06806006102c22603800c07800c10320a024038010070782d59000032050f12400c0da240c0d0b0f101f00c19103556034014100b8900e40028840c0d0150a00614240d580c5c000000900580c0da0140404000e500465a0001d90003040c0540080c00080d4001007110f006c29044080b281055840e604200c40c070050303440e8030f05d00d035000c003009100c20400150441042c40d40f0440d10b00c0810200b40b0b80740002c41d1500c0a509000840c0303a0350800100740100b8100600c02c000b070303001614000d9010414481d0b94415541040054514003080018100a100f44015452080780d02c0c0c0d060003403502e403543d44240c0500054100c0c1d60b03600120b02c84c1803044046400a0001074000d00540c03480e03145421028511165880b140c110b241d0006011210610848010355030080c1440c0c216405c5480b002004a0358000440c2988142030f01e03911180c2e120b40107080492001440808e45d40b0305841850700b000c1e035112 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 82394102 1250 82392852 82392881
    0x101103182103060d060606050c060702031911010b18150105030403050a08060a1e061106070203040314150103060b1809100902180a151a181906020d03 66
    0x510035440014111000406120088002501c2c0e4640b200007400301401c200008103084e01d0414001445a0450054284000f0703000a40703400b41d9a400c4c2c141d8170392288100c541015180c449420303490302d02641c0948043e102d0000002140c00080e000300f54042c090344140e008051006040010b2000f94803e080c6a110083c6802170450802c1c0e07402a0440c041d01c10450240b05186002452548408505800400b010044164400030500070540007a200c4e002d0400041d410301e114801e07070b00e0000b0f21b090142c01154021440d061564603011040b03400c1703042003025405071816007400c913052006980d000e98050100021008074100400540304510302c81c07001000c160740c0c1003002000000c03e60200d100d0541c0800300701c0c180079200245185070244214018a40740d0300030b0281c00541a403001d51940080c0c15400b070711645500c507050804a500261040c064810022003000c031b03011219030402090003604090704494242c0d41101c14603010342090006078043c58011400c513900d800b50900f1a82041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 82395352 1250 82394102 82394113
    0xf06030e240708090c03010603080a110105010803090d170310060e090f012709110108010b0313150209062209090b04170c06010e090706090b03060405060310110318 72
    0x148052600500c018000b405000101001a6010b0014403200060000040080044c15181e16107400c140d080000e080000849410010841445c144920790580c1c0320b4800441c00c240303100081001c0580140801c4403020318032242060728a588c0400b42d8000c102c034240c03510465092540003066048a01d81551042d03a020083c086590741c1e800c0c2c25030644002040d14092001e480c003142e402101c0805000c40b0040c9403076a1041800141201a21a581709a0710b2000c05c0e41d0790811001c541c041940c00640e4150008440000241019075202184400c00400741c102449200043c0b4180c00002d141c16030351240b802500b1044e03800300e0012020342640c600401071003c0380c0d11120105103008100030b01908100600070000300901c8255000c1032145c001302d5402c2d41e147c41c5207030614a402d0714000e0117403054280100c0c045010701662025542c100c3c0611b4155900d803001c10000d00006400540c0600407204a205640701c1c078000c02220818a0850710359a08160440480900c241c40440040c2d4104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 82396602 1250 82395352 82395403
    0xf071e06080601030f02041e0504050c0f0d050603280308060415180212180d0f08071b06020a02010b010908010b030c061818040210030608070b0708040f06030e 70
    0x807400d02d420940a1031300040c44020701c200540244070b10307040314141c00b160081e6040550101c01011041c1d4005980900440d101c0503e070400b94026903903a280302c00000c2c013510450100310340c00f050380110300404554440c401101580c42c064244c2030440d20304055400000f080c580c002c00c0440e081703078041c0c40c1004028104440c2c180a40780c18004c20301d5200300030001d14500d151903010b851140083c0c012241090800b00210a502004559546401c1c040d2401c0020414094004000802d0302380d22900c031386a8541c242220341034000f22440d9408a07240c905d00e0003089951002d005248403940001031400c241030000340440d00e5a41c0f1001c020b0b8100810908a520b01240d02c3c01102c1c02911000e1f00e070120548400380d80d40750820320a4120344c50307905c000d01d03e003c0d064290340501e0003503034804c0300054074000480555120303002e0315040b90b02080c0c04004400c456001001103501919159007815211420008403413030b00e0384000006a2940c0d05040e40e00c4040c40707001410403a01001c442075001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 82397852 1250 82396602 82396607
    0xf090c1221040b161203020708090603040203030712030f0605090606071106040b120103060b01050903060408031b03040f0201020c0105031005010c0309210311070f0b0306120f071e06 80
    0x20801525044150210703003490100c00d001d020349002d40001c07244507071900c94200408024100740003090b40c0e013020f501071850f4000d0080c42220402d58200900c1460000d058060200b01d50020300304a0305480b00708004008a0003460000d601070381035540103d031404200300904251030883d00a588664252030500c180c9580d49000c80303003e41c0c3c1c00b80342454205088400500c0a008541c04800026000a0b1191000a416803ea41600c0c4075460800140708010011075084c02180e00243d01940b0550119012840700005035500c0050f0419560400b00210001c2240d90400c0d20101c03190502c48000104543e014040031408100c03c1c40d045096213440345080c428030190b441030364188400400070720207151040400340041c200c0310303c0820300c11f16111003510100103110030640005210b2903420301104030220702a800c41d200e070042101c9080c10014554181d90002d003029070b0004065188a040080034455541c01d0400b42014005c081e15002941c503528115002e02c002d8400802d5091102c0f03078 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 82399102 1250 82397852 82397863
    0xc050702040b0d0b0106030606021902010f080405010b0409061508030c100908041508060a05150904050a02040306050f0f07020c01080403080a060b030c0a1101050f0403050c070302090f090c12 84
    0x3a0100c0300800c580d0291000f042c0c030070040714000f4080c0c00048002080e2a9095041141241c42990880300300d400c15180b8a1041315001da4001d00240e151546201810300c07a160031504140510b0000032a0400e4500003800c87d04545022100117888880c86004018844614002403840704090361400c0f008442a544800a209804580507951030b00785007440680f106481c0509130f254801a01c0551210025165581c2101d01038440d550205010810b81054800c03407010b842a040882e0400802c14104405000010009c4110a600b40000004200a0b004039406000c822107001038600381180700c4020310760000c0c2502c00390751010b040c0c00c0890740d10002080c0d1240c2c15144c0180940c55154100d0090402070f480440c0210000c01441202c1e100c204c010300340e81604ea110440e00007240301e100e41c02d0700d4045444200300300d106400100424002c100800c8015946003e40359101c0e1070b980014140d40066405101440000007044a8044200402d00481c0d2048403004c0e030b01d065144115036200b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 82400352 1250 82399102 82399117
    0x60c1403030402090412051614010b180a1a0d0303050108070e090706050307120e010b120a05030f031e100e0a0b030d11030c0a0f020a060807050a030c1101050a050103020906040c05 79
    0x859001c45903541b0144201d043e5003081111800c080200425414070345001110f40c0c007803044071b511f0300c02c04200d60700c2e20b07030405011000b2070792a0049a0750782c00900b4004007041d03100300c0551414196052040c1e5180107410660511a80b0000b6895041140c1d881c50020300ea0821141c140602080c0040428005030803800c0f41c0142c80d009640c0d60b030300c02049415901043c0c1122405051840b03503030b000203040d002882c01c6101a81c0040c000c0440004444d55004880406405c0e03400800000c0b819030141c00046074440c62181541d06142480011407001400465954010004e04001030014450703640d405034204240c0b4606005c1d01005200007601c03010214050310510941c3d0003085488031050013642d00fa62680310a42d084040d040c02d0240d1038480c0c0400413032040100d1030010a00e0303409054801d001d18229a2260b090071840705068000700061107150061100705004201881d0090146912a0503407c102082c00d52441c0305100b01540c020300300c64411400c1c00860201c184c5e100041d1903c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 82401602 1250 82400352 82400363
    0x70620100902010905040212070e030a02060301091814100b06040b030f0402041107030509040c0512072d020c12010b0607080304060902180f090a03090b0a020c0604060c14030304020904 81
    0x45007218801640c44110035800300b5007050003c100341d0703418030001c1d1070140316102c00e80307440e4403020b44071040641f0307141d84046c0207600490034401442005002d902c000d00d2400c12042c45458003113651030314480d2420415000c846a44071030f0714045482414000c04c0b15540b02507404600746070030055181c825000007081903605629010001e4290340d40c54110f0002c400790035829940d02c1d0581d04009200c5c1d88803075101ca00036428421080071003445082201c24800c4680b8450788151500142218400d0011701600210600c01e41e40341c4910403d4141100e00040c0d075001003404801000031b000c0c08004104041c0300692400c1503024464440303204031a5500d40c451082d41d5130395140d20b814802810001c401a40002d51400b101e001c64241101890146101c0b00380000c440c3d440d0000c0070358a160810008000400d100c908202910300c05014000845150058642092031400401c001c0e030450750003000086c00c01d5001d03c1c01e005040d00d04080038103404024501d107290680118040b1080a0301c014072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 82402852 1250 82401602 82401611
    0x216030f120c021203120f010f06050a0309081222080f0c0a05150402010809070302031504030c0b0f060a0812041509030609111804020d0813031407062010 68
    0x29034402d003401968994000d141c004503040510065590750800140b00c05c0f1a00460041040c2440c141019030488030b442c1100842030b418040b0803941d5400041a00013803685581e0f070400004c902902501d03034400404a541d420b45450070201807007202d034000b0882d4104443c0790740000700b4980b0342164040000e903000c07a55500c400300210b500e06941d1300c1005d0064050002d03841a0303188503912940c0154001d076510040354845a13405030300c600b10b80c400254141d1020300650740b1503000001c002e60282c0203080c4046180d820740c5030361018100440b81c0090a4407000c04101d43c41c40c0c800010390103003c4080003001c0540101c01d030480c051040d0300801c9d20008071803001e59042c0b84520180400345500403014007000e4210303d408407811170303184000c0c2c1c450246840554036400460300a0b921a580041841c1010080c2c0d483c1e0b2921940105000141032072030040100100f0340e0240032100c0c10083d1401440c0e4140f4140004019040300710058924144010104240c404005090010300c04254000907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 82404102 1250 82402852 82402883
    0x14030907090e0f010204080f0105010618051005090603070c06050a020702010c0b040501020c10020a03060603110313111008090c0a0f090509030412031808010b3307050a030216030f 79
    0x140fa0808038100480e40c1c1d07000141c080b800020204144a103424107500030b00850b600c4102c1583c1c10340011081c5585081000e07400c00c201c0c98409181a000c6c0c905007003180ca0300b0550804140203030702c00c40d0050081407800c100002045041d10036107603c821501000c60815201da40020080e100004000d04044820070100d414050b00b9070403142d1510400044401c01000520f4101c043d40200b850340c1d02280c64894002820b0740070303000b0441070700c20745506940f541d40c8a1a141c0c08068010340181d0750110711340d113107161607118100501c03007900039a1070798031040c9818900700d8500446090b46034080e0351078481c1004490041c65001080e100c1d803482c040707001e5807006155495802564003010078840ca10a13100141134010031040c0d80c1c03080304464000200e03218110142651040170080380c0040322880d0b00300c4a80c10042c0724040c00724900000c4a0404d00c01c0a00403d02d410051064480e030b00007000010030146c04010003d4000700c18614400b00d02d245445080310307451000d03800341c6940940030102 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 82405352 1250 82404102 82404131
    0x14040f0b030105010e010f05060f161a0703090b0c09060418091a090d1713060902030307060209030f011e0b030a21030f0506030304031101050d050103080a1403090709 73
    0x409041601070001c101542c0e4035032003200041020301c15041e801c104010b002c601c45c2052011500b50200540a2500d88080850941005006600140e4200b100207540703645105240f542140250400d54010400b0045410700980d44003014203015100c880800c10040903071140c00c01c0e42d08842c01d4860200344003405d4180c04029114410700240f1042c603070b0000c0301c92016046449402840344c00e04448442411100a03112801c004124680344601c100020720100881c07500100d03801d1042801240751011503002c01e01e5a00413101c01c035461500816540300500381000b0340c1c0e1041709004000e0010070010090f000052401e89a6004000d455003801004c2c0e4030108540101240c1c0a500c40004487c1d8003020740500c05010b00c0d88000030304003116100c4404840c0289801440000e01651520f4615071b10a4a14284040380da414030000703001d04030020300107206007030085002c1e980b259a1000c00000007080d26801443c03141d42e950043c018881541000110501602c006550000710311003401d40130b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 82406602 1250 82405352 82405361
    0x11b061a1c022808060f190e0a11030106031e0203010b0117060d0f020907080f0907062106081b09010b0a05070209071101150302120a050607140f1b0d05030114040f 72
    0x70084178421402802908114811003511503002c40c1001c4802081c0d906c0814280c0e480d00c11132036500e9208141280106d02802c8080f13100220040001445d1a5a5541c89000300c00040020300c1100f0882c0c3c01200b5401c0a0141c1780051a00b407a0442d002e01d80d895001b800e000b80540000c0c020649034400404000300f0002c0c1c0990982c0040202071a441c02c184000c02c0c00b48101c901442c1340c019000415918080000c91405483e007648400f11001400d100d0780c8110120b6044102d1a65280d03400060740a6040c0007484803030140080c0d0a2174075051000748003050204ac3c1c8000c0c980c140411454039940d50003016070b002c032a411500d500c1c940d00c44110172107004940c10900343c015442d0102d042e5103020004210001c9920a440b20785100b02801c01085c0c50348a0003002038400e8000f04005140035202e4541240d02d1200401001d041a002509111030b5400c54000e0b09080c0d401020440e605000401c00000c50007414500a441c41d81000c100b20613042500203603900481d1661000c0910302e2241d040f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 82407852 1250 82406602 82406609
    0x91502070f0609240203010803070201141e0a0801080c090a0209010c050d1205010906030b06060a090308130e060d0809040e031c1e020f0405011b061a1c0228 69
    0x700f4030101d02c440c202040c507000b4a0341d1101c1d00d021201040188160b590003131341d0407680100003550034104140c0040d981c61070f50304614001c108040048507030b03075145401401d4400d064450a10340712808100d02915000040c1c1043c1c03400d03400b14240d002c0b40d80c0e5110f40c00303a00102c150300150300d071201e00006a07521b00361103000a0450081400c55034006a00441c1c00941c42d95140c3c0500442c0d903600300c4d00381102c2c59400098000032034100041e9007810a03500a0481c00450315000f0b01090b6643c880e070100ea0415440509a000300d0001002240300b03008000f60405001c84948005259954900701d0520800507454000c40d111000e0607582c80d0248140c90303c80200084a825545045104c40300070f002005803c103480740030404803407010500b8401da038180d4520007412407a00781480019502200714000b80600803546200c80340c0054440c1c09a05640350b9021015506044071030108080c019420061140c0003800d1700c0f0701000360703450007003102c080940d6100007140c20604240003030101003142c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 82409102 1250 82407852 82407863
    0x8060105011824031d030c2b110a0605010b0d0c080601020a021306051f030e0d08040609110d0303050901050106231602060406020705040f0506130e0f0a0c080d03091502070f 76
    0x540c0c5c9910714000300003818442c0740d103070584649104003150498241c0c2e100813603000d011800c2500e82c84440c0903011411301d40d04080f0071100c054003ea41c5203000e869090b0000c900c9544041400b040d040341c00e000710310700400d07103003031001c0f540c074159000075a2800d210b80060301c80d049919400c4983c000d10340c040b0014240c05013008034a14100c580e0600c904900d0b400003c002840c0c2000c600b6200c50210b050300720400241d1320000c081d12a903e800000d003507601e0040e50158079552a1406c1c2e50b451a000b1204148241c90224803468610301e000d085034016403100042c410202010513130380202400c0c9036007101e00100c40e243c80701030320800c5906000388cc54000b9081b107000200800c01302d40018144048074001c0b601401101000c0180d081910320682c2c01b690440b0801d2443d41c101c1c0364640116010400b0034084560102c9264070a5141031031b04d68040e543c85074902011312594000b8002c0d2850304800e070030706101405041e5900150080c0c0040d03450419a404034215003008246403c0540464100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 82410352 1250 82409102 82409141
    0x4080a020d020f040e0307150b09040611040b040909050f0d0203070311010617030c01060501030c0c0206030615030a06082116140a0803070f020a020105090f0d0c0806010501182403 79
    0x3c000c0c60b546da030310076003003550010001b00602a04d20094018014258401380c412402d40e10761b50b88400140910071260101e6103c10b02012801e154544054401842d11800c080b13990f140310300304039061201038032031411a42c016402a075909078001085452050303151600388040d2035105003980c010580741c2c021044c44d00382091140080c41e0004050007585031a24001c2111660319401542120764000411000c1a040300b503c80240c0781c440003455000c00c000c1c02302442c41d4000d200e20707031807071340700b120001600780e540c040c140b02811041001d004402c2040202024900d0740b80790f20440750180e215881c51030000348151314104440502000c040b01c00d00d00403503808001070300c0c01d507103a604100c5a5000080c6095524041030b440001d0f0f031482560103842d02450490000207006441d10003855041d0040b18490300301c0d00140c00201517070000e0a10070050a200e5040100041c100010b648400c0d4000107070050034003080c0a46070407034168261854003042c41c001952015405002003068506003090030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 82411602 1250 82410352 82410371
    0xc0a0b160b0115020601120203060105010302180a060f020c0109050d110a080d0306060e0306070c03050903010b060d021224040c030e010c020703020a080106031a090307050a03020d0e040204080a020d020f04 90
    0xf6500c0c5000400344a03000c1c0c07681030b031301c40b603491611a10001010354994060b5004100e594000da004200c0144e41c060058415030030400415401c07245913201c0c8000508100e00d5560381c6906105954a8000c01d02e800d1040e03070301c1d003400a0902e042007039000c1d202440c2800700b14440d07500e4044140003880214107503400b1030303a0303140064010329030361144002055620f01c0002e018a000310b15107109514030384440003440a251000c640301c1d080015807a4042d0340e582c9076440e141ea2514050320101740041000740c1d94483c042855442400040e25207014102c80c403d0368489542c40040720711106c50107440000d0030300c280c604110041c0250510b04034465180c9100181000d50109100741034a00948441048a5441c0d008034201c80c42840041c000c2c16414581c180b04400001c0c645800181600480c1e040691689a050608000c2103048001da40070a1880315240d0308425041c41c039103412035045080c140b03009085a25000c42c44002446520000c030908110750b10100d070351143d40c90141080140c41c26 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 82412852 1250 82411602 82411619
    0x403050a081e04050117070e21010b031c0305070c061107120206061e030c1002030307090519060f030e03031302042a0507031101050a020a110c0a0b160b01 68
    0x8a1004032030600c54990b04800e0b02010b03841110304a42041c0d594600c840d007a00113009642c1d4001e0552001c05c92002c140300d40c2c0f5a190168102480b191140301c0918904040c04ca41c2195101403c0134004e030480f040200c8076042d4200682281909400c0c081102d41d2a814116440380010200400ca00e15146e003410b000d00e000341c050300083d44070701e00b0705002d03041805081c3d940b68000c55160740c3c4030385010429040e060b01140c0ca540d101c0405070898002d828641d00240c0c00484451041005034004820840c105610040e200020001664140c8036000c212200000703e680c03a0040740709100c8141d281e21a420310a0b0b0004808448082c292030300c0703060811440c005034001c12400d034883d0317040541509007504040e070710391200c006034500c1c840e84011011060b01c864000680c181d09119500b0702c0300b5030700d140c203005c0d481c413035548600b0059594681074005420300c0e07a0b243da14501544620284c1c0c0a50716401068415510920340042e1100e0403500f40325000e84005100801000d100c0d00002403181 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 82414102 1250 82412852 82412857
    0x18051003020a0e040501030b0c090402040509070c050714100302090d0c03031110051006031d0a0c030c06210209120709050105120f030a0c0f02030f0619020a0e0402090103020403050a08 81
    0x2081a500d510f512804101008103580080c00f003d099040305c000451780c0070b075214004046800c40600007605250340d0300005402181c0459003c00442c40c1c1400140c20088203001d8803002d8090b00c12568001071100000c01c29070900700c0760013400d142d40018954060760300c400ca0301d800031703622156040205441740f0b4018030b40e6000d41c090b4a03943c81600c4850550003080e000709407040c000041035603543c2e031501c03000702c0181c0501040c4a46503103240410f02d41c1c41e0400e2002080c49401038134000201d40c91498020342403801039004404108030b40e01c0481c5242c450040700302c0c20580907400580ca41c0711190000303134088506010080ea900c92400002401181504800e0403260120f03005020401c068410a03240c000c0460410300541040007070341421405400510760081c000c0480b0b000741c40700c945c046481e09002443d03555240d8030500c00c00c542c0c000c2821444130903801110055041500c5900c0150030601c01016017445660007150010183c0d110ba41038500440d008000c0341e0405445041443d0f40360f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 82415352 1250 82414102 82414117
    0x90e090a0308092b140304050114070503090c0409050f010c09050906030d05070b0417040306090b060316210803010b0c010e06101e0302030304090b01120504030206071805100302 78
    0x500b803200003a014000108046203203010720180500d2102c4079203844055000400322403001d0025002d11480e0061600c405148294410700c00001d41140311380e00107248410090054003000000c02c1005a510300201e103603c3c03100e000341c0700403950a0403840c050f0b081c00780303000d40d00c0181d601c0e0101c0c018545501c58064011a0030949426203107440350028941c40780315480185012071000c02c18017001406017002203a00034090140f2101d040301d420090011a4040c1c2c1c401d569480e01c0e000c51505108201c2590703500b00350300310b0040503400540c01a2412058551007000d0300c52001460f8403e4110100e01e4021103907900c440815540e6840f0141601d140c0c010715440c0c0070075841d0038030542c9982400500705014100009040b0180c52504c11841c08201c0c9603000403078411b14500e8004010703181000a0000f514002d42c0120b01181c403440014030311002e24070707600301d1a4200801c1c48046500410b589401100500d007403e8807030304592400b6140c0314241d1029400036220803100c1d402550550240101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 82416602 1250 82415352 82415357
    0x5010615120b100801030b0703060306060e010501030f05060913081204140616020316031206080d030b061204170403050d0203030a0c2c010c02040f0b0a06051c050601090e090a03 78
    0x303090205003d801c00340300e400c40c0c0202d207000d401071011590695205621501c1440c0108040c1d07286d580710801e0395015030144410780803210050007190703014000c2c0b82441c0340c0e08070100110b1405800050182c0c202600400703818600340c14520034825010304451306450807581d03488050905260003084904686a200902e01808000c940003244142265245101c2940114100200352200e0030070404541001c0b0300340115400041c0007443e040c007a41004014201c047d103c03030381000c4005000c0c0c445055013a403256004016020201c0c04a5010541003074018101c403550741c4a24065411520640e00058141c2c483c0491400f1543c1c2d0001c01148200c104a90070311010181c0701041d034090081c186c0340c88030485c605944080741494400f884800100c140761829038001a500800e044072034001d00310a90a0f12002d0344042c03420510303410b1005154a140071407804a201201c260702e40001268a51125111400700b5250383c8500d0715440a03008a4084600a041c41c0000d1580c0d0503091004401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 82417852 1250 82416602 82416611
    0x305060105010c03021c0e10030f051806151c12020c06070203150703020409060b03040c080f0a0303050a110c0f06100501051c020c03071b120206070206070501061512 73
    0x81e40e500c80c84a01140c258160000c00c0304141c41c031b0f00f07190340212000f400d40802002c44d0002034907540b640744031001c2040036240003403480d20a05051303040c0c48000381702c500903425403408070519180004820b50300042c0d0f400d0300500c54095000090040c0c001c2c0309240302c1d69002204c00014840d01545013013461086408480e82655280309002c0c103030081038006035050b005500a40c1a080301e0881b01c43e8070049a11380145440d03200c440d500115136447c3c000000b0840084100320421140f001650b01078038500c402048810009020700d995980f200348000d0400d0380720004100d080c861500105620880d005040e078a4071403485c105c40e039801125500041074491040450380f031001c218409030644a061356014504241d4000c02c803401409404c0e2482c03d03075400c01000756803102c01e1024060407440341c5e030441c001107108110410350a01540007076a609140f000d00d040180e40d040c0880e03411690650b419901c0e0b072a9400d200d1f004000c80d40c00700080c48902a0f115450a81c0141d003414800b160100402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 82419102 1250 82417852 82417859
    0x24020601050103230405010b060c010c180e1308090d060902090609040c05010302070813060f090b0301050d0f02030c030d050301150e1302030919030909050108010c0c03050c01021e0403050601 84
    0x10f0980300c505845a8588821800c0810f98030b520704c512a80c080d0044002181900380c20f00410420750082c8005c4405035511400c0c43c408039480025920108101c044803100d00d810700c240010488405000d14000f4010f0708001002c001c3c841080d03c094007002031105449004506001001d030071303500001c070300c02d41d6440000307805850006030f1a8001c60700f21184074125070a00006400a42c0055400d0310341160600c07803000f1000d090005000030345442d5543c248000080040a17041d40010740065408620520040c051900c48039400c81c00e0b241c010081d680c0c00d0210f0b0010904002180320056010b000c0c901c4051403040d0000d0003941240d0483e92510508084440102d4000700904042d03984018030042500d0402903030340241d5046200c9809983c50020b40110310750b0081140d10040b00410041607080064087ca0300c941c0d4010030f5040000d00c0b9291311248010410081c40d10000c0a006002c5205407000409505236040642d180d1401d4401440c230b00c081e80140c0e0403920046030103116800012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 82420352 1250 82419102 82419107
    0xb040501080c12070f0c020303030108100518120d0608010c11070603020702090f10121202011401030203030904050a06120f060c0309081603031407030510050f06040e06040204240206010501 83
    0x301d03040c0c40a0069100607885506080b9983c0504500d14020090300700107a00241e6814401103009201403401452109378180c943d40540b003004042040d000600c20420f00302d018045070300244801d403078030810b030746401c65201c0a0003400182c02c103c100790f04e80403d11840ca60012984008420345604944ca440da032103500b00c0983c415150700a400c1203c1002044c00000f0403141d6a4009101410305840da503210100380140016a00c0d041d00e00307413030501c10600c140b5020700c070f05200f0740d030a00038401c429811034003c42c0e40e0b407041005041c080d555a00c00140c14440e40d034000c501402090410315113601d038034145042e400002d002c00351081442c00440304800d500a1050f07e00d85a0301003050340c14045c00054665000c0c10101c2c041d0309154484e0a90700c00140313103603c404d1151f00141c600003094117041c90041502d03503154010a001d00e0321800f5070703405503031000d096400300c4000e001201d0702541c625004c50082d0203103501180e08014006044061001c0111100e5032490035542220f070903070b81c0ca5004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 82421602 1250 82420352 82420357
    0x90609010b0d0504020d060e060a06050a0e04020d020f0301060602210a0905010c0c030f0b012103270e010f1d04020a170a020d05030d1805150915010b040501080c 71
    0xc840150004026010382445950443e5038030a00040a91540401980b40c44042c1da90045002035190030002c204040400c4610a44025000c2070b03411002550510400c1c0421920103000a8800e00c141e50301d0b40300315914214415070340d02d4080d000b403160a0f59510b001c1c1d80c40c0c1c045555102c814202c908034800114102080e180c00740c01558840740c0c0c56240000550748140400001d0720b07000d00100000c80030401503c5d01900b2103204141d190920343c03410b503600c65205006059401c0c598001090400070039400420050034201c501409061507103031250042c56889203500c03040303121101e1000022046450441e003401c0704c0304d82901c0c50ba17540d010700340e034494031004440096005a070201c0a010344100300d8204050818803000315110714400d41c0010700c1082c0c0101c03003214958000258482040d04a0080c02180309890b0000d24100850340d40781c1d51500c641d0105010b81c1d174260b030300145010708104119807004180d01420941c41d61144180a00ca078024054039000c1018031010501c442800b504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 82422852 1250 82421602 82421609
    0x40c120e06060901050111100e0a1101020303060d08030a021b0a0203010c140d090311030d0605010306141c110d030302090a12120807030209060c030309120301030f1101051204030e09060901 83
    0x2200c803844c1e00b008015141504901000e40e0f09115040c0c07805d83c1a1140e100d51400c49a12000825203484070385003903078455034500303d036a0454000b8010710003252582c66844000d56803184009842c7c1d569035060400a0050080504e0194140528040e8014010529502090094000380f2109200355410b4039610400b84808a841d9010441c0121380c00a5611180b4039034070038a0203521100d5005421840c40d000301c48009500c56490008004640e0940324501c000c103c011300f504021285000000c0c40302c08030000807010040e40442002c1049450841500c43c034100030400180c0354050b09005009400c51807040780070350030104001c0b48031007031024058410365112203003120b04407120b5405c0310703c420041c25110a061f028044080903039503031805482c0c550008030040d034803464843d040a14000802021480400e0f0410052010a40498840505c0c81d000301c51100d00741c0039003004903030030303c100d844040c1ca0380307210002e0008040d440014030340c069804a030030702001d898034010004025000c0c407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 82424102 1250 82422852 82422859
    0x60504050c18030c09070f020f06090a11040e0102041e0e040b040618020306130501060b040311090408040911070201390807050f1507021603061a040c120e0606 70
    0x2c528100140010100300000380050191061507045802140031154162071729804030701900000c0c00f803260304003c032200c1000301742d00034441c900703112000a4481c010242d001c0c02a9903c001d440d0304645990300802403103000500210358550307403114002481c080354101ea00c28003448940008003147c40c40011401650003c03111030b16034580e5504c803002402d552440031001d0300200000c0e00503a5050207401d200d056543d5035000c0321200c41c40c0c00d03801c54105412015040000340401e101041d885040c0130022441074400c0c201c2d58407507042103001c501840e480092072508003240300d1407000340c0701c002c1c0c00b00705e1003a240e00c0c804a51590a00000107c1d1409010103078200390035800c000340c0c100400c9000b99000b405050302d46002a1941030030718108003d10044c50f40003042962840342c0203050390382c1c0540144041d000d0401710008010140909100c003810f61070310303000ca0310001800d40d0058000d4620081c0100041c003030b4030342e01030b01d0000980e0502d04083c6c0b502d00d10000070880401d14911404004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 82425352 1250 82424102 82424107
    0x20d050a0e041d06010806090c090f0604020714030c010b0a23061c0e030702030f07060503041106090d050115050a08060402060307141201030b010f060f031d0106030c09060504050c 79
    0x1107040c48010000340c0c4100710320380c002524406101806102c814064920070024100528054010510b030880030300800d40512010410001400100104d10f60400d10480c0c0142e80c1c1d81315410003000106203442d0485460000003010003203807a0543c000b034040c0d00b0036a420800d00741e40703807078280104100d42d2140c004000c400c6e50021207885c02c1c0c8000c0500001686100c04c010107440f129404864844081100c958000a40e050a5181c01c2203400484078070381005080300c5040010003800743c000038100500040005504c1e10950350398100ba82e800031700203131180c0c0030101c00b400c205000e8240145a28640c0d01410340209580c00d0902c141d4082e83c014030000c0c2055141ca40c24820207500c0108008100710001403081e0050340040010843c4071525a0f90b0341030743d419420031803000301041c0e204a080340030b8120100603413908021041000041c82c100010445244100084c0c0007804280c00681c0e940381c140e010007000040c4a44d842655042002009626200d400b4003040301e10544101c086542d06 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 82426602 1250 82425352 82425377
    0x30606050306041d100e070801020c190c0e0a053c060a0509040c08010501060f080103030f170712060504090804051009031a06040b01020c2101110a0f020d050a 70
    0x75410100101c400040b002a08130503100009040000c0702d0f0600180d55220107080d02c401408200000260460f44021071408102d1108959a100048032180d090a101c00c0078a0078030002d6803100b4010300480d04001224600031010a00800c01150407000f0415003400000080844056140c0c00e02801d06000d580d90356040c3e07846c5950b0400610556101c170000c4404030301034481c0b08a550150307202d007143c5040300341131014450070354405800110401040d4402401405c1c0d20024007411a07405003130120100e1141001141e21070101000c0d080e40d81d85072024020b9040e800012a040003100c040208036080e198410001510001800507051201c2400306011030328101000d1060440307030f402c04454250381c0e6a03030700142e2407602c1d1004545800150800402d800d2601030003661100900c0035051070b076501e00002d4003104499165000c0d140c011500c1c03500c078020951220080c1000c88116a40b149490300b401401003c4107010354006024524040710881e02032026104491032989801440108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 82427852 1250 82426602 82426609
    0x206040203030f13050303040609080d0f170601022406030f070503030a05220b0703080601082505070c0e040219060905010507060603020d0c03031404060203121e090a02010807030606050306 83
    0x141204e004905120080040c0a650800040c80140000e46074048103a00c0d0100803803c0c0044149018284580c2c1d0700c5c071000a9a010030fa00b40e080f007000c40881030b40d40324900102e207402100c2c0d44100f42c624034048201100d2580e1481c080c4154000c50842e20800c0c000e000f080c0c0c55054604c910f6806074820701c5a20607550040001d0003215025500304a0040f450454103403780045500c11000d10f04005101420b0541c03002505074014002c2c2003250080c10114403181150300024a0800304e80c052008a00c80c4e64815000c65000b10703004001e03a81c0503074031102c560b016401d00341c5080303105904d08091954141c04c0081e1a03c01c4440c1500c0e0980207a24180c01035409034408803080303170710710307914000400180c4d03a20300010680c0d4056000c030f18480d4218507010b454000903144042d02803034240010132015034000200d0f28888003108040d460707600c629410303000c08400300348003a55105103002080011500000c41a031070b54001d80c3e9050054032365090a074103c1d4100e000d1200090310800000d0010304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 82429102 1250 82427852 82427857
    0x50403030b10050301031716110102010f0204170f160e0919030807020d03060f03170403050105010b030a111e0c070e0c0a140a0e011101141e070206040203030f 70
    0x900904011506001c0a030005607504007400080010440200050043c044a00b203042e003020740708059103242c900340090403a004c82d0410b00c01040c0c501003507020001c6910030b4000d0541d03110340620640d201e85c0c80b000c440c100f8581244440d0200d11071000c51030082600001d0062000c5445120b44000034280500d00140410040810005126070301a039440410408070a03100c1500a64a103411030801403c020b013010650b407002d408040c01c00e6000c0c008130301a08600021a90700c001c11041e544a4004000300c14012680054280e51134100000340003401d00000b1882143c29074000c000341004440c4205290040c00c604586500390900008551b1143d1001881c071802e01c08110b40c2c480da070360f1828001c4002d080318003d010507004204c41181c1c640029180001c10304115204d410b1079410f01c001040b0703103412003a8a0404c0590400a0b5030a0784c01e521030580c0380e40501441c0b0345461300120704001c0d6001c8100c0207031181060000500170603c086800360203035a00501862500b0907a00c044887e0341c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 82430352 1250 82429102 82429111
    0x70f06020903060f01030b0906070f120f060608010305120f1b030702040504031e020105190b0604170706080603010203060312090a120c09050c030c07080a0903080a110d050a0e0405 79
    0x150303081000a14907030b01000000e00c83c3d0040303241d4081560543c078050181c0a0041c080842552103441400416508091001c1c0f202400b8a0258281c4400c540c141c0f01800b00300d10090049803600c2c101140541e80b181105040c0c9006100311010b5224802001c2130030300c40e41c0b075107c0c40c03d103061090700c1304400102100b40444165204503820060301d82c000900702c6205940c1240820303000c1440d002170154600760f050f00d902e664002001603181000410102c05d016031600d00d03241c4d0782d521103000300d0343c0c8010503100030b42800d40641e500034640e005015a680b250303010b0304021401c030000240c0035150500807281308038406000345c5020902c1101100c0c0d29004507503950b07841b0725041c00101d12603000382000000d0b907014143c1c550034286061020340031100060601c4c034100204104001c840d90188048860865015a005584000c2080202c030410601c0e04001c080600000b4840c181036440103d00014030841000c0c0c40107002048025910351144020500200340d00041112540c9413517405903a00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 82431602 1250 82430352 82430363
    0x706020a0f03050a0c150b0f04111209030403120201021806041404110405030318120a030f05070203070e07030b012703230d020307060c0c030504050d0c05150705150606070f 76
    0x8401d4550b031006c0808011000741888156035a181d10b1b000d00c1d09203190110080c003a5070400958600d0407038560684030b03c001e10031100d06600081442080e081085034002c0d600030b018880702031081040240070f0740c00250407145414504550400c24540300c070803207044500d001c103240043d84c149002c0c8800b500c028419101040e00501001846440900041c440c140711540d400c502110b01c0d20070007840003412545525036910412a4500198201d1644240320300f0504100c6d03203c03001480060b24000c0c850b00980e11088010082c003214607051b410a11103450240c070744c5071510f507100e580ca150281c2c0303410381101240880c08007040070a500d050100d6000819403c60103074100019261031803c1404000000160301c0002d189007440064811901c12507018a0104240351003610300404c140030740d02400f1f02c24483e0082aa00704002e003c0e66400902020b0454100c070740b0421444580c8d50443c030001d030b5541c0a01c5815110707020b23000300580d1040c140100858142109a254007051281a1398101c42 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 82432852 1250 82431602 82431617
    0x50f06030f0a2004050a0f0302180903090d032f0d030c03110406170f0105010804081605010c0806010311040e010306150e240108070c020609150403080703020706020a0f03050a 77
    0x726040c1c4604250f4085040142c0d440e516071800050150f41c0506501405009803081028001a6a00784180068404040a6040640b90f10244c2070540c0b0809940d2030340041030f02c042100300354014004d01d04202c00990080c90710a07991828041c00a440481407200da003100c14100b0856000742e00052108020345070020b45840307080450340709544250040004a001c1081104c4004044120f10f580305180030b1054010354540320000e01b86080c081c2008001c1f080c042403a48000a13000884440710390400d0080c44100c40000000d01048000d4845500090500314030351403600da40422035083300e1071f80d030154002ea072171900e40340300520342d80a12010954200000003540a038041c4218050071001c0501240a864014100c2e0940c0d40f0994440c140845001040a030b0354011b0004e80c4911b4040d282e155803003604c00300059201d041843e01848804000c180030042c000200d0142c01d04500c203800711500d580d02c40000b682d8416070008014850000e01403180d001903c6907014001001007800c5c16003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 82434102 1250 82432852 82432871
    0xb1e01030c05160510050702030a020a080708090d06050a0c090303020714040204082a010e03100e0c0411030f060d05070312021c0302070c06030c05040909140303091006050f06030f0a 80
    0x44900c6140070554250f4000c080300450301e0300506c00c0302c3c0c000c40740740001e514001202ca406034030b4051616000c1d081d064081040b80500181e5811242000402001c152100b0105c1ca40580206015110315000303500c2c01c960100c0b16400fa60108060b25095001814410720307150b602800624814410350f0810303000d01002440321740421070f0001201406107110500c802d20341680001b0080c8941c211b0422400101003980e030b03100400c4140f0403035514240814107188000c00640b42038001c404458101d4600302c00c003140c416101c1d02841c01610200102c00b140d0321424204079000b00038000192443c5c00000033000000d0340c040c03524464103e0344c01622402d10007494400030003200291202c01107030300080c1c21420401c0b400e280074050300300e60404000d59903a021000305030740201c0c080e42d07685c282c2d01c80081b4244201c90380444041440c034011243e50340303049100203450740c528600e400d10341c6042001c082180d1a0107110310030140310141c160f03420340da50a80c041c1c182500180010b50006d0b0b484801c43d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 82435352 1250 82434102 82434127
    0x309100b0618040f0c110f0307080d020a0311030a020403020a050409050c01050d0b04061202030105100f05100311070c050a06020f19061404061b050414040c1419030b1e01030c05 78
    0x4a25044240c0300d4046c00c40c0100302150900f801038244d01c8454204020690005420b481a41e0a1809203d0010b8440d140c0007403d400410710030421465082d004000c001001080c3d40091003664400d840100e10b040d035800070300c003da51440d0402080c03a00045080d452551041c0701411100c203181902080c021b1404020400711800b5402103801d8048046d1070a055080901490381c01029044d91008624036165000d10680414040d1901c951003c910501d2442d200f0b400008410345c000e00b17601d907101018039060400601030311800c0d00621210a00048075400800c0588a1048480281c01c101c441045245a80851084212502c603a203000c0144110340d0900020700c41d9115034000182c1e141c00c13001220500c8030700b180e410b0402c8000c00040c0074100aa00c0c060110b000151070104aa030601441074560551400d000000008081014504041d2050241d1408100f41c0c40c01c001270808030042c0b0500565100f80d508000007845a06051035220754007031240207030749150490034a403030f20581 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 82436602 1250 82435352 82435361
    0x40e040227060f09060a03030f030e060a0608010c051303080306060d0f141501020705060d0b0d030c020f0906010503040b060a09090501020405040e0a0b07080c090409080309100b0618040f 82
    0x55521900761504000c0da50a1424a012081a04a803d1011032902400140e4030010a01009042046010440c0545030080d0019070b00c2451080a0300c0091500e0942c8100900c40351084410035800c04243c3c5219031f0062003210000954080d50707180017425902e0300082903001411064001d8810031152100b44640c0c406d6411041c0c7c0d04c1b8000c00c0326400c10070300c0b402d503000c0500310440c00940c8541144050382c00107280e800715101962401c0d01e0316144a1181d000b800e660401507041600320314148105a030140c52100458403c0301c1c048001d441881c14055a15002c84215010500070804a8085150f81100780e0740402d00821040c0380b10340381c00c0500107640b02c400d0100c0e1140e40128080c0101c0c80d02c1d01440c2400740e076207002099118095100d40d00d1303900c800b4100301c05006160020540414415080f2040d07a117000d001400004220300e4543c40c682e004446040017030040c00a401404084c90051b41903050740140102e00304041c004455411a202948041e0b01c207941d2180d00798000c185024 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 82437852 1250 82436602 82436659
    0x103030201091104050613110405030604030909270f02040603020604260a0210050c0109020306011205010c02010e031c0b04110901090b120708090f01060b09120111040e0402 76
    0x10402a00c646040c018036100d41440f039105905010400c034540e1640c106810300d60040007404660319402281030300b068450317038108a4060061404001c28146c03c072654408803040240c0030025160b82514442100f070484140300307840c0c02140b2900c2c000c1a610b030410501c2d907000410000b000c40d03603070380020800d07030156104e0000d031a00f03203000d0886c107011800a40d440c48282405040c100c82c00c0d500048480c0c01008120041c0940440c0807207108000350b208600480e409800ca4400b5611000c02e0304915a0a1004481135800d000c40503114a05c18041da02c02003110301c00a609084007482c0c0c81c1e80c80600c0112580b2401d60b1500e005190750354901640d0041d03500300e5401c0d59a4480700000504040c0e050300703c00c500000400c000c0307071150090440c80d580014585841a00760b100c20300d001b828542c401c1c1c88038900f9070800310007107103c40560f4014a0301c1001113440c3e043c40d01b03030300b000c860a074ad01842c013100c1d5050052004000c0c2d0500c010007183c0c8244010081720f038182c055040400c42101015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 82439102 1250 82437852 82437857
    0xe120f060709180209130e1009030c0c090e0c040c1101060f03120f080103080d0b03030309010b281e0510080f0106090321020c060a0206100e0103050312060f0405010303 74
    0xb008101c84044401d80c484020303240d01c01940791100c09008904048550026a995075603500d20740d808a000600c0614028002900240000861818020640b0100d80c07001e5429000b100d0001819454500c00e00b07a8200380400944808100501003000804034910031405001d007840403801500002e120f01c001a00000a4018815003181010310415500141600038481c100c0c6140c40d003181c1042d80c03241180d91203540da9903190642882d240142814003800c541501c00071007407141405040d0400308051900703a032403800760000a8907020302031003c0d0102d28440c07911050f0078400ca4047c61a00b19026951009803501c2c190756401042c50410382c035a090300000e005034180011040c5100c4410f00500451031311401035030460f1120811001607562020a0100c9422411000c500034025078441c800c004064588034900484003a448510407507443c1c0481e10007400c00301e10823206880303c0c0e040e650050001c60400783c0ea5120b40e020024003a05c19680b04d02d4003481d41c0301b290360b01c1c00b036603006e140309030f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 82440352 1250 82439102 82439117
    0x50d02040c0525050d021603080a0e0a0e09060603011b050702030f120c01051315090c0f080a020301061502060105011407051e06090715050d020d0906020307080f070e120f0607 77
    0x505149040c00181172624007150404001c9041100c100341d030480070750b6008607016540381c1290000360b4038160214030103500001081000540b404005160a02c0307a03c451090706c0d4aa6a028201f40c02c079074014000c00300840156015600036481341014022051000e400c444119885079281d91620310040180320b480100042d0141e111340007800344940010141e0711101580b5590f68800c49241c01c00c1c442c031146140e4480810091015006525000b005a442254403450f1035446040c0c8481002205074025802c110b00080c10500c0e1000303651000501b503001d070a00364244001140c070413001d2990801c03040411700408011601c2440802c0d01105a00940304255940324080d50070700c4001060109141c105280411481480440c0501c0700c840c1890155584e00000d00010020701030320740c952030103920b0400117034104840b96000398000c02c12031300c914000c3d54614510880d044411194280010558804d012140c289982e04d41c03810410f000aa8680e00b12241d011441c010084a1507000100701 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 82441602 1250 82440352 82440427
    0x7030609021e0102030d020a030b040504030306060201060b07330e0703030f05030f040803070306030501020d05070e060304050a0f06110c1b010314010e0903041e050a0906050d02040c05 81
    0x6001c6202200360b204a080340e0084040081e40b00e0241548480c4e410b6000501025180c1c8264801d41007241c00400c10099404c0c541002070041c4220301500c001340d1b01e442804101260040300362051941d1142c00d00455000250045061a040890120721250038a00740450a6814000e4540c14261003004080840c6541001000ca44614502e442802003c0042c028000d10b21210942d125800407490742d640c0c0c9a90038110020324559002421035480418154540485078102a005a41a54409440111200c100022807006807401041036011011150028801020416030140920000100040ea1305004000e0343d000c2480e041c440e40151030415450b448120108050003000e00c1d00300401540001660003030101800740000140050b000500c07203910800c06c540140254680e8801418802c240480d2500124003580b40701d140381c1e81000c6055400d5101c1d0400b1184020070450700d003441c6c0e409100051414284080030441c04024010b165804003944220b0200c45005c114070704e061 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 82442852 1250 82441602 82441609
    0x604090e010605010318030e1207080a0614070203040905090c060304050102030405010c02030c03040504050613020f0301082a04090201120608030903060c0304050a1205120106080105030d02060103020307061b050703060902 97
    0x82c40e000b0606052521910396220404002e091483d182d06003040d440c2101c1100c00501340c004820079916031803040d808081800d800104092946600c9400207028145e06d034071080207840400c440043c01a4030501c001c00c202149900b02c05d8000c00301c08140c50026400f140460220381c0308582c2501d950f90008140800c102d02403091011000c101e10103141084606100725407030b0b00c510301c50f640c4a1034888000c605195548004d80071240e5010108650380c150600340c85580e0380091003200e01d640a18648c4e00d6440755080720b404d04038010480340446440d4490100002401610002d0781041068200504a52543d1146401514549000719100d020f040308061501130001d00540c0102c1051083c17000180c000100d810400350300003282c1140044032842162540a03030212120010005000021a240c10202a41c1a00c4040d02610f00107002e00780180d80c2c44070203100017034040c1e2105c0010092544074200280b503109a00024015a45450301da091400c029030300b055403210f903240799074403c529 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 82444102 1250 82442852 82442861
    0x405031218030601050906100e06030403030c0207080c0315070c12030608120903060414030c03070614060316090b06040f08151e040204051510181a091203090604090e01 74
    0x410442c002c1c403a540c140030200c1c0f0340300409881035014200d01102484160b000384924052141d02038090f980306d00d06424028040e029070003e80015010700f032800325896102040e81e00e900440a001001e250500c40c81c0202566801032103401040b600b82800000a51100511b5444c00002c0d9004140b603070606030310f142050200030307804000c10f404010710090b540b0046000e40d031107600804034941085c0101c18282c190700c80c1039495101d5000008042040090991000d08a01003480c480340c025580e060505a0302e442040d4042d60b0030440313903001c000c120b00c250040604010084d210307601b05541c4200031288140980c0000303200b90440401d03400212014200a540b100c507600606044038044544041c0381c1c0c1c400b0b000a80919150300026841802035020500b00420203403600ea8204076000b0b00030a00b0a081410120005410000041c440304440b0380c0d9924140800d650392a2201c0c207420040d5801e9000c829150038002849040c02ca9907030300002d80300410600f6000314440103a6480242100d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 82445352 1250 82444102 82444147
    0x2b0f05090c01020a0f06060b190306090c02060a0504020a0503030a0e10050f0a03020a0c0c0303020309030114150d150e1006060309170c010906061206140105031c0504050312 76
    0x40d80071890018203a80d00082200c1c2c0b43d60000c0200c01c02481500f03005001e0851900144506000064484030040030b048001000114a5404001007511030919409848a03200c0c2c0c1e40059000802059118465500c020f03001480103001000355984c17440441d0540e00103e2003440403400e80100080f450802d0111032485204900e000c80c9024042c2140d001140a0b20600d502050b0b40403610700300c50390040c05282d00c240e40100c1c50001440d44c80ca4000e559602560000707000b07509024850b0700811000c040b43e401154603100044000c50031000b030120054070408151110712000c4c6212040c0095403050100050000c0701500000c0003481e408000d64106a002208052a1420000110b204916940e041c65411700100e1f5035441d03a480c20794090a00180c000c1c00d080d00d0940c0c0018414105e181795030402d0b00c40c0038107006c0038044d0780c8001090300c02441807a406820010524112100b00d81d14450900440d05085082c00d0700c41c404a803038100c1e24102203100d1100040e07034100c5100c40180b042e420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 82446602 1250 82445352 82445371
    0x30903140901080c0a030e0709020306041d0601050111100c02010b120d020c01140d0c120b0a0f0b0a110a030c350c0705030a0b0103020f090106050f2b0f05 68
    0x1c0c0681040020706540c3c00800c1d282202d040802c20b041d0b098030940208500000c103074100c0c6e0505444510345002940300350b403254421031030f0509483d694940c403080042c2514160b07001d00300c140e1925005481010403406086441d0003150000e80f1040d81ca03100c0c004143d03680340c0c00003d04e009070701e050016840040d50a80780d20741c0004644500b4a50018a1300c6c00040c084c6403d24400000e40b0340d0041601501c14000e040e5400c1508911419500544060a0040c24a014460000348900388040f0000da0300410036034100303c810500512240c00000d01030504a0324144000741ca0740410641801c5c10f601d02180007400e505041c50500103020420000131070350072541403080d40c020309008288a00c8007030609101101003182a20341400740160002460f015040d264142c0e074924040b4038060003404120310812000b0340c20300e998100005024141c44140e02d46500d030160740e00340805281c0002e50050741290391207181040c040401c64101d0303c9510000300c040fa4130380308108908241c800003040c440c003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 82447852 1250 82446602 82446607
    0x801050c0310120206090301020315090c040b030112030e0a03050706081006020d0e060c0d031e02031909060f060312170c0f03090c04091506060801180515030d03090314 74
    0x8803220980300300201c448400000f50211901d01c08901e1030302660300f40e1541540701004004c042c0d600c95040e1000844110344240040d83ca00c0c0040106008900544090708001e00040c8843e01d003140d4080200b038000d0030180d10504039000000d9062209030402c40d0345ea0030082080201d59000002641c11a07a40e400100d03403e42002d000079650440540c061081010f1402d91110640320402140c20041035142a900c0c41c0d40c0c050b501501038000c1645281e01b4440d2100481501ca00e24030a1b2070144945000c4a6451340000d40140060014184240c030960b0340c45000502d01d102520400700150700c110110700ca41051080d0140c120300c41c20000035081c4800c2c000b04a14110740c03030f08903140c4061707220419840e5100e441c041c2d480c0c4a0001d44940d005840d02014500f407081c1840c01e0644a9500c0034117118141c0c84800450343d4200a200c1d14508450340d1844020650481d00100d51200001e42014081e5440000007843e01130642c072403e022a40d2894440181070380070403028009108840450b2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 82449102 1250 82447852 82447861
    0x911040821030a0209041d070513020c0312041a01060e1206010803030a0c0c0203070e060307080d0f120b0a06050c1006081b010c0c0801020a1209030c020f03010213080105010801050c03 81
    0xe61000800f018079560340040c1ca0040365556501c44602d0741d030351b4007100d842030004110060b5244424052130344903101d11440c44c1c44115680c0222117030748008001450400214400151101d440684102c860440b450301c10341b00c3d2400343c100540209629642c10344c00c1d0390307084148001c0f0300e00810b404151742c2211006000341100013007241c0c1c0149000c0000603c455800c8412158080a060001d60500403000002904c0115070f00c0e0b03d0194004405841540707a8406209a5801659181c640411700000304a01c1090056031200320340d00307518001080c6003c0c0d4000007081200241c000c1004220302281e0240068410098210043c0e06004100101030800b00610358500c184642c0300c0c0030540d9406402007613442510704501c120b03440b0720340c504c0707040d282c07002c55002c7e4100302449000a5000c0894541c40b40607405a03940740307a05601d034807484250720b0b000e0202d41908010075507095902003000740040064880400020101c50f400080c8650400c8002401d40340041e0400c40b40c0b001c24428013 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 82450352 1250 82449102 82449163
    0xa050d02030a0b06040902030105100905061806060d020706140109060602010903020309120c0a060203250f06110f0703030902090709050114130308070f0c0e090a03050903010609110408 81
    0x10100da40c0166083e0010f0307035100c002034090600d07044025015400c02007840f514800e803415220548040140034040c551314001072041199070360803da501000c03080007090340d07030500700d000303100c0c14041407009844c1c0007450704c9100c1943c50140341ea261104003100104400c420502c2040003800541c8001e00600d045034600a61384c1c010102c09610510b1040c171040900413080007000c10550b80640003000300c60359128040d4407904035001040300c2d0280680c41c107010149041c4541c02e816401070b4428100441501d9290003019040b2510071500410444000a2081d1601521415129650100314010144140107800001402c0030041c02401041840581c2c0c0000c1c464802134007812044d62140034400c0c0b8404940030f03561024041c80310015880d01800f8088200c009103e0003501c07502c0080365202c5180c0d8041a003202c0f500c803250040701c00207000920510052111100040020402c0b03929014640200c40110300d0340090200001402c100040080c00441342c49070031492850700120370780c07905 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 82451602 1250 82450352 82450363
    0xc02180f0708010f090e070e0f0f0a09150902010e122a0d02190e13050c0109150c0204090803011e0b180d02010201090609060204050a080102190f0215040c050a050d0203 74
    0x6074401703603407510f0750403004070402c0001c140140001e0a10fa019400d09803c00c130046041a1042108410b182000400c01d25041c09606101548912181c0c014001b40d04014024207140b00d0403410004801104115550f510301101a14440200035101c1070030908108001c810f50041014500302d15000e80d1111a0b880c41400e00200342c05480380c000707000c00d03540003040601c101d80142c403101080d40300303001103e0110a12003211500c5901100c50b41c2481d0f00054034000d00901c6902000d0244030030300f10b0744511403da1407603d103101800204455a103681d622000c0e0f0800d801c5034000943e00c2c000400c00300342095540d0020501007089504e010381038064100319454514a250280034140203100469100b503000400395900507004202080035464610041d500c80e00c04c9034459085514081072003201071081381e66214480400580c0c6c80101e120984542c1d090032100015406440c0301c0c1e4402082c0e0229180c4a60f1244001078a00b5040c0010013920700e04641000b401002d000150f03d0050b14002031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 82452852 1250 82451602 82451609
    0x117010b0f0705030a0504050406061106010b0d09050708030a0305071706100908030a11010501050a060504120c030b0a02030a1d060a1113030f120e0d03030c0c02180f0708010f 77
    0x3400366074100c0d0462224140c82040b10060031071000151001145a1080c007038070645030110b0307041c80400c0e030b16401102c0641c0800c00c510b001390840801007140802d54002460890109980410300e80e82d00d03110182000d0240e031198056410009441000d19810b10072694030815504000104100030700195900007030003030107540074102c100b41302c0e01001e0191210b20700070200d0030220390791384240e41d40003040b1020482c0c240006e03600b440e0000c0746610782840004103a500941c2c0e002e06040c60082101031000030124180c910320050000800480c100d4107503540704409860002d6580d00b0014881c0048030051140249100d2014824440d101000300350550030068203500400c080d06c403140303204024030030085d2400c1c1400580350004108158815103289590207448000d5000d54928002d8a00e030000b000c215074000c03a01d848841c0024080d60180d2108203641c90404481c0d0070a5010601d517920940380a08840b9001040100089079000314540c89035003450010095454200d805480980d07e00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 82454102 1250 82452852 82452869
    0x20702181e07091212140a0c03051b01020703092102060d020306011107091d0102040f1a04031a01091a030304290406081803040f05091e24011701 64
    0x18003040714507101c1c2440707602600035034640d0050004c0350300d4410181c032120203030305002c00d2005281525a000d94000c3d81c01c0d0034801c0d101d03428625000d03541100d503a40281003c0f070274100600c5030020b41039424801751a0082c400d032500e225150424144008030303102c0d44a0b41118000041c481c500603224134040d038042c00000400940c40b6100d00c0c0c01a41d42c0000d59400540302e1069800005032491190008000401d41601d47d9580c071041c5500c41e4203070701c6117000b4607010903030b0400300300b0950903004204200a00c0701c046040c00c042d102e550310480e0114040310305025005030740c010b10035900980704608150b070b40da0501c050b050407414086a241d001d070b4031844000400c5824040c840000c1c0340302c0100449403031aa690303941c1f07460300800307003110100343d0300c1d6821890101c80c2e004054400204450580b9088261900e242c0c1c81c0c0300c1000450300004050025070044064034520120034410064090f01500741c0e03d900c10240703140008941041c0c0c0840b03c0c1041302040c01c05101170290500b15054031140b5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 82455352 1250 82454102 82454161
    0xb041404050604020c0a150f1a01050f0d0c021b030109020a050f21070303140f18011e02010b040b060f0409020c0a0209010e01050a06050705060f0603011b0302070218 73
    0x140c0c0020002d0268131099000d60148486c4403003002110303800b03200e070900d41c54403c0008691282074103044801924100c041442d2000d0303c03561035030081c0082c2c00000c41400c2410b20300007200d0801030a0303520807202a8090b9101d0a2503007244004480032003c0c080c82640200591403c0d60002020601c0521602d4004c0d41003d048480300d459a4039284111503101c0c00c00c80d81c56484140c581d81e520901c0c4419800036a481e40038070310b1011880c0c1100e00060170a8181e034186980300011100c0d40c0c06001106051020140d5504a41e10040041040703204c1c0c01d400009282c4490380c00d22043e60407404180d440b031681000f01c00c07002105c1c03e00703030380994486803401030310780000980552500c042d402029601c00c0315040005446003001c0d0445040e02c200f40d5025600581d81c0400f9500340c003035503200600f1a00700100203501c609090710300c1c5500c00001000800e45000c0d1842651100c0c0d02d42125800094001840f4415400d102e40c0500113120980c3c0351500c2441c0005c51200701140380d50300c43d151020103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 82456602 1250 82455352 82455361
    0x207090b0102251a0c100c2c131a041814030405040510081014060f0f0603090c01030506030a0309031e0203010f060303020f011a061b06130c0b04140405 67
    0x1406840f6014100c054510204080d00000c0d5003195084071840c04640d01c05c41580000c10340840c0150740c074800c05500c4e41551400c0180503a04440040d10030383d02c003030300c0f0740c4c000c0c580030382d212810071703103490200c803000503418910300b140000e0024040055402a0f040c05248203801e0f081030f0405511640014800c01c41800354184203045210f02d81c00103501504000074000c00c80f0402120f40e04031080403041300c000c031119140342404c2e522039510201001e000c18001610031f060040c201401e20000510b40038008400100184040d0015616a4616405500d000c0c2c22541c15205e42900030f0803c900400c1d4120035558010910142e5000041a40303601081d00c501c0144c20040f000b011075030040003881403c181045600062040b40310540040c450f0810f401c201d078038188648206140c2c4109040d40b103100d44000e0042c0d96100030322a160b6091444210b18003c44140549030180351510310018503217a00381445c10355540103410000c18070700e00300b0040040101941c0c070003640400c01d40d40412584c0c0e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 82457852 1250 82456602 82456663
    0x150315230705130801021812120d0c02240a0e1f020a110304030302010903260601030e0a02030f010c1806080a0510051207031e0201020304050609030a0c0b0702010207090b0102 77
    0x16680000c800d58000b14144001383d046a0400c1f240000070f4075030b10000080124140c1d0380e8601288031018001e020032146e800e610a071b82181c1403218048c0100c0303001c00c140c0c0d840c0c500341c1c2e0070384c2a44062910f03a180a20004040718051310200c90091402840d0041501071814452410090500405540050ba00a0744c1c0c0c080c0d011803694413882c60649440700d036603080c0070707010700032540d03044000038100310351008800c8008a021400c0b5500003000c03031790351f0784100042d001041c01700c185894910804c00540d0043c0c0c0c0810856002c0040344001180c11200d22201134094a0b06110369010030a03000018440103502c03800d1954800c1c1d086401250684800030110210991a0895a0448104200c20301e08040010307040040328464040c843c0034060750070201450700c0c034400e00203006030001c000801040c076202c03000d81080039000301521007003a8a80d0700d0100c440c075980d10201e0322003400f2440307809540c0c0501001d0000c0c000e2032828080c00c280000003e41b982d203032001d03140d00c0022111000c0800741 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 82459102 1250 82457852 82457887
    0x90c03150603041212020412260403200f132408030a09080d0e0910050303030403110c01080f070c050a060507030207110f090408070501150315230705 66
    0x5000c0e0015a8905040c00c0007807103840d403000380c000170038040604240c11807a50b101300c40844098001194103070b402071f03682d42c101c044005603c0301600c2000140c8200009000001c0005500c0740000b0030901400c1183c4240411003420b039180b00d1100d9885160140d102c0740900f60b41424246000101c80410402c04c031051400c030880d0a400d05111000401c0007100080100110601903d030448803e549401c100d54030582080403500003101040148905c2c180400780c150404120103003401415140d802103444c54204a80540001e41503140a02c54000140046581c05400f0b10300038500e840e01a56550f10160003410050802076500c0c411400d214050000d0301410368051424041030800c0c06008019420110007900c142d05500c030300c000c02e0b145c10042d034046910050002280d03a81da40e228008150487e22007500e15540b60000c0020342c008418150000c1c5114807803201202c11014002c50854824001d402010620040c0e81c50342e030f40e0a50314842c1e00c4003403440e01540d5180f44008140c20711 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 82460352 1250 82459102 82459141
    0x10b0a0f030b190906091e030f030b0a1208030609010905040503040b0703030e0609010b030c1219083108160506030910050c0d0c050a2705031005090c01030209090c03 73
    0x101e00e4007110404209541d000100500d016048050544900034403051030203410130002404582c1c400101c20402b4000d8100e0103040000400c40320825a40340d05007808044683c0c4100c40d00b400000800c02a450054580c501504003500100800d01c2c15603252541d0348114094806241c0000c208503080501c60341000f048071041e14107503225810508061070180101101d40380c80f90203598080d00032420103411020482c81100c1c000d094015200034014000d2042d00d10aa5110408015518030003c1c1000c4030a000c49c001208488400c1c05030007840b502c0c1170b16803c121040d41005c42c0311038400440406140603240216038041e43d0340c803841980d601d46810000003071055801c240c20012200440800f400d0341e100400130501030401921000c0f10b441c426918200c020510414281c1007101e0310065070b0748080400c0740c600cc41180c9030400a4a08a11101000203a984460811044107010710020f240150f080c2025420403960740300003548100014024100324101000040e0000d01c40048418203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 82461602 1250 82460352 82460401
    0x90d08070b190903090302040506120d050a030506060403023007060302030105030c030303010e01060f020a06020f09010914060d0902031c050315010207030b060603070905030f070503010b0a0f030b 86
    0x1a08000d107804520810200c0340d45a600b4500382a108070580302e40690b00308070b5850303a60340d4899400c0d94200700051070050110b940041c2003032221202d0400030440c580c41465235460746502c4000c1c002c0024240c0390300500603030140c00709001c10001070b02c1e0100c9402842c1042d41000c1e013074800e030215902e110091591024114420703003000050a82c1c040d801941070304c20650648010112210a00d40d49101c00c0c0b09140680c4221001085018881d0b014580844050f01c103542c40d4482648402c2e007680c00940c0468142c0c030f00020380d6106580c025252100802038412b00c1c0c50010600c1e000151980117a0b1801d074462502d032010f400440d0350074046040c8000c400c18100301d9005021100034803030380007111141d04403c0c0d0307011005920340c000110308048a9004080441aa48890603c2522340016000740144003803403201155950f003c2c4a202d071602070790030041038914030702800c050035030340c48080301401080c480300d00f400904000d00415082e00e07008001c5501c1505d4842100d10031049810346e00340c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 82462852 1250 82461602 82461607
    0x60a1d130c0f02012417030906070b01060e010c080f07050703080d02070c12021e0103090b010b0c010f0b030c0d030c06050a020711031504030809010603050303040804030b0c1905090d08 81
    0x412600300010b000720810b03c1d402080a20010990700c2c059652450000d0412002e1000801c00d171507008051000c2203141c401500d0134414460003050707076a000340a08442440100005100c0c0c191301001072086c130002481e0000e031030b00d215102c4440c580700b101d0400c504d85400150130024030030101701900003142c0c0a800e0544e2148084441d40081d04880320440d4481111000054100655102d0a41a0360003c2c510350807149500400d5100702c0c038002c1c1d030a05043c1c548901d8008516460340d190700030001c2040180c1d071a1910024282100c1c3c00c8900404014980071422030b040e00c001480d8014604192030505103004d89007030139640c1050000005005a00700010032401c00d88580140c10610722500804485108400030542c032412005a4020300075012400200443c0c40f600c1d0440c0c01241c0701000150300c07602c9856860941e8030848003a80c640f000010108200103000c3e88440d03026440311181418003070440d246213800d500f0082c0c0c880410a001c141070700d540d500d0b54008122306610064172035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 82464102 1250 82462852 82462871
    0x15090e01090203090c06040608072105090105070206072c1801080a020126060d020402040f080102070221100e07050d0302010c120501141c14060f06060a1d13 69
    0x1c0207540101c8000d15a40202011500503007484001c0e2019a00c45450f05c032155a9403c0b401c071017842e515031034070070310380c0684a050246000c1e074482d1034003d41d0f4480c000b040320f20340780038003901e420009803c460801401c14a1000030000615404841c0042d10444031251031080c00000c00e419521701092072065000c100004030418000348840d5642d00c01c1e01e51968484010800c0000c411000310001c8140c0002d100003415031500748580c0b41c07054030003840141006e40340c0740f20000c003000f0368001d28440c1c0e6000901c1800c0d441e0072241c468500b00800b0204e4002c1d02c0c00d01944d900e40b041407400340c0b40f481c3c41302031600f801082408a04003922003d031492411701c08500700240030b4011034586c0e10114010f0f05041c24100820302078a4142d500302800f40d102e140e104000d111ba562201100b03481c0340c0090311030000014608414107800202040000c09150400f0f00501414030750140685129000070001441e83c20780103032800c0320610311300c824854202d26010110340c084d0f424100321005c15140600301c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 82465352 1250 82464102 82464119
    0x20904170301150810230415080c0109090203060f090a0603050a080a0f0305012115050c12070207080a080702010c05070b030108010b062a10060902030a0c03090b0115090e01 76
    0x344119456440d44015120001c4940c030102c0c1e02e0003250102a07240c2606c4080305050515680036030710260000840315131080f0103440d002510f802c0f00046400040c0c0940e610341e40600d904010b045840c2c1d00f1480c41c102000003429050390409154041c0c00480d0001d102c50b56103902c02c000a5400070165040c07442c04e460035040681c44501d882000c1800c01140b0034080344a0300c240c9050721484442003044921410207107203c01d800c041c1c221580380742c00c03260542c00505401124012503110064070388519050005d1582c910307000741000c0440d400803008000c4032000059024200b40c0140805076100901c1c001241d86040500015115110b940400901c0c14510b000442c12500c1c4d000c000c000b03c1d40842d040044602c036003401c1c81100300c2081e85a00c0e0b504004c101c00301e41c00c010a001c9a11031038100b80141c0503a6065445103a220394003108000340b550790360141c0d0008440500d800c00c2010065514051020b006008003100402050022901d55008840c0c58000d08440c211190303513580e644c070a5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 82466602 1250 82465352 82465379
    0x13030b131205030f09030a0206010308030a020c1f2301050108041a1503010c02010b0d0209070e0a0801060e060604060518030106051206090d021f0e01020904020c0604060b0105030108030403020904170301 89
    0x28580c14008240000c21740301c4003000b55107203001103174081d2540340d1950720b401055410240c00010100d03820021441c901c1d104000301781c0384a11300c09140140003242500ca02c200c1e0389100d0b0500f814600303019100e2802c010b440c81c80f410361300c090070105082c0c1c5072414081c004400e0030306240c5c0786100700014013483c40f1202d14035845401045000344400201400e04909803803000b800e09400c1028060f0590040c545008003d600a0091070b100c101501c0c45c1e000136442b4040d0346c1c00300c48242d56030402401404180a00d190340702c001610310328541840c040c0c004005104180d01e0701510108106900404e55080d0080307001801b0083c00d450345015800b07141520b640d02a03810344080d200312641d140c01140080340700c6081d1602020b40d05582c8440d6402c10003d441c00000c05100c3d0f56003000290402e41e04d6102500c1c0040820f4000c100c58074180c44c100c411518000221418007000380b00400c086a80001110183c030b60644034021640c51700e00d0081105a07048040003450440480040742080e0034003907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 82467852 1250 82466602 82466611
    0xa0f060c0c09020c1608370605040b0106021c21060504050109020c0f0c0102030906030921180d080a050a0903060f0902090c031005010309020d05010906021b0313030b13120503 77
    0x1179200d58180e480b45140e5840000c00320004102c00c150b031031110a0b03510b00c0c03803510040c20b10741d046046654141c2c0e0b03500100c0c1d208850482c0d8040740b040044c840507a04200c640d21503c803000117282c18541004c030280ca0703200c001080000c0300b400b18140c81401285500305c1001404054400d000c5d0b5612100700102942244135243d40510848002442120300050b10865100c1d040e0007a40c9400e206600740f012540c402482c030040f5100d40031030015440d82038600280c4801003008032a07169420410500241e409845096200360b110b8000c80b00810354550480780c01030003500789540d84440004041c0c52030041030b40050241494040401d10305035164200c0c2c0741142c82240c586c1c10030795410140801034081601e034000c109440e4101801254025030001944030f00040c0070103c0c802441c2e0f84c1c1825030b41f00c490211003103a008640c450303800400861140c1001240800b40d03080c9221030b000840420340307600c40038220b80181000300e542000350f490341005e840d402035030186441280010292081e481504c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 82469102 1250 82467852 82467883
    0xc08010515030c0702061e180907080f01150201060e040f03020706140904050601030902041d060105060403020310020904060b07030503090c01050432030a110306060a0f060c0c09020c 80
    0x801c807500710900c000449105008040245007040629020f1041d01d421020000e03900103408805500030054400140c0451901d0072601410070b00a1400d00440d880d000e00580d003070004103c14804040c0c40e100c0881e0558a111401204092000317001b28058282980101c0c42050080c0500c0300b0322240741c020b10040c03806034003100c178401d9031014100c03441140c400049000d1034003802020312a00e800e8100f150014014035021a0081c543c0d0001401c4803030001c0303c0003040201a03440001c0180038000d4500400c01156964241851a00841c1e10340811440d40c81c3d01c81d9001443c1000395585520000181002412480e2540102c1c6000307066a4002d641000705882541c0c1d10819039031052044406983c1c58004840460300003400402140e410090350340c02c583c3c2a2031036801c0b1a00c0810944c4846805040d05c0881c04250782c06060401d00c0103090a8001c440d00c05051101580e070302000022200e003464640901300160402206811007500420292400068029204040054010f00d81180403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 82470352 1250 82469102 82469119
    0x4020d1e0c0f06020705030a080a09150302090406050a061d1c0b01081c2a020402030c180d02030309100509091510020a0b0105040207020f0a06020106030b070206010f0e06030a060c080105 82
    0x10f0720142d0360340d5610705c54154190300580e80780f40000d5145016040c40032181c144040d100d91903410090850202c00d01e2100040d9021130751072000d16050003114001d0005441d407892040c01c0401c0100545140c0000c0c0402048003181c003480e47d25159007803d419184185507410412051605d0741803c1404c0c8161a03443c0f041d600185441c0da4000d160710b800c264240c590080d22011a41b031450b2040c0000c11902440a1f513040304005070701c1b01d0000798400c14240b40519074075658007448800c01756120344054050352140030b1100040c1c600008440c1010411038641e1101c59203a40c048600e8403c1f140455089136540061020409061246103c2d1860071903041c01c0901520804903036031003c01002510400d0302800421460500c0d500401b034990005c3e061080d543d0b07140c408122802076070344c00840180c0d90344504000388240d010701c841c0c2201d000e1000e0b100303d501d40006480e41481030b02030340c9100e2081c040490700d1a902084403401352540030710280421001e0a41c05800a01c1c04d00c655030242032503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 82471602 1250 82470352 82470359
    0x1101020f011404030c05100e0f0f121602030703061103040204050c120a021c020f04050a1a0406031e0905010c0206070207060219020402091503060a09050403020604020d1e0c0f 77
    0x42c06014a0380b0300740c11115030140d9407510219201c440d55401034a01340140701311600c6008190140302d040031030010080c500480c0703030b5030701500d0f1115a1204660302d030400c6034800071000882085030710490010650f03a403550901e0000a0606001394002010545407003910300e84a8201e6002c1c511a9000711020021681c80044c8200d0900c90b09001d40b5080c4030741000071743ca02d0081d90241110034800006110000b4090341c2241c101c2e0b22034681851440c0001c981000a0300d0a03014039006009070308408000101074404903449d50266002d40310a154588880d0051800011400b040c41004014140004000c2d4140356000b0307e070030006a0014050301c2e00095105000107072450480b500c42c0c0c0245581040b8000088210440500480e8425001c1107061143d07070b50382002c0380c0d4484000b0040e5943e41050810051442c1c40d03540a03a8244c0d05090422000c00d4001c5011640300380c044e10314102140740741c504050070007a03141407603a1100700408284184440400400d040c1d074003d0820540035034a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 82472852 1250 82471602 82471633
    0x3060506060403050a02300a060e030903190203030f18090c1c090515041209050301140703050411030706110f01020702150a02010f14060315060306060105090607050a110102 76
    0xb240805001903101c0c03a601c0005007800300e090034000c030300c144035072000f440b02089001c0f055841610b07808956111010303020600119109030221882c60318000c0d80703000e1601c0080703501e82c1842141c1d444400002007044055480500880d070252007551483d50380d4899074104a80c010421100407070151440c40001107019410b002202c814103081001940061100311042024001e4180e046405004000c00c414181141a42150007244103650110508004943c009c0c101441c90b030040f031090b0b05085c0c02600c0d085118030f505400908610700451199110b08203000b0032840b080382c0340c0c0c05210398007000811a5105c0308140d54100c00c074040d00c02d40c0c1442d400300c5080c0d0060850181d88904660803185525003540020400405180000302d101f40c4074030352100461301c002400600d482c0d20300d000c0009925007400030000d900d582e1580f400f02420110046556424000c1c40a414000c0016801801e0b43c1c50308140c403030310b86d800000c80345150030a01d049440d4028a641c403034054460823901041066 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 82474102 1250 82472852 82472857
    0xb03010606121a130b01030204050607030203030f090a031d041d0c040c0804020a09020901120204080a1101020102070302150c0d1107060b09070210020a09090e07060908030903061603060e100306050606 88
    0xc0000346140b200c00e040c080540c00170f0204c1c0113501d040c0340d803c20000601d0307120040035080042c001e401a603120302d003100a00012000042445139250448210000026082405203482c0d030420007080807580b28a4000c2402003c81100521420703003c1140400b0b01900040c4020031200181c4090204808501c811b98820700c1c2580c0096010280c4541030103e4082a80680852001450000c8107610780300c040c0700880c2d2194016683d03941101d94000203114424281c00b0008000384002c503e40305050310003d4850301c075440301000c83c1c100203001c42c0f102e05105c001d0b80c5d01502002410400f0004442c14030750309070310148080b60801d0070028168400c0c030f0065100d6100c0d080b59005480303d20b030340b1480c0500170b61000e0040c106000804c200458420a00e104240c2e0000000000742041801c00d400a00041502d07402103031a03030708c10001100a0388021460981245038114507001c1c02c03401c3da03070907006008640c209012103a42641000b1b031050f4000004022079000d0101003006031280000d002062 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 82475352 1250 82474102 82474151
    0x303070507050d0317010b0702010306151b080405030106060503010510050a0801060305060d0c030f0b0c090a120f080307020703060b01051801081015030c020601050d17030a0b0301060612 82
    0x1500722010812150900c00c16000c1e20358420710300f9004580b002c0c03406400d007050030b8002130000b0b9404501b440c2117582511405002d400441c178814402c2041c40e10081082440e46481302c440031900103584104103074802034030040c1000030001d21800761901001000d07030700309110b13031441a480c401c00c041070140688112150440d0aa445c074885071300306201600030f0600900400d40205140c0c02a001081c40700c1804d0010350b101d0b500f040400001ea091030403000101038481a5081c2e420068000195102c64000c01206c8000c0c0100c100803c0034240300081d102ca154020b0f107541800403c03c02c1ca9540440c411043d03904c030368010403280305e00500450b00f80c00345000c2c8044609110940440d55070080300701c40d901c0085030080915464903031142e4643c1c41450002c0d140400d0f114010901d0140d0188800d034054001600e0501ca42e00a54903030384221646038007110114000080030030103910560304080b00501c0c024000303110303050351444001d180701500b100140a2602d49011101c1d910605015001e40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 82476602 1250 82475352 82475363
    0x7110102010f1a0a0b04050102030301032628030b090a0c021219020708011407050702120f07170c03030f070c0f060f090617010b090a0e040606030b010605030403050a081e09010c020705030307 84
    0x1c0da370075079440444146014029602641e80554102c01c3d0900000007002c20403040c003400040380310190380c912503621003801c20b40107041c1070220020241d00c40104595008000d1903010488070407002e8160300f0100c4094000061050000349124100000b403030640304156a50f00300c8401c10394840d0070a00303d40c124440342c40c0c110204000b0034002c52080b00a070004600051900c88100c1040c0c074024035000851000a00c11f030082c5904004130311072080300c0980d000070076010b003280321000c3c00029101e1081d046403c038041c50208004081c0004980aa805000603211440215440740000b61041088030350034000601148404180f0134840c0003c81032014000c00802300503424018080309a400085886802c60004c0034005000900b00c0051400b49000310400500c4508500306040c46000c141c0044041c80400c20922000952050442e00400818a40074190741c490f8a85200c540c2d440f00808051801d40800380002110103611010200880d6021148a5a80c0e01d041c180c60703006a0f18060702 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 82477852 1250 82476602 82476607
    0x1504030504050904080c010507020c031204050105040306020a0c080307031e14070809100f050a0606020a02030a0f0f02090901050702011406010e0103020711120a03020d1407110102010f1a0a0b0405010203 89
    0x1507424001030f090740061041e5090760410030061100c078211001120036100503031014442e00d56905062240303010105c64803211038500790a000010701503204a2000600e43e42c0e0014a60380118800c032114201c580d03118610300d039241007861000b406171a00c404014031511369200c02102400503131045183e010441140c0c03210959a1500940308440020301a62450207615141c1040348603078400c07840700e284802c000080368117160700c00c001221b40781e030800303403d40d40200e05103409a0b42c0001d406030103a511603c28445180180b5081c2d03443d001c41c01d0300a41100b0040248110003c040d003160384510710719030081054540c8800349401410701529440c0c04103c01d034000340010b51194000301310700760003620080c000c079482c00c003c205218800e00341c401c1107800c40c0005600b0150306000240c51180545008105548071071180d01b0360b4881c101e0010039150680455250303590007900121001402c0d00010040303540303111101d01e14942000243da00c01c14506d074010410116850503141034600681c025030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 82479102 1250 82477852 82477859
    0x1030c0303110f070602010e0f03040f0512030c03130e0f04020604090902010e0a120b1b03070c050f070b0c010b0306010305151e09030a03050105030c010c030305070311030f06031504030504 83
    0x1c0740141c206000088030f01458180094050b000c0149100910165000044040b25142814288140149004100d410400c001c01c45a50407192036800c1d20400c032403498000c030440103c1850341c0300708102c9120a00011640d60846040c425030002200c50814100103103644043c0486403005048500940c000b20a03c030030f0040c40507039800005414418100324404c8039207180000c1d28901329521403403003510b04513005410031102000141e00700940728041c03041b42041c02502075890100900343c2040003402d64008050010822010703442840c200b090307400160725545180901d51080c407a2958941c01c4c407040c1c14541c10f000030b045040303d81003006458800841e5506012009001d0001c580c5408011098416030544000043c028640d100003195200805280901500d20590060307100f03402007016080e1340d0741c020b04410300c02585450b0001e03c6580c3ca41e01a00248a8100300011000b400301c10002210340303160381d09000e01c2049084803983d094414100012600450700100002c40502040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 82480352 1250 82479102 82479107
    0x13151d030a110d0204020d02250f1106040902130303020c060702130906020405031002030a0f11030403120f0c02010204091413080f0f2715040e131718060301030c0303 73
    0xd001c0000f4045410b01c0690380018060fa04601d030902d640c141d0001e5040003180941866025807445054001c0300094180c841e60034803521800003034448042d45400c6001541c03842c044601500c7c1a000454548003298241c00c050300c0c0c03030700080300036100e814520b1007240b62a4040c0c031403c1d540100030320303c207001c02c0304024050000050304071a0581c0920000c80c003550284030380c1e030810040d2600103850b4509084034400b696210401403089900e8013035203880c518055803c49034400d415041c0380d270013244003c80380740081840180703241000b481c080d1710512456040d0014011900c909a09005030b034042a81c4105099003907075804840440300401000040340c82c80038020a403401440541403020380784c0c00080c1c80e03000c410f1004105005c40013080000c45004440c0e500030500707440109020141400d0400c1d240b24a0092040c200e850310001000c0d900000741392a0103640c04400c9600b103c000400b26840d5410070f110441c16001001c402c980c56042c8003040c2d81c101c81d0480c0420040f40d203140c07801d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 82481602 1250 82480352 82480373
    0x301150512010f0207050d120504120c0201090e0c040f0b09060405191a031e091b0406081504031b11040207031205010b1c0e100e0313151d030a 63
    0x10040954075041030003d0744441c0d20103400c3c1e090250014004c3c070100b01c00000c0811510402c064185e0303140c0310034000881d010070004e80c001102030400b003070300d81c0d103138001a58628943d621618402001404014003000b1000240c02100c140003100d281c482d450305050300c81401030501140e00240180810040c07440d0510002d1680a0001101c50225890740f0009103100303602d008844090f4400000e005c00900b196907440c0c4000075080c18800f041c104015200c1d202e9804400c1c1080c3c038a00607080100b250380b25801000181036038400c5a15000e20100f103078441c6181100c0c00c2d00843c0c480348a94118074104d009260f42c19900007281240b40e000c4008000c02904848000e6080103050301c84c00c41180343c42d20441d40079142003041c0e903807140190074000300105c8901200340c015034108850021034240026010f45100042c00300421034450003c5028618000d00c14410203660003003000140b403881203100c480e511505035849040c0554603130705010882100806050309540710010100c00b0681104c103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 82482852 1250 82481602 82481629
    0x31801050304020d0b31110411161b060810031214070c030203120f030105040b2b0b0610050711010905041a190f0b07110d030201091103011505 63
    0x30040302202c02c5d441d0112103040032582e8540e070700030900c4804580202c0d01e1003c402c0b00710b0b201202c42d102c41c40d0b950300c2c8070b103018045650340101c1c2c82c2c1c4420315901c2070040965000b000d1407020070000d41e54500b04501d01540621201910a07503600e0007240f11481255a58032a040302880146014955643c07480f848513a40b6083c02000b25298403105010081401010101e009803107051880c3d003140109800c042e030f28104010b00301d008101e4200c0914061080e2811034904a500065000d110300205080c035080320ba10081d0076906210080106603900300d86c04816015002c488400c0d0b40752024400104d900d044080042076041c00003a001034400c1e600c0c0c0c1e214003418581502041d80da00041010740b40340300801c29020315000c01c1890203050150184001d100c070041d0311920b07145822041080d42e03050340901041010700044010500610503030b8203068100280030300c80f0140103410f00a00820140404982c9504071841543da945414015440341100400700340400600e00002c00100419410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 82484102 1250 82482852 82482859
    0x130309090c0f030e0309010c061505150d060504090809040c0c021c05010f0209010f080405120706090213150603090309030c0303050a0212040605031501030213091d03180105030402 79
    0x20008a01003015010301e541c1d440c1903840b0421103144511014090b2507502503c20100d5106000101d8141e038020303e030310704850300700c0d0b070018180f0301418000081c0c1c450342d08030355007140070b103500340340520604c600518106030a80010841700380c550301000161124580c01078008142405800310300d25155020001001c0241401e001c501543e50214924448510108030316205400007041800003c1c003482e61304501d000e008520300300e00c007000a85281c5180128108100100001404220303041090707070001445068002e854a005140500c040c10b4070036004c902440700310034040701450150140c2040811141e03036400c08581490070880040030401c03c250100701c1055030000100c0c07027010341031010314020b40c0c0b01a502e0303513008806860311311040401000030b101044200724840c0e00c071050b2138000c40a036070802140900400100c020380100c0b06017209801085100080845840d0310949049521a1110311130f00c0c00360940d03a480380900d0600100088207580e4041d0303250710480065502c5403008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 82485352 1250 82484102 82484117
    0x1050306031f0c02070501020703150c020f10061724100e0c07050105130c0918051606080112050a0809041e14010905250e06130f05181303 61
    0x5000601d6070040e503510b80d030300e0303a41c1d016520111035040c01542d01600080c0020090540b8540d950a40c0030a401d00101d80c0700d82c0d41085044082c800d1106c6190103d2081c111001401e2450901000340450710842c408030790940015640303ea0003040c000581e0001070380144135241c562802c0129000003d16030141c10207505030204035034815541b050b000300d121207001c1352a00c84074036001e8212107018042d40a0040c642640500285242c9542c005540c0c00c0000410340c004010b0401b82114180c08005000d40030f40d0303800c0d49030010802c41d51400c5858503907400322540d81e12020b490424441d0300300a0031a411601581001c205400014070a03480040c2001a0f4804114070401801034080c1c010350403a5101c1e00840907854400f10100c1c054411100c080082d81458200840e50140490f1040311034032224602118050003040340c40803a40f00070f07210554a20480c01c44c105001034078022020740c211081c2004c81d503800e101c81c42c031401d00313064005804503443d414502120068900001c40c01c02240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 82486602 1250 82485352 82485373
    0x91d0604030f020c0d06050114011106130606050a0603050403021b030c0103050c040b03090f0606030c090402010807021f02131d0f100b0a030b040b010f090b0a051b0a0201020f0703050703020105030603 88
    0x4a00c2a0180c4502503800001c0550402d2901011350850a98040c100710400403820b2f1600d13408949a5006540c2307a5076030301801000e00d0a034003c1c0031150b028a44c021300031800050001c0e0160007592046d88070344c1c02d071900800003043c0e940002c000c240d10150554496006c1041c594025400b454121b40b141e0b40740303418542d0310300580c41c6c00d500c12100c0b40d030a60850500c8a1113644c0400855802002c1103018006001c032110128010440c010400380c100030455001c00e440074003d100a14500744101c069903560840c0702400c0c006035002165280081e2149c14000900481c6100f460701302014406c0503c0c0b56480c2c088071360403034102c084d115403030585421800140c0190002c0040c1421a455140070802018a1040104681a07006c0e001d05200b4501400340c03505a22007000c200b600c8100c1440c40c1c070340341e44070401c03121400340c03002500c54030746100030307040c9192030002d1410b258030301c00d80c212058406044441511900300d4131000f4500c1e0301541d424401503001e07201840e4000750103001c94520514 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 82487852 1250 82486602 82486609
    0x31508070b0d0608030408070515030402091315240e01080d031e020403050d030c0c051c0309050613050d0c0b060f0612070c15150b0705030c070f091d0604030f020c 72
    0x4541d0107d80aa07000000402c03250800000e41840f03c0c030900c402a045160030307008104803140c0180f00e02e181c3c48074050303e40300f0003030b16066007041400340840420045001811080c245140d0500150302083c05402c00501c0c0080007907240d044c0d0340700344054030120340b43c981c060307015042050044030010b50310000004030380500e10240000f180500f000f4503518002000c05406c4542a1011204104035006501d01041001422003000742c544030100e05940e102e010200c004102900300101180078140a001d144040301c04030303044d0203010314152031842a070783e072042d100c0c0c1c201b603500144801c2d03030800024864030f0905410207a07404007a003c0d81c41d001d9250301000a80380100c0340703203001c200601c2c40300b01440056400060740012031502000320345904428203089000d41d02c552240f100b0000340e42c10070440c003402500d162400380d4084442c03858482c003200c140f900c600c0c0150b01400d8902081c15005000c04600700249186d604007404031901c2d6900c0031500303188160841d20551107060500e541948 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 82489102 1250 82487852 82487857
    0xf090c1e061236060b0f030c1212070c0305010c17070e060d0c0f0206010f050109030f081b0616030c08010509131502040501021507052208010903030c031508070b0d060803 75
    0x41a40052400355242d03240580171550110219402241840190401034a0024025400d05022601d0590410040c042945091000701400c1e03a842004100700e420012500c4c0c07540705070b9114400920a211220b10102c41c1c3d101403002c00100646c68030701081110380614074501c1c1c3c854028016500d031003903108588040d1000c80100e000042c0c6059440250541d040c000c41e40500f80e621005800c08d40341400007020f9109034000500342c0d0708910190350030408200f003140c841c800b28140e00480104500301c103548481c001c4a04003550340b0260610710120344640300720300c00c107410350302d03404026401e050a00000b500010704c0f4400420100e83c40781c004c900c1000780d0340c02c1403021030340150707690341068002400c001050b203c4501c201030301802d00c81010740107401d40300782421000700048100c400011036071041080390f000380d40f15403a0000180c02c1c10b5040d00802081b03480c0c1e45061061302e101d0420032007000458810144aa000170310b05018004948004008419107844003184080c1c4440c2c3d00c0303040d82d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 82490352 1250 82489102 82489181
    0x1b0403080a0f11060603030f091f091805040203030f070305091807020c01180506030c120702060103020913120503070c0614180304140d03030f090c1e0612 68
    0x810300a09214415401a4100c80c00a00382c2e01904c41818100046656030140301d4540e880613001061040d03040e280d90720f04c4507810301000c004e0f40140f16484406040e140700b0307021781401c19403190600c040d480f031a4002d040c0030b9613003d0020342c60000e0030040100503030001c40341101004401c100301105036440200e0050b080480e2481e580a1382030040001e450100f1491480d414495900d034a030f11550401d006400c11a44140d8880741e81e544c0340303078610813140701d203030a4820282c0c8620188107825900051080c143e0f4401d5036070700d0807516243c40c0c1e520340e45000140103142a40d66410300759240c0c8a4005907402c120141080c051124503591188141c8008003580420554035208000501d08484160451074542c9009180340c14101980b071850580c41c05900e81c01100520301c0c910802d0310a52110351610020b4500b000060b84504c0c04299040c40d5105d22a039084446501144404210404008842d802e40314a8110100e622601c0f0203030440d90a21301c840034031041079130300c0310703003a0003030303216107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 82491602 1250 82490352 82490357
    0x150306030f24110421050a0b101703030601030c090503070824160c08040306020c03070215030c0a030b030c0a0605070b07020c0603040609051c02010204030b15091b0403080a 76
    0x41c031044240b00a15146a01c03060030710608280b070007802070f0b24000032502601c242c04111240e404a80148540138084820300038461300c0340c82c0d0341c1018040315039011030040720440c89a0800d9580c500340300d107111822124207400da400400c003080803036009502c04c070441401e60601d8400340d5594400203041600c2e03548898107607008901c1c500d2483c0c90307004021602c070a06607210041800c2203220050109000b100c100c0900c054500003005010700346003524002c540c0040c05646d41d00d002c4001d69140d40007064100e000e9000d081030011702d5042d4000ba42e11610f06009040e0401074030000440280044040140d00350207121812001501c07542501c80142000e91940340e0f440c0003d250460804100403e41c03000c5400202050700d06546420031250065042000410906e20600700a824002d0301c6030001008015201002c00244d01900a0001c4234003a14940702a41d590441c414203602c501110079910810002c00901007003c517508090014550851003070070f003034495440b00255400100e00380c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 82492852 1250 82491602 82491623
    0x16110c0303160b0a090f02010f1205040c060e01020601060e040225050d11031801030506030312010f050a06020601051003150801060905040b0c1602010e040b0a170601060c030207150306030f 83
    0x10b1251002501e03402c8101030004214654486d151814590f500c0d0700001c1c108094174840c07116545c0b09400850000c2d040c0001085281402c2c41e01d00d84041c12442100007241c0c0c0082d03448415030021419604949880d2500b5001940f003c003080002d41c400d1103101c0305000303032001440400c80c0c40c0591341440c600ca40b0080081214003100504609502400125035038400c010040c0480400c000f03040d82c8800038200480c940e181c0c0c20011f8218024640882d09070301c203040c000950b01c4402d4420b0701c12a442616154100c5488850498460030b0902449822a10b000b41070300c9051320035409291242c1103404a40e0300c440e1200c03406ea0941d86158040f100d125160018401032140c04200702d9007140c081e80c070552074203550320209600e10026a4000c1e042c4038075a02614a01d4030385401450001c40001c0800d42200e4440750b03c12144414111500328a210b03080001c5040350003002c080025a8040e0010010146041c202c0000700b8a17200d00e4104247d2070381c000000081c130311a82da22916204041040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 82494102 1250 82492852 82492897
    0x4080303190605120d181809060516090e06030307051006150824030c0d060f0c030b06040902070809090106020a120e0f04090206070b090d09050916110c0303 69
    0x2e440c0c1c0c642045204800301842200d040100083c0d41d40040c444d07052000008540b6410010f14103910750008039601d800a14503200526240d1050010b82d00c1098100101d0f02d4101445005107444076056020407503001040c4201d5460310003103913000c00018200c916042995031a103040402d0381240050032900c3e088107000f0090015903411011810745050203051030406c42c80d0f002c14001e4100841181c145a004080c4c07078400f40031030f4480340800b40604603108103501d00b0070010000d000002c000c061401304c01c008800d00c42d0080c41c1740c0d640000c1a07a4100781c01c00c1c4840000398041c000c210b80c51002080f40c40c2541e20b4101500b8000c00507600a490f842e186800d000000564030702c0c4a030b0400801002c0c030303041d542d40c0901008030f0000503540000d0642080c030116030329100e800c201500d103041040420a00040c0040c500c2248600ca54554810594410604c40342c0c050070b41d4010704c06e04800445800c242e104044034900131011a0844040642000209046031312403140c10110151030071307004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 82495352 1250 82494102 82494151
    0x809031606081f1707080d0509090a02090d08160506010f030516080706030234050d050309030304122d0315050f011404210b0601020a1208060604080303 67
    0xd5000074200e1108a01c0c0700006419100c43d0300d40d000c1e515010016156088668108100301806490b40d00122801c0172200640a44590400400503124a0b0b4240003d5044401e9000340c82c80444d000c0c042006d41400c55644071060f801844819482042c140003000100303100b0020b00d4000c00d6034036404103181d815410400d00f007148680e000380030311303003c40c0e070070000e82400199110440300d1b18500182c40c0c0d10802c04460341d01c40c0205002148848140110380c5c801d41c0a4001c0c40041d01c100308540480d035410009aa440c00211036110007a0001e0002501252100100c0c84200c1c0e001c0c9030802a00004010320701019648818149070300004203a495140f075090300c0384000b0414800550707101c2920305400540303001d003254080c43c10031103501d100c003c810b62404281c402a16405104480a0b078958102d408080ba04042c10f40c2c030f090308440403454550010807007440c1300e9080f4400d0900e21203841030680d420007002d06542c8c0c00242c2003100051008050000d180200810085a8000b00349121321 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 82496602 1250 82495352 82495367
    0x10308090111010203150918030c03040f05090106120b061611010e0a030206031f170a05070b070206031f08010c030b0f120a170702040e060a14010f0e040809031606 72
    0x2442c1688100144100324014212000311030000f02e81c098240d507602013001d444420032602c05070152201054402d4003100103c00b80c010b50f041c00720820209561902045001c903820b1082c01d020a56206003054149407907041080b48000c0640003525145c0e00b0b80f049100a90440300544079504050508001c1e907900041c0a1448a400c071fa402c04802c0c21600001d4442c40098951990541c0d40d40540183c0320760f0b820018002d200350060542561032541000b80c540f81d400b40202c4c2c0d640100580841c40310303414401c0d01c1016130040c0840d0300750f6030f6050802078000a014607418589040300c4000840c150700f402050014401540c000c1694613150091201a0f40d2024a440c843d9504030184843c801e4001440300a0507005015510328503480ba146042c240f04024029400a081503411900030f5000290a4013804003500104040f00d400c1060072084013007070083c0200340c0c802c1c01d020024a03c0c2c0c1c040060b0824061544245030211420002e803800d501030b4441daa900d018107208002482e04007a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 82497852 1250 82496602 82496627
    0x907050706110c19020301090204090c030506070302160201030c09080615040506091b16121d0306071409010203130e04120e010c0308041a09011517060406020906070b0103080901 78
    0x2d0703051501511020f600e030800140e0540c5090a102c0a50055583c2508468403403500503000300440301f894105451742c00352307a000c1504ca074402e15021a1080d44244222800c0740f062074400201c1e099668011000307460003902c20410002341c0d000c00302e1400d034184006405440a24941c441d500501c80600c0266400144214403d110305010440f0301d800d41c200103440c0c1219004500d03640e04c030070055060440d200d0700c0040c1148410001c0a40820f030042030388105401d20340420701045518808069444e1400c552401c00500031a403008400c0011101800c290310050055078101a070380c03048003030201c94aa0181c8001900c1506000a2080c61180d0185840644c94013642d000704240020b0039481e40d51030300404208103070000500b07004803221582802c0c03204500d01d0401b410300140080c082c050480680c0c01602c03003100c002480d0041d4031000d10444c0340c14005040c442d602c9032503520094103d020b200707030800f0040110b9800990300c00c0040c2d0103140300f40f030016198507007080010701d070640c58074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 82499102 1250 82497852 82497881
    0x123030603070605040b0f030c1608130e3610090b010806070c0b040231061401120e030c0f0303040c0617060904020112060e0f091c031a0907050706 65
    0xf400100810b0081f1845a0741008403a682c9407200a10820300e840703100d09c0b2a4030394245517071507030070400514010303d258441c20308540759050f00c401545150030015251086010070b4150f0f50065186501a94044055001000004030b5402c90b001d9050190346083d800e11a60354270b2400040007c0e04280380d01405250004000d2490100000303080020041400342c81c9004500c005030840d950340300f820f249182d91812502b8401000410701c07440c01c495030301412201c4d0401d03070040b803000c2001c6924604840142c2d00c1c3c1c83d943c046034400c9401404084101511400100402c0c90104020000031a0040c00c140c02107035285840e0810707c411005580103401004036011121402d20500445140c00c003a0071600c06419072198401600c0b24056239150043c0c1c14105200092040b411581d4a40b1a45000c50031703031210b56070a603070191a4111580b0984038450a045699081c0d44030f64046400703121600c00080c50004d20000007104104211840c400080c800270301d2204110042c05204100715542 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 82500352 1250 82499102 82499107
    0x30105072127060e010608010506010f0e030703050a030f090b070804090b0a05090109020a0318020a1208120a0f0c0309080904020d020d02040b030105011d01090e060123030603070605 80
    0x200e5075040710070a512607450060ba152480020709219039066510b01c0107000c51110810b81d0b0700c1c0b40103c003030f00540100c514a540391000008000406000b0789200f1031050790740b801c0c541b02c0c5580c180c0d01016201038141d0103102e04103001c00001c1003000727507a035160b004c2c1d02e4143c0c05c0000740300010710b090b5a41d0003400e9041002d000c8140020218000e07038060765001c880100d01d201c10b0030003041c448040c6500c01342d403205000b0000142920103500a0501100c259000c0c080081c0a0f400401c00c9618040c4c02904001c403003e00b08100c002221810700510b20070220315107408810341d0300545814007a100c1d414110b46c0c8071298000b4400c0340c495980d90f944142000c3c810286a81c0310f550050142c00b200e1402160001680c2c4110345490b4100d07100d00280c50700c00c41d2110341719050314030543c10902546010070725603130900360f500100803100d20b0300c1d00c2d0594034901700328200001c1603401d04001c0c00403410f1041c09030141e07100d489501b01010700c1000450807503807285031400800d864091075074861030600504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 82501602 1250 82500352 82500377
    0x130e03090120062502010b0d14030d05040302030a030e0c030a0b060307030507080d0f08090d1b051504020f01110616050f0406050403020405010b030603030d150504060b030603010507 80
    0x10055808102007400c0c03045004600c40c400b00068440b020005100d80180c4041050702d03403111400100b04c0303d12800c0c0c10803003550050706a00702c0350343c6160103078820051804c2c07100007070b1038540070340d0080d003030b5000d40703084c588100c0c074042c2615401e50b41100581c00c04a42c1c829107d038544034940c3c04240c0301000702441012080465220f45003424050710303100240000860607101003141100440d440f8040303441703a41d60b4103526512884103103c28400034020b5800c0b941014401d030903081c040c03030701304010f046580c05000c01601d10380300d201100c02940040d0090701010400610078130038401c444a14089140c03505104001304e100b04024100d041c041500a120301d2030400107600b5600c10b800b03101701c131a5100e00c03280a0f980c600641e90795101143c00003038049030450f030010180049900c01e550512183e40c80300f407181c200c0e0004403501600740c1c0c001e0010b0200902c0540000c0354081c01e00c148500d100361644046400e1b03501681100180440002c1070102c44e00b403d00c02c09034020428500094801007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 82502852 1250 82501602 82501631
    0x40623060f040b0a05030a060603050c060403051902010c33051006110a0c03030f080604021c0b04060b0a0207031406010305060606130902040f090c0f0203030606070c030204050a090213 81
    0x21140781074011682c07030021074101d0715495a028081c0c50300030129078140c40300b45088406440d090004840b54001c1d512841640d0500e03500341d4040d0781c0e101024012000b400c5816400550000310264104103903841200046600303000c400c00381d000340030b8084000c82c580403034000210440c40c1d202015180b0703150070800490f04245642054910301d00e03061301565020a5074501e4100100405407444400040000c1015003015000d64002c400b522060720542e00c402c2000100d002d851402d2014006c03059500e0070000b220f80c4000d5070b01c00005c0c000a0403d40b151807005a58009142c200050b030b01c440d00600511a2a040440d09045948001c1c24290704643e100c41d11810054102409500085001e104980007142260054000048210340300c1d0b65454002d20445094480c41d24210b103018101d00e002807190a4082e145151070f0000e600e15110b40c0180070365a4000c40c01a5955011540c2c0400140c3d924020380e4010b004110780800c03c5101030041104506500802c0415985415201c001c12003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 82504102 1250 82502852 82502869
    0xa2406140705070506030f0f150306041203150807080709110403060203060112020712090815061905150304060b1008010506031005040c0804060f0c0c080a030905030304062306 77
    0x140102115901c8200500c0c01d00d1810b940d43c1c01240d0b00480100401c2001181240105c2c4500205400d000c2c16881d02c8880b40380740308a1180041c4c05070419070000300418256800e01800c070b0074514000a104030103a20013042c040e0660001142e54011900030041c1440c2004046e0181081c410104900019501c56607118412484010321036034000c00001c116030f000c0d41400b404100841c0065680d40344d1860510200e607034032201d050105041d07080c0807800890004145c00920640c1085841584400302005a010000030040080584007000402c59844507842031120900c49004c0070740ba4109450600107544416000d0f034001c03081c81385140c141960202682741100c00580780750b507481c0c6072541d208a036100203070409a040350410704400c0300709600c1401d840c411800386004100c05040031035400180d402d400d011400160000d045040031031700c072600030311030000c482c100000c1c00e03000b80d541c25041d43c02c129005e403040c1d9500c03085220510840b040b40e03200c0000c00e0740310803a10710b4800c00040510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 82505352 1250 82504102 82504127
    0xd09080a0f03030b06040e0109060b090102210d020d2c1b01030914030a02060a0227180106090807050a0f0311040605060414030705030d0804020105030a02120a2406 72
    0x719003460550041c1402540510540c0101800142da51600c0740c0840c11012420b100320030700d1500d00f55001821100c80d5042e220551016405000c078003c8545141c554441c2c12116445600000c206988400c50584010924040181404144401800071982c006100054807502194146071484103000d0b011420500c120700ea00c103815442440000102c000b802030306001000b00049007601201144000302504180c2500e0342140c9450f6549074000301a030251070841c030f001076507504101480060700904214811400b42003c0c420f001c03800702c20300304142c00384d10520100e4400c502c01e120b80d11081c8039142c0540415220507203042c0ca0103821802c0907030319200140140c50011101c10040c0d883d600104000c14006007215100e41c0c859031102015100046003520901c2000c2d03000950341004240401740203d19115081c040e030721a0015203807584014140b052180c1c1c01c02c40b001c1c03083d8840c40128042c0340124030000d500000c0091601c042031101c040544951000c50042102c582e2150011000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 82506602 1250 82505352 82505363
    0xa03080901021303030e190803090409050a020a0e0f011706220c0f09140103020612041b0b0a080c12060f0a050301050a1505120d03021e07050607020d09080a 69
    0x2296129000c080c024081c000c00700814002d103040010600d42d1005186240c80707800c0313a41100e5a50000e80b4529803000d00c2c1700d054103580050000301514501640b1151700c0c54000c80598015491b981d0000742d940c00c1030741080d03000035080350900c401086800031007405403c08a0240c012070030901c44440e074801c00100104070408001d038030866286280b00301071750120b601c01d500e4500309407110411070019041d400b484413a1441e0620700d24000c0d4221a0541c12640c000e050a803800742e1001c80b60081c0200100251100d183c3d810320501e040780000641c10013081910841a281c183c2064010b202d0755002c3d00a8903174a109122110031201085030960700141c00322004000142c1c0c0d01d000c42c0700c00d441c50340131aa00d5407800d420420441107540160206680602c0300042c16900c40c0200700e00740416031841001580241c041040d986c0c080e074003d1107018011007140403490031645101c1031035880303454200c034190850010f01ca403443e01000001d080d01c8082c109503840700c0c1014082c230341d12481568003902 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 82507852 1250 82506602 82506617
    0xe0f060d030e0f130912120b0d06020a030e190209071716020f011a0420030106030b06040504110a0905030616030915110703020d030204060e04091a090a0606050a080a03 74
    0x281c0d501d8542034054040c809000303201e55441424980050101464204007040c900c10300400b051f40584140c503044000140483e4154585442e00e8000750000300218092554800e0642e0781d40e4410801040004518401d8540c00851441400250003018101c0018031010381c225904417615803112a9006150003101100a424031308c0480c50b1004a0284441c01c0d40b03440d50280030212840402c0b41114800e4600740040055000c1011142c8004c0c200103500501c180010b204462003900440d0b03060200820607400c1646510010b01101e2a54040c0401c8040000b0004010764004040070700400044014000c42d04c1c282c5910085001201e5042c0100341c4d0322102c550070001201b5400e01d50030007554007000707040c0442c4c0c80465103030700010054000d8410301080095452003402102c040e600700d991040d0140001c40c0501000c0c191a40d0300704c03180241074020204100c01d10781070a1045a121000700300340321807402c103103040355015041280640c03d64041480340000004003810020780c1440c1596 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 82509102 1250 82507852 82507879
    0x40212012909091306020406020a0c0b0c03030f07030b040f05040605100602031e280909050108030d0b0102031c021308010203150607020a08060c04031101030c0c03081f0e0f060d030e 80
    0x100982d0913401002c4903c04540030510503400208004c000c1e10130407440d40c00301e40b40c07800481c01340507a24940c64950f0040001034440380b060080030740c10400d28100482c65100c001c001030165600071080051041e90b030404c01051041c08e0140a42182950607610061810028025168171401c500130800c1c10341c0c609245036821086c2c080b0398104058020a1001c2d41d460780c021303d090800c48444100140d080500424501d46601c54103040702d0319035000358948540740c217003030001d44410018541075020901444024091319480750f5003070020a000103a0381c410040300c1c48010000350304240d0311617105000b0010842480e2803502e0515030125686922401c0500c001220070742c0c650004040f50007150709000a03005110050b2080c0d84c81180e8030090000d650004604aa81e1013600d44000381107011200042402008295000f50302c0740042030401044001c020a06182580025141000740c0c0800510003040600c00d42c00c41411559610b102000c0c0d10000d111010360400307503200f0b103a44181d50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 82510352 1250 82509102 82509121
    0xc0403020a090203070201240e0601030204080d0f020f0703080f03060319030e10080708130314040303020708010e06010b0f0904090b0702060406050c0309030706180204021201290909 80
    0x1140110380c010a0303510260344440b000380c00380d002902c404c005982420154500340e8845221040c1100714040010011468411203013a884406031403d8180340d403c20000c5403e0304240440c0400c0965501e524118a07107058000740f80c401070800c111040e403c0307454180006460368044901000030000080d403031352610f800003824000e0035030008180d441500c80c4c01d0b0416422400304050b80c80d00301c51034000241044020303510000d04a8440001442c1c01d80051001d0a2841c412030145c0d000b4940340b01e20a54030b24a02883c1d030b106410a8025a11900342042104401d00a400540d0402d4002e040039500d082480c080c1c80c010442205034404021400304400c0c0c807181d01c000130341e40e000038031100c150400184c060b454490995054482d42e0800b0005243e030b04882e000c9a00440240000358540605900d035000203008550307500d84c0141d02031201901503a600c0c006000080156081c032091545880a0303855003400d1040340d49800a0f01e036444100d0054041c090f115404000d80f4004c1440c2d4078004038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 82511602 1250 82510352 82510357
    0x1805030304030b070305091c08040c21020a0b0f0f25060e191104180f08040e0f06010507060209030c04060b09040c050304050304051c0506010603050708060117060103050c 75
    0x115094440460000148800441c0c5a8000c48030358070200810707100c228105854100d0030391002c40c502441b40198100e40d00c10001c01d81c0c4140145a420640d54445c0c86055950a03101d003218100441c1c40c03402015441c10440007001000144501880c103800038081084a02610020341c0440a0215a200d152494407034820820300b421914a042c075601850204000c054544840101d481400b1540120f1580003204084064215001100c2403a50400300b1000c1c019113501b000081c003135544c4000000d0307014892035034454410307038009448038103100b582c1d4080d4800922040111101c0c0c002d2043d0350b60003501300c450047e0414005aa1481c4041c0032030725190404c227156400c1442c2010010340814090060002148100c406100070341031480c00301d8260005540280c226002000100218545003020003490f07540110080f000c0380c016101c080c180301099000101080c3c42c0d804020358680e000c180030394030060908107045e8448884680101110b0000c00c03460501d985c40e800301d10b20701500d20a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 82512852 1250 82511602 82511609
    0x30306300303070206070f0305090c130603050105010e0a15030809040504060b030f1b01030c090b0702040603120503010905070c030522080a06020705060a0204031205091c0303090201080601020d0f18 87
    0x440b03540b42800b61000355107000480d103010001e60003022856406e8402d004d00d0740200184002004802c900004010444680340080552556604c42c0080058022300600b03000f842c1c0304420364014601000d44030151480c9c80441da0120304800800d100050003803055500c42001078500192541c1c0701d103400c1009108c0000120f51501c40c0302e0b9407640382070b40000c0040d540e1181d141d41e211a2000140150269201c05034800b01041c000e103800c0c000301c00e40a0152820600061000c903402e0313500c4d220aa064442c0c480181c1c00520300000511078103080703000f62504600300f0f140020311030410780c030020032601482d8038100d600c614200400754258184242407014148034000c0d030700b2502e201d191079002035002c41d10442d140d00855000031800051403003510112a048184039882284400c41100d803135204001d62940001c00502c02080503039005c07006070540c0d101e034400041c1401c80d40009401d82c50002c22250443d071000ca0160041588841405074102c031900b800c180c4aa1004428000075104c2d80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 82514102 1250 82512852 82512949
    0x507030b0702100e0a05150903070f0501020d02030106090f080307080f031008251a070201120212012319090c020a060e03040608010b04030c0b03060d0203100506030f030306 76
    0x305560404d800030403201c0080b4481c00032203541c0c4000c0c0175443c010410071640c00d42c064206014250215260415114615102c1c9000600d84045076000c08202d81003030b00180000f4101101c140280740c002101000600070501c015030070720b02c045d5218000b41c4103c8503514084c000c0880400c03044009620007402422024040d5440503040c80340ca500f0300d07002c0c0022210b4409440c41e0002e00c2e0303801d80000041360b0700c0340e102c0103140291030780041d1003408070b10f000703070f03020355820407500d004400454030260180c103000045603940400c0190b0001001c6c14000d00c24420300c42e00800007450b02162000c002114009503000c0b400300740b002016818500300e810058506403c10034103111400003c0700030003d580260311996016602c40c2303119040703802036020040c1042c25060040c03141d00c0900c4081d40c5c3c40307078005101322680da0300d6038003090800051b07001645c0140d86400600c420351400780100e0078888500c400035411890318400052009500c10200030042d517003034071404200e10b80081a41c01a08111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 82515352 1250 82514102 82514111
    0x50d0902030609030c0106380c1b01090506090109031403090d0803010501080c040b0d0b040204050d05280b040b0417070302160b040308030604050702070812040f050405040507030b070210 82
    0x2151668003091862125501c2d000010075601c420180907074040c4040c48c010100c06025070001005484071080d0a641e1340428070040c00b8450081000002103000034185c0000c8884042c0090a00c0400360005841104140400c88159a21654400440e80c00030611020300519a144c64210312682c08030a030045002800c141c20300410000071812580c00f80d803034030780b550384a03841103405000b103024040e10034074100042d013442c00c1240c0103800c0c0c44000400051401d82c0d00c0c00010310407083c500c03080f60280c0002c1c08000c0a604130510f40840c285158171059841d01e07180d5164010424000c00040c8855212000300741440b0890310303800300d10400140c40c41c1d0b40758014203001e550b682d07604641482a98180801048000702c505c00d542c102c030b1f400004c450a5032140800c01001e040020300300c0c401c61194420000b4161010095249214a0761114554072030401048010500c80d5070000d034011340c1402d05100c00940c001500c030307003243d42019080404c0d445d191401c90403c480c05034102d000c242803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 82516602 1250 82515352 82515361
    0x1101090f12020306070306031a060f0a090e0d030605030d050f2101150201021612020f03040902090a050604061b03141209010b0d03020c0f0607140f0709060e010303050d09020306 78
    0x40c03001c0d0301a9603008074200d440c03a9680e104103d003660111300001340006c2401014100311030b4230180307468100c41d00034002d1401034450800b007841c800c0d0a62050b207105498000e00c00c04041e09000d00e180311301161405001050610011031ba4400b8961700d408100400007401000030309410040d0f408055035880d01c0160b54210550340300194600303008504058076000c1100e01010700510840e103103c40c101402010340030003900c1e204003242d4118140f800707501541400d02c40f400f10900040016011205006858a42d15000d00c262007020790460380c00b610b01008103000b52900a2000752403000d41a04480104800e8501110481319044106804400100304070400113010311000b0300c12600e140003002041d11580802a20802680010340540c03c40e800a2300182402450038020480141c1032a03d00324440d521690301000003100d2104581000c50016035002050003400c00414820300c00f0301141b810804030803031104040c4001024004009130040e10310f47c1640181c601103070010150b881d1480e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 82517852 1250 82516602 82516619
    0x7110309040c03061809030813030c060c0504090b0a030510020c030f070323160303050606071b032f100306030203031c23060607050705090c0c0d08060d1101090f 71
    0x1141c010b0614240f41c000d105d405410203032042000440e0540d540b00d0487d1a5043c1041c3c8101d43da000030342c00c002d0844082d1011842ea030107a454101141d540e1140c2d524901090340081b9000390303071000d100707007002142080400d00018000d45140300141c00142d8ae545903480d030500c1c0d4401c04030105641e031b001080c400d09154001030a064980b0501c951401c01c2092420100410301c680303034185d44c04100f12401e010201e8031075845141e106030060f290910b00b0f01c00d520350203500c00c0c02e02218110880202c03800c0c000c100f4170b10104a070030101180685004048415141c3d050340d00c2030007103070182046c20000502c0600c030340c0105009540240a90b56602d08a8040e0410b11814408a45065083c4424102241c0058894404144c9013900d880511b403510b030304105850344104015100c92141040c007080701ea03114a1041c3c0950300b8600b286585551502c80b1a003803105039089601408031102c10050151108407001c545540d00c25030200101200790010b0301d05549a40201c000d662841c030b0045074000c1d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 82519102 1250 82517852 82517861
    0x60117041a0105040501180b0127080c01080903070b100b0c010b0405070e0a0335030106030c0c0201090509040512030702030403031403010311090a0207120f1107030b07110309040c03 80
    0x5512403160720740c0c0c1c8034402e000079a0702c00c0c4107001e42600c0c45100c03c0b00355605580300c090380410501d80302d41007516068890b03840100c086080403540146080411040368100401c140601c002c5c207203000c00d03240200c0d4964680c02001000340584070110300003060038060803000720207001300285030381c0ca41c0e0000010900829005186078061817a00300811111805107008401503140104203040340340c10340e61000c8200b4548141d0b200c10240b00c650142c0d108040103020b0900c1450042003c0c3c40c0d40c94440010292424840302d0824000c0c01c550f000c0160741c2c00f540e80b80945005840180550702d413440c0c183d160103e01c0544590072034000c000d014100c1d45c0071000b0310071240284d807810b00030802c84105000c42d20080c800100003403082a100c59607414600041ca0780100d00386001030070404e403901c52030075580c014100b0000040710030f110031181c00d4020281010121054004100050841d43c13006018003001d08401c1c24002542100810345500304212440c3e440094003d008103241c0e060090041c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 82520352 1250 82519102 82519133
    0x9060203061009150f03110412050d0c0b0f06061204060605031218010f1103181807020d0e04020c07030f03080702030a0203030c07020406030b1306061406030a0506011704 75
    0x4484024180d200b2601c50b04111060702c010070441034022021800907a1400d504501d81d40074580c60308140307041165010040c00c01090b1081a03503411521520b4141c1c10250485818420b00c04a0380d41500071036101c40d103440d4080241d600450158651400060842c0903000540d1800f040903c00c200402645d90880c000322002501150b400340d111080b0550a405001900c034401c40160980b0209503100d4408092410294100850100071f00d910650440d800154070440409076035142d0f0007181012405480e010014814055103802c010a0007911019070001e4607040218401c8510100c0d80c480d4101c980b0003c1d00390440307a44c11350300c1c0381040c1d502140c03400c150086200180056400b90010080b240200d049501951460b03446107007420441e00191030690300185d03180004000982440703205800756407554002440c60b4420f10341081607850030741140200c070345c001c9404403150710b803041a00d802034681c0502090540e0342c580101c07000d075803070341c2070708140500c0c60300f030106001d2407a0100d885d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 82521602 1250 82520352 82520359
    0x1107030206090612040f17181509061b060615091e04060f09050606041a0310090608010504061a0f0616050105180606091603020d1d15060d11060304030c060906020306 73
    0x10b141f40c4402d082140540c1d503041d026100042c4a210062528910741c010812514003803c2c00c28044a000c80e0464000480c58010000340748072088000404011496002100701c40e1191060503401413488540a501103880c05421514025a0047e04801c40d4130782840000d041004015650305031480c0440f0b95104411603d80390501107581d60410340104d50540d030f0500916506200340e07180400c3c403580000d003041100c40744907101184402c0f95000341e5004100301350010556040c1410310008840d081440c0d851004d44040903035106803541c403458011031504170f80381c40d2104882609200d80050071039008199518003820803820441c1c940e809105803500c441141c5041d5500d0303003840601d490035100c2c00d500031401c0c101e43d60694480e8009040d071104000000c103241c103800814500410458a03d0a403d40001d15a02d43c030700481c0d842c1662128040394000c2e01c0c183e840d258110402c0036401c5142c001d9100100180605001c0c0b0000740c12940e1012080010031349a0601c1002900140ea50750320 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 82522852 1250 82521602 82521623
    0x30d0302041e050a0302130b060a11150114011209062c0303010501090b030406020c0604050f0111163806090a0e0d0e1804050601030b071107030206090612040f 70
    0xd0303101c140203804160f5030080c4c0014030190441c0c01308001548800c1c4920030143e11039040101d1602c80c00302030101c000701c9032200e10f03d00f00703000303d164100940e41c5030800c01080f6880040200c40780c050b042901c540028203002c80154140c0605002074030760300c40f01400b82403c02d41c0c8214404090414004030011203e05040d25003240d40c0100d4407440284500360000300b914109000241d80c100003940c2140c41800010b140c00d85501405003040011101030760703250003802145520b041d0a02400d400c100c10380128516000b081c203111140f298420502805e104044880c0d042c0e0701c0640494a0850300e40c500c002400c046e161005619802001c90f50540190164008610740c40c074036003c0c0301e40c01040740d005041c02c0e12200344100c0e051000c1ea485030b81c0c400b455812075440f62040d000982c1c011030040300945043c2d03046042c20060b22801820b0407040280300c690310f45814601040c204140d950454203142d0711007065000950501900041d030306800c402c48103001c2000101c404800d40144560000c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 82524102 1250 82522852 82522889
    0xf0807120b07140c0607120e0f060c071407090912050a0806130b1005221503050702030f030903070510020915030c04030501050903121b07030e030a02030d030204 71
    0x10414180240300400001410021455003405401d5440140c2580000707141461101d100303880ca030404c1520014042881012142880681d60207286a20511900100b14450200307003169034620000b071021034202404104c2008001c012203603003c00900c2001210348007034503103038004010048400100e030303042002904044107600400503180b10369180e884040741e0b030b035a4a0500407900fa0300c0c0400340b0b0059444485d04c03082d68170200540129009030b51550f45880400c140c00e6461111000e1000020304405810041e035040c04610909140c03041c0b40204250702c48080983ca14042c4801c107516a002c040700b0400710f040c002010307141c9580680304a40c1110f075000b60050072841001001c80d00002c3c03154001e268444418010f40d000803c0042d0f0628141d5282c070b4072400c4440c2500c12002613080005c00074520401201055000000c2c103007181400510820302d514071f81724184008090140210005416a80621200180d81d4014090300c0342d030040840001c0c001d500600480c00310310000b02204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 82525352 1250 82524102 82524119
    0x106080702160504020304030e030303011d100e011a0403062a080907140109030b1302090a060518130b010602030a11070b040519030813061d030d0810050303040f0807 73
    0x400b20b000c5082e903490142824180320203540001c0c01136040c0300d14524040303a03075141040154001c0c0421054024240110050030100c08405810b080ca40d500b018000e00c88840401d008904461881d618848031940c071114114180c003580e400502050b00e4016102c041d82c032145c542050f206550411000e8003100804140c941410a9645c1c00f426400702005000320419a1018003040c4814140755017800d940e42e80d0b92242d240c04480c10090036a5003003282c02181084400540c210341400700c10704c2020b042a01003454074000c4001c942c2c00b845200c010410341d0a82940760400c050b004801038482c0e68541c00c0280d52940139038a1072000840c1c8800010703003c68082002004d40e404000c069151514203810070202e40f9020b1440e40c00c0b1005140000300142d403903030041100300c0030181c10702c010700d18284010780303420451034800b812004100aaa90300d543c01264000707022060b804d0443c22611485003180c90751155400940d054800042e000caa20030b40b40b4810812201030710101c138011611001d10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 82526602 1250 82525352 82525363
    0x20304050606010f050f030c0703030b100e0108130210020c01021e030306060315100c0203070f18051b0a03140c0f0a08090c1309020a0b0c070306020d020c0d02060106080702 76
    0x2030400d401c41d00102e40d442d07204101c1305400340c0c0b0525085040000351031294a8a40c4140c0740e4400075000041e00c041091b4050041c0c00e003804003199110034120814402400d05036200b22034604000030034002074039605600014070f490a0b000f62542d41c041d0f0309080040e40d03400e0701031845800f42c445c01940e64400f0000f54540e80d498020b8001071411038940d20f043c4412a0005007411110400701c683c02241303600c8401104414644c01c0d42c0b000c02501080c0181420860640c11004807203414100502c200c2c0c2d44400d01010720203000c2c1d00020035913110008880f0070541c5085c0c1418440c4001400e0aa213640340d0016000034508440315039a035104d0034180c0c4858403900b42a8900e400b0180051070400c0d00a1501c40e80c8040007409807030220380a400015040340700200580480c60b901c50602e82036003800090140905001d42b080b07445c1c15004044107584125511004002940003d1120f80707011094060b90643d2801104a030001180c1c42c10180d1100c0c03090144000007075803480010046403002030f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 82527852 1250 82526602 82526611
    0x10e030d05040909081e030a0f02030c180a080d09050a09090b16020c0303032503090309050d0f02150c0d0819091e0b01050307090e100b0a0905090304060e040203 71
    0x241d051800b80340400b034001400c5070741402d4030080d00c144031005185900012804c581041011400d54030301c1c3c42d9881c80110342d040c01c2400b42c014810b02c108552640e030001100d2070f122008900c1c400c2c2c000c01c500059190652030300701e00d080c0d0081c2d00352954080d800401e010151042140c0501885842d8100501200d200a8001d01302a00090100302c40c1c511085803540d02d06410b10541d0700012009021038038560007070350040800c1c503400b85041c501c5003055428600c10122482c051041c0c8040d038800418940365401f0705031098948004110420508540110f052980039161b00c00d014052410b0039007a03000640482d050380204049132007000c0c40740b800701d4414002c1c206440800d5610054a800400d21507400702c800a42e2040000d668a4010324141d1032640b241d107103400250304040502d8200503240e4030ae01145810711141c0308142e040891008440201e081001401e0a02e01002410b20815031b404a8081c2d443c1000780b1030070380720100041080d140c1075207038030031820004001c0c0001c0b03120495 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 82529102 1250 82527852 82527857
    0xb03070905010e10080903120c0901091d040212010b0d062003040305070b06040f090516080307170a0e1203040602151302011103091903170a12020a02070f0303030506010e030d 77
    0x1c003452550b1700862803943c21071a407004590a22520000725904280140d41c031001034040455072040365030740001900090003004588102090080440380032400000d04028490050344a00c801044c10941c49a024204001c182100310001030401c8030042240108414000e60090729442240300c1880031a40101d41c159030b00d6103084266211a0107200d0054440e5900c41d44803900c881946000b4003920a0150180c4040c00000c04c400d00100340000c2a07a001101c0c2d03030404d10440021030f0000062072040750107883c00c7ca42c2d425000d83c040703580b042010242980325402c0802107040600000c064015940150200c40007500c0b2058000f240923400c07581440c0110f2054840c00065115465848810400b1170841c0e05140341c85002542403078210510102c48002c007030303040081c80017040c000240c00cc0d21155044c607040d000200202588a00202ca09240e90000b840704040d51081156100522000c800d80c51070503100d29008020301401d458150005204400240c40c0380b03030104502e82e4004454 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 82530352 1250 82529102 82529119
    0x130e0f010e0c0319060e0a0209100206010b0f0d0902060c03030906090a020609011803060e0c2b030f020c030d1d01090609061b120306030b1305060f0a02070c0b03070905010e 76
    0x4480400d802d42e0f103500c4c2c0c800b01501e8800010b07005001c0b428aa0240c0f40b2207901503203c0038200e050106001428018908540c031502c0108540c0030386400300c8031000d080795000e035510b144080a0300301a0004000094110a0008070b1091021010002e940940d0018080c1c03101500d0700c0305080e546801c1c080011350b0004007000103418540c0241c040a1109034500d00c02c001c1c8a58a8880c581100c0e043c41c4000709a40104070350003124076000c480d000007080282501035000a0f141c101030300b550080440141400360f0b400001c540a4020008101074100040c00c44410b100c00e00300040c44194446408031110107a01c40d41003183d0b0154000c442078521643e1000c021500d40482100d14280d900c03c080d0100f02d8682a034404a000301c0c480501c200d10b0380e140800d1462031440c1840f4040001410366001080d05203c41002400200306aa00101c0906007006540c4408044030001d2041c4035008290103000303031000030b8460941c000b9600c16015511882019641c03823005440504105900691040340c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 82531602 1250 82530352 82530361
    0x909050c041d07030501020901110106030b060904020105120408070605011202011409010318050102030708010b0f0a08220605040209060402040609091104030203070612150803030604050903130e0f010e0c03 90
    0x107940034070000701082c250400718440c1c50b10030500300a40d80c2c000b951142d4001071650b07010b580000e1640035218440d4020080d640c91610b0750405c041014140740e21803001c21000c1425a842001543c003402d02c80c682c1d5020b2428a4917101010b940055011943c1604040000031415040000c6c0d000494041e101c040c0481843e55219132158450701e441414036564101310441400310203607107030829206500050f6230741441d45001e8080f41d0160703c5211141410000301c00c03c03101480540d440d1400b18100300f900c50303d07510820305e0f10080c8006100c4d4a846403a40410920102e900164040d9000b1340341004c543d11070038140021383c0f29900500300422800c081c10003191072aa030001da100501c2554090606441e0382c0041e00342440d0350711180005d9026003d900c00541a480388407403004d00c0309101f050961a01c0c091689a00008210b54826a1f603200082c0c9228414811655031351580f00c03901c00f10310b40b203040c0004424030689540c03040c3c1c03144100204003140e9040103540514010503159086644 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 82532852 1250 82531602 82531609
    0x40e0a0b040b0d0f0201110d0305010e06040204030302150912120703110a021515040903081009090c03020d060609020a110105090106080712051f0207020f0f090c09030316030201020309070909050c 86
    0x60b484e04034100f100c40749011541d48001d00a00030742e03c0d22542c1c0840c00394034144400001210150806200300d10412007080001c1d0000742c802c144484443c03014880d5516100c41c00d040140700a44020550000a00d00c8483e50301450032a11544075a14100001ca4030455201080d0154548400250f070040700c5924031041800003255000110342c80ca030100d42075000108050721a030345000c401049421040c8400714800100344006095802c10070400d41410b0707110000511194070001c1e001e2441210721509010031034102001606100c0c50070b6503220601640244402d401c54174880c115468000403401e036460600070315080b90400c0d00100042030820325800000005520215a03610450344903c40c203d118114400d8685411080142c43e0801401031103400e012412445208805010005c1c201e82d48152030142c002c040b45141503150041c01c40402c0c9144241480b529241f8204240f50041542c150001c44c400e030466003e0782c071150303603940f80202a01d0100c00001c25039001100061482d04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 82534102 1250 82532852 82532873
    0x103200318070305030f19020a020112050601030b0a080304140402160210211a03030310060f0c06090501230108030d02070206040302040c020d020106080d050304110a0b040e0a0b040b0d 81
    0x3201075003600d403060b699039190380ca141d11007031180c42c0c0c200f0082011000c840f4440c5407540b40704040d0019144402565000800c00f00c9805d8042103055034036404500ca50b44a07910a110303400c1c0241c1003094840c2c481a129940780c020740301e06040307001c1203081d040745400c05000380d1750180d4006a00140140d01a82003121311030100301000204209820405150218011411001e524240000407140464502084a885070307600840c00307648108144050044000204800c03114240780040034809c08801c05c46003003490300e10140071981003868102c1405419030200c0551038403aa0000d410003404d45041d00b00c8842442940e4007a04184103440c040803281d0018548140b006101d0340c50300b9241d0303000504492204001c4d900507072090003034907019038091040d007001e408001300410407540f860900a280e03100042c0010001c95517901081e4085e101c0c10050303c0940b030f189203001d45454442003007134150721040340d044c5102401c04003110580e041a204246090178054507940005d0b00d036480d1902c052 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 82535352 1250 82534102 82534141
    0xe0712110a050d0221010306020405010305010b0c3c01020910030b0901060f0c0804030f0b060103020427020c0f100c03020306060412110418060b030d02030301050d1403070303020901032003 83
    0x4c100d0a04c500445c480519000e03020750320a40c80161035505005c0010211001600308a5501c2020414092681c0d000286501c110b2a08440040403000d010060786100d9030402d508507010301403c9800c580300c0419005003940c41c1081c0e500c540c0c030b181450003ca060300c041c4643c075500030701ca0740018050203200f1190b541e0000c81e50708045202c15407560354604980d015a1054904403481e46c2031004004040780529085803003440c0c150306081c2040d50001c072072000031410760130b1413040241500075079450390143d03a4001c940744199400c01c822042c0d80c0762643d80b407108807402c03680307030001c06102c0390700a20a8a00983d405800300342014100700105000740c0303000f00c1c02c1c0c0b0140c1002540c90004c0d0340342c0c000c01c00050380103404c1600c02e001601c0e020741a075039a008607600c2908216106a9050750000541c0d0441d001241c20130800d000c42e06143c0700c0b00325030b400b00c01114000060071005068064004010254003a42c2c03c20a400c1c00701f82c2d0410b0400d4a0b000c00003a080c041010072224500c1680c010140d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 82536602 1250 82535352 82535377
    0xa05090f0718180507030504150f09050706080f0708160c050313030303021b03070f080f1207020c09010905060904020f13060f0305070501140d05040c0e0712110a050d02 74
    0x60708204100b0310b80c40400c80d03000d4111200108000790010300c560190503003051a906060089041590b540000031403000e100c84c088550b070384240c01000a0302c1e0410923009800c50152040d540d04c40340028410f0108a4042003100243e0001c2511584079821191041080200c00c0e60b1400c9003403000c1b902050364840c2940c16200074800380345d1403109100f400b002188244c9006139254049030000321584403d0003014026001404a2004155041592080154040341544d9214480d420124031802108004040300141c6000c00400a400060303100c403100341124440481ea030f80c3c4c0c1c00d500c00d41d001119580c5c3c01050340070120b00103091407200504041c40042210501d0380e00440c0140458400f0b41c844d190a100c482000c01c1400300c00d001c6480a0182845c040546c401d0000f0f100b03c0c548140c1000304012507684000030240880d0b1400403014100c055000011820021350040c04050362001c100103c600d811309140d040701d10203044a01c000a541c503402c1c2410583c0304090002c4d0040100c2a21 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 82537852 1250 82536602 82536617
    0x411150403120e0f0303042106090f0f1704060c030e0121060302040c0507020303041406040b03070302070614150405040501060e0c0417030f0d09060f0509010b0f0a05090f07 76
    0x20200000380012800c41d5550304044182d820030044d40b51a9080e01d640603400402041c0300006050000660603441070b42c2c24113000c0300a10f403142c024640500301411141700c5290340410009d0912000706018082c1d1650511600301007110700c0c03544194480e0034041401d40c081c0328000f074000c2e0711340200707100305040c07489a40e07012080740c5c10b0381c06400d40d8911209030364001c14401c40c03810303100300d400f824900c0c034000342484030990200b56207108502510203d882400b82e0700b43c035690f40720700712000760131a80c100c1e80d245d0600990140203908141da0894940d41405100101240c0341c8072607910400309846580e4a01d010302007848002c1c403000e03005460710b5403189000f03d401620f40780b91300c0c02402500000b544d5546400c1510306903008500303486825070010401a440b8909010a6404070b005543e000604109581380170750003002031b41c000c903901034104400c01407103207410760000800c01c40c1941c3e00050403940c00c0802100b20303000c5c00f0b042d50000c041e4000c158079030340b82039205901401a081180c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 82539102 1250 82537852 82537859
    0x605101d18100b13050403090e04050109020a03080315030a05071403010905010504051606090b09040b01020313061d010309170a020703141c081018060e09010207140604111504 77
    0x82c103004240380803104a030707111a80002c10707003031451024102080040b010401c90400f564010001890381c4100150080300c100440c050000a50081ca00326034010700600c0342564030b01d005209504200d54a01c1504400d020039521800c0104643c0c0441c0c0d40a40035202e014206030382c0c00103000c4440410340d003565070780c0803140c0055801d1003868086c502450051900011901c90010388442c142c025504000300c44904124850b036800540d1030083c401c6401240686406004030304e1409072007201307a10308150f0980000d1154006c0301c00781642081c260f110740c07001160030041d41619281600103003000440316400b82000c42078006070561540354415907414a40c1d82c4c8072141c40550b010071022850300b1920740009420644005040317591024240015903140012a40701e5414041c4104041550b4140c404403080c401380d030200015108600d40c1540301e0800c003104034000c2d0000300c402c44103c00c03142d22628252000080e802d114541c4014003603441d00000050101d030125545242c442070200703000c0032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 82540352 1250 82539102 82539151
    0x207020429030d020a0305030711031210140904060504020307030812060306010905010b07061505060406090815191802040912031104050604031e020406030803040605101d 75
    0x807a8240030416070215403401001e640900c0a1a408814803d52119601045164001c40d090f0241a00340c02c011351207985448080e03e82015001d101c6245000000380d010082c0072100405025000020b0407088603a1150441418007040c0c001c000e9001c1042c200180002c0c0c0c05400044c1e10a00c0a01902d103015641d030b45487d09900540c90884d01c50030520100086400c0800c045801408100418496545030030380e034944a12a60710050046030300c411040c4034240c81d10204400405001e01100d98903540c0702c400600c9686507028041031401002500fa0b4864403061800f40280e00d06032003085899081c010740c030010150458140200705081c3e044802503175851042007651802a0100c442e6004209001001c6990059443c500040144410f03c62516100152402d0300e901550b2041c9441c01108941003141304418001c4d40305080c1100401000f0103000074501884c8208003d000c15100c080c000c0c1a0156140956500c10034100c1c40650440c9981110607000b6070f8031042000440042d5154 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 82541602 1250 82540352 82540361
    0x13020a080a0b16050403151d0a06110301080c0607140102070803040b0f190b1c061b030203131509060e0609100209060301030b091c09050a0512061902070204 69
    0xc44a103410100010007808041c006056004449400c5007001e041240000b820902403070201505141000b541c000401800c2d911225152841d034403074030301d101c16489036039555900342d802c04c542440c00c0841c0300c505501108203881c161490701c80a0001503220700203024941d081110103413007440c0c00d07040408190b0001c2c8001d00c3c00501600b010381d5685000d0410400a8801810000000802d0b0302044219120310601c5078614045000c0440c42545040018140078241c1c0c03000b0341c0c10400b00f0880c034100b00044d0301c908c4100c209142c1c1c034403220070080003d40483c002141e141010200300320700300c00000d0602090a10b1401060702c005094002c580b00c150480d02c8203003456003030790310440074442000710410207070303a0606107590309529000054002c240140410b200c0184003001041c00310705000c0c0140300d0414100e000806000b0fa1850a0314000c00510143c40b0745c90140e0540f503000704090515900303008c4902010740082c0900d4441802048402101122401003c1d03420f21611006035240d004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 82542852 1250 82541602 82541609
    0x20c0c040b1807180e04031e0903060506030f060108010f051003030c020103091502070303060603050603011509110403150603030f0e030a030f02031306050d0506040605130207060b0603010305061b0307090b0313020a 94
    0x100001c6c41d040c41c003e030847c0300e01c00395000c0e40000d080c4004030465001c41c5000c140d80c0e200002003402d07152000800c3c0341c0341100d1950710a40c02131200100342c4101c15807040f8042d2204a00c1840940c8a00b0a480013100d454040900040c0e0f07004035090240d40260049121075104902c0c03d44e40b8041004001c080360410030341100001c0e101e080401481394503003d500d400040840c020000209401802c1c40a0704c610701c24094091380300c080c80c05002210b02d0940d4000d6030001c00210845104800e084021702050100320003140388084211911486060126100840a0300801020409440c2500c1001e0061118002c6110801c040b601c28980751840d10010502522860344135441c00c000b03d01590f0700101100e004a1030210200100e5950060030b10000c117040500681c2ca15050402001420000d0f01c240e410000000c000800c021700010500c5c8034800c1500b680640e1001c200c0b01c1c00701e0307101c26120030000652801c1c1c00d0103d0840700000b0340e041150b18190f0f1441e40000c0d03000c00c410041b01e90 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 82544102 1250 82542852 82542869
    0x4030204050f0f01060201060810180803040f15020421050c0a1e0512070605220e040506090c0a05210a0602030601020f150c0d09020d06020c0c040b180718 68
    0xb06108a4024030404140901940e000900c402802d2002072540d44502c51020081d45e62155444841c44140789207850049402c074004a94a03d00340c1807041d2a10500b01d0304941d60200081190100783d800d2080e1010350b0501c40312071881c034a0718007070120200d80e04c40c0c0540d000c3c040c05400391002d60754640301c0c6008044118201c040d0050340b070300601180013075034000ca01134180180040c0240d030000c1a0907055500505000c2e840d040c4002660607002909640b251580540040100d07510250300491031140d0303c00c2d42110903039aa819492034460100d48003080d00944855001c0c030a03490f010400365007030307141300b8401000c070b00150528a00c0c007003140c03109450300350307000041c0420765034144040b01200b81d80d18001d140c42c02500342207618003140107104021f1000c0104400050518070b800500390140c0040844408003c9410203070004d5100c1d2500d00e0f0303a0712074211402064101800b4840c0c41c00070091042056500d00c50301c80e0980000108500100243d09811266020441342c1c028080c20011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 82545352 1250 82544102 82544131
    0x120c0c06010e06010f0c0b010b03071101051f050d0b0a021c0f020301051002070e0c0a030f0c090f091a06030c0f131a04210203120d050a15030f0b04080403020405 71
    0x500240400c1c061881c41e00400100c01c500f0400300b28400707681411110358500d201d0340cac2d41d00c46104660382080903656011a50900c410300440310300401004800c100b41146c0185103035620410003110800c401f50050080c02c0c000d00003820050154050500980518243c004002c1a0b00b812411070300c0114681214507404001400b850070a40104807070b100302030004020540c2042030340040950f0080603136840345070018070404294861b81003000b1202160200748280007180001070210b11141c0501030307d0003c10076002450700e40710302a800164401250f031000b40c140c0c1d4018000281e00080040980960402001d6502d00a140080001060718000580410304045144854201215060140220522007480302d940380c0000c04203100c1c40d450101041003018070201b800c046190551020700c035030100305080c480350740790862403240313404103020458000c1440711801400c4403130001602070f003288001c2c07400045081c1e030319a0f040740c09070600c942416900c0c0d0008055440850780b008142800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 82546602 1250 82545352 82545361
    0xc1401020d060f0b03010e0a051f06020a0b07051303030305130c08030a030b0312040501081005040e0705031903020a0201050f0f1b0d080103050606060d02070618021c030203120c0c06010e 82
    0x124040340c0081c00c0c0302c84c1c0103450765141080b203880710745020b01700c510810303a07480100b1a094000369400c0306102e44040f5034100316649020294852102040544210300ad290028581034421011203508003074000500050a0550310101d00405004000480c1904010078420104112000d520000c10f540401566203125403075005094800d038000c40381c080d40c410285641c82503040016030381620700c02c3c41c00c594160f07a0040d0941100300c0c258880c640281c602210890b85c0c0708040303000c209480041e000c588081c05000c4648808c0d940c100d6020300160401c812a1005602c6036004000c000504604141800e1218000034403d520170100484156201010105100d106110f044880045424642b61540c550f40b41c143d00d540e802090b00e03101d644e000030b5040b00346c07aa66059583e5190045810400c0307100001c04c1210040c2c03000804c8c0c0c801c03442c0443d0401d050307003210000209154540e001d50b04101f00307000700b051802c20151054005640c14011a20320100070080c0743d000304076821314000305050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 82547852 1250 82546602 82546619
    0x9110a0b040f0e10030f020103021e2a1b0a09060603020405270403140c06010306050708010b0c0d08060a0302031009020910140904020105090312072001020d0c1401020d06 75
    0x1c80d500010780c5510f01c2041014010410362500100c4c0c0d08151140e106803080c0c40102c00a00c0384145502c140d80000040f0307216000f0300b8001e0074040e05070542040000c5d20f01c8440403051918007500c001503520071082c07911010310380c84003c0340e0300401800c4030525981301e00c15034040c2d8403150003180000ba40460100118900042d2031011680c20b42860344100241001c003a04002000344043d00f40000e0151b0880c500e2070040458000700000e8081c0d46144d610f0f1320f044409450309030b03405000601c0d480004075810102608841c404600000181002a503030b5000790781d042c0c4003c0c0841d0b400f00780010000090f803424060160109441440007880b070003d40304001c4100000b0706805090394189405000300c0c044400c0b003103400369045490071800c0c1e0f1a440102ca0314800c02601503010300032007036081501f8050502400c3e48612031550b01e00070400000054490304503c5145500603801080d966a03054020f444101c01140140d2001d80501c8000c000c0c40d09a0380b20601c414034043e81d9000803c410320 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 82549102 1250 82547852 82547879
    0x70308090d0806011d0609040911030f010b0d12020a020d06020901140f1602040f140103060b030c011b0c08010e030d06050402031501050c03040906030b0712060501021009110a0b04 79
    0x81d00c41c10300031403038200900020070034001007800c03600e0306030b008101000ea075451b04180c0d01f41c00401801400f0f59181440e242d00e00b01c141d8141e050082c0301d00000e00342010f206000d2803242040150000b1001982d5031101e4102e01002da1285056000751f20140e07016881d00c541038190240214405a510704140d800141400d122074100000f495052100f0181e556a140c22560984485861090107118900000740284920480032010340d00d8041c0e080840c00d2108200390480303019000401c26000e0103418151100841d46c041800501400c0368000b1045480f501c1910040c02401041195501d441106003110654004c04a60383d00108107940000f90901819014003c191810f500f503042000603240c000340c9544102d03043c0840410841e005403403c00a88004281c00c80092040d2540c0703090854135482c0c1500c10b0b8000070074402071171006c0d0405003e40e008031001030740284009007817005010b006100c1d16504480c4443c1c0307611400000d03074a4044080140040c21080d59640e03280580c00e10601 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 82550352 1250 82549102 82549123
    0x705090d030914030c030607030c050c0d08040b0c090a050607050307021e0f0a1a0a05070b01030f030e060310051c0b04150c021f021e0a0305160e060304060216020607030809 76
    0x941c040880782c1c5e240d0301d01086854202185041c08a42c00400762010b8a6030301500620150510400e125104041da21191160080d40241c10000c1d841c2c070340c0001c20130940300748035071030b42c10601440c0d00f00b1050510400070200503004405072401c102a80e400145000c5020032150705640c12040381c01403610301200c44c9490080300701c079504c3d880d5141074656070803840745c98814446858080b4107941030a00800840799030a5001c041d580181d0317142e19040542e031070701c96000d40004681c4007920f201350501a0882c1d014074190844c83c5151031502041045003420111040303030300c212940c5242d00089840c108640214402c140b81c0c5582e0f03203500120000c40d4030102d800740440d4460407071141021204242103810300401c040169030340e0319581c101054003445140c03c41803040300090350070031150305501c0140210f4029114110f41c0300d480400700c0300004680342d100d600c04020008180014041d50041812665503420015201c485400180c20703504200700540c003040d1070008101840000f0310131004030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 82551602 1250 82550352 82550359
    0x7030b06010c02010207030f0c0302030706030203010801050703060b12060f03010e010f0b0a0e0f090a0c080c100201060605120603010e0d110705090708070302210a0c0306080304030f0b0705090d030914 88
    0x8820b80390300000c3d503a000e1480040c0103448603440600c148110001c2800246d80c0190031112015a079080040080d40244034440c281d51a01e408902694405d016180444003407203e051308041800074021011000a0505548810300c00c4580d0040d0700c0070701800d2102c00300c2c2c0d0000074040741003074400002d40303511444061003000780300b0003031000105118400c0d402020084ca902c4560380c50565092402408503809000c08400c0310000551341e81c000752031407450ba4262032541050740406026401d99100340925008070710103200c0b424031445915500c0340d001200034008504003601581183c10070400d0310300ca200041102040b202244400c00c0102c0c010b10060f1140c15162074074002c003c0c004140941060105a0000b81811403525851405142d12032104840c1000c0c0c00c000c0c0940c8018043c0c1d2801001087c01d01c05c0005500d24084180c80c2141d800603165210090150b03294420030b90014050320620000380003001031a2144003d6070151882078a644107103606020704803800ea021554083d10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 82552852 1250 82551602 82551617
    0x9020c07090e03040e0a38180112020a0b07081b060403020307020f01120c0e01110303090604080a12021204060f020a021e0a2910140f0f1207030b0601 66
    0x2014030000120340869a24400811141e11415480406000680c04a0100204501c039549910400302c1d0161f80d04054000900c010001d00c200780414205900c00b5066054082c10040084041c1d45c001c004455200078141101103844e50480d9020313811562003030301c1058001c40d104140080c0605024000740c1c050300200040c0c90135540095491068a00080c064664607010b1065031b4007810302c90500048490062110388180315000f0290202140c0702800690b01841c02c042d005d502004481c00b800100700070380b4483c2c0c2c3d56119031445a0003051100100b102c0240c000c0a03d100b03520144c01013400d071101900c2c40703042ca0300780300342030b1064030754410355107881040078180d00d03034002a221034104910514041c40002c0300c10414108454010040c00c2c00b03020312040903800c4460143c840304080c0501240006489070000700c8002c40090264000c40c1e4042440c40e9643e140031181840d080c079008021586000020300851921510040480c003158403090081c401c01c181d00c4401940301c81d082c0303011a03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 82553958 1106 82552852 82552871
    0x50d02030f040308060d05060c071a010602030c0115060806240c0f0601080109030c0b0903040f061205060102030307050702040b032503050606031504060203130c09020c0709 76
    0xe00250001002840030300d0f003090200d201542000091440b561182c03880c89c01a4043c00003584c0019076040c800140040540b807807400380c0190f5001c2c540312102200c0260a480207076030b1516000301071032001d01c595580041c0082d4054000c0706c0c91707070510b400f18152035a03000d01c40c50740840b40f00b00002c11039080100043c06001d51200c0703c04552480e80c1e101c051600f00d40d103020b001400100190000c4010810f01038800d034006030314078140d914041d9035075408016408550300900c04240c080f4100328504810348a599440740b0280055880d5280c041c000401500c60390794002d104540d5040200820f4400b0400030602104000101c0d00198400031038100044040c8000c459a00c501c00001d0014100494070800c440400c00301903030a0b44a50b591840690070081c54103941c030f040114150080b400c2485001e00501e0302c160016521007001850a04060403904840ca0545c208980d0a = true := by decide +kernel

theorem cover : BRFrame.Cov 82374102 82553958 := by
  have h0 := BRFrame.cov_init 82374102
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82374102 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 82374102 ≤ n) (h2 : n < 82553958) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
