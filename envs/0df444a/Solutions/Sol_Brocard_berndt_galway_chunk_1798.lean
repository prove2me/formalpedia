-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1798
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:43:01.530064+00:00
-- url     : https://prove2.me/submissions/680c5668-d385-41b2-9cc5-c06b1dd86d36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 323201438 ≤ n < 323381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 323202688 1250 323201438 323201449
    0x715032c010612050c1903030f0e0a1205060a180218070509060a0e0f0a06120e0a0605100906050f130906090506100623030402120109060f051504050402031b 69
    0x140e01c252a440f09560f5220244200400c0185080c1c0c011681078540b03014020503910420183d102c0500850306c000d00c0c40070302500880d02c0d0181d5450007412032420302e45072036a00001c0910300c1e1303043d125548110100880e18203244038071101000c614140c1c07440380d0030b19400144003007a5074044885080f01c1d20042040d550140060302c0b01d03510020b01d843d8681c01800001007419004045092007010b099400f11000d04001c0000815a05a03980d0b00840f0921506510060240301107000410701c074103225200030030800d01c5210300915500c51282120b40c542410f80c415078201d900031034460202050801c4880e03403070b1032400038032003104000451803d0a50803c20000d1086643c003038190f0081e01c00f0014050081803010f4196942a10341510401002003902e65420702030740040d1340d07040708201140140c504001011005150f080c0007080b04409030340c03584241d94081c8800484a85c43c3c00c01c0c4600d10205200c01155600706507001c1003540380c80d40001c0e9484a00d4075080c0815613200969402c03c3d00c0f00b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 323203938 1250 323202688 323202701
    0x512071a01090f0f050403050a0e0a03060905010e120408060f041e05010209030f0307051915020a020307021201020a0804020103230f06010e090112032d020715032c01 73
    0x5105040c80c6541c2d58121000142018091a012503440d2104801d5065101e100f00c3d402190141d48950401003400d10a40b02441420406640100c0544001001441d0340c040e40e2450b900c41c1c03002080c1e84841130482880c0083d40346a10703015010603c02030117018400290283d00480040003000d0548890408008003030049c070380d4820503401c0d100584c0c14448150010880c484099003185e03000ca401c610116247d01039490020843c0d040807110904a00d07209091041d5140a468038a4140d01000b92000407a8404903e41c40542c1001c28840258903000c3c0b06240415241c000035442c0c03800107000180745400040000341070540c1c4066851042c580500700300d04071117020030810564108698101900402240c030342d40041c0074a51910b81c0c40c1043c40d54241203c4000604909940c050390381030f03982e00c0c4a0a0b00201140700b01044040131078050072a030000c9684c0d50044c188107800c08444860b0280c186c0803410906051021510301141c43c0c050b01c62500203600c221011b007601440855016180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 323205188 1250 323203938 323203973
    0xa080f19030c0216050a0302130e0a03030e0706050f0a2f0a061109130207060212011205010e030a0207032004020301061707030c0e0906010e0306010914090a051207 72
    0x880c0c98100c03000c20340540c40000314002540849003451120f13901c501250f0840e0180c240c00c082c00c0c2c1c000f0030041c1810140780035240c800c02404030f012002e55000318686003003e60b0a81c000b07034a130203240034001e1080c000b007000742c069403900d1741c580f1a800205c1c1900c2d1003141684810040850108100009094002d10090025503451844880c0d545920382e52040e2612040e90300c1d0345410041c3c3c0b4494560411071301600300280003d82122510189100250130000c0305031503180e02004034080200c13603103100d540600420264442500a50b080c4107007100c0d02c00305c4000d01c550003008425915500004d942048950265058550111034000000c01c8a41d200055410034004070000c502c0c1c80d0840c012240340c01c14004480b00035503410b1011010b50b9a03240c1c2c0c1d80e0224003800c075108102e09000429a42c051010304001090480c0180428a080400d83c000c4552950761491404007403201d9610a4224035000e006050108554550179150002040762404c6440c000070418100807581d05a004000c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 323206438 1250 323205188 323205217
    0x30b040212121315020a0830011d010608011809050d02010c14180411070b010303050c010c1d0103090c0801091101140711040209010201090b270703050a080f 69
    0x1080e4152181035800c0fa54180c6000c9400780c20208013014440c3c40c2d0f0305503c409034000c10344850503440d100f20688c400e103154040000050008000c0c440c20000345a0b101d6003010007039a01358505400340e00c54050f4007914101000000300100016640612030605441d982c49442c03a402e00c401381d13600010000c1d414018514001c840203020b20580650101c580003405440307100c29092440940e0b0034078400d90f45070030052003694501c3c54040c00c0c1540030b610814052140285880c6094403030b488080c509a20440020b0f0b00003c1c201f2a082c028080d420441d040c60034044d0843c0983d2018240080d580c6190504055890003407105000c00f4006d150028072424000b00000b003003509202190185101c110b60201d40d401d0000500d413803049040300c002d04e8010640202d1786203442d04000c048c3d03000200150442d9282c40742d040201c0c8501004502a155003a90449000c4078010030910f0400c141070610141d0300103402c108003045011502e08420f60b400203445999001c40300d5990102d02a000b08000d260 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 323207688 1250 323206438 323206453
    0x118060603050c01110d050f0702130c030f110315030c0a0311040c080f181609090209090307150e070f0612050105030c01050d020c070b070506070e0316030b040212 72
    0x1110035400030050324012000e0750142030302c1c54019900b0100b44049103605500c0465a0791450740300700041c0002c04001020b080c64200c083d00007588260700214000700035503031050791500c096014400d0010300c0b034041c6000d00040c00040200034050100400c0000c58070400d01a4200941c0c0601190078898401400d40d080b2a07100e08121500000b00c103103c0d0301441c45d02d05182d1950703005143c003512030015440074a446940d0b80104d40040501010380304030fa4450001180410b08004142d003020385826000002d1180d030741d004001840e003015050000035001000074001143d4079203140c1d1901e000185005c10100d60798010180380c8a070302ea004041c220b4074071001003000c0d41d202d130000800c110030003000c4c40703182d072100b04040e15520191025404036104000700e4240000702e801030300320ba01000058506080c0e840040c110705501840040340c0c0d640184003004505904070312501c0d000b44007500103211440f821202184100b40c0c40c0070140070760716841c00150456840e040000c80010110068039800b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 323208938 1250 323207688 323207693
    0xa030c0204090c0e070305100f1509080102040810150602030301170f0a0f03020d021b190503240a050105090a020702030f0a0b0615070b0a0507051905070c06031a10020118 75
    0x2070005c0c1c1d0752070006400d1101084590790022103d01c280c92151a0b1000d0b850b02d082d0304030010700d52401c00707a07041c0716000200181080080c0f001d0b000502c140c1000c1d084100c0003209403011915201b903116801e0400d06024030206a001081d01c3c1500c6038071895020040210b00b04516250782064a06400d105031b2008004016100404020712440380c0c00300c4545040207a026611a8031100703001e03030a06003110035080c051130300429415000d64502d41100075192a400400c0c1841580c19900040f07518000c64030070110803071301c0410350007c4105020810783d414440040c0701c050014012101c1540c002c00c096080d9035040c0811108941814103c07034100103d445d00c1101d081007168a40c0c4114a2110036440442142e13040b01d45c48c9500503412801543d4010a0500078240541800f041000610504d080c03c048011b20140007201610390035201c421340d00c1c01214a03100384c0c12038001c050400c03561007004448407040c00480e500440d007034503880204d07200c224010681c443c5040d00c400d1078440e04c0c0c1d06 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 323210188 1250 323208938 323208959
    0x10200301080a111807030c0903060905061f1406090a09020a0918181e0f030512181009060f090b060411071a04031206140f03010c020a030c0204090c 65
    0x840a103c0d80101a10928440401c00c1d002c9410104035040640e6900081324540300e5071049240b54054109490030584036100c80f42190b444900c01c82d81c55000130305000041004401200c040540c62240d20001030411559007403807070300c0c40c402500400011400700070030f0303031045907200c0034010141c821519942c85000c020403007003945c41402d03800500c040000700210b900d80103444800245025400706041c60743d0b528076074400c124408107048142510910005280c0c02044d01100d400780d640c05890b608481081c00b8641e030054051400c001120580c18650301c030214003101c814190600004800e2580d06000015020002c0642c0307440c1c0c07900102c5130810111411480c0541c500b902c040140015145a00c8114421488040c02c004120a00000742d019400940750b4003600c80c0c44e0819428a1402c281000d8580d990001251a00e0a000800107400c14070044102d5200072002481003c186440183d2911980403024040000d00c0036400c05641b00c5800c00740b6039650000007003551680c0c4003408603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 323211438 1250 323210188 323210203
    0xc1802070204060602030a021e030d1e06060206040f03120e030408030d0b0307050a0e0702100c1115010b0a030b011b0305090310050c0901120b1008150d051020030108 73
    0xb440307507240000210b001803002003a40c00d80000e0390014200c00c0206924800341c00394a9160b01114030003042201001c10150007920701000c00001c00c2d07540001209100419150b5582040e821503000700108170105070032507009003181d034050502004c50700c480220840038100101c424417103840001741c00180320344008010541c40f4407454003001220080f60030151030b02098800c55078490103401080c4880288903e40c1500003d4a004441e60b030040d1004101c1520346600118000ca6040d60404031383c0e007000e00410075400c92030740d0200701c1c4d90b062081070b0500740195031000c1e0030569a141c848565900403e52880c116602115170001d066152800801903031205410724020b01a050070721103c0350503409058058007079814020304000c031510044a0b08030b03440c00104140c0fa1214046d105039212804d551381d1000c41d036620382c80703a8a402d40302c045032610426420f0780a8115400c01e03d010074001b041c403141101000d2008100110601048226490f820070307280002c1100000018038100000f8501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 323212688 1250 323211438 323211443
    0xa0509031b01020114150105090303130308070c05040216081806030c0304030f050403030903020f01090e040b0601020f0a051b061308100b01030b060703080703020f0d23130803040c180207 82
    0x1e1150703180e0745c01c10f80c9002c58203840104946a032001d40728804e41c0200e010340650a00075085a0418020752030f141d003016401d038002da9105000192520500c0840c041007401741100742c40644c60300c40300808035080782d805040041d020310780120b60310130980a40f42000f000c044000b40795580741e01f05041e00303a88030340c0140d4044000c03a54000b046810540504261070840f5015210340c0700b46881e640034014110030030200d803810040300c1c40c40440c0222080f18401e0250b4000d40c050390103881c040c0b0019240401c2500703400c0b400d51040c2c4184d400240006500d080401040d144120b40500034004101a40144a04114400c040460100759071100042d0982c0c00b074000b0b0010701942c206038005404880f00b0804003078000034200842c10109010f00c0200b5001001494018900321100d203c1e4400d0b5042002d1600c407554447c20b10451400c2a0000b031040c0303005000c8100060b080c00c2409034400c4020396070080000c84080300080500960b8402c0000400c882c141d0119a440000c01c0381009600c40c5604 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 323213938 1250 323212688 323212691
    0x18060619021c020f0a150212010902091201060f0b07020a0e040f0605010f030206121b0a181a030f090c0409060c020613170f1c06061b170a0509031b010201 68
    0x2c0c0740c07030315200240b20b40c06401d004010340f41144250710b4414564a05c440c8900c1038036000c0107014000c220302e201d4103000384541034005881d4045802040301042c5108001c0d80c4580c100070040c0400880300001e80111044502860307515002ca03c0842c2c1e842c50254017074510041c002040005021100c40d440030782e688034440410460fa240c52180c0d4900000380806504010140f000900c203464503007890780c0040e0203004050000201d5002c040e00d55011b6000c1500181070b0358103951801042c40d482e44054424031101c0030385a640120044110b00000f070801e0402170440700072800c44103050200d040c3e00c0764041c209020700e91071803c00034040c2161000000061007500000360187c0d40d0080f60400d410391086020320401003074a0041010741110315903c1d5840010000e07020612030310b01645000f090921000f143c50351400001910000e44062403001c00100c400380704c00001c81d4001131540e40f00c41c00001036207030510244100c07068090710b0382c42c1d03070944a40101210b20000580250000d11802da00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 323215188 1250 323213938 323213983
    0xb07080f01060314160c0b1801110702360a0605010905030c10030b060f0711151303030c03030f02071505100305151312090503010b06091806061902 65
    0x103046044810b80721444c0b60b0b8014031000715080d10f603042c1249401500d645064040130b582521344d040c0e2040107403941c01240c60200c4240111840c00e008265159061603115070602e10945c02140d40c000c0300c00220b529211324041c80f070ba00341c41d0201c820110065400168212460944480001001c4a008150220340e88030340026452400044007030300c07090060030208811900180660203000b001c400c0c103500100902030041e1510382d010141c04194000c0b0402204007c815043c803041c200075085a942d618000c108070182201c161040c201102d171f0614105050f1081c50604038001d0070b550300242c050302e00010711501400500c40c4044040d60040c0020006c944800c035a584400c00c00b4800142540c11805031254220b0702c1c00c0100303501c41ca02c2c65410036070480380e40e11200e070022860070450100d4465034040c841c81c00c09100e03090300442c064900c60300e068070884c0004c0c0d0344040b00a039500703065120320004400b0707183c54054030308006038114403220001e41c0b960007075204c3e010074481902e010351824 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 323216438 1250 323215188 323215199
    0x203042d060c0501111810030b0d0c0512060c1801030f060e15041e18121107090507081503010b090703020915040b03040201050c0708120d0c0927090b07080f01 70
    0x1001c6400340f80c000c0c40003040c1c001507001032003a5074003001200010300d40d407404440f27083d49030010b1003c1c003940700b29040c04904d030030700c000c1084c1846122400030807036125004000c0e82080c0310040f5603c0804a102c0c890143c03807100d00407805042201035504206090000c00201e000070003100c10300490b07400040321a4a90700b04140300446841c0c4c0a8400c000c42003081c05204040b0503032244942d00c2e800742d003192555440d0384400e640d0074410050030001894954001d000304900780500c101405594000344250704007070400505e030903c080e068400d514400030540381599800d61040c044a04060300f1b51800346440300300030b402504151025400381d9001040c40c03007981d01300d90031101135628001c01300b411074849400444894119007081403c62080500200d003450040244140350f40346a44055550340c00d046681e025201c0c0030303000c87c0030700144080501203140c50007010100f100141001250484100d0f58107400303002020400b401c0c3c0d15860007031000195001d8410751249a180c0b0500701d20380d03600e9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 323217688 1250 323216438 323216471
    0x317093901210f06030803090304060801060302120403080601050d090b060109120f06050c0f040308090f0103050402030706050306030703082a06070f180e0702010506030606100203042d060c0501 85
    0x28484080b2070b201c80c944480035045a404070307030100c4180d08000340003034490303881c000b440d8415164040300d40e0012608120880e4049051401351550f0f2a0541c1405025000742350400c20140000b004d000b03800d8001041c076441202a20a104410702c2d040c400c1d4129800c000e9680d83c0709592160000382d1840c404140104c50b07001c1d4842c900c0e0320120100d66580d1a072142170092601425070010381c03004100b0b4a0408010f0005000614058080655500b40143c100f1100e050000000c42c1891705240400003d07a07004125001124103e040070fa07602d5039084000390806615410003090140042000200410a062140707002180d103003417002c1d4285426500c0356141402c50340b0a000642e480719198039a40705040c2c0c154201840d0705005400741d21030a40580842c400c540150050390340d9005c1080f541341c20050741d40c00c2801951182004014410300070340b02d2195018104401c600c0001c40f619032280000f100d541c054090441100c140e4480720000c090400010b001e803450b60802100b403045080304d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 323218938 1250 323217688 323217707
    0x5010207060513090f0912032903100905030d0606081e0108070b090a0e040b0a150f05090c090315010305060912070210022104030c0e040317093901 65
    0x11802c070800a02d0204000007500101140145042e25540701d46c0c00246080291241d005890300e0101b8510045441416000c40e000e0345002d0190110030010312544004c40c1194445c6921107001c15401110b044c407a00e54170580c02c01019140ca0044002513081d40000300c1401520300310030031505034114a0300444120000c3c01006440c0e00720310800c2101520a100604940348060800c5c1c80d03d0743e8600c1ba000c030b072010464060360070b14102c8040082030003a62003454105840da111040301c00d802c0c801c112000007428003e1302c1c022410880403e12055016060301c515100040448081142100c80f0240381c4100381b004071802e10801d004182840c001080102c00c2c02984601c00c2d00f001013603002c001e40011051f40c044c0c01c2d1300404101584603042c41e14031403010100d00c5200c079591882c61903c181424200e038844503820140340306000001e50701c03004000091040011008540c0c84150f0f806085c010000042451044042c5c4d001c00300542070320612503450f04001c889100101c6090055841600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 323220188 1250 323218938 323218957
    0xa02072f150702122b090806010906090b01021506130f09032a020f01050f07060e0102190e030303010b090303040b03070210051312031a0306040c05040b0612060d0812040309050102070605 82
    0x100384030035603020081040ca02071066602d844106151f80308546414220b0030303000062100c1d254041030000c0300c2140a0221400300030310003400b901e0a80c2c1881408120064140e0703218004032008000001400c0d008055010b50710381d0100502a01840c01400c20303a000c451304041241c05204a5111010902042d003202d034015200740c01c000c051f1801110150311010103c08811010310901010843d184100c540800c5240e00050f500c078843c20400b0131600030a000e140c200320a042c3d020b90181c5000c01580d0454400155441d22404c1e00300010b41075001e01c0d00028250072000c020041c145a0015200107105503030f44080040c0d40712255400132180e80c90401a10503049510b42180c001e02c01d80c414070501045104100c1c1403004880040e00382102643c05981904040c0024082841d0034412000c010400310303025490621094001092100c004105500c281c9030804140c00f48841d48003180c0301121481c5c005c00c4107190a10b406840100240070705130040c42894404540b43d170040044541191 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 323221438 1250 323220188 323220223
    0x1513050d0507090915090b06090604060803040b250803060f0d3201090f020a06030b011d06040312080906060f0d06020714120c060a02072f15070212 65
    0x50508005a0144c41e000c001101c6034840607803001d19031045481443c0500f842440d030007095080070380800614440c00b602461060303241071b00400103801c0c00000c550480e14000f0301291240740703450354000d4405444c1c501c0301c07181c3d002c9c8224400300041400190304c24002100c01c001c8410018080c01000c01c402c5100405039005040d40320380b00110016009100301709060300002806824a016083d0343d005003003103501580d90b00e8070008501c0e004152502414440ca4104180100000003c00c010380b250184820304000240280311030301c45200b120041c60f04407a18010380b400c0c44a0003802d9510450b20701c201c07400784001059052070903007642d0b00340700340040210f0700f24080f43d15010005d41c40240102c40140c64098100d0b0004010302a2442030f541c0e0030411782d00c600c110040c45007446c00041a43d51118030400c4190001419406003044600300540000803401e00116a2161940e4240c042644640c02c100340d0200c0002c100700410000380300b07840141a007181600c40383d542e840070100c6442c065 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 323222688 1250 323221438 323221453
    0x1081908090409020d020402040b040503010f05090d0507030c051603140c01051c02040504060603090b07020a0f03121d070609050612040f0807060207030f0e0306070807031a1513050d05 81
    0x180b4142d0018030741c0c035000a010250340019075000400700d0f4050340c8501200d21012604000130315080c0305071002165201c0c41031055203000950b464503225411a04000d101c00450311406051246005107181540142120402244e1035602030400b1210f1004a81000b49001604031a10b40441d81c2071003950103071980c500349070221007280e4540030443c01030107d1950a10000440c1d985501500004101589000901d0503041c207000c4007070b000050040c0d082d54020703045030700000d02c0d402c0b82407001d5801d4508822402c442000e01b1740541440000d0340300d40c004030030305c0c9010700b40003103202c004442c200e40f05c40101666542c2400b015005088a01c0d2030b1038060000600850784820ba03076090f051207013000702d1529000d5603411040380c00120b010f400140102e1502041c01e0341102c3c0010480204600503e00c0740340049005000d01c0c2c00400e0700c402c258032600090341880060454012520b40205032084090407507044007029000f00d01c040b80b00e00c1070520f001446080c0110208540381d009800307010340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 323223938 1250 323222688 323222707
    0x40c0c06022b090b160c0b0a090c1d061e03010e060105010f020d02070b220f03020301150b09010e041112190e07060f140309030a11120406080907030204050f01081908 73
    0x44150008074050113034000383c0500280b88031002501c030b0f400d100070005035580e0381e02b008142e0f459a9000f25100f0750000b0144013010f0407a44000342c1c08801117480f09403e00034039442c001c1c00e03840e801c1e10640560030700c3c000711078034200804c01d075041c0c0701d00780da8200302d401d00c00d04100e0340e82d01075848c10340150f003000c0000c0c0f0074010004e0080009580c1c0302030ba10000c1c1d05a0928052003149a805080b6080c1001c10520031481e003030203411541413441d24000c1100f820101c0c0c50b1220710840903040e05210074402070b240e5a45598020045040d41859055140e840546161030201c0d07089940107175825842140d010010b000d44280180b01513188000d01556040c5102503501007410b96007141800710841c1181000c90600004512078021500a542c494410281c00b0b004c0601003031198079540c0000c40001d44c1c2e0003804042e00c0840e0a10b2400030200d481e0402140d003852060b03000a501b0905100411400e4030012480718101e4016008454a07000603448030301402e100c00600628840781000034103c07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 323225188 1250 323223938 323223961
    0x240a020c1e06031b0c03031b030f07051804061203030e060108190c09020a0e032a150408060a0603030801170607120b030a0b100b03010e06040c0c06022b090b 69
    0xc0c800c504c4400390440ea82c5807580520150010740d11420a5440001004020124043d089600c40000e00d016800d500b402d0b8043c082030320b001401c030001c105000c181031507090041c18100ca410720f00074104105072510790b9501c52000d4483c042c03d41c0464101180441c8030355000985034100c940c0080a04100c07413002c00c6400d1042c00c40b12041e00c00705003032900490b80c144548024150901180c2707422000320804014141071584040100e60182c01030350b038800760901d40c4001d207580306508035410103845908404824090055802c01e603414032980d003c04c13225196582c040821341b0700a40380e00746c050f80e9900385216820038040d000c508540020700801e04880c0918800420245001400714591081c00003192074201404801c0d100701e0101814000303070708507050801c0701400b50329503d68503640c10621201550722001e0310541c000c40d600e400e04103005105101c0c080820303502c00404c0d56140303034074184421021004075203802e00400901282c01001d1091249038441940000d11148d03076900c006140c1c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 323226438 1250 323225188 323225191
    0x6092013060e06190c1208060a030224040f0302120d3e010522210311040b0405030706030e0c0909070506070b150a05130b240a020c1e0603 61
    0x107802560500c03013016035004240307040d8082015a0f40b2414a0442810610080301d020316010041c0900c0e90203010303154640c03410f12015242c066844100b400c0303c2c00c81c04110152100034000d0344030400300700800d41490482410080341d00842d2041401d04101d1500f0391036142900d504800310741e4891959004030b4010f46d031303070800207040c3c1d04181c1e401c12000c50301c1150300701c0403004c45d1060b5558000c00c01c1010310401002c1c00094048005070005450743c0d5406420500d495460b4441d05001000e211396500c04e400c03624245d48030103402500d0f00e0341c6451083c0250081d0084c1382c40f81c0602600492254440d108403840540d016006040ca84201418801c0405011307100c4131840c002c101000c110394881d00b0040c01003521421100b56186000c000400f000000a4800b62103101b500c1c60800031540c1c0d61900aa01c49220000081c03500900c5001030310218a13109800315001013940b1210441c0c01704000741801c609c0c1a02520701009030350b0204041d08541009842ca03c00d0700d40078a54040c1085406103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 323227688 1250 323226438 323226467
    0x3080c0412111014121f03140c01080c090f13020a020c1c0221010e0a151505090711010915051009110d09050309040609201306 56
    0x186401d0710354407003040d070046040702500d091981a51900440c10840441121800310346800e81e41074485050340d80e41c1d1301c50110034104110b071503000726001d202d01684840411542d1500a0310321076403480d1004034855003156000c61401213405011141d402500b8036441407250300c00d034901e050019820807080f06c407140c203803603007003c4c0d01001c1001d0199130740b00611508081c0c0c1c0040c0600c0301d0b454201b14118480c1d6203003044c588051446000107031140d035031102c2d1450006401d91050469050300500422a010070301c1c210748251010841844070b1010f034250400f000c05024015031314031b91041006450f040c41010307080384940340040c0016103c0d8004010b0700b0303100c40010a10000030786070752443c003540007110b40c0ca0966034018403038a45000d1035040c000b00b00c2c084c003e0051f601003034460019800f80d03040301280c898650046108011703050044945c00c54000704104800d90b12224030724005c061021341043c85111450141410b003941a0aa80600c003007440c64030282810a0b030101c4070b602900905 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 323228938 1250 323227688 323227711
    0x4020a0309050d03020405030c0a0b12041b0902030703050105030604050a08092202040503010506090405060103030e0a1509050a060512061c050f0c01122901050c1516030203010605070308 82
    0x241d0000350240094070f143d6040343e40161300d483c00d000c101030501d042003540b14410344112604120103850001503840882054002c1043e0381d40740d00707281a0900004502e00074030032201d103012500c0e55041d07014500401155808102aa88880030705a035180c050b10003418507803000e0410000112080c3c01450100c9014009401400010221060a006231251542d035146c010400744000e003800d00c1080c0e0700007400c0718080c006081507150241c40340b01c1804013030200704901d1111486510b503501c281e0000c2001c903051045a008109005008a0300e40c0602c9100359005100000c000e4414800d8500d9502c0c1800c600086071903000070802d544004480200740700c2901c3c001c4101249040c0301000c19000c3d1400940301c54210315000428488500c3d1402c035201d80742440c00e1f00c07210540d540c08440e5000c80004e038554003480034010384486c0240c10313090184c2e115107650900d1341c001c4c005495006036411115a0404d4030f20f6042541039020034040d82000170b0303052095501180c403078080e1981020140d4032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 323230188 1250 323228938 323228951
    0x51014070e1f1e120b04060302090112020109150201051501050415031a0a080d0f14040303082e06020c0907020303070f030f06270c050f07061b0e03060f100504020a03 73
    0x800783c4440662102c2d00c002c1030800c408a084540385004005485000300c40405c00d10303080d903001407020003040c041c003822460725285240469000c0c0030058041c12807a4000082d545807941c009001c3c000484a03000540c10f1000c1c100c8555029000781c0d0140c0d455806c0100401c880e21900324000c080100162840d800f80d401345001d192074803c11a00900490400707803005041c0c000001c2c0014002d45500e10802003146101984a000d800a440941b035041ca410701403921036002e08120302600d46642e8262445405071002c5600700c80e44003100703c1d4101e4003914981144c24040080082d004c40300d090250700100002a09144a224038403c146820705000450700d001c024090229003031034104114034614a001c250035164206202d080b0180400401e1128400e0240024080d0040b4001c40040c1e01000c51090100819600309804404107583c15121402c02090001c0c2031b040d0001c44180240544c001280d8004038120a50381301c0c6041001c480101890070051100a5004882c144201550f840 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 323231438 1250 323230188 323230217
    0x28030206030709031a0402131a040516030606050c0a0219030b09010f1a030a110a09020f030402181b0f0d0203070207080c0a1a0c0a051014070e1f 64
    0x41c5000c0c220340d83d03c000e840f80c29440d00c200d6203072400c005070160202a000f04401a0340d81c000c0038042140480000c07031056842e40104000000c00420319074410300f400d081016200700a50704003500080390b9010f12801d17540e0b0209403194800e03c2d400c4400368200180a1002d810304046034900c60b1941c58181e800c1950341d8030b07100d2400b00c09a405141c16511458900171240740e40c0144005030414810b0035115004020000c2d60300c01d00c04800400342ca14104108100395240180b050050900c000299511001203009000603030084404911030501c6068201c4840c05c0d00d90316034400c643d02400c080e100e04000101c0b0403640c02c81424003c0b208001c000100e37080b507480c00558000ca130103800600c241030800440e070b400d0a104400d201d000d66880039040294040703070f200609aa0a00c030313003217680d1004004030281c01c0c101c200401030110300c18a50540500403465000c032050070b041307007401001600caa182c211a0040d13201001c031b40c0541d0100f440720303648a61003c8619480382505120703100520a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 323232688 1250 323231438 323231449
    0x2030709051201020d051e0a0c050903160918020603010e04320708010c02030909130203070f1703180103020306030a1202030a1107060c03050d06080709020315040506280302 76
    0x182d0a00c0503e94011404481800040c0103032904100c6076191012010002101001107440c010312060049441c3e00c4108080c901480c12203032220350250554103004d41c0460110100d02152007480e0210b481e1005080c1c0c5a40c3c070003c0459000c1e4010002031850b440c2c1a21024441d10290080e580c1e5000c2c8d0380700166448601c002c224081d0122212040e00c5030481d0101810315526500c10942641084058500290301008560240b4400c5900c07042c10303114005090740e0800c200600039018030500d240420f52620750144402203418072100c040c0b0002010794401d03142d014508850304900903000756102e0a60282d0051940040c028045595102445c3c4880c402505a0b210740301c05600001165154030b40c0c4520004101790445004044071480d1071001000300c8c19101300039040000c003284403040c076005600000000e1000311308a5407059100c1c081c89009600c181c448910041401d4211407003400c281c0a054840e2900406203104104040c0502e2680c0c00d08000030414a0381a60001c170045c1d0f40e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 323233938 1250 323232688 323232709
    0x3020f04030b2a030a150306111e090d030e010e03011508011404050706050c0304090c020715021f020c070302061215012a03111b03060601050a0507060203070905 71
    0x24540044075003880b441140040e0381d0111040c810041200d075040c0e1410f5180c085a07004078001c1800601265500e40003440781c1c0346500020090303030400c80705880c500d0040c3d0190911501d80d0200528074444071000880700d11074595401d4122444c07100100110b409044004003090b8103061017540e805010700028215a41c407074080050042c102c00600183c802413144008001944003c0d003a1810300303403203855846c02c0318459102081000101c0303800614040c01076078001d003841ea00500c4601480300019460320350311700464081c200c00d069100d22642c4001100c0c4a00c680d1188400d8411000030f82240280d4028010a5218825644000300603280d520003080140782031442da61071801e00e0800910040a02c0d002c0303504000c5c14941100c5002c60460403c200011200501104143d042c03806558416110f42c000c000760250003c0b8682c00141e140440c842030b68100e040d110035544060041d038240c091003a1210000d80705125413030000d20f90342d004580040580c10014502c45e500c1c00064004980d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 323235188 1250 323233938 323233943
    0x6080114120a06060f050d0f0f05030f0c06090c01031a190503030c0303011e1505072d0b090115140a0509040311010e06190c09080d0c0510050106050708070303020f0403 74
    0x5031010100b117000941c59064001d008211040542c0003e00c0d01c07072850b100c000748000b5040f11440080ea204104040007122025800252416142c44542c00026180c0204644650040c0038950229050358401d00c070780c070f41d0840512840c030a42042d0406010403154240344a1010b82c0c144000172510b40e9041019140e008031070b030015a501d604000a1802c05840d510102400503400301d000d112070688000040003054007442c101340c075040582000c1c400220045100c241059076813089903070915601b007006c5022801603502000030f40740e50300c0ba1401c0f10342c0c800f003c000b60300c0c961100307010070310100981e200111001094151107988134000940c01ca1003d441c2240407503003040614080303081c00c1c0555074298013924040c040504d004440c1445054040f03280014550f03a0f0940c10760300301d0103640c0e000040c5c8541012030300301d40ca400d5000350203954140302c20349040c400c0c01d417400c055040314050f06040c1c440503a5214200003990782e4101c06500485001c9081c275400b03020000d282107480001c0c100950 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 323236438 1250 323235188 323235191
    0x15271006060908010e031603230703020114060f0d03021513050f1501050402070807060e0f0f01202104050307030e030a020a231504030204060f06080114120a06 70
    0x5240a1015002c0201c60380401200c1c2d0500b00240d900800100c141c42020342e280d042c0150044991500b11030640d924130301d140c920280c0c5030481c00b1022501003d844094401c2d0001c2142500301124080500011200c85030300030302c0282c000034a410b1103940d1500d8584240111107204180080c00d500d948000c40d00e82ca040384908200c081400020440845118540405820b111000d0342c1d0003a05041e050003400d00664000468404003c0c8440449412940101040041c00031151440b520341c200450780382120306c507000105060140c18030070081c50710a45004072454a88101c040b102507048144080c094410040c0c008140f2190250614482e6200307201850b51f070f0000b8a0083c00010188103103a009601c40400140142c03900741d40241611001c200341500080f1301d46c1400480764840342400c2d00803000304c03090340350720341d1520180c0156842103809000880d2141c0c0107040e225494421b100001d1810310042001028242001500d054060461000c034400071003002d01c1c0c6201000100d40702c0703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 323237688 1250 323236438 323236451
    0x2091b121303090608070203030f040228030b060612130804080601060203070b01140102030715020f0a12050106020c09070f0201090816050d0f090e0907030b010e1008152710 76
    0x59072045090000d13291604100d4060300389414000c0d0349000050032000803d10740c00108080d5139a59400f041c0313020004249a0840aa6005682c00d02005200841c1c1c3d0010081c0482d01c0c5191107000d642071081c5801b442030696581e03800919500400c80c3c3c09603100d400c10400402c0201090107810b0203849140c00440d552511860301d0411404140d214202c0108282e581d40780581c0d010003103d0040d90000982d914114402400d24002e12490304034a9040100040034021a0380001e1042c0141e8011201000540c1e03a139076050341c0340e00d821060540d01c0301c0140000365078103000d1480307052401003900c000200040b281da1658101ea2215514036085907141c80b01034100703c02006482d903980a0303441c1c03400701c0161600c000b800100d01400f079240040c00d041c00190300c560040105900441d040607003d1007559440010b81032000c2c0644035202190034114010403184000510b030810384d080e5800c0c11029035540c0703050400c03a004030b44100f08084140010084000000c212980300001114000500d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 323238938 1250 323237688 323237693
    0x9010b0a0f02010603020d020112060905090a11030712020603090307021e1003272f1207051e011b050d030e1f2703080103030e0d02091b1213 62
    0x5001404441c0071681814428001a280d004140548a5085c24044150365010402d00d0182c100c54006c40d00840c81c082c108070003544c00103407203000580a0300213005050005420315860b0602405039032940f06100e4030101c0181010001903034800c0440060f0313030502c9184d600080720380d141e10181500c00815020112618034001c4c41e6010303264903d040402c0803110210b043c1041c1540c90310142420014568280c0910410008104022415030140f40c0c280035044a90214003030414210b5000d003029400f03600446200003070030310503a10300801038045070b0191556080108001000783e1704000d00c8650795030f245000c0311943c4201601c6180a48412019400002c049800c4200366a100740c0c86901041e51080c8000407804070001400c05c0440d004250f60300c0c2894200059240f008010207040018061581c0600756a058900ca561900d8000b900f1008100340c5128511019500405036808585070604080030310000b84001d031000da082412442c840e65003414100c0f01c800d520140040c0380000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 323240188 1250 323238938 323238947
    0x50709090c02120306030a06050408120106020f120a122c1506060901021608060106090f050105161106041e0603050405030d090503071709041b0215100509010b0a 71
    0x9440c4200080010121a5400a5603921248591103820f41c000010800c0b580b41804403c5c0e503146c004800380300310b0400345030004441e402443c81040504004d07001017406803001c112554062076103001050441441522960746034840909401803041c03041e11a0f044c131079107006142c904010311420001310800000b010203264680b1200b4030b0750b0740194048810303520034901c13111342216007a586240c54184c3e800c0107034a06130200d00c15541140c448040022902c10003d081410b84445544a0501507034480f29210074048170b01032180030a20031f008203880134071825070f034404190095001a4810b8140008070b1440d9000c0d8001c070303001014000c00074200d4003402c00e1038001803c3e036180030407035031034652145900d9004101407109280c1d20390402d401070080800036a035015030050f8980c020103c15455140d0658000c64010b4026818580117540d4000d200103990b00340c031000d80180205590b81036001851180081000c1510a100480032415442e5005000d0281009801d6a699211500400752 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 323241438 1250 323240188 323240207
    0x1e20030c010809030f160807050a0614060105070f11130209182e1a04060e01022a03031b010e070905010b070303090812091c03050c0a14130305010507 66
    0x14144101e450070f0000807400041103d51a2440f0703000301d40c840d841080303d0b001c40c5040c000050404200400e1401c2480320100e42403115070703c0344604100c0c560800c3c10030f076041c0c8021640035000c240c1c1030041708003045002070265072030f610500448044d40710071400940e5400002d08021500d035808143c986e82d0b410200e0b444803050504c0000d8280514000c2d0220400742c4601c00c00c9881100325580c078a40112550000b40c001e00480d030044183e0000700e046100b03160700a44203100000300d8910080e0950750010900307003070712899000440781d85014554401c140880f615011505488100718002c0403401c4818044ac15403076000002c2108001d50402c0351502c0c8098102d808500c1c90000100188444c182c04c56120961500380820321034014103181c00c2d5400707041e40309800b42c0821410400c40d050045043c1402c1440c5545807100c07001030610031000c82c1d0088404035040003003080f111141d00c0c050040035640b03070440804c240ca00b200141404030b42e070109500440b416911881070100c03640e084402030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 323242688 1250 323241438 323241463
    0x507081609050d031b0f060f0501121106031b07061a09090c01030f0f02031005090c07020924060d0203160c0f020906150c030d0b0402161e2003 63
    0xc0071880c204800542d200d03500d03850003410b1003103035560304541e9401008000d06058100c1043c9a0491060038800042c2c03400038070340c02c1200d14040012560012280b03510300841d42200c0c8000241c0002030a0140990015000ca10224110b20603001c0c03040c2014002c1c00414807400000c00c040031240030a0400e1003100748031a00c40c84004040040150000a580c40c102e0301c2480c01007004115100540000c1000c0d200140040380000204400c14a03c54800c0003240d000303a40808403640c5008100c80a800740660003580400000c0216550a00c046411400c1d800030000d44020321880c08006403895119070b076200245900402006140c186801100c140001c1d40c1c2800c4140e840c2c5590b6034411240c0224001f44241d00c01c07000301c0c0d86511028148907140805250095481c10400701c40b030384d02e8002d2118202e030b841c20104030000e181810b00941d00d0072403400c014210200320031750341c604c0032640388106a40c90311686405013000c64032892140707a404c1400c2d11544031404018003410706240b030f181d00700c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 323243938 1250 323242688 323242697
    0x21050105100b030c030a06050904121205190e030d0c0f0e092e091104081218011b0507060804110306011a0a02010e0d02061e13020609010c0605070816 66
    0x100300700d1034120103c0b6407088454607529683d580d0383c0000030040ca4541c0151350822144403c0004010348111182003905c1e150b1070302c84590103000007200c01d42c0d0044540120180d000e2099040440042d004013942c5880c0c1025241040c00c112004001c0b90400314002000441a0740f5140e54a43c21911461a5107800d90390b4080c0740c500220301c0e5144030403001840400070103101d4005840d0200700c1102d009061100340a10401c000a0142e05850700a405200c46500031410402c400b10101022900b000c0040b01907120300c1c0340b10800541e90b03c83c1c206681d24000d8201d034100c000041040c41010090800d94546050303e05050814030003080d05030881074003035801080140800da000e40011002080d1051006555a00104003203000d00000001000d562044109280e003060700414003d22a006510791107240e40b240151507103000c1d405039010b0382181e00050b0343d072015050a000074030a080303043c1050150017695585845c1118000ca030158001a480402e1203110400d203900d0200181c000c1c81d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 323245188 1250 323243938 323243971
    0x5150a0b07031e1125121e080409021c0b0d03080a150b0706060e060a06050f07020103020c030c0d0305181902180705030105010f05070503090f0a21050105 68
    0x4002e00903404401c940c820020303c00c1c0085110f14031a40618080724030704015101e0752141c04242009030300010801490625600c00040b5140d4034007941410f070745400c5225030032040d00081c58404007000480d001e9030350348803c11001c98030480a0000b00040350f2155440354650001e01d800400302c95484001510450b0340d40103d001003580016604c4e000303102c82d80006076030507040204002c1d0410682c0002c48007600450498240311045e407100d07084440403440e0720055500e03a0100195081203014040c089003041c4110040c00e8110409030045501c103040042c0341c290079091052454020340380740a480d500814030403006603818000e554001100001d40e440e045440e80101d40c40c0c04255001000810340030a14800307560fa800c2e1002103841400c0c282103c5c906003148018100d5109000b02c43c0030600082280c20300a11480031180f8ac0381c0c2140203181003443c0c0c4400c20070300755448091158010f00f12003000c0b650b540088007241d01c0340000b80703c42110b040b8915000f400c0d02d60042c040000070140d001e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 323246438 1250 323245188 323245193
    0x6030501030f12051603030e0105160225180c030b01140702010e030a0f140f0d09060509010917010b1302040e01030f06060e04030906080f090c0d030309050105150a0b07 74
    0x892100010b9103d041411607a00ca40710844060042d901107019800c41e002c054800e25815500904609015030002e00595a0f190440e07402c2d826000314010050303018807141c2d20703040d224400c80380071b44140d0081c1d00c1ca1641d45402d40503544904141c1e802500d0b1340c03000c1d49401503816100b024011082800e00d83c117404402c019032101c80c041c01c140a03043c482e0148680030941d800b4480e040020b6032141050081401c1c4d81011340360030194000d48403052044c14451404c240000500c5401e58400341d49903c9124280802151036401405039641800303482c400101d004c603242c03c110310002210341c0000900c115034104100c01d00540e003210840d9184100024891041100200c905494000ba0b01e214040071515104005042030340c011034554610310140410035921010481c1143c1c1d0035658140c403521052203484918400f544c000b109d0740d0120100280300d080c4030184e6a0124001e0500060f4512103445042c25207004850300307464048103041c18003007840c1c03a001507806001461381113400d00300103a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 323247688 1250 323246438 323246453
    0x60e060f1504020708040f0909030809010b060304140a02120f0d0c05030304020d0305120a050f06040c020c190b040f090c09030c05090c0c1c1e1209030203090a030302070501090603050103 82
    0x301c0c0c4081c0101d0300055860284a000c4044400401c00100c54550040da00c0d0b10341c10040c40c22a40c220001845031011036034424050090a131102e00052a40c1c0c0b65450316550322072200e210800d1b225450143c0350104015954100b00c9081d81c90040c405010900c040d2500c0380d0509202035102c030107000480c0d0700c040124200006587c1c5c4035038103680e00c1ca040782050030107031164003507490482e01c0b49080004000303050080703800280c09908203003100421034480e0750400044c1c4024105150040e030015020715460318207450300b03810402c00e03540d2004106841e4910021203a12a030021254800211000c101004840c480c5c954a0101481c01c144021300b95070741c1c80c1601e81a0b104051007003a040010a800d104001c04540c40034098404031000c0c0c02c24101c02c441400540d010b03035004100040f144050340d0425881000300d01c03809030744006100341641c02c90002803000820a0781140704c10701c00351181d92150303480800998000c0c0c00a2800529200004100036242e070024010541402c00400008814 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 323248938 1250 323247688 323247721
    0x1e0c071a0a02070b0309070b04270203040506280c0801080c04021905070503091008150306060f09040c05120a210903030c050a2415050105160302010e0a060e060f 71
    0x1440b014a039241c82d40c646e01e51030134105401c401111980042d000411017180c14503030702d01c1003507000e075416400c1030084808200e02084130058040d400060004c2c8680400c408044c0549003202011195401c4207615201110809159540400c416100500c0359081c20440c2c00d108181c00c1b0b5040d842c0c01d603142200544150302007812824480081980010043c09005840f4803020140c50451503a44508004159108c1629252901c414520707101c40c40f4100890200e10560000e4900c0c2c15582d0188203120129030014810313a6645541c60001c070380795442008400700c11181d00024501b00100c0d045c44282c07002904245a40c42c81f04c40405412107400c1040700c0101c9402d805d01c8252001107042c001d08051031403d00410070100d00341225a91f4200000303a0301e41c0d5944850030030042c0303200000558000c44074010b00340481c9040c040c41d40c00c260101d2151651901c0b074400803443e00d03031001425180c03c0791880704841c03464403081290003000080100c0e603400078000e00d030300c00b40f0f043c240da040980c0c058 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 323250188 1250 323248938 323248949
    0x1e010f05063c03010c080106180f0b130302030604051507020304030309030f051e0102040f050a0506041e23130c0c06020c01020c03180312120105061e0c071a0a0207 72
    0x4016808610a100010b40300d0b150070040c0090200d00d4104c10010405442405448007143e18034491100040c10f0316821400d031124213074120419400c05625024541080c1e070800c0b010221201c0c04001a1002d10040d8003d41c030580041090040440315000032880081c4100308540c014001000860760203a41d11007240d400c140e0140d85080207041035410000c4007803400000013104e0080d440795050540c000d1007259081c0c032039103202e51744900c00c000c0142078a01c9a02c1e4070a00070701041c002e949503c41d80b54040641c0d4804440c180740d448a03003109446108282c0003c0b0007045050814a080800000401c3c0001c441c0400000c60030010261035082d13075070000b9209540c04180e040541000b54111a00a140081100d8030b400500f03d26121042002c01214001d01030030307406540036218030050352138048041440b55200c1e0300700414041c4c10341103610312040120503000c1080b403c222010003048502c8151000d40f0305d582c2058650b1410b644a0014000f00150030842030025541c0403a0031030503a071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 323251438 1250 323250188 323250259
    0x240702061f03170705011b09060507051507020c12010c0909020406051608160b100e09120a05090402030112020405010f060516021f05070506060105030114060c1e010f0506 75
    0x814034140f4101d03500903101d005150f90701c0c0c403404002c032800b000f81b280d442d003a2650702d06c03ca43d1313140c520403610f9004640b002080d0f580064180f43c01a4801c2e640c5a91203c000d20445200781c0007000090310031980101c1072085079560b10201c401c0c580d40900c4110142078500001c0d49070610304a0020124455202c52032901c0003020604010002c1c08811601a40700301001c401d000801414880c8039898251800c1c0890440407800080800030040468461030a28003e01030703511140300b14900c02c0d40102002006c001c0c0400c0704045039a520310245020f005000141006a5858814002101d00603040324505100d10b01080004990010841d48034516103400e24039125100c3c8049102940c4107056691407460200f4140007003039109000e0704003940942c085803072507100c0000540d0039100a0060562000c1c80084241035428440001c0c04004600400c44000741c40c0204401e0110240c4448540b15945451002540880501a4070b030800e00072644040021080d5140403843c00c1c2c0303000c0703001040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 323252688 1250 323251438 323251463
    0x1810110301121b0602100f14040f1406151c0b190e010e010c0215010303080a1d060c04060906020705060910020304170a0308011401090314240702061f03 67
    0x3c200c008611109071000c00841030350503111800071b0b4641d071001c000c80500030314150b1880c4512019020745c0309041d00c0c285091006803a162600c003400003034000700b6907a1050000081d50000d07010000c140c0300c2c0030b0408080c9240c564080c00c000190361030150314100ba0402c04000c0c1c012440c00c2c0601d9400003031544c070300c05003100510944000343c141140201d24035440c2c0801001d1006040d0171141500c204c90342034070310701014110300d0300441d5020301011300040d100b1400609201034690114000d06281031000084030003d031041403410720219440d00c00c0c44004a4100200d40c0c018403880050302460000d800664103017008924035003d01c00400340b11b10541001104028001d000700c0f00644140d50003444a1840c02408583d0355030701c958114005400346000040364100002c090110800596130b245800f440c544812001d48030f00c45402809005001e9561020002c041c0b44984010302504a0200c034074000748041c2c1002001840507032683c4036104040e80c0000245190720607660710100151a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 323253938 1250 323252688 323252693
    0x7030507140309070911120705030606160c030203010c0306061d0f0d0f0b0606030c07030c02041d160503030f120901110d05060a2102040b030a0209181011030112 71
    0x41c0d000144009089002081c00310120011542100341c502400703081c80001c566018244261059480840c12240040c0c00f1401c103070b10840080d82c00c15001000141042002c800c50111110700340000c81c2c01100c00c41003041141420702a02d080b034091414200681b0340342903409003202c250b400a4080100e10741214080a58806804403841500640303040708031082440c2503222120f03107060a03992071843c1703800241f4034134045086a20400f11701c2e818070300f0074500380c1d0199a1a80700e24803c030391081c4c03961071640c1c40284015451442000030001040708006481070320329003d20b01d0f04040e0107174000300030381d1140c1e040c0d07041103d1030ba013000c0c55099810384e120050f80340182410107616134150000900760080c0c0285800090042c402200c603c2d8003a941d40b12036121481355028152440005032071580090328107a44099164a800b80650b0004919940059a1268100c40400740101718203030315003414004001d180c1009000d12070800a8515040d0000801d0005100b60301e01e0702c1c540c041c00f008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 323255188 1250 323253938 323253947
    0x209060f0a2615100504050601051c060510050d06081c0815031204150201140a0f0204030b07030501030302120c031b01020d15051801050a060807110313030210020f0607030507 77
    0x31148459040c2d468038200d107503100300f40c03a1054914031502c04602e400071685140134882c050041505840b01361814480c480328070b83e485100450a03201c143d4075071000507203407100030329400211025070b5141d503140c03000c140e45801c442168000348d400d54080302803060400010154100600c1d41410007160a641d5100e8224468103620302054142c00f445507803400698040340031304152211001004030b41c8441c45012401c840e820300b0500000381d2410080b6103072110550205080071100344000d4a003607180e0300c50854610b0f007901c07100700080e901c10040007410b506000f0308080e030307291400e0546408210307103c55a5038081e094000d07070007a6244140a94030b0209504440042c1c0206405110500115200414902ea01c0c80703140d00410450200100d981040352101d0b041e43d000411071401681004012980c50400a01c1c000c01d2103080e00c0e0800d02510f0030030141c0a0720701205108520182544140840e246860403680c1c10740d400076107080a00b01010803280e030b2251003440d0001c0c20340c0e41c00400703d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 323256438 1250 323255188 323255249
    0x507030605181014031e060a05160906180803030c03010e0106020d050901050a0c0b0a09120903150b0a050d050615041119020c0409080301051c0312090204020f160209060f0a 76
    0x400070804600701c06e0840d01040300b5128510b03801d0104443e680d0300c140d032a81007101502c107000180b0614000e000c1240140c5a4500f031141c504000100780e900c8070212480c0d0760090384c0d45440800003000400074480c900412501402e014805819860441752020700603005075401281400004112580342500c6050003418207500016105042e0501501141c010b05072036405031100601044c075851200e008048001c1101c0e4000419029100c6101c182d50007484400c0f25907511070601c034030005180c1d0314940d60340308860203503010340f100f42040200d080e4011510342c170703403400745040005400310a031a003401c9c3d81002080c001c0c0d21440440707401c800c90600000000301035015150501c10001d015950001d076069400660341d400302c095822000c2031110300036542c000d0010701032034a002c1d4494800d030000216284040c00144c00c18907a40082081900668049410403900a04234025841c0010352a500300800741d0b1800e284031100c0d400301d000c04119000d0080c044404400d2041340c01d4072402c059 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 323257688 1250 323256438 323256463
    0x80406020906070602091008010f09020d1b0207091404020603040209062b03110703050a120c1a09100501050f1e0618030607020f060a0c05070501050703060518101403 73
    0x703d40d914503501c0d0590007900407202c402c0c003445160340038540c003070302460b00039050380c2d059101d8540301844c06203400041c1d8412110102d0050712600340c485019060303440010004120380180c0801806c016800d0304507840300c1d030002c00c00200c050078400540c41c4d420441e40c10507016502001350b5a40c4902003052098180e844170301162003061b01c24603001c59001c910350a07034400c2d5030703040c0701d441c18582031a1381d000107001c080d003640c110000c804005040004403150200042c10b10920b81c081c02d854485c0103001038822000c01e00b4155042110b40c0800340421840d46203c90310800030f6504050109550090a0500c24081d20345c0100d100c404030111484102e0901e00101003594030841c800d481e05100804001c0305000344103010206214074004214a52803209180c014909661002206405001d045600760140074040281c6400f046003802560310070001928040b800d2454201800310313085032404201c580300d903400e0902809640d40300c03ca07411a01c04c050080340740c1c402c20300003a040521840f004c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 323258938 1250 323257688 323257699
    0xf011d0a030c0f05030f120901020703051002070b06010f021b0604030b1017030304080a0c0f0605040c080705040c021002090a080d121d0a021504150c05010e0d09060804060209 77
    0x810060b07400400e01c2551480d0084a154968560034076541e004d8203100c410349030f004140505070401c00311000d03041103d0148105e0b54465a2034594608042e51654112070090f000200d0300107109982d080190010404c0c42d145101c1542c3c2e00c4000e486905800d0207141c05221040c02c2d55456071180255405150030066064450074007013060300702d00031075100c4e001c03616a401c4280d400b00715001c01528031a0b90040300c01c5250210003a411108241074510440d0900719202d00d20300858041d105191056110307e4612900b2814124a07616108032584032511035030800d040320340180d5000c5000406da0700400000341e1503200f2000040c00c0c1c00000d4001c1d819500c00d03110103540860b8460003040000c80d086404100c0c04000c0c0c150340c200c81c1c220544240e1990712001c006c80c01802c01803064000101480e030110b06264954400900240c0d21201c81000503c070401c03400f00b804401c0c400c00c50940680710017483d4040216a015141c0360307007842004180244100080c040c0500c9030121030300d0b440f00814 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 323260188 1250 323258938 323258959
    0x1c080a110c1b030d02070506030109020a12050405060406110906041a0403050f1c0516020d0201030920011404030b010b160c0f090f091e0f0b0c09100302090f011d 71
    0x28010180b144449840c0d01c0391242868800c40280003080c4142503807000350407240345a0800352107c0c083d5104010311306c00c11041e075824003d01c5203a481110701491041015000320b0509050034010b4500644505110600c10040c41125589078000c0360102c0b090740c0d52820204452041d030100c640200c4d4000b500c1c1e80079914490b40780007400f003462280c401034001ca80418505040c01150319015090700903406003030040f00302c0302619001d0700d0f050b0010320524000c18100400e6a9440e01000400d100345602c0300c111020840b2584c00c244280c9920107001629401c0074a9034480c2841000c040c400e80203101030010f40310002c0007100300e0b5880e1703003504000312056560361895400d120000b54070a0384c0504d4034000c22000805024000e6134000d03600002e0350000e034503040802c0c0990182d00e090803185001e1841182d070010314030011280c46000b00785c5045403200c0c1c4500038091540c0e00c00054070b082500c10012600300350b83c1d0b5040c10790441420b10b40078402d000034440d00b40c503000b151085194804c200c0745 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 323261438 1250 323260188 323260213
    0x30501361106130315020405030705040b06130e070201060b03040c270c080a050a02070c0e06040207050712060b090f04030f11010e0a140d020c2b06020c1c080a110c 72
    0x51000449202d00700313800c8445d60003081d84080740100d00030f49506401101080015144c150015504854001e00c1d89203425443c0750b4403801206150b010403c2400e041c810070507403c4d028030820005201c540c0040c0e03c0c510f003507600d041138606035000d49444102e50300300e0512060b201320b081000c0e0f81c5070a20204424540070704042c0c000101202e10381556820500000c450070800e00954030a660f12035041c200c90b41c1000c10000d0341c80e030300030019600300e0303800d12090000c1581007046500501038104105148812820b03c0002e031030380701d101c036070180710340b881031020034000460025405501032801c8556404004000c89504007a08410003040d824210031883c1044003183d00c1da440c501c108400c07894070405464894075007a903502044056004640541e030307241013101480046000c1040700d0b80d074001042880d9181107404c0384007555119808603004104076410481d14400152020b504401620a008001e0219100420301040d464131070084200c01c080540070b5078254108041903503120354421 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 323262688 1250 323261438 323261467
    0xc080c03040f170d1110060b03150603040f0807020f04061721041701180506180105060603010306020d0f0c1710060807110a0c03030801030501361106 66
    0x1e000e01d5001640460b400103101c1c41001c0904074100c1082c000d400c0a0055090943d14407003d0125019030317000d10f5840050060301ca204d03040c060490308030016140c0c2415985103214240c17031174950b03004440401c01d03c00400d100e01c090255440e40304504955624151012a404100501c04582c116041410200300c1a107103003600f000c848c82c24801c035109000300492070506150b000ea60a40c001c01e0411040c000031999000c418540c00600c000400c1c107024403030000c00c07803030554041034440c2d402042c14000c065684d51861644140010001d00c80c40c1845d000080303031071006120041245030b00050100b11541c0a420545009882201c10000e07070032000c2c0050309450741c443c400318101c5520030024804092041c0c03c0d00c2a45c8807a600c880c4140e998103410740341c03654040e61144040c412040d41704001600f00403050041c504c00d965044855144d880e1590945072803c60145589590010803041200c4038800c660400218021b004e1400802d03040c92266402d003035a440b60010400140b500c003c401c1c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 323263938 1250 323262688 323262697
    0x10915050411040b0603150d0b010603020307180f0b0307030e0106030303051902070506040206091207090b0a060219200a0e04031701060207090507050f030a060302010221030105100c080c03 83
    0x10b1000621a00c1c0d045007000b040340c0c41c3c01c0c1c049911580070b202084101042c6210024440006007024a4800c0707541ca0ba2619414264071600c0041d400000304080c5036070001466030071820700107044540504050f0030210f000c1c510700420100c0039000c000146c03001d1194120344020700c840ba00030003203140c40e4100103019000440340d802c0c41c40000030604c1c1c00c0308001d03c225441c803600013018100980b1154200f02c60782d8002d02a60703901a80c105025070050b070080c030100740100880704c0005034080d81001808080030482e8012821364101c026080da4810040804400e95940322403560b59a0a64112a020301c3c2d03850464903800100c4002d001c1400c000011342c0e9400f590007034840030103890b403820741c0703a003d14030034002c100050300240300c1080000c0b0250000ca42090319400c140d07041c964668480f1401d034104032a03c83c00ea03034075600f040066580601040312000c80070320011036580c1c80202c00080c144418411240904800302e820108039120384014240140d21035001d6075182d0318101c40d907549812 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 323265188 1250 323263938 323263943
    0x110a020f06130503040e0c0702031b010801050901082d100203040c080304030c030305071a15010305010806060d08071704030c080d020102070b0705210702010c02120310170109150504 80
    0x52400480c49220b0529141107034694408000c41c034040c1041285c604400d0064108200501c09000d40700c0146c0c3c0a00ca00c00a004c540c042640c40121280c3c001080075a040e84151301a002100041c04012800714403114460840320000c2c0c10403550480100c240b0062038000c0a00d80074410041640b0300e0315400450040b8007502001d103400741c966104c50340317078800c41c40020b02c1d05001c98003c20001e400340000e0980c26004010b2448054031080c0c00d4a5142070481340c0002078444004c07882c0980da0544903803400742003420028a6a8030700180030a543c01000c1d480a0694000401c0e14020480d2002540b2103400a0014940d11281c0c0c074500310543d01107034095000030380200303000030024034814420b070352937150443c0e0105e206498128058509a1000880842004611349041440340c1c00c81c983c1405105668000241c803c11820002e081c25030001c01c1c10040b900400034031181007800c0c1c80768800d450140382c100044141002c0981d005095401004001052101079800d5500d101c0e4007440c401d50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 323266438 1250 323265188 323265193
    0xc040807050402130e040606030204060e0609090604120e0301020d1505010f050a1d0607060606050316020a050a0b221b05030610170a14010b03161215110a020f 70
    0x9444200b0401640182e600c4c00340390011040e010000c01c440c941e005a00300d17014510004015440341c010409031031650700b10800203180320007801143c0c10003141d0a50f00400182c00b84c41c440c2415070340c07400c2d11141e054420702004007802805105940039812104080c1101a04006d0b0359401d2a0050320407403144501da02003a100341201d021507016030111404a0629a0790200500e20500d290340022044011940c01030001e01c50740b00001d10764454440a0138068031400e0712860f0a0340c40d0458008074102d003d0454025450301030024600042d03401d5103030350042e42108240d403190032a680e0401c0c1c501c586000203656200c0e134014080c0d111445068000340340d1200c404103448205044c2e0300d84d02610021024011146e04000c20000b50a150b51900500e0041c1ca500802c2c40c2c5600724041e14070b07140c000059644051688051404000152401160604007140c9618102c1400c094660101c80508440180d06005006894680c410503011060203211078480302d51140003599402e0319140b044951 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 323267688 1250 323266438 323266453
    0x618021314011b050d0f17130609060905160b040305150921070c150c02041a03070603060e07030e0619060e0702010f050906090309060c070f0b030f01050d02060702040b0a0b030c0408 80
    0x92040c3c8035010b46500300c7d4080091030315814007205086640400030703110580e42c1c240842c001100350203045c400b1802027000b0400030750a00540c01c0f040341181d20402402c01c080008000040000c03402004a4004803090361140c1c0d21a40d4250400300802c25001407600c0c0c0c1c52015000000000252900031f0040c22031050075600c600c5282c01d5201c44065440225074401d0302c8500500e086d4010030540c00d02881120304041140300403a2810403550803600200352180c500348400580c2499265111086140901c145000c081c10a91910710140c6401c0a5583c400700010f5895660340140c0d0007005201c8019000340307001c04c4000d0003800f00e444881c1200d4282404680d0403440012118000c00302d03200a94035054016007003019582c000e21502c641e50041e80d07000210f186500302032000400c001c100090b41c92500c0310080000b03100580100340702c0c909085050005d6100d0700e06690072598103a800017140205407001450340703220740d80528864107002041006014980010300100c0303280c1000c41d03c08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 323268938 1250 323267688 323267717
    0x80c0f030406080c090111060a1d16030b04080405061603030510030201120c02070e011d160806040b120a081308060f07140c0109060618021314011b050d 67
    0x181c0c40785114010000d0040000b1558000074a0004c04c410070f0141032080c3c000203240307245c6003082411a90030509075650501c1484410f1440c8404c4901c6520710301030144045403500089a00001e80000ba01462908000a08004880049a0241000909482e240e04c248220900350f902c040c0800c41c0000c0c2031501140d803840d02d0609280540f07a058540b034a90f983c91105000081c458600e40800318801c3c00e900260501c20581041c2c0a0900a0161954944140c41485041d00098034050070140320301170315221294800380b85508811704440c0456250f061200040305c0d400c204410901c140904000e0404028089000b000713070f0342c3c2003501000015505c0000ca91224400c0341c2e0387e1200ca80d4400014141071007401c1038404d50b41c074891420304081003170a00608541e0480c2c02203c01c65601d0006005943d458203501401c487d40600c150f20f0b040100e140310808411500c5090102c03042c1e10802ea92a80c081c101c0351022820540b070a42a40300903080843d072f0b4075443c44494001c0382000031107206 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 323270188 1250 323268938 323268943
    0x61a07051b010c38070c081309050910230610050f0307081602120f0a03060806090d0e100c12120e0303150103111602060d05150a050415050f0a03050109080c0f 70
    0xca00da179922482001380142c1c0380d43c5130603804081010440622401c02180e025610f00c5a035004030000d2000f404040c0c201840107040300d1000060700080d58010080c1c0c0f2070000c2c61100d29070702040a17a00c02c0150212610266a54041c5030300c9582c031190044200082d50f54460402c0e8410351004a0101214000100990312a062350300e006040400800945120080c800001d214000081c40c002501c181c0d034000140c10504140c58031301c0039030480910181540e60011440c520a40c003100d010403640c100b1000030380300148040c001403800c01c2420103191004c0c0207207a24504011181000e010100f01710100a80f2507000702c82c0000240403a40801049501c07a01c5042d545440120f04245001c1c115a8920400410302c03a003280d10820402240b08040c000d8099207004040c5141d0403041089c0c404100034000e0b0440c1c2045005514041c441442c08080600640480f4019500c000454000c5000700702410542d40003d00203600304180e26041001c070380010041000000290340d5000381e034061168 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 323271438 1250 323270188 323270191
    0x319050f0d090c030c080f060a05070903030c1a1e0a0c0905060c0106032001020d110d0e0a0503030406091d090607050d0b0a0603061a07051b010c38 65
    0x89208000d000e40c03407507003195501c4404840d004010425000d66244c1e101c54111859400030606900304d10b0b1480700d40ca5040000315002100034109219038a0460b200801301c00e030911020b810018041c121009000e15800784880d0104261004061464840d54003102688800707041060300d481100010340340c00840c46410402c4485585440d80d05103444200035494000a0020050355a100c000000045641c0c9041001340d0402903003200d9402054000ba040c6403800eaa500d041c0b1607500d408549044020441c007030104228200400c000c1a42808262511041e803c01e0781c25120000b000b080f101c0d0802a9082180e5414220f04c44031007000c0210180c0f5207064a42c10325591040001c184201c0c003c1c0e02805250400182c00105e00d0349040026030003101c0c0e80c0c0300201007036840c0402d010356035529002d20005c54520700750500e40f40f0982d071030683d64416100182241d0f1726000005034541e202c1e690310324a240d000005000070030051105160703000c181c10721003024842800030f102c00082c00d110030309 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 323272688 1250 323271438 323271457
    0xc030106110705030319140310030c0504021603030e0c0310050423030d050406180b04020103050106020d0504030b061c050c041d0c042a0e031605100e0a03080c031905 73
    0x214100000d1b50307852020344141e00407130070034030110404038030348040048082d510030004601800c01d00c0345141025451036189401c4580607a00400501c2d8042070718040141005506250010720f09281c1645a8188001006666414002c0d281d600701030850341e800050003a4090540c058800403068176041d402540001c404006400501c07610318400f100c3d5000c5540280128804144081d8a10300f0340e10101207103408558429128080c0015960b06216150152034036000a180510001d00090312500440c0320041c0100301138000940c49031194013000030401a8149002240d00d40c0745000d80d1178803a02d00903203010380d01d80b001c410340e61801c002d0786644c084c034008050300940000d24140000707405102c1c01080c180520441d00018241160020030403580700f556040c59045c0c101c400c150908100050000400440b80f02c10b0040341d03101c640f40e100400d501d061920203c0900c001281e40314200d079101074018840130510a1540c8400b0000306000a01070404001c0c0f85840c0c181503c02e400f0703c4140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 323273938 1250 323272688 323272693
    0x314070306051f0306210b0708060604030206090a030b090a060b0f10030216050d020c0112060803091003150f15170c1804240e1e0408120c03010611070503 68
    0x50036452242000c50f40f04891454045640da45600740450a40e82d00c406116070b500000b440a070500c0fa07450090b41d003001c07061402c50114207200000800c1800346000103440b451002074501015943c800500c4003d6074005401e030640d14040c0b00b000e13201c610341d043c207aa1075030816900780c10501d4480181d401d5004020103a80402d12940340407002500460740003104610000645404a04100030b43c0c407402441360f00604c1114040d0f030004084900403d4290101070030030f001842010300200550300c0c3d840341540c18843e1000c00c94001c8001e0203852500040421078000045100c4032841900d6042d0368034a610240c903041c0d190303400c60704050300803000034007400f00c000410b540c09410002803542c07210301c0e81c0b000d034100074500008046031049002d070117004140100c030850b40442041c1d440700402c0300c0c2ea2240080d10303000c02c5810404031182076034000084400300090400c00d101e400d0391004845c1d40e03400b0035903140000102034254000e008003000b10305100700140c1c220030005094000d96171b01501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 323275188 1250 323273938 323273959
    0x6050a0f02160e1005060c0c0409050312010e180f060106031e05090106050906010903051b0402040e07090323070e0403050f0c0a02040b0d030e0108060f030d031407030605 75
    0x101100c003862440104011800b419006400040b140e12401001d4103203119005041d0409055144540070b05600003030003a9811b01009510b0300001c102032020700340950740410564558a45103013584510440000d0003c402c0001107041031b6510400f61045880c0c03c02481c041000b0b48880303541d24800c616082c4e05a2081005014051294003c08a03100c0c904800b5011a8041c4850300c00382d0720201c0c0c4191440e9500c1104020519010702e100e50004001c0c01e10b02107a0b41592030305a01c42000702a201d40a10402d010504551680ea04450050505c960841728905044400400508841c401900c204c100d02024100904c50412141c2d076001c80c00d0028a12289002d141c889a442d00410507010f01500340b00c21940d09642800400d00d0103503640241c04101d0b89441080200c0c0c1484030214001c00e4418580000a41c10001010310301d00c1c24240524180e903031800003450746407000710054044c0141c0c00060302c8150160812200b050440c040a88a580c4414007142110654071036168488c0c404071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 323276438 1250 323275188 323275207
    0x623070b060d0501111611060c06040b150a06020a0501050a0204051e0d0b01080d1b080301050d0c09061d0610050f071a040807120908060604020f0909010b0903060c040605 75
    0x1091041d050300c568001700b80c40140048688040d0030104140642c007040d11441d00811003071903256601c1c5442203607000e082c0240038150070f607101002440207060070310500119080c4003c4402c404010600105844005600c50394003d444800550040f80d0703a6081030040741052100d802501d00f581c1d8054807a4401d42a4143c002810401642c0100c0d003104980150384042040c00714424041c0a01800a010414a100c0f006114622081c80c14400400c0c241c44800040c0e4140d08a0741111070131034911085c40c54608040b0307107005503988203d040c54603206000507800d101d02140244145070500c09490b543c2c2e02014050019640350340d07440025010040c5200c80c5048002a000540c0075848028400080c5480458401c005440c10354038120701003070441c00c0164006000380a10304615000030780c180703801d80d166950b4034051300c8544a2900440c88103820355521007500c00c1c2c580000e10703d4007a965242c04012450f0300c02071026019008400c00102c00b0300280d000c0b030b0121240d543d5140d14008416 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 323277688 1250 323276438 323276449
    0xf1401080d12060e0114030d0f020a11030f0d080603010b040605030309061b0307050304090c020109473103121103190b180c1b06010623070b06 63
    0x1c1c255441890f965800c0400c1d89583e00302c1d9907000c0c0c00c40440c2c0071501d041e844109890324000142e000100001a48003110080d0b01103013404550303a04c0070040c030103060100300090410320581414038107481603aa01e82041944080c0741400b81006500030800000303186c0501095414501a0a800d544200544581d40c10020000d01d01c418207048a4007100010520303c5055a010344c4081d14280e001040174802094503105240140720303140020000030710981c4d107004854203d40e4800c0c030f04900d2065091076180400012401100601042059015115443c500d141c1c034192024035020300f84211480640d03809220780103520300e920500d1a000d001c00e81c0c049070850019100003440917164082c1e0104551410060350142c92182002c0d1006044a2903d00c2201d00030f9002c90302c5480e0426511881c1d03414400c05d160080c00d68403045a036501da001e200c1030604070380b0f00115a00e00c42c51b800000c40381d51012a089200004070300c0740c418a00c403204012400c5c0a60030000d84040003886c04a00d040c90003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 323278938 1250 323277688 323277707
    0xb030c180903090307080303070201060e010e0f2701050f16051206010207030b010801050a0e01290301181a09010209011e0212041412070b160302120304060f1401080d 73
    0x4a81c1141e1800c4070f042c0109040c601c556011840039440402840421502030054030f0140140d08051a2a90324003821146404c00250052011a050502040040d42482c614261041b042c2c4403000130001a141094000e05d0b040315480c1d502c14846011405c4040d10744051002903006954243c10100d024401c0c02c400c1e0303000743c02e581c10f40c4103000b4000005241c800440c0d0003011203100000d02c900d0910302c0c0c00e040e80c506d540c050740d00380d143c6030f1140d51245888900c81828003c582c0c111400000c00720104e401800d58450720400c1e81146a4011300300034200683e500c184007001c41d00c1c08541c584080302c038240d005410740c50b0b02140e600090324501e9400d50400c1d1100d24a03c0c030490b81c59138070800040c8219401500400300300c504003160422a420101465952100340b04c00030300405190406840c07c03406045003d02d540030342c5a0381074052520820151200c20444040103643c0d04241c90880010440c8200d490320407420701c2d50f00410100000c805d68101d4440e40050015449522011519001e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 323280188 1250 323278938 323278951
    0x1802010507170913060608090d050d09060e030304060b100302090307150c06050c0c01060503071206110f0a0804020a0504050907030605090102040b0706060603051f0302102109060b030c18 82
    0x14284503a12441d13441062400524041c0003001440d103050000c024441170000300100c41d65440005080011903120b42240d401460000d00041d040f13140d4544000644004034040025110100501040c04951f901000d40311a0403280075014890b426002e80c2039003d0308100c40d9054014020402881040a4450441d1201450072942031a25640e514003202c0c1305483d1464a00b0020824500b945004d210340b0300544070407001030402c186010403809c0d041d80310131002403080d515100d0300781c1440c1c02d0006803002e02400c0d8030b01540b0360380030150041001a080300e0980c031403815981e000032282403e2144030702650040001c2d0002c141513807581c4010380300180800440f903500b0003001545880e06c0000d840c10601c81d42d4003050341c1d4039000c002015550060b00c02130706185a41401c00e03007080254129012a03070306494201980901e08006d0b0364004024400d60394170001c00300303c4d41460075550310000c1310034480c0c402003048440d60024183d492101a200030717000300300c2d0b25140d00c510943e6501d69a0111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 323281438 1250 323280188 323280233
    0x506010e0d0b04120302070804050d02030f060c090a0b040e04020d050f0d050306090a0b010903060908090402071103011104062c03070b0d06050f0f0d020f120a03031802010507 77
    0x1804010030203200040000b070ba40c0c000c0e48001e0108012140d00481511040d0307103015800c1004070f45500904c0d00c20b5110f0a8400d0501064a4046407814401c085040900b44180d5100d0702d400c003002026940140c50103407040c001c07200b001c19040c44480507a01940c0d4101c0d8002100e03500c542c01e000702640f0a40c019a054442d00c8014070380c4d103804018044100c2d489640d80764507410f000060015800c0094808109c807410b054402d1016684142900f0480350441404a2009070600b03111849100c0e90540e190032600010b410000d114408603422017542c0207400801c40c1c0750349032a882440e4003850061400040081d400c29070345a18501c0e2501c004034241d0181d104140204c4000780c5449110b9020426403038001c04d11102000341da10816000b024182c9000c1c140c0c2c2e20580c0000c1503401c001d00303a00d00c15440080b4000075900c0300043d81074160405011402c00402d250380c3c41d41d0710109a001100040e0900c0c3e0350410507613000c03c50300780341641a10b480341009a142d07100030715080c1d98030140b403849 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 323282688 1250 323281438 323281457
    0xb04030f060906060503060705090913031e0311160213151a09100201050f0f0403020d1d190519030215160803070306030309060f020a08030903070c08010e070522050601 74
    0x1b66014854507018130340341c0c3c4405641b80d24040a000c05088014110210403070185c1c0301101194118100300a00f040ba1105404080301030f0130b050700205166420742803480e80c0802d15000103000b0015481c1c11078001c5803c419401c1c800048802503c00703c55200d4040080c0c01003c00844203100c20440d03042d0709080c0b007141044d8060002c01e10f220401c880500042c0c0d100c5060081c052a02c5001c1600404000100b0302c8a141c181c0340a0f40c0c501011144d03d0412122000c1141c0d10b240161400a03c424000d02c40104d000790078120300032001d481e028691050150303c1079006444500c1e0004000c40354042c061141c0c00315003192070012038001074000035126020554000008034400021403003100c40e030b1000902c090a6041c010444402031b0441800d01c2844100c1ca00c8049d000151540080c1c0c3c4994060741d2607642001803030460140d00001846150380070000b04129a041d0072070000c2c07024200496995940d1042040701041400403a5426003048001b01850401d142d0007603a0b0006d01810000c038003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 323283938 1250 323282688 323282699
    0x3090a050a0b010608010503070803040b0a0c02120f013b0c030d03090b0a0902030606040b150729100303030c02011815050916050108040f0203030406050a090b04030f06090606 77
    0x10440340c1d034011610100b0400040c0032951300800d981e4050b11041d401403108a040005050340c07403040d4060308803506004140017216910440f9100c56165000c2c101259030b01c06000c0031650760b40020b0703010b581942007104020100b55003003182092010f019480d84c000d412100400901da00c0403d0a08409009903285007000752004c0004c055562801d0750b000a0761060341c106040391a60241a01c0f40072420551042c015075000125282c00200c01c4800041080c00c08002850417218040011100c400c04500d02080c0440302c0c038640c1003821620640c2d45040c0381d8050504141c2c0040742c0c0c20f82070f00b14007d0140f0100c1e2081d4003d207481c010340d0000180203080800320b034818200c1c00d4021200011105402c0103988401e000b041c1c1c01000740c0700204109034460b804484180210b025503410401201e00050a020000c0d44840c022070300a0103880d40c45882e050010290307402090148082110f0344000506054024215000c0340c0d0042c1c100c2c09a01000d965a40181c50b0110040c0c1e220b82d142c0e000402c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 323285188 1250 323283938 323283943
    0x1805060c070b0f0a0e090615090d050f0123010e010e07121a010f0201050103030912051014180a020307090f020d0e030915090907031107120c1406090d0503090a05 71
    0x1100d0f42c003800869100e400d00702c0020000c44421030858050034503a014440240c513114000e464054a50b0141da031108800008140056040d101c0500288a84001001c02c0d1006600a12044040c2441d61000610311000410010300a2160305009126903004100c440001d006281d040700c41480c0000803441c00b890304406131100c403000015490714544054080b0341e00944a4884200580002d0100b07615545000d0300004051080300c0302c000c0340c51940e104000062040785100310b02048208034070900c0302c9078041c0155007110028248500c14403400c0c050b10000030110340285c4d004005220b5981490041405030070386403440080030f90240103104844019024840c90802000001c540722000319081244507100c40c409000c48800c100000180c9459811140760300007014140070407107075100a50b0149902ca84440038101610310112001800e0340022506156070040801080040002c846180c54141c00e881d03049895000c0c1c008104110b010b00702856001203600b0540340e0031440b68803042d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 323286438 1250 323285188 323285197
    0x20904020303160308010905010e07140d020c0105100504060e01080c060d090206070521090d060c050f04030501022107120c0e03010c05040830250602030708071805060c070b 76
    0x4c000c104c0d03940061025480500c1f40324010408480280041c0c180b840001d080b66060f2001642c1e0200c00164901c0612125011220004001c03002000355117082c64818064210038001e03244158100040001c40c22845d01d5030a058404036000340440084941c10082c05a101c2101000307400e494800f840090780c1c4034006462020b000700013800d861524280300c0042ea00007584000304240c1c00f8040769499454102000c4001c95011a00240c0d06440f404161200e0190300d61100110b400020003004000c1c064020b061044841c40c00643d8040d808014000c00140c1200c040000501e24060008181210381000b02602c01e0350405449074600b58020a013501c03d07182c04840400d031300090400c03514400b003101c0c03110210b03a6a20203003060706800c1c2010034003000340003240200b800451240400c10032000400300e011400000c43c9c405854a1500c407019410031030341000400e2520001400719801001c0056001a032444001e541504040c208000ca4103d17840c12001440f4500c000b140c440b20b0380b001032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 323287688 1250 323286438 323286443
    0xd1b080a021302070b011823042f040f0f02070503180303120c1305030118050c0a06171b070b071808070501050c030c0a0c03021203040b04060309050a0506190f1802090402030316 78
    0x608c01c1c0c0342c1400c0928589034001e138540703080c03080700c1d25109851080300000391100e00100c4010411540442c0c451014104004442c0041480002c070003081000010007042080c400c440d00402100040e420036803030b4096500c83e864200070510001d03a10040020082c4020b8118a07041000980c032400802c2c2107071071055100746031020410070700051240802ca06000c010044404652040c10b00e007004000061400d1b00f003020a504d400464101d04100341104d09407045c0309012134541145007013020f1150300130340d10314010030702c1100744400c401c0c45190202700743c40c0f51100070b00b03040e071820004403031503401030050741c009010601c555000b081c014841d00d0710040c02a500142e40380c0c107600404c414a00001240d038010350040004000c070b100c0b070f0402c0d201154a507040006402c5014200103090090411004103940210010001c2c450301021b09041c3c0070981c0841000645d040c40707210000c5454403000c00000403240000700005140555080358094409001d8905103203040001c500ea00d24110703001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 323288938 1250 323287688 323287751
    0x6050301050a0504061206022803021306020d0212030601050d02030c030a1b020d0e06121006030f2a0306030213020705100b0904020d1b080a021302070b0118 69
    0x401c5240b8142c1024800f40c2030842d030070840c45180c0344e5200300d02102c0c0e00000704946d4000c59032040d81000400004c0308024540780c89102c459003407000400a5000164142104040c90000305925100003030041d040300485d0000d0008a0426141c10405d0300002e14940c10440c3c20007d44289410314000745014086c2100850303141d0418080c5d4100f0b0b07036200074043c0103038907180145900d0540d0000f03001c0e20305080790501d250031071100400f14416104207440545540792501c14000d170b400190384814200d0b5502e40e02001810060401314080c4d842d6001074683d4158003d003030b1001d1005100d80c41c0000d0406007800548150390394041010201c0f0003910320451503020441c9801d1020901c10740b208100038507170401903a0418000940742c10b80151019005500448803801003140c42a007256821032054900c10f407645c0e840342c45680e13501400c14201d024008400d4a94440781880c02603a40007a40640e00440303581c2090b080e0788805c0c0c0403d002c4940e1581314402552480001c0c400403480d03000e104c24 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 323290188 1250 323288938 323288941
    0x11061803010f02131e152708070603050907210605071e0509031e0d02101103070804050109060c052d040501050f1909080d0201020c0a0f0615060503 65
    0x80600b1100c0030040035040ca0b004000c8441074640380e20380007058400c4c84040c0400d10400c1400038607000b01c02c6d0014000c501001e0201c1c001c0a40100003040d4015149482503014040351029401e204103903c02e00c2172590005c0010300907e40280c00a580c0420f03e5401c95903015500d8000e503450525854030746590350005242d000c2440118003845030300003428200b08030f00d100504950b1003e03182003035440081190100e0004100d540c03e11140d0f140d1144a0500150300ca00142c829456111804051015100d03100608405000034040d900fa00135907001c03024190394409109680d80350b4002c20807149950788443d0400003651034401c810340304e0855600c8580b54511a6074010702061120018403c0780581c0c006101d0403000312040300d0036281d00303103805601d40903401590440c40c021040001e4094001440d040b08551f801103400d0100c501900c00c46141c003280d008240e00702e01c83c010304800590010100500411350005141c1c4001e44a24400180403644003000b0400909030b41000000910000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 323291438 1250 323290188 323290237
    0x1d1c120210020c0c1203070204060f1401030902031b01050c010e060109051302090109110403050708150f0f060d03050f031906080f0a060b15040306020a030507030c0206040f1106 78
    0x3000c007031408903640c02103107080c440c42c03038142e9240160803c03188a542d00c041d03009004503040c4141e8005c603901520030b10071140c544400c1c090703400b00d074020b2106105031400886001e41c801c5c000d5401e0701f500980900b5110b5401c03c803149032078803030605982c1401420031070080104c109201e817020340c0c0740c65809806103506104500060b5035000d84501c0c00403034001114009030b0345480515044810410000400030404401850940540e92001e04140120040000c201502041d000307500c072600c60300e1101715941c02e1000c40541c4012f41d81c0040000c071100000c0c4031402d115072581c4c0c3c3c060090400f14200314680f010494554000c4641c6051112000600b00c007080782d501030745000d4524400640610800070750255034a005501001e0641512150300700401e4692000d07006022210040e2142d68603140d05001d006588059040d0000038517110000346e03801d02c05d10030007117000c409a0141ca12a1265140e03201088009030b400d58562850900041c19035480034010220700d42c2115100c00d404403101c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 323292688 1250 323291438 323291443
    0x60a050a0b01090308030a3201051507080403060e12180f040507050a030f02070c030b0f010b07020a090b12061801112802010b03150411010c02011d1c1202 68
    0x508600c1c2c1403001c1a8010300000e11000103407940300303040e08000198201641c1c00700c04d16607981c00058201c4d0300000b40040c01c2441080803941070b0ba600751079800011003003504c0300e43d1600c1141e02c09040010148420f00000d6056040501c080ca024422908040010b0345116079507072100403100d02c1480181170740c1c14030741000402e0310030702c6500b2076040200d8a804100a4002c0c400d5103030b04800c2554540c042114940b1030342c19030712100d40001580004030344030b02d010b60940030296442040882044000280c0e400140120380e00ba40d070180000003450320300f101400123084c04007400703a8044119031040b03074a803400300809441071239414440d078401c2002c220501e0031121b4800c0103002c0254100001e444400c0c0b8094079120821025080350211100c29100b2801070015241d0560316003e020744007031503035100c40a46c1e0f0145004030129030311710141c8801500c11941c1e03280000e000c10140541d000440d000c8211101801c08080c0200710103591b0317100f480070546c500000855103007001034840d540d1140e04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 323293938 1250 323292688 323292701
    0x2001020606030d09060c0201021e01050f01080a0305090d022220040f0e0402010212030a02130b070209270105130303062304020a05040b0705010c2703020f0a0305060a050a 75
    0x140c01a106400d07085038001c0c20044c0c0313070080c2e005010b984400b101c21039108100552020540c4000e00508003500981c0d140680419260001080070b824004204c20401145000c002981910b80301d241c10554020b0000b20804510241e910138140d03150000080c00f1103141c0d00b01c3c1900328800240c4a50383e80398a0320700d00002c009401100c1000e0106011000c014403a04040e1049600c1e0444640e94901c0100d03d0401d10300c03241e0342d81200c0031040c49124407460300902101c1d08480c54004040b5200c0820300c0c4140650314001e980000040b0108220480014079900c2035000080303065540900d080c2c00b9030079510300f610400369030901d881e0114103060345403048002404032040c1c500d9150f049801c501001804003a823030391055070300091007030074540100100e80051000604a81d120591820f101e0b0003808500c881c100840c4107441c0d1000340052a03011988448601601500103e08503000d00820703202501c661608822802d101001040007008007502c40c21000d40081b4241c80c110900c003080d54107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 323295188 1250 323293938 323293951
    0x3030815131b090b04030b2e030314030c190203130b030a050a0605090c030a091a180d0516021504170f0102071109070e100c0b010b160212010920010206 67
    0x30a0b8400d101c1c01544c14126000c40307800040c00040c9071990440550f0301c120324144803200100010107441000d942c00c2e01c0004982c001d03150241450b10a041181051008072840c90468004101c1c00c0d107140311464201c0d0342c0c099507204070380c100010b0280c0780b861500c2640011000368008410068038020300d0081503800310a98009001c410714040100300c2d16a00980720801030381020000501c99400741d4000408a50804481d54900d0320509003803903c0c0b1720a68200850280c400744110302c140000514280f440000d80d240c0d854244d1440410f05904c6600030120fa0042c0350003400b00c3e0000c0c1d850060005020000807080d540c200d030a80c440c0c038251511500c5922640148145000300d89c6007405903071034440c00e4443e0406941d80740011101080340350512540024603d0710401c0c20755002c80c00300c50052150000c80c5e81a40c0350703c03600a16024018110045401100d100070041c1001d00600e42c032819460000b084102d0955a06a046081848002d842c0720000c007140b446503a04100d00d640011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 323296438 1250 323295188 323295197
    0x80706020114090a111e040c0305091b01091404230702160305060f0901090b0a051801060308041208040f1d0c07150c02030c010203100f0614030103030815131b 70
    0xa82a5031804880401915041d100307540c1e06060701b5488400c1c0c0d41e013443c4032100910130400040e0b1020040c00074032003915641070704c0c070a200c0c880070741200f0180c01e07040004050b100d0501003031400343d2100c00c41198801c010703000307030b01c4d8101592100d24420007146009041e001e54100d62403d03000003443c1610ba1854582d1043d0081802c1011034004587c0d207400403d4198204813a944034004d141c05001d044400030402e1980c0410409400e459500240c0286510b000c109210100300e00d01900741c0b1101e0002402d00d140401040114501001c081c01c0c100d41f04060460074540e442c150446400e403075a0004d041c5030421a981c010724400000700c29444000360000508048c4d09440d54203440070500540c0030020f903600300f0300c0d041d0342c020420758031030a084200030340d503920703042c0700300d48105ca107502c01d21028050003580803d01c0c5001d0f19454600c030a4070040c0301d04680c616181181c840201402240088098084546a5071104185403c11410b0900d0204039442d518510720082c804800c0b1040410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 323297688 1250 323296438 323296453
    0x18110c21031501050306060712030609110c1002130e100302030114220507080d09080c01030c1b0201031b050a2a02010815091608010816061808070602011409 69
    0x10030341840d60b142c48a03400e10b00240c60356911030204005124012014004800b19816590025410b8000c8000da68900c04280303c400003000d441c4400d4000e0140c0400f56800005180c180c22103154050101403100b80c000140b502e60f075400503864241d05036142c200340000b089003030042d07003024022541312001c01c00c00804d40d803806010038821076024482e03182241066110400a110003000303801c01910b4003000b1b442034103600a60103015201c2611500720305002d14051001298060b2251121b108501d4403580202c0c600e00d22901103a10101000301c1c14540c0d43d0302403141d00c030780540c05d106c03400060742c0b00e0303070355811300317004c02800c044a1001c0710610310b0704004500700180302105090081560a0810300010388603555076030801c0f148182c24940140b002c07030030403850b44020b002d039401c80f10040d119a0b115981b20806d054484510340606040300701c80d41d00402c012441403049a41e640c1e03104140d9a02640c4036100141461510391015005039141ca1010341c00d0f2540ea504190411007410080011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 323298938 1250 323297688 323297701
    0x10e0109050c040f0e09120d0c03140c16080c0d0e01030b090103110121020f0901080f07080f0c071a011502030304050a080903161215050402030718110c2103 69
    0x2041d045c1c010503081c0c0f0b91075004203070307400c40c1000200d5001c46800c480b079413105e545040003c01090444841d8000038101010744610b804c0803a021070041c85404449440d20b043d404c0040441036054030119843d1100b0441050240018030101e0540c81c0545e641a0a070301d034610004090b2401c884010703100b05049001000001c1414550b89010082070800c03034092070034180705d51500c61511407810b0381d843c0001041181c01007890010301060009886404458440e642c0400b5070303440c00c8a0001c003007202000424044105080740550200d045000c0624010040d0b0740d2441c03055070f0109104404098000500410b80c150a8032648800c2510040d07040d4a030a807241175507200410000741c10614001280b12840e1418070203124003001101d042c00c9069541c3d079050000409443d01a80d601d00d2041c10040c07542c0c140d02800d40180e40050080c0308082c102040044804000794102e0705442e03807075000000c40c100c0f40001c0c0140c0000400a8022040c54031920410100e520050a0340c421080003044030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 323300188 1250 323298938 323298959
    0x9050c1c180f050a02010801060f02030a0513092306040209031f1d0307050105060d030509010e0310090c050906030a020a0317040f0b0c0c0604050d020405040602070b010e0109050c04 80
    0xc0d1500814045001c5007040c28480003400c500e00c0c040c0030400e80d20107980c140540081c0001030710380300381c0c0c3d440c0d02c0d40ea958504403401c2894a81ca640140c1080013690350b40f030b1060010700328520780360700407040c99075640c0203540c00c50f0b411121152807000001007900e1a87c1d504281c941d407002003a24158038000b0031138006032311814181c000d03440d4842c0007040030101c42c855a1000500e08900d000c10381301d41c211b00303800c00d540340c000300d10440390fa40c200302c001a09800d11000b0524519859180e840c140b48800c001901e01c0d191800090f601803044800d00751904605000c0c082c0414026a40d440041c0e0422080c400c1d0500014201400390307020ba40d6210042e1981140c00341180d400c58242c032112103103652002281c3c46940d0001a484282e5030001c035140c0d40e00d000400c80549488105c40c03050541500788113a034015449a0781d80001d602c0060800f500b403c0c0c02c52070b401881142c0040c90b1450a94402e5846403084e0003010900c511040140300c0300e540f1344581d0350402c3c1d44c0c061407801c2c640341212520 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 323301438 1250 323300188 323300227
    0x606090108040c0302090408072a05040f0f02130e010923070c021009080c031c181806150c02130207022d030c1806280603020409050c 59
    0xd04000d1160005001c0c00706814100d00555802070090301203050509040d41260050141074075000900c0050300303903814040c0840e40c0540581c00d20403041070701d04020030004000300d000c1c9180051715400400d1180c203192004000028101d51940e244a0034481980b003091016004410080e107840c80b2032020f500400c08134809800307a00103c0d0302e5551200381c225022107020100940040040d40400320036a013151b000c405441c2035504995002ca0001c081640c0c0f091140140c403100322465803444900c900c6000120204076441890a40b03032940c9119011011a51000c0c100070703243d0307400c0140a5420b88225950002810340780640d120202900082c80a0b0002c69003110a540d0001d040c03130440d01c1e0fc1307149522240034500d01510310201c0342c08002c034002c0784111940c440e004200350742200f4500400f08040c2541031032140519956490140004180402821310038031002c0390f074121034040c44681e03840190100e55805a00e0341d1401d000c01e810b952000d1329a4000e10000c0c040300340d80702100d25012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 323302688 1250 323301438 323301457
    0xc0f1710020901050d0c080a0e06071e03060f120506010e0c040b0a2601031101140d0c0e091504050703060b03040b1008010212150315010b0702010201020f0307030c0905010201050606 80
    0x582c0c440c0c2000c01a5194450740040c003182c1410100641034454214000a10502c08030400b80311039103e08549640320705c011120680850b2940b41180c800c1001502c074140c200d0300b24100001c1d010b40350100001d00100030b620441d50004100c41c1e17402004820b00c01540100141181a5098200000385011901580c0101c041c4041c2c0401c940001c144130b100c4036400c08001e0040c0c1103007003800410800402009010546108001940c086050b512424030f07407070b0407810240003a04101703070035002c5c401a0041d189800c0070450b5903402c420b01a5640e50b0a113000d21400140c4c00da5a000d42030074802074500041c600014075140127010090400010200c80c1e00c40c0d84039448054558616000144514441c2c20101c695840465001c3c05001c040d40340c81e008440d40c401000c0115245010140c2d194103d1115402600ea4038004002c0414130a02400207944140000340c03c11604d0b0b11541400e8000b02c0d0b000e0002902c51000041d03813500a01110b002d420b0a10081c46a860000d0100c0c5d19880b650104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 323303938 1250 323302688 323302691
    0x80718020a030209091806100506040e15120f010e07060906050c0708240c09032116030905090604110301140111060403090f081507050a02190c0f1710 66
    0x80000c0342c42581168042e4000078030182c1c0c207080c09180900041d1000c0e12581140c425000400d5212000b003505100329000146090703c1d041c2405410119800040c00c00811401105d294044a50b14041e40510b01100300c00104201d00c0054103e80c00e4605c030a4200358150001c2074103020f1a40d0290a15055840038145a40c1e0f5100802846103400c4559014031740e58003c201c512141c3c01e0703c0722402c04400c0c1c40050440360685424041d207184e48030b10001d8503072540c41141007070802080d07a103100004805d080c81617410680103860480401c0251682100004e41001c1c05000c1072800c2000c0c940c01c01015141002031100001e010811803006014883c00341929250170b000d20b070310500e48540364265440541f5240d040c0f6140c050300c0c003041d074000da488404018401007800000001d00031130002c0c0b0240e050860741c5130f00307805039039542c807080c00d00d42103009110300c0301460510800049000b07481488500711240c5085032410000880d41c1003042a000041c5006031103c000140c02703404015a01c90 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 323305188 1250 323303938 323303947
    0x60905031615021804020a0216080d1d03070e060307030807060b1008040b060906060c0a0c050907020d05040e060d0f03080708091506060901020f0706050703020d0509100e060f04090b040608071802 86
    0x90627843c0c49000b404c0f6140b44148014007143d11800461300d1030a6030a144c541850f9aa0802880342c4800207001c00c0b1500365100410402c603110040c141660401e03005415900d03030750b4907615082441e900a41007600e00030303104c4c0a0701456003040f4145800d4200d0710302d0103588a09056403040303940c842c0640a54400d40c40c1101080f1240e071420202e640c2d070b00b1403c0880701d1142c0e07645440441d9800702e1196510446154000640250001c900090340400641e2030340c1c6000c0c142030a0505448026007481d400040740680c100010309500440b90725180a81c0f42e0005600d8403000c010a5000d000b0325444140d0003030b800c0502d8080c102040c05802800c02c4030b50760703110540c002c0101e10b40b04a0003450070030351080440016180e900301008085050080d401c1d03e8205010342801c0d6000c0c4500c081e01c5030070081c81086207180f10301c0b0344500b041030300004000a01d818a2400d17400800e4105030091841c4565500580d4070758a400d104040060191401405010b0300e40200513100300c14040c80d10503090340008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 323306438 1250 323305188 323305207
    0x20a0509070e1e0409050c1008040b070f0c140312011712250f03080a020a050f07030c050d1d0306100b07030e090408031906081906090503161502180402 67
    0x11401000c00f0080c00810001425042c42940c1c1c0c804089072030300450081b00302120607407054008500c2540c002c441050280c407082411901c42002c618420308004411400c1c0f0002810fa1001540ca20583d500454946504580407003017000c060f80207500325806400080c1150501107408500118144003142e00e5a03d0003100e888480c0382d02c6500d1900459120428040081c0d150100280a010b40d0301c031005a6100c450341d100700c1c454802c0c40000302c4c2003400580d820750300282c0180315042c460b28246543d0b0309030755102864003111000e580f0100f00351005003120140030380400d078101003040f4014007103400c141113514400980e50043d080796600010700c02c000c0c54000c541c11020307054080c00d04402032615081210040c2c20075074003a00000220101c080921560f802600142c1e007160002c0c0c5070305411802410025246400b084030342d15164000d440100e4814006031000e580c3c2c4079281103d1191501c0d2080c0e40300002c2e030030600c4107881400041c41184060498413203c9800380d0380140d4484820 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 323307688 1250 323306438 323306479
    0x50a0b070201020c040504050f0613030e041a0405271b010309020a080f0304052701061b1a06011106040507030602070c21020307170a0611040b0301080a020a0509070e 73
    0x40f60641d81060074982170204020700010f602794121b46140070340c0e22a440300710100c03084400b20100503002407880305503280d40b40b425a204e24001200001c5e40180440c0e11008601501c5044803004101c4544150804100344085108102e0b20b03180c002030700c8012030818240365095100503007281010381c2c90a00d01c0854958501c0a00a041c4050499111170380707400360306036607501c41d0080074040c2082c0e10204e421a00061140160008100c822414680c20b112084411496100400001c0240000030390007080d805800700441c40203000c0001070a14114001500d002d41520503484994406802c01000c5803000c604482640d03804a400b44e6100c08070b007070080c980b6082d82c100c450749100341004441201c10800042302190f20035004d0b103410b2503271030201c0c420960220504000030740000e5020000103019038452100707200d00d405000d081030b459000f00c840a82003604241c4850f4010035040044d03280c01042c0a00921080720000c0c501c1c17811900080c41c25843c0c1180701d01400d03415120060250303c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 323308938 1250 323307688 323307703
    0x102106050d060507090b0304051e0c0406060c0b010608010605030708060d02060f0307090503010204050604060e03070f0810060e070504031101030905031303170a17070201060302130e0d09050a0b07020102 89
    0x10700c036400c054500e0034400020201a43c0c0c810200741c8601000030b0300c05d407035815a803040343c000700500440c5030285041340d00e02040d03507012030190282e45070404581d40c4601c1303514090b00c8165122419021149003032802c513107040c0c00003418402d414004005135544902100e50010052502c40419150b40c800700b400200c140030f0080d4080c601158910442c801d0750041c5110b0031031f566404031225503400a2508038800c5004890300290100014405640201031b80000ea001c050216024283d449148442c800c1e465003004001c1e40004001c00e4011115004040140000c03802d0f0b02402c0c20b0215000d411881548401044200d4404544009038002d5000c2078035030385c100d010382e035603000040b41214130400380740002c481c100a50994086a50070880a0320291599612455031122000b02c20301d45c0c00740000c240104664072a04040f00503290101c012130382c000c00c004007140b82089448004d080c1400c001035a020003905400400c01ca0340d07001403401c115030b00300844c2641d91143d400101c0c1442c52 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 323310188 1250 323308938 323308949
    0xc070603111204170c0d050909060f1e0d06020c0705031c0207120302031306030501081e12090a1203020102030403030f050f04080a110102130906060c0809041e09030c030e102106 78
    0x1000e9406d10902d4014005000c0f03070b80204e0304220031f80e8034a010002d2441c90450b0700b940090b42c5001c4103203000011142c01d042d0080044c6100441d84441e41c2d00b4050341c1c441d141840440c0c1101c4010445428100001044652001d0705180d021492100081d503a02c002e20030007440e014007014180c103040c000e2040310310311000d9070400c04919807112800340241030203106000d0a88106030014903000c2199002c0300302d00301e01802400d070310808e550b4503030101c3e00807c05060340903c1540000a541c42400922804144250000340e1039280070704000c0d01300e881000b0b01601c1d13142000308101101159903281daa0080e4880764540c3c1320915641c0440e292210f200303140700030358030009614400303140121008040340c144503410302580741c88440c1200c00c000c41c032800910a000a004000e4203203070a80110216007003c1150040c0c1032500440030082c0e4000e0001500442c0684c0410b00601d6400200c2d40c01c0e040081c0c5041c00300080a000c02020b1902038103041c0c540780c001c054204d403440c045030000d400428 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 323311438 1250 323310188 323310193
    0x4080901031103040321020a091701020408030319050c07050d11010b040606020a0c0807061b050a0c1811032e0312090e07031b110703080c070603111204170c 69
    0x25051601510303101b000b901c404000340070f2200f0807068299600880f039000380b9035030b1203040c0380745040b01020050030004a401001c0d5028003002c290000700300091445011034501c1d0798688120a100300c0d0031281d000c0e03c040d0321403100300001e4020035400101c40c1120b040c00e1900c401e50072540c007000d0340107010752149103a2042c03e00c24000350266000880d080064010001040001e540d20101542c2c1c54091041e1004130b0110110200850542c044100c1424058029159140441e60711900d0116960300701c802c2c04d2400c8100c18030300420380d04c00c0b102c80b515101c80c1d091071030501c03040d80304641d1204074001c504140c0202112003140c0125204a0055601c18100c3c80840708460020386442058020402200e0b00301b000298400e00c40e00901200b007a0000e41e501c011314074400308a5120390b10042105552182820000025107900e00400361142140c0142c0011401c0c50001015154800009400d0380d0041c4200c40000c1076900703025800c55400381854800000e0b00c400001c0900510f0000749860 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 323312688 1250 323311438 323311441
    0x30c18141504050a090f120203040b033d0504090c0b120f160e0d03030b030a03021015030b060d0203070e04050106090b100207060e01020c0319062304080901031103 72
    0x44016904a0720741076012102800f503542d074240404200c0d01222000750652408072910404144c20048000321941d10b881501d00d00b640f54400d8040c182e0054503112070f441903070541b190402c60010000c5411214043c918140c03400041d007602c0c02280301d40102842199550700c0d20042040581e91030000b40a1181d8080e1100170010081018287c100c55410104030f0b07401c0095450356078541984031980c019100d81001544000c14010000300049003141072507038451508440d0307a401c20030000030911a50040070010003003c401030a5072a5178140002c100340001080c40001c07074041c862a0f1102c016030f2200035400c2103000117450050a03602200f40850a0024003041c0141908182c058840180782845061200024000280101070b41c82c4c0058000d0081801440d11803016201070000c1481200c0060302541e00207400c1864100c503500d910801214000100002c0d40502c04083d4107180039080d0003501500705240b02000103200802292000800500d980c0c040d40c4907080500003480301c10340741e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 323313938 1250 323312688 323312701
    0x9040f051506071502160b13210203090609010c0b190614061812030a030509010617072903090f0606041104140f120d110106030c1814 59
    0x200300036186074040da840403405004a0404904455916600a0300c24109491524025000390480e0100c4e42c59511018030203404282c840312010b0007048041c1d0356525803c2140f6007003010b020f803100380c1102c45c0d00d41c0c9a2000929004010b651071094240d901560f18500e5900403101d07100001001001e50300e0030000d0000b4409c4071000c5688003405d0100070002030351194419446c0e50071505520354030081c104090022808024100c24041c0c0c0041d00c0742e01c0500d08025546d00355041100740000003503840080103204c01c4240121001000003079480d210004202c1e00c0183c440003a802020711200822440c0101c154096500c04035160f441c13514180c507410315000b03040d213078109030444810320301c01c0b8408a0b10500e0030f44514094101c003108aa8982442d2503090b0f041045648405a88043c3c000d407000c02e69100d00c80480c1d460752002c805021048018000a070036100d68005107074070750303160800c1440010b9040390182c0a0399580180d0710707901003803a0b000702c002d064440350728000a090607003400203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 323315188 1250 323313938 323313941
    0xe0d020105061e0d0507061e020105060a030320061504140103030f08100e010306020a020c030601240c0215130f030b0a18120801090606050f071e0507030b060f061801030209040209040f 81
    0x104e12320700d4076190101c20f5200d03000ca00b0385000ba101d41d58080380d8901d0410009001e421082e03010036444440c2940c1c0b50802c18a1410508102c070340181c1d160780f0300c0201c240c2e841c1912900009541800324655154110b840051449508000c4481481b10b0100400e00c8045401c0c1901d00070101c003007440c2d0b0f841d0303101d280810280d000480a01c2c058403d2070b07409138492a001c6030f29416941c0c0385407003049205060344020500c400c1500e9403014803002d5405880507894441d1460707208200040345030b6484031480c0b45a55040419880074074441001c035000e00008500240380b5070803001d030102c04100350505910408542c2d40c0f00c140100300c81c03400311082c490190050941c034101d60b25075508002190f51014252054807030144081074000301001514000f480040c44001a141300030890300c0c10803802c0c2d8919203429076642098640f10200400c00103149000c043c0c0c40c80d040b0741510000d003051a40c0500350b940701003050010b41410b80220f017000407a203442e410b031112004000d0041c0161641c2003000380 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 323316438 1250 323315188 323315207
    0x60117040c09180b01150924030f020904021314061206040c091d0106080106140f0c0c0603010b1801050a0f080601020f0a060e070803040b032410030e0d020105061e0d050706 76
    0x7c00d0060320300141d079850040f04081e0f8040860020300d84440312103811002070850b0780c1300340f90080d401c0c048901d080c0c48910140c0f01480c100305118400d6810002290001401341500c0d40c4600390401c0884240c5415514582d04428180d0f00800c4080605605076040c14983e000448c5c0c080a2407441c04441003105100c0c2d0484241d1b403200c51079640c0b074640440314800c0b00d01c0c3c40840410f08004180403190800d0003002401701d40420750308030b202c550001071004d030310a034403072451000c0108006101c0b00008041e20b540c900242865850801200c901804545502c48103005004172880000c03001c1c2d0080c0030050039100d40c0d00595900001a2410000a2040792903400251294500c0480d4010002049074240d0380c0794542c0c40d01355036a15549000712a030a03540c411481c0c0300004d40c5400398175003040f11951220b040d280498807141803440c462901000302140270442e81060140316072030700c90110b0761134140d41002c4100510740749100131490400040ca0b0040071b82c86042000216103911040f0700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 323317688 1250 323316438 323316479
    0x321030403081b070f05010f0204030c091a010c0204050604091202032101080312070c12082a0906070302031b280c0512011506030203060117040c09180b01 68
    0x400c0b2902c0e80300010074a440810303503044071040d08200380b41c08a51403550a21120344140c00110f03d440b07441000b682660030030390003126003d006080602204640340901d03142c3c00034006210280042440000308070b101c40d0140070b4062999079002c00c04917141c9411100e40c082d00604940c40381501030b180295a0303030005803a810000b04842190030700e142c03482181412610500d00840c288095150440c010b054049d217944280220300a00c0c10005d40c07485072210042440707032500b44091914504403810204103e40750540b143d82c1280110755040960161041d0301c4050350030707680350000e52a00b82c0c03561140711803a40d04d0030400c00502980c028000f0300100007100885041075150308040001a0300e403510480200140410441809281441e0880c08200d00180002091269004c0c04030550044a5044840003030f0b000020030505580080c013450f4052056031980303c5500d06615040b00152003070140d401041d8444240c2c007008101e034000c601e40581c0200030200f81b03581d94030780e0010703100081c04e50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 323318938 1250 323317688 323317697
    0xf0f170d0606080105100305100806010306090b0105010302090a0605030709051e01030e0613060915020a020105160507050703080a0c1203141302010c1106040b0c070519030c030803060321030403 85
    0x2c240c0a00c200c40c102e040703503c09030110588607a000400d4020b48070082c18080080d810000c00982c044041100d42c1c006c500031803000500c503505060291a07203105802803418580100701000c0f09441f444070400440e4003c1ca0902d07203d485030242296200442c4e408982d00581401d00010011078122a2000452098a0800038002c0d09c0d081180c41d21000c40781328429075007043c5e40e8804500030390892001103104507502d8401034651103222040383c1001c080040103039502c900308504400405854080882c40d03043c0380c3d00f00f2020381c0c0e0b296a9000070380401444408003140748403106010b01c10030002c2d103500c007240d4045501864001401460000d900b001c01c070046401282400380800c0c0d46558803034041e512031329038121544440c200a500e55610707640102c81048001200e410038006440802070700005409214901020042510101d010300e54083c500100c04000049028010908480e80300d8000c80e100d40e00e80c400a400e1921003802c000001e950030000360605152031008504c594800c0e02c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 323320188 1250 323318938 323318951
    0x10c0201020d05010518040f020a15181a04260124060309120c1109090a110402031005010c170409060303080901110315030c0d08092404030f0f170d 65
    0x30000383c0300c0752080b801b15449109000c00d001c81c000c642c031400d503180050b014801450f5a1030f40d030348914016004640004580d0500c542c00c005045400c04020403048001c4100c031143c0307003c1d9604503c035511400c005495020410480540551100c90707071508150000c000800c642042c14010030313003150300c07042810422a000b0507401d02901c074140800e9004400d0003044600390a040c0e545200c0f10078113a8861001a071408040d55404214600c5000c0a901811600c840f80c60205400e1070b250415170b1147e8014003c010f091114800920b081b10030918100420803250b062401281c04035a0070484920b400140129072640240c101004403071180d55941950307030340c6110352400c075041144040007490302000865265000c0148072410504001c0540360615803000001d18844405001241d4441000c10030303684901c0c0041108040c5218403006900a004500341c3c03601512a500004003010031046a240501c0602c40a500c2c406a101500044044030246c0d0709070385410500d07101030308600b480c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 323321438 1250 323320188 323320199
    0xc0f080f1902011a1219050d02190803131509051e151b0c010603061407110d0c060204031a0405010b04020c0a0f050c060304060e15060108041b0503010c0201020d0501 73
    0x4581100220f140b01d038050084841030810601d401003c298205d103115580c51417100003519446982040e100d68018600c03039520f1072001e420300720403448a07821801c458442070b01207451a01100d80c881001e4030302c020245170038601004080401e0f0414818285025106010040c0020754980c00910000e00c02040404446c0c5265070303040318906c40c56004076441c010400d800c03160b1100060026619681d1404d281092409900f1201c0715071040e98590784400c08003010410071a58203030007080070310381001a414030740d00684c0c2e51400c4941c100e003004074282081003403001650645000c2d581c070004030b05045103040c1801c1e414040a0718182d4035940f924052081c13030314107132080760680c440182c013401c120021a12078030b0141303910303401c25140e0b80940c0c01410b800da40c612009521882c80b40ba80001d1014003816018034040548801801d00144001071120350703030b08840800e03880b40d0700000030300340c0090701910050781074255070266425608100900c1c12298064028021005241d2002c01c2641c0c0e891 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 323322688 1250 323321438 323321441
    0x90604050105250e040e030a031b080c03040f050a0b0a05062e0809070305070b03010e0c0403150b041b0c050f0607090302060f070206040b0d150e070c0f080f190201 72
    0x11001d0820826081030750080c0b03c1e0058680e141d010070024800504040204200c07420b690204035444002683ea42422070360310003170304200892400741c0ca08032015240100b42d07031b0041e12000d00082e01050300b02c1500c40400a04101503091541d00084c0f1500c10700300103007250b020300415034185201b103c006543c4007030fa03200c082401c0e00d02500070300070396001449407000369001d885c094640d074050300a01d600031001c200304002840c000d00e001d4081c10759035850034460825400300600034003100d4904010410124950a100e01e480c1101c20500007078003c0400b00180081081403441d004c0c1500e0850410340880d00003034280da00e5401031054480c12818004643d0321108229401004603400900030f00150925401504070701b8400d4030050700d00350320f40e000604240c0069020b804d035a04002900303103054089000e40d0fa18810a005180070b590304150224440c00001000c102c02c2242490501f800c1c80b54400368922032a4212948030743d940030b0405081e44c258410200d41200c042103034800e044c0c65105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 323323938 1250 323322688 323322721
    0x2011b0606141003090c12020a09090b090609030a1e030e010905030c0f061b0a020a0b090d0e010e030d08060607080c010c08010e1005010c0311100603060609060303090509100b03090604050105 84
    0x3001a06c0001800e00c031100e521940132000c1030b41c00003410000881d0b0782080e0712980d80401d004103104182450142d051034504880102607000c560418400031901d240c005074401c81742481950000c800d081e640f24200c00415000d240300d0002e60030091103400f030005c040000d1100006007002d445000403546030003969540c0c2920800340400ca4901c0481920300305501400c240d206d00c2c03042c1c0d044600d0795202c10081280646d10481c0395049031101410741e0382c0209100700c1101d02800c002811038001070009842da892100c240b0b00b4000c00e80005032040e660f07201211074403948407070700c6600c0e1104070512078001c1030b040c0b10920205480a001080020008011f98030401060740b140600a040000445425103582c0044090005407150501c011005020941c1494040c0300001806840c5013803100c2582d42d181d0080c000c880c81e02c0824004a0f6224050005484080d128a4100d840c5d044502150042961091403100008001d000301560040b4006014a000c2c10080c4030301d071100c0950f01040100d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 323325188 1250 323323938 323323943
    0x70b150a05090118091b0602150408030f0402011e1205090f120702030114010e070f05131a040f0b070c09140a090302010b0306010909061805030702011b060614100309 73
    0x40c0c0b400402890705441c0c28000c0a0100e0440465594020b68500c10001941c022009055103100d01c2480300a41c101720401580c0403a201100c254145622005020700c00505500c40f401c80c010001002d6900440e46050b00c050b11225806520804010061840d03800d81030840e121030510011810710345000440d071007606018009401400965040c036041e0340d00c402422030305952075005514003102030203030b03840c003c3c0204451040903203004280100840c2060034100c050007824040003540f103800443c4581950310748180100b00e914a030308520300500480d408500f01e030340c9014020844201000140205c03d120b00c1da10001651540c29240c282d8800c0707003a05030410794113030001d0400034807600301414141c001d00002078500440c10119041c88001d82003145a1500e40e1588010420b0381d11420780303804e910043c00f80c00e4140c1a60780a88a00c120703000a41040210000d10b08521010f5640c0f1001d00c1d07201d0006c104143c0d5903044001c07d40107403240c3c04d00c12064242c1198001d8064002c03a100720b075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 323326438 1250 323325188 323325199
    0x130c20032203112b0b150d05070501140c030a050918090d050d0b0d1101230406030504051f0c030b0616020411090402030a0504051e06010b160503070b150a05 69
    0x4114006010200c4c0ca440303c500600051182d44852181c0500f0720031040c180106a510020314104c5060010303400c00341030540c041c40118802402080b80801c111094420074607014200108109402e8214003640302880d0680c000003e8084079181c201005103c4c80d04181c4003000b0075804001005061141100c41064680008411114281c800d10040802c201c54002c00a403034500140850310500c1106030031104651202e52644266800030400d400c40211841030b000b0249141c0e42c003490358000e52152006050710b8002080422406100c1020a401e440b00c6010761000c0c00203141020b401d940552202007840e00504080a0510b00101d8400510204648401032040e074240402050840d5110001600900007a00d80390b6a40c0021350095030114804507035800c181c1009802c002421105918241c1490007010042101251980c112120385c24141c3e1148520902400000380703580e0001e01a000014110041281c28443c9901036182c0c40300e5201500035460a000e08010540649a40700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 323327688 1250 323326438 323326463
    0xe160f1b02040204080d02011d1b1318030215010902040e060d1115070c0f151d09040b100506040803090d0507051504090509010506130c20032203 64
    0x182018400040311070310103080145010741c1c4921040c20001c0c1c0515a6006075128141449485140d05c03265030a0703040c1c08003904c244504500c1e2074480710003a070070b0203002d17421520003400301c2c145c1e5510652449440c0f40d0403c11319505490002c0d240e0540300707035190044441d98004650980a4070030303a4282c4240c4040301032140c1718101000700c814688801100d05403086400100c0a440354480c41c4010700803883c0d00707501c48120b494403140f291400d80003030703401541d02d2404000d0445500d1001c448031160b130420040c0003501d522408011440b2468564101403820107200030420105046441038910a40d11408141c42d81c081204500c254483c1d0101035005000c1c9145134030700384d0f074015030303e500c0b0707008840e046030f03075600810800d40c01c01030182035a80c00424100520310441c0107942e0f01244001c009c0085291080000382c06084400c05d50616a07a06e5081c00005405104c03000c045102e0b10050b55000e81c60311108603034070303817080c030352820485004501c01c03000076460591101941e0b880040ca0041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 323328938 1250 323327688 323327717
    0x110c090c0304170a0f020c0607020109060507260702010305070309170a02070f031211210702040b090f0106030c110a1b090e0d0801120213020f070803010e160f 70
    0x55400180c0b060340c590504030500500c41d000000280b032507210648408845104200b0042e08058100c10443c1c003400c81004034400503a400a07217241a14a0790400c55222181402d211902001d00340c0b540403a10039034524024400d81c0306c800f0703040d218800d80e4180241d9072a50404c6094840e2942c0c028904c00c540030902d5000b8100001038500111a0300c1100d104558035400046400300b1a482a1a09246041140702041c2e00c0b030308111117143d01038001d18181204040288031043c2d0001450021180401c00030300b1591181c00c00f08006800512109080c10f121170302100c510001e10030180481d18107001c003161039010b0107141c00600c001d0000b40c400305840780c541a4650905094003a40e201f407241022500210510544801c00e64650003802d10301d40c445409059144180c2107143c551940c201c0e4840140c7c0d4403078101c2e02c102d40b00f610158036031514004c074020500031030350001d00780340020001103000c080d0110310b40d20a441c00300041d880c00003900800c5c4c2c0c1403402c0700740100000d405461075100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 323330188 1250 323328938 323328961
    0x6061302070b2e0b03010e1f051908031201150201090b0406020a030e0a050102040e060906100e06040b2d130303030b0a0902180901060e01020309090c0408030c030406110c09 76
    0x80d02080510f19403449420030805420340c1e003290080d4440140220050200000d07510403281c0c480e900194050410114000c0210351022500c00c00c0d1040c2c080100b0710300301e25010340d0344800400c49001101c4d00c4007001542c40a40c2c1c00c09000d8088a240524900a0581d1050083c4c58195800041c5080b4680b20350b1180b5000e0f6100043c14810305889400030f45803d4010080c00c0e90150003407000686a90400c03199044510014080074403e0941c0e00a03c0780039a00c203a988030190700607040551107100701c0d0002c251207000750390101842d0140491008084603903000d10280401450180341211100581101501d0080c100000c2c0d061144903400e0002074061b82c02061140da00422805059036103454950990740021991000e00c80362103140d00840c1041800c00c0d000d8025402d00307121522054000035034a000e000c1e02c162107409e1540c0412540300041d01298080e001c04025a90f4942500d2000c6591358405d1150000089000544404a04011030880c0740e1701d200500511040d1901c0c820b005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 323331438 1250 323330188 323330221
    0x20c040501060c030e0607050a08120115050a03050a0e060c040504060e070c0b13020913120206040201051c1b08041b08060106080c0c0f07140301090b07050715090506061302070b 78
    0x390001b504200c003002042c0c0c1004141c03071191240107202e80c2e400108480100351803043c1c5c40500600403071030300342940305d400030143c4d40c0050003842d00003410f940303000b4400050980b4614080e600e000b601c0501030302c90720040007003080c0c0e40191070500c00c42e0707940d004848a14004944020008491791880c000086002030b10a0b0082041c00c40c0802c40d11082d0001041d8103001d0380c019500207241648035007003009010100d40280e50a00190200d4502500041e03d83d00c0f860b44140d481440c0000103d10489555120740440240d102e0201c0c050a00608060700c60402514265060680e00d1000c1e00c0290940700d210040c0c40c40d0f84090304484c0d103003000a403074060010301940c140903405d00000e80c0c20710041181c40001100c6d140101081c1d072038041c4141064020224650203079060000000c04601c4e8040103d410003140e06e40180d0701c103500d0a003070340407007034a40e003480d41c007420302c5110340501c074000a0a038022003040341d041e40c1768801c0460340c03801c92182c014000d050a040f140014a40c4e04a260100d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 323332688 1250 323331438 323331467
    0x70303050702270115080f070503091e031b0d0507060f29010306060c0503120408070209041a10060c030810091107060b01020304050109140a090c0f020c040501060c03 73
    0x182c00300b032810007049000f4000380c3c2d890100c01590b803004100420703114411001e907102d241028009418040c43c130f0201f45030000c0c40c0704140039001000c00c5444a040044c00308920100e52a80c10403e0329080150b180c0d402000b086100d00ca55550781701d412540425041140c01140d161a032801d096079545402400c0e50790344c0c00c2c10703a590f11a90b00c014600015146031500c2c1c01002a40000c02c41c8000140845216400c441c0400480c0001c000020340d000007142c0003002803000200c5603545034980700c4894030400304000d401c908030b10107000410107107010248401350f07070b01e2005005c1c0da02c28007a524825154800c0c41d001070640071590021900808408d900016051144d2321081e444026590035501101100100744500203418818410340d4030448114080c244080c510309850000003d002074914014100360310440d400e80c50040d6503101200004003000391042c00380211415000c4c1c00211000c9003e009070151a146440360710b03252040314143c411503103501408080c151021218a003202503003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 323333938 1250 323332688 323332699
    0x20d050a08070302040b030109091403040b070f060605040c050301030501200d050a0b060a090302010e06040e0103140a0605040609050d080106080106030e0106080a050a020109080c03060103020f01030f1a040e060108070303050702 100
    0x6c0f520303004450045000e0640b508001c10700038180e00d0302c61078200940c0181c60194000340800d10510b01110100c883e001c2c0c0000c50b4050900c414240341d00249040c1d03101da03510900e083d8540c1c4c08190000d0145040300c0c0140002c02031800390305502d05411024982c0282c0030070041107000e8480d221035014036040340c270400001030b222010b000410110362140c68050046040031070108119a07202c043c40d2042d09095a4141c201450304a081e00b80c80c406020081c40001f10107070326103105408114405003640c01c00b000f4807007401c02e4102440100149241503d042c059003c030132440c40d0082074814101c4000799120003060b0f1074000100c00604176950110019501c0310310020311030340d003001640140390055010b010040302d90f2002410316141c0e5407003826160800646800d840c2da0100301103045030780560385420010001801240103060390301c124a12140703061100c02001e000c220300402e02560a4608010304c00800301005d540e58000d20403106140c0c003410050000178403c0e0064903d6a202609 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 323335188 1250 323333938 323333947
    0x610050d08210901150909081204020607082101060503060f011803080d0204080106120c030809040e1f0b0109030f02100504150509010207050a060203090915060403080c0d020d050a08070302 83
    0x50345420700b0010f5030080a03a070345a442d0f194032890707001550802451420300030010940c0c2a61146802d002d0b080619a0701d078500c10000c3c1c15911072504844000342d00031050b960b19041030003e80068100020070035400440f81d0b001180e0240038408032030203010000e080d0080c1c503401400440720029495800c2d50001c0d180c40001000400c60382c09042486900d030ba02603155414541d800c2d085618035446480c030f00c045201c030180891a02800701c4e06407604481c0c444d5444032080d0201c7c000e03040f5a051440c4910568056000c1600c01649146600b0701c1d884007400070250f083c00440d8442030902000c1c1922060310300c10380051410b0b036807503494002507042c000e04040d0f8032060301c401c032405001004080f64001524400541e070600c4840c0c003400c811111030b003086040c40740c021350764041d00310b215005460103804601c40c48225511a070311050000c0646a0340c503180c0c540f4021682100781c0c034104512840f92601d42d42030010600b103200c0e5a05683c1c05003008601c4404980785007000d0191800d01d5070030030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 323336438 1250 323335188 323335237
    0x90606030f050f0a0c020c21060907050114090312040e0f010605090a050108040f0506010e040c0b04031e060e10090303060f08060c0f0705070e0f100b0d0b060d090f050610050d08 78
    0x10104451b10406d203142c0124076810288ea40c10280000c01040c4240c20003032042c800b5a0b002500703000020f4814400c135403039500f821b0110f441c1c004030071540d086622002c500003c0c40640d07011000d200b119035458100c100c0e641e9080c182c800340620041c90b40d03c40c21100b030074091540300303d80045d0b005001e460602c03c42e41a948409003010800e80091706088000c004220600c0f6640035200024101c0d4480149030500e15100e44c91880b160a0b00080107811000d0040c042c40483e4110400d0080c290003900c403401b80c182031280c01049200c000b00c0c080b904001000030714403c100802c03800c4440481c00f80c04a0741c1e40b9914003580d5841440c44405030101030180e8400724a040001c0c8003c1c02ca0401c082c038050400703450840f00d40c4d600400d03844d41e5a00303801043c06640c0c007003820755041c90680ea5010514422202c0001c906001d040c07807800c0c215140024001c2404041d04800c4400d501500c01d0f41c240d51660b040c003071340d400581d000d160340161888003000700082c3d190f001820980000d030295101e00d01d001c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 323337688 1250 323336438 323336449
    0x118150908070c1203080c071a070e090c04090e150105040c0c080f0301260a0210020f01050f1e100b09040b040f0c0201050709050d0f05010204050a090606030f050f0a0c020c 76
    0x6800407007020040341c94034130401d600940340319000700c50b40f600c0604100700c6a64803440050640f41040b440003001010071000c03406100f0036528a0302c0200019210704d40195500c4050300184502040141880d00c5441d6100c2e01107410601e210001c9071010f0b0681c20042804007420801c0c4004041020404d454804100705c4070251850980c4908510303034a5240484040d048109022030301c42069100c0000c0340f000200003044050203606135914546540e06082c10780c24681e0040070b405444d420702d01080999a10006454854801d450003074611014420301034025400c1224980c211001a290601080e00b80c44054407003880700600108406203a140864203480705030040709006a2100d42000c11140c084c0100741c1d01a615103000b0003524502000100d8115080601800c00a000030004090160a40403079000e045c0c00f504070b2112940d00c68809000700310510135030000a20349954158100300b280907980c040c94540b86101029141c9044e000c00415404030813005500c241d00701101c058403034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 323338938 1250 323337688 323337713
    0x3506060f0406080106030b01031107030f0201110406180e04050607140d0f0b040b1e0103052d0912040b0a1d03071e05030105013b0117011815090807 65
    0x42d036440d038500b5450600081c0c25100c0500f83d003410b05040102419851004000340d0355501d07003600d080e480c84c82c1c4410040e4010711181810006a50b00001c02051144c2c100c0144100109000701e607400e8540d486c07200d000c07110320075140240241c11140c08034109074410031450040c1030170034141070315000310046c1600458501406000c402c80d02d9060700340c450f00d01840381c14a510010394986601514400e034410100541c01d51480c14940d4400225044864103280144607550740c4400401c84549102086948481103951483d544180b80051722a40c102c0e505541c1260300e06881c0078140138248500703840003402c4800d0f00020540001c0c000ba0755170303401c00a010040c82d5100002e10000400c1000302c208200b030381c000c54001ea0604004000c1080c28502c0d2501501e00d00d100480c850000c103940500070045003604104060044c4008180c040049800741d00d000000002005020303840014020584070409000c0d0074500c00f050300e40c508481942161407050300c0f8254261030016903a0b52003141c20781 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 323340188 1250 323338938 323338949
    0xb0c1c05041214100905030415180b030610031a01120f050f060415050f010318050a050618010b01171801020c0706020607050f0f0702220c3506060f04 66
    0x64910a000c001074040c410720113200c54403981480680b015480f0582d8910861141d10340c0c0044003200d5410640c41901600e001400380d02002d4001ca5842c072003620103400c00d035801c40c8905d405480441c84940203101d0080b8005500d0380a28001c041800151a0705c00300e2070340f88200c20781f254841c9e500d80141d8490203210b84880c003440c1c0c000d8140711042c481203e00a0310f45070010b826650090000340d803018040c011100702441c02140d10140194a80700e0f40707402c0031005009104094058040100100760f0511038101c4540d1903d00641da6207940303090303410000c210b9000c280d00002005c00380400780e216690003410300442005d1a100c9800305403ca80c810300d0345d0651500502c1041c001e0345c2d414000f16800060a16100d410b10304003100c40440e903c100c1c26903080420b0f00141e01c07000c6449030008003000b405240d02a6040049160340580a04a2000c1c43d10000d01a00006800124440030840044e07843c1100079030200560380b100c0c41308030710240590350700c80c10a1040c10080184200200302400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 323341438 1250 323340188 323340203
    0x10c02090906090c0a08070504020d0b030f0601030201140412060b061b0304090c050a050409020715020d1a0306091f06120309080705030304031205030601180803130b0c1c050412 78
    0x703041941203060881344150248500010401044241400036424003580c074100d400598410001e6110001004040001d581601440203000b441500c04541281200d000b84c94401005014400200e024070542c02550550302040300140042440f0740d205078403030b11b0b02601e82843c01080322400d41540c1c0789056042050f0b4400501402208003500483e0315440441c1082414441da8500c081c12500440c0110312026a002c2040000d0006c204202044000c114004540d22001250070a015201d0300c080d0030990070803070b0300c0e10303078903080000b8140d00c40c41d49030b00a00301101a0b0301400344000e000c114608000d5031522400301e5502061400403200910948800004524100485042c03030010752040c0c0c400c2d0014081080802c1019001000d01446072030b0842d580d5460100582d10034000c10002e60859405090205202400200070b08010700c44003400c1d10155a1303844010141c1c85940394a01c40b5401000664442d1036000c07111269030003a0742031060511b0788a21507644000c09005c000d55150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 323342688 1250 323341438 323341441
    0x1051e0304030e0a1202030f0a020a0b16080d0e01201c09061b02070801050c0906030702150106050c150c09040507090306051005090c130303120b0406030b221709010c02090906 77
    0x501d030801129223607031110350240111441a4001580414441c427032010345100010713580b04044084201000020380c4070b83e0007621408042d400c10010105c0030343d4080290302c0e00751a11010200800f14848000c42e507151246059014a103150b040300200c6003000d21592075016141c0000c0700f601903465640e00c030b0340c8542111400700e080207140c04140d0748020403030703450300c03061014071031310306003290380d0b828056412941e00d03200e1006c100d191028582061541521380e0300041081607012004020100c055030807505101c103c0c00c3c90180c0004192079400201004000d175000c181080c1d0006a400038607820076071140c560b80c2c0c50395015179204032028042815020418803031480c11800c569080991010a01e090583c0a203000d5200500c1d03000c041d080c4600f00e012510b20555580040e1080440500207101065491403c1c18022f8020ba175550f5000c40e6110301050801c0e0200003130800c590700300359a41c1035a4284004041540d21502c4010304020240b060a8096120038205600490a0030000e0085 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 323343938 1250 323342688 323342693
    0xc060c07020a0b040e0f04020f180a05011710090507181e0c0509040e1f09050c0603130803040f060203090c01080603011a1e15040e0601051e0304030e0a12 68
    0x1181d40b0307070041e004211081c40103000354012410565804146008400d49544a500019074511410084284c0c40740400c12401400c101400702c0b6070084890810500843c1d0700c910000781d04a00c90014a181c1c1da010b400b403642804000d800240300c050058040c2c48486480e0400e02c51001840004044d0880c2c5070392554081c09244024800e604001e02030401c04055400f500030a14410128242e100d15107615020003c40c40c24049138000c02440e121401e58450b0121075100a480b018200740c17094007900499000b1402d00034110b030310950a803003450704040019501c121035600082c106482d449400540b500c0000c2980c4000d6004d42c0381000141421131508000404140d4010007032802641401c0712000e50385854510f079803040c482111030b002c9184001e9108100030b1640e001d120f50040c16100000121301480d0010019529050910704c2c4a40d50500151814400c15104800010144d1950300c4400100d00186400c00e109243c41d01c00c2812550010300c4000d03503608490345d20002421903c04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 323345188 1250 323343938 323343949
    0x251a07050c06070c0b0904110a0c06060f03030905062206090503010b03150606090d050610150207080706030c0509040c09081005040206040302040905030c061e0609100504020f0c060c0702 82
    0x7054104560240c0b80039500c0d562040070701c4880c400e00002d01000300b5000141c2e6900d40043c25420312856030f07540c58005850300109501010042550358a103004004241420601c01c1c40c010b80e034240d107840d080c0720701d403c042c0f018690042e07401028501d00c407a2815810356400d03640348000c1002d44c0e2240031a034100300070142180e110482c594071992203040b29015000c0c0a520b41350744000100c440305d440e0004500410600022aa0700074294007440040001080040c4411002d4a0800c00766042062028209aa54200c140503950f020780c08400d0030810f00e440303500a000c112082e40f0301b20781812900404503058841090104010031401d07007041c040c05204020413051a244000144000c0c2080d40110750720748210301019010f00d8460f1107103001d00c41d08108032507c503c1e800c07084558a207400703940280d1171540c0e80192990300544030007099152500e044504c0c003c44441141040403440c00f01040002d501c0101c0004440e40280200c0d283e803e000d000041c440c2d040400c842d0b90b6420036104101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 323346438 1250 323345188 323345203
    0xb0403030f1706040c091a0c0d11060c1e0c06010e09030a1d010302040e0103050604050d081e06270f0c19080c070b04060b030d050309251a0705 63
    0x3030800440b04072080c488031a61180b00d800a100b035a000a1008010400f103500c034070a50440070403110788031510000004550010154088454207540c0b0313400d10f54100300c81d44100064401c0d003036409080440d514004100c000d212080b140100b0a0010000c440100342d25000b000910769103411810042219414603841c00d94001fa00381c002e14035103442608068200510b86580700d48800030905411001d9000341c1c1100c0251048958090740c130b69484c5400c6658407400c9804075601d00600700313528221401380c00c101380581d52082c0d00580d041c00a8100e0364402c00010035895006c12038500280a01003400c91045a05c00600200c1c1d0b084d113080d19105405010141541c00c40000400a8604030304140713058181035001d0f0300d00241c0399121501c0b8000f0a00807203030041c100311488000e00003081520340c00515801d0091b000d0740c1c0441002c038010740e65404126503401c025041941d81142c031804a44202c0f226001c240210006540c40d0700c03009030364000501c1da412619000041c02028000104900c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 323347688 1250 323346438 323346467
    0x1e0c03061a0309072103030f050601120513151d0d020d27090902030c01080411010c020616260a020d03180b070807030b0415030b060102160b040303 65
    0x3840024030301824421503403010300180301c100002001207224000c0502c4100001c0040d40c0404042c800c2d0100546814100c29008a022901e85901c9464400b0280100b904c80e41c0140c5800c140004104000800f41800804102d42303e16143c440200141554106042240d901200041c0c4012140f002560680f041c41c0070404034bc1c0400e040d191510740c00034603031541c03426500e84007003801980380120040b15200000d039409042c0410004c52022000c0d4000c51000d03008408503080200c00c5401921401419507002e40141003514042c00300d035000d0f18603000104d1019010320316000c02a000300307105501e00f61041360300c00321184260240b260f42e5044023480c04000351070035141c8900c0300c0019503951049881c80040c1510f034030b00100c03100c0144240701e6103d500a41005007524003a038008261110484004000c41d2030420a2195414140b05e03120402d00900c00303400d511429500c5004d0304010081881e4110320426140b02c3c40c0c0c0d40803d9400008003e04401261201d046160140040f405036160 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 323348938 1250 323347688 323347691
    0x130204030b040f1b41191d07140c070e131a0711121e13181b2106090c080406110406021b131e0c03 44
    0x5001054282000c0742c0c10070b0340404441c1d000c3e0200d142c110b40202d14140b0180c040700c1003c1d40040c00c1c0c10a04070500c500840d50300744400d8000502c0d4618802001c5400d42c1e8446650082c22000a051201440000c1ca01902680301007580e00e50340c080104402000c00c29003040c8100510440340d4001030101c4003901d0060485041c01c2c0207000607036444ca841d102f200d01118450000c6400204203401e030684541c2c000d02c0901c90499070b105400d10005003503030b048001440c50043c40741e21200114928840c0e013896240c180c40d21000007209020f40500310401402008100420150403100406035002002d003a008156400041c0d20714104a82581c5061030f44003092050008000c2e03842200d80c01030070081080d0328494021440490001d0a80e9003041e40c40e0780c03421001074611790308610940d02c6680306036010f04c600420322440d08003501440c070441001d07a002540c801850001c400c0742e070211310301c0034004d0600a81d0f82c40c154000c1e1142071000900000c031080245051a0060080c160300c40d810b03080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 323350188 1250 323348938 323348947
    0xc0f030102040e0c09010c061a030c01080c07080f0d0e1506060301050d03080a0908040816080312010509070c0b0406020304021206070509010509010e120624010903080a02010f0c0e1302 81
    0x126011103c400500c1c3c00c25031000040c2070100b9078081ca14081d603058024100300308150000c507641c40b210551002d603502c244268441c1c4805988181c0d0524410000d001c1d0403401c0881070740d101c2c903840c0c214000d01203c100d8107000e20a0f25400a00c5400d42400c9004010040c2c44400c4204803500c58000d046a8002c610400040c0b08949602e602c154a096052418041654550420400510101e0802051803000040004040100241461459000c0710201003110354640d400c580d248640301c4070310300d44032850004003c030340f5107242c40d10f900540a0400c1510304440344c2c0c88070a20002103e0803284a940442404194188071228191040c0e110000384031a050024014145010f9000001d0400000103195101d0b64815130000750510409402c40700c0241741320580c07549544084601a40342006803009000e0811301c05040d9050310300684a010020b03065032208810340e407000100c10195903c480308080708a08911510341075602d10756400384000640e008101211481507407d6001500600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 323351438 1250 323350188 323350199
    0x50a0320070b1b090906130504050f0712020901050103050c070501020f0d0506030d080f1f030f03110d230f13030501060501020304080705090a141603150806060907200c0f03010204 79
    0x2d041310708000c1c1c1268800702d65074502c030005050420245942040500305000d1008000b000038044040006c4c41d4250313481191035a4190724480c81c5901c01079880050b11004004c2c42d40a50f20054010080c0346603d46001d031582c41d414266805050000006c4000190031680c0350755600c039880d00180e048000e0200451001002000010050003018401342c1127000301d00b0340462071a1044500307400d642c1650415503642442d024201512600b6000304948004503440002c01282c441407004080d15035005040041c80700e0310740380e5800c1a55100c00402000342070742078500345c2c015042c0722150b0130260004904505e041c90075a40160f1242c4d0540d40240014040f10101060080c03d8440640b40c0c0d0302a5a038000101021f085011204100c0c079449105000061010402e150902581600c05004820043d13402400c40a8507200785011a0803d82c0462070750301c9c1031b820a42c1c01c44010301d44062144036014174040e03070b000c81900010701356001c0c0743c4088041c00c100c07210032014602180214100b52804 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 323352688 1250 323351438 323351491
    0xc080106020d140c0d092907030e01210903020c121f060902040303091d0403080601080a0b0a060c03090e0f060d0f0602030112111e01050a0320070b 65
    0x14000342d0610010400490450011800f038620b958410421141c07174002c9980040d1102c49603001d2007100c1c078510f000c06a1060100905940e102021800c040d142000380d850450b06400d080c40140d04006411121001204000e00d60040100300000f0006064070305107000703803409114040250145ca4440007051b44481c0c0803a03204045030840e881c3c2443c5e5aa8103907140c008001a070401071900b4030104d00031082c16401560720701a12080c410342009030580715260200a0b0302120000c000901240000391a5445404101d8110407500c40c04186980c060002607c10011504041c0c0010442c02c020400d041c0d00445040040400c12641040c50a21302c07661044800001c005d9030007190000a00410020710721702d940d040030381041301191656103c3c3c14141e40580f140406617080b20644101c9502c0d4501440030901405500368803410504031a4015103494020207965024940c3e11240240700e0550703a12408205c50140c82c202c1d0ba00c156a28040c42ca20b88060320859044030b001000d02c1da0716501c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 323353938 1250 323352688 323352703
    0x90f020301151d0f0609090708010e150604030f0201180b0a0e0109030b070e010221030103060c0305060901090e190501270308073b0a09090b04060b03010b0d050f010c08010602 77
    0x68500b144046045030211300d15100e0203d2150300804480c08116408e507009030218143d5840340c210620580300d81c582c1c14070003401d0141081c1c2c0b2000402080000600380da07050515148181800722060047c0300700c020685419a020803044000043c194000c0c0781c1c810034100c4190801d0806002d07003411030b19401d42d506001803000c0c0612051601301e58280c2e00802c6a1501034040d401880c500d01c4460f106035006820030b00c822110103080031070501e099806405100d120700800381c0b22660b0743e0310f00000c0d60090125040080790b1070040084400708145a0399020f2003c0c0d0041002040403240d5801c0d007030405c104a0700316620058103500710310000ea4000c0400d9000707142841c11003a0320740702d00c407400c1c1282071256100c400c900d1440c4200050011011804e8002e40b4104d900300c400a50740e203101d078150382c61420002c0c84003480390300042c0006d04075401030001100c0503000060f9a00e054011514070122044203031030590049060b030504e840c0901400d014000140752a016075450503c0c0030b9951101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 323355188 1250 323353938 323353997
    0x90c06141b03070b070201061508090c040c0e0301092d0209070c08090a0315060605090310020708070803010608150103091208252001180b040606090f02030115 70
    0x4800c80c20003019502003042c1c4000c0f41e00000401c085080150b00603000f09454421603009550700d051102020703000b18801c51195000c00c02820020050108004c0141050f14140b014055984009001070700c00348501e0750624070500020704490032440d200d00703508001d1448403010070820f003c0d001c0107883d010320040e04003429083c450072751036440c60850441d0040440d002d410801c3c542001050001c01d10106e039000b03800440810605803a40b074100d1341442560035464050f840311465a0041c0e0855004141d828080e82090b03041061994803039196078020307409500000c100c182880213a0000303550a121401d002d0074101301e010b815694820300501038103a00e1051200303a6000644e2013003601d602583c4d010400780c1d903440c2ea4495103000360014841240408000105000f10140355a05201d4035000003080500c801c070815031643d504c0c040f03420041003125920749a410000d501d03000c034002c440c00313030b8402480561a98105013000844401441440e01041070314080844414190301c8054031252 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 323356438 1250 323355188 323355217
    0x6010801060503031e220306050a060608060f04150602010501050307090c0206220b040516140303030406051e0a02190302070201080619030209151203070305030a1802060706090c0614 80
    0xe45e14450720700603004440c0001303c0380d000407890840111403c01d512050f20300c039840030001910740304100c5044401c40c0c025200032600c141e0210750103180c8004052030b209401400407805d59080c83d40c1500a400301d90088000d0707034490005100b01e29042c401840a05201c03c4204100500c2c1d1000940c2c822010b0440c1c0c82a42d04050301d014014001000c104503180c00c070316090b94500381132800780d503200d01110485424450100c008103448140800c10035a10fa4020011401c0d601c96407510001000041e1012624804603a650300c1c140d1400c1e40070340e1003140c10400050303d5050304024808074459600c020030805104019441c0103030b81020040760025801c4d04d40c1040c84564407141c4104040503040030398820800401c1086200011981d0b845240041d1000080044e08012850341d238050803100070007180080c00003520307102481e480810042841201e58024402a80109006a004840c262002c60721034800000f481140401c850003800d40e40b9004400d9051030901001e60301903010316181d4038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 323357688 1250 323356438 323356477
    0x8070905061e0c2107020102060103140c0307081f05010620010b030a080705100603030815031603030c03140405031b0607060e030409050a090c090c020a12030e0601080106050303 78
    0x42c144100124803101802c1c0003542c0d40c1d2003030041a0f59050f10f00102c50b40003e104095480a4603403c05443c40c81d6410780040400e40d003140c0e500064020707412a00a114440d455080080e40c0d01040014001d0080c0809040d050740000c00389151900c1d02d40c4418102414100100101039001c40c0e058080501402a070308c81c0c400003c8024054134113075120300e5040c8a60003055084c00440001400d2180c410011074559550700c00f9408280c404c28031002d004030b515403001a45800c611a141d4420400007826188c40c965640c0e0303c0e190510f101d42060300007170340c440e15000c10160400c070f020700302d40c0080d154541410301c2d020010b5034501d80640c0011250448021000158a64206480c400c56200100b4007444008407107071a40c0707401c070b48034030b02c1e00740e00b003d02040d14044188102c10f5010703004400c2070846420020180003601c94070200e00c08500c40c0c946000c01091403440700d41c0401c0c52503a400b14421000c9200e00b0f1070b011068004003000d91602408200e680e8001080307411034900d074640300102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 323358938 1250 323357688 323357707
    0x1050a21140c040504151535070210060503060711031207020f1605061b0a120e01090605190f091503140106080420060d0f0b100807090506 61
    0x162042508010780103210809202d00814208040e10039103505482c200108101c0c5120007113014294440d290301c00c02c0104500d41d0440c031070000070006061b0790518104580780c11a40a001c3c030245100143d10079100c2d014850a954180080000e40d55500824071200c0e043c5400a6102c100151004003880814180c021030355600b8425242d200304840480702a51508040c047d4440e0743c2c806c4900c0d503600440b07020303034420548403c0c040c05640019102074100380001550369144100c02940c040745200c2c090889002500c4806003c403681c44a994154000f480e800016085040b960401414440280303c580301c500d0368003102480c40035007480c0c58200041800c0341a0790a400c1d0740c120100c01c1810700c54000c1a603070560480e0b40f03001503840c0c11074105d88e41d0f194201c641d070100360341c01004a6880796650617040a244803114400000070b003006d141a503180040000c481e074201e5452841c1d031b1500c092601c0380c079204d080c1100301102d900f441086e0380303840c290081020100c0e000381c510805010648214 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 323360188 1250 323358938 323358941
    0xa0c060b0d2013061212020f0a03030b04091e051b010c02040504030e0a0b030106023c0c0a030501090c0b0901050412170705011505010918020708070506100603050601050a21 76
    0x25010f401c50070840a61644180e4251004241c8141c8031080e4510b41000740f40c0c4000f0346a1950318052010b060400d00070342d82140a00042d1f18810b43c4152224070003c046070001040c84411071110300d98400d0500b051800300c0c10010910203000e00240500440040350760400001980c440d8112000a00b5035070340d02d4162600030a08900360b4001301c180001080601400c0000c5060703407159001ca540e4910400c0b0141c0900c0816404d4094052105c4280d61041102c84040500103c196081d10740800007000454031411403a44103942a03074565100c8418010000a0320001c0d00d403100030246000301200c0040c0c60762207a8800c0d00c01c0b0303500d040e021009005081d04004034518406855996810306803c201c1e010703010720040e100700f08001d03640001c0d580d8092841141120a450580c02c4000c225200440c000e42117000d0a403603040c01042440300103007040c400f05111b443e15140c4121703c1c90402030002c4c116003004000c641440300400c15080a1038124000c0d031114401d641e0f401c1d5400311040c44000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 323361438 1250 323360188 323360209
    0x10b010e130902041b080a0b0a2421060e01120b2715070e1801140103090515070909020c060c0a020a05010c0306060f080c0d050603120a0c060b0d20 65
    0x1d0307940071780420203800a502c96602c030700407400c0010a014103121602004006510f520403003200c070710079100c040b041c04c20728002240d030740380e850803c01444003408642203403982080040e441c802e81d45001c00c0c440006508415405000000c04900d41c0c018a951903130074400e005800010681d0b07480408440143d001e994001811152901350b40480000d07250700051041c0640d84100404c4010344481c2035420310100c42249000d17401450800b9929011010390000700710140c0d1030405440c2e000381e80103c0d104001103007408044022803180f03490b1455004083c00460f80000c0502801001381c416a680e001a00c240c11940350b44c8160381d00c4004c00701c00da1800300d81c500010155424000e4400400703070194440021101c01e40c5a45559603845042281c09010480d840c042e00700c03091011110f1151160302c15603202d01c01600725010710781411100030164100c3d2103000006160a807401c2c0400050703025058801d0320942d0101c0300d0103110f5070740002c0741503050304079001000003054024065035941e4520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 323362688 1250 323361438 323361461
    0x1112010501180e0f15060f03030304020d02040c0c2901050a03080a032309010501030506010b131a070b10080c0402040b0d05070e0a08010b150309060705031b0a020f010b010e13090204 80
    0x3e039590307690381144220444084400905c29900c0c1c10200c01c7c281000b0048a00c26a80184001800030403582080000d041c06c1c8617100420204000d00300010741c80320031120000b200701d0020407034055859100008502e058015034015907024004200040c0201c0c1a00c4030f05aa80c01e01240c904400b2441e450070f40c0c5a03030301e04416941e80d07005000e2001010750040341600e0054055a106a03210300b110009072040820840031400c2d5080d08000400a42001106030341c901544c26241c06229100c0e841a0b101c00d60340c0c003d07440d141030b00c00c0016000401007201c0c10101603030f040d801c09107401000c08090042400e42d1070100e44070400642c0b018819440d108400710b006003c802c0700c980701c10b4001d0080419518507030050b000c803010400d603001e203581524440d440305030081610740c0e116038007101c00741c00103489050307421092880c40174500c2a035805000c4024a990051401000d004203990035036003240881818800c0004044803a911403003082c0c41050071070380c00400c1c99200e03031001c03800500810801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 323363938 1250 323362688 323362693
    0x1009091a060307050901090906050a03020603090a0f080a0813410c0307210807032607080703060303021207050f0106060329060909060402090d1112010501180e0f 71
    0x3c01c040280c101c0080d1810101c280d80369545141c803540701e1411120076020b855408004c0300000c000600d4030b2001154080110404d54a5a0003150b42c1c010711400c1d10b1400702c5810300c02040840c86e01c0d52000b0340c164450620360709101d10321025114450304045001d1017241d4013020f03083c900340c1c0404040c0641c07400d61426590300c658038804420384cd150300e02d90711828480e000302c540000c1d10b1040284085404284004038601c5514141c0c2c070140c080c1d0100384c088080c443c114440b1108061100d502c41481044c402c0b0217400e41c5008013008001c3c40c4001c1842d000d0500d41042440442d5000550000b600c5402504a03560369032820094035002c0103c5808005609121020481c1c951641201ca1049071005120481d047c00c0702d15482c5800180e0a80742e040b00c02403083c17010514000340040d4015130040c1c001480e000c1c4602c0421040e180b4a00240c40404101c207202c5000c6c10070100f5181c0b0002898001c104035414400301018030174807005075940a82c0c07644150929107905204190302150460704 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 323365188 1250 323363938 323363941
    0x210403030c02010b010c051c1202071109070305072327010e01050a020606060d0b0d0b01030311160e0c0408030a0801210803060d0809120c030c1009091a0603 69
    0xa0040241140804010040d42000300640b40d650050012a98181d44100540030310708215031a0714203403044508802c01c2129441001110a16603c0104821030090b48000228048007061040c2c200005e0500d4003094501000c1140e00d0ba0f11105042415035040c90700039490b9204907040d01c0d20301900140c6078000d1160485116050042d08203400c00707020a03268880700249900065807507001c4c42c0f10503805030700540006075051a04e24000d01c07245064040000f01901d44c08089814062118030840e9800c0450b0014403c0c182c100f908009103441c04001400030200340c0036400d210101510660019550090114000b8643c40c2c00740c401174048031085030340b540c1020b6001000c0d01000e00c100384d04200381d80703e18150303031190100d6122a9904000c80510f03644400b0184001d1105580c015184510180607441080d6500141031000038121001009900312410405090080080c03005105021400c0860b40c0550042180303011a45002c0c0c00040e450119461041030750310545410758010340010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 323366438 1250 323365188 323365193
    0xc0504051305060a05010206060102060c0a030f06080a050105010902041202062a2b0f050c010b3d0912060b1503010303031406090c0708040902030106090305151b2104 73
    0x2c0c0035a101c0e40003203036071551441e507a400680c1c5424042d2411801070704840c0002e41c0c60720018000303000601040c83c00240c2c2c40c0c988402801180c180d03070003060294125904140034000240102800352920840840c0b03001d03e41441c039943d00e07044010003802404041161403110061201c00190391094402210a031020681302c1d80e1958124002c1c0442c0300c2c42400c00c0030155400000700c041103215601c03005c00d454440701054809800c101c1d10b0107401c2d07480d807001005d13503200c044d40c07140c180980c9400503541601002014010740b60004540c810302d50b0026507107041d203500042040032140c020036400111071040c14840f000d810380784400c68018000c8041c564030600ca0300c00a50499000e65000c010840c041c0300c4140d500141559085d5009140a001c1a82c510064004050300f0b131064001c586000c1d41c5040840598000f40e2140002c1507000a08000b40030307090100305801c070b8000300c030005146808c2c91190040804034041300b8989102107949040381420000e2228030802c195035550b510318062 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 323367688 1250 323366438 323366441
    0x9030c02120d020f01090b1b0904060305011b05070b011a070b0f041a042613080703050d080c030703051302030102030a0b041a0303041806051507050c01051c0c05040513 74
    0x702d5000c1e006115040c000000f2040610030701706240d078828520034090f160800c0c04c000061120345168102802008003c03460381d03a0788900070003035205000200354544d00c0c0c4242010050303180c4040c410301008001000004500050702c5041d070310300719141e0b0b00210703a152a0311181d0280150050641d01580c0611000340c0380601c005120350703c00c5102061040c201c510183d9008010340d0028401017820075201c0c0b031014100d045002124456112505010a03012030b46a04542588001c003d50080d1320140300348141404003a0b0700300101c0c2009495410410101111484024100c00405544401050340405c401411a08480e0000c0007035441c2d0503c071f001240140105800c1ea8807032840e1038402c0005140d01e4160110310741d402006107003860324001100c0c00c02d42441407041c42013a6140c130045003e03a291803a03660a10094000d40751141c1c01850035520b081c001d548200d040c4841480410502c040407030050840540c0e22201184103050110181c90780e008580042e43e000b82c0d8160449220541d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 323368938 1250 323367688 323367703
    0x4031202160803070c270b03010e0717060105030d120c0c02090403030f050105040606120504141c030e03190f1701121e120c0c051302040e0708150409030c0212 70
    0x1940c29480069841079081e4158280540304014000c00941650b0b51b1120390b4403518042c18042c001140d4407640032040b0b4102030454112150031100d0b92010900800200301d01805010254002c02940c81c180d2006084105801180100d05403a03400400005201c0c02e83e01500a80c0500b40840c582410b2501034058014084c0040107149060000280f0f40f0b040c2c0114030440b00e407a102c1e02c41c2c1081c01144078001e0a00140141d1300031050701c0c4800000c0307104100e1401d10100540440c0d1114046441c02402c0e40c00f8100790f10450303070080c4400007407108040a01c608552030b50403d02340d1005824030903110400780d201021000e190041c0000360100d80041a100700c2e5221b080c00381600410000074000d6800c407890050031500c3d03040c00c149a0680921042000207000d43d0030b81c401079903100001030741e00050044084010303030003082c10002e040900d04601c0c0c10014900344600d05140400440e4000c07050360f81001d200e10349418605040c54015140c1001c1181c000c0d29021403281402c4000707070749404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 323370188 1250 323368938 323368943
    0xb15130e0d020a0809190b0f0418050615030703090b090d230703030e0709020c0a03090e04030807140c07240503100e07031e050a05060a03080403120216080307 70
    0x240e6028690707680c030204200010a40c080d403200c0c107200703d841c14445904e41100403680b0302000707598040f480100900c060549840c400c003800340d4481c01c0241c1342040d1444008641981410041405a80e03a141d10326012803452110301d247c1c0b00c0c0d903800c00c214041c1610702c0d0081e00904054044c480c0d100310208000f081c543c250b03162030703088c0c5140d140400104450340400401050050080d01c00092198105420100040e0304171000151150074034801ca0744000b40910b0190f0040c4048400c05810004002c02400c201c05403817541e14041e2405040c40800600e8034081028040d104888150307024291451501c6d1101141d0b4006d40f140c42c01c000b03658403203140030086001d201c6008a030602c50011a0300c12208903103903404592502d10b07080714101019018100703154a0303115503050f840d1104695240307412454400320707041c2011814182110f00190200e03010700412041071010810140c1103404980c1d0141c12408408004582241840e03005440c00c40c0b0380d90f444100007041c0d45d001024190b00360 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 323371438 1250 323370188 323370193
    0x160b06010e1806040209030a0b010b041a0309030715061e0807080c130b0418080721050f031302090103080c0114060a050906130f0f140c070b15130e 65
    0x1041c000b00290110241c2c0c11910300104100055581d0074540c0243c50040c6020302118110a40c0fa03540c00f00e4504242c10200012001241c200945008644c2d00d80e1120b00f81c005441c61401d03c0100107841c0d02c00c050300500582c2c0c0d114000c1100c0c0c5940e5000070001c0c40c0c1d50102d100b040a5800d07000303500c0c0c0010f100e10340d06071040c8075000c00c01072004100402200002010b14680381280142507024042c5080d4441d8815540d07090f00d0025200c480750103001c68844d6501540d04c0b0458500f564180d04007004008070350b034030480030100c501d030440201c4444880b0404180d40300c1e038a510804400c0183c4040084d044405000000f040040c464090f1100402c0c1000901040d642c04128400b018000c8418550044488000b0001801c4c41440301b6002007000c0c20b5210003150394501d000540d801101d0000132070303079219200300785e0310342c1c0d84503002c1e602509100e440010700741140c0900290003600b50103011002540d01084a40209058000038500050691000c6040c03010801c001001e800c203500d1001e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 323372688 1250 323371438 323371457
    0x1e030f1119180204050a15021c030209180603062212020a0c08060c0316031811130b1807110f0706031d0a0305030901020c10020403030e1504050f06160b0601 69
    0x1116140203444c1524006000b444a403031030418915010144103400e0303000e600640c4400302c40c107902c0b1403605000252681700565900c1052090007100725042841100c1400142e09101440da400329100b5002a00004200b10f8500b441400d0011000b002400170301d041c203044001e1140c1500420051543c600450320f5404041e50348105035102e40c411a600c0c0103028040000891400b10580d00383d81c034508500d000582c0702d0180e620022503505401c3c05685008600d03c0d645031500c0e00303e600100d513140418060202c8000d94010030200048098402e080301c00c03a90018225070311030480c8070b8422085004403410003826507003141e01c4417418021080000d040000c0c2403c1e58214040c081c03e98030551004007191100d0791001c4410350030182829001d5502040003460b0b2520421480c0504481d503035005035104e240d40340c041c1681c51003c812070f018103092060140c510b01c100042c1c2d01140d000340c401141410030480054103500c42d10402d048020003001d440824070142d82c400c2d5101e45030030303200d11804 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 323373938 1250 323372688 323372729
    0x9020d140c07051c031b020a060c210209040e0d1206050a05060a0c110612191b05030406090b0a0f060b0f070219080d0203030703061e030f1119 63
    0x3248a01ca501501c41d40c0f0201c1d4a40c601da010084460041d001c51400085203c1b40c40c0c10810040303031031524400181d208006041c2417200b10308c00c110306d804c2d160900340004900f6441800315003590f100f03554103a0741d0200d0f1001880e00c40d908612003c641903810b5540d41d0207090b07405481e46045140041d071641c507010020540d405c0c02400102a101c0041041c0e00303090b100d8000712061125403004a6104a00007002c04281c0c6420029143d0780d4000d44010034585005d08440b500300787c03444a00400307541048403c90440d44034410a03140c0404a107881c40d0760f0707521420900c024008010b40208829042c3d02004440034051f44825045e1203102c0d0140001a540e1840f00c0e49800b80c0c0c3c40328030010758200030320343c01442e00070507042c5800b03441e818081200d980c941507113080c1008080503401680002040183c0a81c1c0b40c0310300c6014000c69a038201402d001004200001400c0340002094005140b000400340042001416081a8020a0301c144406d03008102c02883c00c0304c3c030564124150b03c0001d07010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 323375188 1250 323373938 323373961
    0x30406090b0703080a020306031c020c0f18011511060c0403110108061309110d03020a0c0b1207030209030f1e0c090c030604020703180f0315090302060c0901020709020d14 75
    0x100780c0654a4012a417160042000294000b81500c4d42c1131040c82642007075540d501481c0304446070350340c0203003460884040610203480c50b034140c11403040e9041c0d00a0a11081d0000909040d10a0620852100c8800740700540e0000345102c11a152841030008026581d12404d0040003928407860a030110b0002000040d00d00e0301c3c095030340590111411102c1200d05210703501261203140100c9041580703520b00e0011901c807024442c1c0640042c0c10000220003404281c2c45410000d0035568049458003e4401c0b0320a2000c0c0b01415041c10180c0018075444265001c0201c03400c10700083c02903409542a60400c0302e00001c842180c00d801d80242242e2b2000d41c40c0240c02c1c540700707401c0c8014180c65640c90508110007540194403c40070b0000c030a1360010550481e10190019102d9504001006802c50801040b400c150041100e0a0b90504e104040000c0d400b080040d003146100840d0740d240e01c0340100607810040c05800280320f291000c43c140080018a81241503c40d000c901013603007a4680001412 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 323376438 1250 323375188 323375197
    0x50c04090f02090904060b011b1b0b0315040b0f060a360b0702010311120105041a030c040504020a1206060513111606021c020307020f0309360702030406090b 69
    0x113901010703010009001c100e43d500100e02c40c2d40705141015a061186200744d80341c40b22004280d80e550b151403a01004140c440078203902400d07a0804d0b440c250302c0c200b0640d40e010030246884034060750711490706641d45e0300d4a01d040084400000c00c4c0f240c55800d0243c0c01800c0f5071b1303500c01a07041204515401c841c00d544601c50007865444454803480c002c0e040c2160f80f400ea912400c0101d04159840e2222008000350030044c18600b185400250b950394504410803059880003110840c00006000c3e6401041c1e900113841aa1230105807408200c0e0307070f03e90000030888515540020301c003140150441e000c10000d035004505480d0104d8000300e10b030340c805030454119800382800b455015001c00507203102e24001c2d581c5d481c1c103c0c0703e0a409441d0829a071001d001c082d03258018446041d0f0040140601c468041c440b06009a4141008500b401c184200081c40300254a90380e080030f0041e2100001c640c010418004034525940000304410f040001000359264402c1c4500d0f0001000c000300440c44500e50b40844 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 323377688 1250 323376438 323376457
    0x16032f1005090316121806210e030a02030c0f120327120304150504050606040f020d0c0c05060708010303020309041d01060320120a08090a09050c04090f02 68
    0x100029450040d03100010000604401801d110500c6109071440200d40300f4104188100d1040201d6003040c1009030a541c2d000414003d400005041800019800240c42980010b445c010001c4041c4030300074400107025000c00c070166070000103110680140c002000b482e040456030119508090401c0c20f1a44820140340328041d901001c1022032170201003000307020101e0320b4946032035041c22188400646005410518020441000300403c4117000b030f100d044080345180002d09015900d0302d61341d083c0d1240401818240700e665201c0c00b60703d5450051381580c51403052031800300545801d4402c0030780903201c03a400c2100c145c0704020000e8800c511804025040b03980c1500154140031501042002504075140d9008122095507050200d50009015002c019401054403450448049002510070503040600741d0260344800040104144001005441c644e004006a0303164400c150000e05e0700f8400e0b91000a010b401c050500a0700c550040041089900030310080000c02c00c00e0309401c081c1d00505105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 323378938 1250 323377688 323377693
    0x290a05010e0d020f010215040b01030c090b0a170307080d1b0c08090f011707031a100203070609020a03020a030b070305060109060f0e01020f070801020304021c0203120c0316032f 78
    0x11240182040e00c0380e0441300505005881400501450a00c5845c00860303050714082c20940041041c811048104000f900c01660184094030031003021802c1d00b0354510600b43c1111015084042e820803c1c0180c038507895100da0030642e03800c02d20001d00c0140021171100b407107c0c601c4180b08140c0600650303031040c0c03080e4445102c1d805c0040d00f004100c0008103606411b81440a104a8100130503902c130007092146465843c001020558283c01d0050008450705881c019283e01c82d00c0c0341d600d600001560381540e80b204000c0b032140040c1c40402d00c4103000d544001e40094400a000c01000000200240308a01c103503000c004503a42c1c00011102d0032058801e40011550603c0f03003c0e002441480c1012801c43d060048442518206030740915046203a07025004a0358088203100461500004427818061440c03840345480032181c00094823242d020100c0d12618200160300c2504100c28810f0b2a951148a49640301003070082c1409054084603a240380c0c1d14101009407907079070a291704042032076800c03260700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 323380188 1250 323378938 323378959
    0x1a070903080901030b1f020f0303061806150f0d2403020402090f0603012304021207050307090312080609060301050c1615091b08030306010f12290a05010e 68
    0xc9810959010482090406803150a0a44e564444108074421780c1c030f0b004078503143e0201b07800c0c00908080035500d501074580c104009000d050384c0e4030550000a06070009aa44075030b2550740005402c250714003083c0110b0400841c01401d0311500ea0080c0620554900062204c4403000c1c80700c41c8480e15460b040c2c03031494080706007800981000c0e80a040205006454640d003010724000160154009030301600b041c0c242500141c000002d0480b00c042c20130f405a5081d41030540e50302e9040104c99000742110104200030000078845881111520000e6400c404612901c00700c51030020400726044910b03600400c41c50001c83c200e414140b00303803840307010100c81c1076042c1082d200f0441c002d11041c010a442041a403100c000b61380c540c40c1300d582c1c00140305100d01e050303500300341c0c010456060240d0300c02c00c0c180c1c00a00c10000c140c1d822a026050b40d52071450210807580da0035100400400070148441d1440580d02c0c0071400d42c0c080c610b9602d4410b241150128038595484004440c0388140155150300201c4406 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 323381294 1106 323380188 323380193
    0x2a0303091b06030a0b0a090906050a06060512040213060e130203010b090403142a0106170c1305130f0308041203142806121a070903 58
    0x4a01d480c9150818001811500000301407450164852502c004c4c1e1b5030b501c07600e0801404400301c01304481062401c00030300414084921034021031074110003040c6140a0001e4032020840200740d5845655680d090002c584502e803014260729840340400f1440300001da001a202c1ca401c11481c0005c8046c40c010182035541140200e030203005950301780808607078400d0080c4009000c01b000c645c0d55411704d61007500c2d603000c1c1c0c0a040c0c003818802c91030002600c03010b404c444200c0b5040308403184c1d2020341a090703d07103c106d5420303444d41c000d1810f16850603011003500116480780701c2d6841442c0c5856103864106040024040880010b180c3c44104010011070b140c11405e400d82d207160802030082c0c0002c06c0c81e54840098240c07010101c0031100c0420410a8090402800c504076070700740400c5d9915005001404200312040b50030700742c2c204081010030706c4405540d2080b191035451315400b03803554 = true := by decide +kernel

theorem cover : BRFrame.Cov 323201438 323381294 := by
  have h0 := BRFrame.cov_init 323201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 323201438 ≤ n) (h2 : n < 323381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
