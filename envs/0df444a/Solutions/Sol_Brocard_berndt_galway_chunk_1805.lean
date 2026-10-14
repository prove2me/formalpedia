-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1805
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:44:32.771759+00:00
-- url     : https://prove2.me/submissions/c7cd82cc-bb97-49cb-88e8-e7d609d62ac7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 324460431 ≤ n < 324640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 324461681 1250 324460431 324460457
    0xe03150a050c09100c021905060307032f0711030607050d090606030807060906110903152a0a020d0525030201141614070c15020c030d08060909010c 65
    0x550300c440d6120990502c1d03545056081000110880120184140000c040d8688072003142810401040550000c40d08844170310304007c00108140401007072002015078840b28031008002480038039000c00c82c02811001d00c10510199921940e00c8141d0556030f030340c204d200e0521181000549680300f0612684c440c0c0c20400c85240c500c016145a04040c0e403066151940480030400410003010036900c5840b001510403818900b0600b590341d114042c0d0f920840a00a5418549000c1006042e800380020401d180765155020165800b00c2000040c3c54940320304000d5500031b01420040c144080e4940840e9401c80c085003089511f44128040f5166009010320700302c0b6094084514100c00c1442400080703405650304e01c00f0040340004440c0310107103001200d05410b0481d04140c500e4000301d40c210403145810266281c05140030000c0c81075001c0180405080e1b0042c920074000030046480c0202a6000c81c12041e1700142001000c0d06c14511409011020400d5580c05116480f40ba0509840394040101c032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 324462931 1250 324461681 324461701
    0x90c0f0301060c050a0b0a06080f070e070c0302160905041505090a0816140102090a1e1a040b13090c020120030703060f0b0d05061801050607062304030e0315 69
    0x3c209002c6889218480710203000034913580c00c06102e044001e40000c0c800b46007906080c03a10b010821212400c0e0005c0700b00f8428100318010302a484040c90400603800911460201c1c0703001001c5400f024a41501c507000304080385030303801160240b401103c40e0b08801203100e0158080310001c0d00c2038805540b002071100d000450900180c6819858003041140c125010f486090481075910810060340c0d41c0051000780a240180c01500a030018cc0070700040d407840a54100d810f030b4424040d02003a01e2000025045101000084801502551610580f0b84845c00c0c07407065002c034103000e50001d00f800c100580c100c0610510a505040c4010a2034403041740d81e0b410b07014032940c005849d11007050303101d690200729101c04a06244c01040c80445050f03583c600e03200c00e03004641004d08440d1255000c00b801c1c2c41d20482102c0740d2811355804076600b41e50380d401c614154009011000c1e107609159403030901c085141032031040c03443c440d50181d03d85410a003640010182c49103080d00707901721352307440d010017182c00540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 324464181 1250 324462931 324462947
    0x3190b0705090301050709051203070201050403080d0207081204060c050f0318030c2b08040203060f0603010b0a061707050c0d050c0a0b0f01030c09050106090b130302040e0c090c0f030106 82
    0x4441c24001e280a41060110f03080d10800c60b54080880e0001804021a040ca03186080c0c0b01103c000c042d43c04c200321076000030101d20461101808402020a281400303003440d90485128540c0844015550010703d012440070a00c1103c050f20694a4955803002d11783c01001242d21084808000503c1c65480c00f40c0c00801c4252030048541902c0b0910405849040800459001344104605100c0c82546490709007a01c00000c2d800d6010000d02409200040e100041c1c40c80d005200b80b20078040355502d4001080c0142400801c0641c0152074803c0060070301d8000d903101c4d102c0300303e8a0f04040701d07903030340301081e1178900ca80b244401090340040c0c040c0701c0c0248150301801240b108030058030b6003000f180d11003144450302580c1c0b6101185103e0010420402c040354040001c02400100b4005585495409044200c0c2031207032002170368000420070040d4415920420145074001e101b0440340541c01c0d00c060b035515000041d04d000e08444000f02d050a055201074401d0f2048049c0303490b185070308082c02110f03015 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 324465431 1250 324464181 324464191
    0x30b1902030f1f0e09070f23010c060917210411010c08040f080d11010e060a021605060403020d0e0103090c15020703061a210d031e0e100b03190b 64
    0x9003841c00200d00281540506802400f0480045c03142500300f443c2d0800840581d0322455234907c0b4807007140c208901da91110704200409003452100c440450518001601050f0001001d0f0800f1181c3c01402101103000303801e5246c00540c181180000300400f40003102070640d0081d000418071203000fa49588108002582e29120328007050400f0742d41c0820f00c0d080015504406038030b41141031080c0f8102d070f00400c5e40283d00f04003802405a101004c20640d152400904400c8856400141c0c2d04412090960500c022980c000103d0fa494030300780c1002525003040700e0212000400d01e50043c45690b00c00e010702040e6503000746182d0308243c0740c1080b0802c1074002080f10f000f0350040f1040007003c00c4041c8110380d1907180e400d0080b44482c850b0030800058a00c4116425105030b0004170303481d80240c00084a008002c0d1a00380001c2d00d83d0484000b444551417054503a081c0c41c00d05000003001071001c12281000c080000c0d091001c5400ea40070551194491580112000880b9042002041842206076042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 324466681 1250 324465431 324465481
    0x7080417041a030105030111040b0d020901030b13051f1d0901150311030d05040608130c0503010204090209150909160509040c0c0b07020d051608090604030b1902030f 73
    0x455620b0800c0b200c50b5034034485806000c8404001002141028001c80c02d000541d00c030503510f401d040c15500882c0303008407610144603a070701280c00640f1741d010768000501504020168129140014440300c05400111200f9540c1543e03081c9101a00410b00d114001760303040318501d034910520120010349050001403641d9019134a80c0f084113450b01107640410040c40c0034164000e0003081003020301d4075048004c40340b10100401004108402c90344204250b402003100342c1c0003450a0b0880c00d2002c03059080703401503a03155100203400105280140d00a041d0180e0540d0250020105e2052007126801070034070081d044201c0100042e02d00c007980c1000c600340402401d215061002c4900424200c0700f290701c03d10302142c09a0003007414098850412980050f0920080c003a001110354003d0244c05201000341212660381400010000c02c9815240007800242032151a241c3d241072812090005a074000302000303404800044540a5000301c1c1e10521004010348459218041ca1420305003041c0911911 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 324467931 1250 324466681 324466687
    0x20c01020c011107050d08030106090b120402010309150507050c070515160804030804060f0e030105071e020a140703140303070f0e130603030f030b0d0f0311120403062307080417 78
    0x12a80c51007001b2284c6402030404075242e604141c005011015580c22000c114002409100100d03007203c80155841982881c0128002c809880c0500c140418140c400c4121428a8204614a64400040d0450850400807200010b030b0300d10502c102d000c0c54110380c0c0d481c90020044407074100004642c080c10180f041c00300038a419601d4540880c01c0d041600b146002400001c0304e8801d95038840301a003040c06c03045008002c942400c2c1e0029022250703a0b400c0b075084280c41c000501042d4000e00801602039080308044080d003544450454449010b40012a41d242d42440506ca400340300009492107911031b42c45640101d00c08027800c1e540555204c10701c0340c1c42503c40c0c02c405901d45075070080600440c403070307119a0f40107000428058140e911680415008180c010b0b801f502042220b40c03040045a01414213000201181d60050b0030012885001810102c1c0020004100100b6921802420030103581e4001c03000425003640c0358071039056506000054a0001180c00b04074901400043c0c104490042c0d45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 324469181 1250 324467931 324467939
    0x9060907060c02280b16170c060118020c16030c080f19080c01090f0201080105150d050a060e04030e0a090b0303180f0a09061701050603031c09020916030b01020c01020c011107 77
    0x1c0c060b401b04418441e02814801800c081128403000c1c0781c12005100d13a82400c001c1440000c980c0d8500512644404401071510000c074651264101e400406410068400003180510b01c0604000e042c0f0044030000800400043c1e40c03c00407500d80340343c11894029042840c411060a4440007100105a4a05d40c04112010041e0700c02d01c2002806480f4001c681c81c0e08120340000341184070168030150185110710b03600d001d00444182281c441c484d42c9900000d468440c1c41e950341c020314094101c4c031a03886801c020720050541100d000d43e0100000c84a68142c80e0b00e071407001040d52080e10130203800da0300034081414551380a0a0307051400801400a84c0d0b003481450002c1c0c49824a648603115440c0c1d150800d1100c800103051484004c00d83c1d0000744440d080c4280400c0e90ba10600c140d0705012001851090445040c0790001307842c1d9500103200403210308003541c1c060301e100c0e81a00c848020134600310813070240d54004191b40b541164140c000c0c0c1000300740e1000540c0c001c8003004403500c440c041c0380000301e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 324470431 1250 324469181 324469199
    0xd2604050607020c0a0b040b0d0e0d09230a170a060c05040611030a0c0b1503030301090b0108070801211e05010c170105150703030e0609060907060c0228 67
    0x51069000d600205654180404064107011a10400900039071685c0e0061000003d50030031681190440f04006660b80b8100700040010550303290b58403841d014542c00462050303030040401007568030a15098210352035183e14990540440c1440940108510304100404070081c804c050a12240c4c2064030851401940c1361411569005002070114401060034007100d90f1000f6445980e43c46d9400451508042d4540504a8042c4460041007084908005400f40c9203c04041c10610340c00350807a9180e507190900c0d01d002c0e1501010541c00290f00c0400912030034403400e100d90481c0e28885018040c6a01d64407028a01404070300159155003080001d100700480b4042e2036203445004078000501440d0002c4001c0005045841e2100d200c158071005025664480d1170208660602e40b0303055582c0c1220b031500303402402d00c021807500c40b80039920070882201c4011608912450482003a1000d06481700300a46034010300082c082c1d0012151284038007000e1a4400940e8000b250005500803196184502 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 324471681 1250 324470431 324470507
    0xf010807121b020705031209040203040203070b0d0605040e030316050c010b030601030c050a0f180b0112020a030e01050610120b0f1512070c030e0d022209021e030d 72
    0x845214603900034200055061204401071720080700075209150280688540074050302122074401c039800008103086550810410b8001c2035050200e0740c55407002d000103c028071091050600071b50070108800740600021007240e1180200e44003140c00c104004030100c4180e0003801102d2aa0b40d40d0b00e0442c2a00d84d402c01c440382c000c6101d400b0300009582010280040020303143d006404d680e00944040c007510311402a1b6511800d21010005081c03d4581d004840603081d030500404141c2c40080c480b1950740d8942c12807805412a54001e100c951603000500518001c80c91080b00001d500e501e0510961841c2d40104403442001030102016104000001d50401a0f00060007075089e40040c91071007400c0302e0a011a482006400c00c00140a81d90320090310341084800c00b10322400c61481d80d0000c560714040d10710b44c4450700d5007001c1d004400b02c420300030080034013280036842841301c20f001c3c0441c060b0f41c01c04540c440c000030b40545041c61009405a5041d4102c5800c540074070002800d201e2194015148 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 324472931 1250 324471681 324471701
    0x1101020f031504060515090103020d0e0d09050603060d020402090a080111071b0308030106031d06090106030b09010506061905161104050f0127240305060f060f01080712 74
    0x24550381d09005503039030b154200d2808640c2c0510f043c21010003c65690b00c3c01404400c150030011a0344402c5c04c40124024420104a41912403402036940c3c516880020b030203200d404944c035095071741c130b0310795081040c41c5c0012120316a005001000280042c10a9000b414009002612118506898034440c0303096488465014400c40130124061060000600c01003503810f00b01109100e016045844043e0b80740320501404046c0768481501c6901e0001c8145540305000c480c0301a5001410000300c120301038155484161381c440308400101b44001018418180154401002d01e80b8000c2d2808820b01c040d0780360004003052000511494490400c108d80282080f80706420200b0014001001c10048400c050083c880c02c98a810040c0001c1046024100c4144200004020a540710380c070a1400360014640c03901d1269041030456002c80b00000401056038440d4050b0741d2166035195004d502a0022514140c0c8698002900d00965014080554200300c00f82362040114004100c424103035140509 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 324474181 1250 324472931 324472957
    0x60305060f01170304030b09030c0f1606021501060e27040c12021509030c03120d1422170304140c010e0d1101110703030203030709091e0c110102 64
    0x4010301200c55040e007501601a043e0550b14002e00303c05481d80d02d00075408010705248003000400c4110b001041510500e0512108403021181c0150000345c850401801203151800d0040c07010a440d1300128111908612460309000c1c146e2900e18122005101101c1240d0005003c001c650460000d02c1c40c1c40140b02801c01d055030741418285880c1c0d900b42c05640c0034115000071482c00da401070740c651090032040001d03450207946079002200042c1c00c2c01401304425505104040414180010420207041000d00d181020407540070a80c0d000107040104403041800030b80c0040300e112040d54503036800c614150140c4094141601d07801d280c0511340d0300644050303969541410b80304413100c03020001c0044581d02842d106070000700e070401080c220f03001c2c2100102024492405504180d20925138a014081e01c201104c1a40d580d0741000707501d0760300c16a61800016604900401c01040134040c001110125100c03050918600c0001c00b4001c106010340304080291140f209104048240007424121003422 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 324475431 1250 324474181 324474193
    0x7120e33041719020a02131a0f1207060309020301051b040306020f121305010c091d060607080a1709070302061b01060305030f0a0216081c020a0209040b06030d030608070504110409060305 82
    0x80100140640b041d083e07881c055040c00c1025948c0413100300072408483c0240d4649070650512400642d12814141c0c49040500c56844002001030740b5800a0300c240d07000750000c00883e2a4114415241c8014000c44441c401003000204001101035000344000808841d2090a1240007000f101b0865016642e90400e2131700c40002e0402e0010030b100d626180e42e05820013a02980c40c0207107038843c11700c120101c0a0030302150000101c440d104c101c01c84001d15400b20006a0b1411104005022150b0340c280001d02085d901e030010b0182000000c20340c0581342c0041100703051803031078005200e50340301c210403802d4195200c80000002850810140964008518480d521074000f00fa0080c6400701c040700d40d0400c00604101000054008100e0040f100025440303407c03800c03c07001050345861090302c002504200340e441048280040c0c08141ca0188904800384d80394001d49103403c9080d181c0038000c09006421001341002503150642c4000c200b50b40c1c0c1d0007880c0c2466503d8070400101c8a05a10070f642982101d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 324476681 1250 324475431 324475433
    0x933070201020d0906090504020703050d05010b04210503030a0504020409020d060606030b04020301050a03060b0621041101020a051c0c150b0f0a080705060307120e33041719020a 78
    0x180001203c1600f2860549415450028010b00100040c81020f01507540080c5002c02c0c14070440c01c1341c0e11b1414004e0244401d50351625443c1060384144280c43c002c0d01014104118860300340b84940815400c080103504648984401e11300600b00644101d9200303989042100c01600e0308128548002c0c0214030001d100e40c0b038440003a05556000c0c2015204034030410060155503641e600f040d080d80e420100004d00511075101080e124801e0403a0005101c1c24001a0b2200c4554904081c0c8544d10402c1c035040700c14110710040e6038402907403000500c560010f0030482d090805100300030760441402c0c40d0400a051164850800040c3c9d17210341d110001c0c0c1c807442d01d648542407121031003040d1042581d100407514a8800c44035109c140340d0103801c0c401c480000100b04624440c121506c40c0090106c0c2c200044100c0803030880d9990311490040c01114003481c0d5441c3c419900c0b50555440a04111800d0002c0d60f542e80c464901c15503401801803401c41c1030000c018600080c01004401c0040c41d00204103011203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 324477931 1250 324476681 324476683
    0x3010e0c1e01021905072d0f030b04060b0a0b07030302030103020901050a03020d080904060506040b120a1802090c190f1103030c0a0509040e010203090102070605060a060203093307020102 82
    0x4841e000024041951108a40316607001079a00450b481c4c03104c08044415081c6006030800c0060340c0801c4081121032903414a07000d01c920091000038000c000b105405584074010411010f0910014003d060319000180100d1601d0b0003054485100500a2840580340d880d1150181c00c07451040d00081d6000c8010300460400309001805088100c0b1252425403965002403020248440001d04039070020030250402e450b903410074000f42200406040e01d6545807907000d0081c0d0000d0703460040166150010590203100c911480c05080d88105941d84242d07659021301403441800703008001101010040c112003500214006403401308940c4d0b0f5407122525482c401001c038008180401c4d40c0e0f810400030712424500340000c603001c1e2409810516155828180002c00130103c0c43d2180c92594000810407010040650041201303074841d04040019480d04024800441d025002d0180076030300420808415181c842081039440d80260742034a0822103001c00b440300e10480c11010550400042003400440da0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 324479181 1250 324477931 324477949
    0x40516081e06010f12061e21080c01091e03020d110c040c090902030a0204030b0106020f03090d050c09040305090114040806070318060f0b090a1803140f0408060603010606050f03041106040503010e0c 87
    0x12000c88e1051168800030b1551301d80c580e844000b031041400066121110000390084c81000e130300180071007441c00c54808641181000090101c0050007507001209009004010281540380000018803a0401943c2400f0040c41c50b288028140108664002803804050000b9440307051710f88005a00e42e4991715200320308210681104066400c80031a01498003000001e440904204035500103c2107036a082050a01202d420345c503030813514100c00c10082c1a013040c014501d02d0400c0c1d8074044000f1100070301806a019030701510909030407083c041000b581c42500b0403941640d00300d02c1000c0851300765039014119080c40518030b50041e100c0c1001c040c0341c6072504010764081c0b100c2c038003032021450f511481010200c6200c0000c0c24001840e0050300c145041074207071940e007406201800c0d81c3e03546844d0802e5070744130121b61481c40784d03091010101c1c3d8103100e60700b9551042c103c0d1200070b003951203175541d9083c4103402800f5a038001c40f05110014166a09015010030607d520f0060320041c0090003d0080d561 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 324480431 1250 324479181 324479189
    0x708030a02151b030a020c010c270302090a110c070305060105090708040b06010c14070e040c060203070528120305040b0610020a03030b0d02040516081e06010f12061e 73
    0x2100705401c126164260a2051400041c1c140b0000d40c4d80d500d18290030004d0241c1c400d00303802c139864005020b01003608001d90f1502d840c1201105880c9c201104480c0f660b16005000094100b00a840440c1001920360003100300390040b83c0c060b0b800c00b50140d840c1d41c034003904c42d4401d07545540468010019403e000c60704a401000c0781c41c008400d46410b403200c10811102901060402080c020100140300009040000c10341d111010748221641d41c10754154848400d540c19241542108000601320b40000211040c1a91000c09442903003241c50580c283d0b411a100d04090b00c824401d40c5c1000203240b4036022903800c0705ca0b00c1c0068103080a0070032038084c0708010701c19402120400341000c1d2141e000214410f80650510b40401d800106901180c1c140c10b4100c00203401900f40001d0010407900c600400c0003aa4065279800303440c2d60344800d848001c030344c51300c2c140c8400d454040100701c640d4450f131210104440103003440b105d58a00c1c0604801204c00070f034001183c001416141703032070712a644445c2e50018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 324481681 1250 324480431 324480463
    0x515070b0106020127030c0c09020705010b0405150d11060d020c1009050c060a050d09030c0209220b13150b130e100b031f02090901080115170f0708030a02 68
    0x240980705d240c48041c2d880c1c40c01c0c044540c114100075504144c4101d41d01420242d0210703178240c01c16600c40c00780b00a500100c3c0103d5407035003026140d50440c2468401d107481507410a0860704030380c112600348420a030ba043c0c7c0503900e801030a0000380003511050010880880356180050350780600d04030701e50418684d00b041da8003071410041d89102048000070048004070040f910150380302d188003425100c6105101601100c03900b48402d64041c10b802101540030103000740d803154107075070700c1c955082c81c0e080300822164054140ca00503240400c0701e803d03489500034461158864641c207540c0314140b188031550050f00ba00758441c0b81c500741c2c03801c0020056280c411489828001501544c0e049601d4407040d01003204441c1e0b440c59010403598007003001c5e900c90745180b17850105510880d5402d0020b076015403270407802050108000116440c0500c240c00c204020fa000b0014840d05250f807880e50b00c0a2104c01d600e0038030416000c0420035406109401c0100085401190b880b104c0740c801a003040750901400042c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 324482931 1250 324481681 324481691
    0x30f01020a120e030c060c0901181d071404030b06061b061b120a0b1c030306141203090d0501020d0e0309031e0a06020a021606110105060307050f060d060515070b01060201 75
    0x905c50008545800c60300000388142c403080c000c2d004030382c2141c080404106280e089080064903003104084491a07010681c10f04083d80c1d1024000e4815500564074001020f42c100001c00100b0704e1aa03401d41c0010000b01268588044101c003a14865103985903000660005030a0010f1aa040c0038a45410702e2940200c1703041506514408105a00090845503a10f403030304110301c00743c9e903504440f8000b6034400d5110072110610b818001c0040680303004100d50b80038220b504810344d24222401240224400700294900120300b41400007110000b881219599028072021203101d40e80c0c0030700c2c030764440e6420055881d4400402050f14001e09a804c0904541001603540f99402011a0001d6180e0300003801507074808801c40201c0c9000890b07001002d1103e1580b4020442d141c0c0032030b050ba11007142c0c80084c01580c4845007010b4841c0103038491141d11403e0780c20504c00c01c0c09e145001c2c00b1070b41d00d40c0f04009081c5941c1c4020078124200104d0800103030780b0026640c8104071281c0340181c00b5003071501c02001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 324484181 1250 324482931 324482947
    0xc0f0f120405121507050d05060301090c09090c0f2c040506061c0803010605071a01140418080408010222031112010b19080709020f07060b030f01020a120e03 69
    0x150310450090b02c3c0a201c1103600c1e5800d0788401c001810a40815400d04081d516040d000100700f900300b031490040c09410030000c55058641405800c41c5541c1081409405503d0045084010820740100b210f10201e07010b000203030b184030a0700d06001048610040c607007024114440b403105520100c6a065a0a840000e00022400001d2203660040080c0e900e2007051b040b58200842188000000400e45038001001080c0e8a50050180060500c6428500c60524490401c4410030009000709854042c1c0800900c0c018030702904500c83c80c600c903a50540b28080c058446404c150b006e0741104c0d00d5a0b40000f01c0101d0400f10020240c0032002136a0081d00301030541d6240c011099041d00703180d2280482948402d405582907004889901d0001d1056400b9010416020005100e500c9104854002d0340d81c005000d647c14000c42d604182d016000320b00d080e8140e540c0d02c1c0145420f140460b0540f20f000c00764842e02c1000d02c011310101030140c40d2000b1030076007111103038291000c1045074401e80e0810b0100038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 324485431 1250 324484181 324484213
    0x8010f050f070c0201140a230307020d0e010513080304031a1306020d060512060604051006085104090209040f03030e10090b010509060105040b0c010902060c0f0f 71
    0x6800030403d1500d0311001115000486154021030340002103200b0005181052642140c14a030300d562141110003500031540017034032054041145c42c10302681020b40b480c10001d1103070b22400c0c00000141030460400100640c074000054040d00081200d40c000202841480001288604990040d02003408245000401e16442802c0fa210040019030041511032011070650070071805800060b260b5842441d40d080040e9903250141c911074084c074544004100445003242c00441a28055111401d031900c44c1d144611a242040c100b00c61050243d44020610b174004080d00c90051030340311890f01001104040a24600950407d400e110b203113028408001030312160b51a60380a9008001090038141d18181640541084921240c09015001c506507103a5419444900003a02495031060341d81c0c0c0303490500c10b441105540d8540418018401007203828020760003450024003400000c01c00c195a0340c0401d800d41c211840c04041500f02d021901c56031601000784800c50071aa000800064024100d04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 324486681 1250 324485431 324485461
    0x91a040b0703030b0d0b040602031603180f0203011b1107141507020a030b190605150301030b0a0e10060801141b07020103230906010602150123030a0c08010f05 70
    0x405140e20340e4160050781c5d4404030f4400700c1036001800304c0100d18140c5094002903108882030f0004040c412441c880310340c480e1041f507404130042440425171014503240d8283e000d100400403a03156403100c1034040030b4030010180c84031041190b10340078444114500443d080110641001c2e03000f4940c0801100303d56512400c511038075417500402661401c950000c580300e1041d0b9000a03002540034000d02440d01c10201984545590341c0d00c0801c0810384403001c008e040501c444485502050900c01130003c240a203100740d0308814460000142c0c18a81d941807410000401a040380c1c055541c0030130000c00da400e000b04c52400d4503240d00a12245000710504a0342c42c503161002071242c4d03000c1400403c6900a074446641c20740001d00c4116100d43d55441603c820b00101c8060955009082c00010014000100001e91020350503c00d01e03160b080c00f020b40041c4810791a0203400914a401042054a040c032922103c18090040c40e003046007000100c50079101e06000303c5224501d0041080b00611030f031848 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 324487931 1250 324486681 324486683
    0x70308010501050708070b09071d010308030106050a020a21110d0225030c0e040210020703080a080a390903051005060102030913061401050f180a090c091a040b07 71
    0x41d440d01341d41c0c02d040f207181c0100e035002000c1444030001e00207000800100e140850703040700d03020140b481402200c03c60200007031000510002e4280014003006002d400a86548a46441124000c0b506a01d65103080d09403440000b81c2d043c40e040c20300181176840490301800d06c681c10002d1800d44d02c81440256590701d504003800044403100c5a2050ba144070003400002107400039443c402260b00e40c0c402500328801910120711800c41f11000800f228000300d040c90480350400d42e00344c1051b852901c10368400c140104501440c13595801d00700c03045d621a4101050395600380c2d00f50303400fa04000030000001d5034419050002e000e608002040042c0d0002109550b9150154000c21240c5075680141c0c51760013401c00d0300764040002500180d2141d90fa41c0305500300c6035050002c00c03143e44041d0055840c2c2c0b04190b6400c407040ca01304400d64098081e134407100c01d110009001c82003034655846102044901d5920030034000703001c0c07503c00c204040844ac608104c2d49107070310b1494500342c42c282559447e885241c80c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 324489181 1250 324487931 324487937
    0x81311010e12010f021b0601030c09090c0302040908031f0b0d090c080109080a0311040501090306200a050c0f0d021e1c2f07140411040608040b0a02070308010501 71
    0x6041001c0d80c0394110125180e160210080c001c400d030b002e11103030180d0003942030480390404c450b801c0728601c1c0c000903000d412030f0f410a585030b01446c14030354080041e0100101c140d54200e6042c1c800401038a4910851403010f00400710300d45c0f64140000329403a440444629004c0d00100c5c0d180034414420214210b0341d26995061001170031804525010b0051491940300030b00551802c1d00e0f80b810310030340d0402001404001e603010414250203411048a0340917500a003400115103800500c0050381c1d6a00900c1300f4030408140d5040b80c100e10003103540a500c00c0320300c0000181c010800c2d20590301d04110011030750301d255000d0441c214640800950702c0c4000381d04511100912074507041c440340b0510240c803030000c0040d036a044020007804060500d1b501410103004150b0040758540d4030741c00d01410006031040120241c40d01600e040076403e03d200181e54282c2d4000c0da2440030071181024000200002c006c15104c180c01c925041c10440f21200004140f520300f0350041042400007030b481904241507a00c242 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 324490431 1250 324489181 324489197
    0x5040b040b1207030309060302040b07060e01181506051c080a14041e06020102091e040b0d0b0403030c080c030115110a110f0d03020c061e0d05010608131101 69
    0x800054040c001807205540c01005002004000100200d4408107490294403461101e5a40790702c100c049201d02d100304a05060107002d1800014810b0f0001072149442d00004a40803148901c4140b40714061a401c441000e040180c0c1e0a00a400d4025940101400c440c0c0d0000b9000d607980340490700031030220080c040c040026040300d480340a5110401001c448540c1203882d90784800c00f030502c8400140c21b07003d02c034010600000f5501c0c41402102d0200b4000340265907903220160b9401c021900c070014155105844081c11152a2600711012441c58060b01241c01503003003074140501101d00381848a020801900f00700680d2172034440807a81101d50013410700d00e010410031001c80d0604030070942c0d0b6000d80520385980007441444c1c03444121901c0100c1d440001c0c4800d0708200303c0505002c40004000d0b0304100e92101c00762400c08013500740790051030360015100b07810b0b03449401c0b80d900110750400703c9640e54005203c880e0b03100c0e82c8030364041c1c018030203040c0c5500c168a407581500d4980440604004a00b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 324491681 1250 324490431 324490451
    0x1a03160515040b0a0206090c0a27020d0e070923011203141605070803030907091104080a0507063c11010c0c050f15061302120a06030219050108010504 66
    0x902100c005003009000f540d201c06822070000d40f40c0038250f0b074481c2c09104039041031015107041404d0004940b211040d60b01c25003c0c07000c80e10040030480c0c03107104403203a00380709240384001c00d809502003586009002d0000c0500b40000d0000302da041c005503c0004421100070300c41c90046945090544182d62284414600701d450b00b1560352202441000103560080307803210640442114808860348034401781c0710190b4030307500119501e000854212046c1d6106503070410101d4202d0b4020400045c036441c1d5240307000d071240c41c194034003410500c084031583d0244030200310039540b040e0f4074910b4465588100c80300d210350090302900005810040468602d0310780841a802d4005c030f6048010340c110720024441c03c0c002900182620210a9095802e409008140203101c08041819800c01c03442c1c2c6a0082c05444550510800c03100181040380c0540d402c10074241200660300d6254484d840c140c501280f450704620501810a0360203d188400e145140001d2026a03041040e19064500540f000903030b650103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 324492931 1250 324491681 324491719
    0x2100b150706020c01090602040305010c020d0e0616020306070503090f060613020306010e0d0501060501020f1c141e0910030b0901061b020402040906060e0604060e1c050f011a031605 80
    0x64030b001310b440c41d0301e050008420810030350042d000700d030b004900070080507811000990300d404003841000000740082d00700010a19010010b01f600c02201101c66514000c0e40c2d01103450a4000e079442d001149011082054060080001140d40708070200504101d080210200350310851300c2d00040e180c01d4000c0000f03560390344942c0b802c6c5000230717000300a02d4002c0c6141c20240d00818607401500c3c0140190000d5460349100010001c5207201d140f0286032401940b03100c1194105003640e00b0b80e9150714100201e80644039030070320f60500c005450850039910500c82d41044000c90031440c524062606011040e251965107194950440d41c041c00c1c04100501d404000c500100314001000b5800362021070b010942a00f950303c00402c0e2981d40e19501c202464040400080e40124405c100018110b00a010107a040c90181c4980c44611040310020b60011070341c43c0ca0800c1c1002c2c4190000380c0d560300d0185203a980c19020200f041c28140e015185402000740b22201c240c0c094060540140c440400303141c04054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 324494181 1250 324492931 324492937
    0x150b0a030f0e0102070c030b07020d1d03010912080901050601260903090315150103050c0301060c05030f0316020601053c0a0e040606090212070c0c03021c0302100b15070602 76
    0x34030b0030021503542e1810701d803009a01035507000540300c6409020000d8032540c00040c10b10031004040e110000348020310200c10700d0380724103070340c5260700340d500e6603460310014150b4100400501421b44440071f0ae850100801400c56800a04e11410000c20a5240c0340c000113a10301200481540c0e4207811903940c7d003c001d9031941c071403600d0301a003521864290501d00481b1428840c040c00440c00308030900043c0100445c140e030341c240c40d100c1d0f448208000410445020701e421119a510440589080045020031010b087c0c00407100b8007540003500c45041000c0d40e0622070740c1c0c09004225041002c007405d803101d007881c0c48100d050410100010801503168226000319821601100504001c46035454450311901c2c1201541d04071852401c0240100b1000341700d000b81e88032103030b130315001026655549404550700b01d00e0307520035901d00b546d0b4100480036803503143d0810380e18140c20000c80c000c943e00d807030001d10380342841440d0f070106441c0200841041e6582c174100041c04068104d56074480c400750a016000b84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 324495431 1250 324494181 324494201
    0x3020903011401060513080115120f02151c090c15050405030d0f0f05070b130201110d03020307020f0a0506040809060c10060603060605092d04050f0a150b0a030f 71
    0xa0b0065000050320780e801001024207000203602d100c46240d941c0465820b0f10b110203644c80b503009c8901014031514103010340c140811030007500c11005078100360b000700b4861002080501401e0200090f450305410800c0103800d466520b100003080290306549030454410090b014007599074200500d15a402486102941c0c054100101591408006050060400034008613280081020280c07010490fa0043c01a2241d031508800175200700c1c1d442c90f242088840204100b00d041c4600e002034140340c204108928070074142c20313482c01640d908002030b0113071600aa0034441241d95000d100404001070000c110a81c01680c00307041207850b84201c100081e41c6000d900e03100c000c203108561036442004019049041114101d031020000540c8410041300c039442441d40158004001c15101c16626a0841c1c001840c0d44503040d4580310350041c240020180d4405840041c0072160990500c06828140d01c92806141100c451209880c0c4c40c1503000780c540d00900103003074203141e503403441d0504a88054000b8407000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 324496681 1250 324495431 324495461
    0xa090e10090f020912070b04180f090b0f0c07050c091509090106061b080328091a06030105010315020315100c06050c0310140609040213030b061806010302090301 71
    0x40301d09412682c029000100118070602c801100205650303400700b40f1030b003900c44402c200e515040c2401175090110340a0580c0446645d5542107210300e40c041c03489080140c91251030201c40c582003041d0511440712002d8060710303100c02e04201010004500081500100205441c000030b01d0b9a0f1020119000701301c685142e400100000400011110640c403210603910192260003003191898203100c00d00c08010001030840c002040410b9000c03e555404040d040441607c0421201c80d01e07a2034010303501a0b010460306028484405100942481c11444d40060194020082c642c55031312202c031220345400d10f5407220741d400400f02d501c0000007840d00c11860005050703c0d94406903000c004000c1080c1c0c601c01d8a500c1c1c68500440c0044c043e090131a0b0103040440000c0460500b06210107141055000b0583d0b88070310100310603003131030303c40340080e244480071003140351075003865402c00b203081d2100144140c1c401c0b032182c45c1380b51032100c0000e0180d4011070203180050b107600803900800c0c01040840e10070049 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 324497931 1250 324496681 324496691
    0x90d1e0506190c0c11030f011e0509030a020a120507080a05040806060409050615060d1506110a02150f070c2c01120803041a10030303050106050a090e1009 68
    0xd1240014045019072100303042003071074903952015071007121814408039000405243c0303000080703240b41c80e0b94010140d004003650b01800303c0412a42c01c48003a4520541c0f5210071040b0300c0d00015040c13184617409216a070207036103468000340000751500c04d0304c440100a00c11215102c00d80c2c030320480c143c60201b94444210303a80e80204240c080c00542041c0315500b0644511000114107050502440e11150b40c072030b000700640e440b802d503188100441100b0668129000340802032101c00c0500401040c5280146100300d21030510000030505080f0300d8001040fa40040070201c0140c852599915415500135107494079001741020000c820b00c1003000281c61503c0e40c202c0490081101c07002402940c240c1c540024060303051384140c1c454903400340705819a610001040030702050a00005590091180f0208941c021030900418401c03901681d0b47d15540244590920030517400d8460a8050310081c1002e13030820074642d0005058480e980544407580340340002080e900756841c000c0e03001804078a030b41449 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 324499181 1250 324497931 324497933
    0x3090307060c080f07030e070512010f0906060302010834090308123102060702010c0c0e070f090506090d020307150804020901060c08030406021312050d17010803090d1e 74
    0xf201140070b84504502c42810800701e00d616009100381d41c14142c12002801c140c5291900708a1403102410214100e95240d42d450490b0746881e116006041c0d215403000110350b415400014442000149458403090817203403540200050040580c4405581003d413021a4070481c0048954900a0b840204080f0000c1101207030025a200880d100740c11944201d0307940310316032184101512108100c2c0c4441d5410400701005030070314600600321540107040000c1904920742d2451900740341540f1007000e222044080c8601c05038402c0380e84070400098a80240344608000000c2c031288285121184250291f0000c01c00b1518181311a00041c02042031a520400b803c034005020000700f15000ca12a43c800f500101d1306500070404034180d580c0007440c050566841d640d820000350300c0741440c031004140150740060b41c010619001c40344944074002808031100540c02c003a01804c078071030303200385000d0703010005110000001080d038180040c111012000582035082900040a11a101361907040c184030501d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 324500431 1250 324499181 324499187
    0x1a07020105160201020f04061407051f0f0c0912020411031911040f0b07050a08030106050a020105060a0b03061011010608030c0607030603080d05062d01020c0d120503090307060c 78
    0x20748509040d0384035850711107001d90104e08034401c00b4070100140e4410b201c14060b0510408150401c881a00300203403038504280c42d9103181c003402543d00c82c000d0181c12844440003289009035408150041401c0c02000c0350074001a00020702801070000d4102d07001000c40079540e45030000d00c0d82001d9540c003e90b99040c00205101e108030115040c0521320704104511000040070421a001c603542c200b0f8582c143e0742010100e445035800b200e01545e00348201c114000c08203549400a5000b408141c88440e41d40e44100b101909403003009041d1803142082900401c000c440c040b003120750108080b69000b030b0103900300381d00303603000141981c4c1074009603c0c0c00d40c04035541d40000003c04514a80c5000c035609560751400c210196400740c000140907440600c8210803402c123a07040a80c000c030f0020510a03607410300e5105a50040c82c0040d080700d80b2014828010310958043c40061a81941510032a4402c2e140c0c0d15124401a81c01c0c4408081003000800a1204030003842607680c070f02c0d80800c0a02c42d0040c155001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 324501681 1250 324500431 324500441
    0x1906030c1403070305060115050c070e06040f09030e040f18121103130b070c051801031b080303370504031b2102010204050a170d020312040f1a070201 66
    0x1910030320358600041c00750301c0c0c0050035808595020b001440c030390b801c005281c100703031401146000600070244484c01c01600c05001c81005050000405519880c0c6402080240d83c61740143c002200e16182402c00885c0e4004028030101c0e600b5540807541104261007100207100c0d941c042403900300610301d90b5040120034029043d4100040d600e10360382086100103a5124460020302d41000c100070081040400260400340c01202e0181400031559039550020421201c030b644044c9804000010040c0100907c10200703403005829401a42210b80c10040c0f2155680301c080c0400c6d241480200cbc40044003100c3d404415140724a1031843c802207441d000900c2c016100584007103011445600515480000180300781c1155500900d45000483c1d07203002035440740150501280840d5001c12000c02c8688400d54004000d119a243c40d065000700e0511150600080e0700c032440440d0000c01120100e0039164050b1904240c106011800030891440c3c4450b41361102c054100c0c260b001c0e40c2c10031030401e4042d441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 324502931 1250 324501681 324501689
    0x80604050609012306180108010c0207140105040e0613060e100e0601080a020c0c06030702070503060105180105060a050c120301090e06060a0b09010c05010603050102190507050c06031906030c 84
    0x220380c15500c074a0006401d9403112101c100918940e075074003402c2c0c02c1e284500c258020601801b10002803040304102205d940c0b090b005840160b440d1a00d00d00d0065042003081c00401c42d02402c1d00100e0341e1400001c2542c40786e40b09007030b43d403007000c030100f01180c0c0d81b5080014100d49014003049402c4c2d5822120916000403500e402c1c2e601044c50b000100103102d141da2034410841692070600503616144004020340060038901001c0c81516960ba40035140c0c00d0046001e6042134000b001028600400c061070010160030890080f030101e07101ca4420210b00510b03906644044410a440358840d900844041c0522800751131284600d03101c0d0415500ba210040d816240101402c3c0000a04032066969817032055403420740201c0746403010011f24040c1409804001c0d4149024107811900ba2680d5094035065001940c1c16540000c0128008440c2d00001022011a0410070f00b440040c0c3c48003074903070072040c519a00900b0300000082a000100c03904041c901d80f41c036000c1201903103e0528420720b04260103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 324504181 1250 324502931 324502933
    0xd090c0303081803190512090736091a040f1202030313080a140f22060c110609181b070b1b1303050c040f1e050705090a08060405 57
    0x408140c001008001d4409070b590090011868451140e85c00b100288078000345008202d424828911500f502105107030044990f034005014250030080d60702e100c1c1c82d01d03001c0c0c190007c0d405042030100400b004d15407414a010102d00284444007405e0070305c5034014682c100f08440c1104001c101c104039852002d84a413901030711120440071804002643d0b00d01c01541c400b00c191014640307001c000349400740208402d10745860400881094a0380d502c2c90340c4c02c510b8141c2d0300880e01040004c00d415400000d240c141030b900d0724452055223000e0003d0304100b002d6101800c5450001d50394005038850200320740581001402040310809006182002400152008107001d00d500741c15454204005054950594001c10b0018150b1210300344640a0803200001c14540c0505001906c02c0503140340e0f000c0700950040010b04501c0108504000031102d00308102c040b410310b80102c42c18100511205516030441e44880003405407030700b100c140c0305405250781040d80064214404a140031011a882d809107201740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 324505431 1250 324504181 324504197
    0x325020d17071416170a020a06110d020a050304120314010b130b030114031203060f061e0705060703180c27060612060906120b1e040b0105011205160e060d090c0303 72
    0x645040c917644100700101c001680116103420106503258864501085203250452424880001d040c050b41c0000070501c01141d4084100000e2248941500181d42071a1031304000c2c0b036031303609d040d1068a103042c000c2c0c0840340c40120740030b0114000090020040e040c078042c495125a035841031009000c0075010a1806400307001880f00344150366900f5130f0301942000b019110701c03950034410700c101500103d94510020741035074901001c81070103000400c0d007540648080c000c140390010000c0c003607075215940202c074240c500d01a070380440d0071041e035802a11f0064000e41ca08030003030b0050400d0080b08030b40c81041c1501d001070004510b5004600c0c100c070701c001e0320720a000d140e0352034240804a80d01841040041c6902c54080f00c001940c0402a5520800c1c0c00404049444c00c14410703010f01d44211001c0700d40d200f00c0d0005200a6070030020b0b81d07122114096092141d49402d9413401102800b0f0f115050a2040d45002e2005543d10708069a00d409203043d400c20007140c1c03504212419100c3c612040d80070410b41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 324506681 1250 324505431 324505463
    0x50a1b3207060f0c050304030210080915011d25030509010621080307090902030c0403110d0221190b0105040b0d03080f040303020d020325020d17071416 67
    0x32407890121100c81d161031020956040007516500f070b5460f011a00b50004100100040c0c0d11031151901200c46075540407034034900b03501c11524024a142c6070911070f00440c801000310600c5030b84000ca0010b8240b000f0307041601c512902c407040c2c00700e203085d0100541c00100311541d1142d0640c003007445002c00000a0051070f42e02c4010400b00e03040445203555101c1030011480c00f0030000d6000710b40021103031034500d0304079665500180482c0c0041d222400c188100090070000d10000c0c0502c0c1c015440100d4604005000940c001401d1001051100d40721102e0b0b0b95282041c40d905200050800b099458903419031805071070101180202400f49502c03451410101074117a09240c011508015815181c0030325a856081251696101c01130088080603000c10824244000900145004040f0b0407128540020b50890344a060b091190702d80007190700c100502c00f07000b54031a8078501440450342070054980c40c0c80f50f0486858000701c1c0071041c00a000a03a0700110b840851950306e10324040e50140344900a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 324507931 1250 324506681 324506683
    0x109050f030606061b0708070302030105010603021c0f06150801031202120307050c0a08190e060f070f0809030106060c11060a090e0a0f1b1403010501050a1b32 70
    0x2140c04116010792101c00001c20364244013004017200a0828185801010811902c3d45000310035002440d40750440c10741041141030900940d809041641019800c01d84103412240240c0d81d03c2e40064221606da140c18540c8011941c07090003e0701d642d81c9074000440004002403e45013084c84102c8404038403009200700030b48042110300f541d41c04001101e03d951105001211190041c0000f111a40149140c42c8001303000c2c0700091480380940c81c1071850300025510060149079030b5401940c090a02000703c0d00041540c042100e01c00b036488000041e16103102d080551a5000c0e120ba00c6406603c0e021000c0b0f60079030000c1c0791514191060080c84421441c803402d201242c018010800045500f07040e0a00944001c1190140e0107039050758000b680e00d440d200380d04152012024105802036400d0352000581754014942500605208d907258a907514000008100e4402c4220180c02c005640d01c81c01280300c00146022065500a640d00703102c00c141600a4000d801140150300043c00541c001c0002c06034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 324509181 1250 324507931 324507949
    0x1d04260a111902030a0213060806040609060c0e010207180212090a0c09090b0a0509030c0703080309012702150d15060807020c030618010204080f030d060501090b091c080304030806010905 82
    0x40e0160140405c081c046d03081c85100d0762070310a1804050b459140108042204018851155000b01c4010410f18481c3c10f1080817201070002240400c80500c02c60380b15030760001040700440c2d00e41c4007907d02c4803038180c104200034091444000d8040d8980c00500c0481d100c000340440440e0300842e82c4100c00303941c58004070201d4441c2d490050030080c1400c0011f2903440c00d03511080e844507091055070700d401d481e412084e06003021a003085402d02008800c0c000e81034002d101e500e609100110100c1c500e441044500d91a091040300000e100e0881c00e009400c55011140c2030300c025080c078070428010011903214a00c1404180c0c02840005640540043c0f5030034800100001c4080c0007801415260302c1d00d514403a03280c1603004c0c00291130342d000c00002a10344820821a03052510f4000590386980c01c400c011015584503a1125042081c2101e051028802c03074801c550165801311070381c0306009609030304181d50050503d005041c2e00070100401007070640002d4414800d910917a07504440c0c6481d5010808010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 324510431 1250 324509181 324509183
    0x220f0506120c030a0f09140105060d0302060a0b0d1709151206130b06040e010e0907081b04060e0412080117030409050c090301090302030c071d04260a1119 68
    0x100c80e81c000b0440000740e140095130042d00e010b40204070840700407100c1c0c0a0320380484088502070b520309490141c1100c288a0f0b41d402940840e0a44004201a14020754822003c0c1c144a46103584a00c90b00240e0385859106c00c02e075501000c0c0d0700022000002480361038000c000118008e4200d15840d10700300390b081085032800c83e15903008400c0380d21004284404c528a40d200e001030161f550380040c4483d030383c071030141000f0200c90520351019810040d0349908010040d00700403055120300414020440c000c12695003410398100d4440901d080c020004010b001981e100081801248052005004da9240303030341e013405020f880d018030a0742d035192042d054150740d405850180d001403209001503000350b00701c0c9030006818a041402c141206001070b08466150000b200940e20000d40c3d10710b6060240191001407260044a104955031100d80d2803001400800c014665504224040d603000911182041032201168401d40c44080035440a0711246813040000014410b505044802840c5140396003221 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 324511681 1250 324510431 324510457
    0x260106020d11012d090605090714090c031f03060c030c021e070b0d0e0d0801050907110703020906040f1b1403040c0308090612040501050f01120201080105090705220f0506 75
    0x24041c405070404c018400b200104081503294020f0300c000c199140905130040f01d00c000900702e01450043c0110050040d06000c40c0140341100030010b90b50007110640b54000510041591510300240030803040d0140c94000034400c41c9415085020243d159202c40c0b0511015000c07250302c2072600e44e40b140311100000307403000c5680c44407005002464420707000d0140990300c00d9000c03d82c803c4480040c4d08011403183c02000003035151004001c6403401300c0c007858200c54075090400b40480a041c0340c58072580c4031302002e4020740c20032001c0750041d120395006c5188070b880d2100410227103164200382e03407440c000604844001901901c0091010365a5000c4170702075a4891400c0e04000e00d9603071201082d0708880320640d4401c00610030000112485000584158410b00c0001042d20b41400c0d4111480f0b0180c2040078200c018094050060b60481c0156042d1b03002218400c407695101c0c4812134551203201c00648800c40100c5000e02d52900c80702101050b00c5855040b0b680c13594540d0309102d0035000381c13a001e01d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 324512931 1250 324511681 324511721
    0x1e0d150207021c0506190b0402040815010b0711010509010e040509010b0a2c0402060f0408010b0a090c050a11010f0c02030702130e0a030c0f0f08031e070c0201260106020d1101 77
    0x702110708043e580d1780b00e42c6c2c181c010505458050000d000c03a0016803040101c2d030809282022031030314840403140507011101c40b039402d00805480708250110070a5910303051141c00603940c5901d81c000c0005680c4420010400c2c0b06a103010081c085c060401407003100c1c0110ba0311580843c1d03002c1d140c143c0c078840c0c411074803d0f0214200c01c00c0d00090b0406001d0300680c0c002004003c85801105148001c102030100300c030010034061039120921241003a01d034001200d0301d1a1018082980307502c401201c008031110b191112401d007072034103128010619004e0000c0d22a1402c078004510a4012002e003403584e00841e001d4040001045800d8143ca0803005080c04a401540210300003a010784058009203000301d605000450181c0d98180700a003111106a03855a4040108001904076a449a0403040d05280700d40302401d000c2c101901400307000400a05101000d40c10b40c4540e204803844811b00da042d5103a480095a48040103034507902c80d2604040006c048107040020948140502c84450300310b120440a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 324514181 1250 324512931 324512941
    0x3010b1e04050c0c0a03030b130608070e01050303040506040b07240e060a02121f03170403140705011409061c0c02071401020a0204020d020c010c0521061e0d150207021c0506 76
    0x1000385070808c85690310014804c158000580148200c82c083c00681d00104000b90038103c22003007100050380083e00ca540200300502c010380795007096504a9403000a040d40790500d51510308868140c0910004c00030080102002c2d4001e91074002210503005402556225101d07074078038005a126020000740341d00030480205c0c0c850000b411350000901035021504080580f00e44e126541613694010030b80c0c01e03c502050a100744003044050220401c04440148078841c90700001810b2140c1510700074191800119034041281c4078a02180d003084020b80b07409015000000da848014005981c101005116001c0c000c00d04201103280101070358816001030510362201d0707003000083c1d4050410a540141c0a210107105600e003406000550903507520781176252079421a44008039803001340101e08104505060081c40e0300c0d2403150f80d041010b4a404c01c0110b000790030100f80070556074031000f004c603140211032030b140c9401d940c040c01e405407003140c0d0912011043c0105540d0180e01c6d1001509036086580890 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 324515431 1250 324514181 324514187
    0x9090506071407120f0e010201090302150a0605060706020d0506060408030702090606070605091509030a090b0d0605090109090b0f0c0316180906090b040c0207030303020903010b1e04050c0c0a03 85
    0x2040500c148203003840c03c03206554040b060301e50f5940702c001140486101c0f5a406030094158110b401c000e1008104900d00c1c0e0710025500e043c07170a4900c02c0502400301280403154150000e001810740901115901c80c06454210000e51204a40040e4903180c00c000c0764603032900e101154111041d4200850902c0c01035004c005000c040074007151f5220313008000000004016001c4ca0b449818010701420098243c1c20098180840050200f81240c1040045244840d0803603050002ea6150700310850722900e1042c40c01c402000c058101d141d0101288000003925031480d000104014820724204c441074480f1110b41410b032070280c458806884c41880020102d510285178800c0c0c240b214a4a41407618002054080100302904129042e0b511030109018032000c8d4052045080700c15101045004902d4100070346911250000500309500041d50403103603602508031407a1180300130240c000d003080c1000c81e240d004d07082424040c021424400011520b450078400c4c1c17540b14889001900220007180c1c0c0407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 324516681 1250 324515431 324515447
    0x80706081e010603020304020f270c0d02040b030106180302090105010e041d0309030f0a3f03021902010614100302070f0c1d0c0d0b130f0203010f0909050607 69
    0x55412020722940c01e03041551150514000d00309520011307a01c1c100f500500c800c20b04183c0105019070501240441160a5003442c0d4415080d6400148100e0710f511841d60518420300c4110080e0a00110340800c03e40d803440c00444c1201c0154075155113610f0365140e1110001036510020f54002000001003002e94000c0004e50b0514000070030008242d10081500908000c0b01c0034404195070000c100d111481c101040030b0709824401030000d0489010903924013090480d20400d0b1000510ba080d01082c0b0105280c02902c654110314000c0307140191040c80041c02900a00e030b000c0b14501d041d240e8142d4080c01031042600b910034245c03884a0040c8030f00b00b0300c400b200045200e6010540e0801c0180041591001c0810b1864403070f40b0300611052900c2c0742c034030101d22804c81c0010b039007155200b80b2905038524411200313071051101002c5100400b940001d800550843c3c0289111414044028095520307640194142d0b5600080d05c004141c580760050103c0307013001c40003862a03120b1000f046d6494050810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 324517931 1250 324516681 324516691
    0x70e060c031611010e031c0c1a040b04031412070e0d05011103010305010630022b061a0a3006061802070302030921010e03090901090608070608 63
    0xc5a02e0050000711100c1003000d078510a850918805240c1422581e010344950101c0354102c0080440d094802e20880d80c03460480e4131a0240070380d650602c07080000d400a0341c0000c1001000800d0b0620301410081d41400f811202107001840019019981c220040113a82c006001419001c0321a9034455040d154040d049070010303400160445001c002400c240102c04094402c0030525440c1d51461408a0941c1e140343c21440303004e00b100c80d02c1e10b00900b40c0100e8068448e07022910009000340c50010a51741014000752a0401d5149103222040780b194180282c1c5480c891441000717200e00c04c0444c5203000c8000c40c00a41c0c000c15140c0c04000415401d010f0340c1004002c4603180c121503458200095590807050030488a00340c540200308455103c0c01d215100c0980104020361918409a400948911507848914030981e1909402000804a01d01211607041480000c00080c031080c0c041c0f55032a0001300c20302e4460b1040d14004200d2440d180260012650218010194181415000d031240b60b00180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 324519181 1250 324517931 324517933
    0x190b18070e0118180605040b0622181a040b0f040f061509060201060f0b0403140f16090b0303280e18041e05190609060203041a010905070e060c 63
    0xc01043d030580f101481e00010401c0d0f50070002500a140680d0b42500d4456101510851800c84180c90b19100c26085485049600c4600003104414580840e44107001e0f07000001624041003000c01c8481c4d00740c0c801014a48076400081aa41c00d0341c00300410380f540c030705449401c001c1c001c28010840c1060b4000788444550840003207040c1c0c1c3c42d03e4542100350040d5980c40001072001c0390800103e60203100b1180900100130416582c1070500740e101c070491065110040040c0c00d07189036181c01d000300307106c540c042d00301d0b80c01610240204000518480d004034001c000300c0c0740c502000d440c054a0f00004940d0388007426800800722108040b00081d500070b003118990140201c101088020baa595aa640000d00d0000c0d0380414505142c01c00d007264800c0141c940c0080c0d80220741d00008a0400208240d620740401044c03003404e07920389003141c06480130341801002980080705000c108840900054446a01e6201c101802c1c5c1c0da0707113859400d07258103560580202d07460040380b9440f0305280c00204480005070b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 324520431 1250 324519181 324519197
    0x804060e060415020d0807020c0d030c0203010905060709080d0824030f1020070f20090a02030402030d08040f0204180209160207050102010e030d0504060b09190b18070e01 75
    0x840000c15030f8000c019082c010381050905c18400e039000040550045502e2000341182e0b040710000c540c0e01e020103400501480300d1520401c04650b000d4101c00840d6a0090540d203503818400c00107800c4040a0080c10349a0003440325030441940329809482c414140c41d00c0c00000c24606c00384201095032081e10360760301030141c00b0721440740710420031860643c1d0820010004510608040c81c0501242c2039000901c246810081c000204840141790340920303030403c074003051022900040b09010010234640d2900504200200203880c1c00550141d48914000d5041c1c500e01c0c44550822100743d0350482d0b0017000c6110f1506040c0250925a0000c80c45446180321010a20100d0300060300c0b801d000c0352240c40f900c40929102c040d01c5e5051100c500101002e0000b4001d0140c8410415201c1c0203a03040038140c0c6595000140510009800c030754a0680090030b08061424002400c004c3c4000403d0700c104040c0c10301ca202901c6081030464045c01ba00c0c0440c0e5010740f5241e52a013144c0320080500700b90304102c02c030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 324521681 1250 324520431 324520439
    0x80304080c3a140d0b061b010f0c05070b09030d0c09140f150c0309060313021e012102043b011a0304111201060e090a0503030f09030d181401090804060e0604 69
    0x91b0000f4840030085100b00c103082c90160881d44d00b542d1490b5150b85840e07081038520403031a41c0020179640503d40c03141c6c3c1035400360b0b11301400f24514000c44640001d9581851800c00c1c01a0708042c121060f980d901c80c501010100c0784c014824450807101e111a08154494400a1640f18000c007030300c00c1c2600002500d01d410340c150001031958100340d500914200e02801070404614000d84611400f80c00801c0c010794001d46c0c6000038021f06601000d0384020300105d1445541220320fa230403240a003050a004195150384010b00040248400003006d140001125141c01c000c20420203a5040721840350f000b8080050003520001d240d080500f048030400790441c2c1e01c29aa54640321715007101410368000148040c60130705480c0c900e04020b040900590000e503004c034081000401140d0b80140400c40110043d164102458658810726440d0221903240a01002c1c03406540c21550702d1490180111148000340000118220703110444010701c1c1042c108400c104890041044110a181c0248094100b6541e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 324522931 1250 324521681 324521689
    0x10e0c1f0309020604180b010306180902010e0d05010203010f0807140409020f0a08010507020d0528020a0503120a050a1404110103090c0b04090c1704080304080c3a140d0b 75
    0x507070404020401062441c12030300c40a8454030b5200c00027460107220092800088061003901202d8400c01c0d603841e40d44000a590040080c0b448900001c1c09032003545080f410858002e400030300562903204141400050f1440380090060150f40000d0100307840c031303880e0b08200320040074100c500300d07081410741d4810f0405964840e1020010003c520010425140601c2c0c020b0a0001c034a119105200c020b01c000714825028580c0e1585030300b1040508000c0007a018001d81c0f42014803135000704103200005000802c240c51000d111b0007400000710a00980d01c6511018081d180c64400400d064040d000002d000314145440840b003182d010304001603655210707101d2501c0c050183d007104100d51400101081103290364440d810002c5024034040254500070300e286280719902130b20281545401201060500c03220404450340403050100b245d11464102d44484410602d10b808140109403100070240340f003c482201d008080501d46d60844064140ea050b01c03c9034201c41c2d01c04891695640284080f615 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 324524181 1250 324522931 324522937
    0x31b030412090801060e01030b091504050c0913210e030d02010b0906040203090a060e10020315093d0308031e0c040b0f0d090605010b0c010e0c1f03090206 68
    0xc000c0703803403407540d000350070014045503415070207846144c1c5040c0040003108900b010b86410b5031350103020103c503600d41c140d41c01d24117040c814180541c00c4218040c4000c0000000c2e100c60060415140c0d01103a036103540182c1c90b40c403020340014000d2401807000d031940310500061409002c107581403491042803403001292510107141d002c0c0002d1303035480c08046000e2904410580c1d000b401140e0540c61860f1000603a038982400300c50090400d074450381034803c2e234802070140b11032240c0005801c5480340f40c20508814240c0384c403140580944850404100d44140c00e038541c1d06000050550444034801c4c040048a10030250035803d40440100800440010b80000003503000d069040b410394000d076400480b48d4800744024040e42c0c0c50401c1004100000c16008080e40c0030b00013215145900d034442d64012074043d00780c20710002c11561604002060141883d4041c04c0ca95551500800c9600c002e218100e036a03243d0b888416074000b4403107540501c034412210310320b603041c5501e190102d6184241c0d400306140ba0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 324525431 1250 324524181 324524183
    0x30203040c030c2304090321020f070b04030305090f210405040606030e0f030a0801050f04020717031b04031e150e06220c050f03070e040609020f01020f0c0402031b0304 74
    0x120640a130342104604980803031356120401c4908200e12941603070090542c000350409509508000803820940c800a58103503070a8001268403595038001c0340ca444010840b0450f01100442e2814002c40c2c01060300007405611401e40d0001002200300c8003a0081c4d05143d494485503905400f040f02183e19216070044400920b220b890104e4402e40c0f204005042503101d8071000d20541c01446130500d0303154024a41411954140e9030700308002d4508000c0b8010344070756100034041c10914080441c0201c4030f04001c0d403040c90700c07010195501d00d00c81529a142e11aa201c041c0010100a072118501030115810349002880b440f402999031051404000a4075084584001f0315000030302040705560304171460000003420164800001016503691481d500e00c58040d55000701c0142105408644040000102030a10f42140510901d07151404101403d880d2504a014056000807d442540005441810100003074090904c556212003480000c0d0001042040030300350203050501c048484038015800b0b0303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 324526681 1250 324525431 324525449
    0x2090a12201906080a0e010c0801060e01050f09090601020a020913021008010e070f0212040e180d051b070302042336030f1303060e010605090403030203040c030c 71
    0x69000c103040300d01d49406046840e01070465441c0a400c0c100c07011000c0d4040e5402d40c1080e481e5600c83c0c01c00c80c0300420784071400003450361a0989001c030260300041041d040701c410340c1d85c1a0b000e600900045406008090540303a861800307004134041494150722140d0b00074010700c111940c5841c9500020232005096408080c5003010594410560a00503010f0342200c0150a00da51603500d030a801700c0c079510000b0a00000c1204038900740180703501c02c0c024002a403820140039a00c5a03190f550b00b0841c458185e807001c501080300d1004880c03285021612401c100c1594442c0c90402e1950724451444001c0f4801400d0030340600c4e4000300050b42e40e442086690000c50455400e80041c4c001220301145014080d40c00720b00c03401c480d100e08102071100605109040786250207032241da02c007207503180d4014008541c0040b000800c8242d034042c11143c898084038025a02440b507a2640206c5901b20340c107601a59410800c010000341c0464000e400564029104000741c000c1c0c65a01d0b2070320b05490043d500a0108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 324527931 1250 324526681 324526703
    0x1f09050402030a06090c09050609040309030204051b030c040806150607080d0905030414010809010902100f090b121b070b01050d0f050604050c03071a090108070908030301080109031106040b0a02090a12 88
    0x347d9030303d40c89942d0b44030401307460340c0c005410141c5025107402d11500c8028841d03a06c0d00000390799030030283e07001e081c0c00102d5031441d610381c149038480001c280c115009241051007448000345841260025940174040040c2c000c9151100c1c1da110341d4015400310300d0300342107161035001c03202c0001d40800050006041050514600e03002d44400101015405051a41680e04020311100035a0701d1000c184080f112508042c130014002a00a07240e45105a00c04140300c0c0000c600003450349104480306100d41c90041e0940700303451804800114901030441c019110100050040c0000c0c10480440230500340a0f00708142e1340d01c9103588040c41c14804840450360703070308488440751603810104282000340100407403514064106151030403460207035600703041c1003064002c08101118003412803140a40051410749030750351303100c0c61214082d0510420440c00500c0309026039124402c08580140940d84c02407450201c0e13101c3e006042d010790000c0320850351104d1080c100150402e070248646c0c0e02144260390043c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 324529181 1250 324527931 324527939
    0x142d04150c11041b2003030f0907060f05091504080a121b02010e060310170a033c050c100501050a1217181203121f09050402030a06090c 60
    0x11a0040001600b030041d802c0215070203a01d0490040e135040300440f40340c00303068842c0513040c42500c440144020440790100105000f95841c4e0074459078403c0d00c2c0702045840e0b45036203017000c0701d8913945103e44a0000d803084c880400b640c82c00e40c42c2d61007003200303180040d07049c1900c5114203420042d156404990340c0380084400c0d04015046048002d0f441c0d00f01e41484950551500003270b281001540c8090300c145000400180100c8403410a80081e01d02d060012502d2030703800030360540da030031404402c0d40403444c0c550820168418500680351f2030510358210344164240c072806030b0500e60344020b0803403d1101c00e103c281604d1a0800000700f060540c030002080d25407500080c00031503e280c2d088118000c1c5100c40c0540815030480d4846c4041010241041d9162005141c0102e4100300f070500c0765111314149503030801000d002000c1c215440080030352080070380340e100b808120021480700117404d50a10000412040c14580d00242d800307030015003a641c106805517a0394048490001003211030403e5482c00b44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 324530431 1250 324529181 324529193
    0xa020a12020408031c09140a0515011d04050a120e0f030a0503220f091a010305040302070603020f0c030409090c090b0901121401110a142d04150c 64
    0x22148000080c8118a000e062048080d124031030091031020100d00560710162603401d541c8031501c100d40007220501c114118002c450b84451980340152600d10490741122141d80401b02c1c214100d41036072506030b800340490000240160001402594039000b01c42d0040f000c1003003044064030300ca20709d64500240702e5150041182800315810340034025032202c084034001030000403c541105a1303c41c070282c04522610800405512690050240000415400104160340b50020007007500015000645401041c00440880301c0480c0c000d001a84001010001d03d4001e5009000c2601c15807600c520700300d007143c0301030b14550080e400100219540c40142052080905056000e8048010140000c4c1170400005503006410300410302c1c0b1042048030181041161001940400c412000074441c06c08030f4198070046411110300b0b54089940c05000003200c207074420480e005584000311103d400b02070354640c441c40e610348151048114204120108140f40a4000948100119566852005220b103041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 324531681 1250 324530431 324530447
    0x10c03031e1d120301050609030a0c0b0417010b030a06020913110309070b04150f0c052b02070303020a06020a030608100614040203040201210b0a0810180f0b100b030a020a 75
    0x103207a42000341d00b606143c05801c2182e0441758100e418544031000c0000003801d2041441000f80304d0b00740d0110006803500214050f02c115055541403001820f080803110b03080e51200420a54145c109200c10340008803941c1c0902003207103000e8942071780d102c1d85803200d008940e2007050404010001004111400c1c50410403400500300310707800103042ca0321707003400c26403070116505595050005030b8041c062440d214103402d2501c15040b400f2501d0441900c1079511034420701680c82642829044491102c1c140001038140840398164001d058007000343c3c0310701001350000000300e0b0406072941400503d032141001a204071000203c40002c01c0b902c0c11a8908038a94103c0d805409540103104100143c0e0308010b460f0b40c525050540030f4100220711503000028111940e05541c0502c09680109150400248904107410b03280b07020841c2c05006c0c440100c942c4c03020400202440c0c0c00b0012140004d0992616680210101c0d008007030050301c0300d40c0908560012584450110b60100308800d480390310400b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 324532931 1250 324531681 324531731
    0xc08100b03060a02040317090102011118011409100804020301061d070306050108060105030109090302010b0a090b0102070f121b05030604031d192601020a03021c020414010c03031e 79
    0xb14941807035541c82c0100c00d407500440c7c422540c40420b403a0380070b900030340000c204065807a80e9565504080301d04e040c200d2444c42801e900141006902404c0c03401d6840441d22003010090841c058a20110720445a1007401802281c165494a50006a8103600007000e0f031901001c07605041149040403008003201c10360792185040042c18420b011642e6049803c890565079107010101e8104800d04040c1e01400c00c201240e9000a14000d0000b580ca81c958090181c4171426400d680c2d0f5155034108900c0e1803491409401c201c518100816000901c7c00c040402c0c0c4001d042c10900c03603c1303a480002a0a00c0402c07507059020a04000082600710040030440c8181102200d0041010503a0b0001c071004001500030701c5680340c803130700c23240e810650001c0721424803000000083d9915001040018081e401c8501041c1200e44414502c104007030b000d0095070b0036034081b91003807480204a400111f0f04904000c800743c05050380d9441c0700310201881c1c601142004040100810b00100c21912201d603940c00c405 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 324534181 1250 324532931 324532951
    0x50118090210050d090b070e01031d060a02090a030c0315060510020c0108100b1c05090d0f050913020c0a0b010b070803060409030e0a060f14070f0f0c08100b0306 71
    0x316001640c0c0c1404100040c0701910b030441d00c1e021201190b1000b090075210241c16401e440d420003c1c3c20703502c0078030224088401c2c0d03801d00c40720f445024526036004200000360700c590050f030002503c1250540c00b4000c407040003072081c1400c0d82e03130b921030600c004040d41054540340d502030a04800ac0c600d50240f540105001d8130031710a042e008201c020340740c0c2802d154842c100103184020400440120356500d000c0c20340e0395103941e0303202070a81406100f036030100c1920300b59900303000c000f5200b040003083c03040742d60300c403900c50b11004042d002c001c640603401000100d501c02c441c20340c0b406034031290748050320070402040300400903220107080804d1030840591080720704903010000c030f400140e602815260413040580d03010601412603c1c00b61000102c0c02415600403000d900c0029660381c0c0f091480f0403464050310307191f21441002c240c940081c45001e07030107440784080069520024014002001720a8000c8082c00740203a02c88440ea81844280340b03c3c207225540321090f0004516041c452690001c1c03100b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 324535431 1250 324534181 324534191
    0x5041505060304140106090e010506100f092723060306010b09190e04050615010531080d1d090108071503020d0525030c08060d0c03080c01050118 64
    0x80000d4442c0b00c0107000900006a1188418400000350808000b8080c3e02c1c5052103002e41407000c0380e0081408840e0a032007240f0a80d044414940540c44410b11a40f00c0d41d1950b852900300000c0e030b012448408220915462a0350844200b0007462203203000d040000740600f52038160182e030fa00714103200a04928030940100c03004000c546504411242021020f880c014040c1c040b0074007a0107065210fa2000300701c1d400d0202080200310b4041130303e9208442c0c41c07031030702d07041800a001110359008140785024010003c10740004c10030080010f2000115292201941c2c19441c3c16002e82031441050750200810000140c140c03003803200842202004609503080807980d032402804c00c0d514501441400040e6600352904100d580c4a07030100c0b408080350705405d0055003080c100d61201d180c0001c0c000300f0001e0312482082d2415229026850807880c5699a0042ca509d801341000b801c80c030b200500710340d101d0a10000200145084024081e08014000005015858004401445076104021480d401d2070f203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 324536681 1250 324535431 324535439
    0x20d020106060e0f04020d09030e0a060e0f090a090c0b0c101112061903150b030d1e0e03011a09010501180920070b01051005041a0d15090501050415 65
    0x85150f401601e02202c03e441e04800300c0002c100244101c1d41c0702c1016500f840010003c0c16006040407914420035070f400311500d0b5503400308035070341001100720991250134105586940d10f030540c4620341018440d800014242c000c0e594408010255511aa01c000000b080100343c10b0014040e48941c33020800003481074100f40c1d140324500703118400c0100d000310300700800f10300151100c003c0e520115089100000d90b80b40c5a040c100c1500d0412041131000380d040028608440c2000719525940c00c1143d1a20b030007401c0b4240d0600b032481e001134088400c014120440b20456902402051b0030440010200c600d80c0c5016000d100805a05800c12414040112451b0a21a4548031580304941003001c000451000701c48201e60034100c5c4480b09140a4004107012051002c404a1f050484004940c0d40481001c541c0d0142c0d624001c0b44102410012a0001c4001e52000e031001090941d00700400020219600000303002128510303080030050542c0ca00c01440030b41098481d4504200a00310b115004610f4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 324537931 1250 324536681 324536687
    0xd0c020f0c041806020304061503030302040e0a0b01170a320c04080303160509040c1215050a09020c030c030c0d081b030c07060e01020c01090201120b091303050705071203020d02010606 81
    0x43c4004081903800070000317040c0701c42a40014651140d214211000a60700c0c1002406074000d4050403000e8003075800421101c06492052020004040c0c5507900c0e40104c041c403080142600424081008d0b440b00211035122060030a440c00e04400032406500c1800c1c0550842c003078010080156400c00003c100602c55004000b0682e40d018059100504009900e80d00882e600e00491064507006030801e81c0024480303400001898401c4001d400820041e48502110b10f00d0a00300d10a240d0803110340300042c00240159001040301c07060903001c0740e04e8030700481465890765000da440005640c01000345141c3c010ba0005125410042003007452100e0000d0102c01c0301c1034880944440b10313005000540008000042c1c10001401803540001c540300c4001001d03881c081c2140c4178080340014211a000804c42201e445580d08000c0701624040d040c0d42da10089191408041ea400c0d400c0c490b0038007607500060070070041d00c0c010380544c080104180d002071074060f00d00050000782c0029641007250501c02994 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 324539181 1250 324537931 324537971
    0x7140706080c030406140c03040510090c06030c02070b0d06061b0305122d0108190503040905060a09060b0a112103060d08300910050a020d0c020f0c04 66
    0x2c1e40c15000741d482d00c036494010010401100c0740e8030480328002c20000c0311440131001c1c5100c2c13130048058441200c00d1012844c11140d03941e40080c064001c510341408614425440401e80074654011902c0580c1c0f10038401003690440f010031202c00e0b0301e0325024090603030b01c03000120b010404054001e6581340309036005401070203810b030300788050115100040e00d40e007410115041d40c51a100644001c1d40708144074291818003d01810916206060781ea055084903440b41c54065600a80994202805c00340004080c2001824190380803600203070218480580344100401083e82e000c43c2d0365620740b484005490381351300c03444120180d0482200c495550300c080800d801c80c8684078283d590b80307a60710030001c0d44140426001500c01540860740705003027446200c0f000c0d41d402c03c80c80d01c0705131b0500d03e184420309035404540c10040b50304540da011000b03440039000f0541000e908403015042c84280303001c1104641c4003419007001a441a01c48003114401030280c2c15100350190fa003409041000d45a84080d50 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 324540431 1250 324539181 324539191
    0x1030c020307031b06060b160c050109030b041103030705031b0105010909080307031d0703050a230304060f0507120c02010305150f01050904020909180f0606011d0a1503020714070608 80
    0x206031301040300c0030040d15503c442d001e0f00e500c41d03a10ba11503e80349800c00301250b42150407aa0712000c0303403020401d580074a802c201265072006103060035988559560790b141a04030049038152000b407040c0800508144040c2c1381c0c6100701e0050b14419661094420300792017060344036645442c41c000710070b0040b036031a908683d84101c035400c0110f40b050310a151240c0b0810710014500440c01003110110811a010a00c407032814021150200d05812000c0245845600409000d082c1d0b4001c000800c43c0d20300a079007044001c0c0080c10550304200e40e6844e420030400079980003400041e40c1801c4c6000319a058410345400c5107041c0001d819292040d00030951034121024400d06000011480009030b03661501150210316003e0a9000c250034044400c003588042d0213100440750151909942901c400000e00c00d10652059549110b5242d214050050051140c1400790300602d4081003c031344e441c0340d0781c40c80f08110b50a6400580d50340e0603003042110b0460305909295107410050082000b10b46c00130b00c2d943c0207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 324541681 1250 324540431 324540467
    0x3022719270b0a0506030601020703150605040b1f1b05030a031d010e37030e1003151a0705070806180a08040620070816080f0d030203090c0307090b01030c02030703 72
    0x203625800c0062b2326201890384001c02e00025420985205103154100000300c5005440502480028004224051030702040f41040c0e13030301d0f02c460b00105520441011940300910030100301e6100090b02c400c1d0859128480e41d9011a2302c4070040c41c184822446130340d01d8491188000c020a072300c6014180d840c1c3d13680181e65240d88001c0311910128030b0a1400a52010300302d010008429410f83c50007500d0a0b0707201d01024402e0b00002c10012880d4024052012900d40503a50f203607825080c480700b03103807441e00043c5030a142d45c2c0500c1100005031040280c500500004001000145040c4002248514080494810941004025500040b01481a40c096a44a0401e0f05140d81c100070152619503004a040240e4480d000707001030400c101151400c0c040700e03a860b0070111a80c41d603c1c500d42d81c3ca02001084026400013409484280c802d602030741e0411140d0b42a0340180341030000103840d0805076041306c0c45266880506860300d68141c0f007400c1d200c0450380055810101c00780c6028000f035003503100b200a2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 324542931 1250 324541681 324541687
    0x20109090b0118080a03031d060c03071223010506040f120f08040312090510020a12020705120c032808090303070c140301050703022719270b0a0506 65
    0x8268012005084280d80580c0040800c44da90b1040c50796582000a094020a20f0700070b004a0782c1e03c2046002c40e422042034018489620f4071b08805e03840b1750005203250104031601c64490001a10b0303000e401c003003c550701c8c1424043c0d581403100541c10300c0103921443c03054000b00700c10414201400c214000f102d010150810320700e100750800c55082074152000a0000600007004030401c0705600340d06840062716542c1e2030b1803d4030ba0061105200c420b000c540003580c0b2071341e02100000c20400780500c0314011071060342d109990302c40101c1c03028845030916a4240d00403111410310750a0800c00e20a00d114140301140c003d03c8400c0c143c2418811003100607140c01000104c0c550b07192230800448203c0c50744000d840b00501d40c1e910480b101c54a19000f22031081d400c020103d14018424006c2d60240b0000000141810000c2c01c2e01c0d40b075140ca480b02c6180c012802001c4080c9004450302c000d40102200c14268041240b2241c00384850030142aa03800c1c0c45280280360020368031a040450300ba520290380f41ca030707 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 324544181 1250 324542931 324542951
    0xb0906090303131e050601150809070f03023a030815090103020d03091505040303020f0a0c062001020c011410061b030302120108010e070602060c2a010c0c020f01050702010909 77
    0x3503500c442c00c4c1c018006128590000600c40c08900ea1a41c486089940d44002904c80ea884039865070440e1180c06030810039030200340050700d400751204018a400303c220010990340e03e000c0305a40c04d00820013150310450141404c0034580c00080742035101d0420030395203001206410000340f09803c10f0201a0141100c1900c1208242c01244210054000141c040c01d50000300080180b081e801808118010300920301c610301b000704002103e4007034030360000307078411060b041c5041140c507c000341049024a52003405900c3c0080001c0c4000c1440c540f05800126131044012883c82c0011409010307107030341801c00c010030003138285d2000580071100342081c210307805454541400c030080d0141414402c89002c11400004815805500074015500d100041d40e413183c0d83c62100742e8450a08582414403104200700d03403a079828401c1e0300e1030309402d1001a558000040c1c83c030340d0ba00f1604035031203400100c0d1100b221442585002e50146511000918003145003404960009000c0300a5100d00b224060701c0f100064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 324545431 1250 324544181 324544223
    0x306010905060f181302160c08061501030b03030d0905010b040516020a0b0703060e091e0f03030402060c070f0905040b060618042a120b0a06201203040b090609030313 73
    0x1400a0f0f83c5c0110039502d40c038a0551126101d03580c1501100c5041031f58000055408022814500c40c0900242071400b00c280c07000150003410048100ca54540020001241100c1301e602c0f0340000310b40600e0000641344803040c240000c645010f000078405060082101c00103950004403400105e500c0003d105c2d86480c1cae0034041d40500300640041410315103e40400c14020310016440044560300c045480c404800d0481050719181c00c0c2c40f27120580d400820006e0050705002005151007050a02151001941c459191900e03036000c0d040a51202c0c0c4610500c02485104684550001002c50300c9034541200081c01c2901c2c190406181d41c00b036a26500140c55844617100d440c1410b0019440e0740501c00d0402c0b20040011074100c681282e0745151440190041c1800903d4000740c44064803441d030201c4044903428524140350031140300314415081040301d032261010181d0301440c89040f252105042030030717480d03042102c0100b044080b54424410003084240b500050b11400b9040700c03503503071902d00741c0602e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 324546681 1250 324545431 324545449
    0xa120602040509010b070b060f010f1808010507050c0705010503060904030309060b03120c150103030503061203041a0711181f12080901020d02030c060c0309160b0306010905060f18 79
    0x20603070002c04400001405d614203401041c0301c3c0d1081080890958030142000554030204203900c0c00a0001c42281ca5014000d6021aa19842e00d102d1000c4040e030b03c01c1803034290b41d011580603000501c0402c840906a50401c6010003806003420002d08610f8201c010a030311450050000c7c00305500c6000400520215a0100a003013401809a680c5440745070010030301e982c0b00b410482c080380b040142e031b04601031040c043d85051343c1d0b055a40901c1c0d9102c0e04104110300e02c42520801a83c0820480000d6407541c0ea80b000300402d0100c411203443d90010b00344076075414010a20140101e05500004049250b03a8103140d60001c0c075900007680c45520045003c20b0751009030003020000242094101c02e01c1150005400300c414260300702c2c4c04c810480030040303889000c0c1030706080159020501103040c200725103002d1a4424002d5045800040c81d01c0030340c0e142101244d00100080700c0010600065580c082e5204020b070606864a500e052248080c9500d24403c00c0003018401d21a20303c07015941c0c0d00d072020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 324547931 1250 324546681 324546689
    0x403170c090d030810080c0603040605100807141302030f01030201031109090c2203050a03080417120f060102010e120f12040606090606210b1c050c0405060f0a12060204 74
    0x4008802c264519000d0030034041036a05004a0064000024016100240d140e0140201800c48d5043d61503964900c005041e02400322150354034090b4020a911804001c0000200700d03041e851421071103041d00380700880c60201c01d090341390b074010402c0007040d240c81c00790300c1d0440c3e9081c600041c50224440020805024090426078820600b00610035400d1540028000d40259100d80c2c0781c000000702c01c0c51581441500c030060082d0004400c500200740103541e0340e0750003400f030706130015220711800642c29158841c07007050b0002c1c10420244890704030680700b171540c090f900780020031550b41c152078415030b10f40400c0120020084e002071030380c04500c4010240c8a00044088c246240707811b042c07628101814642c00703000d100d0740c5460700014400f84a0003400c90341520040c06007800b25080420b1340080c02c5460b60030b54120b1000d0490b0400c4940e02c1016030342460040019040503a0540c00b04000e0702d2001d0505885148001d21180e4250344600510040300c241c280d4180704282c8030b140c080060b00883c0c0c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 324549181 1250 324547931 324547939
    0xb010e0f281d09010c021c12060e090f070f080304031401060521190c05060309011e020a03050c030f010b030703060b040e04020306180c060f0d05070306050a0e0403170c09 75
    0x418000031403103402009020b402040002e1084206210080b82c0c0e80901403547e200e45c4207103180b43c4580900522520307502140c1144082000e5072918840b071040b00b41912003458942c85400c9886820b5030600c840c001420240c2844c1d440d50349070421480e924019030002408076030400c88a0108101c00358001002030501034110741d101e142892640f0344410340903c155001d406515000018001c8108904a490354009040c50465080c0010f008450f04002d00c0c0300300540da585114080301e0074030b40345060300c4103400f4009a13580b41c3d0404000e09a8801a200000d400403c1c0144155010b40c401242d040d546c0502c0b105407078de134840c03501302e0107002d01e940701c1500140300140105032403699505080c4194002d504072040e03601d803805e01118501442c0f0130504250090700c5071405910f00310300100805101d0f00540303414a000b4200403011610250342d0000405d41c4e0b01c108114905201c0c2d0b80400030044000350100703914168401400d0101d0f44c510b608200b802e4540066400c5c0000c6d0180c0e007035102d010b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 324550431 1250 324549181 324549209
    0x6030b0105190804020a0b0c060403120f05180d0c0f35120f15060f0d0f020405030c18130201091e05041b1704030c05100b010e0f28 58
    0x8100685410f4095800313a000300080034003c00d1b00ca120108035580b0100f100300602c00d5aa031307524100c07401040003080105654544a07818001440c5016940c040c20103510b01954400c800c44200385401c07004c01a80e030900100703540041c042858001e044030f80f150080034690b103009044c80f00d820340c000d049433000c4500101c40b0114a207480e60030080c01355030f0350f20108160b894440800c807403081e08040300c10180c09450304c05100080e040200191203c0c901c030034607440c1800d085140d00da0540c0c01c203201c1c501219901180410152804001a80009a043e07964880d4460a101c0407202120010007540c0948402a4208216442101e20500400200340845882c1c203889000c403680030110f00c205403055080c1035002c04540680110341010507040c0c0c84070041e6803c1107000110740c0e00001d0094050141810380100810010f00004d60b24007140e001c00a09061403c001411001007944107501807918584036083e0381d11071482e000b0031940302d200600c0d01c20720401164080d40d0030070303040b128902d0003113 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 324551681 1250 324550431 324550477
    0x7081c030f051f05030c241e0c0c01080609340c050715081302030c0409050a03080f07021f020d060b07050114060a03060f111602010215040c050d030e03071d060a0503060106030b0105 80
    0x88406807501c4c2c0f0612701a98200b12410b801191900c209a5800c1c1d800007181d00890106071401f01c7c9164010300f0f403160000b40710a443c408443c060521100e06000c0b070152030101c0b040100078010b0101504050111401e01c980500c0d0080080d40c0042c1003d0204401c41c50400c259075007000145d010400041050043c0d620510341b2a0319120f5504044000c00d80c100e0200e090b0001460456204102d00d074001c0444e81440c0250704082402d080001ca6000d13420484850012024010380d40501040002255100c006240080c00c45407003002c4e01d8580b250180c02c2c014196a520040800c480e0000d0380422110181030380320004042403060100304450009a887c84001700d84000b1101b40d000760241d426615000769880d21100044400900f03d00380fa520500452a0912035003109034000c0c40d120b4441c0c071044000c42c0c60690f068100c541d40071030006901580941c44584194481000c0e00c010043d20320b03100c01310b40e44482c180551000c0c5621101e150410381d2049054609085030843e00f10802d800d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 324552931 1250 324551681 324551737
    0x108240105210a14090c1309020a030b010909050f0309060a0f02030d060305010b0f030c09070c03020a0605040305031519091a030105161107081c030f051f05030c24 72
    0x1200342d0340c001085900c1c0000c10400d4041841d40b50080b0140000b44c100c0310342c0007200c0c002e002d1000c0883e481030400100bc404078450b0400705010b00b500400000d41d4806078109603140002c4001030120551007009482800e8070b5043c280c5203000032078209900c2c208003501042c0d046000c2c00e185403004501d40309000041c814150001d0142400c20703991038004010074020f01d070b2604038034000c694200c00b0f0302001c074114034403410741a201e1700d00034410349000d0803040d43c4c0d000075242d05860541c00103401105101031003014415403007500710102d400c001407101e602070f550101e042c54490241026a00c0d03007103c510307003411400000b00ca036005000304041e01e440c1e020254400c070f01c49400000a8024030f0700080d9140c0005504041e04c064500a05202e0301c00080c1d031890151034039000b8101511807404100d450801e0140034083c50030002e44d40c20103020089a4401c6c8416039010034481c0d488000844402c0d140c0b01c0840c204110710082d007440421040c099802544039034926140c0440310003d4186a2070350b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 324554181 1250 324552931 324552941
    0x406180c031205090108040f0203071211090609040302060a05091f02180108060d0602030402030313030f12050a0f03020306030c060708030106030f140106030b01020f0712020108240105210a 83
    0x84145030b2621003181c0c03200222a50300850240a001c51500c001180100d4880c0c5550f00d0b085200500701e9203000d803181108042c0c10001042254031000d4032014000c10b1501d0450603170b02510980d4030254918180e10002e60724200a00b03c2d0324083d44d100089031a034081404042c40b86400440f10b0b49404904d500c2d200b0007581300180c0400c19031082c0d407e05469602c0b549059001d900300030312184480e00aa12040c001350b00182003240c0c148070401c1030843e180004903462000310f0154200620b008800c3c00c04000355020b0399900010007504007c603886032030300701c00294500308003450010784941d00d40e40402d29100102c200035500c040c0100e14102080a640001e5041c1c4203240e400b8010100c1107901c034400d984101c0b107421070710343c0400c006124052113a880140581414411201c110303204001003800c00c035040d000002c1042c0c0030f07c00c09040d542c200c1c07002508005007802009110984030003000f040445155080d04000000410142a5042071024901e02050907940c1d03405003420f03850180100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 324555431 1250 324554181 324554183
    0xb0622081e010e060103083c0702031009031e11033417030604180506070f0c0b180307050609010203100e040302060402040b0427050705120a08030406180c03 69
    0x50f00f8052250003000c408980b0f40d0480e40e002c4015030800d6980c915a4150074650356415448006001304181e010b62210b90020260f100904000d5403000103006050a00680d85400c3c15007a0810000c1d1002076840090001e0300a20942e8103000d107074901208a503984001080880244004600706182950300810f400201002c01c10540140b03281d8506202220144180030b03002d08080e02035031078100c41403001940e000ca801400015890b405a0300b80c0c00e80c0c3e00b0b00301d096500d81c0c001410800415080310300f00c2c901c5003483c20280c80d040d00a0351003045041001f080c1000b5039080200140360394401700f0980b000d00d9409802d864442c5020440d00e4000d40048800c031070140403608001400b0300c070000d0b4a038020360f05a80030b0006a5555000c0c00050b0501c98103a940003a030720011814203034400007803000300d80780c41105611819420300f4200c0c606040da40049202c2e45c88038844110856000408005c425404103445480703988504200c001000c1070070030460140396001c0003030704018248070300320156 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 324556681 1250 324555431 324555433
    0x2310e010e060603070b0301090203060d1509050c1c170702100c11120c01030b060f0a02010614100504150c0b011202040c0509100507060e0a0c0807090b0622081e 71
    0xf550f848040542d038084034072031179031042c0c010801844403200030780041d80d201d800945090015003159803030803050a41c111000e800307665201251001c2260030300140e01c03000e00445140320304802984058031030034440c3c0e40060000300300781d0300c00175201550340a9402e881c0c0c00910b04034440c0d441c44005044089404022107103814544021321040ca050385000c087c0008180040581c0c102280c0150000c2c038000d080c00e07620032000c0c02030041018203a0005c1404800c250b0002c29464540503403000c52130b0502c1d00017440355444143d2500c6159100050f24201c0d0f50500c0303081601255042c0036109138800810143c095494203002080b90031000c8141c80405100f51810400704a40010417185406405084e50740080c504a944807c0c40c840e0010f4405540908000603142d20403c80d444d10b4451907101c104c0e000700c0c0300001040035041c14403506004016020062001141d464006a0548151100040f41180e55441e9264505800305a10050050001118013103810062090901c2d100a55201d0b00c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 324557931 1250 324556681 324556693
    0x5010b060f090d021207060e0a05030106050102151f030c050112050402091f091406120105040201050702061b0a03021b0d020d060903050f0d020403060e01020702310e010e 75
    0x903040c14000c9400c118200c826080c10504984200080c0e6110003000380d030700060b000800541d209080c80110020807040c0c80e40a103020340c580c140003003540160701952003a4904602041035903004030f0354041542088183c1101d40d91031030000307094800c00b44442140500341280200402c000380c003210341501d00c2602e91000c0c0300b034002d05040c00d66000710780007500051100c000c241c10042611060101104441c080800c250b11181c0410803a4020344801c0a00c12524060000c3d5051070000311a9444e5a40300a01c158545032700041c180c1e114005000780030760000500c3e0f041c4440c1a00c00d080c00008124203031034002c0c105040c009c1d65150489000406107281180c510716034a40303108010f8090383e0152015a82161903200c40e0010001c1c3c0b00709906000b0100040716030502c00d0801460106044880140c031141903040c0801210450140b1040c140e10400444000d41d07650a035800740c2191003521900240e40c1c6007080c500309801c03402649000d030b00f01424a03154013410b412402045a84d0000c48403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 324559181 1250 324557931 324557951
    0xe060103060e1501050d09050604050c1002070305030f18060a08150409021f020132070e01021e030405180103061401050d0305070c0e0c0c0c0901060203041e0911070501 74
    0x3036241030996145003901c00f03400e1070610550180018000d04201e03048002180341d40d54548900300001105c00311000e03040f001c48541c007071504015000007540303a4401040401d00f556200d030340c1e91085200c01d44046001182d204010246122414002c0340d010b40500d490f803695140150080c0c5041c3c4001c01102104e50860440341414840c0700401a00244050041d0614814183d80507581011640c2195201c040b080300b181805404091041c5007200c0454110348c03541394446070108041d0101042100404031002036a07800200e5044000130443c03220403005440b00024a10721543d071003a43c000903050342c07502c20340203d040c032079040b0ba004a0b8103000c038181800d24284120002d00038a9030051002c26864086846200a840c445101d6000c0c40605920765050a0494004580c184c2c03000781c002642201d00c04052001c500046000d50764612194100200039440e8000c50040d1460811448001281600c20104400080503c0307103003044620307509007010505611070101602c0541c24459211 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 324560431 1250 324559181 324559199
    0x90504020906040e180304030b010e0703060303080f090a05060a091403040509131a0103080307120b13020a090e1303020f0a0c09020c01020c01050a0e07120503070303020f130e06010306 81
    0x50301404010082403070103007894a8113899000190090403201d0a802e0003c1403043c081000f0000785010300c10100c40c540c50982c00f548181001041141018100081000002c0e08040020342001c3c60300400c4c1181e40d0761544892030140c080c80c003d0042c2c416030040c840e491019900c04400c45d03000c1c00001c0000411000b040d660b03032049108450f044050480002c441843c410255a1010f10400c006004001c41c05810703034501000303800c140c44440d00041030008090300022000c041a030130740c4081c40300003241000194008444600291079580000b20500410310030400c06001c2c0001000022081c200042100411110004102d0240c8178010b01c0a4240800054414080758400d4004100601b003480413006900030b2201c0b0300481d9006c0c03144d503444440c280a054865000e0100010f1b5a85e005041140f0380512584100000c2c2e01e40c1c403452000c500040221800b03e80c00d403c0240c0c0d100e00d0313440c2c0400385100f10101d100103a030b290100450280402028180500006daa060144a4a5990711 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 324561681 1250 324560431 324560437
    0x1807020f03070507061103070b04030f08060405040c0308090105070b0c04050315280e032209140402060306180708041205030c0703081b04080708010c180e060303071502090109050402 80
    0x5490f66010f0078080083d00e02c64240c0c0280300b1001c00541c2c0c100f01d40c0d03580d240c100313207800d54040f0081070704100084442940b26000c60742c84041204c1c04e000a00381500e414040d020107010103840c0e503c1c00114a00780f41d008070202e4001c15802540381c212460b04000e94081500700340600e41c4207003d41482d41602640842c3c029010b104002d80c0060320005109685442c02180c20f0000c40040d1140d006c0c2441082c240b001d0010070091142c05401510903401b51415414103401ca240450f16102ca0015034100070911140d0055060700c10a0780c0c0e441d07010014203c604040200751218842000b086110b43c0d2003403903075001d5071151008841e003d028a6042c1c0c0d0f2800110340c1d288034803e040c00550b000c284200d06040e0000382c43d403810481d020003040e5120040e1700c0340c1c00405903a0700038801004099000d00ca00380882c003d51500799440602c076400c0103207a080707030710521440312203410104460340d07414012250403a620183c118640c8560095900194011601c45800b1070144000060300d42010300803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 324562931 1250 324561681 324561683
    0xf030f0b060406080d230c01050717090a031206030f1a010608040b0c030709050303030702010b010908060105150a030f091118090d030c0909061410030b1f030b1807020f0307 76
    0x1808410800042c11a200040c1320001d0000e11103c291250f40710b001b00e0000c0c980907020384004621407416100250641c0180c1c40d04800c13407416a001c01c0f20a000104a40c00e119030b2501e84001003500c1c0c14196405401c26400140405101503000400c000c08034441587c0743c500c1e0102002a40c0c0c0c1e030700c02a40c0c820812034024200314420030001d41c1c1c60203480000c692040c0c0c80e0815802175901c03078001c249150011140607015039918071280302c40d91b03040344100e030080104070300820b07031581000702141c80c1c202c00d0450f20190407004512080c8060003078000340580600703111b040000030b01600f01015040040c1c00c18900800394200043c00b2421500c200354441d00343c0000521443c0341c2070f03208a00074108085024108049540e0120705000c1c2da00501f0020030030b02900c804642a0700b410024203080c80d00241052502d4212015543e071904034244200107190f10f11150003418500080e0080c0440c10780041c1d00142c80b05031000f0120402d03480754010032580d421280b1442207039022036a60f200700c043c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 324564181 1250 324562931 324562933
    0xe090606040f1826091e0d0f060212060607230a0507030602041a030114041104030b090706030e010c02030714071203030501080c040c050304110a0f030f0b06040608 72
    0x1001565074245a0003501d00c2c40e08480c00066814500350500000c16150001141c02181e607480154040243c01c18010090b41d41c2481d07149800f0071000024a6804924580301c1d500540611486195440a4007940c59a41100d00c014070344401d845c060000354811003002490724130700c0c40480d81c603042843c2502c0d040b56000580c54070040400d490703000203002801d0140400c0c420903d03170000044050040d00e00441c407070701025803a6418160604440e84c651403060701104000c1c00108150313030f84441c0c0d00d0301c200000c0e100080c0003104120582d50911558201600000403e820320004117800560076044510316070b030401c041071a41280d242a9207101c4030290060748140030710801724008031180490568008111042141d840c100c51405e2420701100380c000c2562240100860715090102116405088504000740c400c13140001e0054040a000642154039031f0000d00000e0316000d0348200130b000c40c1d4051f03c0107d60740c6e207003100c440f100d2000d040b903001f1041800300700f290500740914416295528 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 324565431 1250 324564181 324564193
    0xa15060f171e03041503021209010504020303072009090309030120040e13020409030203070b0106170c0a0c0c140a12120f051204140c010c08090d020411040f030c0e09 73
    0x542c0402049040744140749160104002c0002c0c41442c1070b5104140d400796032805621004030b61801030ba4580c000305a060941d051904000050b6400b2048070301450380115146401040040b2440c007180d50b01216940004c0f00ac01801000300000010380303000f070b070210000c0c8014289076080000c0b080b0f0f9442070f0301c450340080c0b109200c40c0b40c011190640c00908158031490ba40600e40000f030913607210702e00540143c1c20000340c800500101c1800c9501511440c100450b01ca4203d6241003440070004260328211000421b0300b0031500d03c15071034600600c0e0031000e1000c203251105028044c208600d40142d00c80e07100050300040b45039170204142c807402d401041e008541c03100c82c10142c0d2240440d0000104004c41000922030303020782c20300c0c0103004034024150300c2c0070707842c0040e0f00ea4030b4400c0c1c0040580c10720aa0360708060000d01720710111781407c0d8003590600c0c0c2245603803020801802d01807000c1c041d10807011802240b103200c052951000c8074050f01890300e2060b40d44031400d00014040d0350500f0036070001c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 324566681 1250 324565431 324565453
    0x11514090f030a0c0b03100b0c0a0605041b0803040f06031a010f091a09010318052509061806051203040b0a0e041a0f011d120a15060f17 60
    0x1e6010703460648040c0c01d42d0341e002465610491400003d81000a01c1480442842410080c40a20750301401c1c0040b07802e0716003804026202d5889203010801000d103611b8200103001c0000c58620f8110b40e00c256180c520042e52203c2c2d242e6100d4100340a081004101c004000400b60b09c2800703050040c40000c0350000c0100030003401150074030748061502d4140100b840c00040c00004c000050200d9501003201d045c0c0b00c01c100b02c00103041d24008001c00d06e469100f4800c042c0490300104041c00c01c84031840080903642090315160000c0b485a5200c101030341d1030b04100040720034008414024400360401c00f080001d07199004c21410044000180c54a984180024000400703c1b20080888400c4c5080c4910680500c50002d000d442d40e0500708100610322803501c00860030f0040f171036001480242840440111001d000041030401d000707415205150038164500da284041c443d4181d031507000170301c0e0f003803190844c02418060909072007a034485511a00340007030395840803186044400702c000050940d0030307a2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 324567931 1250 324566681 324566689
    0x6050919021314040609020a1d0a091e030e041113140307051e040f0509030f160212060f0a020f030609250e040f06050f060a0201090605040b01151409 66
    0x801c40159421998401c5016441d40312000c10f00d10a503c00c0c01c011510a68070310510804146c0d42d4041300c02101c0388880400107100c03e4268950140b1308800000c4c0f05109030070b102405400c140c00e50256600550402d0303040c59401912072021140945041c0410b1414231040f049510079800b0030115414089828420301507400ea0002400742c00034111042d41d0349500000e100b0780f421380032410340010100d0b280c0100e810729016035040030080d250300300f00c1c83c604458041c0d100e11409060710202c02c0d0006140c605a94a4882c896640750041d01078800c0504d05030145548500541c0c4640c00b103c070301300000c3c480d002240200ca501791802e801c0c1606585a02051000313085000e0f03c4500220a01014100c01c1c0c07082882d11100a103071a51454081d50104040c40200c2c3d040c4e0302e075400041d00b800b00c1030105490300350454070a544140e62090752121890005c0740103041d00840245401e0910003031200f03000303489861505031500b094180d20f0034082c8100c2960324940c140001d49001405002100d12490 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 324569181 1250 324567931 324567949
    0x60a061b05070513020a08070804080f0a03061a030117060702030901031805010f150503030f04050f0109030b090d03050a2f070803010909050c01021603020d0602090409030c0605091902 81
    0x40700d801210395240e1101c0c0050160211442d00158140d80400c0042e013071a4048511600480380d03003002640b41c20161160a028403803081003080b000c40005613118031522990040c00180f200c50007441002c049880e540540364028806d00104c0c240300b030030803a840c0d88040344150003901c407a0010f6140131045001900606003c03070081c00741080030014000132405c28040d81861340c51860380026904000364059a010759160040c0380250b00a00010900c0c010540464090300c2040b604003070b00d0b500c5a40102d444603000e40004100103002e01c10310800d290005006900d1300b000d0786042c0700e82c0ea1400c20100403910401d40e90f100c50500d08030b094040c00003615142da0a15401a40d4502c1c0001a031207202e01503200380d00c102020760f80c564041050242c28020b04071400424070113032030744032182e040600c0042d04901000e8491440d85100408000165044540c070761000362080c030680b0450305000d043c0010004003500c04604107030008885420214100d480194681040c024072401902030000c100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 324570431 1250 324569181 324569183
    0x180c0302040b07050604140708061504110c010e0106090209060306151b071e030309170c0406060302030f06041e020310080a08030108010c0f0503071809050c0909060a061b 75
    0x9682044040ba060303100c5401400054059002003916050903d4103c0f03440151415052180c1c00844043c030405034081500c84e0000c03880e0145401390b0708000700040c000c002d85282c3c0e142200700002c2c50082c0c0003041d0040074418040030002c200c0c0700d03912540070042e441202c0910f030b4032100801c0010450329006e607603003c425a212075a01e0038040ea8981208003090010b030002035560100108000280c1070100d199142e0209420411006195540260a0147c5802840e2140074a01c0c02945285010403d03440e40e85001801480100d5440001400035401518640500c0c01f815000070098241030084e40304180140301038601d200015a8410700940000e4040071001c11030700f00000b5180b500f003020700889406801c82540e2545080b07005401c680d0440d50003400d108440d58040e01c1d44d0707080300950741d101c00300d070034681090302c544012480d80c2d080d150441e0251f540340c041440b0070708552030080d019814040e5120360b07403502c07000d04018807040188107210000d1000615440c1d0004100314010103a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 324571681 1250 324570431 324570437
    0x40804170c060f04170f0316050f03030f07030c0903030e0d020d0c03030819060303090b07051006080106080708010203090309120a060c1e110703031d0904080a020c0a180c 75
    0x1e01e1900c0008609911003402c00750401d4010405103e0b50000c0302c0c51500e081006401401d0300b6070600310003038882c0038004440181c0ca0031910203200344081030118120860b440d0003629070724580780305401074050040e90304d84006440c000046a000703006803514010749402d5103860101101c650200031070b0000001040360031180789014036000450102c00500036500ca500c0c0c0d8100d500d0403034031265070384480340320341c80c80e05003406820070101c2d420020034415260140780190340c2d0400340c00c00ca4a4009074494049a0070301d416000141c1d08819480902550000003d554001d40d03501c850fa801d07400265507071a020b8000300f01364078451400e101c49811b62201d020944004103850b031642d10496800103a04e10226032b0102c411820000140d0b0ba8445200e118280505504451070900c4e42d18150380c04002c1c140441d0100341c00381c80203a1080c4c1e281d10700707000707220f0b034030310701d0a49084455904204080c5000d4031a40741504041c2c60000d011009540740b88080c0c00210b03260032070f6607007c1d0007290740b41014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 324572931 1250 324571681 324571693
    0xc060806130c260a2007020108061206132906120a0227010504020f0703111c260c0315180103140706020309010f0c060b030607020604150504080417 65
    0xc0d000742c03c01c0007240c0c0030034042102d4291808104040c103640901c41d100d840742c0b0b04103481c24901080072040c1c988032a0203191402e62966114040b5545d4544506201160302c114410414070111007001b5120451194149503402981344000040d201100041d180000f11032100185ca01c0c01d01510083e1080880b1007182c11690700d94022840c040f04407221880c0c9007002d440d1044030400a101d00320f00400081e00c0443c603200c407521250200340185c000003420800da20b641e22003054010800d09542c0c0808400101c9075038160500074202005490b4104048185000781031921920103e62512541845040e03a15550f00c21b030f05040680c18107034845500122160001500000da103c001e4060b5110707448407411460080d0582c1e150139826444002154000c100c0e103401668003062601c996581814003480005448c50840c0181640c181160f4052040f1410800641d90020710240a1405429459510841d0302040c5003500da044a000d0300c5450b0811003002a9000d10005151207609a400d82e11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 324574181 1250 324572931 324572957
    0x30609020d140607090f1805070c080a0c0b06040b0114070305041a180a031203090f020303072906090106051c091103010f0203060d0206070201050f0c0a0c060806130c 73
    0x89031542a610b48100740d00c0740307040004050300503603004094850407102041c1c46141c8418445100501c036001070304583c480000c101001d0280d207008030419804020252900c6055000a21405000400b0b40301d0300020300c0803940d2810103109e40700700c000b8181d445105005003240c0303d00d40c2c2d40c401c0030214104142040002a04110210401c01c0c00b00c200914651350011141c0c01c0d02c107600001b081c2d274413034200002d00300006010009814010045410045101d4416080c0448800c01c000401794060000042c80c20030070142d6002d0b44040401d036668001682c510102100c854403049a05070f800070008001481600d020300d002d00504a14a41d00c1c040407000101c2c02000e84070203510494844200c42500c0c8114602805610045180e85004604510781000001ea60b410702060190041600140c0107055900c81c0307044550791110b86e89290b544411400405079510003020068814004130340e400301c2e0103842815424000c180041c584c2c20703040844109100101200302016041c802c0000d46c0203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 324575431 1250 324574181 324574193
    0xd231519140111061510021002040f03020a1e030b1005030f0705030f0c01091401020f06010f090f0612060e010e070e0405010b0916140d06270510030609020d 69
    0x401600c0c0801c00000054000400581100d4441d80c0c003a980e600002c0030000d00c41c060500000030b1150848075840411030120080c0d08001036801c204001c02c1c000600454060241c0ba10642124400d07114100542d5980307506904000b03055400c0001d0310000c40003040818020085560000b13035544019610700c0e80c401c0003a01e03151103240051066001070301d08100e40c0c9002d02515409040c942c0281c1500000000000d04414880c0140e0640641c1e074500701c0050392007000707404a046c0c803400c1140c9081d40c4540c4260400811481005401802e18000c065911640e004580480710406000d203000080c0f43d0310072000e09110b09070050076650b2181c2001c50000200300010060000345120074841c00c141c00c210b401d41e070074400c045010342000e0060045000c158000c0c0c200342450341ca030808005200c0300f00e0200c80c2c800c100362202058100840454400c044144c01c109112030081e04407c81046840e2580a88408407940346000c40266002c0010070243d4002d10800c5100801e40b40403020341e59515 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 324576681 1250 324575431 324575479
    0x16120603030206090d05090d0b27390d0804080d050d06050301061202090a0b04050109090c08010608030702010c080904020f0d05060f091911190f0503010b0d020c0118080d2315 77
    0x16042540b1860140310020f11104180010b403024408c000451103800041e001c11101d43c800e890b0003001c40034cc15070700380507982041d11301614405003070701c50b08034210400902030340041c002580c41510300080000c0c1403030140305100c101c031041400030170b15007503640070850080b03001400003007000e440b03d606c00d14a6442d80b04080c0a030032588000502c800c03140c11f05d964004026003150905038540b10040c081402c002098424031740d0309182036000201d5518102d43c45000b110700c5075420600200d04c0803500c01541c8050400940e081204111560302c100c02c01051401070044a5003200e409404110440d200c141d64102039000010080740c0c8640040075122603030b101c0e04100340e014200000f0801c4654bc052000340300440300786817080c2903504100412040c0d00c200e040d0f440c1d900f0350010f041c0072601d2082d000070347d907000c1c0e168000100e00b207942000e40340d5500050070144503c0c039103501600c0c49211500345d1440ca8402600810391956450603c40c4160007150b0007a03808000d544920814140d04552 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 324577931 1250 324576681 324576751
    0x2012007151215060e03010203010f0b160606030b010512160306020c03070c1e0f03081213050d030e06161209050c090406020c1002030402010816120603030206090d05090d0b 76
    0x607050541e413400400030a60744c1031000c441e200381d00420041007000724040304c48043c2c1c3c80718541c195840300080c43c10040000d9400c00141528104103000091003903005041d1704885040d110401c0c0c6181d00c20002e511094400c01c4c0d0750f0750341105441400801d100f540a80004c4403803c0840389480c6690300e40303050001c6030b54412004074940e07118000c2c00e440ca000d00c9030000d03c14216115001c0d400d56a070110740f401404200c12881103100c000680b00000c0030012581c258002007a55914512410300801400101c40041510301c210808503806c1b10241803d09641000c51360f40d9050b42c010404100003402449001707441030312590410750051f55440709114003e9104800069840d407030000080d0034103030740c00841c0c0881c600c188104400350341c0148a00b03600210201c810f0f0b0070707074501d00b100782c503039100e0480c4868100d07160a070040100b40c1c0020320240504c802d4002c07140795070b036642421180c0d44540c00009411030416003821001540160900360030210052117180340c0c40b40c00d00113600d10804021 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 324579181 1250 324577931 324577961
    0xb0f0d1103071a19080f07080c13080616020c0d020103020c0709020415030c090303050d0b0109180e0610080a230a0b0a0f050c03010506070201021216020120071512 72
    0x30b500003190403800307040c111320b61140c05c207910545400103202d60303100401800c4009100480000a150302554012146030001c0100c940107a151950b0810baa207130b03000c0f540800000c058000415006000044030100d20a0040201d082c0c0d8440c1d41c0114003941082d4001e101c03600c901000481c02e00a039001402c06088940b5415504044064005094810400c080e206024070700c601070001c83d40c40411220040821807010566540305001203400c0201070740419100c04070003100c90460911504900041c080540c100c402c5919284000d03614100c0902c00c2c0902944a0490716000441c04e102c5c0c040700c1e024200b1444810204134207141e042402ca8001110103e246800b001113000e41c61280340190000175000300200c1c64100c483d00d4031840107009441c445d1002060280440e03208018000c2106443c07040b41d52113140e0340e0740600310b0b00c043c3e0030220701040d0300643c4044074401c401e890200c00b440400040c10600d00d090003900c0480140030000c0c04026a010003560801c4180c019036240d924154 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 324580431 1250 324579181 324579187
    0xa020907022a0a150c02040c09080c01050c030a0c0c0b030702030a03050a020c0a1509080415090602030c060a090809120601060201181109060409051504020102010b0f0d1103071a 78
    0x6402c0ea48000071030b01045091141140281c20364a509160b442a2107080c08a0358440c0e02c1240b0984504030121802075126007031003403c0450a45c0a502c80040b1500c04007200c845204500064616000d04004030f0501d901c01d00195a50f1842502548220760064000504040e103401122400340e208071007800240e8400104015215030510510358440b47c0c10b0411402c221204007410b444050240740940004e40041c8800c8000c001c0360302c04681b0356401040c483c0d0b06c07595070b4000c650009c1c111031170501086290314009400e500210840701507042c0200030300102d607512076014000303040e942d006a4428100b40f18000a94440c01125401c000795040100b40f250f152050007400d40f45581c50300300344030b1040c420400001d01000c3d98902016000c45094010343d07171b40d80101e40100780e8003201600c2446180701c00301411a40003c0d0901440c000c3e4024020104148240190542c814074500c2d0800d2140c0388207000f245040c15810b0350faa0700201526081a614114442110040381d081e0003942800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 324581681 1250 324580431 324580453
    0xf05070915060801120209041b061e080103022b0618020a08070b0a0e13060b04081902060406030c030e0d11150408040b070c0806011d100e1501020a02090702 69
    0x64800603004180b2442d18200f5036043c54000c0301c80c0c810f01240240500703884070128042000c1d20545422544241840c40b010a54405005155180c8840032912120402d20361a0603240300c0c221030b6044c0ca402130840c80281120790b448891500c90b2f400703100f0a100c1c6080d000b9002443c00d000350b090382c110101c0e4440420440c2d004000103a00c09600c40d0300c0030340c080c504c204481c1c401c110a441e401c45881c00d029a0070380c0c09002290301c8501c0008010b000c2ca240440c040fa413030001c07a001e001603c950070b0445211490425106441098401c0040e42c0050b007070004000803403282d080000b50102514020030001948011103241c00380c0c06650b200451045500d8041d0810100032111040103080da0b4001c1ca400c00f600d807000244114000d500b4014000500d1006001c4050000b0000f405820100c80c815070303541140d0980120507d600001c1e00c4c2403070000c6690b040c0741150707a1041d150b082010060f15281d00500e1481e00441030052415802040c920601595406003200c4c814203c0d0b0300600505000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 324582931 1250 324581681 324581711
    0xd0f02030c09090c01030209010201150f030b0c0c030d0203040503160627020603220c060302031005030319120b040509100c081e04030309081303050705180f040f050709 74
    0x48510510b0052504500300905580001a032954101c030078200140d03903225220040380034011b10100340e40070000d1f41d0000150b866104402030100c0b4040c0580e00ca064031198403140c0d90307214a00d0829040e0f0300510240c01c44804513030055400134420000c40e4600b03013425150780d406440c22282503c00a640d0380d40c41d14405c000b107041b0300d0038496150000d0b03100a541c0e400240c2c0c0e0701001d00342803a1142040c0354076291518942c0d4200c00c1542050050b8071081d82d42c070004010b94030444442d6802c8140c0c1c46d00160f40d080020945103004d040081c034105180e41080e0440703400040400c006141c41c1c6030044060262101d1049502800d4284041d06184500f601c000d0300350742e001c1d005401001926010031142107002844400740c03042041c1c2c0d404250b15241801c602604001c80b0140071071500141c00444401e04014450490781300740706490140e0f5a4104100c810390810540d00c0369418004000348445107211a02c03035020f4458140300117851143d882d1a803074041503030090300c01e6031703641c0081c0014200c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 324584181 1250 324582931 324582943
    0x50c011d06100e041103070e1501030b01080105130b01140f09040b0906060406110307021c11040509031210030602161a010308090d030e041506080108030307020304030f110d0f0203 79
    0x4445103481e0300c6441d001081c0403d1030010009004941d120465100540e400d0058000605004900c5a4107007024000d2056092002803054082071038081519907c0d40a031005034100e4800508440600c0e4803180d8038006040c2c035591050420001c50510085005100050892843c0407001c8603151141d24043c40304541c400111640f144145030100001d60346c0d540f040b2070603034130703245400088902a891043e103180200f40c0002d5121070610601c2000408044410315058020014281c103859007001b4007085031010350302c0c01c00d2500100078107541c5e20307a01802150401c1c4040d0a40702c101d60b8030b85501040360003580302c00305130039881100d02061000300c090025a2031110345130380450b07500d150380d03407403240c4994107260340034182c80c4450406050059180700000350020f00240843d10306286150b04060442c00b40001060031000046030380701d030000540344142c401e90021031406056031680403020740e1386a4200c1301844d01500c1141151901110258518450200131103007020038410542008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 324585431 1250 324584181 324584191
    0x10e0916031116080a02190b09061803030a09050c031006050907031103010302010309110915011206050d14070b0d090212010b010807050f091e0901050a06080610050c011d06 76
    0x4900340840c04020f41602c0c40301c2c003080ea0110404c3e66900391190240d042c141101030f07121010480c0c042c40000c1c08400c40100344101412020f98045959a00c141c910b000b100301900d6481da841880003400e00a441c2d440b0f000c1050090781103685440060001a1400715010b007220105602d80c2d10800403410810a0075030040020305041c0201c40800e44071041da800140300207410036444400d9041441114500620000000340c200444ca15045408140e2210b03202c1869000946840c843d1039a02468840c0100f0799400612945651149803180302c022165074030500158000c5a0b00020001d052400401d03082c00d10f00c4010480c3e0380a401004910704400c020224540d051140d18001d9070390040d901c540c4850641482905e07552226007032105400744040c92504201280c42c0c0c4a100070300c90206811049003254110102da80b40d6080c0440e02089101c0c00010844410204070240b4040b0344001c8610103d24029040114100b240b60075544103c2c91101e0355913134038002a4140c8414800150301c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 324586681 1250 324585431 324585461
    0x20d060305160e0f0c1911071e1715010305010e15071205041106120a0b040c0c0308060d0c06051308030c0a150605030d08090d080f060609010e091603 66
    0x140380039482c1c00c071814001c1c82e821000c2045400108117201e0300d02030724000d140400d0403841c05010100003524801888028560302d104114000916103800d24114010540040151a900f4609a5100c5045406188440c1517003c0c80701c001c183c0f4009504003030300941c0101c0020541ca080b15200506050805c6c2d1418410913082c010803158030781140701c40848042c1040000340c81c0d66207003030420f07841d0f54502040ba804100020406518120910348500680940c0d00c200000e4082c40c0400080b101c4107200303c004612205885800b0a0060070704545c009809071000e5800980d03079039900710300b42c851f80141002c075502160002100d201c1a2840c005004002c0042d8a0049a2203100c2d130380790303000c120080c070020414004004017006900328600520380074044a00c00303251180090488441114018406c0c031038800030070311043c41110801e001d1425505141d840f074a4903414001982d01940459041c804c0780c0e2803416a50319200032040c410300b810300b500700306018840c0000741500c481030040100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 324587931 1250 324586681 324586723
    0x13023606030f01030b090f010204080102130f05150304060b03100203070305090c090c0d0e1203070f0314130f0b09030a091a0a0f090803041202040f020a090b0906040801020d060305 79
    0x801d0b024440300c18103694001e44448981d50754661403c0c80c00d405051241c0e019400803400054400c015006026a01d0070b851642c0101500c682e2002c0b030700541072040d2640300d954440281c400f00d40040c01150428000c150215510344080080307032412030000c402d061402c5d80081084815076241c4200703a00b00600c0c00180400580e068001510307191701030b00002031401c00045100381d028490b48000c03094501502a40c080c42d1202c8164451a01b00b00c0712080884d05141404981034440c1c82080d000818030400010b0a40b04c210007050000742c1010102c69806c6041c2d448800b081c18003144622608044000b15500c004900c00100035451aa10160040c3c841500e010241080d01d01900c08900843c41c03d0b2610129040080b100200a40d10014850000260200b0558030f1038181040250083e60284030380190710001600301e03c6000c1d10b07540040c08070401800a010b0740e2008112540000308900d050584845c007150072a4800c009210541e40e440b40d0030801c220080c010600016051050310711 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 324589181 1250 324587931 324587941
    0x105060705100f0f06030605040201090510080f0703060801090f060623060901050426060c120a1e060b07140102040617060a120501020304140c0a051302360603 70
    0x280d1034110b56012000207440340709110440d4460352014030b00c030180c264184081c940c1c9080041c010202620241d0000d5a40040802d039814013050f091085031982d590641e0700e0746da8419030120942c002e40003c0c10192210000604507809000703000030300313000e00d840078940289440c2c40340403500385078030040301e420081c084401c480c94914401a144002580e0701a40e81a640c1c004843c58070540d0410424045c44d22208210000a0b415501f09501c020044480603101c00c811180c01e400ba040010708000c0c80d210014600e00c1180d000810701202c2d03858080856580304915800340da650341c002420065002c501030003408015a94400a0044070008518050912070014501c03c080c807007224030495510b003c0303100384e120444140c0003005038a00002c508101454001d010b5402980e055581c031807907c040c800c9091000ca01d01449440c02080440700510340020710006090304501ca01042d03a00b4000300c0c1d407001041d101c1d020b4100c90140007003101c860a8240005142c0307680d100303a000e5082801000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 324590431 1250 324589181 324589183
    0x501110a1b090c0c03030b01030636020a050c01140903070308040c12080913150909050c0a03030905090a09151109030d110c030a05030a030c1b050c090105060705 71
    0x500450700305078205801d2404030441d854500007980400212840d21400301450b035407058030030051a20a80c1e003805403002483c011000c0c1d03262070040440c024915201c07600f440704a0040d00c02c4034a941c80740c1c125032090000c800d10890b08a102c410703010a82c0007400008030902842400260001c00c690000c0d0b0b07042c1140041d9490048480003001d00a00102040504c0511032001004001d499022401c403107252500c01070a8200101140c00780c441513040e04040f41c030074050045440440b006445240d40707044408030281c20342440640b400e02400910a201d03845018411000d035020341c0703445030054604400e003c9900e0340101403401c2e007490120000c0000d85035804455103003603030703501c0803540010900303201500d4854901c555034035204445569110540064503105442001410707148807542e00e106051701c1d0024140001c0c0250404c01c0010906406a1b20862090347c040c5004a0017a00d046c00c3d0b1820030081803825142039102c0c0c3c941300700500d803180526000d442c00741e94103030612200759581 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 324591681 1250 324590431 324590443
    0x50114040b2203030905040f0b030d0e010c020a080d080702190807030323100605121f080d020109120e010f031a0a030c03061a0603040308090a0b040813050111 70
    0x140703159010000d45908614030400d05034a082c0c0840241c40041560307850040c060a4061140c1401241410071400c0080009d10903c2004a03002d40948100c9c13030404070480314080740d1201d540c10700030302d4038006000d80c40708a00c0501505001c0300401c2d40650b181000b804508000380b4190840d4490008206044100010958401e0b0b201c1c0040d82ca44840d0301c1c0a8020700044041030580420381901da107003d68100c181d4500a10340d08002014481d1140011152032142c81f09648000d1442004992051941c403000700039903002d940716050780e60301c2d10040c60a040a1580001c010f0f0b44403500902170010101d080300040c911420030880044107a00043c0005c0c1c0c00d01e000d88241a903844448600480c0b0310043c01849100500c020f004a0302c03807408200b5143d0f1030200761030907071034680c042800300f01c000c2220b00304400043c406411a5603540d0101d034551f46c0141040c1a6004041107980025044000315020341e12036081d00c0c0d11130350508211003240206910842c100031103e544050300640100d96 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 324592931 1250 324591681 324591689
    0x90102030405120310090e010b01031b0f0804020409080f0a020601050307060e06071115070501110f030c030c0405040f0e15040209180a080703021c030204080601050909013305011404 80
    0x3245459a88000b1440451126a44107840c847e003000e407060110401980001e1008000740c03030401180c9450040260400049840e01022914000700c030f40700e59021341032031036215200130804907440182e81d6500d50380e9000011010034214010910015198040c000d95002d800290003e215248c90030b600200001e04d0080c8141c081e030030002d0000240542c09111500c00440503208402102d48100502d0080d400203100b620594600211007040b03104070021150524401075000742591510110100030737a2000c0d0101c2041c081c00c0000054a464500813541d0440c08120005032007100c0007500c608002e246030440d402c111b907400c01c10005aa07078045d01c1d078011280c80c0071281000c09071102240360a94000028102002c00b1070207808041c2d000070421814000b010350070b07544000c200c009600340d02880c0a61a4a600b02c1d00040c881401d0040510764002039580001c1003003004003014480001001103c14a07078841c0c222510300c1883c40c62030000086c0b8003842c03c0440030090400380e180341c1c001da0103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 324594181 1250 324592931 324592963
    0x903210509090601030e0a210305101e08121207080405100c03060b0d0f060b0711010c020109030f0609060506062a0f031908060d03020c0d080c12040905090102030405 73
    0x3003c00e1940c2d200b5400004000407000c2201d840e1a4076080171400c01c2201c01050490000510003411564072a0060742d001d0300d5036100b160406400d03c5056906c0001485404141c0c5c1c0ea0341100180b404000c0080b41190480d11120540e078040c2c0c5800c0c1a00000002c2c8020140f04c403500c00d00001902c0006c4904086000f42c20000d5415401c0f40f044010381520343c0180ca11050200b038a04403940b155211442459130b00d07500700500f0f03580742c00040213070040c201301030300001c1103d03420070361940030b0300b00e0103400fa105140c00500d05840750303104912440c1c060740540e144c984c2c1e00000410030031284140707a0050021144182003a40c00080321201c00e802c0003420303074002001e040135600b00d8001c1082070611424801a01d4603004d07000421110046000140d00002d003081001c1030700c0b41080e0945198452b0541d02a02d5151411018020600001003003141c92000801116105041c240040b1039a0640c200440b90b845182010b060203481006d060540e05910401c2804005400040c000c140d00c12007403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 324595431 1250 324594181 324594199
    0x20406030f0207240e010609021809070c03120b0a1418151302120408120f1b0a020a05100e0c19230a12050d09080c01110c030a030903210509 62
    0x16226402030030341705440034820740c00d1240c0030420fa405600a064000c80c400d002e0440900b592040001d0364070b06603035036004940c0419505020a214280e421402d04080c4408103842c440e540114000035000d5001060600341c3c1190302c1840e1507d80c107010a0300c12000c24040c01c505188030013942e580c405070046841071700c850382600700854094041d19180d00406400741e00300e1400f03091102982d4400500e1030000d0035100e00088002c001a990180070b0090b6040d4441c0f419650b030381000040d844001c0e005c0951280c000118000762041041d40b5031007100e840082a410720361001e0b40d107025502020188910300e4004440e0300700307035a18284004c0b292200545014480c80003040f24044824018980d044121404045440f00e0703501961500944030314101c1d541a040e100d0122a6006103000e44201e0b80c11015030010a9841841d52440e045017a800703554040600b13400181c50030341961011000b141015801300180600e40050300118175200c0181c05010698000c010501e11030404020300c05d180358 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 324596681 1250 324595431 324595493
    0x60c0e01020c310b0a08030c0c04020918160e030606130b0d060e1f0b1e0f04020d0b030c0a06080115051204060906110703020a0b040503070b0a020406030f0207 70
    0x5407404480820401c484180202c68a030044405042c981340001e006141889000031745030000401c0f00c0030000200042d100342c829050400c0080d40c40154400c0e80030301c00c2010074007410320a0780c07010302031068510107091900c3e1075200a0301c08140809200c3c401d80001d010402551150750803017856185050002a108180e040040e03640151110080e20f40c41ca4501c4420700c4803400078241214611505101042001c00c203014001d441c644801c0541081c4500e400d103901c8422007000701e400752801001e900194006002003001c90f003145440b0544262140c00307041c01d5040c18040c02c00004800ea96112046044c060040e0520606100f0210071015049820301920710400a45101e40c01403071380303114a41800d0410101812120605440851411040450412410003140d02040d03254000d0b01c1204440c0c2c0362440c103000000c1080d0b4003070208000c528001030240d400c01d4031074042842c00580726810b10170000e0880f52480302c003401c2c881c8100b004002140d02019480e201c0010408010220540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 324597931 1250 324596681 324596719
    0xb0108012903090c01030f020403080702040f1e140606161103070b0d15060302161e05030309161a041e090c051b0d0f0c06060806070804060c0e01020c 66
    0x30700881009041808418000903e201141041d5001400d0780c0a2000800d986294030403403095201c010001102000600018180b50700500e450000302c0400094600c0980c21600e40c004012440c03010599a403222070040201c0701e2050351b00607800703488007803c1c008100b0360002c0343c00c07182001400200400c4c4003652143d0f020016038018100d180140ba445840415005d4007400405221481c0c5404c0080301080c080c0c403074030030b507003c0c0c51511700101c00540d141e8866802c031890356580700080c0d100f00c42407800482d204000850240b01924010682c400c0002002030800c90b00ba0040c03c0700c405204a40c034000420300701614103481403041182000e1034041c0e040101d45006520800040d4142400003006903048000340c6442e000e00e403011000841e03d001e4041c1c840c4444460310020520380d180c03040500d440b40d270040b1a514481e2000041050311213890780d18081c0c0465003036002a16070030802c41000020700540d07900d02c045080c01c102d03030140300700083d484125130050755000e04c019070a4040300c440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 324599181 1250 324597931 324597989
    0x30303070804061e0911010309050c1002072303071a0403020f0f090106090801110903070909140604210804020a05060a0306090f0c0207050306010e0f04020d12030b130b010801 77
    0x50b2000113403980381520f0701072401071702c0e1100302074400d48000c4515020a50082c0580500e0390391080140104460490404c80d112503001c0410701107124221000c82c551110340103625100300e0103802c10071035212500c101860503001d6086038174451440d244054280300c040f002d07201501d50444060318500c81c402c0105103125050410564008a41400001c0d00c54002c650350058580c0741c0000d01200c04800f000c40313490301c034246403140c143d402400c0401200700107901090040388600b451030b814803200520640740c50740a030780903203100580c6c0c1d2201e1980018030001c001e20100c0307401c150550345010303000154451340030700c569405a000024401000ba200e680700101418107100d040007401394104d8070314001c0000724400001f62180c0f0302e020465180c0010b100d0304a620311a0352460355684c0c0450324081080c0500f040780c00000e039814527000550501200585055642d070005440b403082005c00c8000410030794031908072031400390700c15420b990019945044d41c0d0702034004280e52070200b0107034607111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 324600431 1250 324599181 324599201
    0x60609030d0c02101407060c03020f0703050301150306031a0901110c0a0203060c04150c020103020906070501050a1103010609030b13050703030206011d15190e010b2101030203030307080406 83
    0x40900d070304448070660050100b8034524001c0d80c03072552007081c440707050320844800880c120706003006120000c00600329030800c0b01e601c43e80e0f140141c2032010702c10f101d920329080710342c00300c01007440071006105041900b0a2030314002624078040c00524034603100c40040145508081c00c20581b4200013860300c41c400d400091109281d61907080e61016803440103610b80440070400c034403a026480104003607020b090b040d1402e9551410b440e60030f0300352480c0d00780c911040a20003281856000d01ca51350160741c0308006446110700a9002007110316005071550111b4281c0d004094070b4500520050003440c2e8400340c41003c0e40e9101003501013a4607003a50301180683e64580003042485201c03008000c165002c1400fa04132101c0c444101d00201080c5042202d03810101d86200c04ec5040102000092611000c659031031040d038100e400d1b1007512248001c07554542604410121440040c05111a99059041d800d106083c140791a4880d41507a00183e2079100150214040164880c0440c05000700c59111405032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 324601681 1250 324600431 324600433
    0x103090c03080d06170c040e03070b1317030c1903110a03021b101d030304050a030e1206090f07170d030504081207120e0616081b0d0b1f051206060903 66
    0x12003420050350f601d1b0f44240c1032074001d13030800d800c1072030b000b000000341c3d081160b21803140d9a4503904c0c42c0d07003140c1c0c040d0f140c00c054400d10b42c080d11160055100c0002540242c690b034000d00d13a14043c10302c0300143c00460860710010540341c6000000701c595072a00b950b10100380c9181c00341c0d64030341e80564a05010036224000c51140034849803014100041e621100842813842031903513040d18100b01040c1c590100329006015a0420107940c00041d12510382d081c18511f008204041a0414600c858071b4040308490b890780d41d40c0700c4140a8141034040110b0700003045081c8000b0100440e07141403a842d2411b001c811400d1544403004202000042c9094450794108070803100749515240b40010403510403515002e6203075203046c48402030300c1e02c04140c152180c0c1c02c900b00110000c00f0a10102d0300030310020400015004d000c9450100700c1c0743c100c0188007441c05440089a90200d800820001c075040c010204003141221800703110641c0c000b0191601d803000c039035042c803e40d6100e10100c2c515100c0d0050103685 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 324602931 1250 324601681 324601709
    0xf0314040906090207050d08041101032d090b090d021c0201060b030408120f01060c1b05040603030509102a050a02040906020310090c0203070b10151d0103090c03080d06 74
    0xf580110f03501a240c000d000304100c50108590a0098492001c02d607000b62011440440d22105540603400c00880d0480c40119107102c51407000b0b82c0415000145c1c40c6800310794a484c0110184554103641c1600b21032107101820400051303141c083d42e0760004920603850009048400d041180c000e6200f10b002303003600742e07402e80e0743d2902d8035081c00303035500840403c08981700c94004148900703400c82c80641070728040d884110321000a51103a024074808504c0d0b890650044510225564541d03004003001507200c4d88545454015101c2040006d070310300042c43c001c03c07400c820034400805d004d0f01d51580752f500781c0b40315125844550410034102016038130040e4006003001800410010b00342d0045102b03140d50204000b0280d1a446500103903200c00e0b81c0f04005a000b8814131000c078600d620712a8003e80c01d083c804548650780c440002c4849034211842001c5010003402102e0300c1c49410074212145000d03e41008410380e5580c0c1c1d0700030440740340000361600c003001c10309421a55555100d440a0b0a0248040072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 324604181 1250 324602931 324602939
    0x3040905010609060206090129040603051f1107030c0b0405032101090b0f030c0105180d030816020f150414011506020708120702092805040605010b070f0314040906 72
    0xc11090701c1051300500c80c81e000035156680c10710410b412000c12911700040908a100b01c03408d101c1e4407040c411391055450030008002181040714003002c6150481c038100b14500d205e0130723400301c503a0408100301d90242002401c0009034002c8001261507030007101d509a680391403c090381765009444140814142d100c000d81491181079002074122441e100381884403068120503c4030f54443c07020040d802da030121650018942c0580060110131068080401159421000048000d0700c80c03141900424280010704c54441004c001810310304c0c8150001b4420001c1400c3d085030350344180301c40000b440701c0803004181000220315a1000c0351035080c0081c02828401c80c1c0c07240000312107108400c0503200303640002070420000b04100d042e00c0400e4414505180d02902403003025a001442d19115220748040c5d440100100e0a90502d04014220001010314242c9441e00440f8010313003258000d150180300c224002140d180442a040764103140061409000e02c0c6404014022500141390540c14040042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 324605431 1250 324604181 324604187
    0x50304050a05071211010c03080a0c0c08031906230d030e04053909040c03090f11090f010e04030c1115220f0e070504030b09160806131103030409050106 67
    0x1100d405e0183e508a2002c40d288001510010541c001c0140031810140004101c0c07204c951088440d80003900345011030284540e00e946880c1d000702d07400102000c4000d54181300039a10311410026200326069224031404d0042c140300e00845107001503119649020000c0308061090f440d180321800068000c3c401c9003020240314a04d07142885d0b103280b69440d05550500f1040407207000715991155440c0a03803416049a080c000a4180008400e06041d102c0614400080402e170311890f046001d0340314444140c80003810415071640261090002d15844001400028405284983c200e0b034181000c1c2001c41c014a410244088103000050340200f0781d400074100540454000c00e03400004003440103072420146211720004099004980700c400c5944000c1c4106408203910070b410003003908050381060b0740d0307580f03103c3d0201e0201e680091ba038001d40f0724552044021440d100c06403c5d81d0b0050100d074505440010900d074003655000c2c252185880000359903403070910840f806400019400e100c00d6071201303405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 324606681 1250 324605431 324605459
    0x4060309022b02090c12010f0305011118040b030a060c0324140112060801051503160321050c120309160b0409050a0e0f0f011d0d050304050a0507 64
    0x280e0007040a241caa2810101458a0a201c440e00e06400c6400e000035409209480f00b00030812443e0840400c86e0216a01140c03168070300a2000f854400c1b80300382949410713801c0d50340341c002d016008038003440907a0703440343c41c0604991040c0c004c0c0c80005882c240480002c0c134119540c400580024074120142106580c1074215a0a680b11003060b0f484510001c15800e5000da0306206045200503501c080c41c14640c403071060202281440140407505544136480c9508540b42660650412000381c13080c05044d04050005940404907022900380062850712280c14080d03840ea0490310000322441d500b80c00d60b0141c0c0a5600311103090044030240403111001c004103031320a40d2050098032801c2d111102e00c511a072a0001600c940e5840141007500d4000b000020340000340c850390505481e900031500b407080070410214448001c00040ca07003807405c406d21908440b108207001080508100401ca9550000260511182070610300181e60742d9860802c07900b0060202c04c010024000d54400081041e260007503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 324607931 1250 324606681 324606683
    0x807140c04140103020d02010309020310180b3702040305061302030606030f0a0f020f03030a03060303090f051c02010302160c0905161e021207030818030a140a0c0804060309 76
    0x810442c0c5003650840d08a101400d1100a6102da00c00c141080194800c1c0c1060f02d020703201034110745003074880d8415441910041141c001108260052800074000609107041e004080d84110004464410941c8000f000c588040342807140340110803502d421000340c1c1103074000c64101040e10303803130709081031500c81040c002d0b00280d01c41c1c8216408103480e070ee00800e4501c202c0e01c1d0740000703102d40c0749540d03905c4109500e004000d80c5d1003410340c3c508940340e440a100810001850360340c00200c5a0440c940075064601c42d0300a04840c0b0742280d024407490700c0385299001e003182e41074270100c22a41e0510040380a4850715003080030006e4003c20343c0040026103082c00054600200c1c0c20711590340c3d441c510b00b94041200d1032110004540c0d21003d40807c041c11060080b584191040d1390102c01d02c10300b840304d42d03409814110001b03890a003c01203c01080c44038040144e43e0880610f180404019004011020242d86601c000c500040c83c5004103009002000f5440c0d809034036a61241ea40c1c43c0054000c2c040648 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 324609181 1250 324607931 324607939
    0x106201f0f110405010507150609090f0210020d3002041205010c080f0a0e07091b0320030c13030c1409060103060302060f0f0d060909140610120807140c 67
    0x601007151140b0001a2015550b040c0d403264149a580d44540d00c0c000c00760b021062000e99540310101c0d844106001e4040090700541110148080f14414098445e040005134801c64000c00e4800e4010742c2d01107844d00d421010513420003140c01c000c1000c0340700440d290110701c80c280c3c40010001251001840042d43c4503000e280200282c0030340040076a540d100417110740803482c4901e00050003010455004c1115800c80c0012034117030302e40ba001a602241e40708001c1404180d0680d4446588640c140151b00005400c44c030380c4102c07000b0b00e5010a24501019040e1440c1c0760004c2007140c441e101c1c91129000564000300550415580c80c25402c0301500b1040006028805a4000403442d501901403c412264060000d521700b1800303130400c03422034100c0804030881700d80801ca81840200d55000b440b0144c0a1400002048030741c62400e05800ba01c02045080d050300190100306100081035110000c903404030048030382c41c0f40c851402040b14072030050028092000140c0070b030b40804c00010b0f52810304509031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 324610431 1250 324609181 324609191
    0x112211b06150e0106110316140c0d030509270406020703020a0b07050703031b140c071e0806010602160e0c0f070b010608011e05060a0e060414100302030106201f0f 72
    0x46c90319268450301100802c1480e840428a00003102952007255065a600580e04210000700c001400701200000640002d00040303961025440e141a080c00d03019880581001c4840c1629840401504000d0024003c0d580c041607010604d4024484000042d5000314100024604194083c2c41608400030070b4001034600040c11040c1b120345008200c2d41503054075205000c84080f03400c884250b11044110009004440c40011102c90b0f01d031390606425243c84080c0942030034070f41103a14242051344610210351140c00070550028175505010309544200403000d10582e650707089a05140b00b050200250b5100001d1654180a4411b00250680f0710300c3e13030390305170690f078a425a03d44c4040c5401484180d00403060b08000c1c51804100900b01b8007164140381c04009884030000c0c80680166210781130320300c407a120410aa14140c4031000d0390305101d003000c41c19541030400003850038501d07184480ba214000403a4003000a400c1040c0d40302e02d10324410700601c0d0081c4503079500c0030300402d10311581070604103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 324611681 1250 324610431 324610457
    0x905040c0504140f0405120c0a06110708031b09060307030b0307051f031a0a0810060e040f030c0302010912030905070e0405030f030705040503060112211b06150e0106 73
    0x180c00303505041d00c14902c0f0190316407030791440440034800242007200d85129a900020040300b081000d4141911f03800c1c0900000f00d1107044c480103a0700c3e40c2e107032140c05c03441c00c000c0f4800040c584000d5a402076600c0032002081882181d9140c2e0521130300025035031080002c8200621161703d0780140781805800c2e0b00392148503544400380700c81c0d813100103000c01d45229a104c064100310f20030362040807074520390b40030404000d5219001c41c038002501e401c06801500245240d84a6044e0340c001c210013003042c5500e400c41480c15464400d800d920025004040104407501041410b1003500410800b6410580110b00c169480c81c2c054010031069000b00c0b0700d4022480b000507050304450419100e035810101452801c4049103900e001030340018035120600034144408103194808000d158041c000822000690249904089214402c0b54595082a0310740a5a081d04258000048245101c0c5403c0380d9004804a203000c1001d0b101880c481cad01c000810410010700c01950000d20ba048520760384480081c0345031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 324612931 1250 324611681 324611689
    0x11030406062c0a15030210200c150703020a020a080d030e03092b0c08010506010e1905040203331f08040f06020c010203091e010213050f0d020a0905040c05 68
    0x9402c0b1044155102000801c1c010603600211801e843c94030388680382c2501da5001961030b800c020908070014149000400c0c000349000340d40c0d02070000010042c104000d114001851409261110050b10326010900c0c6c41007500070000b000e00315500504003070450b0b4517008001e540e002c2021003a00017134100140300f80c4500d0b0210485010701e0020341440844406106a00d500050040c4401c08000b046d07590000802c54041524020300030b1040085035904001d0b000509610704410403c0c8500a034041c0400c80d5050380240344203c440503100540c0700da44044500601d00c1d2174103c00d1500a044280d82904842d8908016017015004c9548058120550714810f1007011041c0c4e0350000310750210040303004280b00d65078240126210710b00151820301c03030810007420b80e0001e8482e082075511001414103c0c1c2038041d0260080a1345074000c60603d42100380b076415144191150901500c45904294140c0c2c50310705660100f240c0281200f2041580c510f54007004020850f8251200f00c0c07503000c041450702e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 324614181 1250 324612931 324612989
    0xa14130e0316120f0c0b071407150b090f040b061315030506070302030405190f020a0303081905070905010e0409060204030308010e0a1e0b130501060905011206050616061103040606 79
    0x748580c5d030303502e200000e5a07412002450240c100820f00c2105000249007414000003045c5140c840c02840a000611880520558560702e20013480707a00e05d10104041c0c01000301c281540f04d60001000b03903550302d80e0001708050450180d2605a800d090000c50001a030783c2600b540c0890303125a00700ca5041d598090101c089001c2900c00900b01e400c41c1c1c03110010301c4000b203202403407035015881848000703003160f0004092485170344c411404101d1031020028900031410304030300104c00001d014862480d007100010900341d02130207801c0c140a9030125011050301c0f0782e031180d21015880074045588075140c0c1005410340c0024450b6451902c0254001240e151312801104c1074042500c040c41425131113924610082c0502c0034080e41c1000c039005a1089118260080500a051030780b211407806040100040200070400c0d542003ca03418010f04004035195031048032800c2004543d802401c40051400070040d18602c00314541c60f000100902c01070000e41d82c010001c86070222184400300b0786401e0005030b610 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 324615431 1250 324614181 324614207
    0x2280b0c0d12111b010b1c030f031a0d08041d09241302010e100302040810053c0109060504270602030606090402070b070e0a14130e031612 61
    0x1c0b018461813250382c4940007020407841c42c9a0005c5102c000c100041602420094800103071325400c404078005041d04500f046d288a02c5074038050281340002168140180b14800d44035005500000740310090146000c1550064844080701c903840d0000380101d22010501515034402c1402403081d2000c86440700f11101525414042c000c2c011941c1c0d40d00d001e10304480c0c0c41c90603814050a68503080c2e15969408000c0404c441d50340b001600e442c20094428030340303d44030300807901040c6400d050080441c03212902140d62a01030000c880c0f100e4a003003074804e04514030716125409c07858010003c0348221040d0414001d0b0f80341a070382004440040a0890001c0079280ca90300d802501d030034401800700303503180c008551003c030150800b40340400901c0468200d0303009090640d09004903009010300c06a000c20242524401140c3d00450541083c10b410103e46075a100c0c58403400c81c02d01c0d0104461501e402140022000c0820342e42c42d200c41480107000210200412201e030566103000030941c6004c0c00a17803020f4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 324616681 1250 324615431 324615461
    0x8070324020706240504020c031603031401030308060321090108060301062d05090603070902180a1205070b0a02030a0c15061d07050702280b0c0d12 65
    0x20491241404030300116041180420303000c1200002050701c0d40078a00413490003004d2462030b940c11601c002a55100d94111610581c0100568074140c071001003920356901c2c2d40070b05200c0d6017480c1c0c03400754000e210000032a4680d4941c00000800e0681080c502481548244c050312102402000d503a665410b142100d0304805c282406400c5595105280f016400300340a0300000b00c2c035442c1c00340c00d81d09408aa002042080e0141903240d65229618181e4004290685800925041030800291102414080e072a1101e6010401c80f00c040280350360150920800340c110300e039690321405003000502045030305850603c40c00303500141722410f03c401c076250b20115070b01441c01e240b2034440c01c4800e16010740055600c0000480050051400c0e41701d031200620040008400d81c06841b8035107006e4481c018580700911a05010503400768540c6810041c1080ca4454200c240e0f548034040b244c41c18900350005500511301180c24603041d4000184c0007810384154503031001181c0280f0b40d00080d070780c0c0e0f01070b4800c079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 324617931 1250 324616681 324616703
    0x1060603051e041704230a0807270614030c0901030c12030c060204090207050f0601081504020303130b090f0406030c03060905031605010207020405010b0a0c0803060d050a060204030507080703 84
    0x1894070b0b41c0314140c00602c00c0940942e004004200c90090790440d4008a10400429000721900b14080c22030701d0f60400182c80c03648540d071034003c00ba61607501a114002c014901c80007408044807081c1c0c007a5003040500d403810488036031260040e116500003069a9406807154102980c46464030b245400d048035846588103403103034288210707881c0e0a0424101102804401c0e549540000ca1a00140010380f0400d400141c50750003d0070142d140141a5683c1085508614014064110042220503c3d0006610700344901d0b00c039440843d2031481200c0c04481e001e103140c2d00c0490701d4000c0400500103004100c410741202c445a00c10007040307a100303100040084001c1e40c001c0001807126002505203c3c001c0b0b007560708100e00a1400d9040a03607003d0102d0303007030b580014003004514040c0f040300d025000e0102003e0500b600c00f20040d14503046c00b200509110b4002c80001c5007a62032805180c8403903071040c2075070810300c4545421030203034000e400101ea05016003000454041030008800c01182d40003886458 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 324619181 1250 324617931 324617971
    0x3130c151d100e060918100e070f050a270905010819060e0f0a05060a15080c0f03010e01110408060601140f0a030603140d09080102031e0910110406020106060305 71
    0x240c0768060044a0b030045418002031005d0b9881e52024401c04030401c940481782c1c500140301100003d0b0b641c0100f51800c0c0500140318025a21403440e011030700c040c4c20455604d2900b4041500c181030042a4005085031503030300840c0c111580200b010880d61200014422a605c941d465920b1707501a00c084002d175030040c19500c003c10f030750347c000c2d5090525440960303480c080310081c0c49003041000d4005135140c1d4400c0040c45540300c00b600c02c441c104020b0000402889051441894550020544a81c8215100e69640985a13000e520281c0080c074000000c101081000404920740d82080c85184268043d41c40000c009500507a50035800648550307c0d0b91500c80352401c0c0c01815000380e040502050794840000c40000c9010714400e89c5180100000d0108002c546c00c004d14241d03c54001844690040c4180164400d00d031040703c681d52082c00c000500c1daa0b400c3d030b11030b1410180c40e00c4001094103142d0035041d13511101c4c00134011b880c840e6000340a180c0e282d1400b6010307114151002403910361801c1d80b2003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 324620431 1250 324619181 324619187
    0xc051512091c03110d060608040b0f010f060c03110d0e0a05041107170903100e0d020a021c051c03020a09121e0303180308070318021503130c151d10 65
    0x7400304d0041c044076061002900041c411107009400000c00702d1408400e00050022400c0070b81d51001246580c41c08070740c1440381c10312150301d81d4880e600c144620b0301181810035005407100c0c03500c45002802c507804c4155410004010409142405028114540c1d0109040c24940940e11020002c80c180616100c0c0036035031920310704603421580c3c0d0311460074042000955010303c40d0420f00c26032124041020f42290003a00e040c030b012100703844195400b00100c0c0380161a4513040c11101e90f02e00e000003910101c83d007001c5003828070340c4c80741d440d01020300c0c0c0700c42c503050f501540a40160360399940c0d4000903507200d0747d051541b032011000241c055020858a00f80075401001840701a61003894082801c021042c0750235284c00c105881207020522500810442d19458800c0c1c42c034228003240e10130703921034540e008150707985100400c2c490910310001c001003020020342c0c4410765042c0c3c00324000b40074030307074404003146c480704c0700e0316200001045200072069a0381d0000903028500b80c014004d103035900c0c0b1100e0903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 324621681 1250 324620431 324620441
    0xf12090b010b36010305011202030a080c240a0507090612020702010509030604030c060e0c0f0d020307050d060509060a0221070909090b0a05090d02030706090c051512091c03 76
    0x43c803804201c02c45110941c03184500725400c4009000052542041900b002606456050304032900d06086600b0743d40c00340ea00000d4083c910b90b00611030b1640c0d041803401c66400c261090000c6450041c02d54ad07140e0603400151401351040020440402442c0c450050440d40c007603951060300e000540b24181c5001461907507008060403841410000e240000f0400801d0403e01c0445047d00032885024121051110600401091f25518001303490304c240240c00103030103050907040c03060054000010980440d1020400b20003d000b0007094071100c20803626080c0064542266840d90714010500031501c0e04a05009441503160b82009000c0f6840303400480940d1300c5002040380081000c0480b00142d030312010701c500d80c1c0a80c052030300a5090718141c0d02800c16130b40d0103084542c0660011a40041560b804020356203107c1e4424800304201c40c841c1062080105e44c0d0b080b07564000010540a0107401300a030003007050396810707041c4044035034034050745035250805812801c417190040314101040034425406 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 324622931 1250 324621681 324621697
    0x30807120204091a0a0e131106070605040f03030e0604030903080c1005010602011d0c0d0b100e070801090c14030a0b0a08190213020405030703110303190f12090b010b 73
    0x50800b83d58010110a8481c2d0b04d07104941c0703081c0d8482100ea02d040461010029001c0c080d44c2c0142410022404d01b0f42c61864840546080301000c1e100e074840e50b82e4422612211780000c014020307810f0505100c641c80380000700480100c0e01d410024181d1032804200030b84200d41540318842c24901e0340e15407580e0b0b540706150741006030060124040700080544502d42c0a0802d5a00006100c0d10703094038030080301c015030f105e03418550011954418a54038001403c00d0a0790050208101d43c481c00d582d0030513400660030581c2e10484523410440041c0e40850490704030b520840041c0098000b908054624558100d21180340490802c000707101c45207250042c141c1c0d40d9000c2c001c00ca0321592801100e04000200c0800d4807a10200c2d641d0105601c0c0002400021000079682180f4080c40c0c600029583d1529100040c0354030f01050788150160340510644201043c049004048003004943c018018004e5481610120380c82d548103c003881c510b44030b840d4086902c00d44c00e035507613400e010b01c0b000071382c1208076 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 324624181 1250 324622931 324622967
    0xf04020d06020904050103110114090d08090a030f0318051e01260906040b06060c030706180f050705090702010213140a03050708030d0f09051506040b040603050a020310020403030807 80
    0x202100030307500c0d144100e5000f140039418140123500c8000005214140c0301e00c128541440520030b541040d610b01c560840b003168045200da5651903c040031502c0501c090340003a08038002e101105080c941c00000c03c00400d010107800c4035085d82c0301d40800020180c00010b19201e2400f84140b00d1003540128810050519a180411480d490780c0768269080c11040ba964405a0800003e1000300031000c100b15400c8030742220040e0914a004078110707642d00551001800507503c0b41e5051884030100707481d0002d65074011300c02001601c50307814901d55940140c03041034010007003200001c60301441031017961580c010300008000450300d000e00300681c0c481940380203a40f04003010300010005500b004482d00512002025684441241040b10b0840f40c004c4101001c0c0ca05103584400003d101151216483c9500c0c440c09209842d01c50119000301600810150428034215001c01407240000780500c02074401c4048035001110020041e00f0703070255100c01008110180c0108087c280254070240840300094 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 324625431 1250 324624181 324624187
    0x6020d0c060b061602030606100203070f030905061614060112020402091314160e09190b120109020a0b04030c1203030e10050411010c08040506090604030b0f07170f04020d0602 77
    0x680001c11950008081806078107140b10f50130214107050295036031001088903001503a1036880c0307000e5200d104802d4003c1c10a207060b0807280805000361a03030000303400054000707516052003400200041c0c131940001c1c2c03030010a90010310899900026003d058070100c0b00840500d480032740c04d01001c1e400c215612644101c5805100c0600d4600344a5032a105900152401c1d56081c19038079041d0804d2080720400400036110504001502c03861800b54000348441e242d20074031581000d8442c01050202c091960003480e403100444400f50540041c40c1250003140c4400120b44c0e50043d4019611a40c400200910a130013001c0043d041880b0760079501030f001c1d0601194000311a02100e060002c0380c0038150520355500140400d124641c000094090020700302078070820080d440d254107a01440c40342034801d0790000b0300320155840b028282c800640d4040700c00101170501c0d24100310b410508841a13000921544a403032411866045914040c0c0c90007448040140c48940a000040605039400d8804580070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 324626681 1250 324625431 324625451
    0x3020c0102070c1502210d09050a12030c110a08070309030b01150e030303090c04180203010212010806060109060f0c02062b0513170d09050d110106060906020d0c06 72
    0x81c00100303401440351684000e0f480c104521111810b048945042c210f6002c40070684d01c4103104024004400c1c102549070b134840d1001d28616014004002c001452030065111050800c0180001200114180c0e04c080c07011920300700d41122100c1d41c405034074070b55078020b0b02e0381c1c404035909000605c100e0b8020314181d40c0c0c4030f840c0e4030740441508080e40314001d80d0308a005148092544100724504c814000c4024500e07500302804081d5461702c10202c002d00c80e03541d40140f0400b41502c0303540075554660103002035448a03501c031203240c440c2500340704400c0e8501030b5100040513507100d007800780c0903910315440d0814210540e003000c60b18032200311422a0462820414142e0303039407182680f0a04000da1022203104030345108902e000303032080078080a90a200e15140c0500190806903403913514a519600681c5405081c10b140010341113540340a04039004207001055030300e0b441000b2100301c10011009001840d13a80300c08544c40d15040c854500180c1041f1600e00045108550050b0000d0160401041d00400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 324627931 1250 324626681 324626683
    0x7090e190c0f03030e01080606040b1c02160305090901060e1807020304030f050d0e1c060b040912081e01030312020702010909020a0905090c0a021509150c0c100e030d0c03020c 77
    0xb06420a0b00880e44281400c4499070b1300404a550145040e1071607802c084c6061060485d0f4024204400b41400401428400101e019810307501c16043d0407459040c01e41d13190801400640c0702d0400740307004100c840004540c4034054106038515080150010143d0a1365040c010111107010b4480c104600007008004085000704940f0712615000d003003c0c0c8141d24000348054400c2c288003071b00d075004480f000d01d03206038a1040d4401d1031070550403010104000304642d000900a016904009082c0c0d10900301c009020b80d03110600307a2052100001002c40d0b2a8024070002c0c00c0311003444000c0000318951a04003d95210390080d04241d0301c1810815805610f69001d2016a0012041600014440042040b49c0d240102d070241c0c102e00142621307480d01402100007526010320091094500c3c2c0300001040054900f0442d004081071040d0f22000b081c10802c2000d0b1043e80022500d186c9441a1804454080c03404c0c4140040800104025841c1280c000194400303000e222110f84203041d801c1c42500d0203407030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 324629181 1250 324627931 324627959
    0x14210a0507030303021b060c0d0e1e010501030309090b06090d020d02040f0506210a0602090a0801020706020a0e120601060e040f180c0b03040c06120207060212070207090e190c 77
    0xc400c2d2405031b01c4004121110403d40c4a403110341c415503001b4400e0041d01c0b003135041112081300f55000b02181844014808c1c51401c03d02451a203071031041c9203041c0214500c10751005052320b120b5520789500f55030b0b03981484240d840c15890f10b68043c1742042903110301e00d000602c1b80d405030b101524003500c00070310341c002034102c0d005a0390f134200d402e4a4408112040c1b4080030102d40d40002d044010b020800c0c00c03d01c440d0ba801118070700030003440c4c2c0010909000d6450490900003004904000e6688010f286440e078082d402507090300003c5410f0710001021031070300042466103150b0301c1c001056a6868544c0854081035541006074020f40e482c00111012007060144075203892402c003240070403c001d0315003509006060760004140346814802e10000440f43c0c2c143c5001c5803442c1c139280a50355811105100280303d8604000d00007840040d44030308118120208911030400da13000d07140c43c0c40d91003184a00b40d030f00070030b490b0031641c001c040c2c86802050426000d0b1105402040010700d002e4a07a102c04010075 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 324630431 1250 324629181 324629183
    0xf0402180901051b132d1410050f0a030f0b0607030c020a0b0703081612020412020103200702041814030309010f06060e01030b1201050a02070b0114210a050703 70
    0x651034004005a400754a80d1502c60560003034016403401900000000c1c8811070307400356060151109841200d00c420004070b02c0c501c040c000740803080c015517507c8240300c01c24514040c24000d08900103625400350044059502c0c103043e101480d480d00c07003e01400c030700500480c401107130203036a80c07140d098203a142d100160040520039190001018400c3c010007840641542c840b60b03103c1c0041000c0d40c0040d0b44410110341007110400e99110303400c040102a074101500740004a02c0c5072002c02c000800c1c3e0300300b59503c0c903203e000fa00c08200540c202c03496210500c48100c020101c4540400c0340c02d0041c00c10340c0c0502a132201a855a0000740c4056582040c2441019030000155002000b40311070708100303108604050f1002c0c00c0800885140400260034810590703c01814550340b03442a00c940d8446900c460f041d240038034020080d40c64040e1009000390407101e03082c0d50700750b500c01c00800d081103030030701d080d183d0a80100101c40080545141d22811403010012010900403c4150b100144003000800051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 324631681 1250 324630431 324630433
    0x40302240c10110a0c03110307050d05030105010e04110901120605040c0807180302010e10120c08100e090c1207030602030103060f05150a0911270306100e0f04021809 73
    0x18a01032502c4a05440c0341004610081504010b82020345401603241c00b00154103060a20081484001142c2035000d42c810150090040ca00100b02c41a8403400a50694078240c0300c0101052250041c00b0440c1c0ea25020803001800402040e6060340c01000703079091203203051801140c0c1948071004502500c44060840c4003040a50040c41308941d01300309500ca0350f0041c100c0000d080c51a580000300001d15180b5030f00d0260150112490307e191003100308030021600c1101c14020441044001040e115086440c00924171480364041016502e030340501d40104d004100a05014032035108010641c682e006e040b046520800400000040f554005503000f10f01480c2c0016020301c101c2e0141c0c0c191400203200c41e611001c001d02c200d91a83d6805000700a4809000e0001003010005080700724910a00407490700c1c2c1c1045000004c02c1c40022540d240700700d401501030300d5468440b10300d05c0307403180b03418082c0070a00908480001c070002e9002d0703ca25402800200030001c80c1d05607484407000f80b0000d0f50502d4807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 324632931 1250 324631681 324631693
    0x503030108011d07050402071406070c15060803040b03060402090306010905070e0f030d1d1806041a010507060f020d090818060c2d0618010e06040206040302240c 71
    0x403007a028441c2c03980c18803040340c40c0840b01c000c000d0204d40781c00c1240640c9105a50102d01c0f5001e105c0e12060625941d0743c05001c40320701d4240750102a0000a81840440700c1131540d0b5030700501c8201d94080d030411289280d000314101403e00982c131000d81c00040c10990001d5090000f110680c0d02085002d000380b00c0030000284030b04040c0030051850300b00f004400d000751042c01da804615103001402101202040c0f03410301b940c1d801070b10070240700c1c400e00f5440c0354401e0185c01120369000c040f200035401010700301da0070094003000d480c0e03d001351091882c1c45404503009002c900c0104605401454002440400042ca80309581c410482220316880080d50181404510800d0603071b61030174003c1000c0c0c3c08a92542c2000d0b40138036940d0351811803000f01015610200207a903400c040c6103140464040081c000c4d543c0500d0007410701021140c4043c001d0640e9800e094001310541004100c05000300c1e00500620310701404c0d60240300c07580f040b58a110b40405080c0580c662950b092002516640030840f001d021307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 324634181 1250 324632931 324632939
    0x6031008011a010903081309020c1b0d0b06370503010c031103220f1202071202010c0209071101050103120f031e09080c010c080a110304030914060f0705030301 70
    0x2085824031105408201d848110601440c1e8004041c40205d03540001c0d00b503551480710444030103081055002000050010071410a5100041020010102c20b0040a04807420120070801c6580c0c54100181c41c5a4140300412841e08242e84030180b0000c19000600c0022980002e480071884600104000d161180364144001c1c42d0a00070301000703003600d2034140b01580c004d442900741488040d041c3d0162200189942c4140c1050b5500d242c80140c00c0505410082c2550410107807990f43e8030320480050040e48004152944031959003c0300e2901030f5542980001d003a402e020070301d00c0107000b034010b1012514152a0075002409a280618800c284a0361000440c25001d0440641c17046c4080915050500c41030301c0ca6601040e01840e90902d0401045006d554240850315200b095190440d9500f0045508455034001070003d01489001508000311001009907041d180000e440040000328180020001c00719243c4a240341d0300300c000d14240c03802c0103941c01e10000d80d008140841d025040400100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 324635431 1250 324634181 324634183
    0xa1e03061406130608060301090615050a0f03030c030516060c02070509100819020a05090406091b06050a2a2d03020304060c05011e0e1b030c010806030c06031008 71
    0x110101da4140c500900b040800c80310a0020a100d00400041207142400501a5034003500f00207040364200c80704001c01c40d115200e283c00302605008140c081c3c842d220000401c0300c072010310902100e80540c0c910781914400d0750101c85540c001815407070310700b10301c4c07c148010407203e10840e140080301d50001d020301c0b4940001d10007054001001c00c110314074081420005490081400c10807180541c2014030020f489100040007040c3d01d030841b680080d1008200310810140b94081c0101c80d004000002e0024103240d0420320710305550207280000381c0107011440f001c1d801035180b0710300b10201d40013950081041900c42142d155883c0d42c184d4284415580660494100b160b040c1e0030415200c64406003a900c2ea18060f58a1260b4840c0038104041c1c4e03004442404401c0d4080380900340010b2080d030543c0101c180c070f000540a690001c2c045400b400300000d0b401441c000700c94010301c42c0600508080201c09005441c103036001000f903074040c000d8240306e1385d481d070300e940c0103600c07134141e400ca00514503080042c1c4c0c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 324636681 1250 324635431 324635459
    0x12190b0603070816030b0a1a040b13030501063014010e0d030509010c050714120a030b1e011409120a08040609170703061116260712050a1e0306 63
    0x1000174545461038520484c0c075240101d40903151181c2381c1d55845001042c03514020f02c290351043c1c841c004d02088414a40d90722201c0b280c01c07a0300603002440001d031101410740411b8007045d02140140e5060b80b0702c00030300e51030442c1408800c0c020800d00c0c2501304c03540c490a0a68000da44440c9094122508458020f074051003003c1d00406a0002000f4003c3c0301200a0468803500c08060144c4600907043c00601100300701c0c695540740c1b01541182c54041e2820f028000d0300e481a1114402c0c01b5503000000c0100c0d80c0440340c1241e03c0e05a580860070030070042048015444501c4564100750711108401c00c3e214100915140284201002584c8520f0040028800c8015801469218030380e40c08044110200281d1841500d810410004100d282000402d42c113118482c80e11220030048504d94040c0081401540c0038003100044401610711105541c440910480c017004002408030205918101d100d0805040c512140b030030003a440070710030f9201201400c000c2a071200020b0711100d0a029040001e040c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 324637931 1250 324636681 324636721
    0x2040f0b0906030c0c03070f0b06040606020102030906150d05071805130b0402060d0603020d030f0e0a030201090e09070e04081305040b010815010509060403110a06020312190b06030708 81
    0x52030a203410400051032600c0040d210900405000c945d0128003c2c0c00d0089500165020b07070b65100ca103d484c644001c0443d001c1b01e5951040c1c0c5410340c0054000d0041c000c030380c41120000080c100c95502c1100d0003000b48020000301c1d4104404005540c0050b4040001e00090321500752405442403100401c602684c02c001c041d04041008100120001f556891400e41c0080e4100c881c103840784008104003000340346039807010b507111190540c26424180c0000e00700340071400e81da07161401d180e01203080c0b11880c01503100080c001200140200b02042e25044000d0b0000341305004d0341c440c2560350341d00303003001c0500baa402e560325a80000c607a5207102e43c0b40d2031400103000656040c84403e003c040041c00ca40710081984003030101c0070140180c1e580c820350445030604001461691900c0e1a400e014540100c3d4400d414090300e080f41004c110140000140c5110310b412200c0019035554250b241c0b640400c1e000c0800121343d88a01d03003000785568035005184a01c070f46a60320000c1d864201c038030f944030f88501c001b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 324639181 1250 324637931 324637949
    0x80c04082122051f0c08090402120a0504110306011203080a060b1c14131b0312090509060a05060a120b0a120b0615041a071a060111010c020601230907020102040f 71
    0x42803803d078001e170b80d821405030819940e9840c0c0c461080490041e00c14001003202c2034940c10200150280745500040c003c0d406090b0b8901040c010505040e9201c0081c05188a0791091300c40607800207120b00c4415a1261300c0030030208400d81c1d5221103070615084400c4e0043d040c56500420a50381f01c00d0b20500c960300c106000318611506000700f1014503a0388804001c2c01080007070240c07001518481c4842f5005590100c03c15100002041005280203214000c1ca88501d4020b00403480c0740c0303030079504042980e100030309003442c114800d0340a40b03c4446c58078442c0511912003058504654800c0b071918020082c00f40c00c0c2e00301413814900380c060040002c1c10a0302c204840300300240300001e500700342d0b0141c81160a000102d0701d031000410403076024a1400411818001c03075504185d504d20304130b03140680e1082e2694902c1c0c8400341c101c503081c2c0e0018440c040c0140e1280d40100403101e0042103000b1101d0801140c800407003c004045510004226100c80c003503900080d0401c91001b80e251020002c0602c14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 324640287 1106 324639181 324639229
    0xc03070c09052d06091308030702070e06010309051f0207060203010914070807020d1416051e010207050718060b0a030606080c0408212205 61
    0x58059089249a4580505200c1148400391a11100102e642c40075a12213045c8202410001c041030308005d40004800040380401004600aa51306c0c3d0192103a182042030034504124003500c000d042503e080a031901040d004140d0000500c0c0b009507080c000c0500c2e11420002e4010510b024002e1440040000707251030681c0d1182c18038950005a0160399030f2801030a89001d0400c480c04400350308142da101195030321407143ca074041c0c0d804087d01410182c00e1540c20f0381200e5940070844084c1d10030018034000d132100c4074081001c2c5101c00005c0d450800c00d55a040e840c1c401c50b01c1404a900c41c504c0070082c0640d0a50441c80207800f00d0150303c1d40310020810001e01801052084402184007080800c10305c203129000c8400b82d8000200602c5400007213661709418007640c1c3c1035058040e0f030500845165020404007a80b007038503016244107030075041604010400790780c45000d50072002c1c12 = true := by decide +kernel

theorem cover : BRFrame.Cov 324460431 324640287 := by
  have h0 := BRFrame.cov_init 324460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 324460431 ≤ n) (h2 : n < 324640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
