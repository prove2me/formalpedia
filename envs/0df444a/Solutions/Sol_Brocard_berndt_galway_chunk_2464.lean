-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2464
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:47:27.897286+00:00
-- url     : https://prove2.me/submissions/3aafc93b-6d5a-4a20-984f-d35995295bd0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 442985611 ≤ n < 443165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 442986861 1250 442985611 442985657
    0x308181302040e0c0906040b1c060e060f0406030809060715050403110d1d060c031306180e130b0606070606080a02011d0a14030c190e060604030f1101 66
    0x140d04000507956030a0158881070000f004142e208162010088486540c0b43e44080702e00b1038445020454956202856540c903480c13030511001c108a0510340c0120b0307000f200b9090103019000031100030048032500d009000907200f540c80040c00c100000c0c801300c00b8500f000002825601e2007510b510b0280310103000e2207800c84809a40a800240c03039a0100c041d2050104806080003c150418070809162640881410034440d0032141c091000421694030750001082034030440100243d0012400351207160003410300c0601c0c442d411441600c51030010782c8034004241103000301280c40e4407000c4040d413900c6000c0c800e840601070f29000345080044101042113032140714041d01c8644040d201440c420f0000608600da10050131030a0150746032424429620031036603038105d520060a0070041c0e07016a0010f820401000c0c42c181d001607001ca9040c0c5c101c2c0003c020281038a9544591040740d4543d14240500c03802030f400f0017018056810940000f14a6860f40d4020f0390905150503111074403408002031102c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 442988111 1250 442986861 442986889
    0x5070b0a05040b01120c1e030501020714100608060f06010507050a150f0612032f06040c08160605130b0a0315090507200c090c0d140c04030818 63
    0x15030360814441080f22640e0b4440c0100f0711140b0040b0080b40a8544480140c07580c850b20901000000000c00039000d4401c200300210f030001c00840d101d03850b03402c1c40f50002c030f4295100c0d03015024242411144140e144501c2043d00d05010052841d07581d0146403a0030003001800e00d5062110604c46440007460170000385c01d41d00e10a82c80d40c500407500c040181c09642c94030354000d50850030400c05105504808031613424450301464080e0124503a60744840b107504c035511102c45032600c42d03c24958105400103195010318852200891415070300d10303d081d2209041c07048000004a40d940810055208001403c0c40d03100456201031020f80c5c81c010030607107902c0314208002090301c442d820000c1c400b01584040c0202124a41030241c0e140514004000400c00706040c02c8011a02d070f080c0015042c100180c055145001e13210701250f013055021ba2000341c02448035411181c2c00d2140c0700c0d107600251007946001d640d9000406003000c1c215075900380c0750b800001c2c00180c9080761460f075009640d10106903a00342 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 442989361 1250 442988111 442988131
    0xa0504060509120f070f05060702100e01031b1706060c0319020c0d03090618081c030608060f0f1b04030305070201020c0306150316080307060c1716080f04030903020f0105070b 77
    0x418a086c062104a50796680803501c0303408144107100c056280c180c000d0501030f4061404116140d00c54005170010300001d4804152071584020344010345412950400d1903036031f51301c4031140d550390300800c0008a2140c00240c150507042803050500e9403084548501d0007201d40c1c0182e510710314810000c99140d0603c90320540c005588204108201038011146081000202c54904840c80c20402455554621601d9040111090081400d0b10324401d0344007001a18402058410b1400c0040c0d440035003550a554000d04a507a400120369152114580142208094245103040925580b81917415820440050303041d030141c451200301c299018045188214411444110440740aa060514283c22a40b001e22072700c130091414001c1e0040082030742c001030342c801c0c00812104000c05048510401a8007124154001c0000340101c8881d42d0040121000c030a0f0f440c0e20050f41c460b0350301c0c4080d1100392000760101d04900010300250800c40d003500c840c020f06040071442c02c10655118100038404803401021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 442990611 1250 442989361 442989373
    0x3080c03041809050604080a12090b01260601031b03060e0a1b06022104030206070609030e010f0e010f020f0706090f08030906030c0c100504050a0204110a0504060509120f 75
    0xc8242c02d100b04400280d814401c02c8001040d94030140d40c0c03080036002605501c40803413018201841010700c1072101c0145d0105100c61103907894941140c5800f070040c021082007e800c40104030b28286055410010f62000500b11030746180c9807008525003607846800c5420010f2b01c04801314016004002480002000416401300c035428000b20f4440000c00000f012140038004015160340064200381c0c02100002c40e0030790440280c0030329554801c5520083d080940825000d00b4081a90300842046000e0b80310203034420005001101d4120340ca071340300000714144450072481944503200081c180c1005004036107141e00008204c928103180fa078403240000340760560911413940d540280c140102010401541400320410001d2100c4c0401082c900c0400070104200c0248501002180700442450000700180d0034241005a2141302040040e0701030382c00e103d2184003c6091000300c850400c0c40b03580d500d080900709203040b03805601c20280c8a0340300150746402e4103d00d6044c4561010401c0c0034004242c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 442991861 1250 442990611 442990619
    0x31d06030f0718291917060307180203060d02150a11030301121403090d060207050d0e0105090409170d060e070219080c03070b04050705030705030f10051003080c0304 73
    0x203c001040c50b00302200401d000020424030049600503001400041454442d50010640b650041d0146003444051401c02085000007950020039003110714240c0c0780800c4035a80d480c014581c0e0381550340703d20080c4007040d10340360b0000e6000b80e0207190841402068040b600d0541d80000303900c0d044c2e5062076440480c0020350b0700e00302c2e0f8201c507a4081d641700f81d4010b58110740c500701d915042021001006444100240144554941c0910880d007441100410200324401541050700003504407000403503840c0308401481900a0281c9060014003505960b52483e0020130b80074400902641f4504680c00008000061066150030014200b02040028001400c514006400070064009001743d8250f4100c54200c29050344034540c0313154066004410340b940c07007500240ca680b4600c01c0c90405012060280e0502c400c010b80400d071442150b00441c22540c00c0c0e915072040588500010040001941c0510040054180d06411103130b0302c0380e40c43d80b00203030861f96516405940c0d030101e0305c000d2103a040010240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 442993111 1250 442991861 442991867
    0x81f0b09100c0c170a05030f0409060605121801020702060d0e06060d0b07050a090b0c0a0605010b092416060903020106062105192d0209030a031d06030f07 68
    0x18903880901d070004954407035031600a0f018a090007080c0078031016085050516804228885a00d40d100b0102c1c0d0352140700d90384005c07140c0c006000700c0000500b421000a01e10b4481c409a8074035190130003503891151118070110004070318144200061f9502480b08402507aa02c0c0050400b4006107035020803503051104d4554200f52005001c248203584144802c000f007960000804d43c80201c03810016515041c0728001e90381d0b80610384c08442c0350240021030700401500815070540d450f105007402d02071030362240944102d5000f4880640c0d00a108c0c034541c0021150041005002d1303034a114109882c003100084a9825610a00003d81d0501c0d266208602055424820b103002000e451510003040f0300c22000102450003101c94201c040f98841c40800c9101c03c0e214051903808514609c10001d62041404880744440c1c0034270b038070303404120700103203051b03550380f10f0080341d061280083c050035092529aa09131940607a0024554211050300c982c80341c1902e0301401940904032040b580c10703503481e05035001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 442994361 1250 442993111 442993129
    0x2004060c020a0f061e0203041a0d0c110309060904020c06011710060308030708060f0a261605130603080d020712020f0c0d050f01140615040e0403081f0b09 68
    0x100b00b40001c22002c002107036200f41c5e018180d504080c0640f0503a5400b090407032440c0115040a20500060075550001180d240c005107021541504140110900c10005403480384100034204140e400c100301c903840a1a03d40c00600c08201e0081c001800c108040513a24a0b0200c01d801a04114103040140700400748e00b00118a00c3c0c1c1200142408100e040daa0b030807909000c050030321000c0c04502000706165580b000c0c0c5040215a020f8220381d6420f50702c810b46549240318032904001070444000c00d10b00100049060744503042c2104655a40d40e150070203000540301c41c5d40104503010340d50480440001c00c031400400540d002880056241e0440f4101054140f50001c1900300b551300c0400c88035604480415407006014045541d4070b040215420101c0c10220000f0035400b0755407034031069a4031105809071150081006840c1d0f402810500c210101140c441d500030001c000601c0c82c005800030f407141402950000360340b00410400d0710401d82c800d09a001c181c2141a400c0c4006c1a40e14043c00c0a101d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 442995611 1250 442994361 442994369
    0x201090b07030905010302280503070906020f0a02060f0d0f020a0314040209060f030109082109030c060a110910030b0f010306031109130b0a0e101406042004060c020a 73
    0x14180707801d1980d0740242c1074200da0b11132a8107054000c0741060f80c040a60348101c141c0b15446420304011400d50500411990045440380c002c00c510b260003250051001030328441e0400f094001300300c050b219408110481d00811640030341d8040800071540c04400500400d8810301d118213016858120084003c1c2c02e941805a52030311440b600c00410000d80d07244901190407220a40e007028140c00700b0408039016000c0060068000140003520141b103881207030006405030325600ea1b808058403103900407030f00d0340302d0007440b4021944101c010540700400c4c2c3d40410100d00030b030120300d40b038414440082160350014610300f6020a640c4c80e03c200c040c3c1005c2c55800403000340ad1800300030040c1503694044180a055540500400050b0000780318507101c036210b900c089800500884241c40c20754031020180c0041c1001c221180a07200780308804a803140604025210751000c000c00555683e414800100b5048100400d40d441c1000c80400042002004102034021999004030f64a41d500600c1440003840d80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 442996861 1250 442995611 442995629
    0x50405010905073204180506090105031c0c1e0506010509070f120f020c0709060902071a040c03020402030903091f020303010e0a060b1303120c0c050d060f1107020109 73
    0x1040000072940f042c442c40c02d4151800c540120010100309400b5113108401200c41060700008012a4004000d00341c8240c0e011000014803580e61618144a1410020301c9102c1d02b552003001c4c40038030301c080b4003080100c0100c185414005048142c071000810014802a03511081000300c1050030301406209580c09031805881401c020304003200c004181007607401d04901003000744039414a280c7c4142d005447c101306103030001d6407580c000900076030b2100c01501c602e2401b54680800001d0f0100c03d4025904455044034004203410314503810204408002401102c41d0480b000c3c001c001a500c900c00355000d07a803400000c41c0c8640f8000144030300394404000c4640e050341081400d05901d540001240e05681442c0c1030035026460b08094100502400d0b00402172400d03002c140304416030300d030042d00c0d4100c0380205000041c1042e0782400341e541d140e0148003d80100030840301440141048500140b020744101c3c000280c14041e8054030701100c01c40e0942c16010500090200250744e8841c1001000d001d03118 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 442998111 1250 442996861 442996871
    0x705010b0a06021c12050709050108070e0a0e070203190801091505152d0d2403020603150301050906070f050315090a02070f12030f0c02030904020c01090215040504050109 75
    0x100c0c040e55640300030300b04092040c0181907100c4d400d480340200003650752150000340401e0074031050180c14040140905400960f00e00300040ca080d02c680e01240b8081c0019002e1081c69061007100d6003130490043c1032405500c002c001e4400c0740111400c0e8804040d41d107076910089941064903000640300303100c06200021185240521043c0c0c0c65810442080203030303494080da0740c00c0c1c0354030400c14142504c0451a05880c403800390003000303400720010000284030035400c006101c000c129201010f4200224900030311651030741800142000c00c0115003201410500e10700c4680d000c800207096440c21214515a508001e00381708190350070200b112126859410003904610306551008404160f51342c1c118810000103004c100c540d11940e040303480f501c2c7c01c220340700c041c03054a0505a0445410001c40b500091814000001c140220301c142c03641d81d090750740a140f41c1042c103001c000181d040300c064a0f62035540c400c48400140d071440b4056048503031a00759252103d242904010464905034004084a8201 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 442999361 1250 442998111 442998119
    0x92a110c04111210030206070305071505010b07061e0f0209040b0906010f1d06070b070207050303130905040c3201020d0c0219030c060914060c0a0209130c0306020705010b0a 76
    0x41d03401c2d522980f2990a0300103180d80d4407040c0a00d06078144d8000b80d040301000a11105240c0d1080040c0101070144002101480c905031455045030b60912441c0c90340901402088002440e40c0c000031010000421070901c2c0e116034031b520341c2c01c0711103040c0f0740f486455000507040300034106405011503022040795890002e281070b40010381085981440e0500b0040c8580c4050358600300c600c00f0548900029140f55100c0405191071003403988240c8400016204110300000c107860300008a50500e10341c0c2100065951600c00b404001d071101500440342403008a0300440d0311001c642e00d28138442e5071000305144803079101e203500b41c0c612400117110b411074016130710301d13020b25802c00c00c15843c49505482c403001c07991301e06840417200c001c0c0780c100820000700e94200181c0a50b011081c13100380d0b02000c03826000380801c0700411880740304070f56140000b50007810716000945818007a0a81c40340e020441c0141301c141030741d40c418980d17400b500304a94980d030100b00c0340144031091046004201003551000300c180c0c18 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 443000611 1250 442999361 442999391
    0xa0b0102010e03040b03180307050a1a10030312020901020c0d050703030f05070c0302060d151710270c0e0c0414120c060d0b0904080912030a0801092a110c04 69
    0xc007c0c00e40400859146040141034410403c13100c0742500801901c004079441e00d024801005c0384075a00540700c0001c9c010944015561b0050380403179606841c1d070b600c542c440505180113034000b041d449056000b01c0762070000f40d481c0c01d22040e40e43e40c4940007400c025030071407070050302101d0702e800244100881446244001040c00b540c0c0416650129036480c0c03588480c1c0842c000cd07000003c03a00100003162180000e200b40850200a140491802650350049500540e4403c80712803004450700b4684d03000640020036006890300064500606034003c0c2541c0394103003010010800d9401030502d85002804001c1219406403d4143d003404440800007ca00c60a05c2a42d80d000340c001c6034803840f800500c0900042d407a5004e2580d408014240e80780519150034256900e0300460035484c02141d094107081c3d80c040b008002ca604039607058644140c00d90805034804c0060126000c241d16003040c00300304091b5101d80c141d0f040031402282c3c2d155a036168401c13403d181400042d007507150096062142c170f0944001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 443001861 1250 443000611 443000617
    0x160c0809061c02122703120c040f0806150103180605060f0310050a0b1807050304030c060e03030a060f06091205010b061b0d021b13140a0b0102010e03040b 68
    0x300448040c1d440e040752650720720030b18610aa181d0340d02031001512091404400001c1441450074061480740c4072507446184607082207103100300c2c0c40d07134104002401e0b00980c00c00da015001900c100e510342c03c1a0b2601902a40380b00c482e0444e038640c0e03000e00c040003040e000c03c000a1040840a1030284803905025100300400b140c80c490042c101030b1143c0000310180c8405030340f41250174005040340c0c1d030891041c030540001c2600350f40d090611403d0000c00e02e0a800e04040c0711a401181c107422001b2076841f8072080343c1942010707004070100301e404e03903000b000b050769405003e4510a103e40030b940d070b82c1880c2c0210000c6442e194444200d81c4880042041800d800a50100c21109103100c0544038180c1460310b54010964000d070306a00000c08110301c444070350342400019441c1d4001c802c45802c002002c00582e5507141610301c500c400c0d03003002c0b03c091550401e060f484042c02c00032000407a65080d580d81070303a480b00d0704580c41c03100c0b6a07603509510b0701c640c1e0900034644030b1010b00002d03610700350400c2d8000d10184 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 443003111 1250 443001861 443001877
    0x1802040e0312060114071104110a0e0f06030402030a140a0507060914150901051305030102040b2214040e01020d050115090906240c1704050f01020d022503020315160c08 74
    0x1840b00c001210703162581d42209c40c0100300c00740b4040d920200c510000c0c04011258109500404280040c000241000c9003205e005640050007484107001e282c0c3d5901744185104a03092403402035040200c001181000080058149904d41c0245181000d581d84680c3c020003080710300c100f80c0600f24000c011a103804031961172030b0030710303040d591040110400545101d040e070007181c01d503100283c0002c1c1c190552015042c0084030341c255110207241d0f81300f030010b40e8203540603100c40e0703a213172040f174512a00d001d501c402c1d02c52242100241c10060140d40c070a0895109910054180340810088414141d01c01c0c444809441c0014040041d035007080c004030341000c41c40400c0414184440200700c0c0f420f00441600443c25408414904210400c0035040e03000d403c94401c040c01010040b5009403150b0012400c0c1812028030750003000090601651a410301c400d00d140e0f503d000c881c0f0040480580c5041c010704901c03103101d6002c0319060621244801c22a92842e094804200d4800d03125400070b040d40080328130325 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 443004361 1250 443003111 443003123
    0xb060402070c05041104080319031d0606090a11070b190e0c0f0d140a030e010c02030d0c0819020a1202011103040311100e0d0207090203191802040e031206011407 71
    0xe00011005c65000d44a150002c1c0380c0c502c0046107200c2161036600c0b80a04c400350703079a414000001c0000c81080909030810320b000c215004000080e1440c2040c501182c0d00100041000c9011800b10000000031703401707001c0545595414000301b254113403401030102c1255051400c10020303440195245510750032411032051041c1c6c140030b11252241c0d10400c242c1c88803908110554200d80b802d070752141e9100c00c0b00c0f02c00c03008600c42d20203103c10741d805424114217a640150250606501c241c40c216807507181c03801d085401034400e0060401c03840850103a5825580c290300284031400140c20044010022a03803c10300b1681800382d84001c620107801981e420a516040240a039141040081d013400a90190003040070701d0140506200303500011080b000e20540c3d0281c80725070751242700c0e41040e4401204c0904e45c119405022074481641c641c080c10b01c040070160100d00c500b1702c0c3d40c0004c007030380c00019403000310fa0f2011480c1066002082c00c2d00c6d402c0103003400c1c400195980a00c0a0031540182c03003010f415 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 443005611 1250 443004361 443004371
    0x307020105030405150106020d11010c0801291329040312020304080a08040e070206070912060b03151b070f02130902090a050703060902040b07260f070b060402070c0504 74
    0x10082c003003240c1e8001406411462217650b07101e483c000c1da100c81d40e00c020300c00600c008080c8040d420062045280071802540c4600381e80e800c20b2043d403c0403e03c02c81c40d588032044918080c04070001600900741245801071158092442d103503102910145071a00103102200d01001186088240003c850440b580a80b07880c5104024580a9007107000f41ea00092180c05840d0040c0d0030090988001c105485080019684d80d4031281001c90755081e080f104040810501402480340100c1d00300c9101c0828071480703010070b60b511000046400c3c9009030b88189203444203102440f6140e0706403181d42c181d0901342003825040c903036203807540049480d5814019014044038240c10389100196000480240c0c0c000d424052141494051031004084c00c0300d03140000780c0751102c0480c000c580e90084071704403a01d404805091080320307100e4699240304981c08007040010344c80c6800360700c01c45e64090403040c950140e150f17031601c105041c440d0403028014005482284100700d6440024440c8100405558041e6000030b070b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 443006861 1250 443005611 443005613
    0x50301021c0c270320030703110316080a031e05030705090f09040f03080603010903020c090a021603090906050d0317060301020c10060815040320010b1c06150803070201050304 77
    0xd0103c01c4031034058240d00790500d400c011610040e01c0001100e11941c06500c41441a0101c0041078070b0f140c1000e42d01d42c2101d0b00c2007002ca07800f04212520400c004080d01d0b510360303907000b1802540741ca59000baa40d075080361140409243d0000d00d1201020203043e5800d40742800b8000c01059448002e051505028002c10111300d030b070b29041d90405110358060041c00560826003040000d0344640c80c070840000f0007900c0064160300b0107006108a199040d00106182210081000841a801498500315a80c28040b0701004c3c1d980401101d540b5000743c690a41e504e003003c2c422000d1701d86c1904410300980c0004403035000607620504003004150301c00786417017040d01c0d250000390181c0310b0304410b080130303105d100c030102e440c43e0340c0394080411221030000b12007405052107804034040004480c00360104003500400a5008182c0e10181c2c100d00380380000043e9400401d000400900d02c80035132011600380f0100082c2000341d40d105a0f11203d84c6d44031b682c80303154500013000ea5213100d60358000341049008400301d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 443008111 1250 443006861 443006867
    0x305090d020f0303243001110421020415031205120711070906140910120206031003020a15180302030c270c07120503072a1401050a06050301021c0c 65
    0x5c2c0c500c40c01400c6a81c90049201c8405d8505a10764030f21218000040001c226804144910051029000c0c0818200303071500000034034a0820201c0244a819030b403c1180c0180d44510800c02e6050051451100785419424205004d840400c610010b000c020050a8030284041320712951150300c5107401480509104012800e0011036409030520a01304440407070301060702040542c0031902038590341465696a01c101042046910801c4514040c6404030b10142c1004001140d2002020582c092895900d07804070b400403646a0141b4519540208910a030030761200340c0003244d80180c1d10100c580d84c15600002e4660522411041c440c00b9481124031004086490f24200240781080044d00303882c04a0000341a0ba0000b00221000b914640075410b119028100f66801440103589502c8403210100c0c6402c0c0750015074000d1213041090380380d0f140c001028107030f006030740315a404004170740e03400c08103900703000d840403500451303c6a40144444294002d01580381f1681e5500500081084401c1403016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 443009361 1250 443008111 443008171
    0xa021c2a1403091c0c03060207050f0604030c020103050703150b0c071a04060807090e01050603180d09031e3c030801030b0a0b03030a030902040b0301020a0305090d020f0303 76
    0x618511503032039070841d8400301001400d40c0b2181620a6070b000e12080303c0900002e128020020a126042402070011440c00e5015005c814407500840d410861104501da01c1c0c0107045a0442c00901900090011940d07d8003809070400d144d400c05101c01c0c0d68141c0340b42c00c2d221a5015141002a0202d04d4a251060810240004180b564036442c00702c55000082d40c469802030184070003049910010802c5281b180e501c2c003003200c4000d0000040d41e42454100446a0b002900b0590b11a988904202803164148110071a10300243c1350112072501e035203080355070313040d60101104009046201c904040350240c01180f0340d2810406c80c0e180104040310b1414a0013010950080e0100384d4225260100358100913401d050364090b51411a00369070380080c1500b41c1d080741e541150150414020103e54138042d80003403204900c001c001240307454100b804a400c98000e014040000f80c3c460702444444a410701040000812a01c050b10031140c400003660768921000c0e240380c50380e1040301c0c204c0d8503045140400f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 443010611 1250 443009361 443009363
    0x405060f210c0912030d1104050a170a08070201030f1d060106050c0d05030402040e07180e0109020d03030507021002132102030d08090708100507030c170c07061104030303020a021c2a 80
    0x3007142403c04031f80084c450b0414011340f40200464040890145000e1100c0340200381036100070620f140316907449084540000384100e05050707d441e0041d0040d8110f000e4201001078584483d6540c1030411142d910340401a805141405410021080804c0b000b01d4261600310035400e085903640c58074804100100002d820b02d81c568029001c02003403902c201c0e200300d9070340309100609200c1c0400252a141c00c071002c2c0c2c540294444800d1303140a00003400b070342009138040c1307250064940340c030500f0b2500e000342c1e0b01c4480000701042c0c4411086c4010703242c907a030304101450300180103011580d041d03010917500d1411f1044076060020100010b10102c00030010303130000d07001c03e01c2038484050002003544040e1009554040109040456040c03040344241c038621055005a81d0100a50322003901e0850540d01087d0b00b900c038590ac407121b082410070044000c10007184240ea00690302c410701d0b00000d041c00c403d4180d5201075900070702542c10090340b02c04000e08120304441407410780a0b0311001200c04100d4948 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 443011861 1250 443010611 443010637
    0x20f0c0a080a11070e06210706030b030f150c07020a0b0a0801050a05010509180c07050712030806091504050a09051506011103040602210405060f210c091203 69
    0xc4000100076540000d45000300c12a1100003041d5003080003140c60341d00c3c6004003040b140c5580005400303450900030042107034110313107100b800302405880c889042a4039a0458030100791100f00150740c43c1000c115007045018010058200c600c4d01c0c0181d44581074003c0c041c2d014403e40403c0b0341041d503440706100401400c258014954030120100068039060f1b0910843d4403542c0e034403400065550140080311050ba40040004c03140304003c080c4410703800380c003401603100342000340000320005900308a4076002d46882c1c0e0300c00c807966584c0e10300181600781c001c280b030b8002c0d00d41c20203100d45500c1064030841c490340100c0c0c2c013150950310200c0c1c40f00201a0b01e04080d05074490320420b4143d550080a0341c90240b482a6200540c0003040b80f00150342c0e02c180d22404006034045604040f000a21100130802c42e240c841d00580b03032a6407480000c000b03030004028050100000035500c10f050302c211416030004204408060802d151040039120240a150a06400b90104006c0030b04000d2781030084500b1402c80305 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 443013111 1250 443011861 443011873
    0x601090f180221070903060609051302040905120c0105010905060a120803070516060b0108070f02030a0e060d0501060807020c04110a0f09080712050c030109050a0f0303060e01091e05060112020f0c 86
    0x1490041034220b1502c41581c1d40c03446e100f408124209c0c03a010b0710303100d18010a03201c1104402030303080c0700052030305030010388450059112030740454212100410994040000128455041460001c1220800380c1f01d64030034041248100410590f003801c2c52240d80c1c20541094890b5a64901900c8500c140008502c047c00700c40000800c011103a0320240790444203036500e0781d82e56564201541d41c00c03040c1c4405000b50b40107102080601d4400c0005400080c0c0150241e410001c0c00d05c640310a03508283c00150100300c0c00e004006021760b0402981c0508001150180620302113402c3c507540c1b40c49010009030400002841400310f083c020392041008200c2c20f400c48002940c0e42084016595000004032a58050b40303041c0d00003450140512510b40390841c01408485d82c4642d5082e840500c544c0d0210706240e102c0310001045211354540034020400480045690700f0900321300350b03000401c01c0d4501320140c9850240011a640308250940042a4900c0141d0f1100b0f2600d20355170901602034200d020748a46 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 443014361 1250 443013111 443013121
    0x90f090d2304091a18060d08070206070c050913020a030305090402160c15050309030a0e0312070308070f08150f030c1e15034b0601090f180221 63
    0xd038070400b25800d107504c00b00c40c12402c0c40d0411103050091540e9510300c2c401d40e00800c50b50b262070401200d04038440e100c5140340c480d49038045807054124290a681d00f4281c003100f0070160030f040031071503030007021480800f40001c040d80c00070305102e85501001d4100000880c00e000c42e80c41d00d50454072005a403500840019a0625002c0c000d41c11078000c2c2016080c8028068104600441c19603000341070b03d502842c204141c6034411101d0b83c0420070550f51500c900700340c0702c0d98440385000620540d40613950f001e98502e8030f404007070024070041d00d6003c1004900010804001d26603508415044400c45040c00e1100348800001c0c50300f8091030b111584014554240842d111804540e10003e0348261084050250010740115940c0021240d00f0344030700525840c102c0c007070200308005401070b148076104500d8503c1c1c186a0b00117190245810a6090b0088040c40015a000301d49100240b10194100465a0619501c0785d08510302c000c0004c4503d402181c9000000b86c0351402c0302480203c031040c499a4504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 443015611 1250 443014361 443014379
    0xf28050a0f0c120c05040c02010b090906010e150f010e031f0b0901051c0609080d09150f150b03090f15040606092c010902040218090f090d2304 63
    0x4000d10071107940d241d0840020f4100300700c450a040140e0031101e100c10711840c00c1c041c44064092892101d045558442035056255902282d0790f016440d403000500256040240f0076001c80c002034500345507905000140181a0b444d04d5030040d08010a10b44024000c0e03500000ca4600540c90a0682080800809152604d000c640c000802410200c03240e02e51660303108140580d0386081c0141048008014807958042040d03034700407107915882146214503006107203182c041141c222100481e0b10b001c09140605902c0010b00800301d422444240030849a110140c08402140d100e2103400302c5850080005a04a1814818030780140e500c0820b4a400c1d01060004440881d400c4400725007540c07811034042005c0c070751841440e401520242d5050030f2501402e10300307008000c050006040540d2194081c0006032154000b400b8100c5d10145180d05d98410281004043c080083c20300c0403010404040105001c00000c1c040c281e800c250070454035600070500300700f23a0403605500d00d8944030300c00100002c0b0440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 443016861 1250 443015611 443015633
    0xb1b0d0e09060901080a120c080a0c020f0a2121031401150503010b071407031223090d020a0e041101030608010c0906050c030c12120601020f28050a 65
    0x20308036000c2010b40d454a0801001c1c000130300800302c0c154410300e00c080006100c1c00035160559480e0410805502240d911640325512100150001840c8881040b045013040c5c00307210313001c507000c0314029007403410840b00498260410b040c0201194004035000d05208240d42c1d2011400c1d60051301007914440d016014020700300a072150300916400200028a008500c401181000d80c85e13555549540d103022001c0d56250441013042d1140640041220808102006803030300562040d5014000e0094480c00a0b10410034040b40c90040c4200782d0f148016407001c6002c95031601c0d01241c0109220790640040380c140d1860f6000240300c05075000c140020300c002e807001c081c00c0d403400340e0341030002c01e48800880d8241c0700350f00295030200b21411810300c400c83c00b42e00500300c444a00c0c1e08403410100755003422403500e44007104030300d4500c1001400e1440307403440072800d5920420a0000f4503641303204904007907a0b000744026600f602905c0e0b4540c1c0c54602c0034a107041c80c1807600181200d54500c0759080c40c43d40c4075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 443018111 1250 443016861 443016887
    0x403090608063118050c0f010503090a061112090f0f01090c031203060302090f01080d050408190303021c020d06080705060f0d0612141b0319150606120e03040f0b1b0d 73
    0x802079487c00b5182d03100740b08591181c442d01014085c1d00f0032607a0307813601800f001032542060746002d01a4814500c01081000e1181140070f00400b1414071100015040043c007a100e02c24507414070814030045480d41031544100e907409007080c014203525480860042401d80c200135484990300050181e124000e00f40181a611800103494840030583c1c01070344d0501c40c0c1c0c410314800b50004001d0405c4840707201d81c1c0c0d895050203405c0c0507180542110f40b8001c04020495803170304c00c96012860018000d210710481001c3d000790702c004c0c1045400d080002c0d0031809070000c180980b010010301000000c2503030300043e0081109400c3c2450901e0300340344c01c2c2061031406070340c0700a034811200e21426800d03400b91107591103400600a4003460b00b10118006451006581c16a01c102a10007100b01c1c00c0d2840c42550020b00d110303612104024151854101610201020780c8181c6d4024881881025251440c040c202c800d0021100c0e941c50100401c0c1118190b909181c42003401a110080da4858108003081411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 443019361 1250 443018111 443018119
    0x8120c0c0904020a06120f0509010e060604050708010e0a0e01020a0822120507050f06010b0703020601090203150d1a0c1323270403090608063118050c 66
    0x280c0e5100007031066000c01260069405030081c070b8100207050080d8086221141b800c44042001c82e0700b510301300259041980c4c2e07820340b44c3d03407421103051501d02800480d401404c111b405011606142c10020031000040c09584582d40c4220040b5041c15050303848540f80c011344c980290f4640280203009812080300300c07050b6140051004115010404a07207509400c2d5074003004490300e4400d0038100b10343d160803400c0210b9003032049900f03030f0654030390810100d4024580e41203c0c654815080ca002401d06506038001400c050040c02400030301d441c5212854509a0140c4031000001080d0408c01d1078408079804502200c1d001c10306111804080100070126507100c511503d0307040c3d503941c0707980400300003c1c030250441c1c043c0440d0002107464042c454181c401c034800c2c80600019010003842c00f1100094800302d0100350092410003803950400800b0350300c1042203c02840402c0300700c0110200008155250b40c5400080d842c00c101c1400503030203c50717000514244200703902054039040703641d1050104c0c05442 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 443020611 1250 443019361 443019373
    0x702241005030a021e060c03040308180924012d0e0303120c030a06080f030307090e010303020c01080c04090f0209090a02040303120504020a031a04112409040608120c 73
    0x11401c0003e4026040c55016050399600403161040100c0c003020040255031200d41080480c1d25104108060300145008030f5445e6130b20300c0d00140c0584104814000c1c5070056003480204002c0f4442000c1110034076040c402080c11560140c00100d5002000700c0410015403802c07040450101c400006802c05100542c44c2d00c0704522196080541c1c13802294108000181f80c10000742050745e01e100130b540c1001440801040701ea0f122580b00d13003014920b14228a40b0350010040100c0c2d2548114040000c0040c1d2855800702d50454900948854005c0021414032212001007807040c540c03001100c00030100d820b4204000b004000d01980030b94000d91030284210070410100742d12002603c202d44c100c0380c0c1a00c600c0840c070364100c0c14501400d0700030810b0b0707840003801e200003010030241041e100ba52840a04061080d25207071034000d12108038058542d000e04144080c1d10541d0314110188408022004c50143e00e035601c120000303014003041d4001960b84d01500218201140e48540507204030740540e800d44103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 443021861 1250 443020611 443020619
    0xa1208040b0702011b030b04060f0e450a02030d11010e0d020601120303090b0c09041406030c0f03070f080d08070f120c0203280207081606030507022410 67
    0x10a03905c400d20b40301081d0007000e616800d428080d9201914142002c1c0c008a90709580303c00c100e00c143c1c420350004080380900c0082141c016442c140b030301841e580f8000c8800e00d511041101d01158428a4102c2d00441411140e8000c030b0202007003042c0e0301aa00038101c954100304207100526a110a02da00303040c4c3c1d0f007060b0154002074400300b070140e0301c65030310741c000c00320740c0c1c64a00302103107041042c641a4103060740d81c5400c6012681000505215900445c0440d0b035940c3c91000388401c41c0c656048800800312141c0501c040d59138080b410140b8018200c0e50440b20305204400241042e07903aa04c071600100c44003c0001d03a1710408034000b04881129283c402d103d54900c00309950f072001d4401e130711002403c8941110380010080d0300100210650340304803800c004a41190f118030100003405030300c5140b00744203052604c0742d040020760042d005800240c0040342d0320b40190035204c042030080d40281a12030700091b41203482003210303403010071011441102a16400300c110031089010fa40080b22007590190101d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 443023111 1250 443021861 443021863
    0x40c03020901030c0c020315060d05060a1d060f010605031b04030b0921030406090311030c0106053c01021216020301050606040b2b06060201050114090105130c020a1208040b0702 78
    0x440046c1c010300944030b9840340840c8422124001041680c0c400141f005041c0410f2080141c01e00c81c031781505000a12031801486100b030a0503450349204641c0c4070004014071000100b04440c1154407504216032261502c3c00700c44000d0128444440911380c01090000911180000e11801084000300b07444040d245d0140d8200280b0080e00825013084082001c81c000440741c2d03100941e900d00034030740305a071031011009050459120340032076021a03440e068144039500d40208024041200445031233103180d4901402062503d11204044400001c040c92141c0e0782d00038010000764817500700d0085d551342c141201182c0e540450082c02d034000e40c40c0c0000106c840c203104044509403803040300142d0510000306206148010075000c407031a0b01a203106001c1e5944101d024182c040c100301c1d000440e02c1d604040000310441c00710314600d8400c841c000d00410013a01c40e0943e00c1c4039009001e070040750403820070000364a044128030000700303541007a00784103403023a50001e00c20780500e1080b04001c0440d2101e560032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 443024361 1250 443023111 443023127
    0x4061803020717010f0603030807030606030b1c020423010305011103040b160c05030d0608011a01050f0f1c090b0f0f0622140f07030903090e0a0902040c03020901030c 73
    0x180981d0005106105040c0f48683e40d0b161101da450000c035000c0d14203505a02a24003650044011510013000d1080103a0140030710300140ca0580b40401007c580000000d4102c1258000c0d8038203082200302c1c00c0c065441c1c0390440d0a607041902040c040080200c17008445045d02403005481c654a003002da12400c050311800c50707018035000404c050268955150800e158251250024180f094801002000a00c240b0190030303050059a0001215854a8012403d507512041d081301d088500c10403040d00b50b03800c20141c6030802c000680d059192100c01289010034440c803110002843e41c0d0341c03101641008540c00054003e8410341040507581c4808002031404241070314954080403401d80080c405084ca07002400540c1550a01c24851960002031003007120f0540d03012240d0f03a04918200328600c403500c15225041046441c007005044256100181074001a000340541204c022001c11400300383d90b00908221600140200000103961402800070341c070425000d40030130305040d40c0c4002d40c0d0040740720f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 443025611 1250 443024361 443024363
    0xc0d0206310b13050405150a060f0f08010e13140303091b090f150d081b0706051c0b010c0624060c0c03060203060402120a0b090109022809050d0b040618 67
    0x1a030150f40e09040070800580001044130580e00118110b00d545681e8984000b0010912910780080076140202e0051a0780407422652091014010040003000591007011758488105c03202c07415043e070710f40740034210b040040c1034000841c80003209010351050045405c8209469041d04540501160001e2040c041e000f2a02c0c290480200c0e000078a0081098011245e5040000d008080b9800d581c1d1300d10215402900b80d8041400000e06036024040040100348080c010038202181080043c1481c035078070038219880418015195440f105e560b90150b0360507440e090344500144444079005c03600420642020340c03520740340002c8000c00150701e0f02500817403107107580049407110b11700d00319251000698005841c03950060750800c140c0041e0000c1e80401c40c0a06c0315860003041055042d42000240201038000710345081c410805c02482c8241e85818090780705d00c0107943d482647c40076400355404422584200d40105100880c2400c1080c2c5c4c24003203201da03100d100d04000b94000001c80030410703450030368 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 443026861 1250 443025611 443025637
    0x30303062b030309110f090a0b1f03020a0e09060303090d0c030c03050a170f030708070c020301050a0e10020906041827050118050c0d0206310b 63
    0x40480d5050401d007111840e07400c0c0403a25862200480c00e51100581c8070180d080c0c0001c1d50b00d003070000c00c108084407100c02080c0f0803524096071045840000304400d00c0544135000c0c070b90781c994081d1400e482d410000000c0046074070700340700880303007064015001c0e40c4540c0d4070000282c0c0b143c03d1007106250080000c0c0c02081b0260055043c10381100c180520508520f406480c80403103d000000081c40c8415113801840c03103140a0445032a940c504010240300d500340ca01100c00061003180d50900c0284e0641754001c0b00c5190484240c1c032800c0e01941d20031140c5d040030703406508000422003910701ca900300e01c40b45110607046601c0c054411040c00c089000301103000d60b00c0b003400c0100304112601c20030800300310f9103081400520b41c860aa40c80d0040b04140c0c000c0c42141c000b0300800011300900380314104201c03e2918081038014134070769859803a5040072020910850a91034201c00f1b6403110000d694080340100d0b604052000d0f42d40e4100392502e00c006030b82105840c4840003080c0d6810b2441502d000900c0b00c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 443028111 1250 443026861 443026867
    0x2040506090702031c02040e1512030a0804080d0207200102070b090604090b01020304080706120501050105070b0414010b3d090504050411030d0f120e030304060507201015050303 78
    0x14491031a9549440310717240c100d50240004100c4801044109005503a5404242d408004000a210440c0d0080d520a203c6070400d101400d2915081042164040d0703000c01c5e0304c0d0345c402d0302c0700a24000340190740f40030740007000c0c001c540503066510803505803840200340c00700c4000b9540c401480d0118881c4500c4143c00c80410b10040040c43c01c1ca17013140c0c060f440140140e030b08050300c1d0380d005450040c140d405500010500040c40c0481c10091040038013600080c41c16610b0711010340c176402c00c1044041e0008060b0b000071680c88285900c02e50040094400084c60308035500800007006801411102c411894620345c88403490300c0356016100c0040362001e035104ca4108900d1b203802c2000501c4c00410a0b82d0003403603025040c1c2c460740d0500004140108585803005c00e844910300c0202040350140081c14000d2401c4402d0f00ad09600000b80c03a405540a08007180355520320a00b190201d10300c000030b514101600c1c001c048130400c04608802500341c42c000400c6115441e94802903003000d01d00c121505a0010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 443029361 1250 443028111 443028127
    0x7180807051c060b030303190b01050f0919170c090c07020112050c091f080601021f0b0402040305060f040b0f06010801140a150906020c03070b0a1d0d08070204050609070203 76
    0x2145032403410034003c03200002c1010200000c03a003154000c8030000c0703d80b4686403a414003030402d4451410040d0003841c1050800703042c1c034400301e9a446039010f03240c440c210824450b00025020a061400740c400701380c50410045180c4201941d0301e480440103842160400005900701000340152443c0c135805944072110248510b41800061001604100d2414010841c080580d01c4910b407000202c1000900004040880c0c0c2c0010072a990141c0054119000310301d9030100c3c6107081d140d039041040c181c00000b404c04070b801c0000b0700034070540e0700c000c0c10b50240c1010071104034003000b40c15108a01921076403041c1d82e80c00200c00046441168001d0214240000502c59507004d44084d4825000141180d954580c035040c2500961058041d0f0b040000c0b4010300a00000303a041c45918001201075005002990a12192a80c2c60140d420500108000c3c011700b03040e10912100b0390003c0c800d02500100e22041c0303a00700644144d005880580c0100d09210104809007404d000c42480344c05158040c600301180 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 443030611 1250 443029361 443029399
    0x81225090828021c02040c0804110f03031b0106170c191215020c0a0b22080417030f0304030305011a030f010501050d020405122d06011215050718080705 67
    0x3013910700690040c0940e4040c00141c580c0c2c8100f0059820710b80f0b6450203464070b4a40b145102c98030029141c095003030074450001c41d40b1f0000c01d43d4a0541220503001d080103144d2240b0b401010580c0c000c81d600c9030744664112200b85e012882041303481c02075421074040c801c0e1010103d46a091881001c07040b03540b0505400103c1c0800000c588003501451016241000c51825246050f41204040e509401008140913603019515407000003403060713001c40c03900446142c846d0303580d40c0140c1c8103e00e500900714000d119221428001c80e804890603294154403402c1c2418002c004120901070203c0074071070420515011203150041d28410071420620070010303800e050045401ea0032189070503c03981e4080c013010a140c1e845184205221504400070454175190404c80c020800c0020040418102d44018000aa00d0041039131810340b0f848400d00c5c46001030300d10304070300c1c107000040328032418500e000180006507034081c031041c42d0600500d500c1c0d0300003034890981580b82c840754401d8550003882002c000d40d039840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 443031861 1250 443030611 443030629
    0x4050108280f0501080d202d1216020f040f0920120d050c10050703021b03030105030c01030b0f04050412080a060308122509082802 58
    0x22000c4042401d40d10300880c41e400400e185a080c502036142c0c00d45101500e102d220306401440040002d140580712104040d000c0f0109044580c12030703000c4000c510f449981001030b0310703040440c2c1008000c030002d0000d51880b0000d01000b554114010880000d031003400a00070303a00b07040400030b07000e1202e80c65a42084039054030400155046030302c524000d070014005204001c02e0501508108001e90300400e40040790090b0021420302c141c50219040c0d006000004c0e8840c0030300003505041d6030322048491007518104400c0003200205040c01e0400c201c0541c19000740180c0150740d404445583c21240c01592240424010940c050340100c2103410550310940103021403000182c030800c0700b141610003003020768004803000d40710051540911200d80d0f82c0130703450590040e0f60000421503903040d60340e40505440307402c2042b036041e8080c0d000b107035481112400e402c00c1503100c001202d9624000ea00042d11920082c490441c160048448003209104150150715190000707145031000da061030360030054011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 443033111 1250 443031861 443031871
    0xf0106050a0909020408100f05091c0509060a0e181603150306180b01081c0c15050906011701050f060d051501091e020c060601030b0f090a02030f0708040804050108 72
    0x6905100090f58514920051018181c080090310f4000f000c4010101594150209242c1041c600b00030451040000700312404410401c403541007103d8155501259240106190203a00c400c0000d09820210b40080380030a010300140c410640c980d06c140000070307a110702102c1c003212541a40040401140c071075844901c0703808040c90580591a101e0b1a00402c403840c20303040c0c00441c2020540c20080c0024840d456004282030700090100f140b000e01d18410350318200b101c40d01070000c0700d2030900400c049010411420088003008100900d026200b05690720802e03c07803010540603c00e1180c083c48410301070a071241e040001428401d4030b0710400c2c090722500290054969019041004a442d020145098000c1541440115914020017007c0320407801c2440c40410961040103070b50030620000c102c0c1c5501c0340342400d0010f4007050000200e4444080c040d02c040e8802c151b50204002d441c3c2e254007850051200e128a0090742c1d8400d04241c8400c8410345000e0040101030100704055071103034a03215880 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 443034361 1250 443033111 443033117
    0x30e0709110307031506020c010503100e0f240a031b0320010e06070209070e06040801090f0c060e0901030602070813080a1203020301050d0809040608060f1b030f0106050a 75
    0x22560380c0c850034211a003403004641e8598001040c4040c880d458011148000300c0c0b220001100f0b0f00d00388019640d400980807060501001200240184803041450b0700280482c1026a10b9071030424013600050008a8548581041418030304032004000b1086081c40d0310040c1c511101c40d401e5403120413410340d10340c402200c18011541c0c08030000d0324400135580300480c840048522900481d0016090f01c0c412030750f00c0d025001c1400408090b07990b55010541080c1507061503100c0d803910310003050841c4280d0700702d610f0941c24111403104004500c2549907000340034168002d05070707440d060102c070641c002002c010740c4802e80d000144085003655000301100c0c1d2080012a03c0d080c10300c0003a40c900310081c3d00901d003582250700300c10240310036401c007003901c51190303d801c42c515810701340010609100054080d110340004a0501c3c900e403210341c4100d018002c000d0440b00c162900724100c0c1006070049401c00c50b201041c00c9401c42010400090b280107045c2c0c0035120080d40e09003a021112904855503410030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 443035611 1250 443034361 443034373
    0xe060432030304060c140f0d080c180904060b03010c020307140c0102030f0c010e06010303090302090a15061b020312031009050618041b03081b07051003050702030d050f01051c02010e01030e 83
    0x41c4a40c104002d0046010380302c05441d070700c0701d00344020700349c064000c0a0f0060403c2c1001120300c0c410034241c1460b0411422510400903844d10b0600300010030440191540661070700441c0c80c2180d800002401c2258410024012000000207405440b102c402c000075001da4014040d580c1007002800141007146082da000140e413018211a280c40d04d54203a10035804681102d10500560800c0d0a20300c2e8042480e1500307106240d001105079074104007a101d441e00304000c500c224021a41559541c88296400030200d0b00810b1101104144c9a0720969a141003403444100018014003107004851045000800180b801c3d90103818401204200420490b40f81e0508202e01c0c1c1003402c000d07403110255014400050301c0c2c0c0414031007030441c48800c03140141c01381e1210408011541d111012901d003144940350108030f6031100c0c54242c3c40e6000d4001251201070401080005000300c007007a0034102c0e08112110344540d5009945490001301c1018080d000400c0d180607149154005c0d0000006440c0100440304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 443036861 1250 443035611 443035643
    0x30b0a021b0114061507030206010e06011701090b0117100b18030102070302010e0c0d050c0d0c05120a03031b0806040c1101020705010605100503160f0e060432030304060c 75
    0x1086407603c0d040d21078600c15035804d1152034109034440010025000108500e04110360705c0280d40d0f5081440f50240300c0036410005070060344a20720300850304488003c94003040d61240c3e5041d001d44600c42d599400a07903140701440c45ca001c0200c1841c00341920604100480d030074001007180d00e621404c0386501c42d10440c1003441481e00c00b48003e05c1030354001e41c00081d2418603510220300b4541c0e0200001c2c419200d1005c45000b04401145281c181c000448141603024003521b09007440c58441d84c4540d82c003a0f194803205003429004200d00008510a6404201c0540f900c400c4421003240907005a0000308150001000790905600c140307507140d00c03405c06d62824084440f405007680c1c41240b040f142c07079464500421003030500001c241031400c06420840d0541c41c100346140034424480482104000118840007003150203035441041c002405001e940c2d8543c0c03200d9100c44036008006204c00d040181101c12034910566505680aa5200402452425160040c22036207905403400546003d0b82154184c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 443038111 1250 443036861 443036863
    0x403020c0a06020c090604110405060310080703051e01060b0702121510090e07050d021309020a0b1b160621020c06190902010c030f1206030809030115030b0a021b 71
    0x180184020f40c01410f042c42c540c01404004100508074134000d47c14074516007880c01003041030324262041074554030340300d80d56444100d131248081d611910f6540039406021052120226a41d1103c0c0d41514a01d402014080c591908a42140c40307040c604000500420005151030502e1659018200c002c650002d0032407011065085000d4031f0000400394041402c100e01c12590060034554000000549a2646890081a0300c090200c60080c45040d1014201c07202150716480058042c1e00601110001030300c850566140b54031160110003854000740394442101b8000800058699400800c10401e916202042e030b40c0c6510700c0ba5100041c013000c003036140012200e1015000510780d80005000b0350920500c1841040c03000c50500e0b07001400c0c000c042d80982d0b0010001011903900d45044a03c0084115003114228202160110914102000081803100c090064851044120020840c4410303496000e0120019844000c064441800c0015aa0a00d070b50241c5180c40050025000890380c102c141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 443039361 1250 443038111 443038129
    0x50901060f030906050f01080c0409080a110a08220504150512210d0507080f0c0307030b030a0507090e0a051e01020705120c150402181b120619030c06080403020c 71
    0x59411588551b00400108504214507180741e0819602040402c1658030b0b000c4091150100403001d01100340c0420140007420417000d0121500014829115100360b0007603811803c40e0780c52490403074072104020400745018810184403141c0f07894400b00552401d81072148102002519844500907008200249900c002418513140070110406946048a0065004990001e4010702c01c100001d020042015000c50749950060760800c1031a40303960b60700d007007107004e000c0d966540354241c011500c03120200040090078209030f0720000018032a042c50943c10980d51301031a00e0140040d401482d80020614030182e103902c01c0200c0c0d6001524060b45511414584005840701a1071240f001421a1071210700740706c4c0380038042803900e00c602141080d40000706020310b1070741070200051081020950203860300d001080c034010b251030441d80b100c82c0419001030030340f01251b18a0207410310b613201940641c407444149007038a501c00d548505050400703804030383c882c800400880641c440c8000118540c0e07219480 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 443040611 1250 443039361 443039371
    0x2060403080a201c06050604090b03030403080a0305250c08090a12080d061a04050603060a050a0906031707030f14040f0311011e050a030902190b031b04050901060f03090605 76
    0x4601c0c1c2d2000c00d20000d00580398101c608448145c980041400f180e600d000c103e0b01251110310340410080040800a8114429984005c002110009005403181d0301500010b1081c3c1075281c3c4502c0002460b031548502d0a111800311001891501440d40040d004034007600c074120001d03109a02e19034840d40c0e01c0312a02c40c48070f420341d980e40c4046070380e880480c00d03030140302d01824030b901e140c107801108656910305038011401598403680000c00001e00c5a110450803000802004060f00c407095900d05e2800024029408280c1e03004403403058162166601008403820a40e00d80d803801c400c0188040112001025600c6a4900e103104000000e00b16042c44da03003d010b94010410107010845020000d012030800003403031118004218013014000b9044001d99000d00c056040c0450444000d10001d54510922107941035404c5600d10f0100e203000c03107000594401d6080c654007071405907051040010500440c0b2136903a1040e00c5034018883e0910800225070f00340001d00300032030369140c50f540d03070707001d980040790 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 443041861 1250 443040611 443040671
    0x70611030d09060516110c01050c1015140306060f240a031b170c09031009080d0506010c050604030e130c110705010c0804050f190e070909060602060403080a 69
    0x18000e080ba1404030313034038050a440c03c00014408034000e8540d1a040c7c5030310128103005c0c0c08075440c6c80f071102c14000c100c0f2039100c50204000011003d4031082000d4000d014010224800030348600141c21300140c803d0154500804000ca402a408200440c0b1508080350018a44400c020058010511400f8002000c51500c0204016800d40d411301000300b01c6a00c0399003045001029003a038117002407800c6811801c0c504003d0790328100d034000300345000e01d40701d0b0705c00702945401d481c0720a020303010014065520140100303112a8450300011642d80101040280543c0c0204001c6030010340036861114082101800d03500020340024207034411500c0c044200d40104011102e584102d2000380940c0340640400d08129041d00d21540720382041e400b86004083c020000c0b507030b200741d15658150b401d0301c1410094000303554003620356004230740858081e1303510310100b00d00038008102c0e40140e002c0d0340f003510031039402848680d581c0d88040b201c07084090080500940e48440c0b0898000e1805072104400e0000a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 443043111 1250 443041861 443041871
    0x40905070f0509070f0503060409030e1210060b03060102030a08040309050d0807060e01111218160801051501080f070903150614040510050907020106150c1203050702070611030d0906 80
    0x501400340e0003e00070942e204000d00d8100c4031000541110540b030700b250080d2000109641c0c1c1d860180c450286090026501100d03086072340783d10960018403070070301040c4401d050181a80e100f07650a2240026101039015030070034802501154440e01c0c0041d4000e01900c4c18040051b03642c80400d8203401e46840543e04c5410000f00101444003034040c00ca4101c0c4c00500030842d003e190740c4400f034940a0b541464824806840205010040003010000300d09000030590f07a0740011401d02d8000107080d4032440c003143d400c2c1400030391a17802540390108081c9043c0c581050b83d50b248415840751403801040718050140122012021403540812400c44540080c4001260780c1492a20640104074178040ea10031402c041c00c000e110340d86e10021400722481540d03441d9080d2a1072400b640546000d41001880320545203140700c0c019484112028040e001c3c21500544c0100110101c05881c803c07038803200560300103401000058811084d41480113042001c1e03c1c100308580c0d41c80350070349060300c00560303142d0340303803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 443044361 1250 443043111 443043119
    0x100b040b091c020f1201060905070201060f0e0417280203030718030f020d020312160b070518210a080310122103060302030105180d020309130b040905070f 68
    0xb0101c0c0c0003102100403030010111625030024843c40340a80c0c86500a180c40341074286905401d4105074054045403100b4019031402c030400034020215403044c1e0244491041000911581c6050b403a030040340c210700340d44070341c000b882004212a031090f442e08040e140e0714042200e0038001c818030f4190f2101260301943d56410110001070441c405032003000007009119104000103160107250807442541900c00782c01c103d10500020b802c01e10301146042c1400c034002010300401016907043c00d8654803840402c5056118510704407082c1c0148a04940100080c411804c0310303240c1421200c0c03d24100c91100038030700303c0d80f005690804202481c1200d4004022050000d110044d8410b00b0240401d200c1c1c6507040c5445495541440740c16818a001c11204a04c0e00d0000301d129402c814040d50f0064000e0200f401c04030741084544000507211360300d40c01600350141c843c91006c01254000c2d04000e000310b000d134031603401e400e0050881c0c11201f80d000761740c0c0b0b50450004505014420050419210080c010740c03034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 443045611 1250 443044361 443044369
    0x21c05061015111c0e0909070303020d11100506120a03020114160c060216080f09181b130f0b04240c0f050a02040204090213151403100b040b09 63
    0x10003004002c0c00100c1c00d245503c0c107000260403244c60709201810b81022a9110281c3d215140c0d600c0701d60300143c2c1e0004002c00201c00003048411288a03900b100c0e4180110340c0f04072680022228015500d4100440b050305084064122030b410403001010007074040f9136404010700c1c0c403000352400c4016075140c1c2c030903148001603414226880043c410100036030380080c0320001c10300400c80c0c8000301803940c00f00d840c100c0442a105c010b00d586500803850b580d00e80400d1a03502e165001400400d10030131f8150032002600d200501824000c4103607070301c640c24519070010346e01c800b60070419511100b4070100000140743c9102d0142400282490001c080d5100d0a08040c0030344101c400c0181d2200d640800382040c603181c0d1055004482d0380d0824200140300310140741003070418200c50b4001c0d500500205d80850f01d044141d0041140b40e03001000e0100302903480001d08050b014014002c008141c40c46120645001310400079903100c0c0c24041c0c1540c501e900c4108144c1c890b04a03801143c80c08401148590040c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 443046861 1250 443045611 443045639
    0x8041502102c0d0f11070807030b010312030b06090f031005010e07090e0702100b0102031b0705120106120b060607060515090c1306050f040308041d0c030f04021c050610 74
    0x29428050040c1500c03194011344400b030792040e0304080103441c440f48003001d1010721030300c40a084e0410a64902981d6420a000ca03490280020b42d0f6100194860380342090091194000e89600a0582c5083c9445001003010016842c3c0c8000e8160007115000d020024a500c01d1a010b4450102104d03880c1c01c200a00510060440c1c218041102c40107041c40a440d400045d180c92100300c0c8039000c00c40c1c243c0710340101d040d0301901c0e40c030340c000400003035292600d0709000c5018000d40300250349080032401000e201c10b080c1c0d0f4441c403450204a60405076000881c201150b200e500c5040900803910f440b2050f99800200c99048400d054031225900d200d10a0b840c0c01c400c1940c12520201d401e80c1480d0500491000c01481c602c031301000d00c000010315130419a21001500c008581003528140c0340c3e07988124403520982034011a45070312031440d000601c2620311030107130303070048040c01910030090782e5035400c0c025440c0c001001105203c80392050712000402c02c100c0103200b00c0d04e016041c0105881d01d404030b10205 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 443048111 1250 443046861 443046941
    0xb0424060212030114060f0307081603150302040207060605060f0915040305060f09011d16090606080c0d201b060108030702041515200106030804150210 67
    0x1400c40b28400550441d8241901e0644a00b40301c0140c03014104400210385104180e1000c040a03404400c2040c1e054100c8200c0f4419841c9802101d80c210844c24200c1c00c445418034181d004c14440f100a0016060550142031810310440c40040c42d5510b881c00680e4540000056801e041000603440c10142072450b201001070b40c4202c80b1707c0c2001c0c150f40d11240c4551009005500480d801000507401120941204500002070680305ca8036820710704900d41c40398003020345203600c1c1c60404070009651205201c0d11003104d11566074600d203606d4000d240700c110382c010a9002c032078a0f1107517a07000c00c941120203260a01d400100f4141d03920140c8107244e000a146589001049070000c100410a0b1400442200c0c050365040750001810000e040180741d04144940002090700741e00781c00142050340001d14110200c00200d51756500e10001004a426202c150000510449007230200300305000c240e098007151114540140d0301d01c03d003080d85000484801d140380079255030300c0c0c5040381c503540c03e6803401641c48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 443049361 1250 443048111 443048113
    0x1303020619171303030c031b0c0b0f160507050708070e1806040201120f0906110301050315071b02010219030801090b0301020c0604030c050f0d03060303031a130e010b04240602 77
    0x60f14102d0042000c0c500c03c2c04004c4c0034561520b10021526110b58002070a030315100c1e1241d0b111940e8034000070b10755403c07140100c03802c00888003c42c2644818114051140910880742100c94070544011a001d402084c82200c85c4c3c400c5500105451000b0702900700902007411501c00c407494001400c4000144064401c041500100148400360340d00501c044150ba030040300c007003491107a900d4420010000301201901561400e680061142484801036049410072001c5940b846520165510303021001e036028004942c0c2039000e6106600d004240c000000d005005607403000c0c00c407140421038070085110031800241020010300095070544510344090304150000c5091403902101d083d0346003000b40c005011b20021040b0a000c000082100040d01c0c1703c1d0a0584035035091000000d03001c0d1030300703000440100c0d0921035404c4084007941d100141059000f0215625007614080d80002400900443d000d155241d4003030300a2504c03580900313040c5401c40380131034180c0148902d41c0c0b0601e0400b60045011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 443050611 1250 443049361 443049407
    0x3090a090902150a050706141807080c0d02042d110c0304120501090503040e0f010515071506150207030210091d0c040504110706060602030406050f1303020619 70
    0x2da2583e00180b0319100c4a0203045035500c101d010255410b008500c0002c1c04c1c070341090f4140110500081603640144064410540c3d00c1d0811501c07140c0718010b501512800340e1010324141e0042c6410845047c0d110b0001d040022401482c6845400c07904101c1282182451000c00881c985502442401c0c11452216a8142030400d05030036140c5a12961064402080c044e40744242442406c0d8000b02e02c1d95404000c51395510358403800d80b2102d034021520008035900141c00010700c0e09285c00300007a120036007003266282c20700d1555058200209419661802a521180868800600c4205440000300e07074006080719071070740c1b0401032301c080107009113400c02c00d00050401a120550f1403404041202001d9080d19a07204407004045020f107a00c030030740c0a0308040c8003010314030071400140001380c0105030500030140c0f1203100742d94070300c164031607400080c10805c0744860041070100a04071a5100c05400a2810f5407500000e04035003141c0000708905c035541d0403030300c01c0390382082000c00540300510035201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 443051861 1250 443050611 443050613
    0x213090308091c1d09040b01090e07030c0e1e1e150d0f0302030c10091b030203100b03010b0607030f020712051519050a0f060501020a08192003090a0909 67
    0x4081094810f107005202c20321061641d540c038600b0380482c01d0000a0140d6120386400c0c1898806200284513050015150200c105c400d003001185030b07070643e5000314070106003518208130203541580080004a900b00d070012103006000302c46145500030080d000403140c1c80c1c02c07020041600e0503000341159518400903091415141c0750101e00e5980e280d0480a461515016820f081c0d003184500e4041d07600c18052441445408110769020b0780350303140914407601040c0da001c600085005060b010181d8503922003040c00d10f11296541224080500140c000307d082010304000c50340c19001004114041540000760780c00003a03040000c40002c082600f031600303580c000c58950301d4840700c0100501d100d42c00d0041c0090800b280e00e003086508184040400c209915048d03901c0360082c900b41c03240c3c403040350800ca000200c0390b1001450b105a203421182c120310b0180d40300000c43c0c441c08502c80e90014002c8404022002625113000200040384d20405507135200460820000040c2c52a009511414070f8208218 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 443053111 1250 443051861 443051893
    0x240510080c01030510120c08161a0913020c1f0203070e01020601180c092403060f06090b0327010c08132f030709020702030d03090b071b021309030809 66
    0x101b04c4044160070702c01d80d041420220742d040910b420152081c81415220705081000844500890b19190042c43c0c100181d00c80c0d084c1c003172003002c004680c40300010902ca2001e101d1640103003030030300602088a0010083c01c04200c18203030b03600c10744e40c0d0440d80481008105508058004005078091000d82082e60400224400c4981074000c42042241d40d50420159a4011200f02015080180c2842040020701103081b4001e2008022040000d0809800290014100c1e40f42025254552501344000307090440300402900028040001c001e05581040c1803810b202c103060200404520010032039642101c4080c2120310050407440c454460b14102401181101017840c0c00200c0800f81e0343e4010100a074001021004141202d41c50700ac0c022000a0000d03040c0d0042c0380c80c030320a400b0b5840070b10401c001034040b00e00484001d0441d00203540003480750303440b07050800480d0200001060384030311581c010a80142000703502031410f6075646122000c0c550080141a4801c2c5c18200810100e00811000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 443054361 1250 443053111 443053141
    0x60f050d08070f0605010e0604060812090d08090d0305120708010b09041505090a0911030c0d021203070611030411100f0309030207030212062e03240510080c010305 72
    0x50940007010610400700443c524000c00c1c100c0d08540140030558491000074070307500c02650501e02c603520384800055a94004615405d07030400c004602d9080207442c80c10b0009140184504440801042286034995522401318100540c008c1c5d0340d40c0d807281100c10010f25080d030003602d09010700c46d072080100200340c6808100c9028030004d0b6004104221860f81c8038a071001641c0103030340d20a8140c0e0802c08811001d910485050f401800c4118851203a241410340300c0c103080d41016081608540c49402506005003205022580002140e1900c85152104401c0301d40014142c1c03a1a4000414001401030390041c0c2045024100c03402c080e90400c41c90007802071b28208540c18245a00c504e80399044c98000c0c8000002141c025140d10050f000000c2d0300d54a4003000c03207aa00070303060f400c901110401180280103a8a4052a4002c4516404c41d111081d441c040680340c84010f407103003000f540d541d100500030035001c0d2550f800c03130b080c080703080030f0f0f48034180f03001c005c040c1c4d040610745420002d6800310f10b811 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 443055611 1250 443054361 443054363
    0x16140a1b0308030a0e150106050a17010311040e120301080109030807050a0e041128020712201512010306050c0715020f1b07060f03020301270e0f060a060f050d 70
    0x400600544200217050421003541c151120218000000041c4150040004d00c0c56007299520300070610a046020468000d0a0001614000c0d2115081c4200d00709030b444592000c0e0072104641461030082c0080d095070f8400d800c503041c142d4480301e4000c205a0010f030fa180d0008101d007401414220b800400070002c0014251840c42640c5407031b4044040c5074030000b2156064916001551604014119183e2040702c5070043c1005100b5014000f61071601c2804000783c0300d9004510b042c09001c41503008281c24009050740354414100c000c035080c09448400100694601d81c1c0003a04103604d941404030442d10020002e100903072080082100242180901880810802e5001602d03843c03228624160307809551643c0c0c100b4030700c1c81644170345140c0002d0a00f0845045541d4070030303150112502102680030070302c074842c00402d03001181c1408080302030740702d19004541200024801101a101894003801c10084821a0419404d0010903c1980201d030b01402c5524500ca295501d041d003c9480301c8074a80d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 443056861 1250 443055611 443055631
    0x51c02010c1704020d020a080d030e10050105010f0c1109010905040b070e0a0e1e011d131110021c09050a12050606010804030c0606060f0315150516140a1b030803 71
    0x81d05d501190346240305400503200a504035064003042c0c0342c010b002003044141b85c003154400d02064085107100f501856050307070810fa40e1500b410003601000d032007034441030034204c4004402c083e00c211543c0350340740b03428020180f13030501203980e0401342019580050050600000c10034030085052080e03d5407a9003404896000c189011103654034a001040c0e0002c4401014060300031600019116800c981980610805802041180d0f220b000c10b60307006201e0000c00400c2d81d042c2a02114862a0880090030090b000c1d00640391800550b450440300d0786607038100741c0c000c00c0e00050288014249010901c0207403a400c3c2044a00700c2c030b1a1242d56550b04001d044604203d103410015041500c5031100302808e0381d1101c3d06104450300c84902800540d54007403124002450300201000040c5102c0e00b000841d100a00d40c8965920285401c99982d030020060b080104140c0000600081c85021024800d03a000b0000d045581c1c06032070801001000c00100301b01d10b500d0b1001c00e03c00703c3e043d40f0460b504520580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 443058111 1250 443056861 443056879
    0x3080612010605040c0201020702090114010e10030912030e0d090e0a1503060e1c0806150903121614060124030603060c0c060b0d03020c0f010903051c02010c170402 72
    0x12054a014007501d0700044c1c2c02c00e040ca035036a00c1964054010348101352080354000196a00c2e5448507202101c0545d800e8001400a1800c144a061841244000008900d004151503100303486521b4032041d91340f10303240040c0d540d9401040c6d8030300c03d010060341d101551405000b40c6180c582d0418001d80003501c2c01441c19a0303030302c40c44582c0c510310442e03a00a682c0007000380446c1c2282e000d4140c46a40c090b580c1d19201080075074140101c0d00c6580600d21401008180602c0d0300d0504c001d00d0400d0300580851501841459620110b003030305031002d0450300c002403405021003d031b2840d014042445950b4180829070000005000c84544030304118101914085a103100c684080b504a02806250f030016001ca0320f0030200d0404254812998820f030741c0612401c0c002404a00c0c28400404448180034006030000c4d003141c1110324005400034902c0b441450f010300c00302c0d01ea84465080000300b00e80056000b0b13500440c0340c14950280208203881da240c6c00c1c0144900c421007005040da9200901c000e10801d808 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 443059361 1250 443058111 443058139
    0x1209060f09030f070303052a210d060b090f0303030f0711031204030201021803160501031508030f0301060f03060f060509030f0610180506060702011d0d030e01110703030806 76
    0x82103955101940c2e02e04441c013196032801c02038916032209100c1c1d054200050052081c50000305400c800c1c500f03222006001070316443c103607001d4145403000c0346504d070741042200300c1c030329545170040c81c2c09007008100325030391040f01504101d200f80945110f10b00070b400078010000c00c0840d40400543c058014200000420441000c0900b14881c4001d501070046107401800145581580540070b1754090070195203405581c40100755490340321a100c6030a0b541c84402c20310842d4440e8004116064510ac02d0072242502d0760109070640d000700c0c0300070340010004001000076070340c8655003656220141c10200a00f90030219030111520312401010244100080d0030b07d040e4070200142c90411140b01d040e1005410032007501906403010780303c1d0b04c2e040e110912843c0e810150600c51700d8028400141000d150404507401554080036100b180b144400080f032030720b1516224400c0316840288a07545804409035004009480c3c44820140c01409501c031280c113100103900296050741040c411215801c0310b80300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 443060611 1250 443059361 443059363
    0x80402090405030408010c03050a1404020603070e06090a030f03180f1a13061808011119050d0c080a050f0420031618051e0a0b010e0418051209060f0903 67
    0x1d5988082070b01d41c1f030300380c600400d603605074002806500070032814400103454400001c2440416100039620031030810204012500820041c408407801034519030501c0d40200016051030a82e038026101d00d1110440b80040590226030103a1500261250300405810456404020480f41c09611942c0e9800404900380001850603190403200700d01c0c042002380d0302d0324401420401014980010800010800f01e01100180500805404c00b000c3d024203001c04200440c203004803030302c010818400c3c10090345442801c14012203000e145291141b10441c1808420141100c8000300307800942c10062081c040000c50b00a1307900f01484146540c68031203900400001d0800d03011146401e00c504070800001240c1061700c00003040140d803460308122550340c0c0d003c408400c0b051081c1240b07090001900260b20880d059025480110040c0741400300520745d00086001c44800d0144044040e05605109040080c20013410a0589001c041e1a0802225201103500750040a16443c4440b03400329000c921a18 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 443061861 1250 443060611 443060617
    0x30106020a0305160b150310020703080f060a030b01080f06060d1a04021309051b03010605011b05011b08041b081906020f210108010b0a090903030b060d020a02071508040209040503 79
    0x18011782c080029003042c018081e80091000466402401282280f2440c031225100380c55003da0107403901c000369654030500010201c0e0060003160b129034003103000701c0801c42e40300403903000c1c0c03c40c44014204040514541c0303103801c100900c228400c040200d030400000700e20401b000c00c01490801c800209481e036100180d004000d0740301300c84503a864013134110188200011540b000350040c04040e60072500c2c0e5010705090303c00d50301540e404982110040313004d488406601121660145000280d5112032500c4000c11040d03550f0076130001013060301804144020780d90f4098415600b01d140301c481924103c0310646070710145042d0091030030b800031010180065501101d24080c01140c1d180d07a10300741c4070064a4800c107400300c480707501290000045000c140502c00d030707600d0308001468951100d240030b80c01b0001c0c0803802412004c2646414544105480b018054001004503150251726103010000003840d0505d60782c00842c16003044425003d609070030211094006170107a07448200707943c1d14101585948 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 443063111 1250 443061861 443061863
    0x313060209040b120309011205040c051e06071101110a030816020c0d080319020405150903100e0d020f0106050d080a02030418140901050f06101103040e090d05030106020a030516 78
    0xc13015241c03143c5080c03008002444000c100740ca400007101003441074002242e40449005060100e102402d02903803a010101903000c40170b100030f0110420285001c9005c1c1d42184808444c944007100194025607000b00e00c842c600c10406e40102250f1341240c800811241015054010441d0300405401c0c0c1148244540384050304050b00005d0040401d10780916164812608003540d07210b03124418000c004a0300840d011201c0007030001d40ca0f186135051100c2c890f488446195030510030b0f00c2c0002e074080107034001c540d0700c409403030040c24070100344a0000c0d040c02050015074a4692400d43c9c140b1269642c3e0341c61081c041e2308900c11a45500030f80c0380c00d92461007150010402000030f00d0011a2084154101070310309110000d152515441d000c5109003070350030a5904001800b0090001034041c203244640b822240715a1500039081d14804e5402070440d03009803c010b004802540c01c12841d400d04000020180342e407468032625640c0741450081d01e03290014402010814002141018240d15a001300031107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 443064361 1250 443063111 443063119
    0x30c01050108060106180b03011406160309050108072c010504210c0f080a030e060f070f060c170c031f12060c050313021912030503010e09030313060209040b 69
    0x1d50310794040e956035070303030900c107060010b95140b0040d10485821a6010100d840e05200c441c210f9090001564070003180051041d0001c0d0180100380c41e0343c43c07007000a03202d00e01a031a000308007410040010f00c8bc080081190081c400c18200d501c03044c07200c0c0d1003c4030034113041c0d10300051404000d02c012101485035910800c01ea8a011203a0592086080c070031169080c821480e00f82900c3d82c6074004007c440d218814102d65405c16640e82d800300740507244d499800d0074000d005078a403084005018545811980c41035884801d0340625a04000c00c621846d0803089160400b0244a041d4841010781038200074031201d0421001300204490041b050310b0780d41845942130704114440d4172000c085c8402803211f80262140e909000e460103015020b4811039001c0c110850110010540395000e2200403014180305944504c26500009440000340d00350501480c030950fa0a5602d526046290800407406031582106400030003e00201301d14000072013848541c001d40140e111500d000001e070080c2500c21f541070708 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 443065611 1250 443064361 443064371
    0x4050408130e012d09020304050a0c09060612050606041205210910143c0318030a020c0907030e0d090906082a030304030f06060e0106051201030311030c01 68
    0x100c0315103560304038140c800400d940d62038a8421140784681a14024130070b15400e603032a01c28002600983c00a507402401230701201c648030031a5071045e0702000e10346e010841850340c0d034609014281c0d100d200d850700c011400d00f040c4660300301803001480ca441284200e051072081029400100f20044c07080f030f51040d00d001d42c044200c2c090030f039040815501011010f4800c044016061100600400c4409043c0c070f800c480e420300380210b070140b400401036403a140460440074244506000c04032080303200d085503003002d00c0d80d8503418040c00703401074402d98080a12540c1c00a01040300c10310741c00a42000c1c2c04d48101c0b03c0243d40c0c4c0366440154020b00600c0c140110502640000d0429a0340010082c1c0450700806010401503a8a400e06500c0e200f1210781c01107441c60280030025984407a28030703110707254030040c10b41c1c1c582035a90344c81c4041c01c540002c0483d0000c0c0c403508104214078581030b160f80102818100b2925040c40250b4205601c0d40501008041c0221843d00c4245035034100140c8170f812010a000f044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 443066861 1250 443065611 443065619
    0x928240218060c033a14130b040305031305030d02070201030b0619120b10020105040b06030123091c0914010813150605041802030c060405061c02070804060c230c0405040813 76
    0x180c0104408804514024000301f0700c0d900c03162030049940c40d089600e031a22030b02c4568040b0381c03e6001170f21403604d862942046d00d0122300705100030101c10034842e00040c0c4d02c060750b10024041d11914440d10b4030400e8144690401d008149840c01c03170f0180d0500e404282000065a00f80043c6800810550807040a501c0035110350380540c481800785010b036102411680c2c4100c101400d03118000e5207000c424401809589070060380c0307000d01d1382108a800549104804407a82003145c0400b00c8554000990801003c0298a141038020011a1403e280c00a240d10301101b002c50f50741d050000090400505400014a080d80c1c1e501030b002500c8024010700c1100381049001151503c141c0c410792080c040e010950f00c035031401004403421a03c0190500707040101d41c01c0c050b000e2004840d840e0315041e800300003250004002000400c0681713055200c100d603246071400c1407455135000305c9110190540201d03680d034448200059030b20001004071000720383d59a8600d041c901901031800c11605c45c0c02401404a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 443068111 1250 443066861 443066977
    0xc0303181f150b0a14070c0801050f0406150b1801020705150d0f09050618010e060c0a1128020a0302090103060501030b0928240218060c03 61
    0x2c1100c040e20141e1161640d21024640014400c0f2409040415516180140035400c4280031704800744c000c020003180c40b83d403400142c2c259101241c8041c440c0314904200400c2100300c1c464090000c4811002d4041c003030500d030b000c0d540c620030301101e1118091180340202061b8400c0003082e024002c00380007040300c2c03145400c18801c02d400800e075501401c3d0a050711103004100900c07906440740d03000001095140c1b185801c515000b4174146102d4581d54854010340c40524081114600401c440304049070b070380315520700040070b800c2000200c820a420500300d41290704043c010444105a108003c480b41040d41e01c00201d2038034880c2d100035040060702000206020207640064101d88c0901c0f41c58402c0d641e0b2001c0c064070b80801400c030880700d103e055040240d161406890b038060f98810b0180004104050f035140140c1c40c101e02e2110540c540010b001c0a1021078951003011a080030744241d81094444442d85480c0c2c064419160502401d0350308444400070740c0c0591300e0380c031024100000c050048801e054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 443069361 1250 443068111 443068121
    0x213080106150e060f03042603060a21150212090c1206010b071b0306020c010c020d050406020703080f0f0f030105040c11060f1b1206090108030c0303181f 68
    0x34100c0620035401510801e80a0b120003030161200804c101d00e0220130f5001e81901d40c101800650380d140d26074a60b2420940d020f07104541c04812405681c0e101d00d0210200b00c840c6610782c00040079509803808501038515000304a10605910001030010102c051081000038000e99170308403002c0e02c00720180151244040346841c4d00540a448120254046070003075540d0b044284208995000c04100001c04034076141c07001e0f41c01e040c0100350703c181c05540307496840c241c0c0c0090250340001d940d1a4082d0004a40400c2042342030021802d00600342450241f000e0f4035049a4400504804030000f9801c4010024004a40001c959004101c1d114000c0d13025903140d0390000d0040900a515006259580b0307070240c05c17140e8ac452142e0004160541d10040c480700141d00c041c0c0000d090001504c00c089020b04410081c2c0389080aa011052039464040204145450706a00480e40c94208011591001030301100b02ca600c140c80e1440c280c2611000765101c1c0c80c0030040c1d010707070004100c001420ac065110036080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 443070611 1250 443069361 443069369
    0x904110405011d070c39170d030b03030405040524100230040b031008011518060902040b09040506060a200a06091a07031104050f0402070206070305030103031b0201020a030e03010213080106 83
    0x644520551aa24000000708107849085008c3d800320551940ca18400d8218600c031400160581e0304103a40c44002c1016a20203840814074030145500b03041041c000407940e80c0c81c521044440c00e4210285810107501c80108904001c10079039601e210a0481c41c000c1c9422855103003800c01d451344c4540d101c90000d100c4d00292061030518100d11070001f44180d05000e100020172480130248029480c02510740302129849034071200070758039110000303900308013880580010a0082ea456a0340e03c400360400044540041c141345c45086d05212207001682e00a004544861046810348004145483c26504c0c002203214024501401c04210804000b0703810b0707100d03441302810000240252503c182c03da0503280450241c4441c1c110900007081149020a49488a060090001446e088450b008078601d03910580054002c114004010010164065040c1c00c1c9a00380b0080b540300c905855000039111070220102034200401403030001040d0b9000e5040381d81c0002c0f10b000184d5026521400305002c0c248500c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 443071861 1250 443070611 443070713
    0x30f150b130b0412030801091116050c03060a020a140f030c07020d0b0c071707020d0b060a120c030c0f0b0904111210080c0604060912030e0904110405011d070c 70
    0xc000124039049004202c42c518a41481c00d0501019040ac0c200401d0002c4050340d030352007009a0209262000d121141c041c2e02080400343e641c0003d508040c1c1070904c8600c002c40082010400004100012015250003d80328502955540b10a000044003030769040f0004c0c01c940015070a012010360540d0083c40032a00c1031211641c1d01c159005c8010950040c01c0c8040d400c55140001e1200054181c500540d0118008100c3d01e041a250b03103201922000301c030002c49112a00000a00500c8285100e240081a55518003031030070341000342e0029180541d24482d03004588032104c0c03c00d5525050305440340f01e180449a0800791038407010041311602c00744a02500340c0140c90440c0c41908180c0d04460503074146444403442c0e80e1401101c0d0500c00c500000540400c0b03010030002111342e5480e2407250040d4019407030382c0041710101d0100700859106134800710004020944650440b04090040c5a000c901c90406da00141502e0818000c000401e06040c49002c00c154180807144103120600c1b00d1241c0f00301 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 443073111 1250 443071861 443071877
    0x605091509150d2a030506010e0108061b0304050304090207080d0c0f0e12100c0f0306141e1302040602030c010b0a050d08130801150303030f150b130b041203 69
    0x4038070b002d1040d030810540380c00c209441c0a00021071900440c602c1540d03503482c03030392110f01c8a0b000381d56000161504111010303080300d40104070007108642d14a000d000c5003070190040b0b0404020744a42030200028500740c0c00c10100c002002c3c044103000340c0e4024500e1400c00d540c1c0c5c078264600150241d005c0a122480d151805d804801141e102e0241ca40340301860343c0311640102c1040c02000500e51001500f00b104e44134800810480c03442501178068080141d0310764403600b5011800240c00d841068225207001050074005c01d07015a640f0725580c084014411504c20443d000c8804203810348103400404114a0000400049590380000240441c402070b00c02000b820001400b001203000e000d12a040d4840720401c0d0010109059000a29903010480800322090703650f10034171403d45040ba544e418030140c90043c01c01c00d0581501074048130790440802080400036010300d82c05813245901490100c0c06000c20300c05070020380c002d01c0c1c101501c00d08004c20386560707403884a18042900c440048000070002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 443074361 1250 443073111 443073121
    0x1080702011406040e011e02031b070c0e06010e04060f080706050309070605030601050c010c1706060a080c030a09020406091d1209010c031e1112090915040605091509 73
    0x6104a10303001081c0142c26506464400c1044040d06840110385815580c8440031080040d21040c1d0344e0061040440c050780700c1c0361203031510203810450590501c0ca44820002ea40c005404080e072442070f2051520642c10036241e0070b0048a00400d5200d2031900300340360840114041d05110003100c210340030352084511841c1c642004130f826000a650407429a88a401f0503c0b9890182010359409601854020b040c1b4510790012400d50307101c24100c40100310002d541c1160108506000c561090b800e50b10710340b4100008030020175928004000d03c94030076022000ca50140020b0304840c103c2030300180b0034002d05844060003801000150040040264580c6140074241c0c4089031100c5907160070380540c0c2c01e0103541070040d200311080e49001c40800401d607502e00303030003c601902c24240d8050341d6141e8a0485031000301c50f00e8440001b5107032401400a0003049450381d41c00314680c2e444403d4111911980030035001003400b42c07446411450b4044550003c2000030314a180880781c03c140c080b19600c180e0f80760 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 443075611 1250 443074361 443074363
    0x405060a060909031436012d03050919050304301b03021f021006121e14160e0103110405041109010801020702010206150307060c110a09060501080702 66
    0x1103440043c0031400345060401c141e10308a02400d01c6e0303207401e04080b4030b101901c9034078944082d074200a0402c80c0c0b400500c2c0821075921800503038101c654021224801c048051b600c0300c000303030f41541c004105919400019001c3c042030051404146000064500d10301480c0740681d1290040d000700403601000d212480e403212108201e840d01000c00c0d09544030082ca060f200d0303001b071071a00703000300c030280401d164000010707103401503082030120300720740c1c800e0b00c0c0f80041d00002e080c182c0c19400108040d0030203506022103e440c5a811140c161311100d01c1800c0140980c41000072804200042c3c05240c1911000101040104003014441c0d03035280c46242d9180c6070340b982ca42e1301034280805804601c00440102403424168099900302e40910700300c080c0301d0404400100f094034242c000c11003a075000700c0d040003156010888681c10030b500b50b8424041c03851480c0400d6681c00144a00320030410400105400d0000710205d600503100c000d02801c9030503848904001c0039046038440c19001030368100019071541c1c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 443076861 1250 443075611 443075621
    0x314040309030b0c040f03030503010e06010e09060f0d050607090620060f19060b1809060f06070201110a0507060801060503090c01200303040b060415080c040218090405060a0609 78
    0x26064999821242c11503c600c0070390350340240900f6900c9070030880494214500c9030308100a5100c2da841555940c10300703861000c00400640014103005180740994101ea8460280b5036200400340c82ca2a9400240300016000e04c24056016089000c0c400c10b1117038160744010780a003035030b0f0780382c55070100981460541514403400c8007000c1041c0c5c015002152a20f20091511a00b00500041d030100c4000402e0500003258100e510124001c1c0000a01a45e00c25250355a203c5803242101c40c0006840c0c000007044011541e074030014403561300000c0540c04c5a016001c2c00140c101c03807038200e41c10030780c00b881d00550700c00e850b01802d0b010400d5000009000b42c49074084a1184180c64054295107481300d0041d248048030540300000c10005060f0719580c06d05c200040e40c0708901410700100c090610209200031a01d00040c1c1981141d1084020b01401c00c00240c07104181e0015034006a80b101485a640d240307850200c030156106405c1018003062006c0051154001c2d801c2c00c40070054150b031580c0c0716040760 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 443078111 1250 443076861 443076863
    0x11409030f07110607080c0c030607050c030405151201030b010503010b0625210302030a0b010c050a150f02030106030203060f030105130311010627110703140306030708010c050901031404 82
    0x111040080c2c5001070480e03214803220402c0506400c0c10b2010307a40d02d00441d5042561040800d40c407215020a040c0f0701005990b40210003030074504e00e410001402c8540740e200703d014160040000043e040e80c40310b41c00080310003e905040c1c4a410700d58480c0b40500e104102885514030940c00c124041045290201c1264603008075103224503011000003402024410f801d2405940011441c0c0e500031a00134250400310703401803269001030350791402c910100100c408900e070701810031103200b00d2400002c000081071042ca540200d00e00e941d80350031101642c0a005c20f5584110038a001100000f5216010b4014600980044035038020300c5242c0000d03d0700703c0340222084d81240414040c0d000211380141004032152041600100b4526181c110000d01003143d1240c100c00b0094141c0c02500c000884d1140c1e2108031401001700d46082007685000b031007503010001d9040c1031007000001c50090f607020841040200710540003401070400c528805010350f00480c1946001c6030030510320003400f40c08105400d00c21 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 443079361 1250 443078111 443078137
    0x30605060306041e060f05010908010c051c02040b04151709030d09020f03120304020a080d0c2306070306090f05040203150402032b090e09101e0e01140903 68
    0x1640e1004100400740c40c50401c4818008160111406110958000c0901030501030314140350103842c21700010649c026550101407140d240c20044900e103503100040360118400c2040c211042881c1000c0d00000f80700d5927215200c1c4a1001800140458440d1041c24220600342c4a040c0c1c80b00405407503101c149001c5502c810150010000700e0194400c0340d026448a030700140408200001c01c0000c2840c040700b03000c881a22000c040108000c52800c1e42650001d442c5c2807001d0909100c0c41e150250110822a400602e0800380d101229088a0340c07102e03003844140d540e021900542401d000280080000d401001030050905100184506032801500d000e240d014004140422008080100f040360241c4200d0b0b06016084502a020070452a0a03602215142c00c0c1e44104001c0702c0064114401c942c0405145030850081141240c400301e01e2050b00b294000020a82c9503054504a400d203400303000c44007141d482d02003034408201c01548803030041e0400c00c0217181c40e40c95202c5401e6a80c041e82618000c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 443080611 1250 443079361 443079367
    0xb0a06260c07020307121101020f07030305070f0b0a0911030a0804330314010e1e10150c0c06030203100b09060702121005150109230d050a050106050103060506 70
    0x1158144000d961000080c002142031070203a81c002420000030364461014644070200c984140060103144034400c607001d0004249040c103522071151200128400541400700102e229820b20406000010405030301a003642100c0c9806486075000700f9402c0b4041d5403c0c03041061180144c00c000a40c0382c88160001803c9090610b4000d50b4042511b01003191048082400c60b50002c4003818120032004208989000c540c0160b40940354441c00016880150300750450030a11030780d80d032020f00713409840800c000303401d443c0d80e502005207031480c19940c0210b007200c1c1040040b00403142d1148120710014480c0d80403029040e0340740002c42c107074042500e00d40840c1c0551081004090004001080103090240c096800c0414a400184c2c1911141004140f680c20000800040e280e80b8816541d000e00d060304110050b6001900003486003a9074001d03180c058007030060070400d00c0d8900c2c044003031108004010380000b01d024500503454206101080303801d5828082c3c041038a43c000d00a490a5a0014280d00c0c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 443081861 1250 443080611 443080667
    0x2032a0c090136020a2d080727061205150907050706111b010b0109150c03020715020a0c060c030c06020a18030b01050a09021201030605060109090204090b0a06 70
    0x200c071425500003145000c0c08215240b025030303c0d400641034259040e00d41400d0b0009000c135962a040000504000d203244100c0150300e46a00290030903000030080ca014556003884007025044c2007a000440a80360ba4800d10001e602a80042010a01c0710340729030501c842c0d1180c071300c1d00540c0d0340070007500c07a0f028143e1000a16140c3c0701d4400f41c1122070144001142080401d0200e00850703100440094035408079203c2c1c89070000302400340c01e007214800e280ca600c200d45001c018504014140c0c80200802808000440070b052003000482c1c098103550010074908507000074040e5840d080c0030800c035511110980e00040311801400c4041c042600b5440b81e00c644162030369a08001e6101c40c036100d0500c0904d04041c0d000040644400b0f01940c8101c075189040e50400041110400d800e07840074400310b004000b40210300560740701c1d5030304480e840440423075580c90704801a02d001c49203800a070301441c40440d0002d2401c4007074102c1c4564107401e640c81851292513200440d140001980d000c07242c16840c4034419 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 443083111 1250 443081861 443081909
    0x816050f0f0606034c06060c020132041202040608120409020f28080c04032f090a05040b070e0d1205040f0602251d040302032a0c0901 59
    0x1400504507112208452209030119015030b01460070b5842084080310140007085c01c00e1007914060031050504454403032403a40000c0005c6e00004100300140001c02480d02904580102c590039840312414158540e51604041030780d8482c00e050582c0700c3d1382032010020700c41c540484c0c41d0302007540d0960f03812b1030310b400c2c1a200c0000e94404450801042005c02030808424200f6800b100310015140c084c10111042d442c004101a001403c1d411603080704020400015503000d020a5032a610440d0b0200402041070314085501d8031802041e800c4120309007008101800c41c0e010b684505e01c00c0c011006141c5640c01304a0382008014110382d000711512a4410108114200c040704401c03103032070407030710f0240c031584500c0401a940c0c1c001d10159010f10041c0306981160902c1051a2800030107040007203107008010a01e4049462807250b50002d0708000c9002d1602c203100b00c07203000b95100629075400030000001183d00042d120709001d00c0c01034419211882c982846540d040303c022090a0000b401c0650301c1e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 443084361 1250 443083111 443083153
    0x506030f07030507020c0d0b270c0d110d0f151a09041b0b04090f1a1504031e02030c0102010b0102100c0504080604080c07090204050604060c0816050f0f060603 70
    0xc80b00751b114000300885941c2e151040e040382248114140d01160a00c0c002a00b42c80307c1c4000d00c2e414003004007100c03292201d0005000c078894102241d40c10001040c03403c00e041e0141e001c641c0305810020a64541381800815548010020320404a0700d07007501401c604002222140c81d0035219080085900b45542d14201c007000750418011800800e11044100e1110942c2429901021003210086002c2000101904c681c203822090040e007800549603050341da00500410303009041c401c903c40e51200c5140004041520f015503403100b03805080c004500171601d000d1003211006c13486446444103010465206008041c512107043e0010f004c5107507112401d8000c6c164290300701c0e04012050100081074103003044102d010354065020395958480b030009003401d2020541141c07242a0040004010369152001203d044035660b00d420b0034810301c207151080d098490201b540904110141d001000d001c0702050024a849901c0111000c0f070815008141d01c41e40c044a5040e03058000d861070400d00c800724902 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 443085611 1250 443084361 443084371
    0x603020a051509031005070207080f060406090312110d0605060901170603011806060f0b0309032d120613061a0307021207050601061704202202070204060506030f070305 74
    0x480b500b000d01c007001103842c0105c10000030300b00741c0c0c441042c0100030390140000009404500050100a5003000c4915502c0c0340207000100007603600c0c0c514009041c414450481e49101850050011100c4500380050036000300465943c0c2c1485d0001c00142444c00d40100e441005041c2c42e4251582811072403895203000c018521340d055521502c0990700d100411b504800800c2c070903980000d02c6400c02c0c0e4079013088603980d080000318030020000d100c11000000242d800d4800140c254003080304901c070551641c0c11501c20040c00c604804102c0d560122040240c040c0b203028155854117090b040c0c00d803110b09a802901c100c4104034420081102c0d82c502c08002960311103113038012a000946e80a00b800582c0d40710050640350384e00604018400d4030707802414829010403503201c001c0641000d49550b4074004403600d0510390b44690302601d104030f899014542e4014a598100d802c00c060110354280003a60084004a2041b46001004940c03803400d00c042d079000b001d225152048076550f808085d0f00501c3c01500c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 443086861 1250 443085611 443085649
    0xa121b02041d010609050a0606020d050304120c02150705101e050402040617060a060e040809010c0c030210020309040513030203120a06081605130c1d0114032502010603020a05 77
    0x10342c10240d0b001d0040000914a101000417585030080e400812618035800417403c64104000d01030f10183d002094036003158000c0b5103200180312100040d1803d95a001001350040220710209240d00c20000150a0381806807058805135482c404003001240c0003000e00414921143c040940000b4183d0f0000d0740c0b00344007510011709651501507a40c12003484400c0440315a000c4803c0108049250291b07400420b003a00c03614100f41090340d10100d142c0100d0250a040146070441a02484103111900004507000b40501030b624034107000081d00c980c040101a802181040040341c40384220107814295aa091ba01131414402121207207001c0080103001d0301132940e102d4101042448052050349043c41901e4004001c140c500001c0c400c04680c0b1910f50500d0340c4c03400c5a809070783d940026481c40c240042c05030300b81c028000140140c4038001d98a0701080d0810001c020041389401d5074012810403914200e0700110040d00c840c0490a881035404025001140c600c4104800d05105c1140c406101402e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 443088111 1250 443086861 443086901
    0xc060f02010f0501080f1203040206041802071407060201110f030a051f0b0d0b2205060315040b06030613110126100618050603151903050a121b0204 65
    0x102c00d00c00341d41080e08001d04680004100008040d0200031614100f42019000381c107503d0642c000600d01e01440c46802e247e1600041210164400c542c11a00b146034842c01d408008410180c4095690400c0e001c0c0c2405986081c090b01022580d1109480c2d00b020311580d01403640c0c1c2d900000e82e0241001502c4810b181e5107224800240039402420100030b800f12059250300d030300ca18526072080c2c41c0c40c1b0424502400c96160318400c034258103800100f07a07503050708002c122500c50002081c030700b08000307000c0d202c80c640030700a10040000740350000380624400c400b161000c0c1c80d0740c1102e0035810002040149410300c480f0390401e8a5000b1004016481c84e0032400322400445c0e11076030740c101c4400311000901048130903024402540c2015a196481d00c4655840726810300303050100302c860ac40940045403903400141c81140541e100c1c158042ca8400d441394400d942552803034155507549421500700c0c2c0d00600c840400c02440c4c401c08000c4a014110846c120310b06040e42c0078400100032280501c1c3d0036806003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 443089361 1250 443088111 443088131
    0x201090503031605210702010804292a03010905060d080c030a18050a03110a03020307080607080c030402180709150c0c081606110709060303030e01180c060f0201 71
    0x82c809402c056000c0e4880f20001c43c810b190090920503001c1c03c1440c0a034525280103005000d200c00d0300d4a003a03082c05c016085841c4c0d8280200072040f01e4a009040c43c8882d540855003484800e48940565500c41414807036071141040c80040115100b40c1ca05020720510040202c40700710f4001c0d03074002c2c80140820840d011103480d204186e91001d01d5691041d400080d107484419442183c45e41044646089203018904100008040860511003c3d20842a403007414005a88040071407009542c02001ca030300d500d6039070806a80310342044a440010078071450000f44000c07224000c480c4156401003203801101180c0345480c044460180143c0204120502c0c00301e4070300d00082092119840644075588803600320301d8642035801550b00006c40d19040301c20f00c1448040e403460207100b40e1b00030342807070702c11031032424181b92502000e94060580755003405800030500d41c0592208c140944040000d004108004021000001040c3c0004007016150030f01044494840c81240003035250604c0089610141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 443090611 1250 443089361 443089363
    0x6090c040b0a05090324010b1c060602060717040503160f020405180c01052106010c1703010314030306010906030c0504091a040507080708040f08040905100f050f030c0d0201090503 79
    0x2100440c1e101180f00050710301c10303902e0308010004007039242614001c0b4080c11843c42c01d448030010b10800d4455000421050058400d220120b00c0e12a400032003040941d0340c0d950029581d4078180c86080202e14043c03150b03019541c0e10302c4010710aa4006004603d010002c40c0200c9241240c103400f41c0350020040d07420320041c0d031580115800b49481500d002c0511902007402410031440b124000e0500c24200b100c014400b4428503503041040d141e896500c1d60395207400050307034030411500c0000c0c0807803d0700440c02d164284071005141030382e0161480c842c41401d400303110b50340d911081d201c02d40400d03e5081c0411019100b604288654000b9142250520366a0006041980d0303441c81804202e003140c0d20100d1203818a8400c0c29409078140ca002019801c1081e03014080940c043c10140000c609041d25405000c13640046800614a4030070410072480d1100c2c00f00c02c4503a90340a0068400940c0d2400943c0e441c0112100415020040181c801c030700c188400c01c20368421100b41203041c442c035000c00040711340d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 443091861 1250 443090611 443090617
    0x1515020a24091505090c0a090b1809010501090b0607020117040312060611150f13030c0b070e12010204140105090411031303020120030a050712020315190b0306090c040b 74
    0x4400c03244001c0e001d94120801e420384d14014010341059115420042041d524514910200e40402c40e000500d2203400002c40c13050512840380d07050109030350091110000b41540043e0488440e04030800c1024824001c0001502c103558019000400400c038201180b850080708681003842402e04004c0c1701c4007090400d007a03510035401100032690000c016000c90000b400000708c0791f05141103035000707490104072045000f4006004113a144e041010508105402161280d0740701c1c0e003001c03100e5007502c3c2060004100c0303898404200c0c010b13046104082c2d00b03028140291000c2d944950301c00740e19810300300c004681030341016100540c815241c505185043c0200c0c0010b5009040340b2980da05254103d042c06404d4076075912440b408050940241001840e4100c241c90308103000c1a404034513508c801000f00c4e41c451102d203c60304181c0c400002d2140d010141e4070080303000c2c04180c442500e503104c005084d140300380b058802c20800000c01c1001070315502d03024802c0d0f07038069984100d041c00c01d81c03114091015a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 443093111 1250 443091861 443091863
    0x50a112e060911090114090d0f1406180d1418060702040f14090a0b0703180c18060f0e010b130308031906080105150f03070503030d1515020a2409 64
    0x840044d90580b5942d02450480105143d45412480c2a80d40400714203145050341019200300207210203042040760f03105007820429803c60444005091107120751100d401e030001c01032070500c601d0f0704014126008108a03140d960300c0002460400700320352140c1149441c140c41559219004000b40c00060f80d03248641d020050501030000741844c2c00000d040c4107103601401000442d88407113640740010381500301c4190300c140117290103e600c03a60b1900c0d0003100300403102c1c01070030340301072510109480501c003103080d030050050311051014654a0f000070240003098041d40c500c0d203036204c0c01800380c121020000d001c50420702c070b0740780c00359690b135203400c40550402c0c1d5803904543e03456030202034002b07128001c0802810808008214030304001019403800d0b8401110140151840f0070700d148640d4040c0f0100d070003400f0150540760303038240a4140b071008000091901d080c02e0b144130b41c04205e0602072202e5020140164005282840194846245410040d52000007000d5507038a0541100c00c0c5000d108152 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 443094361 1250 443093111 443093141
    0xf061f0902030a0e0c0d050c040b0f0603090f0607030207050c0607020d0803190f0b0d1b0801090f060c0807050f07081b0a051203060f1e060a050a112e0609 68
    0x4c2c42c02c00d0150400d070344070303e006128030500c25001000c0358010902501c009011200002e00030106408540c80c080c148041c40c0d03100b5404020003084a00109281c01504490026241c040d0703500c44054003240180d440217021580400c0c600d54890404400901c0720900042070700d030940b8540e0ba1070070030036441118049010b0700c6481e40c0b441d00100502500340c440c60050014011340203500042140c852105502a000c07403150303691605016150128a000340034030b00d000b44060012800d0502c4400141d04088548600d4540d2149006128225460142e00c0700c0d51494900700c0c44c0b205201194000300400d40c0d9142c0c00b040010f140317440800c1140310b034074008005400c0c10040760030543d040c004c0c41080d0713000d640c6003041007003401d070b8030911510700d105411610b11450300108295212020b04102001e60840e0780055000502d540240144c0b160b030a0558420402c2d85615080c552a2000c01c582c18014603150154400501c441401d00802c0681098000600c25510003c0f031058403080c0080040b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 443095611 1250 443094361 443094371
    0x706180506071e081024110c01090b0d150f031b0e0601050d090c030f290f2d0a0f020403050c0d0c0b07060506010906020f061f0902030a 60
    0x30424180210756101e00c0600304840f444040245100c503c03102d0b04041c030100240280011071580c0b514a500010300030707160321042c1104100b4400342c14903881280140110b281c0c0c142c81d40e0151400240b81c07402e2041a91804407103403401800c01031030341041105441c482d4580c0b42042c61003803182d2081c801056035001d895903152460a050b0b0301052000c1c041c244188003060305000031100100034a0f0042c1082c82c22607518004003080b0b200511810300002c01c0000c840c04000148143c96140ea40070074092110030b01803420903e003000c03038550210841100c1ca04450001f905c0318550080140c4d0090300c1483c480c044400e4500c00ca0718200703208011b074a404880d1014003203600c15900c54808034440d03540045280c60b0540d203a0315640d000203200b5500c01e00c0054104010020300c04801e400414007689501d1700d802c814034048018060423110a800505000b0b4001451072000503800380600c454000740c101c84d11500d100380101c0c40c41411a18449205c800005804480f51008503c611401c99000038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 443096861 1250 443095611 443095613
    0x140d020c071401030b1503060310020d020406030e0a0f06230f0a0b0a080616020f030304030c0204110403020607060c050c12070605070e01050a08070c0c031202071a180402070618 78
    0x9046620104141c3c1010702d80482c0b044151540542c0c01d4680c541883d03d6034603540c903480001c3c80c05001c90440c0c5101c80c004034250b103981401d03070050b1042e07445a8500b030291903a2011519942c031a12000948494584106074003c240d19170711a18100c2c00c00701c11042e40f480010001c4818880588918200c902c0036001c210b221074042c445d03552940b004a80038401c20703160003c0995103520150001102d50300c07002414850900030801441c1c44030100003034070f807245002e0030086c2c58440c0b13904040e0701507400d0041e8110000070701030840f01a43d0f40100f4460400380c0503103c02c5e00a142c00441c150601000f00010b607142a420000310041d045034500c2140da40460b03180040947d00c0c0070b44400180020542e1204a603a0042d00780da2640c00c0038035150341c9903902c05108130381c2c0342802040509140c0c10a80c0c00b009110342011064801e4441740c0841d5041a40d81d9004120814600034a052012050003c482c0d0b007180309048811002e401032000d4240003203510b44408071454800d08080440c003042e2000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 443098111 1250 443096861 443096879
    0x20406050901030f110403080f30010602010b1e01030b030618150106050324061306081305070b070c0b0f0901120e031614010504060e120403080901140d020c07 70
    0x10b04c48200340c9402c0c8a58102041039040c28015030000030070b00000811103070040340c80f00040c0c8070b001051000558200301c0d0207c180c06950000c81400031a030f01440008201d0302d00500910380400c0c0042c008000c0c020b000c1c1280da00f007002610925041540b0b484482219a4007000024043c04c0c803120740e00d181c00e40d103d2a00d0300d0000c0d4030540080d158100c200400690341c02c41e05490740704803100c0c400c100e036000341c11030060a040d50080c107990200b008180080307031001c81c648980650310240c5406030140c0740c0007401c04c041c00003039500629039445400c00f40244d03009040a41103444c4140e100d000c007251540c1184141d030b0440361801d15003c0000c26220764035a4010440c145080640c80104811290507003800e8907403040f440c229901d800c1e0b021620040000303000c041000991103038001c20940c206032074a180a001d12040100061284818100d880c0c0b40c540200e404881c0d1000e206442e02c15036000569408002003510651400709000e808021405030008125601034035000d41003050030030103c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 443099361 1250 443098111 443098121
    0x270f06040e0d02011a03010911010302030c04091802100305131506050d0f020109150801030210050d0e010b1e011e0e100203030105030106120f03030506030c0a060201050103020f010f050d0209060d02040605090103 93
    0x100e8881d0703052203150070109109c0a071a80c0111428600980e480d590b00d0b90a08041c0b1070340e0700c42e101040c41c11705659080c2c00405007514105201f150000310300070365100e007213050302e000703503807000f0094011980980024080c01518a181034417450118600740c3d920b0016950740403420007034072103041c4d00808904540c2c1c402e024002a001071480d508408212800051016205003c02401810420350540e816070048040d510703031101c080710601500e807440c18010b001c0d00c00e480b0014003480404002e08002c5d5503010051003910b4042e920507910a00d401c2011072041e40352003d0130240565681908040d48a000c600e084030b44c2141c000319507a515042c203050850740b09600182d0004040c2c01c224000814000c600c103081c94240c54007003101d4543c140001d0901c400b8030000c0c1c0e44150740840c0000d18a4042d0041c504890007100c1d00e01801c40f240005643c6085042c8080740010010440b0400200c5103a000c2c0080358006451582045284032180c1c3c100da1107500f1100c0070a2001c100c00403a90f03414010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 443100611 1250 443099361 443099411
    0xa050601080f280809040204060509120d1b020d05030c030301060e040203010609050d05100e010c020c030c09071d0306100503010c020c060313140105040f02270f06040e0d0201 77
    0x2c080c1035883c1e04111185090128007406203d12108501c0180301c143d8040c4d40c0340100081c0f04659440d030b00d900c080d106078800718515000d04101c040740d10032400003250a00b150300b0f01d600c598480e041d80e1301e2182e502e06072400c001c82e40032907010b00c2ea6000c2034080010340000d01261004640c0c95041c248040c04002c1c0c07003a2018801c500400044c84035650000700301c4219081981c22200298803407034402d061811915540103510301c3c0c4a510b008440c0e05412202100c0d555409030b8aa845212042c1a25038118082482c0c02081e00c00100e04464400ca00e41004030382203c0f0540c124000c3c010000b81440405e441c101c1849028103c1841a49070030310540e40000da040c00141000500d2001180c601e00000304a20a0001c500ca501d005000034003500c01e4040d00084001c0156182910f0403a02c6008060000d81c0100c041505000594821061b030b2030006a045050b000399941d010381088500500824058000c3e846200359080400c0800072926082425000070070906690400d110a046078010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 443101861 1250 443100611 443100613
    0x106030602031e090c04020d1b120f1a0f030f030a0309140d020703030f0e04021c0b19050904030e030d091505121f03080c030a120b030606040b0109080a050601080f 72
    0x90002c01080090700640c0c1c080c0941c6c0142e111190342e85070f0b10092a4800c00001025007000c015007419910070a004140c107078040c41001500d00310f080b030000321801d04035900c0d081e08021400302002d14001004036003c80008044616140b00040200c0c11074020800407000301c0d8a41c844074007048209441c1c000780c070301c0c0b8100404c2072507000e5100941d220340c94031010b418040e0015401064901c5413115403002240a00255641e1044d407102c00c1100041a010700c243c00d251610841d07403494441d0b070500740600781005207070710310741481c0800c8118280503100720240a050000008640c405100082012180b0b40b20704008525040d45504404009148113080090030843c0312101002000005c6c0c00c450341002c41d012a88100107050300511143e0405040620046a440c1c1c208100100800742c0f10710a82c0d80301348035080c00403150305480c144240c5540c150003040c0011020305281d80034148001e030514001452541e11020103007800c40d40281600d123900721400600030201c0402001d20075901001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 443103111 1250 443101861 443101921
    0x30207150c080a0b0319050f0601050d020a1401020a0c0e0a0f0203060a06081b04080f010e0a0b0a1e0507050901082a0c16090c110601030c051908010603060203 70
    0x2580105035210043c005491036a0300d0034032600540303040086a00c001501c612017410003189042a0f03070f4800210000c800746100c0c0200102c0e190811480005100794050072006079141010508004840c0b900422170441c070075030200c0400f151038101c2e00002000e024039901800c1c00d00c8842001918a00c50500e15401d00402c00d114060319040c6104c8110b80a5103402d42064481d0084c203283c41051034000d0b50b207000c0100380401c1c03110020800c5010160500003c004801b0f145040381c7e04e03418065809030441070030400040e03a600307a90700080c607180303070070200d440c00ca01e003074410001110001d031400400a1390225185c80d03035580020100380c001c2c0c158411103404803856504030500058a0140341402040801d4414546008000286540c44004000c0301e00b5921411043e0040c84014015030000b0702102c0f0940c6802c07400305109040e20b4102a02c014070f28107003414000c0d04424050343c007001142000001507112420311a220107548280c8015030343b070a00045690f8248070114800b0304031139a40c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 443104361 1250 443103111 443103131
    0x510060605090f1012090309150207061d0a0b39070501110607030903051204061b08040b0105060f0417160506190c03030204030641011403010b1003020715 68
    0x111002d60544013081011509400c2031504858031070030b5038051a86490b054271072000705d81e0046030010541b40a42c2c0d82c0004d00d148100c0d070304034003a400641c040d000201d11000740101d0f10440e0080c2051b41a05500083c461016882c002c00a04d99141c486010494000d00725901d8000f072100d5030041c0000d04e4001740c0c000d07181305903945502000d006030090650701d240000c209409501503804061a03d009103a0900e800d0a00c0c4000c0c0241c03a8000f520600b58054610081c0e0207401050b0091741c00c0180310850368245418429254444803851141c980b040c4400200d03040303480c09036800c44c041c0350090070000c01d00508400c80082503030809440f80301d0620010310700407420701c2c540c9c011495603d081c4030038024904040d0020310558001030301c01421300201c007081400040103010381f098051a4018190006685c0e007050401050b00c0240014004004108803440c2184010646100070000509007081c14001070907103001c0c40359000440d4006ca801802d0007010201c1d0510348000d0202840507442c0b0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 443105611 1250 443104361 443104367
    0x1205061002100b01021509010c0e060a0c02041e020f2a060a0203071209080703020c0109080d0509040609240b090607081812032503080f040510060605090f10 69
    0xc031074000c40001c1c2d580c845152541c0c030030450b00d00d405c58004161203043c108040d00e0348c0a4503c001d81c040115640c00500c1da200e0401d5011202c07264407d07580c0e480d89129075070800002c4d08a40d55000d030085030f07400604141c401648018035a4011401003a903946e88800b40b0b10b58548200500c58003106241079000e24480404201944d00814100c401a50395503014010703a0580c4200d07421152442c60f1040f003004104040009000321740c002d03000c440111601100444004115000718411500248410320025000d80c009e4203d404000f00080303180c03030302c0d0002541294800c020201c00304210707003904003116a451228401810011902515003042c002c0401d03071070702c5201801070070320740002841c0311505034245e4407036000c4400804401e03040d40c4c0c5081599070303500803116000580740100900014005403a41c56010030b80c0c1900c3d824419602c2100101d003a1000074801d841038021680041d00c10212441043c0c040c4c412601c1c1e80f92603008820a02c0b11a1903030f8040d081c014100c561035000d0041d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 443106861 1250 443105611 443105623
    0x5030319020f010f0b011d03030f0f0702132c15070221091c050a0303270302060f1f150309050303040b04050c030a030f2d1205061002 59
    0x9142038000c040c22003141000c034036107000034203148555440d0602c241d101e0030083c0c00c0828605802d9a0f04500080c0740a51104004d44014140e80c6c1540100031480e400b00f40751001e40002004c240c0000e00301003ca070003041c10f100140325480d9200340d440620300c216084c0c1c40045890a4083d0000d034090843d10281c031581c842c035202200300c26001c0c00c40045e0b08580300308440701d1030f03814044800d0720f41151100310b099680c0003042d080e4818942c1545041050556000002502c4d400c10001c00c415003690301d068006050825250b000e914001c8001e15105488442c1c08294a120354014600d9141180b42c2203014080a01a605001507011080000491225881c001c1d125441284642148080c106800030044c52400911500001c810001400b8028907400d00c40c50164060f180e4607400c2d10105503e179155014000c0100701c1d44416000f80510550300c541e840e03191a4138101c0e1214442d90120036450070404e03281d0001315071a1140f03080142034050150041801d0301d000600e00760000029440398 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 443108111 1250 443106861 443106877
    0x5090d050702190b0a0305090c12060c0d091a0105100503010e3d05101e0c050102040302040609020d1a0607030302070501060e0112030801120f02040b030f010515040e0304050303 78
    0x1040914200d4035828183c1da042c3c00038501384003000e54820344100041c000d001c04640079455809050340005690801100369500002c01b0b80240c02c4555620020224075000045107044060f5900c900e43c002403184514020301500f8601d024803a580b600c000c200381c0c2c000d640d402408002d020703c010850303d90030328190340e0041a00e03104441e000400b0907140035044403010004494484902050400304150115103081e5441035400c0a21082090825950034200a218905480c440c420304842d0521a0000d00c070f150340700380c0026142554940005040d1046608410011a800149c0700100d441c40e100700100e42d1b10441460302200c6a00c800143d940c05402e1000c1d040c95000200c14042080a501010240421811480c02542c40300c02c0304a00310a1510201e011900500012a550b00e548010304032850740000c0118054072180d080c0f01c05000700201c22601031241168000351a20207000d028440c6c01c0f4000c51400410702c3c8420401664107142199019030010402031015840101c2280d00b80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 443109361 1250 443108111 443108119
    0x1a04030f0311011a0307050916051b1605090a06030b060d06200415030204080a0204020a030e0a08180103050103050a0b1807090219030e1c1202030903040905090d050702 74
    0xc08a00d040c00c1c2d88104401c5400541d5501c3d1148095055450f4030b45451445001d9080314005a214000d0080301c600c10384030300f10305040c8031400c2e200080c8079000402c55203051302010004481c050741e42c84e281240402400180210414050003281001201035500902c605018080c4500d16128009514000741000340070301182100d10090001e0350308011440c107015000d0b201d40181e20350340d42c0f000b0381150242d8124510448030508005200b4001d650a86120501401c00c4640d1542000000d60040c01c81605040d111f84080940c60303c11f026014102d0700800c0f03ca580e5500c5410380009400c1140c180da4141881d04005202054001402c80e50a55000c0c04070001c1d0349601d20725101c104000e4030f0143c131600c201000070400e65041d401421401d1019440c0c0c104440000340300b03a007541d851151410095208810030404a18910506480001e4a0614190380481140322005a0380100d4520000313a0002900f0403102109124140d880813010b00500322907805c01c1700081140c440c0400182c41 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 443110611 1250 443109361 443109383
    0x120408010c0e0d12120b03030c1b190605280207050301230a02070203160303020f060105010c030c021009051e0a0602060402010903080a051c200c0d030e0a12020f071a0403 75
    0x2005d50207030700c01c0c440081c00400b140c0d15202c0740b8031a02d42c1c90200421200400030400000c481c541021019455440070f981402c1c58494180381c021034003034001400d01d140070a0280b00345c0c035203c81ca84000106c03200499019104440c00c000501d8252040001c0301203007100700d046264000721080d0b0340503406c031103d080c0250755000203000180c80d1070325848000b0200000d90b0300001c1010303000a0030307100d0700144000340c1e5007580c3e90303d00650301807904400c0078001c20b921000c103900529102c141c881c3d0740441401c000c0d6160307803100d011501c28a080d18405006801c201080212890100c0e14100100454401403003a0b181076800200240348a110003441082c0201759003a1141c0104241c2d8055041e2604c6038a00310100c10400c1c02420700504020303d8080c1c0380c041c00803e54005002c8440e0142c0020013880110800c0c00114024035044041030f409019051032240016801d45100454084a0b801010080030900405041c1000c5a00010704140b40080c2400070140420649044030b41042c20030380 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 443111861 1250 443110611 443110637
    0x9010c08070204060b12090601050616020103141302032a0d0809030109080715062d0b19110c18130c0803190c2102120408010c0e0d12 59
    0xc55029511000303502078201800070032483c1c40403004c0c00546c0c03a00d03d00d080c03291b1200c0302040d803112028000c0781d4112100f0005040607c803030030041003c0c1403040c50005030200701c0c00d96146240d1400da9507205042c009101120039460100714130350500d04201e4603c4540e000c004084040d00e80038801031405040c801c5407820502c4040c0d0196000244060300a009440351823400c0700d80b42d808050100c45000f08100e0100402d2813501c643c1c01500d560400500e2580050360047c0d000341018815801c102c14a4603000c1442c0c001807014018201621020001c00120305102900c0706001030112881750b40b01010002d90b0365101012080131180b00340030804a1380302c0c1c504003110414601d00240c09003000201c0003038102000401004014042d1611604030a50000300700e48802c1c400001403d40c0301801703c40c04000f00d440b21449580d88080c0110f4080c0c10070800100004e4110f5849240980d559211600031030307402c0743d00d01e81d100700c08980d100203d036503554401c2401d10803600000104050552000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 443113111 1250 443111861 443111873
    0xf010b0f0612070e0d0b070206011a120105040b0402040902040311010305090a0507031704080a150b0d0b0406020309030927130b041b0915030c09050f070302180909010b180c09010c 79
    0x488169000540c4100d41d1030281f4002e5a00d40c001e1080c544951aa4018110254440c0d001d9849032102040701d007002c3d0340381c2020000900003c0759100e80c41542040300080c6a603040c4020001140301740f44c154880e0502900150441d1b200602035865500401e00b000d0000f032000c941c42003900d0380403020719817818030f0200700030b100c3c01075401025040c810380001005110186c0c4943d41400001c0c3c6007403000d040300c0c0d4240482c915210074000c100c0e40c030000102d000a5941d8010f182d0010300300c400c4030f003408400350001c0c0c1218000c451040e02c805000c619840e18030305170f54141d40d02011200c03191802d6124cc0c0d407005a03903500200040c007120b00c9002d15014020002217214000c00031604144038002a40002900b100d155100c101d581c9503d48400140000440c040d540c07003100340c031020301100c1d0344690058010f03500c00805003d2001c40d805440c2074603901c13425140d000740450400045e40c14075000c1801143c11901e602e0041d9901d0032001c101c1c2e950051400c40b00c501d1400e107030107203041e02c141c6806 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 443114361 1250 443113111 443113129
    0x60c0302041d180d02030702011d041119030614061b061e060406240e06070b0405060604090c051002070b03040602030709060c0c03030e120f010b0f0612070e 69
    0x40000a41c400615502c2c0000c6050500a140c0f904040050f0b107828100725650740c0342c0d0b01c03003140941c2081c0705c00320141d0701544a11056011798600f1110505c1c601d000101100c0d0403929504041030082421504000e00c0140502248190b003410000325040450600c00505003000051181000113814a10709000e80c69045118014008648090810305407071890800c20f07079151900e000524000903110300c0e042c0100c5c070440d6100c4d504680e80910282d0a4409411044004802e100030014410341d15291040101600c60040742070b050f242c240b80c6041418114050001485941401d0088c804106400540021503204803842070861660410603400c18440758800900303850003000b008284503540d0000c42c400c0e09565038a4000c1a1128001e84403105800c101074801c01c078071001800020700a40349286001c80050091080c91050414146071404604111f86180d446406541c5603050048021342030709000c81c1c80380e041c014410000070003100018852010409800304000343c0e038882d0a10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 443115611 1250 443114361 443114369
    0x60312111902030a08090f031e100605090a05070512070f030c05090a0509070e0d0b04050f030708041e0315090215070203030d0c1407120f030504050c090a020c0f0a021203040b07060c030204 83
    0x540b4000e07075105010990070b0110501680c09d40c020700c1380003402904c2e140710790700984000411031050354403404200c40c028080200020706100c820001d80d1901c00903440064030803c480ea0740c40302d9000020742c00800761030101505a0900000f44408003c03969000e88a80c2903c1c0141c490850326030300c41320125600c030400040d00b50407034400400c0368103000ca50320029104070f0080045540c000400f0003c113940340704d5500050314800e41444140040203c2151181343c000b205218103041c030751251145c28280c18119080c07608583c1d540665011801c0403010f045031003000034582400c01c4140d402007900e80c4a410183c00c051a65502c00008940c092503125059034101e5007559161380440c0740c0010001c611600e108041114001012101d500c80d0160714811a4000b019140001c0c0140600c04082e4021b85081002a003d0101c180e20300000c004059034408010010012900c40f801031084040032494041415002000244015078181044500c0994029000a01c0c0301000344201c00a02807900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 443116861 1250 443115611 443115613
    0x1e08070e13123c0206010e04080d110408060a0b1c02120a08041e050418030318050d2d020304060c06060e1302030c0d0222060312111902030a08090f03 66
    0x410307403c90801c0c030b50f04410300160f070041410059070101000d0740ea0343c4003449021140991840000c002030840f401503d119104c5040c08181c0c1451003031068600d820540000009512000c20000d080b0401d0141c04400882a6a0f80d054210340100ca20442880a080a806a0713107103d03054222410802c00d81079420f4000b0304079611291244400e420b00505003081d00340015400740081540e20302485180ca14800c500c0c0140c0c46000d1030358007600036100785118091081c0005491f040420014002d03a06419280c0e5240c10742079056401c0d46036030002424084044a03021624003d000d03400108840580c0c0183c1480342d920346e00d500e800d1000d420f4540201c05800c41d450b0038080c80702c01c1d03102c00607190b40c07007142511032174240c0c4010f020501c8101180a5840090704681180c502d41e103409800c580700c0c0c03000000c14032035201c0c1c482603244425564141e00044012000010008003845442e12068264040e1480700308a0340003e959120500d10140044d4400560719107a5941d56400388a40301d4094 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 443118111 1250 443116861 443116907
    0x20c12030c040510030c2001020702210d0809030a08060303040803070309060e0609090402010e03030f03040c030c0602030a05040e1017010f061a03150103061e08070e1312 75
    0xc40300c1c1031540203403241502644035080640500b40c042d0103124280a078940e50a00e80c200003078841c00301b1460209200905560801090001d40c0b100d05c5c1c14080b01040e901c0051200c0c0c0103460715458803c01d05400c030b0800884600380014240040700300d4140a4240c80c11000c66118040082d081d44501e91101d100d52100051080c101070708103405030129410303038039846100365002003070150718800d4200060780010f504000900560140040181e041c00107130469040250381524055581d000b5034081e1070020304068100708125041a0070809030070a031002d9800d1548011014145000d28000c210500d000080003440301800c603540d120040070b003003100c000c10070421803800f4002d11108010011950030b244002c035511814a60040242c1d00d254605032541c2d850b003950390841d20401d01d100d41010307151900040c03110402c440c2d0000b044064040a00d6003813500e00c01c545045500e61004030384425070230402040805956050110702d800480309101080c034000d04941002080020307104180c103079 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 443119361 1250 443118111 443118121
    0x509180712061a090601210f060b07050607140307030e0a0c1d0c180d211e08010509130314180f0406050a120c050301020f0726090103020c1203 63
    0x1900481c0d014000c041c43e290382140e40c1c0050151542c1c084070081d010449001440c6030350b640358120301031858400000040c0420001d07161105644040d40032681858021a852091003002c1c0005500a10141060801c3c80103a9610f005d090100804400c181070391074004001c00170b4207010030751265500c010805581921280940081503486101340c0750001000002035688102d03204548400e034231084d9120041014208200e0002440f03c0b0840d04040080c1211544513404034000318881c01c0c9490340d080e00e800d4580c99041c0b003080c42d0550000c00030400010003440e100c00c80160f801c021404c0d024646c2c1030080c2000e035012000010001e5803080001200801d107100751920030038101003103034504094090349040000b0349880c0d018146d404525032400704440180f0046400030544030709020407000f42c1d9200041e089802040405120001c005021810000900d111203c01d0090320506407010aa0000c51940b501032807040b117040c580e0000740000703d41070420802c640840340354119562881e03d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 443120611 1250 443119361 443119373
    0x20319050307030506030703021f030b041d15010e0103061109030a060e1002030103201207030303020301030c05031902011803050109150c050c1b0f06220f0509180712 73
    0x204494002c0040d2500002c07600a01c0c0c04900d00045a800810902a1301101150400901804c42c03404003419610042c00742151541d0003606410034540d41d00701c0100644100050030001131452061090150b100148801c210000c0700782c0c19650040b400240180c0b007070030708480c01e219100d1034543c54841c2030250310400c48588c2108480035032284c240c0310000040300303901050b0300003800020500d0302403409005d100c41203890011a9441c0045c0a07a00c850080b032040d80c20300c205030300700f5000660000018002e0010314221840240010f50040c4208a014901c204e00707038480100082c10044a504503269504089140c0000b4580120080044104d0b0786052096882400310b6030300f40d6424481c10480e9035000d001035443c0801c40d800035009950701c203000c41d20f04401070416140d116440400072607554841a019200303500d0f81e1203900c40d6280f014601007113281030035407010f4201d42070100c00b4012502c40b2444c0399001454402c3c6990154002c2c40320508040950f04001071500d0039524403018086 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 443121861 1250 443120611 443120617
    0x1219090b0613090201021c0e06030a0614010e060901030c120c0908151e0402180f0a060807121103070b0a35040b0421020f010b030109020d0b040302031905 68
    0x41c08407510425401c40c40d05103000d494003124003034090b0b04941600090b0030003a44000d12400100e192900d00c1c40200c0000801e1508280e0750000c405560711424005410f402420b44049142402c2c07a0302d9940d5000005000c5114440c407441c105a106c00003034004034080e000d0000d0640000300244017030507004e14001c040d9003007817147c80102d01c110b0344004034005d138004855000340300640031850308524821060071526009803040f80c021005000d00c520718215581d5190280140c041001003d003454107110f0b0950704680c01808050704205410403004c0183c0c081e07018226840301c0f0520014000c100002d0405440c0da000d003060f56400a03040d00541d5011181255040d1400282c01114001d04085c1030716000140f1341c0140d440004002ca404201ca003107006600ca403152001741d007240100300409092006907006000541c1c40701782d86420800e03080c00740340540703417007900204800c80a94000640910b50084060180000c3e400400e09040c420700850f41c034100d51412150002e403801200608a034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 443123111 1250 443121861 443121871
    0x20a0c02190803070209090f010504060c080f0106120c0c02041802092802030c0702030d020319052a0f010204060c0b070828090b0408030703060f0b1219090b 69
    0x20040446924540380280d500d07806031401c2c2c200650401c2c4082d420300c031485401800008040c072859520700401d410900400b48150b00c91107021440395003417100a13150708009000118110b00300001400583d5005803004040300c8003040105e59102c03d980b00369858440e89101a4002d0f08001040740035140b10b017506640302c2d20903075000300c1d2581d403030f0b0382c2d14004e000c038546024810b03d02c3d0340c00c000080b003680c01444e004080c01000506d0280590b000900c0d01c04003281e20740260308089020803000c080c1c460700c3c0f8038946941c108030b0704d48400d081111031445400c92607094640454844203100c0e030b404224142500d942c0c00002c658883c1c94410161038408520384c112207030161440020355003486207209600529411500300541d103076020807540c088500d40c500d0701949030386411800100c2c0700c210199020310700a8019664a0030b040c1c0d0001d09440c100d400c8003c0b030f10040360003005121803200849900300c41c2002000881c0d00e4500a4400d03400c0a150151459410552810706000c0401c542a0080c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 443124361 1250 443123111 443123119
    0x200d050709060f09060806120303070e09090712021003060b0d02130506120a1e11030f09070605040b070816050d0908010618020c1e0303090d0203120127020a0c02 71
    0x42d5510012501141c02c14841c2d000600803401c104181805214183e4002100400e0222013034148407009103560000c0356210b0004080c04541c0c242e5080c204500d64025185002078a46c142c2081c9044800c00120700009000359124020462f6083c0f09074800340c0580601038104e6515038a588006002c0c0d04000259462019111000625441e204003120110f121581600d05ca84e640c0d100c0b040001e100300c04c08100d803000c111180d69001c8801340714503100d9001b40480183c590400325240c20201c00024840700d119401a00c0610031150400140c408540038841c00690316545460244138034013807490403401c80da1080c51041c2c10840d01041c3d0000d20351721a5181801507903255900340c2a03407468030403066402d0500012103a0080190000c0c041d14118030200c421a49074403402000c40000782c44c80c0c0321a50008402d009000c41c0a104c0c848080040744000d40c100014801c54000360302c0184500d900c100c20b03500b4076160341000c0300740403140301d6009441103440b907010440c00380004615550803841 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 443125611 1250 443124361 443124377
    0x120d0209100804290c0a0c0c120317070c020603040620040501030c03060f0612090503030a02030f0c03040b13030c0b040525180c0c080403051b0402090310200d0507 72
    0xb40e500040c2044c4030000c01c00034000429101e5501502c62684030320a18410002ca0007151000310324000580001001400591000c070700c031a040013021141d40c01c100303c01013014001440006540b041e4004c141740e4040340e800c0e03901c4e151031030160010a003020b05c60b048035400e09105010800900301800031a54281c805110740e03201c41c80200c0c1198428007e0540803072401009001c0c551060420b111585402500050940e4950b00d804d4074540007140c038002c605800108115140400c03070086a08103000b08102415070400d0ba0303401c0d07401803009050248108a012062090620650b050b0401982100e01904642804c1c2001034541008808946014119611b02e516210741071000c1002c80c2c00c0003000c500c1d003100341c0d8003000281141c1e43c1d0000c00c112607078081d000460758000081c4000c504c0f8034010304080b00e40d100d04442e034030b1000919034485c0d032041c08401d2694501064a089401e6130721070001e03c3c0b1840901f00c100820801e003409949504c04a8141ea812915501103401000c141d225104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 443126861 1250 443125611 443125643
    0x8070309020a031103011e02030a29011211070302012408070e090f0d17010909021c0312020d02041e080706050913090807120908120d0209100804 64
    0x105440e03540d04029008034000c00100042140325800e1004c00d13800500209008100091400001c42c010140314240c40d800001c2c090810030074401d8a115801da90499044a400a2001d0113410b00655480303051282044442c03404c1c2180d039109100081598a171152161000d080c02802000300c5070801424048100c40164031042d404202022100d2110040204034240394540e01143d4018180340882e10a81c400d249840c00700b40104807030005981e440003840b00c400d10b103003022818180d01c9000214038240d482c3c00541c483c80d445115401200f54410711141440c42c0c111425031411610040c03880c0b001c00c02080c3c594103134000708126460740c00116440c01403107011000407155841400c00c1e13070740040d204200d104d010b900075080b070b900c00070308030914074514100c500c0544540e082c003120614000074243c000c01000c0700e0b44984021603441d0000300030742800c0710550340d00c0c0e880c0c020090441001c928040345000d00e4045074101440603101d03142180000c44040c140b0780003668110303048815044d003a1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 443128111 1250 443126861 443126867
    0x1802090a0204052d03070e1e1b090a08060a020d11040501051606140a0e0d020703050c040b030a020406171908041205030d1409101803200708010902010807 68
    0x82c0681d81c1c010443d0580c066241140401650b40e0048580400c2010082215540c0c3c180802c20041031103440b071450b84e14042c2480c65208a40400100b41161010b040c00b0200c0703104102402c02c4054042d0199071045810001246280c80d0703488500103200e80020002c2d10600742e00905214902c00e001401101070780848041e49010308d0141b1400540c0910140c079101000c440c1614200380500800240b803600f08a1103040241d04031800075125450358090281030008101c407124804d2984080d010080c29030361040c1e1a5016031203403610603034071002e04003107903902030100c040050b9004108000342a0340e8090710382860130001c0c142c0c0c1c25000e14600a200b100c0c00008c0d009400e50f1181029142a090111808802d48105c400391000d03c800d00107210101c100d481210440030010615501614084010a24103c1d00e1030180c01c0c55410680400c40140c060f400807822180c4c1818141e82c0c0700201c20702c02c6280c0c0b41400c0200c40030b2042c0d841c0000d403558103501c0340700d084e130003a6100002907440c10300035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 443129361 1250 443128111 443128117
    0x1e010f0608070e13080c0102070602071101030b031e0c0d1202010c0807080a0203071101090f0219060815060c07060906020709050603060402040504080f0703090f06022a131802090a02 80
    0x16803250f00441c0080e00040743d202c0c1c54495a4450f81d076072400e10003030b41c3c1d0090883e00083c100700d4403180c5c00a04103050000446801814140c2480c041c080107116001083c0c60340456182600703540f1071401e801c9004001888241100503020306081c00480749400d0048002d508081c401c4059480c1c01c40741109144100000f522488d05500c0340401030b102c448100c0c000b1b40c80203001e030080101400306855801030a0040c3d45681c1c0c026403802a03421001e00402c110446d4400d030044010742c6100e4200032030b80c0c021500b5079208a80c0740e240070510104202050141c455502000d10741c0c0210311011808a411504210070740e980381d422240c1a80e1948a0742e000c4940070b440340c1e83e0550205000800606d040c0d0060381d44944903901080c100040d107881114560403a020460201c2c810850522a203160740c0e0081d401441d8510080003864a880c480700100f09100c841c4205c1802102e00304040c5455400d040c035000c8500d041c00b040a21003140c16442000307981c003012845074140b0408100700242500079 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 443130611 1250 443129361 443129369
    0x417030c040618050904031d03241b0c0609010606300f020d020c0f060708011e05100512060a150e180f061003090c1401021e010f060807 60
    0xd034039060070b000301a1002a0b9004500078040166040800c0d203031140d00c0c1290040d41310341c031201e51424840151140079540d00c66164000e910400c0c0c19149118003600c988050b09501240c50741d942c84480341d40700801c1d80d44001c1040801c1c005007130600034100280b03d40c03140350140000c21500345c45050441d03024254400c826000c00e07000d800d0340303040000c80d001040762002007080043d1039600022721009980080b82040801580424013284624041c84010300201800703003d48002c0c6060b120182952806014030034440110394810074064900307402d03290141000a2540306c1e402403204004100e40d01a041046107101e202010803090708002011900345c071002d0410151852002d80d00302c1c0d030642030a4100358042c2181c49148000303c68098001e00804080000d02c2c0e891800c4401c3c05a02c0d00300b408540105480d244815001c1003101c03001c101a101d00306080d014207840240100d20b01100750150501403070744800d40c203c5010055001032000001a00d003804040d680c4d07080f65440d6061481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 443131861 1250 443130611 443130631
    0x70503160315051e1002010b0a0f0506071205160b010312020d0f050903030409060909020103060e0408090603040305090306130c0510021002070501020c06010305100b0406240302160b041703 83
    0x741071040e45001d01301c0520705a004001d0a0a480550002034925a155007901d03005d030b55126889443e81c213240885201801c02100f400d61014680004070380144200003006d04440846505540005c1c850700c100c1c0e01c18010228543c1200959061803191081d0030b204c1210308020414040d107800c1c0c004941e810002045846a84090203806000d8805074403400600303505000400c008188420b0903c19a8003030f0524580000da0340c4050f1002504031002ca400844508048004010000382c041040340c8060710300340c070400e442e51103074902503a0320b003d00c07030b8440d031f1500070b8800300140348580b01401103c03140940d4440c0b69450390740c003d004940c250300c2d12220042c2c0000d501400d40c521950010071886100da000140b5002d00d90350000d00b00b800c281c1044500d6009106440d8558050380141c240d041c608403410040c00d4a001400a20340080f0301c5480c0c1488103058506800600079415504041d20043c0b078100d04504a10340791082003000c440445903803007520b400d41a11003042080c3c1e4440c0c0000c90b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 443133111 1250 443131861 443131901
    0xc2d050904031101110c0a061a0a09020a050708030103050609010b0402130e090708010c021c05090f010c03090302190504050c0a02060103080f0c0111040305101527050705031603 78
    0x1450880c0d814140121801680d074a070000364085c510307004014002600c800020785179010031441c0140a6404031900004075280ba041040e40303558a0151300e200701c8498540050b96841e29140542d00c9000e00280502000f00c00301c000001c0c4180403c1d182d1062550784001c10030703001500100302c100d01506010810285641c903017413008610b032420b01900408540d00b00d400180c0d94000741420b49804164500c010b8200c0030590f0700c0403960240a444210844c24041c0c24000044003250707100c043e03010740a040154007140c000500d07000301403030006590013400003403500e0f000d026100c1c080038403442081d02403483c050000e80c0d4ad40c0c8440603a490a01958050000c0d40d103552100d0325030b500562410703081c16408008008000300309204642445140600560301d4a145043c0a400c003c490070000c0c5002d402d2000c1c0d40c44010341d000696068840500c07002003c0541c054150342d2411344c0c060a00e070064580002d1240080e0018042c1d8810314020480c2021400058011029512201d00f0b030800b1104d14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 443134361 1250 443133111 443133113
    0x1205010b040b0706020408010c03020714060103050d03050c09040c030b01020c062515060602060114060703090b030a090602032410050d020706090204140a05010b0f04050d0c030c2d050904 82
    0x281c0003c01c51203014600c050704098946941710b08480d40d010020003ca0750010b0120700300300500703124406411602026141c0c0c2d43c07640d21a1501d80312902c0815041540c1c0e04006600300c3c403c1030a03107100280103402042041005c042c0030f0001d1001c0c5000c0d901510030507041c5407a81c503102080340e010070f80130348101c86081d84e507010300b4076131000800c0100d4800c91041898120b4685611a510040089500504481d498010f00100066010b0f06c118092401001404042074100c0405821103044c1505283d036956a00310040003041c481c0001002c1c3c40c00001031200312200300240c1e046038041801012080d000903410000546482140180070403400d20242e111250307240e0141000b00d00a44001c00c0011040e40050304035044010380280c1003c23240e0501ca0303074546078841c107030161060200040c680f04450000e840913002d40d10486114442d50a0b4100400600380380100c019a80004541240346d158444550b01c0c07510121101032941c40321440c104804100480d010444c0c2d4003520960349070301c503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 443135611 1250 443134361 443134379
    0xf09090f06151e03020103291203040909031d1801060e0d080c06070e090603070509090304081603050c041802090a1401060509040b030a0203061602120f04061205010b04 74
    0x103140070480380c0301d5120b03100048880c05502416001110b916154081a04500c0050300b26088410000100c12a111078a110300e000e403203215140c1c110840b880030354003a080b188a0b1440c42140c0001d21890305185070441007640100f002c903541c041941401c06650605428000444000743c1450041c02d210001004000d0080239001040c40010f072041c10605820b84418400360301468400d400c6030704c0003081080c03550384401061500e8504488208450500500013941c0d04030a000c5d040c0300b0500000440d200e003030200225002403040406907007017081e08005181c91950789110941d442d0042070300184072481e10f40b01d110303034502003008140180c0200d03409005450000604142481d030759514000035001d120311282d80202400c1e62215902e90008040c003007036031140160a070181d40700c444804010307036002c10341691000d1241910501c001a180080340780901207025014403ea001441c01004005980200140d6005031103696400210540c4107044600910400312484804d010512503084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 443136861 1250 443135611 443135621
    0x30b011e030b101d01181419090515090f010c1d012606040e0105040830192702010e010e06030a0902100c08030c071a0901060f09090f06 60
    0x5500041c100b81d160725402240c00b4414803441418160403013078010840307203c0300409400001d8040e0001d00c2602c00d0f18110302e8802034060080d0300005110140440340d04140d5000410240e0000f003264040541400f80351100482030700e0112460103030038003660109030140201c0484000310707070703c00d0100c1240c50000d0013001d49009009040004e02000c160042c01103498a082d0714030b00d44c03000030850038000100310441d050300b49400045c0e41000c0c1040301059509058481030301c4c1e0a510322031151005040d100d50342018201c0a00140e0064042c0941008012022445039580d20b008001c0701e50308000d90314400f6440c900c0103492410200200005500ca40c894820325101810032041d0390500d500020f0b0300e0381044800c1c045859848482c001549405811070b01280b0850810150700801500d4101c0c492000414030030403080000f1780c040400042c20100448a8090b80d100c035420b082c4418102c2c080c20705d03840b40c1401051750b040d0200743d014081c40f03101c00082d480300030591010001c0e541c000140c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 443138111 1250 443136861 443136871
    0x403030921030c020105070209070206060415031a0c040302030d0302370f050c0d031b0e03150c040302040501030b180d051b030c011107150c0e041a060a0504030b011e030b 75
    0x12101f1310180e00140c44004c2818050411600508214a0702c034051000b220304a0002c150b45044141d0204007050040a0f45034000703496071002080741d902e4040c0c203c1c03a407007240d00c029090b21480d0240c0e031301c3c00d9059000c1c1000c06401003a4070300100940180320703020b1220f8421001911010030008214030701031403000c8003241003401d1990a001c0d210f981d040c2001b00c09140640401d071192885001041040c400e08000c3c07081e828008100401c00d8042959090414101904140301802041c0c2d00d4000303605440085900078418405503860749400680b580f01a21151394100f0120b01c1000010700200700780b038140102d9a5020b007040300440198140236118015410700d400108800d00d00803900f0b00030719903048030400903295190358902d80b100d20171078410310742c24000d8a0082d41c5070000b030780032024969000045801050703411144a8100d4501c0e80c1d501501d83c00100012980409a00200075200b00c07405801451205d80c2c2c0c80007040c1c0c533080207000e15400000026030500010714901c400076001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 443139361 1250 443138111 443138117
    0x803150102010f290a0e06100507060f02071109090d1b050d0c050d020d050d0b01030e073b0703051806010e0a061205070504020c150a020403030921030c0201 69
    0x2030007141043c2011118005a000d03104498860760005102d40500b8601804d0420b81d0901001483c0242e030071620503020b08a68440c140343c1c0c031029071640c0701d6020780d141203403c02410001c1c4032105034054000d52249504440a600b02042d02015180105460740300781004000352400120422044170030300c0401816a038041540340e524000300c0d504111000c1d01402c1c2e40c03608400c0c2c1040b801d0092400b40c48030a003104552080320481c081c0f0b644001601c400d024058000300780d466110700143c001e00350741c41000034a80310354017000071045941c1d000d1180142d1000d40028407107494034680e120588a0321000a4a98020b00218007007038400c0d0310240e403080500e01c0081401c4540ca01c21410580282c4c00003000288490900283d10079510030800144000c401c1b4883c80440703559802e4503114184100b0707115550118040e000300405106200c0603244946e040c030811301d00001000d00030f400c5070000b600000c04544011480501481101c0b01849e02c00201a181c812240d074220b40040c202d185c22810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 443140611 1250 443139361 443139371
    0xf0b0c13090e1510050d060f1e0e0703020319020a050901030809040b1c1502090406180609050609010b0d110c0303061519030209031e0721080315010201 67
    0x480324190103540600100000801d8070341941c04034918201050881412803800c4409000407011645901c00032941c0588a080f8668554288100100356088807c50b41a09081e441c80340d480040f080d10b001c00215110401860440f04040c641e20784c024003000703406500503641c40d66051260540070341b603d0720041c102509507407108081049140d00780d0003107550040202d502e02c82c03840c2a01844825403c2030750441822250403000003100300c0d17049000b038010541076030f441c1c003010840d4040394a540c90141041c0300d10795030344070b1020200145a0060f44c00503d413250224409000703010b9103000710b0f0010681c01469003081a0006a81c3c40740090300b00c01c6603100c003040080d088210144c6000c003e500c01440d00c074608181440b6a0f0441050b03a80c0c51a8010419010016543c60f0514100e00c428030300147c84085003408240340529044444140e030811141c41c0340a18400201c050a0f206541194100245040d1028600022190008000000c10f00004103140031030026008480414800451 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 443141861 1250 443140611 443140627
    0x30405071a07060e0a0c141f020a051c05040302103005071e050c16080708150106020a02040203090c090901050610110703060b06120705030609060103090f0b0c 70
    0x28000e03146059003444004003080001c140242d9114048440c441103015010080341c541d139041d4160190300a8810801080c4c032101882c3c0c03100d1801c081c08220b40207a012650b02340ca20003958038100180100d40c00e00c10401036205822914101c90040106070f242c00f07041c2804c550070086c40140822298041000d155410900c0c0003070f0b0a10b4402010012800c0c00404e41075003c05400c0c0c4d80700038031520038080c000741130003030b07101030071803102c00c1d1100ac1d1408548070180500e08070704264603200c18050201c1694804120041e000c0b83c628101c540480c00c0f1110052070100c4050740d0301d400d120702d0003d42c000c0c10318038002d0700706034004590041c02c100035031303070b000310700c0c1d0001080503000b6a000030f0940e40d60300c100045400d14000707a00e42c92f446c03420300d03000c050800c01d450396442a0030302000f411280c4031040c00e81151662011760303200340c035035054500396442d2500005100da0000c03070f803182c824022500410030701c2d40280b040540743c603000030030350418001c60b844900351407002800e490725418003001500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 443143111 1250 443141861 443141879
    0xc0c0301140601054005010201020702030a062f1201050901060c020420030703091203110f0f040503120a080105010e1807020717070305070611030703030506130f090215031b03040507 80
    0x1002c2c0085541c1700001d601c2000112030b010000640000307056a1040007039001598001414441d0554080004250420a668800c2c13190f00d01420300c42801ca081e1035a1a0a084c02101030400c0103c0c00520848aa0369a0304100c0c1c02c00b4284240c2c001f1400da140300c040942032070340100c540500c1c5500d40f98a80355041d80d48400710350048a02c04006a43c2e80644010040c0b08000101c200c0300915050046910340300c1c0800991045000c2400700210001d50a095454140d09550003405c0080c16141c110b00c000410b0030250340002a5000010a644008595036010700401c00d4501d0002d00343c41079210708a070a20a5040700030b86103100350702c20710340001191203200c0b04080e8040c401134041d00f003c41c51440c11034544044c3da0013039420f02500859400e40030a0020035101c0c1c0a4051030040352603200e000200d59282c00a000101c10541401e221030102c0c4115040303001c56034400c0e168114820300c4001d07000024041540c1d20342c1a05085c0b92103128855000c4080d681290241d0203a0706c0941d40c400402c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 443144361 1250 443143111 443143177
    0x26041505070c060905030717120301060521041e05011b020d0215070e2b081b0610090902180a0b0310110a08071209080c0c030114060105 60
    0x868001480010360600300600c5a180e10000e203980d04110342c9407428240000d883e05040d018541c007001c1d4440095400c92001c000800b0303ca00d014040c25640d5840310402401a031040400b060000c40c0c031154241c0c103001021740f06204e43d07001040c800c0821001075010751141505c94096520b907403600f103040c40d190b15040103542410542d80041801242076031001e810509460070111000b6146020426141e170840d86010a60030300300c64541109180560318004031500402854503886c03081480010424084020103440310341d01d40782a031020001d914156a010101c5600d06641c40b1000f04010f4500305811464201d2300c01030850b2410220a6906c110000040311031520030354844c0e07a80240307428144805400e542405406028454101130209803612441c000c000411040c8400507100610490780704d0360340016841e003444111240e0400a000c0c0d0400d03440d010150003900640615854140308081201144090504c8940e46400041d00d40d50031400c0014140f106079005483c00c20784176102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 443145611 1250 443144361 443144399
    0x5090c04060e0702010e07030c03020108040512030c251a090f0604060c030b030d080c0313020301020a1112040e060609010c05071215051905100f09060504182604 71
    0xb100140d440c000360000c0c00d44620b01d0711034043d0f070488502840411a41001c9400b901d40a00344508103171124a032a6140590a012540c81300c480441800b0070484490000c1c503403030300284031045440d07540d5017205a500080c2d0000030a0381101c1111070b21904160707421142e00040810940c1c1c1101160300c242410444201d82c115166035032503403202d08568140c0b14400209400707400502c4544400700006e07190407000b8165a002410200029028043c402d5000402c04d901500035901c40d04000c4003e40358000301d082c0100d8601400140242c0c803400001130b14202c414002c1d40b182c00703865800610500e54422190503041054801e0201c02107601000380c0701c020b054505811003511340c507003840040d1804400f003580d0740c10304103000c1c4600680304203000031310305107000400511521484030b00c0000d004968010080702d4007021000680c03d0069100d1011948280ea0a10800c0005a2032003c2e0200c0e0320301c0108404000701741060914880c3d03c082c144120400501c7c0d29054841c01d550201d464000c038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 443146861 1250 443145611 443145629
    0x230607140f0f0405031002030108060403030902031207081305040b01050703110102040f08070e0916140d1403040608100e040807110915040c0906021902060f0a030504140f03090405090c0406 83
    0x5013003049060401c03205c0a5110300080440c250750400c40b80507142c1c4005003024040640b141035160540d50244580f00b1040e803d95050b5543c0e005034a041e040741d40210100e90610301c0701087c0090705080078051a042d80005070f450074a00380681c5d40542d4030012449003681190750030300020501542d21202e0310301500724980200740f01843d0030b294000d05d12004000e2410754010300c00f620300070800c20704500e05440d0486500d030b0306104e001000c034001c5480b001018111004603800c2c505104004001041520080d07520804140c2d0380c0c0804c031b211807031075100d940005001400000c000c11041406809151300c100c8034120504105800107008900a5601c000b21500c0c0702c00085041c5007502c2052007940550505030859407820030003a40f02c5628065247c1450f034a5180c4400315950401110b1948810f8030304107850389403c1c1401402040d0440b421150113860b40c0f800c280088000513901e400c060040011807808202c802480044d28002d00f0403115841380c850310004503a030714014900540480f074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 443148111 1250 443146861 443146867
    0xa090512010c090311180c04150e10051b16181802060a020a060e010606090b130b0d1e0b090c040b07110a1d04230607140f0f 55
    0x80400903400160500320328141e15220040c00040d0300101610200c2e0740200000c81c1109040011030341c000c0702240d450112814a0082050030103907030707001d8020303510f84541144030802240e41c20358a4400f11841a54000b062800a441c0e50344240010001c40c494000b070030ba404982c0c007280600e80040d00100401c0041c0c460000d10071011020b0803090380b12500041803112000f850100c124240300321902a0085800107680c840c0715000b08140800c1c16889441040403020101e45140208054010103000031014400000c15066541c00c0d1a082440d03120307a044200c0c600540e290440c1c1c860303440424000d45940700c1804000d52564086c0b00d0b001304401c0881c410301c01d0710070001210f10080c15901420800c4c0424849a080b050544100f254041881c800c100f41c506c0000b844680550320400b010110001d80c1003a90700d2135410aca00840c41805c1007143c21480c22201c030300c0c01d40c640055182c0c95100f9070018101900c0340618001210002c4080352034004000d07403000c3e02d0b5102170b45501c0030740000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 443149361 1250 443148111 443148119
    0xb0a0303170c07030c030e0f060d0609060b0c151518060f0604060e010e0d0606060504030501050f0708061306090608011d0102030106080f0414070306140f01050102031e0904020a09 79
    0x101107201d80c0b02d440041c070a85404125640603000f9040003801070308000b40c91403201029192007090b1111490001c01d0641c5078191141c03044050305030f0780110768051f42880400903071910f0304005e039804908003030003420540d4900e1445583c1002c005004151140c200d41f10020f10384c82c0d0715407000030340e0120810314259247c400c0611001c606461000d03805520204001c00c0040d07440a5601c584860900c3c00180b80660300c80004c8042c6100c0034041e180b289011000609560084014411680300c0c4009210640c2e40e10105500341c202190100301091540300020290726002101654581c050200000c50a4a44a0660840e0010b40100415a54031510020009803691440a030800640000c1d49550f0515034000d16600011340044081042c800c0400d0801002c98040e041e014040b0341252001692030034600050328940c52664803040c04480481c4044100480d41c230b060716070680045290000050341900d480075072545240c803425040c0105038503a640c5000411030300c0c0607a66034900050030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 443150611 1250 443149361 443149397
    0xd0c0807030c11060a020d060807060e090c090303030402060a021f2f0f09010903060c0305071b0308040209061c0c0914091f02070b13060e01020a0203120405010b0a0303 74
    0x64220542c0500c03481203081ea03504080024029800002c41d807001d41c032108030440c8840a01107039005080b040c0a64070000c150b0a6101d0301074280040308440ca00115200c0c000006d05900c6015289501900100000b0b0f000d420204024152010944103da0307240801340758990f2031400d0034403020040354031000c10315418103801130f0079800c02c25009880c104d151801d52054001d4032490241380c488900204c0e000590f40c2c041c2c805000215004981032141030301e000c00040040208460358400300e401603031700034001080d4118100c44160700d03071210591505c42e0303000c000d400c900c02800242e01001401640585110000000c51113502c26548401c10714100300c00842078400d160544800b2692a00402c450b203c3c00081c100781800300003007001c030900c000ba10440041c2c4a0303403601902040d5500207000c070720101d803030441b0f05442c0142020042101c580400b81c1c00e03846462000c40050340280130500e50584000602d40e0414801c800010340051700d040072604c0d0701c065038016804a40314580ca04007400c0c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 443151861 1250 443150611 443150621
    0x30f0309091406010e0303160b10030b0108070e16050a140f0f07020909010e0d1101091205070213060b070305030604060f330504030b191a030f010603020a0312050d0c080703 76
    0x4221b01850800b00c0da0360740ca40ca10000050050400c04201d00800c41d69440d002d8048050341d0000d00503811980c60703000032550b8103454410218150f082c8000600800b009000700e40400c0e005940b07140c40c140300cae0581120400740c50b0000340102c400800c1a04022114071008003015100d03c9082501e51030940100a00550014071645640c2d0500f6510704034010003043ca0106403000382810203803c0345440ba828014214007400800c5103417a40ba450914980150161800380e00c00c440580188841001c03a00c04e56006100d1006698010700210340045c0c01800a19441203002c4c00c0010481c1d40c2d02c0404d4040c8940e1351154003a5014104443d8200140145202000300700503448440356490b188010b10b07900c180d10000d01454401400b00c2d54071001400c000548a1003a44140135407905620300c1545146402d01c004d209109030544d03140c04402c10300684017200e8000704400540b40c503685914034003910514408040007030821413900c071000c45215008441c10300350b40f81c081501e4000405070440e8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 443153111 1250 443151861 443151887
    0x50601120e010b0a1e060f11190506160207050d031106041b0f050a090507030f0c050a18050f0103270c050a0e1603020c0f07080d080c03040507030f030909140601 71
    0x814400ca0072603084c10030461004580c6140f408038502c81c407c40c81207802c0007600c0c4031030300b83d0f002e0b07a12044083e51715030700000c0005000c0c40980e1201c0c2c5682c404648481c058905100258100b84d0042290707150039903c6c0940140039060a5003c08804200f403800e081c8115030855502450066054111a00c1c608002c060402001c4c0d07005210708010005800c450a40f0030041c5071521803001445540c4240c220202085d801d98003840749054814018045800520510b0006042c0103000e094484440400c1011202c0150544019000d41001180581415065090654141000c2e100360044220b00110030321f01a03c900c0c1303a50790030f00d01002444100b41e40302c28036080c010b0702440b48031500c0011416501400d401c00594401c1c802449070b06201400880000500640390700080c0f4000200750301d1000e41d51641c81000c02e0380c1c0c0840c6640c5a0006035405011540080414400960b0512041d03c4143c0241071444c00c0075680c06408095070403c040384000c9410309400d10583e5600440c0050140c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 443154361 1250 443153111 443153129
    0x414010c14120402012d0e0a0501080f0717100801060b030108030909060f1305040c0509130303021c061203110c0127091104031703010308030109050601120e010b0a 72
    0x81046581140140100101400b030030402c00081011680621042d070321802000a01c5d42d04004070201d40c003410b4901c454100c1c0480c03080c03100320300c2c24075002d44034101b51601616078944e982c0314070040490303e08006080100340301b190754480500101d00554540300c1c4003907507098481c090406107524290345555005075a41d020034801844402400300a81d1a409400c3d1802c11441d510b160008131041100d101168218101c0d4441c1c61102c0e40940200d4800c0d8080c003200b01915a964040c402d08403400c42d41405c00e07030071000390000000d2085d00140680c014400440a641d46c910810800329043c0b9403008030480354641400040542210041883e4155040501141384140002034007152006080c080202c039507440310a0385100d00f070042005040f00200400200b03900701c802101503841b40c0029110070340740d41426002d02c02640100c9041eaa440054103045920f440444000b80101901203030502c4600980c840080b0000c0c4940900e40980d4030020400321090424400000b0140d0004a09 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 443155611 1250 443154361 443154377
    0x516030c0b0f0313030e09010f05091b0306131b0e01030507031407050a030213060804150504030516020414040302030d0b0603150919020408070f090902010206160908060414010c 78
    0x42c010142500d5122400201c0c00c001240310345001c845034403501c0002075000c40d0000011410414071105030003a00d00179511000203440b40311a070b100d4100c0c488442e92600328100000b03102c50400c07802c0c500c1c1c1d1502050f4041051307a41d2104422605040043c160009281000c2440c000e42e4180034080d004990350a04024075451281101c0342c80358010000b00034010000344891380f6511941c1200d10100003905126006034842600801d00d032070070b0b04d090ba80c545a050403240c3d00400c5214031801158903807680c610f4030050002000f04071140481c141d0b03200c0c0e541d1040e94003504000c6aa28890b40c843d03070295a80f104a94004011682c50040c040d004402c18001c0008030200c80781864844841107034000551750714500344480d84402420200c11041c00486c1c00203240a00048920a86034100c04640a07142c82e00c042e40b08442a505021b030040e4492400308400c00240f0f041d64240680c035180c0105d450340c9607001a4030304401680c040300c22949d06c80f6500b2070240b0a202c0c041d171001d45482e02c0c8030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 443156861 1250 443155611 443155627
    0x3070506070332100902030c0705070518041502040b0c0c0a060219020904050c030a080408101e09020f030307050a02030f06010620010b0d0303050406060b19050708070516030c0b 78
    0x610143c00e000e403a00c0b07241082c0045a4541d40405240c1d0060054900a40d0b40303140c02e0b8280c40854104a904544034031135440085100e01c1e00c1c82c4d02c41c40740136070000c08102c1641c0f55180c220381e0206020464000b00d03400c01000c2541e180c00360007402c264900700006d21b85218107400307110b0b02c91041d501c007000f150050005548204075203008003000d950122030080142d1614200381e810b09690546d655858441c2c0e01c00203042240441c003510407103200500f86c8040906000706203050f210540074400d0400c424401000d40b10744c055000b040120700140078040319a40703401c0460710315444000d0540d02a80b00c03c0160045140401c0910000038140028081e154034041002e8100501185814402c11409151803104542544043c0c003080c0010505054501e0504010b03004000c143c60a441e114140800410090072000489600f0701c4040801c907404905900b00710303043d42052000700d514a20800030b001c042002000781c04012641074140c5c50f1403520314548a403400c210743e404101c0c80e0301d09200200c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 443158111 1250 443156861 443156921
    0x1090e0f06010801080d0e010503090705040507110d17190609021308010605040b012a1e030201050a110a03090f0f1b0e040210110c10031a01031103040f02010908030705060703 77
    0x15031f21042070804913142d4035003d0b10704c0c0c20300c1126044540c005180504100010380c0c45030000203001607040a84107482022107049903c18262080c1502d014074030304c08241d0300700c500c1e80d80012110941c00005201e948808030701060f030340207004680c1091035942c0c06103d40a000e2145038001c04084608001901c406000600b00501c07529450002401c1e94060485100220b842428500d600c00d80280705001e40c2c40c60000c44441004081d0010b610f40300024030341019521940c0d42e90229a02440c1c10001070050450240c10180380c100c0b00d41c0c00d18901000021013440c01d01100d54450032038604030040e003d9030116428050b44c425050003071072105000143c0c031096118400300b50640340000b0144400c8a8180c42d140607125001c1c0c02418007046601c1c06c5905a01001128000302c03003540000e19920011003d070742ca00340c504290180d00f00041000500300d00b1041000600c10704000c5c00749652401a6811034100f442e064400e508a2001c01050380c0d4540f00702c00b071011103038107009030100110040d2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 443159361 1250 443158111 443158127
    0x3020901060e0a0f030524070e04020a0513080102090f10050d02030604020708031e070c080315010c0c0e01060905040e03030402101817070f0308120601090e0f06010801080d 76
    0x41c280800031581582c543c03520588031002d464190000a4815580d20300503554140201c400c00d80c1f45042d40c019020820b46403441809440c459486041004101307040000962140060800f4880104a1045002030301805c09000703103595400141c607582c020b02404003d618a11346144100304804c0390888042e042130607a4030380c6080010050320f940e20240420001c1c80b8180c000380065202004000c1103200e04540181c40d80e448101403440c0c1c0e00c03059025500c940000348020511070081c00006e071b00f401d201c949038862140505d441c0210080c80d4480e810700551940081c4200c0d292100140140341d003040e2404018641a9001c0140b00c945800507600c9000c080c00092240d421010f038a00d00901c10b401007030185156170760101e0169503820490003840c0502810ad0a14000d4603030003d0309034407120b21002102e4011001034588604000044840034004010780c5c14882c0f0b419010030b4040c035200d4114441c01d0004a0783d8200c0c00c00e0000074000303080503403040c2e005034030ec80c1148549a42c81508 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 443160611 1250 443159361 443159369
    0x12030603061602030706140603070603180b06030a0b0c18060306130207020d021f030f02090105031303050d09060203010918030e0d150c200f070308070501200d0e0703020901 76
    0x80802100040c0a0413400c52098000c06080c0d641042101011070f0307a0450344074001d0b0000c400b100d13480c0b544c0b09026020380340c41920100d032070f800134410032011800300000c032540240e00400303503000c1451075511160703210b20646611000308000715181c60301c071150480300444484100c42c8603080d440d01000080303003c040558510507082e004104d01085440b00000384660a9004145c2d0710b1a090441d0942034007101c0c0010070000a041100080540009208641103540c0c103a540301c2c5190b0780d00100080aa84000084081082c2003010309030f010424403800c115039108110151b50381d45008880320680302c0c6601400c2c2414004d110520001e604480202245e620aa0701e660100c40b482c00c0c02c002145100007a40079903800d00344103092050f8080001140c440d40c900080390103035403056103581d0350711a4108541440e8004001400803a03d10707005004c03001d01c0745001103007454101d281940806c6405403002805075021a03602d08600e0140030f0040b050351400010039202e03240d07400145076a08107110b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 443161861 1250 443160611 443160631
    0xf1b080c06161e0c150c020102090a0b03101e03200922060c03020d0f0203041e170708090616021f0210050402042d05060901060c030e03030c010e0303091203060306 72
    0x10580c0100004040c10301c105c0c4000c1c01003040010745907030000e4040c1d404940c00501c41c12007103401103201c0840c1d0040c1c900540c007010b801c0c2c1d0b1080c200004a104007100c000201c01c0307005d001d2000000100f084014081c801001a50020300080d50350601c03000a1000c4e050020701c1950b6881c644024407000100041150880008206912400b0b0190b009104072000c51248500702034142c15019400c2c1c00642c000d51090410211030031a88924000035595008020311544040c1816182c001219001d050014041d40c3e03c1352030202a00d0018034a50700c045003003040404511040c0080d45000e400a0b075000c4040300c10400c0e0080c1d5094000c0d12020940c154072201d036031306d00c04613096480c0c9502040c034019120914007501e070781100036890801d040004948019007070400040046c141200765a0481c0c2c034a44607903129948540d01940c80241c0c05c4d200d180c05200c01e01c0303a07801c80300c0b0902611508401030703400f440c0c0d2803c2100d8520f00b41100001d4050141101300284070a540f40020203680c8614404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 443163111 1250 443161861 443161877
    0x403020f04091b090e0c040207030f05130f0306140c2505031225180e0a0b060f0a0305060303160201050c0111040b04060f030b010f1b080c06161e 64
    0x403400c507403c8112140c4202464060708404684060503074003400e08071180780101d440c0b1002d58020441648204030000300012406040281100c0c00380001d40f907002c19a4621100c456103c0500481900180c3d01c10350b07007251580202a0040b0702d0b1904250030010707010310245810008200150980010106c06110100142d040001d12006205079803181050f41c0185544d401e06120b1841c0b140654100c002c11905043d04035411140101d144141e990300c0c80350600440c0d450b20354a0343c2000340040140305040c1c0c4444006071141d881000502b600d000c4604444c4e12001d600d0701c010110f6200400f80c0f4003950081004804171094100fa85010542c2480d0443c3da940760403007618058020095005140c0d00081004204c2003002c0c800303881525880e0380c541c4420842001c01320700b9589086440b502140720010a02c0c50f0921031195480b2040482050b03440c138607419074a000c800e034031043c4032496a0708404140115104604205409820185001c1c19105049000d060b14158000c440c00c051100748 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 443164361 1250 443163111 443163113
    0x801120809130219090f06030507020c030d0906090b030f040f14030c070302010e03010516080a1d010b04112b090b040b0405061807050d03090807060c02030705060403020f0409 77
    0x208903032940d14003804801c14820481c201034081d4200e03d4410200d21401500003098a2042e0000000c4404006455140618247c0300740c0041c01c1c0684040c0440c0a4000045c9568030100004020000c2643d0b810704c4980c5008402045401c65410800042c102081808000d030740c000d00040c3c0094001c03c02c6101d00c101450b101c541251060512801e6000119403900343d500302140c010120780c002e1721400d08041420003054201c690445480b5000050641c0302545035110352110b45e40000c82560003d160020a901e9030382c0c01c98000080c0303a07503030744403014952242424001e9906500708502d4140c140301d072060000c00c04070501040034180c0d1f440c1d41040d0b41043d03080d4201d0340495800451003100360405042821a003001141c094070315210f00390100d0840c00300c0c0504040c80503200e40181c6102c80c203180c2008403070900a0b0003501040030b4020040b46029007440f00100800755616000e140011620625040851075800380d81724050178002000940c464803a5500c0780f0000f240c0c005002c4440d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 443165467 1106 443164361 443164373
    0x313141b010c0f060c09050a0308030907061716030617010504051209031203130b100306140f010b03101a0a080a200d0608010906020a0305090d080112 66
    0x941070b110303003c6019617120540d8060b891400304070503640d4800182d0030401e5900f0581e8100d00010600524800c10490400103000604011051201c81481c0c1581c50000031700030741001c0d009440108844c1e00c65400300e000780c2084045101494000c040301390081c8421601240c441c0700b980c84545000d0050005d49105980040041010340364a103a080450740004d040740403140d425058042c0094101c403a09482004044012120b0f10b1a500342032040c0c0b821315082c09013140401c0b0074070071001140300b401e80c10748525480301c030350f680c442d04107500030613002c0d034441c600402858050600036003040000780310200482e030b501001526511046002c48450191001c2c0340b00c104809040c00c00d40c0800580820480790f07000081035541c5007041070944c0c0004104a03065503000610003143c642504c40c180d0445001c00c01004d0340b40344404054000e1106004504075002a44605020450 = true := by decide +kernel

theorem cover : BRFrame.Cov 442985611 443165467 := by
  have h0 := BRFrame.cov_init 442985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 442985611 ≤ n) (h2 : n < 443165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
