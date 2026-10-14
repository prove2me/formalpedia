-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0989
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:40:52.935782+00:00
-- url     : https://prove2.me/submissions/b63bd232-8316-443d-a162-4b0539e87778

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 177697841 ≤ n < 177877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 177699091 1250 177697841 177697843
    0x70302030607270302010c030807020309030a05010507031505090402011110020a020706080603060709061803080c1b060f0304030c02130c090302010810060c11041103070c1101090608040f02040b060c 87
    0x101c5402c4038540040d0218108511070f01d0390440450740d040c2d48507480d07400c00d0f48040750740031006407800c0c0440c002000391008641e8100003a00141e80a0000080c0b14100b180010341103500841001451007034000d020040c6a9881d445694015020b00b04560200c180958690508139080010a109440480e090100c0b80d07000a41009031003103a01d500341e03562100401c050742c41030100c5010b40040e041082c240100351068003c45800c0c0400b100301c540141d2a035940d080207820410f0003440550000b0111102254a450725101415080d84c881d40782c4100752030301031341c140300081000e81840500305126046448008240c031042c0d4449108001e4200d0303026000303007107420070710060f40011040004101c2034035290300d0580444041e61180400c1d441d042c0e6449442d490203044540c2c0c0103540320340384100c14401c01e0086102d03e480b907403202080310f174620f04a550112254041070404c20501d005016464010442030303001500421081c000b0602840010094200d018030990000c001041d0b403403000724 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 177700341 1250 177699091 177699107
    0x20f15040302181909110111030d0c0e041503020303121e01030303050604110301080738030703060801050f0f09330f0c030f071206030f060b0301090320070302030607 73
    0x1c009038100328503c0781904030007070305d42c41c2c00080c00400075860001000d40c050081c0790090805d0800ba641003020641d044002c580e8101012800300b00c0d008912070413850140f040242000c142040b21064034196000300303a9034090001e140c401e46900d81c005c82c1c1519a8082d842141282c0305030080400d68491800070f0160200b5598036008070304140b50440d105180e03d041d00d042c0c0c0c00d02001040803d1400b412a420006110f4040e40740b440f8191504400240704071880320a81c2c110721400341d90b401d245000508503150b503440505240d14100910102000403100320740c100c1750710811401c05481d240742c003074202010001c0c5d071a0782543c4840c01a80d0400d40402e184581e83c000c49a05145545100b4842442c0c0703002c480301285903500300300113044401420140703038121910345800030f1840d01090700b403c100d84040c0c005039103d0304d6800c1d4a908000442c041c0ca04000c2058001f40144c28240d5006024141c407541f00050082d00c60f0241e072201c0004002c6d500046800a0032a60b45050008000c3c281c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 177701591 1250 177700341 177700351
    0x212032a04030317090d050a0c0203010203010e01050102060c120703020a11010e070906050409120c03261902090f0f0d0b040b010e01050a0308030601081e070f0206090703020f1504030218 82
    0x55a14000c40020340d513809005119000c034101030304c500740e109282122654890861001400062243d140141c4c030244061406015803070f9981c102941040006403404500030298484550704000c2081d03152254521107070002c5090402585038103034031600f501c452550f18103404040d8039240c25905095000203c1104681082c0410042d003521041800280c450340100a4019a2803082c0440d1081c0b0810400a1043c000e1a21a50150130b000b50348000c3d4002540c1e0105140551007804984010859240030004d0702ca8001c500d0180c10f0b8012851440108400620501c032000681000d500c50040124100e41e000100b041d907440c140c41c044014000a00520903d228420300201d8241090803e000a69401035405070440c0c1d2460b004454803100200f500e580b00c0c0310a030302c1520440c500e003001406103030561a0540c41b03000d0900c00130302d0f00b030b40108410a59400001c0030405600c0307515070742820032410740d01d041500d05c4000110b100c5100e41c0d800250494141032070400b82d1040602594050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 177702841 1250 177701591 177701597
    0xe04110108130c1503020405060a020604030e0604081504050f0f010504060b0319060f0603060f020c0d0807090e040512030118050603010212130609081305030c030703030212032a040303 81
    0x181c031142240c0b0806103800760000d00c6220a40b909000320b9080c11a42c560100b603074070340546045e80ba0008141c1d50341044a0785401b5a2009052204260b008402e9640d441e109032842c034105450125101da07601c04000303c5521850100c4003182c2400810b010a20409808004030b0b400d80825519480c000c003001c403802e550f26880e26240480324603005c259864842c404400b012410761850304c499000308405140e9145c41960b40000100080450054580780c0380c1d48500113860f14107100c1424204003850f14041d0410000004000b03156070082141410b40e254020300400c02da8481c0b600d603103042d01145058550746004400001e40a403030720070150234511038013418170154640c10145802d0b8041d15002c0034140746000e00180d6007407006141e0b2210710340660b0b000318500f48540c07134240719940441e43c082e01c9048420350a00480c1410030070000e09140a400900b030180c41d54600075190a071421b0020324549000003c160716002c50010a001b0058810036a0805049031010501c2e0368041d01c412004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 177704091 1250 177702841 177702857
    0x80703110d030f120f050703020319090b070f02030403020a081f02031b072111011a0603040f0c0b04090501061202130b0a030f060e04020307082b090e041101 69
    0x1403820311240c440003050707040d00c803001142c0441500b61071340a00d80308118031407075942002d004024007078020f0078014a0552001039823410300396000d80c0003202d2507514807205420201c00b600051446410940d0001c02c51404550700024944100e007140301c0c540c00a03501c5240c0d6400070940b80c1c00801c0c11344440280c140c51319170800306801d0100503400200e502c0c1c12500041203000815009000003018800c1c03180118501c0030360b40048052100c0c1d130758000c0da000074502a000d8181c1010034402d0504004c6080321543d0340200000028085100c02400101500b072034280340d004018080207c503000d003c49242131900d5540300c2500e50300030700d024814500020050700900d17155500500c21031b52110741e1040205002c0382080740714bc04541c490032002c0101641c0f40d50480b100c2c502442210050003103d00e0a205600749401007610785407843d007203007060b5000100691850100c41141d081c80c024010745e41c90010001c40029203d408196010305180b82542e030410003000700b05170192050a400744c0b61098 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 177705341 1250 177704091 177704123
    0x1101050d0f050121051207082104020a061b021e030303070201140a050c0313080405190f06031104151b030c02100206060109060e0a090903050403030206070e0a050103051e01080703 79
    0x3500c6a001038050170580004040c3d450004101008104541c01150100e25043d4400c2c0044202d01e6807003400220300b03044000740000c5140c06080580100030525010102402498200c11594100140248148100c01c55150110200712000c5c201c1e0800505582d1030385008030700a4041c000641004024004460010346241e16520031540915020300140f0b0840ea10040c0a4500500144068510b61018840000c4a680d1214100c031240c2d1085000341b00145413528400203101c00d50081c80925044c00820492145080152402c071b0307880c2d41c1105d1030581342410a07920350031412810302203664841652401c0c1500301c0d102d000020710a5440c0b1602c036198650407070304d8040503900e4500003034403d003040103400e1185903480f040c8c40c0014200300c40e141c3e442c0901c9044400c0c0c0e0b2802c5010980204080052640500559a0002c02c40c14140a00c06480c0b00190340ca064a0094506159558010861160700708131184c22205c80c1d408092520758484211641c0c8203014441294a0081106607603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 177706591 1250 177705341 177705389
    0x40e01091503110103051017030714010203090c010f0c0203030d1a040b0906010309053406050408030706050c160c14190e06030a120905010806010e0108041101050d0f0501 75
    0x4000c8a403c0100c00026580b45001140606009042072000949003980469440c2c100401c085c01e440f0b00c2001035544554615282c1030f0702d02c601d803030451640d00c1403041100d00e4101240c0507003042c1003403030120000e503110318094070522418500690135200100d103401b54030030b0590001011140c01401120398021032000c0000742c1d41c100e071243d6046890036010550950281d0020100c0610400030b84803d41e00c043c809005098604c490240d4049003801000c00c50b110721644403000e000799260440c80d1609040ca01540d03441241030040c1429500c6001401d46c0709050281c0c0c102042072980c0d4641a0303001e043c00d01d1481d04034020600002c2d000208815103140c2807031250f0010b4402561400a20714286009040f440001d1001e0b405003e10211100000d43c8500f03409120300c020b488030200a41003200040450038001c0c13078913042c88030040700d0100980e003103280d0355845030b44507000b440b1079203071140103c5680c002c0d80c13150082141031000620660700d1f540c000d0750503500d40707001403850403007251284 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 177707841 1250 177706591 177706631
    0x6150a0207090f0903020706050c010603050f01090201170c09190b0d0b03010b240304020d080f0307140a050712020705030a0f0203010b0603061e010314042a08070618030602040e0109 80
    0x7170240c0d000c00b00402109028101500640c0c105500004981e942e80e12102d0a00da0766882083c601c0e5500c031b580030115a00b05564449001000082c00740d00e01e07040413800a10310501240c9846801401103030340620b03007081d41d100b02400703040d0205d54075088051036280207400d20390016403181d400c1001e403411a090031220341c2900f6041c2d0901c59800e015851017094103a0014009a03045a00d2104860104a644c80182032400b085202d40765030745000c0b40300030075081452102c02d1040c9810800c1e0203186074420309a40c116a0809a40300c000003c5502c01e9142c407a0940c04203406000c0c21415009005074254420601402a00244103c80d1600c0800c0a0381c4001c5035220790240c41407410124002800d03100f0500c091060600150071480103144002802d0b04450842e4002c00c80010359507001103480000d0302e520300d40300e03110b5156030915520b1910b841c03c50103400200580c505a641400f613a5801d400300039034011504654458503850309007d001002d008410005040aa07000451443e082034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 177709091 1250 177707841 177707843
    0x307110c2e230f0f04030b100b04050d080a02160b0406081503190303090b010b07140c01080105011103070c0801050108061f0308071b080309030c04150e06150a0207090f09 75
    0x6003042c003441e0440041c5554005200d1103103904000e0080081190002006001031409140002d00b0f500d090000c402c175a142c16000354414605c203100801140e1075903d4012041648440813644903c0040801c03482c1c0455141c003d00c007030500a000083e0052088028001e0700c0e0a40d442503156941c0c0148200e1440301d041d91150554000c80e440c03100402c40280c000c0790140304e850086483c003004e4550602e007480a030400f171007034417001500604225220300103881c01c000e840003424107007034440d0019014000c14411030741805031004101400750014400c6070080b90344041d001c40c0c01515036001900800d424050442c480c0f042d8404a4214510003950080c590400e840f0102d10b5815540c0d680303021b400180089030f070707001c006451031420702c460b0302c10b407001c0c00300c1000450b207031500001010b02e0b107030181c201680220301c0c00701c0a5040c1d411940c0b01209540c030b0a000400785440307000c0840d01c41c00310954181803655010400200d596804281d40c5c0855808420500c408061041c100c0c046803241c8030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 177710341 1250 177709091 177709127
    0x150e12070b03250203090f010305040b0c030705040803070804140d05060103110a05060a03050901061413090819080f0a0227130908120c0f0307110c2e 66
    0x82048a000110002c42d44400d100d0700c41d894504071441542c241d480300420759400f50b000480c0c182c82c2e03411729488040044100340307030074825070801c0e80300c4140081018200790f050440000000701101d020300125002000c0420459541308400c0c00c04004d039030854054106403080e06503140e921441d100752804c0c0e006400c40c010b0030140e4a140e0b1400401c00e000301550380c010081000025050380c811000d44022005901c0109240c40d1007004142110700c1a000650307101e081c2001030b1141c1e110000c0a00c1c0c0c501c5501030000e2a01a103003040e6166002e00d00d01d0141124000414401d038680c0107541034014140ca000016a949540c612142a0b0003840b003100051464201d00d0b4600340400000d001203c1030140202c00300c4175038604102c0954000060546007034030f000400c9208a60001c072413540c003803046503640d8104004083ca0000c948406400141000055010100c400c141403000d8000c48900070700441e445480100c9038154001c00d10028840c0701c80026402100074015405048208000301d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 177711591 1250 177710341 177710353
    0x301050c030a0e120f070506060301110a18030803010314061308190c021002070e061002030a1d03060a060e090601060f21020d090c060c080301090f0b0a150e12 70
    0x10002d50700420108454030501e10030000d0381543c2264010041c01812613015a5a9458849050041c41d148021b01540e01903850040c118031030707440c0002a1240140b07070b4900440440300c00071401545a045400c05040040c0010001040000c8609282c81c003019a82c10ba640540d50400400d04003400c1440181960300100405c503006040d200201c0d05c06000d5040c5159850526008101c40b91404204940036a00c50031091040d15a50320041c1d0340f280b13003220324200141141038025120f004200c4600148100000c0414515980034100408660302808448191070a180804042c0c5110711940102e04502c0012410554010030203078103a07a60b0f81c442100214445400f00c94000300d0461510303444240e09000700e25001180002c0014501300d2801082561650a10301c1004101d41d1045081c000107102200016800d02c00317880c1115041200000e80f00c100c0e81c9448041c046c03076400503610101d0544040f40226004081c940c0c030300100d9031b40c0c014050190040c0b1140701708801c18150300d54000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 177712841 1250 177711591 177711601
    0xf010b12040305071406060307051f080705040306110304060c0305040f140312010311031c090905041a040c090605030d0509120c0d0f031806080402040c02160f0509060301050c03 78
    0xe098032076046442894100d01d4446a61a40146043c004807503600c1d0307400c540c06002c62454200048805000c040740c40c0ca21450001d08003203805000305000301e0078002c1107000100643d01520070340b4011600084140028100099006d403d980201c80c2150201c1c80d1a89006100d4800e1054501c199400102002400c1e9252500348501c1501e080402140c070080001000002140c41424021840744c1c0041e094548080d08050038806031071480241420300117400b15001d0740c040503d00c12140d8585000840f40c03a2401c0400707000e101c8044140e50400554203200c01c02280b40c3e65a411280040c03002c101194849041540340d900032076030700c0d00280e4144407a01c0345d464907032400c3c090710340a04100c40105da07404002c260540c284220554a1300c0b4004402c20500d6041112008401b00e40e000352003983e802c1c420003500818015102a01403940c85000c0c0b20280d000f088a0000241a6041a01800d588081d101c102c8041409440e001d0000700c030216a26080c14083c0d01d001e28540314010b030443e0b0792 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 177714091 1250 177712841 177712867
    0x90e040201170c1e0903190b0a0c18030b06010305010501020106080a020f060c12040321091401210e0c030a0809011101020d14090f0f030904020703050c071403060f010b 74
    0xd40399810f03a08080106101c060480e03000b01010004003070215031210030a0040605010901c0c40e00d50b0700076680d131f000d50005102600e0035644102003050001e440602d4075800ca40d100d80000b0701c0c0040c0c0b20a00404010b000c4101d11540c4a039000f40e0f81480389a8031100124241d0b01c02c1d1003010380700d50220b059040149011580384240030700103010300b81040721001708103140903400000b454080400240c24000d004a035103600b10f0078604e0b0121580c3c00501190300500c01c05180c80703140740100b001c107500a0207a101e03100e11901d46007503040c3e0340403003981c050842000f0980304082d01003510a001c1084c00721709001c51b05c110201d802854035810700607aa80191100c1d004211944c4a03954200119161840c4078403940213120881c3c08070b00020710300f07905803a181c0320354908124902d41c000c001c0600106000030403190075010581d009621001c0d60300e810394490140181c045620302540401052281c010400c440e0b00c0c620031001c07039125807548902d202c0303104001e02481d680800100099005810 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 177715341 1250 177714091 177714137
    0x10e01050f220c0c1209061d0f130519020403050303010311041404051c0c120302091c0605011805040b060f0109030f080d0c0906050a05070c0905040b0a0e0f0309300607090e040201 79
    0x1c070141c80940c8132020344c4000ad12510000341c00c1003c00d07982e841440011040009420111448600114035040c00e5455070707a941d000520005046074030740e042d01415600da0360400d520000c01211008030030b0820b8608a52201c2c80c1120060f252030101d42c0c1c0810707030351150329010340c015003212101100d12002c0601302c029510403215660030100c82e00300f5050000400030f95184407030041a0000e000c0d4140145009900c0b2100200f043c10740c03c003024070021544035080b65802180803030700003900440b1200142d64841045d40042c014000741c1040c00d003846604401000301030400b503410004d0301c0740580c041d04c001c0018040c0304005807040c40000c4245001c0c000415409000741e02e846180d50784c0d030050200b0b481c402c603000c507400034031003042c080600040d0141d014160b0400014040700000381c0003050303884c0a02d8108912407802d03011980c000e0f10383d0400400810420000c000c044003504074040f0380d00c020644d0303e400000c21005001070802c0b100c080080c0070f154161740d00c0000e080c0040c800c4140c20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 177716591 1250 177715341 177715397
    0xe03030f1801171602010501060e100305060103111803150f070804050102040e19110406020a02040506061e1b0c092a030106020a0209010e01050f220c0c120906 70
    0x180f9009a6a4200340094015118040320007040c1604250040020b080d101c0681c401c00c00c1c8284444d400c1130707a96641c110100450b0481c0340020301f0755550001200a4410180c075400c01c10030005a1091402540c1c0291594640036000ca0303002d04841c12900c0c1c1501c00440741d10b81c4030818940800e1229100341400b94006010300c00150400c0d07101d110b994140b0360280c5886103040c00b049400401401c032801404280c0c02003030015030030705107040006900e807c0b44090080c0300703942d00c50016209507981c0064a54540042d101064070446028201340705030711540c40105440020030008110010001c0c0c00001c0940191403d1100e4803a041080400d01c61140e4502500e405101c456424554100c06540200007a41c010700700301100340180108100e06801044140413000010302039904e400d4106440000141e03170040c2038a074140e50308403c40c03e80c1543e103504141050041441180e10500200c031550045461310b00c1c0840314030050f00c99100c00d104000100f5847c05a20310710f41c82e0400300700c1b00c42c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 177717841 1250 177716591 177716597
    0x2b1b021501033521070207060e04090201031407090611010204150f110d0e18221e06021308010c12021303020306090601061403100515070206070f02010e03030f1801 72
    0x5901401d103c010b250840d074448402510701e14100820104135901d0141c0051650001e03084135410680014049030204d840c0074080d6854445075802c41e440b0b90b00020303c4e841400250180360601d088018a03910652141100184000d880203102945c10b100300c408690601840f4840400b50b514141d071082c0c5544400c0c000c0c08036400c0c0303050401c83c0a202d81c600860031555400c80d00da00c00c108110900c0359842075203514034030301020070134003000c030b03100c1408140302d19100d0b850704001c0e45ca001c04e098a06d04003004e40e60580211444200b0043d500901800c81c0c0300200b2543c0035072258003d500300d40348004c0f0403002075182c41410000d500b080d4010b040700c040008020090030b0312070f004a071918000350398180c000d274800001040480c1c1e00c080303640309143c8103186c0300d441c50400700072400c0c01c403026000c2c1901c900a4903800380b030340c0d0200c00101d0f00a241d002c1c1034141c80390001e003421601440044820707400f04407199111155440d0110071161130030140303240b81e42001c0558070400a040c14400d065414 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 177719091 1250 177717841 177717923
    0x10b1219120908031b0f07030302120c161203030f02031905220503030a0515060703050309070f080a030905010306180b030f0a20060f2b1b02150103 65
    0x3e044800d0004000d03455031a050b6101c60b0911103075140c40c000c04007000c1c0d0103640142c032003840000d50105045044d0900035a240ba00c034101085403030b041ca20f14401c442802051100006801030325084540c40080c0261410401c80602a48000581c4800c43d4008410500341d914014195440e500a40d00031081e5011245280545504646051811242a100c0e41c1c0f0110821060720182d0081c0d50b07203d401c8071840b110f1481d00e4404030714a8064442c004050220110004814080c01c1041500a05400807a0602d1070307078840c4a16164010a01d0540000c1c80303507040400c9950280c001c4c14120341d0b020345034900e848100d43c840e00c0140041481d45600d402001c0c5000150401081058545030144050f00e009003080c04608594200c0d910700d00340544401d0001d1643d110003607007581c040d6a4000b00c0c40e01046a0480811010b00c2d40c0b450310034030b007443c3c2413580c50702846038264000440f805400312504543c2d400c1c8840c000750000d00c001000300028110303121f016200504105025283d030b12001407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 177720341 1250 177719091 177719099
    0x510030204020a0c0b09010b090112050a0611040905071106070309030309020310060e15030607031805070303030515150703051c050a02120105090f040210021905010b12191209 77
    0x680c0c3c080b0b858000000e0640c500c00d82070104002001e6004810700008110070800131002c5400110140b04a0340d110100e0142c07a03087c801c050050301e583d240e024404000302020412081c007981c05ca0f004100815103410f0010780e09600880b0109000c0500c00c00074001d039507402c007040b4050b11141e0400c1b0201a01eaa48000c0162002c02c0010b841100010021410b0740c2031201c54000020000d00d45075282d10035030441d004a4802282e101c0d003040e141d281c08141a0400d0800c0441e007030b4410002080c40c41507250000030f06906503c0320303000c1c184110400c0403882001c0d003000800300c074008001c2c581d04410008040000d00070fa004001410710031542c140522800e010b0201203130703030444107052507036000a564580a1101c20b8640c0c0949400c81e110001410f242032102c1440e80010402405035605010030503400d802041205004804000071240181c4030303103001d501815070400391070f001d0302483c036000e40c2c0c203100403903002d00000900c0c5070344441c0d0300b19807034690441d032480b1201818401c40d640041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 177721591 1250 177720341 177720349
    0x90a0e01150510080c070b10050d1208160203041203030b13061409040305161401020c07091a0102060703050a0609060308030619081009140601080f060618070305100302 74
    0x9041d04a465450031486203054240704a81c114024000200800c410801600d04e83c01000d40d82d616420001810303055488d40c0020072003034816081f8682c400e8a0844a4007004103002e2601b4064410741c5e0350040c2929040900342c0751410741c801c00d0002d60401d010034008141c41000c00f407460350203894046558000071002c22618141580c58241194440d07009109589901040b50480c14042e20624010700d002d40300104140104520801c0c0503c0c080004807e008014144000e021070a4008550302d2040d909001c0d030f120042d00c42c4400450418500c0381010020202c2d1302414401a009043c00380c0d50124203c000f070900070140e81d90142d941c1000715094146120301e10296215503030190b540d080010400080100010100c0110504c4035414440d001c0c000c1580080d1044201c0b020030300d90403030315142e01e1125400503410141d20403500000ba01d20b100240c00346800201e90150341d4503480300402e1000c0c8010070901c10b9401400c0c1000b04104512a0340407a600840b0030b070900c50059107c2d0f00013 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 177722841 1250 177721591 177721601
    0x121406070e06090d0f1a0f0c0702010315030c0605040305071d062b0b0403122c01090f0c03031e05180105070501051005030d090305120307050403050106030c0e0c070b06090a0e01 78
    0x391101e822542e0181c9140c085d8003030203070700710444100c601f80c82d240400b900da400d4803d00c50024100354a440f401c140aa4560303001c2400341d544044032918154a0b98030082203a00f1901c07017640c45204d84a00090b4003d40b402c00380c0c003040600c0f080c0c03d040d82e4840341400002c911441904007941c81d04458010014040c400c95800c40b44916003641c1e0605090600600e804508004001c0c000d28020301103a984502820560342c020040d07070007041b403a43c03520360940103000307803040a020f07413142c2000a400c0100c80c5105da41964032a4035400300c0c4c070502c0e451510003a0075402d030070008128104003014801010b00380b42030042c10140350103860035140355165401d54006440070800c1c130004203418480c80c5001d0060380050181807410001c1e0f1032a545820303903190030124110340321150002c086880b442c4280c00725030140d5007141c02440446c0c1e0324544914008281c2c810661600300e1306000ca8110701201044880f0250804016540b03038856108000765008041d040101140e940d4421107141007080c010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 177724091 1250 177722841 177722843
    0x303150a0f061d0907020a12050d020c03041e18020304111003060302010e060c0304030b09070305031b010506010c0503030708150d06060e0105090c040614090406121406070e06090d0f 80
    0x6a0522040a007001c012010f400c642200d1090301c0360000c20800c03030350000c2c0c100701241d04003103441000664407006440034823407a0100c00d600e82c000554500c55034000070003441107c010000380314090283d601030700c1a4020f2401030002e4040081144c8041c800290061500709000c0c08600108042810000300d40340203041c078900111b520303140b04009540e0003090b084582807050310620700e80344840c1012600d038450760000802d2002101701080000c1000c10000000d50780c4038044a694032158010032400480c090744014030b640c203240000350306520840b122088164803000071811910303214007e40c3c0010002704030142e2070340c0c140b2200d50350b030381c2e4619004076150242500051890400015514061050704010300940b004e40c103104c045600303042204c0c2199002d16280e1090001603440110700e2240d011410361050422001196040742c000300c183d42503104030003001d404c000c01118652204002c50301c4902154500d0310489031410001d00500302081d0040c862001124155140141002d00840c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 177725341 1250 177724091 177724097
    0x150e01080105010f03061a0405150f0901061b050f1501090c0311040b180405150a120803130305040b04031103011b0801060507080d1103040212031e07062a0f030506030303150a0f06 79
    0xc0341e0160304240200c11084bd600391040f4110398101540500040c0b101c1070110359000828201505100082c0001c1040440c0e0f401a219015503a08000810000a00445d289186884001c0e2261070084c491790341030050380610130381014030707124254555812280b08694189108000d024030741d039403440f0b030701e2099084506030840c81180307000384511168550031100344c8102c8510004003168000003900e512510081446001003042d1070100d40d58025903100c580e40420204020080103812160440000c0c1c2c01d070020440071a002d009144100204e014000105000c3c500501529120b100206001800b0388203880c40c02402201400413203120000e44040341d0740100505c0210f19120102000000d2910015801c02038203403803003c1c2391001500384840b0103e0010b0704108015668008003800756498030b000b025150141c0000d25102c81e802030480000d0b00850081d02c52902900c140c0c0c3c0204005001542160703a58481880d501d118150100d6100402481c001264018089850b0140407559 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 177726591 1250 177725341 177725371
    0xb090f06010323070f0b0306030a0813061412010e070e0d1101020c01080c0301120f060c0206090d0c050c040b06070c0b090906040c020604030e01030f150e01080105010f03061a0405 79
    0x44901d0f410b02c1030302c1c9164901901302c0740c2d081002c0700361840d400050319400c1000c0380d42d984074900041d10b400240c56005000314808038410327240700c0e0700040900c04c5400c16114142c0c01d00e2081b4599113244a8000c1c3c150410414200500c10314042a0a250340041182010141b1a422000240d01d50828110403101440d00d059401703019641071244c6243d0038802e082122080c00c060f8440b0110780814051081d0f42420038820f0f506102d0240040c014080d04000c0070071154555007070003500c0780001c40b005900343c847e10060004140c03240c0d004101e095000f4026022046103601080081d00722600c5c442e03402401840120003040c00707496080e004000151090b50344409010900c200901c00030807a921a500d002107030b10701c060300030408a5000d030313142c901880045500c2d401a0300520303c0240604019107010b8181580d05100d00042c420341d54203280b20741c0e00703a0303039801c1c0b450980f0030900170a05000491075080001400d15040301c030844000502841c212480c031804074084a0044030340d00444e08041d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 177727841 1250 177726591 177726623
    0x10504060b03030403030219112d060f0d09051212010f0f03080a0c06060b0415030b04051003080c1f06031104050412050c1006060f021c09030b090f060103 68
    0x98411000306040c2500511306040c82c0d506c0c00382d207d56566101ca84001d0040511808000c141207440030410740050030042e0401814407103991103000020b41d030840c5404229030011034548441620018001e501d40343d4506134410a40702c028281c000d40864040c0f0510840036034994111014000d00c41c0654905d980315031510192401c44002544001c2c429401100c0c148007196409080340c40d00c0d982405e00821b20005442e002000f071040ea44008100c58010401041c140d000036100300036807c00e0341d402e01c070309030404041104a400030345082c15243e13924941000068100401781c0300f2008100e0958000070000300d240000c016400903420742d80f940d41c4a042c030401103040c4a10180020607101046640380c56a59050310250b500940428000e0104400305441d40c00c111414604030750141c24091503030b44000250210407540d01c1c04001d4010b4180c050403000c4809207031a40c21a440d070711012040d2968580c0d41c09054050854030031805580c88204500c202000490300031442003400340f45601603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 177729091 1250 177727841 177727853
    0x170f072a050f0a0806090a05150c0d0b01050d15050310052203050d0203010807060906030917180a030b0703060b070f0602030a0603020d030c03090b0c0705040f061a09040b04020304050d030504020102010e0708010504 94
    0xd96402501001d0140b01401282b1100c1001c0d510102c001c400c000400c11404401a0780c18041e42c0441c181140c2004440b0b20081103059051040350400d03021240b4001c0c00002d280240c8808603040522040c42a854200703d40b056002440307001d009040440c81c1102010044007643d0090b000001c10754000042040041d501c4500c0400809041c5401c2201c40a01e40d00c003160302242e480f450b03254400215019a2001c4500c240c0c51011400800b070030301895603480e140315507000841d040c001080c9032410020300c191160007203690380d66002104170f4030761295644c1c240013034102030b000b40000c0d40d0f07424003c0010703201c11004040150007522070a19945407441c0c0100031070035640291030b01030b01c24080096402d43c009640030944004841c04904d1800080e13200c00106040d5204400c1e41c05449419260301c18120010004204140d0382841560640000d02c03042e441705440081090340085141c2408900c658000c40e000b42c414400460000f40c0c4215040c503111044d0028a010395451042c0020080303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 177730341 1250 177729091 177729103
    0x301080706081e0612010f1b05040609030602071b0b0702040506040c0c02060c2103180615040b0d0c06030c120506010c080304170f072a050f0a0806090a05 68
    0x35281c600b40d100b502d04400c10719800851058015040b030003060214000c1da4403044e070b05c140f44004030001c120340c452002695000d01407400c07070340345800d034080c2d44001241e100d9401c44040d03409540345c1d2a034091960740c1d40d00c020350100005540c0454801c451500850004100c00e00034034030510300c552264801e0042004640001c0c14940c4218944246000c02c1a08110810342081c0c044407050303100c0b80b00404140c1003040500c50045110031413031000c2c501400315006140500302408420714032100b0714030303680d80c2d9820913100e41d13200c00e01419030000e01b440c0c00d170401c0c3c006aa010700804941030095031050014002c03904490042510342030030102007a404600c0064840040105003c50b09010b0000b034140360200002401200c0000002424001b2181c503869501d0452007605a843e0200034103200c55411a1030119010062200c10070801c64032080114412710300c1e010380103103852411003040046001d0f115201d820070348280b400103040740e050016a200f00035003009045103440d58601141004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 177731591 1250 177730341 177730349
    0x1b0f0408060a0b03060c090d02030102131d04030e060d020d0f0501090b060301150e280509010b09030d050a0e092505030c0708130e07020114011403031e0403021503010807 75
    0x940f0b007903031202c880d560015015820441c0e80340119920418200807500c40140610043c4d003541c000102940880760684c00f8004441d1400c1d0030f04005480458440f800007010b032400350005820450040b0103207414801403154454100c00149019102d40311503090310500010100300036602c030010481d00259009003801103c003142d00d81d207191f040a6103150b10110350384040b01042030001c8828180d80310044c0311000100341801c4018107805450101824503258000c15026000f02400000c00001c5613095810298000b0050101c401e1818000c69a0340c11440c100d500f0088980c1c424541500c1da910828060080744c3c000404008510080c0915a0091410303501000030401c208505009a030091780c00481d03110403603641d18605c1d10740d0040c00c0b0b1174542180b02001001e2042c000482e40541c0260820940130b90070321516a07a5002e418001c80444005076003607041004803609405c6406080f801032411500d950741443c0e20703600454008440c2e0b1010740e4103090000b0041c04070b000e080140358014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 177732841 1250 177731591 177731611
    0x18070207080601171011040b0f0702030d0c051b030115080102030402030106060e06030f04050309150a180605040527190b090705040905060f030132060a06081b0f040806 74
    0x3c602c4600b06517500d001c92480c1c1e0244d540d8521100d505900d074481203600914036180415242c08400701c00c02650707070000380e089120340706104055803024020200300b000340e600300c1c010b4011810348500c2d041c0c0325141128550352556848500e06c00344d140d40354041d0080c1407504001610b900d003610500d42111a641c0044051141803100414a0b59942040b2540082e0300b0100c41e009031100d18000d8654041c46103400e500c1400030b0380340c5211204c450060b1034000c2c0c05075202c800301c403000704140c003403802c10340210400074400f0403050000d0304000c01c0c0360070000e20321418084085840d0b440380c40114002d49404280d00c4641005208a0403075019411424604460107002d9051400f0090010b100300d106107000c00d074681c0009805503640c0700711040300c40e40180c002d001c03d448840401c00001100d007885420510101001c03100b0a01c0015640c5c401d89024000302c2c0711b40e0601c0d20a44942100a2200314040a4002c141000003070090240c03140c070386d00c070003416100c070305100840d41021070040c005680 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 177734091 1250 177732841 177732869
    0x106030b0f0903030c0d020408060c0a0e0d03051905090a0807060908070501080a0902030a05060408031905012312030418060504090c0302040b030304050409080703030e03070309090b18070207080601 87
    0x20700300001c000c50744c0003640650086c0c0d443c04c2d104e90f814003034001c03a4000034407030150000300020760403482c0060030340e0b01d0550b441c0408203840704200152108480000390009406101a15038034510450380b050342c101c3d500b03003181004070503400101034030256004005503800840b001c10441e5084a11000a42081c201406030341c2c0c14200000c12911006020714400b41c0ca480e40c0f2810340d01c060100c440c50907041400d9032214509410030070b0342c1c0e50007614038801c141c5554208a094184a100312410b0305e208842654048114582c83c0300c0801803008401d6104400c11150008010200014401070180f01803404007581d5180060040f0303070581d80302a000b5424401d130540003c118050720310940e44d04440004480d010440401e00d507010b50340181360080d00d480700c100188010300000d000c42c18072a56050005401000b200c030b403607000e0003100402143c0841e0b014071041140d508138502600001c2d1076560301c60000c0002c220310603405da5250000d81c000540a014944091001fa8090408a540700d18 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 177735341 1250 177734091 177734101
    0x30b010c0302150a02070615060207120503090918060a05040209070e030a0201031a0a06020a0501050903070c0e070201020f0f030703050c0306030a1103070909120909050c19031b020106030b0f 84
    0x1480d03040c1441d126100440f450300088000800b903041d00c40864100c1010405a0001441d524140070180958000751285050000e5400516100c0303a010035449070185040c00101810300468070400381078607e010318010400c084180081119a121700611400846c1c94101401400001c2001621450800c40c50380401d052544001682c45149a17080c6400254170070400d040c5458407015000d916400031458800103105940064400d1200f8040d00c0200031f203440d51000c460b5a4440c03204018084402c14104011041250070280e501030790900015180c01ea08071100031860348201d21617408030314080240071039607078503225241e804150101107070b2031810850f0003c1d549402c0c0003401042661816600b0204da213003801020001c0010100c00d1107004020316044100207038030f00c65040001e03200075000448094038060342d4050b5100402440c648804030101e810580980d0742202c0c01e150f141c3d03207480c199a0303803007074001d010001e1940000f4030581549840400860058100481c5c0650702d41480 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 177736591 1250 177735341 177735343
    0x10606080106080907051c02090c04060e01051e1317070b030c070606120807150b06040e070e0a0b031803030c04060807020f0a030203120105180109050a1d0c01030b010c0302 76
    0x107041d10098100380c9029070f540c0c0309091030140c66170801e54120700c02c0705a003c003511850400d900d01c81e100b01c078000d200f5a901038881c61203000b60301c1000c0c000359001c1103619465000302d006040340c082144043c04000860602c02e5030136070099244d0440003a28050070071003040d01140c40b00c410035803007000e800b180789003030190f9440d400080c107a24503211000403540c00700086540311000504000050603083c0d1041d00b402d038003582003100141d41e02004045515140c0140b8414a4040c00d4020611810303d41070010b28440d030301c0d0040c20300c4103000101080e08c0c016619010440b00034039a070104650340b45042c110800200e100f002a0030250b40c418020b004401c51184196416203046180000e015501c400089140041c140003c2d0724600541c0040300c00c0c0755000c4011708003510654650000327070340d940007440301c0f14102221a60340620018014062110641c0196030000a81040403031071166094012242018078542201c986c1d03c840b880d004c070382d40c00d40030f52001c40d80d090801842400d50f5860207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 177737841 1250 177736591 177736607
    0x18020c060408090d1a0604050f0906010303031509020304061505030a020604030f0302190b04110d021e150412020405060616082b0b03060c0426100504150e010606 71
    0x34020381c2e000c100c410554039070702680b4003441d800241e0414003000c5040c0e5801c0821095130098002d07401c0000281015510b46002e0f4081c0c0b50460040c80c4580c0703141c500700d008000c0c48100841e05d4000714000204080c05000bd58000e038080d210000703821044800600d10210300d40d0200713011b500aa8184400750751030905490440b500144141104881480e080307050141048821721900c401141c00810f2051000d40d0130b1117584140052030761070951904021111303810740390007907102030140d14020104008100c00c8201390006011211000010500051150480c1c0c0002000c0d03103405101c1c4041d4030b4075001e510b402c0842929814a00200040030700e00c3c06140546c0685030b108006800301040b058440e041e01401404d030302c10004242426000c0001d010810a00e5119204d180040341d00c2e4040e00313040b103045074508032a10f03e20349142142000d0f00c415420030b0749001d00030009207680300005d5015944c41188a81d0b03070040411080100c0344115440c80c85c16200f160703d850820b200240e0030040e1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 177739091 1250 177737841 177737843
    0x5090d0203040308070c21050d0806130e1617060c0f0f03070e1504060806090708150117010b1b0c0d02010c150c020f012301031112010204080718020c0604 68
    0x2110317075500c105042203212206036600005403012000b0541c4440c46505010815007880350702038540c0c0410803003003210f0450040e6942540000079018124240303007660b00c05810101c0301e4007680c2c40b10b00d5211100e400708205501140c1d44038940322486c64032520038800241e08c401c0181e040d6041c020340c030b00d010120b4061445552110320000010480460007032500e007140c203600500318000103180b03038050001900144901404507010a0100b0007034500940c489108104641d141740300303555400400650003101c00038a9040c4006070703020100c0100c803140d026000e445011041c5940380300c804001c10f2002c202002888198000350b11a05007981c80300c81c4940c8541d02441c0c45601d8010b2400e00da01d07801d6000f0018051240b804038503000301500803c01152107064034000704070311158809182c0d0011500940444c0201d440c40050002920b00c4018289400014204e9016408184051402c99101d904801525070200f60304000d146604131194540c1562290306504186004032403550f10200500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 177740341 1250 177739091 177739103
    0xa030c0302042d0605090a020a0e0415030b0405030702030c01090e0412200105070e1503061201090c030606030209100b0307080601031b1218050303040308091c110105090d02030403 79
    0x452003410300005114118600d0784031103d03d00c05080704400040c0300512402c2d0144100c100001d217505824401d442031844162145d1180750b03d4442080300178207a42d03076440002c444010003c404900421a441c2c4504c0c070070001107070340b441d10340101031070900e08040e03850400100a9052200e054400900340d042540031000d00c59040007020180c80312048152595901c1041202c5181011015001103000f4005030700d5180d02c000e4044140f290700e144200359082600b00400102d0080c1c10175a0300b443c451503284000007203961040e40e48445030001070780156040b54a65a0900940ca868141e0701e800949804000c0c0e50285030012400041c0002400310f41402441380004105900030b40009641c0315414070700e40d02c1c074500200b000c0c240420380b1510100d010301d01980741c040214600d544540300b82c0c001c0003e5048d9951a9411540c0c8040101a42c410b03014402c504a9181a000e400300007100160305c03145d0070400900d58050071504002c006070404c0d400303c08040c415035000701c03c1301d041e00c2d0000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 177741591 1250 177740341 177740351
    0x6120602030f15030a1e021c030905040b0d030e0a1205070905090303040c15090509100905060609030a021302130609090507020a0201080601141b1f060303080703020d0905010f0c0e0a030c030204 85
    0xd41e1b100840006048042d4204a40c15034160030604650140d2458030b1281c3c80e84c501c05510344090004480900300d4098000c544000744002180c0a10202d02600800606500c0c1040e11031411001500c030394541150030382d119174000c1c00000c0c51030151740c1e48124900015800c45c41c1549940d40010003502c2034090719021282c003411401d100b010b040000c0d18028286100509251103144011511441040c034564034201c0032a90618140e811151803c00040040038101a075408000804011601c46a0050b500700284100400248031450003448a41c90328002c01e881c110340304040e2400140498110b400c0b100c03070000140e0b0890201c80e0131010070f1801c3d980302b001f07802c400750240c890301d007980c282c4c2e141140c0c40c10010600056000480510a602c0383c82c0c1c040b180d22200180d882601000b40459401c0740081d282920036409080268a020303000700d00c1d09034540310070307003110140300e030107a01c00740c40d11031440c00c3d150401b10308070408109440b0016800c1c6191036401c940d0600b400000d00c078035116 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 177742841 1250 177741591 177741623
    0x6050607051c390b39030f060a030f050115050607120305070e03190c05010906020619140405010504020916050d0207020103021306020303070305070509031903020106120602030f15030a 81
    0x1c025050a4660010103400c0f28186007070a03000c80c44400391546540e40c200040915175014414489200703413100140c107400c0da122002010680c000050559402006051001002c1003000800e0395006e40900000605120a0420010040b0043d04001d00600040000c9070020781c80800c03c407071502c03a5140008494807106001c0301c000520403500c2d0307070510a0345000c601e81d040c0985468021403042103c07010981da00c1c0c0054800504900c10740002d60404400078031000001010f04d035454103103d5000441d501111050415040180c40940f02603564504000c1141843c21819820030064541d00c0002c0320320301d400038064403e000b11302500a070042141d000316400b0380c05a0346900000c0d0601000c1c0c64403460000d41d203400485001c40001c0c10a004104401c2c05402180e0085401401400308944401c030071a171032000c0100300310219981c0e040000348418a8000354042c0300e04c00c81d4056039904002c000f9403c0e800c4040c003500042d002d003040ea0882c81d50b0003c1c60510b02030340000d100c0706900718 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 177744091 1250 177742841 177742937
    0x20c21330619030c1d04050a0b040f0605010303170a0213030f060605060a0c12090e070f14030a06060216060e010c06060e04030302030603011409190606050607051c 72
    0x2c65410018800c0b0403540220030090030100940544d03182145281000380c0e041948081c20800740c0300078103142c1040002d40b020030f4000780c200c1d500500036a11001c40880300d55408046903400d900c142c0000b4100420340f03c10200700700140c3d400030b5881d2029418811010702d1085031107050301c00280b18204010080d000c000701d5400480c02050000d21b0b0075110340c0044000741490321550001c513401c00304800000b1a0303d0203241c0e0038060b151490080d41c055640d2480650314241003001d28814001030f80c203490308158001004501c01e010042003c1200c0380b42400183c40d2248000744140b10010800003840b01075407203484140700200910300384880c5071180c10488002c1a168101c00c1e00c50401808000c03c1c5074064005601034202078000b08059510140e6032a140352090b0740360031090f000a080103606008500300300b02140d005100000b207881d654000116a540000340440e100d400220920845c0307225810380b103440c40315a0038501c00e03038039022180001c1e07015288030a65181c0447d041c05e4421081e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 177745341 1250 177744091 177744109
    0xa06030b03100f09020a09090503190e04060603060501020c060f0a05030402120604030c0b010806070f080606040e010e0f071419050c1b0307060c0201120507020c213306 74
    0xc0c0d142d904004050101c21910090700107604141d000c5c0b911154009007801c1c13a40b05542d0b02c00e412402460500460340d5a4a54100c4c2682c03140c030030040c140401901d547e03950311507040240794a07240025018508000a400d1008907102a48074500c1404240503442403803003110000811461700703658079a5144005000390902d00c0b1405503a1159030300308001c140c2c0103441002a0f0340142d403a40c0650781d861518039034480049441c207001a90044803120001e025006041e00000000c0909003469211070600380000d1090303001c5001421020240800d05010f43d0010340c11044e1850124100d12101d0300030307901c1e4420000322004101a0350078540481c3d10070015650707c01182c4065030440c42c806510b01074031360318880c2418031900504100141d40c034000c80007900710320340c1072310360784100b0f07038041400c0000f440c00500e10350560086038202c82c441c0d9242d83c0d01c0106c2c02600d0350079440f05880307400000c0c80c140d071640300c1c3c02e1083c0c10802d141040404107007808405500781c5086601039601c3c2000b080a0751 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 177746591 1250 177745341 177745363
    0x5040203070807030b01060306170a240e060402040e150c07021815011205091504050102040b03090a0c05010806091303090801060b040518010509061009081608010506010804020a06030b03 82
    0xc00f40348804010849036150b5103040329082d640038000e803a1159a8503018104294100b200ca500407807410b400a01c12261000361088144101684040c00b141c581d41594007421401605401041c10001140f500b4442c080040380704000500140b902c4000c00440312002414600d5584404a1508210740e5000c0c900c044a02018011264909101111000ca05c000c0d010b814003141d204d80343d00030600c00d81c1c0724035442200400010402000c1400d0fa580d05404d018105441c655002c0102113900602100118040c0403800c0091002a04600381800c604505422003410031210a0920038640d844022044d0005000300c040c0207a91490300d800d072500152940007418079400c086000403100850009001190350076500c200e200e11000d110301d49490401d005040d1301080d20000300700c03103091201416154203500c1c1011030746907490364801480c1070b131240340030040d0045031030040c41044420f00865800c15420f027001d500b942490ba00244444032580902010950b540d003004035927a8003002004550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 177747841 1250 177746591 177746593
    0x30611040521012a23160303060812031b07050307061805061026190f06020f180301020717090a0308130806180a02100504091a100c0209040204050402030708 69
    0x1442868000500720a040380358008507001c51084000c22003007004045c8409130005100e40741040c07000100640e000c1644040e0704142e0343c1c3c0d501040049003086080c1b00203003440f11035512442c0c0441114180041011584205a418031041002a50000a481701954400c201040c04a8030215262201c24180005440c40c4108000d00c9100c15108801c0300c16141a0070140600c044400002c840c03400056403038203080c0e404401c400140062030007170148014440d03035400d0600310141d202c0314241d03004403503004568440040e0b5204a80c00e0300c8440c40001d40c0c160000c3d0309007071441d2a6031080c031401c0c0301d0301502c2c01c1000030300444607683c9807001c50141d80c1c0400107070348811400520140310911805424450b20800740407444403a0303040d50310b103407640c030307140c001c10600c01c080d401d2001c0c0c044000400414810140800705030241a07008030581040183c901031404c100c84410040200c502d28410030910050560520158840104140d84075405403008180741c0c071079102180c50408650302808603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 177749091 1250 177747841 177747881
    0x201140d05190b041514060417060709091a090916030f110102010b033a0c0507150e0f0a090507050a0207050105090d030e032503061104052101 63
    0x209035541d258181c918a0040080184000c1031004031005100d0b412200c43d484a03080146c0200d24842001c2c10700e0203403941c1c0c209555403c0c20300520041c43c55020040d080760040080c080d600c01d400300000c2c41c4200003801680b00070716880c4428240868400d0040d80040006002c081040020220004501d881e0100e5543c0e00d042c4400101880e078000c0360210b8210600002541c81401092000500240984643c00201c0c041c1180e103c500814001715151a45030709082c2e88004202004541058a0b41300c0c041841c0c0c50f002e03040203946d42101e100d01500c1800342203020351280e84055040410b032019101300904400291180c1111350001c4d00243c104030800c0240350703110f0060100500f1507022518100d0310341c0010740f21401054446608a800300c2c2a07100404d1041249030910340c0b02400740c1c0e1954a40512281c2d0041101c0c0e681310103801400e00400400166100e907140f01117500707203003500741810031001521842100110032044420450701c040c41110030f6208040a00283c254050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 177750341 1250 177749091 177749101
    0x315030b0c130e060906060a0306080607051c060b0313051002070311070e040503180f030d031d210f040f0f050f120a0b2707090b0a120201140d05 64
    0x905940710303010881c01880d1801d80042c03000036183c40d090041e03a00405c3c5a059a54030000d0000642201c24800c0c2011f03140c20b80024601014001d0a0180482c1c1d03070741a58a00031540da0024486400c1020300c032040c90b04208011160ba044240c13900a0102c2061500804560170b2444c035021620003ca4404e610000340300d42019084807020300340c984440c1c180c801d41e541e00c1c0c46900c8a10300842c0c005c1c02030380080009020400c406013240c1c420b072100821200d0b49421810110389880f1a01d2a00360202c0c0d5564510402d80816000c10604610381100400358000c17480228141c0c0c0d8465003600c1030705034001c1010840c040341d0005940140c800701082c00c0c551651400d00d03203403240c2c441c410540600a100c011014904040c0c10602408160304010041c5170915525000382c82401018101c450f58030f102d00410a0496150301d8007500080c0d40204081e43c1007049010444801001e69482005000d200300042c844503852003040700d8090900c150004007015111400384540b032028103401c0e2510b0f003081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 177751591 1250 177750341 177750361
    0x411151e0901030c05030912030402060f0d0e0708010603020d020402030919030201060306270b040c0801090308091203011d060301091a04030201110f1c18030f08130b06010315030b 79
    0x410700396802da0b0140080d502c280c0c000d41e840e1105458440d13454012103115000007807414001c0d9003040c40900242c0c40c00003042c444a1894100111741c8040f00d84800c0c41a15015003089840c001d484c0b01002000a24075541c0001e103030b8404010000e02554012002524405040c45443c50016076181110403a640c00e00d0003c0c000d00300c6010071501c45240c214039014500510702030240700900d02c0c0145400702c0444d1a100320307412000300300b2195282c1088000c1140f00742800f0300c0d001544a0b440d00111402d004c0c500b141801d0f00c10003408900c5806000410503520f0100d01c4000101e420b600d401c0392911100d001c2400343c000a00041c007050184401c4e00c0342d04010000c0c0c035100300d000b40d000b0002d0121404014905100303003240f40070401c00c280320241c070800c04203100e072317100c0070301038200003240915003c1104205459000030b402085009417210042500210116404103a8008403040703010241d4501e103988001030310041c10550340e00816124240116103141c06142c000441d119545007001c580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 177752841 1250 177751591 177751597
    0x703050307030909140a0e01110f0408010506030c062205090c120f010b0d0c020304050a1205070611060a09320d020a0209040201030b1c0f03030e03030411151e 70
    0x4030b001034418100055003140a04c0341c1c0c0a5500d0740f1074040301da52207017020749000e05900d41c400d024556850f0207107170b00e603074540c0004c280b220000000c50b6213940c40c016009085a000a010600a8202d00d140312210b50700d0701d04030782e800c2d5503031a4212280c800c1d142e1405111016908071035000a21141407143c0b0421400192241280c04244c01c42903680b01005400f44100a106605c15a001032101c0716500c182c030307007202c211a20244126800c2590341c10029660f10703903c1c0d200c541d000300440d024109101050203001c01130300550070f104180761740c10050240c0d40c02004120b108490b030350b10801010455140c40280c02d803440d40b0045004507581d1001503514403034449505c0094450510000a950300200d00c090030103400816200c0a65110340040d80581309940403541e01c602c025070420228241354001c0440240581445c44a614240c5000f030121025116051581d80c0144204000902a880d54824002c01a500100960051b060420481c00f4440340030805039040548040c1000c0400c0c06 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 177754091 1250 177752841 177752843
    0x306300102190c03020d0f020f01062c07080609040819092c180a0c0e06031207211206080c1f051b0705060705030720010e010c0c080703050307 63
    0x80c040c01e00c10402c0042d00c00c03903c4410700401580080c5040300d103050041300326550411050060341c019054040600d802c590702504a100f9610f2900700000068203c401030a1354102d8505205803d410300c4040503000c0c5000500c52440340020740005810032411909458458000840c170540791a1000000f40c1a0205c41c0100c0c50b403d00e11054144201e02c0c201e03d072002c4a0801081c40500342c40310707000034148900115170b0440d648261841000000c100c490300e0301c02082e19007001702107405d19000301420b20002049400c0b82e42c005200810100d002e01c100bc0d207a4841885280300b001c4c10041059a0480d150a04240300740e10342030000840980c0803c1501e40140225203d00400350080f20302100501141e01100c0050414040091401814800c044103204160204c58085544200103030061384070101c215103e0300042008001c00502603070388054488480d00c411758040301100004c01000a070b60400b81008002d5142c40280910640e60501400700399042d03442e060b41300d044c0075503a1b0344800c034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 177755341 1250 177754091 177754117
    0x1090506040c02010605060714150405031e280c02090108030702030c030a03090e0903090303041d0a110a0f0c05010f06170703020102060114040f0c0206010510020309060306300102 79
    0xa009402c1ca48180f16860a40302d000b4101c5087c840c058403104101008400340d0440c911403200240814008603070228810b40c4103400641d41e0303807a1300401c0030840070304001c0c407030f540c0c0c00074403095144003410090850303000f031241009120108444d2040360102805940a50000e42290021655400100007069698000e0f07049130300b1050544103050740c1e40d070b202e84080d0024200040501003d202c5009441e0000d01c3da0080ba0305090700c145c0003a05590041c0e0023483d8038a1080c55040c08650041d24003544014007040404c41c0350304440e8502285e01c540740d8054200410a58141c200314014525140301e5900000200207440903040c958008102a000c0c49a0311103c0150403141c180c0c001410300705580e410b0340506580d91a00703807203000500c0f810040c00d50103915220300c503071505003521404041c0300403503004082c15450482840156005050203a0464008200c50035440c0c4803182100c1d00480281c0300040045a000c2a90710307810149100d210180c10034914855100c40150003801407156012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 177756591 1250 177755341 177755351
    0xc01020d051c02070302070e0910051e0a020a05040810150b030112030311070506070e09061801170102070206190e10022505220c080c03130215030109050604 69
    0xc00030355541c000d06440c4107519a212009214030402900603000007480b0b130044a85043c0c030b07031040c25240d01c000ca0b40c58003594440d00b0210201a0b00f40220340d04110668401c0005c4c14141c1c80c03000d10000000c12112010342c000072030110040c40748044800034907806007038a0700d20001203401300281c02030051012100220322404101c0d021590102e074122410b003031101410829565065014008a09250b07006900034807a81021800030710000d48540e00300d5949900017940401000707800075003c1e210500a5841e034106983d400b16a00005042d90003d403803c141e2941d28280c4140684241e40009400c050045502035075070b046c640200e0025005a2150100145030100340102c0710042854080180d1180000740c0550103c0160902c0440b110f10707039170310382540325002700c2c1c3b410b085420030201074010550b2400780d0488a10844080c3c440a2034100c206091246443d0000d000250082c15240f030800002c0c0b04543e124031000c50810b01e0020341c40e0f12907949514984c010601100c20a015500308 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 177757841 1250 177756591 177756613
    0x30e240301231305061507060203060109140307120c08160821030403180e19110a020604020120100218040c14070807061107052407030504230c0102 65
    0x115141d120030301024080043c04512090b860020344030103060107030001d02030040a08410555401807803480c0c051580541d0f64103242c0001810200b85901030795149842c510b000740c00d13030b8010483d1000c845443d4100700082400d8103000c0d40011040c1c2c0214031030701c250501e86402d1000841e40c00b0403118010203440740b4440034400c09122101606420426001c10800240000d02603200809486002e140e02200701d9141e040c0610071740c1d800e0b03074404141600c11281d481001064007500c0e0029100d640094201690810065601e210103030009050240841c51426000701d000c1e8003805c1e40780344c24115901200e0810f0b1f400000d50203400360007101e00340041103000e01d041a002701000f01c2c1c5c0d150303200e001c0c00c46019050719407500491401c44110000f000104003186d00ba0154030400d041c2d17419455a51545850154980104046502c02c10b038080d2110080c603001003178000d54421603505010403140d0b250310b014880001e0b0046415884070310b011840c03400e00d000050000d0070460a030211562000d030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 177759091 1250 177757841 177757889
    0xe0306090f0d080702100606110106090e0307080c0312010326071101120f050f0109141b0702010e0d1101020106061704110f10030207150204030807030e240301 70
    0x10a10050340303030307100b489507001c40307403041c105260f1258452050b00c1700d50382140300000a03108550300503000204403101e00781c181d040c00e10695004042028007005440c824000c4a500c0380520356008c0e114440100d40158a070b8014412250132440e041044c40866031280341c005a21700d12021001c200c2c04002c050941c0c64075503a421035050302e41140d200da40642c8a40011640500c00b0034a0b40c0c2140e031a0000c410044506014290042a400032442c00d15810014200100c0724989568908109404240b0440d01102005251422a014212030799402203000507109060780d00c000030340040300741c0e00c084c01380311102c0c00c40204000240d009000301566400c08407207024518003410405590300c004100019170b546c41c04800d8080141c1601100295035001440c0c5e00e031b4000c407031070102c0d0b000240c8604100c08140d02c0050441164405c50402e41075446000c6030b4000d004004040c405410080543c650310161032826458624661a00d00303408000918000d0b003080c41080e00c40c1c0083c142049440407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 177760341 1250 177759091 177759103
    0xb04030f0e0105092803080405090603030f0d05100b040305010f0b01022e090506090304090b0a0315090f080f0c06010905040b0708040305040b160b340219030e030609 73
    0x70140d489034100955502044640b201c5c0340e00c0a07200741280c5000302c1e066000c8901800085024141c12503c80e403404060141c08000100318910a070070400c40c60013280406020344442e591802c17000207003a80d0300c1c1c01c0704124980d5600f0007992124041000000c100054001c030003140c200c0c510030b0080c0154a030059a68580210401d46032100048050413a5140e05444003844210150007185c8000291181420300b1007c0d1010545900b00050522000900717018107100f82006403056981549140c07102c50021500108801407286c54504000c2442290407004111540102c009035a0740c8551404c200c259000c00ca1400c0c0c1c900400000060842240c4681482a40c0168442c90b50741da5902085030040d0b0010011400d0280a120100c0c05e205200d01038481e6151002752101d44021134207000c00301c81d000030044400712819081001c103545d01c0340c200540e0101030816040380e42d01480c070b0a07410501caa40c0201c0003041422243c00505038030515625101c1c80a40030340e2042c0d1510030166490704 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 177761591 1250 177760341 177760367
    0x90b19051b09040f0603030e12150126010606020102040f14030a140f060405031c1e0c050403020303030a0605090c070b040206090f031c08150109300b04030f 69
    0x14054031007200c26405044010445110010000a000003860702c020003115840c0c0c1054001070120010452942070400d155a0b0140900004065580c00346100b00c01100d0140100e003806218034045010301d240404400c02034002c0d844c0280a42515810001c2c000e402c1071190700d00d0f083c0d64420015042030b01f4034011a8041001d000b4104e10091900d03202200d4204179100d00603441854808049448140040c40c040e910680145030b0b5600c0188031040d80184030300a08090303c0c604403892155101943c0040b80d001000340000c41c80258141d001d8480b40200da02c06501340c00300000304009240c581e4000003e61f40125080d00ca251600d0400d00320600a07554010b00069400022401500d0240b002c0d00c00c81c80014140c2d1024140c2c03401007400c00090006c850601d244460b61040a20342002101c2e034000d01e503141d24030642100200080c410340191181d41d00d50050107400749240152600044015141c070850b050b0410700c0ca2428001c89481150143c0001d540d40301358488942c81001d14101c54 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 177762841 1250 177761591 177761611
    0x6071e0906050d1a0d1101080609160e04020d0606091e050102030a0c080904020409090201020c0f03070603020c010b031c0e1801030b06030a050d0207030614040b04080c030d090b1905 80
    0xf102640352034000601018401107100d480b152a40c07440c668074400c4084240384900c40003214042088009041c3c0d41014141c10701ca9115032003040740c24400c00d0203020710b040e020700d0038805409210012070300034491040090420303410008040303501d0341c00c40307092401c071911140c0f00031030750940a002d659000d040b400741500503001004910340c1c0034803c4200c00041405620010314160160b40058100d9011740e21013441252604607450544da014000b000440c4021745400107004501d0000a032100030501444060640c049810a050042544116044d200140445419a8800720702c4042c0410200680c8001100742c0d8220155081c040c40b10726008280b10440f02c0983d00399510214850401080c40703803d44510b00108002c54000c010b09403210b0301c5da40151480504508000041c0c1b8090303811096103840840501000580000755a035101c1c1d000803c060f01d5941c6000170f179086100b00092203682d1401c241110050203a402d0030140651b260700e00c2545c0c00303a6410200f4003076500c115103240301 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 177764091 1250 177762841 177762847
    0x10e0709050904080c0714180610030c0e100206060a0b0a080c0f09031005190b030c04230a02132715050d05010f0c05030f13110306071e090605 63
    0xa41400b40d50355800510602903e41003d500b411110300c1e05c0950380c00300345010240c80e0000c160b400c0c0280283c0408101018106080c5400004034452080041d15402055612130050002e01e200e0300e508810864020500c0892842141c0029a1550196159803142c03180c1c000000350800d0400c100d03100070384140c4a101542d9142c000c440d0003908442c0c40c03442502c108100c685800c0c2d5040c81780c0300000449610004140c2060803480c002c208845102c400614a000c089000e51340e000555001545c00484000c00d881101e400d004040c030002401e007440007044103003844070121039600500501c6e140070031001005a603807031b58007905444c90032000003540144090128801030540202c40600c8900e01c00340003441d500c0010403900301000300103840c665980c034401c440d2580b0700e02032140048444d141440c154244048039145808024041105070103901c01c040301040a8418000f1110a008094a01071315042c01c1c0640007403d05031403014800e015000e0566154041c2e4102800e0b038030695a03c6017 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 177765341 1250 177764091 177764099
    0x706020301140909060705070311150108010e03090a17031201060e040f0908030604110c0a0f0b070c0b011811030a1a0a0b0d02160203010608150109060e151801060f08010e0709 77
    0x11f1a54040d0724141d0410042c0c01c1c6003c6100c80030000c2603010170700d000c4070800644c98034030315030b0845880d07441840050308100140c08095803682c0d80705080d1110303440507540c1c54040803003803851841000e40613400c0c246400e000103130003508041c0503113050005a40030321121900d00602030803600c05080040c200901030011440500300383d88042043c1c000e001c001442c20016244e014600103030b00100f01c0d9212070313019400741040354000e0442d0f041034803070601d00c0040c09259200d482005e01401601508244104210804602c64001c441c168007800c0c0070a81d64100a58142d02034000304082c0b0200c040c90448201c541d09250b2008021a40030040b1034bc2801c803003a0415000c3c2d0701200000b40c03546500c0103050096071f0280704000c000c002c5c60005002c031640c240c00d00640f481059005049162502c6420000107440c2007009500a1800c02140d26188801d000540c0c2d41c1101c20080b440968074800115100e034004104500764150b0340c0380d840e03440c2c0c0c3c0c40d02004500078044580c0000680c485000300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 177766591 1250 177765341 177765347
    0x90c091303110f0304061106010b070f08040f090e010b030c01020309040c0c0803161209020f090403021603050c040608030702030c0f1c0b010609050609100f0c0807060203011409090607 81
    0x340d0312031092428414400010200a01d080004900543c0940000a007040000c1d0171180745080300c9020f0024045a6240044521301c0340500c0d40c02500b18400c01d988038081020420440700645040310000103c183c88400b03007401040001141d9406600c0c0c20780354801c5240006000b110b10b14160300851403c0d81c1107043c000070302a143d07120420300c00d4200210000900c1100550b00c1791005811146000c14040c1d001490401c4000202058600d4800300d54003503100d14440c0107140030180d81f55034036600d41d0b250403481c240c0400141441d00d941d5100200030000c011442c146608801c6130b007807003420303128090f0310349a1041c860029496480f0300018807140c141004920742022009041c00d01d15981c19004c28a01d0298183c1110750101c40c40051114035045042c09018000c180c4030395003020509130101d8070320081c00005006101c2881e8151140d00d11480000c031255501c040d80c01c2c1c40d40c035103140ca5006034100380115032401218208400c0310b0f08001c0e42051141c0b40410041c4031585840e83e040d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 177767841 1250 177766591 177766621
    0x161b02090711010f0501032901030c0e1b03070e01020d02030f09040c0504050303030c07030201061202060d050c090d080706060b0c0a0807032006040b090d050a0305061f080f090c09 79
    0xb04840303540b99071442c111036445200d003c1c003e40c001c0008101c050540307403846c054500c4c00032000e400070303541e000140302107641d5070107040c20b072102c07e49650040d46072849410f04c00c008826520f10b41e608000104905140d0091600045020a8084030307150340071880166101d00400c4034504421000340801100351500d03402c014100e84060901c0b42c40c0507121004030f0b003140c1c005c0b1821112610b00082c41c20030075909214140091030328802c034855041d01341e80018400d01c00c020745009519141e0001c101c03030710300200480d1a03400c4000c01e44c200580d0903240040e00d581003028265105403400c07800140c1c241001040ba092901e01c60080e00c090f1078217079140d031a940c02c0311000780c1c20481c01d03407442180d0240c0c8203048005844c07040000d0000e4503092030180c00403a4000d0448009410102c400e08895401100352070142c00d107824003180f107643c2c040200355040300303080c13011483c00000c04015031202d8224442c5801108079000d40c2c40341d0340d140c0c4040c03603030f0711440c9021a80100070000020092044100c1c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 177769091 1250 177767841 177767867
    0xf0b0d090c1a0304293d170d0504030201122414040c09050f12070b0306120118080306010c14010e1006050307030209100e161b020907 59
    0x1069824507202d05a401c4111011002028858400001d10050040090f61441d001e0003004103004441c0a014646002050240c10604184048915481310034100e103d903001d000c402400010f4219000515012480c55521445c01030110f0204160008103000c00c40360031030490b58964501d083c0c510341c0111107000300c070180036511a40c0c0d4054180658004004500402e000d80d00d1a00f243d801c0010544200030b4400c4641d202e240b5042c00c488500303030491460380448400f11a9200310382c000f400421180c00e50500104400c0c0600800416103030507040c0a54080c00098404441d0041e0018056003291140f41c1d25000e9003409602e80000100d03032000865002d001807415030641c01c215a514044803140420541451751518031000c0b4454040098044041c3d801c10300303211040c03604012070744a0b940ba0102a00480546000a80011030141c4050050096101e450700c00d14203c2c00745440350f050948490b0004482ca00000800b03000d03200b07841500b5800400d50407481d22488010f44c0c18141c1020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 177770341 1250 177769091 177769103
    0x3020603041b080f070303090902090a0302060306030c06070f0c0e091b011e0819140103080d0b100e010e0105030106020d0c021512061915080601180803130f0b0d09 72
    0x1400300f24008107000c00151070311044024100369045180c09007542016410081c005841070001e04100d9440c90039400860384c0640318203035681c8640c004241016102394105400200006400c03003041411a051304805010742c1c0602d9586481d801c4c1c40f10500c0b400c4d120f03e1482d6108107140c2d2407501410f05a4101410141060a00689100c0030f4030001c00c0401038060104003042308000c3c1344120900e001924100c1194204600c00e2448209000131740c3c117000103000100040307090340e4805040d1348130222000380184030080010503507a000b0f20258240c0000e6000866100812075154060005d40e4103039481d40c1c02801120ba00c501c4103d464000010084c1d9000044801200000700004003c0c1002a4105120f90244c6062028801507075418892010030040300d4408001c100402c040100f48446540b030200c503181c9481004882924150b14180c4c2d044044040004020b140000103110700760726040e611a005039a003904541300b81081c441c000881c4010040c0301d448035183e034440044284115 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 177771591 1250 177770341 177770393
    0xd0c0906021c1e0302030a0f0b0607140703061b020c0306060d1b03080307050901020c0a030305030112060b04020a080a0b0a030201270305010e06010513050705071509021206071106010302060304 85
    0xc10343c104190400c41211001c250300006010000302540075486011071898410b20400c01c0c02c4010a200f403081c1c99000c0c1000e08200d0b158a56218188400001103800500600030302c2d2541102c0c90b003100032040300c3c1e00544100c0a03007000c20300340400c605d4803c00004220703a01901c2c4070344400c418510f511800e010b05140110000c000284600040d5005a103103507030f501d0321040075000180c600b82d0340c2041d061040003030210401c0080d40c13100407207043d03c0d90403d00b420f000002d850060050216080c01035070150000c500c6a01032039200700902d21401c119101401018104021b011001c49140800380c0005d034049100ca084996040b0725410050031004507410003642c035100c007402c40c0c0e8140e500c0003075a00180010842032511320101064881041e8080005041c81080078109100b2004018116100310f41a141c4002c8540c0c040341601343c0141c00305440d00a04041680c8480b000c45410380403920402c84c1201092000424506a07035001d4243c17891a1200e4540030b80184020600001000c400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 177772841 1250 177771591 177771617
    0xe07080c010813081608030a180807080a020a0c030b0a0501051806040e0c04050f070e03030406120906110d0501030332030603031603052d0a0e030c0d03050d0c0906021c 74
    0x1710610103103150003402c6280d201e0800740005420b81e03024405118640041e00320b0140803e400300c00f2207008540c070100c142e42e2200c50000a9041034140000500110715403d400002c0c81040d00e8464400d02088000b00038580c0c030303481045591710215454600c14000c6200081503410140d1012180d0b040c03010403140c00b00e450710002410760364100e4080380c42400b04418401c1e00c5820508800161400702c0c0030b181804d00f0154003c03c2c04405869105110703403205045000d004665101001c0340000710310345580c03225110500c00107882c00f840110001002025075151100041c0400004001524400300c22480902070384a0f00e44c0000c1c10155040c0006c00255110503501001c1558040c4241c83e05902c0721031890b46070b1952003038a035036420f05a00046480c00e8601e1071500700c805460701414400c102200c40000700e8a008110064280c214041c0c083d00c206050300300025080e50200c40d002882840d1580c4021107800b81d05100e01000342c3d00010031030304280c15182c40c05a030602c4500d00201d01c0303894 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 177774091 1250 177772841 177772867
    0x71b050c04110c0c01050313260a11120c0a020603040206090a060f0f0314040807050f0d110709020c0604030c08070204020a0512090f0c060c0f03030103060e07080c01081308 76
    0x2d021560321581c04002686141400d090244d00c0d5070200900306282186001c0140380900c0710800e20040135802240001d5840c6110309a500c01c5000e40c0c0d0204070303181d5681103000b4000c594200d0010304540b0481c2c40802484115004980c616030103500545048803042c1d0070300c403040d0405030049a0007001401034114607200c00144100a2026a9840815410151018060620081d0114101420803486681c0442d2a81b40d140e042680b00d6000c41e5030702800d051203400c02c040c209600c22580241c0d49030703c1001e6482903009460383d901800ba5484a69a000c06c80220702c00d0541d158042d8103e81e0000300424080d0020008080c000d080301c2d4905905507000030200d034042000b20380461004200c00c00005140025285e0100350040285881400200e00940e254051120b4074881c040009115050039014482c4211204650089035100e507103e28240014059040c1094001c0c070440d0800562150f00040c082d040e4034041c0c4540c3d00341e8450101500c43c80d140140162444941040b64251403a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 177775341 1250 177774091 177774101
    0x14010917011e06080d0507020d02091017060f010b09010c060c02010f0e01090f020405070c050f06010914071211070b0403090f1706221a0a0b01030203071b050c04 71
    0x200340c000020b0300c1030120441c003a01c07000c1d4500d800c20061409409110b95500051015007404030f9040158a40d051880012a5111400380c001e401811724020711104080c0c00c80c2000c1038660009218202d05031003115280c1c0c0d103000b100d1030f1911941e010010003000304104001c20031044185090b140700503607502c1d1041611608840500140c0d5200c00c2030001e6000c5105007404c3d019000300130701c000f40050310350765a55000050042d02c0303641e80e032010400a6008840d984215584103055500c00308140c4a9191034010034840d00c01a2410701d00884a10b04403e44400c1c0706403c01c3e00d411a601c07138460300305001010103040c4c000c0c24440030042c03040071034040307400544100d00c41d9444000440c2403030405c0200404907403100c070a000d2a12a819001c2101040705a80200d0f034810750b0f009003071082034800d03101d0a081c80140c140f91250943c62000103809c0d846600c15a5000300500aa6555000450072403008581c9100003c486903524414180b0b440303020b610b014001d20482342208400c00c0040e0440b5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 177776591 1250 177775341 177775379
    0x1205090d080307031b0e04051f08060f0901050103020109151404080105040c0608011809021804050d020d0c0804030209091c03061811030c0c0109150204030b100f140109 74
    0x91004030030443c00c194540955500c800d101e080c25100c0c0f55041001500c0544650400f51190752104000341b00950495400c02400e0f0911281c403000aa07285807403521400e007504c00040c40440900020081c0c0700500405040300d5041e50b071103070b62030701d080910480380420410314003c2014403060040c06512400250010f040098000507076400e0a01e0310300c0352042c141c0e0101c0c0c180504240100400388101c4100c0402042d0000080390500cd9480050b49407101403001008044103d8140410b202000914841e0300e41d4680840d0218803181005a984d805440390040c4600310807c003d100508000e140c1d0342c0c204100c003044885103142d201052091034800007020700044d42d200020080d0381010508a1140f58120808000290301c41c0d015956034400104900a51302c1c002400c264945001d6000400183c0c2041444400e4209510190087e5000780b105440001251006c116080300c00c0c00d0b0002180c0ae031050481c0d01c0b6152100b030100745441101107a041c0070b9006c0d0700003529050608400558 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 177777841 1250 177776591 177776603
    0x180a0905070e0f060a0317070804030503040e011a091c060e01140901060603020310030602090109030c0f03060b0f130b1801030f12050f0d050c07021906030c03020a05071205090d 78
    0x1920b4000d480f110492802002d42c0e206420081c01040451584402c82008150071126181d4840007420321424a104035072000f01039100004002481c141000300c0b890581d40c06031000b6100c15480e03203d500142c090860000d40c8081d554200e071032031041c1a404540c0c0684203a034041100c1c200c4071092421a0842c12800001c10b5800b000c0100802c0280300b210054600c5040c00c42c00c40c01c0849281c2d4204545000043c08558000390b80081603004020b07090085500145113040c1c1d58442c4414400c5020b10304c0f0807100b0318149005400e041c58450b0328031105440c00741401e64142d0100031660040d001c10711450750040e2428100302c4422010882c002d010714007456030202c4400552403e40010721100c4820000c104083c00501724a8460301c2c00c540004d050414041030644030160140b0031441070030340080d8803810900000c3d001d224194528000c540c1c4944013040341268a00054013a40302f05440740b000140c1c10400500001c070725805c1c2a040d00c10030f203040c5060203640808100c90744d81d640c07030540340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 177779091 1250 177777841 177777869
    0x2b17090703030e0111060610020a05100204080c010c021305060a0b0705010e0f010c0f050304060624020c0108010f0b030a090b071d1816030b030d09061403010302180a090507 76
    0x189604400048491031007885c120b40d506411031240c0b5181c24015094500c0b420a0440d4070091a1081244c1c0c00072030303040810b5590803491000c089009520610407000c0030b015031450694598000c00c049071005402070000ca284841c05c0f40c41400910009041a901500380c10011661104030406800d88901c1000001281d058181c03d03140340a142411221250303050410340c0644036032180c907100c3d440d55541040794690701c0d6494081e001d400c40350414107010454842840003007130700b0303429810500e009800343d0f0304d140303003c100448001d5024000c21807487c40c0c42c1010040e00b14048010b6510140d0148001001c15031a0395903030301c20805917041c1001500c4c01d1040d500d18541d000800d000c42c04100d48102d0000c460758604208000d00600c5000100b00070651150114000c0d0450041100024142c400b00f00362501e02405182c9a8011840050040da541003100760425048a050340e800401c0349803485214410004000001003050300029200c4110704005201040070b00f010f001d10a407207481c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 177780341 1250 177779091 177779093
    0x50310150f030e07030206070803040c08060f0103020117071b050a05160513090b240d150c0503040804050907020a0c09060509060108040c0905090c060f0a02060105032b17090703 78
    0x241d50103c0c3d0742201940203d80c0810040c0e80380c0080707400340d652058245803256111704181c000780c4110303400528280152402c10040701713b0003061a050fa4801d0700d5112054022983c2c080300024100c5071100401c420100c0307040424500d510b00321030107101d00c0440c0d4801c00da82e982d1904003009180c58061030705d98030205103e01d1a00c1401d805500244140c100305200d001d031106481040c024207a040304036a103d00000340801c41601e00c0c5404139010b0808420804c40345400d00c00b601d1801051840c49240110f07042c4110304c144c0441e0300036600104420308050400c0d00b002148070014009000390b1040c0024600050b46484d600d0004146500000542a140034148018882d000708818100803508042200040b0210004800c0da40201c10021707140d44d4449541c0c0c64121007022041c2e110001180c0c00c2051030000c0001c0151130455400d0b1402a6a140700f80740d9a0700b10740790300003c0110031000022015542c040c900a144100c0c0c87c00700002c518482c0140201b00341555422502e402c050800c2c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 177781591 1250 177780341 177780347
    0x216171614011403040b06010c020609060721090305121b070f090b040c050d090201050c012c0a050d0305060105040f0b0a030c1103040315020c190b0c1306050310150f 73
    0x494200c3d00c10480034554075196440300300c0010000e084a0610000031030140a6403039517410340d4520400901003c0e910380d81b0303060104040d440b0070700212466100400c1c1d40b030901c0c80341c3d1041c0200c0750f0090045c11413021110621040750403844104031a148000701006051500300100d01c01084d1035102203d40b2410441410240c1d0300e503503d514011750900c20b0492519512800702d607020498440002211455840100c07410301c50660086403940c00c0103c1c00500e0809446444e000c0d40200c1611000741c110a100c080d21240300e100c028001e9044003009881d041d000750070150340702d50145409850903846000b108100b01140c0c105d4054400046201100c99801d8414260202c070030b0304042060f0902e04115503920f2250307010003440441144c6d0301340c0348010580c050b19511485041600c8191801c40310352034221703040c4441615603a00702030104100400d130310201c4001000020b5038001c0981495000e84544c0d00181c030840091304070400014030a00d15001c4203c00304240c2d920b00340e120304008801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 177782841 1250 177781591 177781607
    0x10050f09070819081309020301060e0306060904050c0d060e030d0509151504090203030d0f02130b0a020c0d1a07031506051305091f0311010f021617161401 68
    0x110010703442240c0c0e8440003e8904100f903041e503440300e280350751101c2401d4a040441816406802110f002200203d40d0035040351312144020026011581556100700400032208c9050300c0240c031540254004001301c6c146000d0b4840c0b9940200800304010240041203443e550040050361030701e541c0c030028070424450a010b05000303100f500070809614104480c51f800011140f070780c454490382e43d9691403001c5403410310642d20b003034091041c204110703604134040d54065401003000c401c440d0254040425a81e40350b40c20780780c0d01d00c65a40103190843c0703020b0030f10000301050b03102560015142440c1081540d0704908a0b48580701c2076030702044035503041c0074007400942c503604094240b00023403120003c80ca1410b034810007201d9040316a02c402d501c0d20115109140d80281006010840030040401845071000c040c001004c02a40c6e007411840c0c00603401c9031546850384400c4444c1007420020001c003040c14242c0f0034400b07038900540707180d00e0206186a000b04403aa010300c2c1c204c014400000002d40e000210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 177784091 1250 177782841 177782849
    0x80a021507110d08090705040204032a06050412030e04020a030f0b10140a030b0307140315061003050402061308070302031e1504030c06051306110406050f030910050f0907 75
    0x7403100e201c11000240c3c44a4418080300c04100f4000d0010380182e070204040002800d01803c11950340391603080450f81031041111131901d04c0a488000018800800880001c566050b40e4071410715061100b1180038441d02c80d019010415121412400f40d0f0780c2d440204004415520300040d400d10034070021095854503581d0300e02c200b00c41d07009482c4054101030010340c0d800f5a1030300c06682c1d0241c080c050340100031001c1d0740d5030188102d1401045494905207207490401c012821680e1107401c070000901c3c2450215526a00311100611701064203000740c10407900b15200070f1080e030800400e54014102581190f000010940c03200b8402c00c01d606041c0402c243e20110541011040317145100d05a40d11b101c2c0d4031400c10001840c900050a151140038803c154590140043c095070a0800d15140040041c3c0c0003500d0841c80d000c441f8111516140c2258122901ba442e40c40c184600034101a400740c2004140031924001c0d0401d03294510110b01c9070b20311078880740c14a4002402c0c43d104651800980d500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 177785341 1250 177784091 177784097
    0xe0a061d120d08100b03010b030405070f0302010e04020c07050402030a0c08090a020d1b03050304060f030c020c011b030c0f05010c0f020304030c0b0a031407020d02010c03060f03030516080a021507 86
    0x1011041c60540032030080c00e400c5031410100800e803103544149009000c55070040101d2031001c000072800c210040011805a80943c0072243d0342900c80b4085244203040c1c2c44001c0c0810f0541844404a0920707402401c4942da007101611810340d42c0d0f501250030f030303803085806481166841800b09442c98020440c00d030000c4c0000c00501040400d07a0104100c000c1e09003001d020000d2480c0c6081b0022051076000c8041c560050650b6120343c1c2d038000242091400750744540c0841c0c24298455581132000500d0300c0700e25016900c4000c01143c40c4558000141c0c3c101040e803c10000d0100200840c0811107404042c600c114000142910b401000928809001c04c100c0115001041304001182004450a040d107241028082ea1840c080200303400604080d40c5802c502001041000907150300800e2003001e0030f11b60b800078881040240c00440440382c1a001d541c078981e01c44c2405001280c0705a01405d1000c46021201245072070503140d2042c20340261580078016400068100c06481484d4402600520a41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 177786591 1250 177785341 177785359
    0x240203061809070324110901090b030907080312010302010e01080f01050405071209050c0306100b390c04060e01050d141c020609120405030a060207030e0a061d 70
    0xe400118000c600200c0840007032103600201d03200039020f220a50080d50302214060366402d420010b0780c0c1c1818075520820001345003040c4000c040c3c44820880d09400c0050f9200029641810040045504044c1c460030444c4640e80d408500d01000300000c04000c8115100005550b245100060000444101c424100b0050740c09100c21005601220341c190b03107003101c0c04070304c0f651000e0045600404942c0c00d583c074241003581e0441404000320b010000c54800f40e054540c507981e0061008400300680c490005041410000303d00c4e07051003520001080d10208098401c0d0510310040100141c5d0158010710441d00700104e003072010300e442e10444008022102c9620080d6141c4000103841682ca054058540c410491800051401c1804410080c00444043c5179804101c004025540d031001c6440c0300c25071013070520b1340c850450070209580031a04001c00400840300142d403844c001e508906001c8080c040c118075900995038413078181c40c010f000280d8a219001141d0025036818425041e4101d0150f03250f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 177787841 1250 177786591 177786601
    0x3050d050a060b07030e0121150b1602010c1406010e1005030a0c031b08060a020702030609210703020a060c03020c010b090106091703130b070b0702010c0207091116240203 75
    0x500a81d180c154050501014002da5500141c54606230908511002c0c0b81d084802e01d1a41241c1d40640724441442e00c00103025a01c42d044005248684004d200603d400001d0140040d071058003920802403190409400418030108a9440d1081c03c1c0c000100806403542004007d4200000081c02404100d00411201490703440c1c4401004040c04040e2101c850501644010340d4411545030007017030808100c8050f8a451038850f0025000f4010403482400703810007085c4414000503500b4010249072a1022a0302100c10110b41703642d125100440a5026071040c440104071030344101c61443c0015100580d5800400f4480d03800c6440f012502803150b030f658001071098036480325040c01503402c500d424944407007140e201946107000b4021040c2240c14034180c0810741e0f040a5010b4100c851151030604034507115000182c0c02c0e2407040d601b003030040e405007001b0880030005030030500c0c0300200040321a181070820403001c0b00000c20281c060301d0403111a030100b0390031b07070310f0301c01d884405d6a00400c114107500700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 177789091 1250 177787841 177787859
    0xc13050301020c0f120f18121501060905090408030703050403120207050c0a090903020d030b03010e06010b070201090b04060806130603051c02070603110301051002010e030304032f060604090c0f0303050d050a06 92
    0x7c3e0b0200d04000642d242052120f0345443d55040c54058500d41264420a5050080c0d155580c1c240a2480000d00383d240c001344505040031203074000c95029110760304507034854008400a100041050b010400b020b003642418480900c0146415402103000e810758603d11003d1241900ca00d03802140454641840007000c203170701040101d4405000c0c5400308109207014000b07405041d4544100c0021b0050307100016001e2901c0008010b014800c1c3c030789000c4650381d000c2c02d070000d00a5201d02d101281071000001c8040c60319080d8001d035004801000103147d6103a4070354038030b0038407090305402541c034551a0350101a40c04005040c02002c2d03030b103010302c010a07040c40786078014041885075a0066155894500706913000b074000c50704030403113001229200d141c21b0900a0000c1044883c054880c1103d414481c414403982c0c1c000038945440c0401490b854a510b000c0c4001002101c40c01e03210500111008100d80f5102c11604000758000d980c0c5549646d500500c0a00b190030142107601418a824010040c10750 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 177790341 1250 177789091 177789097
    0xf0d06061407020907050c0d0806120c0102060c030402150705030309010b040e0d121d06040c09200d0e0106090b03010b0907020604020108150406030804150c08030c13050301020c0f120f 81
    0x6070540303141031aa2505d0b80152040d0180f501c5492140c060202c03800201544500d48500c242c408680100089102410081c0c94a5030410710078016004034001422101002c0c004540003407014142e640c411306d80c514440d415411030f0030101d031160000424071102c3c4c42e090003100308030201207a00f04002c1400703aa0150b03444e00e0b0b02480e40c2c00d0294000001d06405429400110445a070400042903440e502070615201d2100319400c450410b0100c1e000319035130155109200365108505600b1200d5600c030741c0100380942080300008070603034407081c280103545002e010300b81c010018010041102020002094295003504a04501900d00127003000610b5900140207500960203003049003031500c60303101040001030030b24031042e0400e0070030100100b0000749000a00c12100c201480c013a05544000d03045403440801403001d40302400c14800316000d9040240145000035901e401d000000d950b80f000b0034260b810040c0110000d400a00c0302514007001401007a8020340d941158628040c064051004a80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 177791591 1250 177790341 177790343
    0xa0b040201030b0a0b04170307080a0309171905030402040902031605040e061e0c1216080f071e02030c060a050604060501020d0c0602031302061b10060609031709060f0d06061407 78
    0x1c1d9208501f54103200709000300c401345500280382c19551012050054040c00c0c10b014103d914070206a0b0201c041c0c483d850546d586241036000c5a18542d6001404607003540010304241d90190b0366001c82c00041c3d50400020610600703448800c58594500300801080b00c154000040c07268105904102000c000815401e094a2030904010741584525125040c940217086507220b401e500b020500041008a903401fa83c2c5800075a1003074002e5072245181c0380ca001055800001189076021544440c21a4652005104034035104481c109292000b06524014041e2142d9114596550074002c040c1440d02800010380001e000602c1096486a030083c0050201c440141071a503010000c583c0c900140c000303c14103240c00910700d5850300801904080c1c2d504440f6406501403085030003038000d5056a0096404680d000c3d140d18182c1c9145d0f486041c51000d040900d00b8402c2e8081200f10216900c2202038404d0a5030f250b0030301c3d107444528489904503000c0390450024001d004611000055103401212062 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 177792841 1250 177791591 177791609
    0x1090506160903020a0e0421020a23030d24260705090f100e13060f140108070e06010216170c04020309010c0e060403050703031d030a0b040201030b0a0b04 68
    0x48802035089404182c95040213500c03059003000081c0c9140c41c403c1540c003c40c064082221854401000440c1c80d12400c452100941c106800f0000400d826090b007594540e2002500d5030000540c2c2209810f540c8405190b020082c0c1c1ea02140c00503031810116070710340d003201407204904103050960b0b1124080300308400e18403108100d041000248400c1c0300c0c5c80c0040c540600640881d04001540d101d2944080f118401d80d6450194006048901d034420180210441a01c0354842c0d4020344407040a4107442e40c3d0010060703210303102c079100100d410190f03d008080c80c401034118141091894110000c019200070704540c842da00b800d002e0442480c0000c02c540101e0302c90400c4240c102d841e9030800a03d01e8440d507000b8404010040380d0300040d0013101c03000c0d003160345040c03d14070340104001c0640200d01002e04281d01403941030001a000d904c1c010603180c0c907a44044c2c40e95507a980040e14003500700600310b5008401c00700784411541c01d4020007040c1c2008507403441046080800c1041913000e40d10890041e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 177794091 1250 177792841 177792871
    0x8030a05030606180607031d09042316030308011d010f210c0308130503011406010e0111030a090608130201020a110f04060306091713062105070206100801090506 71
    0x580c03129540d00044e0440098030843d2100c4d640c0c1005001b5142a00460740c45003269513120303803075107012a8140c0c4103c0c0d0000020b01019171400c80790300440217612190a40344030340f00106600c44442c0301d106004512070398039101c0325814155400d102501ca40e80c555040a00440188000150340071010207558411210f0079a803244860203c40d010b10301f8102501904440c48080140000d0000078403880b03454404614100740d81e20141422100e002a94203000000f960104410350b12445807a21428814507008074442e4800070b105095074010741c2210081015030008104040d0040c0446034403401c440d00700c500094064002075128031000400510544d0070700205241035580c818130320b0811030003078010880f0075200e113011802007000e2002503400b046003004c48907420640000701c1c0d452103054202035088034544481030340c0c119000300c0608044030030241c405982095520940348a141caa500030003550030034802100d1031141ca030700a40340c2c031390404903a80045840040c900d6000151030b907014034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 177795341 1250 177794091 177794107
    0x3180b130204111303061808090f06070c1e0609120b04030201020c030a1205161e050d09060b0f0319080c0f010617010507080402090f0612010c090f08030a05030606 72
    0xb00900240161803040704000c24403040e0801209654801c0d04c0c40b4640800c642a1189140040e080c0120f000401c03d0304104900046424007210311003004038040c00c62420107003569100c0394038410707541200c003046070b0960020071041d18000c905001080e840c10058085401e000d207034a64843c8241001d40301003002c401040c2018030075411034424221040940303031900300001000348003844480c152140d007414100440c07030722a40c0688492000b80191102800320381c8a00724886d0140c80c84207034200b804400e0100c0c41042d26036002c1e5060080c4079100004044905c0000c100844d01007a0601c0c0c0241c0c04581c9152103c00c0001441015030340194405445140419a940c5840c4044860950950816030000390b400302030f10502811981c0c5800900103030384d8040044881c40d808940196000000501144031036403003000c9107421034000b5040c680d007004003120701d17030079182c044050700005a42600100030000c10342c801d01e006424450f001d9407511444c102c0080c214040030f4041031081500144d144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 177796591 1250 177795341 177795349
    0xf0601090905070e210f072105071a030426090f0a0b0a0807120c02030409051e011502071a0306012109050105060406050102010c080c0d09140303010603180b1302 71
    0x3924840f0000e05c1904000c1541030114541804080a142d45104440451500940120300d01050b2402c0704245005804008a000041c1158610548090282000216010f0b08038184d1119140c03c040c0c10503900c0c20a03103052412070040d40f03076aa405000152800165081b41c400300d84100e801214044a02c2c403201c0001081000b040c0c0c0302c00e080d071000107040c1394030513001110700303124200f10384481c80d0743e00416000c3c030103031201c42c4a1000140c2040105002c0512644e1025802c80240b8082100c41a030f44104907002807000e0300070f22110700c440f02d0400901641048080050311014141001310f8455a80e0380c0d6103400003600c02d506021120001c01030740642c0351001411142510b20901c064030050606034001d15003501e4040c0101c0c10b20102080700e5005005aa5144490342e88269581e0fa41c10040e081942108607962510740c0c8a441c1000451254442034100c00304400145a0707951620401900710f230892a0b244444008040091300420280b05185900c0b4036090002441c1a01707510003e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 177797841 1250 177796591 177796607
    0x1030201050d11070f0201020f0703030507060f0e0f011401050301060e0f04020105070b04030507020907080108061816091517030304151116020906010221070807020604030305120f060109090507 85
    0x380303034080803464130240440c284085030301c68001e0f000d807101e0444a400c00f46d00d5190381e00001d004140100140c80015806038010603050509170000201e250826403c5800c1c8640b004010303603607a45840c00000710300d900820690041000310001c01c021407803c50f10304400031008205502c1c205903100001c041d64020030448114585c070140341c0c0d01e02d203040d21b8080d05a4014480503030007007084c01c002896880c02406424181d0308040006e04c4203548180900881c24030802d1080e241e4008c40441c1c1c0c07035901340d00da0145d01410580c01c0201d101c40f07080c008101c01111503442090300340e4646004500229010044030b8200f07401c07850301c415020004600764090180b5090070400c80e180000d1544c0c030180080402c3e07101038030032034041c501a20303031000490740c40482200301024840617505506010912400070a582c92042e00018100b00c3c040e00013815540040e402038004c10000560080340036103280e00c19502025061459039541000700000705255545d0080802155641c8086010180a1014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 177799091 1250 177797841 177797861
    0x90609040507080906060102060f1f080f0f0c0306010308041503060b04090c020c011701290a020706230702090718090e160510081e0c0414010c050601030201050d 71
    0x400d01050600c00c00050003048110381c94031260190101068447d8800f041c2c09001e0301c540c1041d5411912a03110f000041d4a0701403540002003444000065540b1061081b0700392481204050b14080c88640c030449d06101d600800c09101c0c3e00310304011700025a8490565040d06d0502c00010444c03462100c098004000c0d940001100c05c001080000708200345170481c00b2401c01641c00e650417603101200554282e05804003c100307030710200c80140050070300000c580d000c4014074a00d400c81c04a40000c030580552020381c2000058014580501605801003010345010204c207602e44040941d441040c2c0e12801886c130000d210f00c00d0040403c20701031184985400c05004056441e4040e07a1301e29040c001005101d41104072405031940c03600700c0c2942101400c0458501810385a002c0c6111103040b603d0220007030010003420800410301c001a0011605079208004001240d0b80d1242008005100c04040c94043c1e81000803003140303580003c00101d2603604403030342828026121030014100700040c10312440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 177800341 1250 177799091 177799099
    0x30c0203040e1f063009140c03070b04030c18063f0503030f0c190c0c05090411040c0e061303020f04060b1c0f110909090d020c0402090609 61
    0x40c0140200400b00c80444111a803c00044059a07110f056443d407101081c04420040806450385840b011500c1991018900b09000940102203685094507000f01d400d0008080d44207124020380760408001d0500a00600b41640f030401e0f24580d03522142c45124000c80c0d1442d203210b011084591743c2074000034007621aa90740004070592500741c52803116401170740d0300780c1040e0354031101089460050b00d000405400402551640d590040480c214000203024003e0507001000300090340c801d40c0c065000c1c401c403166600d0500110904003202840340070f411007480303130901e0000d000c00118600c510003281601500c0220300001c5104013922090344072045a600028002101007070428004810303030682c0d100701c0d55140c40010034014041121007502034100c200c442000f43c00c4860f0340074840c01c100c00a001ea00400d80c40540b1040030b050301c00d441c0e1502c01081e804075402c10186000c68009a00c120b0030b100618100745400d10095941500c444040d00442c1d00083c140d03035a03203e002c21502d07a02d00c090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 177801591 1250 177800341 177800369
    0x807020a17030a020c100c11061303080c060a020f0a0f021e030d0608010c230c010c030f05060414070c1a010b090312180402030a020d06080d120b060a030c020304 71
    0x101001d07103d40c48081078900602410440c64003500d001e50781c200000000c0e80d80c095800c0c045503078245042c0d4a1a00e1554000814000d03601c01d8044a50b4442c061849000c54a4035920407003982440c2440c040c1010003068014003c40b00e4100c030180c16101d4041c0c0307030325110400d43d0f00500c00381d003031000002a0000003102501540e1030206c0003c001c100810840b00104442907a60200341d08030790301024004005015054524646244030b140d2044110500b034500b441d0110800059084a0402d801440400c0e225507080b600c0c11141e11a041c1e000d00191801d0140480c0c0e2001048540f03c000c1003001480000c00c0c50341e0621000d110000c002c0303d43d038843d001c26940c6032200c2080e960070030710b41d1521030711402d40c504200410302d800341c407801078403c0d140f1500701e00d17400308000c060341005061000c0240d09100410003030382d031405600000c0840d403010300a04654458024a4100546500061241800a49103007500c1d22022960309600b186400120705004807005c07802c0d84240da000400d08410f40c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 177802841 1250 177801591 177801629
    0xc02030a060203061203040b070318081006030308130c090c0302160507030c1a16060b030318040f060e0c1602120606040f0b100c0201030e070f030c050405090a0807020a 74
    0x681c015030203104c003110f41004000d0340050859583c801c1d07000e10b03410030005210b02c1c000213014101c04540b568002c403c05c0c10198032941034070b19003180700c80001c600c181c03921820000c1c180c2010030744d90061380320003075071040c50256211104c951860384a106038655540390b890309000d10a5064800307641b06120442d00c000c18a050883d40c524180c0400c0d40c2c044900070000440c26a400c0001441c80100c0e1000750600840c041e4008088100c410207a03035140d1201c8203401c10b030358207100070060900031810482c1d203603921000303010488246520b05078816150070014401802c0700003107158401081c0e00c00710341d503201c003600000c0c940418038402500134041c6030412134a0540428190b10404050380d04000094040c440301c4180c80c0401c4070030b41c11850041e0300c81070300352182030710740381040c0181070110300240e0b040d141914220b450f90054007103002d89c00052040010310008140100400c940034402803d04245054849400c410700130941c2c0790000b0f805d401c6440b4580700c0d100800303221304008a0000c503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 177804091 1250 177802841 177802853
    0x1e12031303050c0f0409021804080f04180609060b04090b0409050607050318010207030c1407080706020a02030c0303030c042d060e1002010e0618011407020703050f060f15010c02030a 80
    0x10118005100b41450038480c00b031400c5c24890641c006800902d5041c40c1e4003170101c206001c840250044d568640c08111803880390320700e00010402070494031101c005150480000b2022140c4941081c524182428004c1020991500c29181940d1610340002124014480000c005009103c0c0003462800758400300140d99800c58041c41c0b003400c44000c0d8000c00031200d55598204e128014000700494246d44400c80401c4640e56001c0d10111408121110385456014191602d000e50348181d0051307000c1035a8804600713040c08104070342d40d4181c3c01142141800506410715000da8010003507c222680c1190103540920f0b041a85d100342030400782d03800c1944a0400810f044526100240174075071502003082c140740b05100e00f0f00400321400107094180c44444100082000f2598000201e40d203c1406c0f100c2c40e074070f2404550240e40c240d0010245189103142c02414040030a8252200c4d4000008010f95224056410b40d401a11411700350324494510005a0305e02d40b2846c00a5010300c0790340007600c10000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 177805341 1250 177804091 177804103
    0x409060905070f12030507051e07141909091b060810150f0f0909111b0f030301060507030c05012906270a031e0b061e1203130305 57
    0x100407010358105544803810300d00898000d2003032126092510b03d201c00402d20a602900015104d00c4c10b0300e1905a02902c01176000455030f1214450b40c001c520104503412b0038440700d2441220a130f62522403400d28000c8008640514401c025116440d00307050002c0081584540c2030004075089489040e544907800242000411946001d034000201c4d40403170180b122540c0f400b40c01e001960380c00000001c6500850310f8440c8160f9100500800380c00101e01910030380a103a9002103642140c1e030311400f8901180d089500179844505107508074640c10382c2c05060204c11039055843d9411700301d94030415898100c440c0c408110004e403080d442d065001154a2a620628145040f00804610307070902440401c4450f200d1542c5812001601080c1c9410b000010713a80c2780f1028000901c5540c0040c3c5e6500c40e0400ca84203e0790158007946e030b8090403810841c9201ca4560040019264146501410074141c004654803081c02c0e4403a80c008207401043c12030401c11250900941c03141c0a0040d076883ca4000d60b101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 177806591 1250 177805341 177805343
    0x120513050303010f0e150303091e040f05040b0c03010f030f02010216151103030c09010806041d0d0206100506070303020c0f0f030405090a0c05070b0702011b0e0102010b010c021003110904090609 85
    0x1010b60340105010100c86940c4000d082c0d0018082e509d00520103041080c215403100c3e2400201c0100800c0c1d42c61560345200d0300f03011a00d200c83c0030032140791600d4010244800200350070088101070006001440d4cc051603481501d0340241000d001041070300050303107000400e842040c06040c4602000c0f40a80c1c0a80900d900aa0f05480d2203182d0311100d03801c20384a001c2190140740d608020310a0070402d6100c0c5070441c2c0c10810103800000c2540f4071034042d1140c0d00110070420b4981c0d000012081c095581001899032214407040140b541509100001b18540f245c43c2c005810541c02043e01c0c807c5580c14007030300008401c00c504847d5401c00074400d0700d4980d009446040d1103001d0510004810318468001e0052015107540c82ea0301c0c013550317540d07206070042c8050281c100719981c510b160210840c1c01d01e410290328440c1e03210810f650700d0b200002403d495000300005d0401181c0b442c6c210041c3c51343c802d003500e840102e05012850303101740d803040c155500603002c44550040c02d08640d00e05100307041d48034030b05075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 177807841 1250 177806591 177806609
    0x212010f0806090a03022107060e0c180403050405040203090319120c0815060a020703060c0503161d1311040e0f0c030907150e061803070501030b01120513050303010f 73
    0xd41c1c403d5000c60702d401c0ea5080290150700040020000b141038008000c001d44458110103090030069112501100c070400408050b0f580951883c204518000d40035804e20031000c0025212031500c4d5400503c140114401c081c041d903008008602030900500c1581d0030130326070001028400c00c0c941002004140100f402c410607034508903800070b205115608040c480c2a590811322295803559085c030a0642c0402d45074030444c081e260340400000d2090060502c030a046664981e00c03810562091070390520854507100502c1075030035181820a0342144030b582c5000040700c42444400a000c1c0e410050302900820242c1020001804a1803404d0240c460b401241c0c2210070342a1a62510144502840192803d0b4280d80c4034141c2046032801d1101c00f845200c844c0d14214005040e10703004521070350402039500404494280c1089128201003102000400342441c0510141c81324030b00203041000d220705060880764071800001d0700301c10740440030118180e11004a076681e6030348205401003101c0c580204211703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 177809091 1250 177807841 177807853
    0x8030d06180e1c091a0405030c01030504110112110c011401060908120a170406020a0e0301020405060412230a060606021c030b13060801060612090b0612010212010f08 73
    0x803141688142090b100b8403000902650300020890410503400766000c004211040300042865000e1015051424030002403041d1981e0500c400c240c02e2a188080590406107420100804500303511071070800b603c0207007004142005500600000b90090781c1e00c0ea182604001030802401d40154401ea808080000206541d030362034a02c12503040c0314500c5190503aa0192600e840c0d50b00089006140403841810000d861244408015401c150203e80c01c2e105d165000c5010321070b03541c00c0011110413400490007103142600340000910316001d5405001d600a0110b4106010084611080078905c00140880801540f80030110b81d1b0f2402d0b0803104913050313030420000188403400001d0304d444060340c1100729490301e84041d03000c500070300e004d8132425072169401c00c0094406116201d003c000d8860440045040750401c04003410800590060103079481c0703020700fa400820300003038845070084011903290842039900000580a4011054003116070f580348800000c14050645200d0f08403141c540c2580c1c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 177810341 1250 177809091 177809129
    0x30b09100b0d080316030902090112150e03160309030203030304060b0a060504060c020103020702030a1205030703150503070302040c0504031401020a0909090f060c050d0203010315150807030b07050408030d06 91
    0x1c40c80484000380f035240c081c404a101c40510410107901130307519280c001403000154002070700b0240c0a030702101404c5a8407001d002070114080050218044c1c1c0c2c0c03c01d12040100d01005a074902c181000f41c0d00c1c0c101c010341207404052040c20880c00540c0c0040450b901e0f0304240c05d007030005003080e03000c40e40b041c4100c00f80020780c1801101500c0480d001502d405400b440c00d9001903003e548100800c03607040c040c00301050300241c00180b00d05415000c90360b13129280e1420903406001c45048801892000c0c100308003c006d2070380c0c002007107007e50340c2c1500e010918021000341660140900c1d000100894941d096000317102a0540c040d00684183d551884036040d0f45074001001c80700c0d00321000e8400d441b50b10300d000210f0314580200e040c050381454100e1400c401c1c8800d02003280c201780c00071107080600d04c0980c09602d00324002ca05030441d00142e445061841e2105403a900c0e40140310042c028035000c0006907409001e1016540240074110a481d07841d0300302925800103043c14021a40352aa0f0050281 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 177811591 1250 177810341 177810349
    0x315010806030a20100c0c05090c1207020a1101020f030306150c2428050415090b1527060118140a0f1412010902031e0c01170112020a030b09100b 64
    0x186d5100d4200280401e854100418017000d41741c0141803a690501c00c1109020711742d1003c002d607114402c0b65002e000451158901131a0400004000ba41150310940a1441d10007000c4100c1360841d90484004190b212544419916400f4039044999540141d4210303601802ca0360039034180038019a4280d00d115a1035045808515240b03560352074080482200340510f9161a501140c0c03c00d00503241c0003054908640054103803500c000049803040d5050381801103003c0d0306c460f14800400111141c06140d100e15220702c3c8100440f0b071035003003081e0010000c101141d000d0f20049140d201038014044007141c55884412901d072401d0708050240c1210540013071141d00080b8824180c81c050401000100410300401071086030048004040c1e55039080840d0050b601004412102100c1c458580c1340c243c1260400e50403c1807548042d8103119005e40c50884542090b0416415128600c0758203041c0e0809002103030014616810061401e02c00f03034284400c02a0009905645080000007440a559158248 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 177812841 1250 177811591 177811607
    0x162405030f04110d20120109020f090709050904140d030603050718060f03050f15060d0b0403110706080108210a140d022107050315010806030a2010 65
    0x50501260705011600050b40008603000f414801090f20480c025251030792000740d5912004c00078050503c160800c07640c06c00707024180450b0f000f41c008200d407058540200e0024955154614450100400025440e500804504000d0007014028004520b0720785450384141c0d42c107100402d904d11540200080d914800e005542c1a2070740301014018031880c00c0094420030a002404c40070203511802d011814592010440c40154054401841c10768802e2303040d03a04010449400040140c9907800700003107500d56000b000740701c540c0400488416a61800c00b101c03030021581c40796265010b000170010704264000b02140c1070301d202100750b50004003041254080c640c44200e40d10700700d42041c03000c0c3d031000d03003d064641c0c100b0504820382ca25240c07601c50204200c0e40210714114031285c68244000030b04001d003a01552107405420028518117041c031004000031003400c0d130103040054650005065403020710089c074034075500000f680542240ea05211106d03002040030030340105d04c20b183d1303281424850072032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 177814091 1250 177812841 177812851
    0xa050706120b03011e0f0b0607080d0b010c0b011a0412050a0204050c041a0a0c05030f04140103050609040210031b03050f090a0305122203030903090e10060e0316240503 74
    0x603040075445405020405084880000c4420607507c0441019540300c1c0c000a100300ba100c0c0a89075565080003113200125000520403d04100364013000000042c0c0741a501410340f070140001c200141c103d0984110b4610480c0c01101c4a955080040800c00900142180100c0e02c00c440510295031a04c62000c0c15001e01d1180d811403211924034a0300ca400503000504414059251404616066481d81883c40e4424143c0541004000401b00140200184210400c85d4240783c18403003400c01c40b00140c00004046c0001e445001036106d250301882c000d40c0605030801d14420900c0022450341e1000e030080504484850305a06042c00052030440081159092907515480325810082010034030700307011070002d103402d10503801441c200020301001c15210342058400d81d408198004145401803561505521494040d175050060100804a49035140c0566030145050318011100c2c20000b8900315020340000d0051404520200e03044a1000703c0030007033304030960042c0e203000b00e02904450707510040354 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 177815341 1250 177814091 177814121
    0x20307090e12130e0126060c070303020c07030209090a0201080c0a050403260d0605030c04060311040b0f0a08060610090503060c07080705010606020322051e030a050706120b0301 78
    0x4110b880190300480a4402145121000d40b9919102e001801602c2004e8100036550f01041a09107880a82d00080104405400014086a04043c0142e083d1070040200c010180b42e00800e00c0c4540075010851800155001842503046081205046803100c0d0700041c140d0014070481c0000d55400c404504a8280304500c3d0398461403380355446030380c807140708051101010304910f0944200f10b9043c0c4e02500300c20350070f04000580340b480c0c032080525204402481c0c5002d6414058100f01080001184007041c2100b6500454491107040001c2c02c941c40e6504160360003a4000c1d800304481d440013403544d21030307101641c01030382940482c0c006881005280c400c560f803690100d0005450f009000010700440c6200303906040c01c00055a80300e909480c03807070308100c005a1001c01c401440800c00e5010360354011403841070040081c100f00210340746004080e602c0c6003044000d880b40d142c1b40c404000341440607801c10140c601807905c5d8200140b80c500000d02c0300b6942c508041c558a400d28040c801c054020034440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 177816591 1250 177815341 177815353
    0xd0f090906030b0c070f0602130510020d140903070f03050f3f09030a030305041101140909040c0b0304032c0d02040506010216080c0a08010b0d0f08190507020307090e 73
    0x4030040c4030300d9205c3d207812942e080c066a40e181c001003441c00078040040102400003803450500083c0042d004105411a04550041120300742d8190480e59030a04031500c0d240e010780c1c5080c0c1c040424075008007640100b420086200001090200c0401c4001700c0c480180103840840d1030409004502c00780080e080300403984c030301a12034402100560585e105181e0019060b04200034000000d040251400341900402d40702e1080004005104080c1140b40c6000d00784000c1e840080c045c0100180111844507010791580008203052066a0031120b004108500c841c0707a40745060b103002030104841900c0c2c002119440003901808140c0d210307040801c108041e001540c205d0300d6800b040042c0801030900d6055005e45031080220036000c0b0040f2000d440320100402c8082c1107c000c2c0490400d05501100c2c031645000520540e503501ca280700c0e50075039085544031489111038244524180f040c003030117214000c021940d40d00400e80200151030340c00e001302c05450410790783e09010000c0d074201d032000b010103030041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 177817841 1250 177816591 177816601
    0x3010e1312050d2a021015090b13060303050a030c031a041805010510080f0d080c0a050d14011403010510060c06020904020a0503100801090305040302010807030e0d0f090906030b 78
    0x600160002d83d22001d8013280e600c0c10055480b8800c1c2441386a5501010812144011a5010003855640070036a503000c00142c80711020880360703140103014902080f41c580034059125075503404903000e4001c844c04100102039a03444c02030001d0f40400490320109080400000450703000f441002a036100c01038980c44034500203002c0100134450a0300035070501245c01a9007000c100d0901c00c0340d202d88080d06241c60054207100039685010f544680803112540001c0040b440c09c4d60000500740c0101c901d904454450110303035020740e80303400359005911600b85880300c100381c1d28075454034880c100d03400c1c080c0317021090346d141d0700381420f0b40d10481e44000c03000000101085120301c00d48590003660b0291400500708200d610008081c5e0384a010408009100441404148a1782041c00c400608181008010f50411950050054022488064180300303606000660040c026005454180c6e140e500781c07020f40245e0301000d8150342408102e01d00160644001080000c1d00d840350318280c3e42c05c00c013090016178070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 177819091 1250 177817841 177817847
    0x11113080a0b180a060606030605010207120c0308070311010f1b08090c01050913050108011a03030c1c0306080a1a07020c0901091a0607060e0c0a050108060409031b050303010e1312 79
    0x203003883d18050f4071074511040e012442c68801d00c0081d240d16075010034518a480e000915054498110303642c1c14241c0705e8890002406d203c1c859088130380c452041030319a034981c1010f0710038801c0004071104550804c0b03d41104080584e114044a00c0c110ba016640341d00d242c407040b0b544441c201e400f071105074014030044260b0741c00b031406001da0302002880d00c0d003480041851007003a2a800e83c404220790391a8602d440d00e074000d84455408454040e2b00460a10800c0507000399103601c0c0046180480810b064404040c0384039070021005801c500d822120404a00d240c0010700c110b4040d0b03c14080300d546c00100d00c0403440412804107040004102602903402c04401134002c1c04403024100c8d8000104044912907261400134001041c01080700049050142c41410305007007042010520640e1010018000c581c0c2203000031790040b9058500040d001e040303141c280c550350a02000b02d402d040d041480703202003040c000000d5041c1c5849640703207080e640300c1c400c40303c0030040d261174014003000442000103460ba00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 177820341 1250 177819091 177819121
    0x120b030606010c020a0909051b0303131a0f030117100501050a0e0903040e010f06030b0409030f030b0d02090c18040e0307120504050607030507020301050f010302130b060c011113080a0b 81
    0xc00202094026a90b80005801f21a0030f00011180d0707400c801d800030018601115401c00d502400e40285241c070020ac140d021650030389009007903d924410120030781c1100000c0a42d400c260050b4010383d030b256154070782c1c1410074596203000d1380b80b0b205001590801d10300c1402124108c0d0b501078a501080740c00d0880c00083c2400c001d14059640c8004d01c80064203644149940303001b42294001500000d0405600400b0ba42d4280710f5907010341d090101d00400264085000820001a8500003442503042d80001e00d40c0814040042d62210600041c00a01d40b0000b0091502013841c0300740803208002101880240c2e180c801480300c0e02d410a218110100358001013440844000d481c2a603d4581c0781c0300010503030342101d0001d40004e94007040f03003000c6042c24824250080d4054241c4501c1c1d41c55503002030000300c000003e20b9040c03601d6061340c090f103440700702c01c0d130b641444400b000780321024000c1604100d03a0020401060101c3c54068001403000f0007280313040d15190031901546841c0e8418400c240448 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 177821591 1250 177820341 177820343
    0xd09020112020706050708010801090b011202041803050306040b241b0a03020a031403090706050a030b031203090105010e221406040c0e0711070311060906030c0307120b030606010c 79
    0x100d10300c510401c0c20801032008007030152183c0400501801c0a10000300107040582044a6680c9000c0d030a60124005027109030440d0100d0180460726900391020030050101e01075052902441070380400101754000e8007951180c24295001c212041d0524200142c000c1c8440156001c401c16101e608420300041004003180200390031019a44680301011a02d000c1e14503030180d0041c0c1150040070105030780100100e00c4911450520b905600b81000071640b940400e104680901000150f40c5039414000d400000e070ba840001c041c0c460885283c220003580390720450720310006500e80400460421030a00c6000d005401c0e4901c010800250201d0100700700510b0380090300c2c0f8112580511014000400445104600c82c10005804520307110032514921300140162050040003a2000c40300a400203800044a030404454820841148041003c41c4140b0107283d400040000400940d03003c9400114090685030340c5103040c0ca40390190324002c640381c90003199415000580450074561103661007400039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 177822841 1250 177821591 177821597
    0xf050907050705060408040311270615131503050106050a050c0312010303020a030809070b07061a0406061124010905100b0a0309051b010503010b0a0207031e11010309080d090201 78
    0x21480640b1200d1404c0401c441c22207107080001000c3c010002070004207010040203480c801c0300d080341006040020040030b8000c1c42ca188a510000d1140e5aa1141c1101c840c0c54a00b40c455171484960f108412a403c1405034600341d00d204e5490700d0305140b20b44640d50481d071060341d8041c03c1c44590003007210154050303145da0b1050320050204040081000308040c1c0298400d400130211310f9824640038105400051003071029030828a0104103942c1e50740d040781d002580c00900016076454507100341245c05c1213612040c0e0454074015000c90042c0e00714211400c207a0b81d05040710000d1030b16040078030350285c40700034a8020f0780d550001042484c00d1b80c3c01441e005900308203d2031220751502074015aa8110468441c0025100c1c0421414480180302d20110f0480f0740c0110390304520454000f0344103100c103104454400d01e00240d0300100b98070901600000d554000b050510340c3c002d00b0502e16114210003010b960781c03240307c090f8456560181c480c003103105501c80c4d82603007402d685a141000401c4501c00907414 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 177824091 1250 177822841 177822847
    0xf0b0a03020c060109061d010f060e03030c0105150909070b0702041109101e02011808030403090e010e10060804020a0308030a060513050f01080d1205060f0d0c090509070f05090705 79
    0x510010f00031035000e4003002c20300040d00b13480c02c0f60003c0c80b00300720b5150101c0d0301020401800303014a40c502010941d611803c0c03074000440000c010038903510641c03513158041e51806c0148201c075414084024001e40c000c444800403910340f2030707000f0744607842841112014482000245c005003001e0b001490700046c5401c0260808030840041940721b040508101d0020304900d5014800a05000741d20750141c00d903100070000e4103554400420400801d000160055602100040030140700762411405884014400003007035a50340100c07114503006842069100b003001d080491000d00c01c0e07402521071038008040d00d4030176182d616841201e50001c0c0101140b25110200071074240c41c1c0c5019410842c031a114002b4072454045070b0541448070680004020740c1085c41000c0c201c541c0010320b9036030807840840000d500d403900e000190035000c01c440300c0f80d00800b0040816050040300e60065084540c00350060000da5030303c9680548900640c0108011420100c000344220304205a6055104d030b250704195107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 177825341 1250 177824091 177824107
    0x70e010309050d030b040c051303060905031608030f130f030c03090b0705031b030a0801031b050d080703091e09050903040f03050607030c2303070c0204181106040f0b0a0302 76
    0x30403d059441640c010a0712403900e180c180c1407030b104100346699507141240c281142d500c030100300a03c0610000d03103aa5200c01c1c0b07400622400f4011035004515500445089924519080310140c1040316a02034241c20140007511905e090001020165804290b0b04289004c550741a00c8801c0c2c4000103400304070b07043c4008912980c45500a01c41240100300442c3c4811099040d041d1014205011140940088c03128041e8aa00320f807585d41501d03800034a540d250790b0211045003a004050748104e502c01ca03034403804c0c400d0100d10001030048502030707030b5a000210307100c0805a104140001c0b55608508081e04100a0502c990b40100d030031101810540713150690702c4c821908460306070740040d211504400144003126402d40b01c2c0866130001400c2000b180040c0303601084440a041850040344039001000a11140c8110000703e0709981c0208104038446201720710b400c503d2035086e8115402c1026034030584482c03801c0001e5034116013444609900c65420440014540e8000c01141001e2507000d000d182 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 177826591 1250 177825341 177825343
    0x4080405061b0619110c0c120c191d04020f060a0309140601060f030606020a0b070224190e0c041104030f0b070816020a080f0706060305010c020d0206010806070e01030905 75
    0x140903641c01c0301c60a03004c41078260340e036007152808040c01105803401c0008051458001c140d04c44295003c41c0c0d1500459034000c80d460030a0203d00c0410360002c503250011190110203410541528800007010700c0f4104000d000080c103210994010354044070729600f40321645400c000401d58460b29103004500341d07400795640c050500c1c1e4141e040c110350704110010700015600100c5105299100c3c40d0074002e1900e03016001e0b480e1107241d80c004d4558101c94001540e0320780200080321001c194100c1e408440070700300100c00c1c0c6109055411a41c010f44815255a1006244c020310061008160240c41881044401c00c801003151010020640317200340000808514038074088920207001c2d035101340785490705140042400c07000401003108010107207480c03d841c42d400a41c03a10b485034011500307542d520755504085440d01942100a044509155010080140c10340100f9001c0301a82c084038554405110266203400f800d00804410364084000140d000d03200300a4400c0101040c1000070740326a241d01c880b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 177827841 1250 177826591 177826603
    0x12090301021c020d0513081e2b0606050f0301120c1205030301050f0a081b060417010609200f07031709061006030e0d0c0503161b0e04080405061b 64
    0x2e81c442d550100d102c5903010803900505a002d24004c1081312070502c15940c01d4038a00a40d044111041185044601180c034940c2c101c40a80414451890140801170001d80c070551100c00d00c869030394281000018124000c03070a032041060301e41d0700282140e003015004442440141020703101c80200307440006a13200d00c0b4a1230185140500f000e55036039030402050186009000c401c6a0140c261401c040104284c00310f1090f049030880c1601e42c0002e40280c0004a2502a41c0c00201c40d00c545815881c4401405502c071a080707800b0340301c0500124000c042203c49040c0404111041c1030070810101e03d030121480300030300030b451090402604000c85c02c140c0000c20217044600410a0b0f10a8080c040f00400842444009001c2440d0601614011451907922000d071003180d141407000001d00c02041080910585448964440344d00e0031420150401c031000c0c064001200001451400c80030424180b4404002e20482d04500082d140c1441c040c00c1c006d0316441010140c640000c0000302d2100100c2c24010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 177829091 1250 177827841 177827887
    0x60603030503090705100503070c210309061103060117040f0b0a05060111010c020712030207030204020706020a0f0507021807181502010b06181903060507020d0e04020c1209030102 79
    0x54980c882c58000c3e50185002d0780d58120a116200d40510305107410b03407200c101c2c2e0703114015141110381c10485240104920b01070004092984802e2401e01040360760542c801c13060706000c4c040510800030b00700042d4101e888180c0d0090300140070b03500c440c50505c441007400d0350440d1181c01c42000c00101611281e040c05000c1d2034034002c00e0f44520034820203603404250028042c580e00020040c80c0c1c01c000b00070b5030300c56441c4161030808580030007010a050003805000c00840e0068000d556400442c40c10100039441a0501c0000c02d07140e49c1c0c6000724521400503500501c0c0c0c041e1a800d2000e01e42d64003079030b8115000780b596041092a005051791041c001504100908000120300d002c680c1ca21030190035130f004001002e02a410034888000c00c61003504210714a0881514042042d08410300201c060b5040760b0005000c060a0605000c0c4035540000d0500340f24403180d03928100c1285180c200000e0303108454822410b5031100540c0103403000032074002e11810030000e00040c5041700f09040e0040741e11407004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 177830341 1250 177829091 177829097
    0x711030a030f0605010203090a090b120109050105010302030d050c0703080d0b060d0902040b0409020a0e040807050f0a03020d08010303022109030a05060114041e09080d09110102011b0c060b060706060303 89
    0x290400c42d940c1c02104040c1c1401d0010b03604100c458004140c00d400c1610800f038100781c0751341e0652081c3e201c00c00100c480c0241f40009000c0da0606081c80b0340079001c00e102c124040d1003110b0060345d0452046041c8c541c202a0500503104040c80c544070503c007038124001181e0621f0b90f03034985d60905d0b90385c0d02c020098036480707400101c0e42d40003034010001251780e801c8441e0b000d03508240703020b00141c2d034003105001611b469001c400e85039142e50070052002e0040350401015403141c0c400c8642820000103450728654030035400c81d2070000080340201c1d200102844000c016910554100a1048245100511a40c01d01600c1400d011000000070b1800d2447c0030280c426030040e00c01480b14500000c0d10030742c1c10f0403c0d00d040c80141d0850101241d40341c40002e504080c1550342c0c808808006095048a6041060003414040d00320340341059035002081c2c903a0340b0301642c41e180072410018a0180141c07000852074580700d1140c0300c9611808040c1030840171151744a80304100090010f00d091243c040954001e503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 177831591 1250 177830341 177830351
    0x190f021501080d08070509100809010b06030108031e18040b0f030706350601080703020405180f07090f17071502010618151406160b071b020906010302030711030a03 72
    0x424041c10004c030140c696001c2040c20400480d090325400c101c000100316902c0d040e812661034000c898018a154a61658099000000092103090000140c106800001c840d065882c1c000e4030100614411112001d031080d0642003500710600e441c0d4061204800082c1040d00a030103400c0010741401c1080e002907020940809609190320900c9800b244a0400c00351034a465501d1540241d40c00b2000921b040d0422000c07000160301984a501911300500014045540e015186110006400d20860303550030305825090009240c103104100240c1125200c018503003485003002404540414400c022003014440d4442c00214440605000060b00c0c6503a03000040003820803000c400210401015402006d08040000c524118040c840c18212104103008843c484544004120240518400015008150f200031000d100084000610800c4190b42d9072000c03900050403680411200c0030080d400080310000508554040d600850f04200d035420580d0315148440032152079640483c2400000035103c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 177832841 1250 177831591 177831613
    0x40b0d03090f080a05210f040902072a061d031509060c0703020c06090d020306090d0816090b0306030109020907020c011d0906040f1104030609120203190f02150108 72
    0x40324031500605403450140c2005184c0d0340f1841d5841e5410070700700915002e6140c20004501c00d103000c40303284411100e0708035190f503034814880000390803900742581c204036a00e000c000c0003d40380e8005024240c1449034103403001e007030000032950491004200d2404140243c03610a00d03030390410085680c4441808079622500d42200b2040c02c1141c0540100342c070860034010303000080d0b00800c584bc00d030b81064810300c1d2105590800140c1030601c1c540065094010b1030300b40100381d0404561703540c64100b1500c4d0700c980c0f070b03c58406802d180c10103040c68900140c0f10300700c280b2030310040321300568000100400200c2c40c01c100780c002a040d10416100d030310243c2e01048084c480c55802407900c59805840044d9003e200d810100490300030728006040314812640c40c00e40c02c00c00c0523143d010300035038058403050948851310b0345000f400503c004d15040d105901c2045c10320079107620000444040600d603200729207905944407030588440b00000032040660190702c11038054544a038901c503009000e00360003000380c6002c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 177834091 1250 177832841 177832859
    0x90607060b03010b10020601031e170901140903100902150307200604030e0f0102010f02041e080c0a060507050109080a05091201060b04230409030203040602060f06010801090902040b0d0309 83
    0x192640841c022505c01e900c1c002826008148241100d402080014107455906250380e44401e100c0d1000b86102446c149004101a40c41c02429504c1005e032118400249a0300c40300d90340c0c0c061406c6082d0304d6482040520501681500140b03000e40c8040c010b100302c100384289040305604101c901d84005041c04000041720751442204089403a6031a014051900b000c0e10700500079074002001d03d000340c1c1d92010340246c5034400d51000740745109644046403115110620208100300882519514550035180071681c014003040078000058001c1540020600e0881306507059048a0010340e0295a90030350341d00416404e500903c8026070a03a10103603100001c601700006104868000d4030640c1c503001c020311000000c60210303400d494010106a002010340c1029060428240c00e045402c00e050411420805070000050026500c098099078403e42d1a040c500041110464085001900f40c0c001040b80701555400100c0f0240050400f01f000301d00301d004540c00380c05c520300c11000100e10302c404001a142c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 177835341 1250 177834091 177834101
    0x3050a1205010b0301061110060e06010905030105011d090a08070503071a040b010501110a2406150e010e060f0318010b0607050c0907030e07030c060216060c030e06090607060b0301 79
    0x19251104001e503504141070007040707010500950040c1700e528007007404100402c000c0c601020880300428000540c58101c1204400800e86071240811802403001c00d01d40740600410303044c0d6000040082c083c6c0220000d4040d0342601a2032050346001e18043c890215020340000c202050045c1c008594501d083d1510818a6070703040c48224089050070180b2000072180781c89181120024a0401c610051111045007041d40c060401054181c0070f03440c141c2c5052006401500300610340104000c01d41c0d4071102991101d082c082ea02000651109611101d5800740301c5511600c08007824103403c04c914000c00d042c181d03100303907032403400c01c054000c44031850303882401410403c40c401c1c1ca0540c08e140c040c1d503900395103014000c141031250500c9800103004600c00ea0040c1d1041407884102d4400d565a410080300703a180501407580140291112540f034a046440c1e9582100c03510358070703080e1404c85a282284e11311100c00b01c05070f01990400040400d86c1e108009452514011400058244071107010076003150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 177836591 1250 177835341 177835367
    0x10203070f050711010305040c260c030304030506010b0c031b06060f01140d0f110a1805010c080a1d03010e160e060904023318010206010b030a021e0703050a 69
    0x20000b00f004100181e803054440c1c01ca400c081c00c02140580740c03460095590080307900080800c0c0d201843c5060f441105c1c0a14400b05003e010a48100840302c0c4245600c1c0d00c56800050040c2c1d021134010018602003d00419001600b0020340e03040800d08100c4e21814400c802180e41198011410700000d86410b040904111400342045c0110081ca0000050300d4050700d034803540c0c50f955815404002500e0350f04450480070664007990b66486070070501a00041042d1450404c20034100c41c00300f42c0303501580080b0200380e007203000c3d1401d0903204801151521180700310090390910140150806490900400c0c1c6003001d00c80141c450309920340d028038503500ea1b0b5030108892011040c00d00409440302c09204e50071030b4059584094400415010050400f03509040c0c17201080d0791001c200d042036103070010304044801030002c1e02c0100030101c01281d0b40d10084c091020a2141000400c080180c50b038000c2054010f84150300c2c032215403401141f0203d070880300042d800300d0800507001030500e5200079072107402c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 177837841 1250 177836591 177836597
    0xf02160317070f2006040c0609081b040b03240a241205030f03010605130b07021e18010801020c060c07080403020f0411131412061f1502010203070f 65
    0x1520302200000e103c001c649a60b0780501c1450303022041c0380c0c00104250400b440c03100d03044600509140c50a100c0b46c4800748121000102000301c00304d0024004940013204c400480c0e0309014220030481008000c0c83c00140c119850310a001d80009070b600d51400b16001c050002800e18a2464007000078416a64131484c840c142c07400f401c2140c080c07400c400034100255645039030007038000700712440d0091440c07042e0580c4202e42034011000080c0182d10030001d041805090304030b4a02d4698528200d1007601a4010007584035920245800e1051000180640300400060041d8086200003040d1079000d038003a08200c0c00b0f0794001421944194041244d5900032240061007880c00075140c844003481d00450000078496007400c407900e0003680e01c2d90403058407486510412503403521030b20445103544445105e482d1001441030403100c11450009160301c511070350030000d00150360750000717508040d640002e060850813031940070216092020040b421030440c0c0a40006a0368100310300041c0c10044a08840010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 177839091 1250 177837841 177837887
    0xa021201090314033106110f120901110c100c080910020f09090910050603061302040e1c020a050f0705010f110a1202030904060e0c09090a0f021603 65
    0x35448512580b588007203078081d91316502c400d140140841000704d44445014400045200700c01c0d41a00b0341e2610390b120392001c200d0160000e640f40f0181c0078034041e80001080500590308084141190103901581c180e00004d20590918160556030b0400f0950100941c0b16101c4420754403024825515115120b04110b105032400c1031006540e0545556003459142c0c022500c0c400c954440383c1603c8008000412481103807070f026802503561210707598203a10203410113020800310305001c141d00e805211810003004c10000c0c242c0921015002402416090f8402d0194800d2108107101401c0c101e107129074013500031420385080c0710745881c0c104800c144494101c000e0400850383c0001d0005072501040c00c0c90030800c0e484480850a0220940c4081c01d002c0e0011180c0d42d001c0c1c0e01000a041d0240115003c00440b0b856242c075403600c0344216100400050200308225851601a030000e90080e05843c02140d03c160790340c015820382e08200d00340411000e00c00c40c00d008050f04a5400303070242c4910f18150724 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 177840341 1250 177839091 177839093
    0x170f040e10140105070f0501061203230315030a020402040b130603020a020303220507090e0f01050606071106070c030c1d100302150702030f03121305120a0c02120a02120109 76
    0x20751030700b0b00c0500c02d050000005420040040c1e1003080841240c1100080041f079a4648031450f80c000c02c16030407400140c1440034902e0760103192508090806500e03400600310b41d641c04040c10301c400700c150155498860b581c80000182c0d60342c0010009031401020b100c0d03e4840d02d0040d05040c00c4a900200e05160040c05400003859000003525801062409028150b03018005205d460240c21100a807090003001404500f650030f640144003022288000c8407030b003495020b50f00742251410ba4034182d10620401c18030700452600c2c0d03528034200700010122071601c08103603120024526954022107214500d400e040266a140c401440c4003241d4060502680e46011710031058000e01c24000284100e40801d01e29048078402410b13501c01c1075003d01110000d0350000c0c00c0660702c0d0428010403081445400025204040741c00c404008551b21000134002d180c0d192181d1149904a142c1942c02c00034401c911001580d5080850300c240c400d413001a2400721028018080011000300480341c0381da0514480b90 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 177841591 1250 177840341 177840359
    0x12161403010305060604180f030e0306061002060115090f090e0106050f06160302250f050a050604030311010f020a0305070e0108160e0411310308030f04170f040e10 72
    0x1d901c0705c0202d0700065143c200846030305009080600160004803010a210105a0444500c2811039000c9040780e82d19070701c2404201810500c50700c0d403001031700503c0c01000850741c0310141300488003880c1030084109841d0302c8040b441850313a921a000c100d448a02c00c0b00050828480d00020340800d075140d100001c03104020034414400c4100403400b5034491942031040c10300c00d011990302000c030703604100101407400300540e50000d032500481c84c04400c0e108001403e481d0515882e0200c0c1c10181400b0300745443d5880a07240020340109041f455500d034644002c00d2611031004188840d81342c0c400042d07a0404090080c201c00c815110613041c000c03c0c070180050700f580080e05c1400001c0d286010548031440b54040b070302408a40c1c2401c2e000e8480894405008001c0305105240110511005e1002044400c19810050300c01d100191003500100f010403030541c1255180c503802401360380da0040b00e8003c00340c0003000340e02081d08e00398610004a03080c0203481d42d404201e07402c08191110503c1c4642805010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 177842841 1250 177841591 177841603
    0x6050a0e0d060b03010c2601081513020a0e160e0120070b0c030301170a0809010f05120f01090b240a1101020c0703111002150c12161403010305 63
    0x11034491880040740808000303031500041082040a4001d110100d150703400900880e50303d81d400c1d2100c2c0e071241902d100e0401c1b189500341c1215800d000400c142c107030300506005200d4010300003441040000344114056110400c07030800520707407210000014030f4110640c074a00103003203c26030204003241c15038480c1c0c1c1c0c1c1e00c02d4841a00b04541058404000c0301089018075055003503020440c03c1c20f0200e80b0142280c00440074504940d400159501000c15088540f0b840e07001d1032600400b4201e051027101c6003540701e003942448043d4142000b61410485140e1711112020464043e0b158045000050082d09001d00030501801307029508042c1400241c400c0d0103a2440340b06503005540c10208403855008e1040b01c0c0b109008001c41c000b10364a0081c0150340d51207501c180004e440d2010502d41d251000d091050800c2d501c40c8180c0d01801c03c0000505003004098000744c2a90b0304028180555070041840c07144042c05101d240c2d003072030000d4000c00c00c0500428010f9686009488043c001040400c0c008690 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 177844091 1250 177842841 177842867
    0x501090510030b071209200d080d0b0d0501091202010b03030a02031b0a0807030f09050a1212140d060e010e19050406020409050f061806010e01030f0b040c0807080106050a 75
    0x14008983d541d00382c200c030a44d05c400c0c000015642050170110600c140a84001042c3d0041040340310441c101c1400c0c426130411001004020810030011921441c0b403550050303031040720081c00c0c036004200ca074540c2402d54102c1c0005850b0007000d5464884c0003502449070709503010b400c0d4082c50a10410200103504d82c052a801c2206409039020008201e401c140080c071034240c0e1103202d407a218001ba0a00030319100e0010f81140126900c4d86000c41d092910040340800c45807a40e11301c0315442031941d00c603540481c500c9072000c103014441102d10000110000a00101d051040001481618044d0342e48103403001030303215a41441c04407090104400329041c4c8034003d4102c180d40070901d070300d5900e042c0d0001c0c4103039800200315510380802e000386960351181c1c03680901001c0300c2d41442241e45094000d20074000340d40542c0441d00e058145026940031b80c126024040101c0c0000903c0c68112001c42c0540c2e80400e04000014500000c10602a8201c5400b50150520b881c0c01c508041c0381003800340c420505c01d50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 177845341 1250 177844091 177844103
    0x20a0b090a0218040b0105040501030c0902180a140108060909032212120e040b09060f040605040207060506180720010e07080c0102010b0607050d052503050904050109051003 76
    0x400151810801c00c161400c4a50141c803851552101c8542c0740310200c0705035000c480e03250f207450001400c0e20302801491b05880c1c02546140c200c625180682e00294070a140360500301405a02c1118255215000030700100b0240303100320710400d1030304001801030100400076440350040ca024852500000000e545402c0c0c2c410400c0d103080f070080c0c4113910300320389190b0111443d010000048000c00515822542003000c50f5103d2810504000d4200000d441d007041d0081d401c281c1c44000594189028800c112000001401c000f454a446201007001e0341d000c86c10a46070315072104203000c01d81c20320034441c01c50798103090619802c505040b40000c0462a030283d0161301d00c9035440300303807221200a5029516a40600b0200c03007500d40d95a16143e02c49450000950165203480545065800c001e01150358090b4810068840b02805034001d880d65001002c2c0643d07400c0c00c400503815881031600c05002d4540c000d1300d40f28ac031081c0c080100001e50320141c018030b0519052009216100317101420400c117413a4061 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 177846591 1250 177845341 177845363
    0x240a27051005090717070f0305070206061e19091a0105041a0306060c0105090705010906030606120c0c0203030a0c11041a0405041509150f020f04031103070914091c020a 74
    0x110407a02c20080c058820201e8141c01700b031019081c1c00141a4818805545047c0101d68842030241c0e01ea65003100c400e0b400500710320111008910f10800309240b03000007880035545180503c0d10846140a941020000c1c90b9034880c1d988060713000c0c10280400341030920300b052030941000381e00700c03115007407001d200746904c2c01002142c01542d45500303035200c1d09116402040586084101c2e60399030045485550b0205444050201d10644079000d010191691074890380c0c0c9906c800d000c6800100000c807250f000300100d250310200181e0f402c1c4010480341c1103e5a400440904c142010340010300aa00043d114500c1d0140308200703a11246000c2145050851340042e0940da141041e44c0e041a1144404000a00e84541c50f03080225201c001d101044d17001200700715005400c8414000ca1050340221040d003c0103000400001d40100350a1400401c007500b075071809691000302c2400d45040110755003200316181d080106d200070410a038a01c000c00003400d151084c069441c080e41340e5a5104014114401b15 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 177847841 1250 177846591 177846601
    0x610050702030a0609061a060313030c11032401090c080a090311070b0c1005040f0b0c190804020103150e0601051303140d1115240a2705100509 63
    0x92004449064000905120010703443c40d01c04010510443c160001f002009084880c130b05103441034030f04c212454a22440160103544060b210348182e440110f5200b9210403428041c0e46090000b1340038490500d1808141c1c1011483c840880001604200700351850311850701c0c0481e501a00702078010b8040c103000a114402030504580b60385120006100c00d200382600090f2030f405a400900200110700151002200e190880e001910029200502213054a00101d008500480340080d04080030782005440c1ca07200aa8620000c400b0203844808220814208429540c144c0250640d00c03400903c403007502070909202507200000505228100700000c100c5a0030200c030030040101554004030b017400c0e000e40c08600302c1c2d51001c084001400250201c01c080320704c0000011202c01e40d54680c2c1d030403100c039610506207450b60234201481c9125510079801e01103058660401c880701402132080300124040d00c601c10002c0151060020304050351404041000c0312200e9519901998012214124a0744139 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 177849091 1250 177847841 177847843
    0x1060f02191112010608030421080306010f1b031e02210310030804031112030307050a0c060902090f04140f060604020702010306210218070c03030504050115080318030303061005070203 81
    0x60018a210b90f207010801b00d03d180000015208641168246d100c000709100c0425080c8140c9083c0205071440510201e08150300409070020705160320b24248420014001c4020303030f0080500700a130041009143c880d0301407182c0c428980101d250b9400103000070b403000c0f4555071296001d0b0b800030304000801f0001c21300e81c0101d00000d0b4001c54211813002c0d200d88e1603082c03041e4a210080c5c00c03144107840b040d41c50b81c203218000c0280c900c40d20300b84d140c2a040200038102900c0214000500701c50b203550710040000140d40f4940030b00e000380319a800f0700d40585800d03d08418a00c031100721403001c1d40c3c003400c1040c41d011000a0b43c030b0f611102c01c1d01c0268a41003148010b0b0003600c0103802c4840d00c00111102d0280c01604509290503a0f802100c04076002d010814540d55042001d40303417580043c0f40012a0310200b40603810154200f03106000005220040c00401c80811249400071402508006a4030389800000c01c0c001504134400c80155180d41000c40000b0002c07201481018140030010a005e400d6580c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 177850341 1250 177849091 177849109
    0x20d021203160305220506030a05040609020a03030f030f06140f1206070503040507050a060c02040914120705010e0105090303011e080304031101120903210906021201060f021911 78
    0x5104000c054485030b10728000d4901d4100c0203003846070030704802d03590350510300300d40e01e4004565020348000c0c0703191a9448514051b01e0020030650f2a41c3c0c44540060050311000f00900c01103010350f68140e000048290028140d8100c0c1403120307070840c01c243d030030300a981c070440080701c1078a42100e6012410030030201082040d10003030840c0c46540a86402c00501c40c1e009001588a40d115030b00755210035813240100040348401d40945400900c5000700e44005041591041004901418030b100c4540c00d401b1146252081e00d006080c113064001c117581003041000d00a131001800c2e001d0080c0b260340380c080c07038040e0b883c0014840c4c3c0307c030070807070502403d2155a00c0c03102c1300c060602e40c0c054a5885440342444214a101d0403902d50004224449007800c0e601d643c8174192200e60706681354088103401c0104107008024038680720b0750341603686041ca000607010744010701008110018001107036242c03100c00f61a0390183d00310001503410030261080d02d07003035290044502175408070342c0300c3e155011040441c043e90 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 177851591 1250 177850341 177850357
    0xb010e0409060504170a0e060708091e1918050403260708070f270509010e0108010e06010602030a0c230609060702160513091b03020306060d020d021203 67
    0x9207800c050206001180c0c000c1e41c40b030350103210102c0401c2661000c061881c0b241e140090006412240400000d1070650004e10540e40a041d04a04002e0700c0d40005050304000c0201c01c070031210510100d07070a0f042c1040b42260101c01c1c1d12200d000b00d8a800c00c40340400ea204d00c02c7d000003d0b550800601094001c3d011020181e49146107450140f10400d103111081105481d50400316581304001107400d803207008044411440c596540e82c1c7c40800042c9003100074054100a601500b0202000c20315880e80c0308840e00a1900c000305003e0f5514052040742140c0800c005180160070050050001580001c02c4070740307401d064074244142c801c1e281003041084c40807202103490400101142802c0500010f6018010f400324000c1e40c1558640400903642d0303e005a044545070390600c40304000d5850001d49a840400c540d20340414070b00c0c501d03600d904c101071200a034030b200b2203030449043c03080d42410070180c1e5201e42c040d40c0d400c1c4604e2480e00003901a02000e0300081c8502c404061082295005000340d070800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 177852841 1250 177851591 177851599
    0x804020f0a120b0406110702030c011206210c06030b030d0c0c03020d0501050f0718052112071a060114090d0b07030c020f030a050714160609030201200706030b010e 72
    0x1d4064504100f40d281c05480941d01181082c0d18074001ca504c5c1400c5601c0c0c15401001001c5d43d001743c3e8019900200b0684440503102c0d504e0000080c9441001e01408103030042c0312121b611031390240b616881c12055a08910700309880e06030b000c2c01c2c5427000107842a00003600c4c18414102440c0c0c0c5003100c00c121160304025041020034418104010054201502480b0104150f4409a5030000c04030750403107000c0800e41411044178810810380c2001c1a0402c8940406030904c0c42c50398504802528010001010a008680000709642409042d004040c80c60340342c2c07411010a400e00b800000c15140b00340071040074031000054038032099540c0e072000a01903a88018075401500e0130080107402056409010409401404c03004400c000012049815444a50329141d003003c541e61500c11840222034050001e501c510001c0c0051541947c0141c4000d0400c0e07503035203000c0c5043d480010000c0d002c1e44021a00100c400c6003561071002d02145c0d0302e00ba60300d513160000e1108100030040350300040f446403807904 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 177854091 1250 177852841 177852869
    0xb0106120906020a031e110a03090c091119170402150c070311041508031801020a050a0506100503010509150c0d05150f0118120311030c0d08160804020f0a 68
    0x14054140e08031403980000e076440d50f06c0e9520508a601d041d80c0858514440c0948200660604d250003940000440350003a120701c0619919060103100f110691075403901c4110010038060240ca40c00d060700034025519140c603100c0c0320007410100c1c0b1410300283c0001d00c203181c4580a50440500740c0107582d5040309140c12200e2076a62401c0c23494090414030f52160089040c001c1582c601014081060104c0d00035a00440c6480100d02000c10b0155810000b6411070207026500d5002ca982001a00c0c2002e000d03401401c402c0c142035111452802076039000600a0741020204480b6850100b41800b07607540340d003000a60b03561802a1034506100c1c6c496443d00261500080c41152000f40000e0102504180e03000f00e00300c040d010040d01c0c0058007580c402440c401c20b000170300a10380c036209075202652003424001050200c040c00076043d50000d4440600781d40c81140702c0c01d8440d0b0710003000380c0c00031100d6260704185140603100410820703008001078026101c1001d04807182e214015450020302d490300760103403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 177855341 1250 177854091 177854107
    0x80c0a0c081b0d0306050616050c0909010209030115030201020a0b0702030904020703120b03070b030408090a170604020301060506160b0c040f030308092503020d111f1b0b010612090602 81
    0xd04205124032002c0184a4a0705244040b4002d110780030a4505c020035140c02e00b020f0b4030101d0200500c01d04211018094451800003680342d9032a450300420050b000940ca1741207101c203040c2100c1a2400e015007001d4881410005030740c02044850340c8940200b058280790340c031444164510710600300c1c040c1d0060b100060311400d0551040032600c20840d100703014000700755054101a560b50352802940030a182c10400300e000990110b00401c20b4000c060000303503449a540e541000a800d01130301d84000740e00f01030308000031480c080c8105005031a00700c8505051400140510340380f1416088003c05100b540c5001c00d01c0c440100c070545000300280900304e030381c0319104d19004151110076600b5540c40c1c440d01540a1000340000d645071015600f103600c800210f031a40d020400c0c0c0382c181617029940310308680511901a20b07070014251001c50302d08096044105007110081c403041180352011200c6107031000f0100021816120b981c115940d5140000200c1060010b24005190300c1000078603a51000840d62 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 177856591 1250 177855341 177855367
    0x70309050a0602242503060503070e0114180a0b010201060509090a0516140f0d02041103070f0c0206030f04080c0708070f05040e150c090307030605010509090d080c0a0c08 75
    0x4641c4030303101344491032140f440d44145200d8402c192200180c0d1108400c0c00720ba25042204014510490743c42c0c08030348240e5503c042802c001c680d8020310030f660070170720045c0490700913002101c0440d201602c142c035840c0000441d80400d400040c0600404030f8468500b901c042e8405d4122034041c0c01d004014914074108641000d503a04481e0804540901559064203401c041c20601001111254a0740c2031048202350204488a82e4168107554001c41a85060015807280d2150000c8902451003248c4e480c00d15200260203000307114000400c0205141c60000180ca515040c2d81d0401021250f14016890324544100a802102c20616a0784030b50b51001501e04400200103088880f114100782055403914244401d48402035000301280d881b64281405100142d44c890f81d01858001c0340500304280e540000307040c0700103036005075103040c1c8884c01402185000c41d246c035040140900201058450480040c0c407410004000504044000c2040029540100d508007006030340040e00f07656414400c0070503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 177857841 1250 177856591 177856603
    0x100306180302010b0a080c010f090909051b040603021c03030204081f05060d02100e0f1005090a0b0903070311030a0b0a09050f0708120f09090408031b180105070309050a0602 76
    0x75001503003031807800c9281c0d06100740c0c0d400a440000c00130300a80c101074401550104074250740c283c00c000c002200000c090205104082307400344140d0103060b4014003041c10b0181c00c098800c02c40d2007503150190402c0140e50f900b40d0801c3c00039040c0c090031825035850405030700034000c5600504150069500109403002007600022580c075444030108400e032107060901030790960f01c4400039006500540180c070340302e000c0c916110b152000141085690810200401d4400c500003101c600800c402107110410740c41e044070340d00060070310858140e003428104000241d9481c020322000d44144000e6601c074006490512440c0355168014035072484a00340408a1001400c00c20416a01801050580110402d001c6000030880b005100201074021a008030480258007001c0c80810200080206408584940da1218891030040d046282c9900c1c0509107900381040000250900340010050182e5402422000c034410b40020301c2c141c0d80b102124541a22102c41640102c0d910080800000232382e9640000d007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 177859091 1250 177857841 177857843
    0x1c0e03031906080c060319090c0f060908030f040b07060b0901030f050f06040c090b01020f060a0e10060f12060e0f0106090b0904123506011d130510030618 68
    0x200b005600d80d14109952240102904030383e0090301000415800d00842034842c1600c181d00302c001502070025038070b0007110a51580304c4401440f01060070080795800c852894014801840650714081e51000c00e10030f07034420307405240c14141d40800d0550a01c0321991000301d03501d0000c0c04005039961641850b20240421718401c503001d2080320140070303146502150aa0046038810a11000241080607200203031101c0da8800b0f0442c41030b4519440c0030b040c10003956000706966840010100186002a8101084000101c90b0182000d104010082c00d0094032400c80d091070380c141011400c9440c1a501502810003030400500c1214a941d8100006502850803103040e140304201800311401440a90a01240d014060714034102c8281c828500a640c1c000c1142148052407548200140303281442d400300241c42c0107510b40d143c04010b00c55070032a41e001c404411a07455034050900590016407588506170fa14000c550b20b0b18041144440d11100d000040d6500c6031042c421006004101c00c400400000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 177860341 1250 177859091 177859141
    0x3020d081e0d0c031e0f02071e0b0c03040807030e01030f0911010e0111030405130b0306090109050618030a03091e03020102030a060e0c0301170715120c080c1c0e0303 73
    0xf90024194044d01c203420b00100010729010b604408030640314010f020503210340e00801d8080200c840002d0800700c451610b0b40c2602100100c020705420302c8112806d00400c0300c1d504003410024003000c901c00c1c1060b80d02c03060741841c5c00e2101700855001200034084520104807030508000c1d40d801004143c2d81c681e024401c080c0c0c0d4842d5407200c0303040111502247c0992480444d00100700512542c2890700c02c150ba81d10141d05c01003680380440001c649064401c07521a503041e5501c051070010480d090041341d40114a62a1f070302940700030f02c9145501e901c2641810410326a68003051401c01048046d001900000d0260303a4041030054140603010350f0080311010710321803811034049242803903d14581e000f450302c580c542d41181c0c28156140250a030004016082c3c0c810114000340042010304c08040507001c0e43d03903010780f083c402c030203d0007070714002c22040e400d02c6030b04410003c144031802c00b507810040403e50160b11880690001c50000e0051300d10703408590100104200c040003540207822031510441c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 177861591 1250 177860341 177860351
    0x1b031e1f0506060f030406020f0c070e010b13171219021603030f080c0409020a1706090105100f03140106030605031506010503070c02130c0e04150b0403020d081e0d 72
    0x200e2950071100304441c11540803000b441106030844100010b03550003442410010710b40400400300c100c15402064580308181d10940f010301a40d81c4580c8480c0c01010051001c50900c1c01e03036440c3d05204400c900540e0138142090300101c400042c04c00c10b219001d4602c07582607550b008440d0302070a0800280b007014001d4401ca001d0000041d9040f82030341e0881c0c2e0540e9409015010580c030880b0310744005400c4420411040c0400324081310309100a00d8283d06035102e81d9049014000c141d00e2802c402400c2600c02c1951400420507900c6e00c0c5144543c0d120130340f0703029901da40140c0003900101007541842c1141c0c44440004102c090300b5900c4401540e004804840c3c000c8891006149075113000c0301c900740011406d0001c2400540103144001c51a4802040e41a0703120115050703100312034981c85031a0014a0401d40d01c14203041a2182d01c810070f0140202c5c102c0c15050584020711841540310007070140c1d5407181d81c1400d03c0000c605070f60100c04181d000f03142c80840c40000458a270408680014458a46 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 177862841 1250 177861591 177861643
    0xf0f060d060f0606140f03010b1b0f070e0f041a07020312040b1e0907050907050c06090a0b01080706020703150e0d080603100b10030b0a0b34051b031e 66
    0x7405540d0205c3c0e6101b80f9600d56820035031002e003036421034402c0c43e04120b00a010510043c1d000d200501c114020400140704c418070704503040e0503090002c2c0102e45c20201c2d03130301030101140002c24080b1520780a40743d07121282d11aa00c04903d03510860345119100c1a061050008001d0b1402001e4001c55507803800c0c44245ca090b1026590560056440400640c0f001808010030f0822428050344080305040c01803c01602d01c0320b6509052040b5039541940e0012034100d030420000c0103480c2e0152860703400904030079040001c01707981e0385054040a031141130078a2102000b0070041e00455203d00582d8180c49a003602c2200280800381d00b84c44083c440e002d01c2c103805541050728070460010101c000c3c240311f80229402800e400030701183c82c0d4140c01001054000c03440c44102e1009002842518125111002030320700f901d001203403408000c01c4401007034008200402d00c0042c0c20740c1d010300c4441100000c40c092100203490040e44400a05030849072500760161030401040e103510800b1140d0356180c514400b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 177864091 1250 177862841 177862877
    0x150910030c08040f0c0e0c03100801060b040e0a02070f080c0f0303040f12230901030b0307060206040201050c0102070b01060512060a080304090e03040b031017060f0f060d060f0606 79
    0x81e019600000031410310008011a4802440c0807407940240405440192030f44105080050b040b1061801c05800000703022054a0b020010001440d010380200641030070004804c05601c03131032040000e40d9181001080001e055903048038529a03000f2147d07030301146180b42c80a070907085845052024041c90410100203031011040b244501e5009500161031602175403100c4c01d00c800ca007407003420003640e11300d200c116801840c08028005441840152500001d02c00103007a24010480315000f40c11020382044920380000f0f0311600030340c0c2403d245454407800c0f85128028007403640040c05000c0b4150002074540e8100d4020f00d02d00000c07801c00016903403664140880342c00f480c881c5034210380c41000f003003041030065031101003080301480c2503d18090355039031000c4150300103458a20701c14100c45410071281203010704061078198041c002c0c16041c039010800301f04490f0000e240b03503407284081c4001403146d618103102810740c07640041c0800c14a0103140703540c8010401d9005250104001290820401075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 177865341 1250 177864091 177864101
    0x1091209090e0a0209040516030b0105150c0d0509030a0b0f0a1109090c13080114060a081209040911061605100603020303030408130315140c040303020316020f15091003 74
    0x400301000f401540010760a0003111480148181d5042c010505580c000e11141b040c50b00c0254007800c0000030b1541440b040145a40361180140c142c50401c001c180001100030400a08412850070915180c100e8540820305041729608004d108443c1c0d4010040f00d140c00e001c01a00a50490700200910110003021010750b10680c52019800301d0900300041c8034116001c0140040301030301c0c0c5844030041e60340d4007107403d50311440390605a104a1008001c414100303110081c00600c403140051074501d010459800840c030034482c859010f142c0f6060a038081c0140b040071441e000d0300160a03580d07106540c034800492500810011611130040c3e410910710038506000b2442602d030001c1c0654919151707070b5901140781c3c5c400d61001840805000002000c03d45d880800c4401c0700c50303a6000b00d00126248a0031401d000000e1001030783c034109220500200c6d0780002900c4850207a401c0c2c5409182030f500025030f2100f912428294411849034210780040380c60b1010f44442c90095590103040f0805e08000e8007600c2d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 177866591 1250 177865341 177865361
    0xe18060105012c0f030106080c0f0102060601091503090804081e032a0a050106030b09010606030c170a06090509010b090c2104081e040509090d091401030b030109120909 74
    0x5040b9040490f05400903421003a0200f009080752410b6541d200881d082d0380450703002414a0300504914003090030400001082103100348098401d40c82c0c15000a40750102a010308070148802000032000e441c040d6011281c141d070801c0040380c4a42c0d441000c0b5036181d403035480e4070b80c200b40c41812056000d9800401e442d203030100f05901c011141c410000803803541104100b03d803d9445081003c50100300c00384a4000910f010390700e0000d1a16116140c81d0a691203540104101417400b410303c03c000740c0c005065103440100d0b2200f2100c80d298500c0410161501d9000010711500d044203100c041031055001e69803410f815910351400380d9843d69401564007030b0140ca16581680356090a101e50341e824201070f4010310840e0001c2c1813168400001c40c51150181d0400805e9a00240501141c0707800100a03600884041c01042100b410500040000c145031107002102c40340c00d40c2031035030f42e03000360084070b4000c00c0039001700b01081583c100b80c000d80824180d60b81c086031a41502180e0b500340f50003454607003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 177867841 1250 177866591 177866627
    0x90608150907060c170f1b030f070210050702093c070302070311030301030f0204050606090d1b0503030f07140d050910030f0e010f111602090903040e1806010501 71
    0x41c51030000c0660350061440b004541170301135a4864020060a04003a2a0585641500648030f018101710a9204501c200203014107500511104414064100495807420790542e072801c41c01c01840d600780d440c1d028040000b0750000f251020000c140c20030103060f1a0480d13a010342001180d0402c071162a942980078017900420b0400c2c0c00181c099406500248811f81c440d251036013180004103d9241160402e803c201d45000446408206500e41801820307004003040b190030317103020709660029109031300b0703403100400b010a0a0200750b40407040017041402030a0203000e0743d5462140c0c01e01070150f58880392089a14400c0c603d06c0350f21803e40050b0f50302c185255078843c00d140030350780001c2102c02d000141e240700405172214960000c4030110b006001015401e0700c0045a00c0d000381a181060300c0040e11a000c10788000e0008030311003a80140407500d1342d0340566a032041d94581b8102a8210b2043c0d401a8840c81104020310100c4a480310101c0e1000703005000b0386600740d89500044561524000450f008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 177869091 1250 177867841 177867853
    0xc02060a09032a1a060102121921060e090f010b0d0f2303070b071b02060c100213030309050a05060307030506040b04060915051c0b070203070503040906081509 70
    0x1804042200c0484080c0c191003040c2d004425641c4c1c0e080b120a200060200d11090428400b5558041220a18422440e00700342e0030030903030351801800280c0100900c0e040001010344241044141d18030070030600001c2d902406a1502c402503042c1c211001d6907091007a101e030002080c00c0035818422441c11040003415502c40075051f40315034841c2c8134200703016103540036141000c1d4070449030341d200c00c083d511551024540324003043c28110b4402e40c00a0010050000e550909411482a1031001000340d504948083e01c0d2050308100c94a000002e54040c0744107403001a03900c81a03021130003100101ca110707542d01c602c81307a20f4030244203040c3c003540300d001d422100c180b0206200c14004d030410f0741d002001400002c0c007881040700140903219194050310016607a924070075440191104c602c8090301e03050b01c0e890200001405642c0181e40700210103010300c00000003249245200b4003c031808039805c0703400c480c0c64545940140000741014070806030b1a00c0b40c050128000d000d120341141c841c2100e0805009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 177870341 1250 177869091 177869117
    0xa0c210806040e06070c0503090306040c08150613020d0609050406060f060e030307030503070309150606020c1203040902030c04030b040804060e030105090705101b080301140d0c03020d02040b0301050403030c02060a0903 96
    0x4085520b490107c40b1400240200405601c0410402c0e218a01500f1800c0025103492400ca041010300d00d100001c1c14052010402c1503280c1d101c058041c0c484a81c401a079501248020000810b46500b0141c0141d0803c420b0206200d0310360403000a41d0b14800003104141c2d6940c0e02030721010100007449405400c00d02034540403d010728040e50b400200ca060214a200302a5100742158403192001d00e0502e940f090f040c05429410041100809001d40d8800c4503400000101036490145214000e00540c000001904200e06403058800030341d448890403100b400c2903d42070102e42c0041c0261030005400074004211031031f05002e01da0007280d68002420a5500b80802e00c4011005140c0900c01c0c81101d000500503a00d440c03ca0040e0302c0d004102c8146c5030350501c001404200c03080d0854910800c031056116011070214168841225411203a540003044070b072020402402041c03440c030f549546003504100605825820000096190b50f00b0350354035544d1000c1407000c90b544900d0280c00144200c0d0030107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 177871591 1250 177870341 177870347
    0x4050a21060b150a0f030c0306031e060e0a03030b09060a031110031b0206100f0305100203190218030d05031501050c0a141b03071503020a0c210806040e0607 69
    0x603060980034112000072020f250720344a1a03031004064000140140c1e1203056003da1520541a07407100c42d01e810320030303240345449802c4092080301000c409009511000c000f000b18561041c0300002005043d1070ad0740105080182c010b2103140c058600421a0f10009169440c19030141025240d00454003903440300444180500764480c8143c0c00b062540d10018041c11512a00521104100c2640107003200d103840c4d140d16000c05c032164803006010f506c0ca03a0601c001303400030803c00c040003007a06005840c0e5582c1c58110407040d050340b0900030740510000d00e817400a440c8142d40d04101c0425012036600309901c41d0708036140e00c004c481c1090050102c00c032201c6250f100300e006200d06030140c030482e148100c064a9680c104105107044d603100303600c408510a9460020540c1100c0d42c13100b2400b41c0046450642c4241001d0b01150700c0c84100341e400a020b00b005030081d0b060600701b86d000004421080b542c1c4c440d44465040b00140d101c04100c001000600c03601e040d026444000c0c0445003d01a640c82d128415 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 177872841 1250 177871591 177871601
    0x905010e190e010b0603100906080312040f06110a0504080d0c0c0b0a20010207021f0509091e0f060114090d020108060d0f030504051305071d15030c04050a2106 70
    0x8050b565480304030301c016981c0d03a00059401010300890135822503143c2000b92045400543c01301c240c41e0803d101c4000700800444002c0da100f41c0003180039003114a180791440040400c0780c1c100d80d0820010981024143d03020707010b0415503a403a41100c4500740c0c204800e555503000300f00001c0456403500e00034401ea10101e005041118518180722800a1494008000400210b40002d16a03903011400005514104104041582c3c0c91401c54a03110044180240103110f80c1e00942e000e404840c000c80c072a48508e8400c1d82455034103141e02caa00c3e06049642c4070000c0800e60f6190700017286001d20312141c0740c18600f103c09102004000c401603d0159005403030740c010081903150f01810400fa40004104640400480c591080d0355140c0d8560804040059041c000411010b1080c9080c04014041e500620784a000c4030101880c0940307c02c0c00e000056036501d0084100c5100d00380402803120300c0940c0c01c0a001074071400c40c0d0050580744c41c0d40059003404101c8881d0884560f1102400700412299403103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 177874091 1250 177872841 177872861
    0x606030d030c1206240f05090f0f03060a0605010801051909150b0f0702090705090913050c031005060306010501020303040506010e0406110a080609010504020405030d08060315010608010905010e19 86
    0x31440fa5052951008802c41c0d02660203580d207060b40b04c110b540c901c007408002280d41051410000f000500381207004050f409032810550107120b0100d409880c4e0394907200710703a40400c1c006048950502d054508000607001510660740490303070741000450203103080c02e003900100e064140b1000c40146024044000381105000e090007000c800e81002c110004004001c0507100808001182c1c1c5140c1c0b44140001900300074941c07420000288044c074116510104040d81002c0642e0100e810040c40b4100b00f0301308481022040d40c10311552a40019070906a00010b100340340032420741d0100d070f0740c0300016620b0b8801100e000b007198001c2001841040c07c40c40742a074020b4000c070303400110185291103041c0740f40d000445240100780107608102051402c83d504d28090101514103604062400c000320399a080034039401c406219401c0006035813070700c080020789168400d00d804e4040c036581d0340002038951030080c01240421802c001c00800e44008540a480c09076440c00c804032034045150450310300414101ca0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 177875341 1250 177874091 177874097
    0xb0406090c0b040806010506090a0603050901240905090c010e100c06020f030906062409040b0306130203100605150a020313150210060506030a021606060b0d0605030606030d030c 78
    0x1035038101140001e1040400391104901d940d503100d0a10403001e140c801c05034400b510400c0104003030340c5c3d5515a1204803048a6140c10702084075120142c005003d03243c1005400d1a520500940301400709644200608850099000b000703292100c55021703481d281c1d145081130100b854500700c2006420320101e0003d501405103030119801c8155910041a640200144441c4440100905c0b179619414000642c0100c000c030b951000d00000700ea640702d5418107412028100d8000031900020b943c5440c0c10000d4242001411741e4281e01e0a00c8901d40061b07000c4005a01070700c1201d0381d41d0803d14461185d031081c0c40008005c0010075007200390548041e88181141d0342180002d101114210390360102e190050103900c12034103400d07043d03a5002854100200312040380c09050080400080c0c80d07180440c2d80000345190050b0703403600a107901104c0f206074000c004011a1506000081ca058840090002d45040c0c0700e00748500341e622000c16a039013009841013541034009040341c036080e600a5024001010443c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 177876591 1250 177875341 177875351
    0x3601020c0a1a041e23030604170c03040e010905010b130b030705190c1205130506030c160303050f0c030103020f040b030c0a080703060e010c050406030f110711090609130b0406 77
    0x504418a135421007200340b0301c81c0107000800d02414507104904110307642d4000720f000000d20414000b0b5541c0300e0180c4060000350a504161402e890002c0440701c82a00200440742d542d075990842e6040141c0910580301007903d004008100d10340218100d844014042400c10801810407960b8200d0ba4005800c410601400300301c00980c003950100003d204070308030707180c03814035240c03a04040600650305001e40d030810808120341402200300440b07074802c2e01c00603100d00d900ca46da0303400c010955101d0421440000c0d50021802c1c41010b038541c01c014403541600d805441d660b11411203007a00c5000a00000b548002c018400b114681400c0d88070300c07068240242214000340084002c50034030406d541202da09608018400d20030700015008420030708032010000c0014001c5068018124000c50180204060301c8400c584400d00c0c2640000703045400d410741c40c994856582ca4042848400e0041c124010f00d24000050100d00d0252540d91085006441102c0e0b1003c0d40d5568010f24500240210f07096a0b5031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 177877697 1106 177876591 177876599
    0x1140306060409180b090f0115030201170703060b0d0e0f060603060606071a0109020d0c020715031d03190801090c02071701023601020c0a1a04 63
    0x154a00013043d8441c801d0a4101000c0070b0809081c4031004010702040d4800030514030340320400303440200400c00042c180040b0011080c4000307030104024400c4100007400315501554403415038900040c07401d484207103004481e00400e641d0300c8403a41e66000d01844c3d9030100400e50192a0200041c5600e140120000795075800c024030250040c20702003600010044010020b4188209094001b05551b86800301c0c640250412111030b51031038180020341c4030b43c500101c2caa00c00d54000405400b07020400c20016030144c068101c101e10031180110220030460f41c18000b0b8014103820a41c40046c48011a01c010080001130304101880341c500042001c40c640c00003610403c6900c184e01044044018403807a500a0040c3c403d1147d1001c5030300b850032045134019005c0e94421b6103130fa4010709506031007001242c0d15104011025040384a611003030180394038601001e2040202c11f4010303403a198503 = true := by decide +kernel

theorem cover : BRFrame.Cov 177697841 177877697 := by
  have h0 := BRFrame.cov_init 177697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 177697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 177697841 ≤ n) (h2 : n < 177877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
