-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1865
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:57:09.016948+00:00
-- url     : https://prove2.me/submissions/92dadedc-a14e-4148-af76-5660d1804983

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 335251798 ≤ n < 335431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 335253048 1250 335251798 335251823
    0x320030706170903090109050613150507140a1203020f0d020c061920160f14070b03090c0603041b0303020a06050a020307121104050d0c03052103070302090105040b0304 74
    0x40c2042c03880e00003c9080265103040c20550009003250002d001e4035004201c00114100d0a00351007000200a00300b51320104405592100c3c001c1190b405040184ca0304007560241741e500310004101c00c003101d54416005d55645031041c4003074000c2d4001000d40d2041130300070301c090005a400d50000340b4074501404040c145074506500281c1c038069074003560b24805440c08508078480f09010391188400c0b0000c1c820303d0b441c4c0207602c02e02640c004450750000d1904010517011801c000398075106e10181010142640e200b41c0d203680e4480810300040300c0d1300300075601c00385a00c3d810341803d90045070001d02032100202865480c4ca1659652052a030080b0300592200640c5400c1c0401c520443e504000c42803010744c80c604101c400148528101008402c11a582e403803403501f4008910102d80082402411000d40e00c003003400e02c0c440d41a454030094801d40901d200c080c100215001484080038000c84a003411a150100218002d400c42032019042c488100000314400c00d002c0f0203144500d21410703c2c040705 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 335254298 1250 335253048 335253077
    0xe0c06130603110a050703080c040513050a05010602010903200f150114040606050a0f0909090602030f07030204150804030504030b0c07050c040c1b110603090d1d01090320030706 78
    0x480303d40304004a5416000e0104c06010b560003412034001d2a0141b03421541c644a200c0d580d9240c0c4145d50003207500211080012924844c25000369200d807400c2c043c1000b41740e90360300090303007a14841a03000700010944501e4030568540380c1d11400843e0241422113050500c4040e03001c1c94500c42c3c4002c1c5400020b40001041a4064624041c4d103446040e10b0521802d071410001501901a20a000040c081c40c40d20b040f040c0c6218002d91001450b09100a20081d065410311030002d51099520a940315240d0b8000740031140a8003c40c1c040321101c0045a20071b1622040c00c88440030007078012810450204030020100340d41403003007030041c032041500756595412440c003985030101c83e207101409641030800e00a24a82c120800d403410030b15160322000c1f04031542c507240c103c0494a1040b241e0008000c07090002900c000501520114007686a030900c14007051066000345142e1020b42e4006000a0014000204051200100c16400da241b003850320781c880700028100138007600500001007100328025403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 335255548 1250 335254298 335254301
    0x307120608030f2505030a0c0312050105090f0a11040e01050f01112a0a0303051b0c030a02120a0507060503060a09051918060c1d03030c060a0e0c06130603 68
    0x1c112070750055181000070407071204240181c0b18010303407022501c600400607a041180c1030b100154800c00342c81d0383d02011503000e007044a985500b6000248480001c04405c0d0203807244606075034006060018a584814071608643c00c0200006146a100d20745141c80400c1c1d07001030030161242e11402c0c0c02560408041c441e50045003101030381044907070403010096410101c0c1c180d0229030406d081400007410420f00110b0b501202094030b421001d494070000034142d10201505040d001c44545094011802c0310701603949100050b01a40f5400c9080b0110051a1046580c4030b29490314042d41c8880d040c54031980d0030301d80035030301c0034010407400001c1140038541617070503d010303040340c050400080c2031104802940e0380d500340c0e4080150f951003200e00c0518124614420017141e0002040c84105400d4200402e160451026407456000071000ca400f1403030003000365034002070740d10f0092100d40c0d20a90f03a10007818200a48242c0c030b014003420180951141401401c00344440084140010b180200080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 335256798 1250 335255548 335255561
    0x9060302011b11010305130c1419030809060a0e100827060c030403020a050619060e04081c18031e020a050715090f03030c0314090d08031308030712 65
    0x80460b204141e410004000c2036085a030039000386400034160361050b044089040d2468005014144605000184243c245443c2c241d0448181c61540d492850907150340c214501c5400000c003080320074001d80c071f001d06060b000362110b1070316890b0905405d90f80f240410b00c200c089066840020704c2d008208982e131f00300d205061590b421a65601981e070000d19207040d4442c203001e8201814001c000020506152082000e901016013290944405080842c0242407040c50914030390035a900707184000440b00380c00490b20744269040300c40d062400d500e52400c0c910f0107000e400e40c64502c40d6101d4009500101c0341007600f050510a44401d00d41000381e03241d10728061540e85152085500040040c030000b503020031030404880c1010720f10150303501c4411040c3e40350b502c250400503800614070b60000500d60b011580d5581180282c8590783c4110620449100922404046039003010800c030f00ca0300000c0c0c0750401541e00a80100580840c80699507400c40e42d5441039900c82c0000700700e84015138030615240b1460 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 335258048 1250 335256798 335256827
    0xb0a03080403050c041508120d15170c0301090b0703051003051014010906030201050403030f0c1a0103030809010b010807120b03062e0503100504020d050a061b090503030d020703020a0b010906030201 87
    0x300e802c0c6d8600080c03141d6030720032a41c01c0c0010b1100070030100c042c02c0b05504291a080114641e5101d16a03d900c40c401d1140508a40100c0922400841e54010309042c07142c00011500000d403081c0d5070ba030307a02080d8003405001e00350034914089650000302084003801071404130001038401042d812240103144044c1c1c0d4068000d190040d02c0c0c4102040180e8100c0b0880302260b9050410126220840320240c4e252440c02d50007410380110b00041380140050949214187c034800d850700c82040d2100310036a4222401d00f40300c10b000c40c0c901004158440e0250000e80358074203880781f000c01d560040c1e2001c242001710541e40f03d10040d102004c011070b13640790441c80d480f15104100100c0521850640004d50b20582503c2c030351200c5075510082015512030324016040315400100300d440c0f281c050f14100b8000c252400d1990314015900891440c403074031481440742120b04c014015030605080f440d0180080d480f0980440540c818079a1600c0000c1d8080600c038000e041c03a040000300036145000140112424078060b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 335259298 1250 335258048 335258081
    0x6060510050c0309150d020408060f07030c0806130905010f0506101b020112060504090308041b06080406020a09050d1b0b071e02010e04090609050106050f0604090b0a03080403050c04 80
    0x340c40c199100001341c80116804581591104220401428091007848032444c081400014045461400003806600640c000d201c2080c59595601080f421a854a44540001500e000200780c443c90030407040c1200c90310400c8001021021aa00c0d2805c403040003400758086612001080420300c3d040600e0041600282826030028802d002c4031091400035090090520404155100384815164803840107024007802c10841e16400d0f003406040e49001b2102104e00000100601c43d040d8901d8480400300c0c2c9903a101d119068480303988500194100480130b0003002008140062903582c0d07040030054040c011800c40ea15800e541c07000300500510742d044200d0350750302004004001035428104480801e030190005050045500c0101d03010b41d40880640d9009041254040c2800000d500c65040d0f54131607402040025078480502104509038035109610820601c402c211000d120b802c00c0c13044503401041d0700c41958680c2d1318051950804e0b0400d5400394800140030840e403c251166a24010308d050a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 335260548 1250 335259298 335259307
    0x50402130f0b0907020f150903070210021e0d140708070b01061101060806070903021009090f1d06010e07081f03030c050f0c060d020c0c06070803100e0f06040b010e0d0606051005 78
    0x50647c3c0c600c0841d0003000388548410002d46001c0f401e105882005074014101540540d071240020740d034080d44030302c080c5200d4000d400d00f90707405000500d143c88078210340c0340d5010302031142d0340310b10301e50b08039240c10b031000c803420800c0400180b02d807480c841c00713066240c0301c500306074120b0704a0f0b60031640385070480110b43d44211309100b00603402a112000300ca504443e2103019811035441154940e02c0c5610103140241002c400c80c10724540354101c0200950910403412140c3c0650700066541e030003e214a10f401000040802d0300300c0d1246d001298450f5101c0d40200c2112801c0c08108000d05c02c40c6c0c03042e80000d940242e41002c01ca41030014464210707040000b400180300d4100007420034418080c9400840d17a00003118505158184400d0340380100040c020387c1c0300c14480c20003550907401180c007986c00e181d10060100316441c0340b11101c0d004113005c0000c2d243c59a0f0350000e120003030031448021410300051203c504120b58581c006260418855070700490440c2c0341006224806080842140c10b1040510 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 335261798 1250 335260548 335260573
    0xf08102d030b0a0e060928020103020c010f020307020c010e06030601050c07121217041a09010b060706090b1b03013507090b0d080d0c050403171206010305040b040303050402130f0b090702 82
    0xc515840804040b0307c2000480481d20059009100e0b000c2042015400d220742940d2600e030b030358081c61281d4042c0e0241c0b6021301104004550440f0803c000750b5108005101080243d44103002500d9481c03042c8048036041c940b1915410b8040d240f00804039901c6454842450600b5031144003c0c104104a905210050806540303104c0c03405081c0c0f1011401804603400100204400d41050145a0014102c00d54038025802e00d0005460300d0301007500c042017454003203565603409020b482504260548018116400c14001f00125a884003603202e86880c002c05c400301d10702410042c5458a482c1d14010000d00f4138040c2c1203416075502e080814070543d580b5100d4000300322030b1801c440c002c8044d1480003c01074102c02059400d40070b0783c0c00141080700e0a10b0105440200c140003040c900e400f6102454440c0d503040011070075601300302c80041501e1109004100082c1c0aa000a90414401400302c003440303224003600b000b211106903003c4501c80d241d200c0e450142c14000141e5822043c00d00c0540303924449030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 335263048 1250 335261798 335261833
    0xf110313020a120305090312090312070f02060d090209010504061211030a05070b040807050910060c020f060f0d0f0b0102060f04081201060f08102d030b0a0e0609 71
    0x1000d0048802000d40010110360b9032020110240414035500e04569006080080c182c2d0090800c450107481000009510042082c050300c540d514001d00410028135801620b8045070400d50045441004644031a00140c0e500000760142506007400003401002038010062200410b9004600581c6815001c1c09440e564486001c07120390030000071390130117219101003480c200180c00e000d003060180b1700000c24004103078002003003211030a80c02c450905880e4010801d0700030741558180a00c0b0301f600b0302048018022031406071514001045103240d0940c00c0c000c40c6c0303241d0100e041080607a600040c58840c0302001e00c50000b080b40c2c0f104081240e901c00ca80040d40d5000050901c0707250629020000c0c00b000700c840304403000740c00142d0740440e80b96591280a0a01c110040740e2078040740701d03a0006520100022810412245c00b007070019005c4032070b4607560181e1004600c90601c0d50115403004000316100c00c420030300548510500040e06802d5400303039424810045c03ca2205500a0303080792540b091036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 335264298 1250 335263048 335263051
    0x309150c11090c0901110f01090807020916213905030f0117070305010c030c0807051318020412050a0c0b030f010905071209030c050c0409031d1203040e0a0f1103 71
    0xc6c240074104d403141b522100d00e07210341e103990b8040c0c40d0f0804044c002003106507405016114401e0b620703002c1903100c0444c40d0180d094511000c070001079203010f000100b00c101c2140f041540c010494002542502481e040c58008801c44580900a0301d80010700006203c407040c107a0240a0303460a02d00718100300782412039080c0184101c0b1020728540c106405d40340e8050200304001d59012000700f2070200c8259026000d005030104503400b02c1c1d00e010002c1c00d42406401200e900603100c01d2803c04840c01c1a20300c1c2101c00b02600c1281d0656400d00001c2003020b804049204584d0290b401030003e00c040b850820395a40b03140d0803442d05000180103000f070140e8000b101c4d0307056500b00b010200301661401c4088030005900040c420505040078540401d0640181614951500920640311040d0f200814801990078284005000561080f0080a01d10103403240b0b610030b00303005040030082d0f40d28680301032a5406c0380d0020f000d44000e060038444458840d105080400c011040180084c212001100720709000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 335265548 1250 335264298 335264317
    0x11b091d04110a0e1f06050702010c02130e0307031206080a051c030209091608010b0c03070f0f0c08060109060609140d0609060509150a0608190309150c11090c 70
    0x4039040002d080c0d644911608000e000b1480d0b0105031840c05200030400e940b010b4440b00d24000140e8000b1881c0c0c7d2243c0e08640c0c00d56010786480b01e10200301c4d0b09000e00c0c0c02c51000c4c0da0124560303600c8095102c0700c090008007041406551401074001141c4400d104039411640043c5c2141d01240340c010000308040362075400b0341d541c041900882a1000b40a802030700ca05692158041946010000c070071040c1850941440d0300f55480f121b43e6a2200c903041000d104030101d0f643c095106120030000034203403900440c0600c1c8035030b07a09481c04a0703aa0300d603a4400b01c990440101500100014031000c903aa2041e41c0c000d0881d07284c10602c0500d410016000443c503015014001c40007282d44e4814000103420106a440d1b010b1410032507450103802d0703192a0000510000c40c110034210211311265614050b0302c09803a8024090408400c4034070b4012400800c07000c003141401915800040c481d01126a510105040380c0c5403507101041074a440aa0308d1044030f1224401e404090074040c0c0700702800156400c3c0d04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 335266798 1250 335265548 335265563
    0x20c010e0d1e0306050303041503051609090b03070510201933050601020c010e0a0b1b070603060509010602010524040b030a32030a0305040201030b03011b091d04 71
    0x20b60058110058038207604155058400003070001201340c1c495a280041500550f0100030a03294040328180c050720100704000040c1c10b80e841405501d00d154800041700c4030003070031200c2c01c990b10360214190030042c40c59000070496911100c1482940034a04003c0301940c500504003074515102d08407007004174000058025504441e03581000e104c0c81084135425100c000501c4c0c84c81200c091654043e0504850305401070080c84160b00c1954000e0082c401e0700d040092085100354188520720740b0380d401000f4440c0010603081c124024000042c44030030302902c80c0e42e074045405828502800740701da506a004d441160326003c20051100c403c107903100c213000b103280c9940d1886601c000004000c1d03e171042c0c903a82d26001d0094400200031000051042040c00d4083c86540c51140410700d40b03261145000803030080c1c204100078440c0c0340c070940c0311940c810f1050400140c4e0030801d0700403030b007190b4039002c604222004180c0900c0310281c101c0002d1000341300309800d1300000e6101c0c4907070000500f0090401421034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 335268048 1250 335266798 335266847
    0x10e0f0a12030b0306040f05011104051c050a02091906170604030e030f2b03290109180507170105010c0f050304090203130303060509012105011b03020c010e0d 70
    0x6921030f4101e043c0c0301d0b10050485d1500c1c1050704249103400480300e000ca404c1e40c80e28214602c60350000040d14129000180442c0203840041e1091245101d16030702181d060060400090059445900c1107008104083d2041500302e01144040f08403003003904900182e00038100340e950580000a40140c0c01680b51a05260104240700400c1c0ba26011440701c00b21801880d40107240c40d1214201007885c40b84185038401803454500003a01212041701d0310079a02000f0315696440d00845e0001d580d074030341e4103250500820781d540d410601e03903041c0b81e21000602d1b51690180315040e80d0148200b02500340040712070f50719524000010b03224820200b4004c003403049084207007041c054140b050300c0042207240700540d90fa01e0402803418006407207c1084010901c0d000011541b07040408109040e9100c0000c1504e68403200e08003100c0d1011a40400c03195992140039a140c1d90785d072040c807000e0303c00007501c0150300d51003581200e5003500c1500d1420740d9507500412310340c40c1c01c540c000b545060305040c0403c840c111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 335269298 1250 335268048 335268083
    0x72105040f030204151701141006020a0b130507141009320603010906051c0503090409050c030d020606120105060310230c19110c010f0509130e010e0f0a 67
    0x141100e0740420075000c03012846d244080c2d41034114100009540300e10407d15a20903040003504c0039540107440060348186400070000d5100c0104a4011a455a4008080c60640d5900d45018629001144250f21886042115051a48d03120b10201420b0a05001c51410810454400300401d00c4141ca0354058255800e40f4501c01003001d604c8480241c40d03147e6940c0c40b00410000741009126250207030401c150224a40900004140c05040e48200590720340710710542044003402c9074584c140c03160700030008441600d940030040c0500c09a401d801410541c07902d1410003640241684800700786034109001c200707036a81c0120b01c000e400b000341040055801459400004040d41241ea451019000b6106005009842101420200c102170302600881e007030380701044500c013101d0428040b00307620501e2240c18a41c0621100c17941900c0710716000d03003042c2641e000500c194a8805515410036070b00c0c02140303002c98003809502d0611000c0d6004005c0440c198030b0940d940c5004a1002d411110040700c0e00347c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 335270548 1250 335269298 335269331
    0xe0f150a0e0a0801020c190c03170c010903030c0906210218130603120905031e1029030c010503150d17121b04050d0c050303072105040f030204 63
    0x41004014008000e00c580f00d654050007540440e464807918420076401d0380b003041426040c1000c1c1544240c00080840c0b80d40c1d960360302d152040d105060280710902180b6170880c000d1003181103e5009079404030300200307526009485160b040d0441c0c0c04110118180d50524000c10b10400d40c0001c950b640103a4810124100101e20340c2c6c1200e01c40c0d0310100450001d45102c050b5000070042e2400342001a0244182150a440c00303030b0507110b001d0b00b54000d114a61000350585090081101c41c00e810f41d42442c001340460400c8580401000d82c41c0300c11041648080d42d0640c0907000a007900f940104100100700c40040c0c142e001c02420b20000700281030380140d10703859514403900c03119445086101c0c441c062100c2d1003882c2d004070a0a14110402c01c0000c0d410000d6503561240503401c4c1503200789424105014050700041c0c0d98008c0d1031005445500050540b010002004540c1c064110703020701a461040e603940000101c1a403a0400006100520114964004000449074110741c0010201e1401040d42c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 335271798 1250 335270548 335270567
    0x601030c050405010c2a0b21060d0b04140d0c11120304050603040f080304061a0f0901090906060e040309080f01050601080a02090d02031204140402030103050c0108040201021207120e0f150a 83
    0x1d1b40546c00c0744000b0b207401c206005811035250514a04100d480900303961910540200d88951b400500c041c4000e02080701c000303416030800d00540c90310100034814500d80c3d1420254031200000585180700305020701c1013038402c0035840b10040b122044204001880540da0307003d60f002d500e125210010101d020454240300000300340b94401e00ca10384030b2070982840801842c141241340c1c210803090781c00b8589817918020b2901032480c010451000c0c0c1c1d0a100307203000280302c40d403421034546542e628049260031b0045078440c401c034880e03541c01d03d600c0d080040369030801380300c59200c550b035a041000748134a81e0f030000301040e0703c000f0403000140c03505c04c568001140500081070194040c050481d604c100b50070341b08020030540e00010f915007500d020700340a110403403100b4400900345410604640d800b13507200ba040390703401030700510445400c0c4602c0000780900d03510001e41101c0c0708507610006506250000003943d840803080304c1d50050044003c0100c1c0120303400c603140300c0c8418000a22112003034080c0c4110f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 335273048 1250 335271798 335271863
    0x20a050d051309020a1e180b03220c1202044a0a0807081e0c0709060b1e040f03030216080123090304030f05060601030c050405010c 58
    0x140d50811020202920582c041510082d000c000c0c20310204200840380215240a045607440384000755550184910064803002483c08100078216440172407440c424031030780031b841510840c03507407070a000985408280740c42050444541c148601c900203d13a8070f80c510b070100c413061800c241640051f0702c0050002c04a034560a00050001030100ea5003407a001c502138400580da02e040803660700002e0109441071400304201205502c07010458002603003090140550038410303405142410b48410010b010100347d0089402e1145010904c0400b010341003095a00421000204102d020b09100080c805032152503203541040e01d11401400818621400b20740090064951806000d6282d28009480d01035401821841d0740d1050740100c0ca965041c425803144458094002d9000c0c548019145100703c4002c2c03641c400c0d4081800300001094074801e400e4a010f100d50b004e00b00031b00d0f010001504640e807861030350040040c10b100501031030340c100004132210382d04000d40700400e00d10000901e02c8180b614290 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 335274298 1250 335273048 335273053
    0x1d060913060b220506030d110c0402070807020a08030d06090213060807020a05070f05010201050a02180d03120f0f1b050f09030712030207030311011b080c071704060e04140412020a05 80
    0x100d50b022400c3e41d00003402014120199a02c01c42d100300121408481c0c5200007000342c2001c0268400d61905500500e951391084003004d050208580008118800a5129445540000a0109041c40c00b40303e0803002c4c2c01c000400310700300a41c00ba06d80700303071340ba0500402042c081c2136404660b880c1c0c000c0221008003a0b0006c00c668000e510748410800068042c0320b100d0242d0309110215050035403a000703907044190006004024400003500b044100001c02c01c041e030501503120300b00310b030035500c40c01207950070340050f03402151900c0b10000d65811607a41c0b84000c2808109600c100c03850a5001e81181c07104001c40b03c909455454040c0040d00342042503000da0050b12012180b401003580115500044901940710250541d03032814010b400d071080c001511241e44c1c2140d00300c00c101805a108950000c2940c04043e0420069a490500b031107111b4a24526a440206c1c0800143e540700c00e00300ea062a007640c0030b04c80311243c001d030241045005040144400c40300e15060000d0b074420400314030180d800008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 335275548 1250 335274298 335274349
    0x40807081b071409090604031b05030c06010311180609091009050c040605010206010803090618040213090b01091805060f100801060f0807080a05060102161d060913060b 74
    0x201142c0c1c2c1d0b4000d20a83e0305640b0300c14038144161502214081c40764095101405013942d4a42e000c41f1011691003501d1b41c2c508401c0e0401020032020409000b030b03801d00030000c080950450820b01101d000040b9034920600701d40c0c6643d111011909513045d0042e4040d00d0f404001d4a1301014281422250010f0303200a52805588800740600080c01c0700e070b1003105403810823155840d040120384a5009006960580e4000c00c4800600e04000c070083c0314807038001c0018072800c60541c00103401d0780c2c40b025500300c0440c44004103000d003a2161158a142180908200142d10300d880008140b124852000c80140f903601d0f8005019900d50404555039850700414483d0519039580002d0610003080c0590000a60b500d507504800c40e0103140342900658442d203940340c440d540c64600a000c0e01009208604502a000d14156184026465017000d0181091202c0d0201c00408054003195801002184509030708400d004110050f501466216500401c000c030b13022100c3c0c8041095012480c1c085e103903041c240c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 335276798 1250 335275548 335275597
    0xd0e060403212601030209010e0103050717010b040c05030a0f06060f030b0301020403080a110601060c0b061c080a120b0a0506190e0a2c06010509010c0f02180f0702120304080708 78
    0x8202e0f90580c0c0c0708a450080590303c6220490160a09010082030b6502c076503000d1026080c0c181142210410207000402d081220901050a84e56200702c07030004503e01106010107181180074038144078424a00400401c0e1404e140240714000507248402890754800300b4500c0c0341c80a4046030081c40d0424181e5550301b0000800a042e18002c101d907060b140103180010800754440c8142c0d2030710070780064a5210781d0306c4900410400740c2e07003a401c151409200c2041a000100007101402c0c4c5540c15803290380500c2109081c0e00700f80c80b40d24070003d119003220842072005503951710030385000c0f10710300703070403442c2050302030001d48014504a001c1640034812001c0040d403075040b66800d581c148034511070184580315261444050381e4041d91110301161003072010085a501c01d103801c08546004031545141c070134040e001308140c844128115109a03075100308100d503040d02c8468282e00a00c141c801000d044201d10703c4031100d400b001d80014508800044c02505100700b03103054070740800320b42c0140d10b444085107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 335278048 1250 335276798 335276867
    0x1806090204141203130b0d1409030d0e0a021305180a05030d1a01170604090f0c080f060c27040c03060e060409020607020d050102070f050d0e06040321 66
    0x454840c071640f1640c181c101100c9020060f58803166004100c46015400c0030f00540c2d29401c04c0040d50b550998461081da0790880014484d070242c030018002c0c583c1c82c81c0401c00901500e1040d800304030143c0c0f10206200068030750240d100c000030301c1d00c503000800d9142c2c001c900c121600c00f04042c0610748160b405880a201380030004000501d01e41074200031b400c1c82d559400100315140b081007808503403290203401c4603429120355644d00c42002080041c4440c4d2a9454441444d02c0120503201c40d0103010083c000e043e020000020031003034000041c503461410035011201407007448900c148007406090b220186d100c10709400e13015a14001d005020104611100070001e14403481152020504140403c94600785841071449907900900030307e2421407183c09000340d400c40c05404499a40d4208500f80209041c07401c1003440620a030054501b40d82c40c034200030040c09940303280c00d102d01e4080108000160001034840c400b0402540d109814080b12030341603400001c100ea0700580e10001c0d030f43c819400400e2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 335279298 1250 335278048 335278079
    0x3030a021905072c0117060a2f1903140406020703020a140615040b0102100911061306030b03060c031f030c0603060602010f06050904150e070e0403081503071806090204 74
    0x40c82104c0301941c2c3c0c2c504000109200c401d01038030b580c0e0000f001250781e9440580104007100c100114420482035513030828080905401c4600e0035500000c900c2090700c1c0050281d0014001552400f8051507021001c951150180036000500496000031124105402400300100c01a00000e0042d040300d100e05000ba2244000c0303030883e14614030300140c400e092520388200f2600700c0040c0d0003844c00c8003d243d098401410829400e03a50120003c1d41e1003020f5036540010002c613032004813050300551404101905036a003e465540c8240c0140041101c4038000200390381e40006002c13580204050b5001e02d0701d00c00c00d21a00050301041c41e40c0404911940c05070000c03411210340f64000c100b031440003001141242d540f40a100d034820820008100400d1b0341a1007026244880840001c0d010001ca01c407514200c125404980d5881141d8104802d154002014590106040001840142c005030020b80c4581181c0620451180041e41000b0030031030542c401c0010380310304101155260386076105483d10444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 335280548 1250 335279298 335279369
    0x1103070509100f050a050a05120408040302180106080f042307050a0519060503060111150a1d0c100c0203010f090c0602070b040b070213090b011403030a02190507 71
    0x1c540c1c003098456100d440c03c1000004182c0c0c8890600d12008000c0f100d0f5072084d40d00d0401c2000501805080d40c2d8400b000600a0b4417078100e107582c49140d48144841c4140c0e5100324210b00c0001001007094a4125a02c00d0b40b001140300700100079500d62a00c0c01c4034104c0d8154000c0e00e410f103805040021500041d07d81c054071411101c03071202e0f50340d400811806596007014400d0603501080100186405003000d5908440141444203d00c281d440f030552070b141d42404c1c6118050504824488588042e118000902c980c80c020f5100703982804000c2907449003122009400f401e03005031125285803059030442040c40e4020000d002e041490308004014185849080d92031107180c0e0701c001441400000d0310400c99011804007814203180003104602600f0890007a40c1004c2d845100c1c038035404d1284a1250002d00c40c91803c04154100f041e10059111201e1b0514000d07442040f488041c16000100210744030080c1040c2c50046c070a40c9803c82c2452400e41c0000006040c140d02a40381050a00c0716140f0fa04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 335281798 1250 335280548 335280559
    0xa0b0603070821090f030a20010c0206180a050d080705070605030420030a080a1220040320121c02030a080c07030c1e050f06010b04060c061103070509 66
    0x9440d000b0032501c955041e4410f100c3c0e640f00402c07103210481810080c0c404010024200b2024480351400300e810000c02420403210a98241e00f031174003412000c42c0e0225042c0007860800d00802199020030982c1c4112140c0340003111059503803000d99900c1c0240007014010140c8000d0003003000e0700c1c0c030b0301260700302070782c1102c0c18003c00002050292248040e03030f00c159000061030002401d0140000c40780b10040c441c06405003d0501c510340402d5400c0020f00d041016641c45410300540151000200e51909071115203030b1a84541d582c40f1000c00d502a58190303608015805108200c1219180013841036420b9160042d20130240110302c0c501c0494090038029484030004940781920174101d849205501c0c200000c10031800203d1170701a0483c020f00b50300c81c440d007001c2503006410f23100e80e5200700c110b83c0004800e04030981440c04000d402e01014140c942410010401d9504082c0400d03460301072801040c0c10000c91010304424006142c20054844c0307440c00199950781450040104113502c018041030048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 335283048 1250 335281798 335281813
    0x190f1e0609021216091211011b170901021006030b161106180a0c090c2033040f020108060f030a12031d0a02010f0203041503020a0507050a0b0603 64
    0x501540220b03881c542d0004007400d4580d07181d850480100d82428255010001c5001006c40e41d07040112070001c00078042c15110318010700c44000180281034056240c1c0007400c1e81e401d00000911500c0c9910481666109119290701c12400100c0c40c03c202c0804042103581450700010510844a031140c1c000d442d20b290a07100d04540c600d041c4c40603490200c40383e40035803280000441c00a01002080982c114500a0701c001c80800e44485580d00065040390b2901e0780c1e140215816141c01140b444100d06003099580070b084c0c0c001044d29121046203541c0c2d6003186c080d6400c00151015a02d890f03107104e1500d40c4144035401c080c20408040302e0405c0c030483c08038032020003243c41031030603001240700b10078000c0040800610301e60b41e80f154071641e501150140b607154866148140104901c100c0001c10b0300004003038041c41c1d4000103100c002880888015500204024089621b400c503c2c00300242c0f03d41000351355004c0c2000e040726180703e0080041c0941c00b413885808100701c003420b0310360700451003141100d160 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 335284298 1250 335283048 335283059
    0x40e0903040807030201050d11030906010503060601030b010504150c1a06091005090402010c06020c070b0304110609100804080d020c0d030c021606112b0f080f190f1e06 74
    0xc910490245016039848504104010341c0b1480051940703a29520000c90015020941e40106410544104106411510041c0000c2c20b040100310350101c001d00e414071101c680a000038102d44194021001b81240815040f05c10a004c2c0305a440c1310b035484800441040c0c40790072020360040d01a602e40d0b101b40c00c103a0101d049803c4160080c01900c0e00200f958a050301d403070b40103441d450000c4008441d0740e5028005100c0110090040700c0041002404056580c03500b80303410182881c00b896a21311900c410700502036140c580502403a110344485c03c003510142c03510f0403c2d0305c00b4004d20300f00455490001582c06410440807661070030100d00c1d924140103850107460181d845240c1c20140c0d00210a501c001004401e2040364080d450301000c200303445009000c08501109885010041a007600041c22246081c90b4000d0203040000c02d286030403400c50404031031055941c0c13400780c061404155858030100040301c1c554040c280b0a0041041001070021891a02103400310b0300c05680e600300d244c0000040d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 335285548 1250 335284298 335284303
    0x210b07020610060e04062103081308030105010804080909100501021911010c060f0203070507210c080a02150906100f0e0106051308010c030212011205060a0c180902040e09 75
    0x103000b400002e991140d041600c01c603445680c19165940c4140c84030000607800301041c0055004010f18010315820921500b40544084c0002c5d00345034400003401c6ca60000f2840c80010380781522002d18040510ba00d507801d090300c4901a1020003944030000030240300c5040340000c0b0110450f0800c1c6c0948402c2d80614407485602030302ca2102a01c0e10030200b42d10045507203c0c9034070b049141d10a00300000e860800300c41d0758080780c20850750080072913000200c0c2000d004e1000d02c41603546c000882541c11944038800014541e045116009145250109203121130f00d0007400070100f04510074451485900c1d140090683e00e5506544010382d01d88040300201e004508100c001003a110145040802c0f6441d01c081203601342c0c0250306d0494411542080850070309400c0c081c0010540b26a80d01580321358074400809207070001a400080c50990b82c0e00c1c0d481c00108045a040c1d4080e00000b000a2200c09480b000e88401c0d894a11320350003424420b10200e110038590740034000380c442d00c0d16a80c40304d5a0748a01c555 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 335286798 1250 335285548 335285551
    0x30f01050402032a0c01020310090e0a031713020d0302070314070302090c071a0109050a110307121109100201050f0a0b090f150909011b050f0d090c210b070206 70
    0x1050000364844c5008003010f0090181182c0c80f40f200c40d1494004840040c1d070883e08161270b9114107480c40d0784100070010903801100702910001000e45032900d100e1b940a4625042c0c0c0b0250310388800c0da4000290411444552072040300d40160508102020b00d140094640e2010700045416000740d8650000c8080005000010740b540944003290a8a0741c0c0e01c191540c0d0010202100e81d1201d40d070212040c840b40325a8580240980240811765050031400c0b04103460383e443c894000c1c0038041c02000402ca0380409032494000c0c2c05400020300080c00040c40b40c043c4508205035030081280b460341000181d05601183c031420050310b1001c61502c4240f01c84054546000c402e07a40180420b010a40551103240010b4100c00703030290f500e52544c81c460104c1c4101030122003908071a55910300d04076141c010010f80001244e0b1624066151104c482140610307806072070b41280c0b0042d5598039003c10001000f000001510701c01812403080c030303034044a045110700f10502c211900509030021a07109800060401e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 335288048 1250 335286798 335286811
    0x906020309070b13050f03100608070303080c2505070f1e0807080606091312110f070608160908030d05100e040203030904180b07120c0507080403110114040b030f0105040203 76
    0x100c1013946003008111800c2d00801040740d05000d03507103650140c19001e20030305005000c0040944600c51450a026140c0e8400401000d4001030420150708541e41c03491441c3d11032030040302e0180e03002c0c01f1402c01d03929055031a00510351000c10000041000601822003100c803200460204034002d0311550f036152101c009205402442d882440425010b19040e407500b98403c09091000c640582e4039240d00740300410407040c6e03e01082c40c507080c651484101b4005812400580d100601546150450080032040010402d12481110761a02e160085c842c001801c000c066507800c0f00d84540501000800800b0103613030078000c802c402c12001a41c3c0c00c10701d580c140300d680c00402171403c01011106000c00b51158200031080e010b08000000001800030000038000d40813a0365000c1448050780409046070b00c0140d6610078000203014035800500120308503003c1c0ca611080e010428400400140c80e8454900d040d1249880c0104010602001c0a8041c41c8140b803100300110320740c0da0341c6061008034401940d22 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 335289298 1250 335288048 335288077
    0x8030903070902090d0501020403060b01030507030c09152c0414040312050a02040503031b0d020c0a031202010204150e0a06080609061509130e010525210906020309070b 74
    0x80103006a41d6000c1c1c908008054203690321100b8558486d0b08a034000d400c22542a47d441c00c1503055940e142c480c140e407114507401c0800071110180c2018007036050f83d00c10101008000c4c1905141107201e04a0505285280f10001c034071800212349c40740b100038101c140b4500403454811980c480b504038281990040380c0640f90b14000801a40f05a8043c01008000b140d40a408100c00540b0707031400c00003000400011041e2500780c075184420075040200702c1c201603085601c10042150b090f5522401441125800141801401401407050740680650303400000240d01d0300812190320b540060604a01030300c101c4034482040d4840300c0c103965203001682c5d09a0030450180c001680c81c07c007071303e00c0320408004081040c1404a5403000030084441c00724011240d9848050b142e40b4a102400307115085102c40c1c0c10040404d010359442c034000041c030f0841d0000c00103400144d09803002021180140015044014043d07680e2030306000d00070350310640d81070313010380b195020002d107003001e0405540064020410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 335290548 1250 335289298 335289313
    0x902030f012a0203030c221212120c0210090c0e0103080307030f110405011d0301050c090406090903020c01050307031104030b01060f02070f050402130e011d070807050901110309091f08030903 84
    0x444800c5039040404c4142c829640e810200c0c007503123080c0030a0002846484503180c9180d0080303004009401c604804103e05d4203064030001d8454005c58610031003056540c0009045440e409c080b201003039503600c25010320781c41030004000c1c4101d0340011446400c07a0749060004001e000e205200700c40303080c04080c0d0a21004e20041c030103503110700d07070080c0c0014801070748500d48011701000900b11282070390310300012900050b914409050a01805000700340d1568104110b4501e51000303505e80c48803c00c52030403c440007000540c40c3d0300a03440300c0082402d001c1201d0700d45e80c40f4901004042c0d001c2c050070012483e0296460f0f0403520004e070b00c00035100d0300060101d0003840d01c81440003030b401c113510070300c00c603054010302040d44008040c81a000305903900e0801c88030840417210b1055941d0140c54641001160001c214030150008202c1e003001c04c003803801d42000048040f00a0943c0a20701a59078090051018004002c00c8030070700c1c100c048511807080503015a68901d0998030320407500015010340001d013 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 335291798 1250 335290548 335290567
    0x30801230117060102030d0e0106090b01020303040b0c03130c0602010902011d030d0503090c04050a021206010f0801030b0c0f0304030f021b3a0b0a1406130902030f012a0203030c 78
    0x140000c0c0c0010040c0110390404084001f071f003064806026a590541c0e54401c0f04101c02d04c602d000c0c0c003100d003c1c20700180d4558105600c801e8102c07007005080c036501400020210300c03045409440c640341c80e070f04850414200c98407904024042c100d403030020b0340050342c051620000c11101800701d090580c0010001e022a4072050001e6856070001482c1e42403d0003803d01441854917a802190b100e00022180142e4581203c8500c0d004d00c28050815410081112185406070350002c1405054039000f40314403449554880a4600030701c02c03440c0c030489004020007030008140d00550094003100c11a000e0b0340c02c1c4104411446400078002d4202c503030001c448098110b070002503803c0d90034000100403c00100c150080c2d803800461024510855817030100b0340402c2040360701445060780c2c95400703080030042414158001070400710300a000610040e0341f60a0002155010010402c07a12140070082c04540110220241b510300b10031441d28030f0780015403003100c03000d1011085070702c00c00162610b04d05004000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 335293048 1250 335291798 335291837
    0x1805120d0c060b1009091406130e01090f03030e010e0606030a0303091b121434051521040503071202070503070308030105120705100f030908070308012301 68
    0x1060903140c081d80c401c01038010b904c907a804c043e10550f454603030f4031401e441d001850048a0700e08404010300030003502800750701d80c1d8001d50002602411807001c966440c405030064014250300d080200343d101407900b40d408060300350b00400010720300c84008210b0b1303a00d1407440c6078468038212242da515070410608900001d000307610200446015500c5003600b21084001e11071048059003200081c040303240109000c11101001c06824140382602402c46107005072100b038810352402c81c1001c518980c0d4031020f071a601e02081c0c2d03038006100c02010300d8036100340508010308a40c01220710308604100e030108011100c40800d0722601445d403040080d0704e050b00caa11005052141e5140e40350850280d1480040c0543d0704100c01d2001e580100001c0340e03294500310400c0340f0701e1214000301c40660000d900400076555a9405161000210704028082e0140084210020080d000008150400100f0b0f02d00c10702d0b030b004000710b041e1440074001350700c0705400140d010304003500008081c0c0022031031809030544a40c0c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 335294298 1250 335293048 335293067
    0xf0901090e1f0509060916060c1b03081c11030402060a1b06050a180209010603051008070e07020607140313060b04021602091f0506130f061805120d 65
    0x20141901d00d000c9040c2d082c03800700c509500301c80305040c1d1a8001d12120000600040b41c00110000c020841c1143d00341804600148912854086c0300412050f04140031150409403808a03141240c80f5003a510b910341081c00350000040c6000c59110644c0794450710401e40300300541c2c2d954800c0c1850a5030340b9642046100e604c41c040e40401c01400700401c01945401d241505415442110f02041c149458031b1903c04a448a4034a41c0c20449455220000342c0c41d4480c450703040d01c00d603140114050b51907007060a44c1c0301807030f8414007851080207400120b8103803620003e030161010b5800e9074580d880308403040380c1da001c9000303219004036010404a810174441e202d00142d2540b18000c04140d051901c0009002c0360414410054038920851602c021890206201070b4000d40703403070f9580d07003004402d040d80300140060701a040c0541000240880031500665801c401800e4440300d101c411921010010150741c82e0323032802070301d40401d81000319042c40c1003181040410358040040c51039000c46c21044507501034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 335295548 1250 335294298 335294321
    0x10302070203060c0408120f03070c0c080a0b040c050603040510051e04080309010b120703140304170d03060506041203030b042403030206091c050a0504090f0501090b0f090109 77
    0x18200030040050700d0501610340b00304010071401761560f03d1300b240ca600f0400103a26150900783d003080740416040c0755405aa80110031850004c80480e80d92030441c0b40c1046d03d81040a02d1302c203c44111741004407640403244241d01c120200720f0b000d541c030402e112048c0429600103126422030003620440407500e910040e44480108011020000346400720314000c0c41c140c80c1038440c00000001c101041d00240103070620100e0035940d0301c2c540100100c65640341c0c501804028103d030081100300008030340400c2074030080c00c2420700b400e07103e04100021130b68132074000c5051700120741051800181450488180c4040790700030b1003200350300d5000356401c4004140c9008401e130f0281d900c02c000c12200a00e103262141403010040c80c41d14a506606002c1e141032002010384150341d0009441c2401c00700c400f0500d21110840f810429201c152b140401d03546801a50800d1005900d0075000b03003a4403030140c00c0107040354034030300d030812400c0014001c1c4032440c07980d0200241c2002d080801003104c0d10440e40304040111 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 335296798 1250 335295548 335295551
    0x12021c02030d14120c0417060408040510140a0305040b070806030a0b1909150f02041211011b030201090c060305160f090b0d05040b1f050f130e0a03020d110601140103 73
    0x41003440441c0c580d80c400d84080d844804040b1b07043c032420703589240407100f442c40d03030008000b180340c0390b82c0b181040e01c1140200740c0220350b5070b105800498000c80b1640d940b10303960000e143e01c5401a440c02402041d00329002d8907a080400081801c4c41d0041d41003a0054030090082c2240101c19120b0303101462002c1c103443c6060361a4200d021050301148a0030b0b031443c3c442c2c81d00c0c0304460080d0340104192010207400700355031441004200840100041c0d841030b5140d0040190510010306c60060b01c0d03001e000c5528075903106004d0110030406138194004d0340c1d0b140c82082c100030001d49610048040b20310466003001c40d01c840c640c00301016401050145140192440d01140390360300c5019100301500319441c0d2038410b0707450b4030a100c100889000c2d0290321a4202c0c540609450040c05441340c24800b601c0750364083c40c1200020841c6803a00800640c4100a4902c180000100e15041aa48400c0031900b030b0014041d4865141d012440f400e0288410340c00c001c000c00c900d900302000d18095100c00380c1c41c2070615 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 335298048 1250 335296798 335296807
    0x60c0f06021b0604060501030c06110307020d03140c0d03051302010e0f0f0d050309030d05120f041a2d1b0d020c0f0a0c06090b0711040b060412021c02030d14 69
    0x46800c101e03070784c811442000003045035495460891482911500084103000c120851400d0303445001099171705041d01290b04861401103801d040d40d07850b60f00c1690031615000002c000b51550342c0082c0c400802400d0740d804001d103694413a4a06109400824024005490018011054a00081400d1048100030000d00e400c0e05008001005045200d070101c0e2030380c20215006d115407505105820384503a550402d549008a4036204808040d001803103850001c1d1020301050500c0070b204145e8042a0f442d0f81c1070402414160410690103d140c08546c00b42a00354a29000760800c4044150083c24001d0401549920703000300725180d41c110784010190780c1d038240403080c01c45608105584200017880003070014185103003881498005903420410a10515003400c10103d8460401c94101d990000d0300085080d0b0500d0000c3c000d005c1b07003c00c455000b44d001c00d01048403183c0052001c2c401c1d10864403010035420b01001c600b080e140505000e03505800c9211000c100c14001c0a8110000040c858490b250 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 335299298 1250 335298048 335298097
    0xc0a0b120a0b1207080601050a060807080a2003061c020604140102120a030c090602030c0d111603060515030601080d18120f02041109030d030b060c03030a15060c0f0602 74
    0x1803c9841c40011080d51101c0010040103505214541c054036050712054001410400040d1541001600c0c0d04c00700030442d00080c00c2c1c424182e002c05844910500404100681c0c031004c4003c0340c100f598900c2c407400d000c8060b201061985060500041d50143c01282407030318121021035038580c03c50100c0d0650044101e4089400c000c0f9000340004155510001483e015a91005100d040207800400965004020001c41700c200001c4145031030290345003c0d64000817441c0841e05240003015000100d005a03100841040502d410a0b84070b00901004a41650254000c0507501c070310030310540040d6001000c0c0321602501c1440304984200c1c00202e10307410302e83c3e034800610700549400303001c1e51212008800c4008502e82030007171030103181078803d20900300034911000a0312801d0515000f410f055686400d208142c07940d100741d0b1b0000da52841a01d459107803a440380e6000d4108a1444052021002030100e4203500504000540540000e651000f146090b0780300d81c020b520640c80390b004031504031903c404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 335300548 1250 335299298 335299309
    0x70203070b0a050121200f0405090f0f01020403030801150c05031803010c0302270109091d100c0507140a0c06020a050607020d022e1d0c0a0b120a0b 65
    0x11010704200040711343c58030341c9511108070305640001d03810100075031040c003066039003100040388611881c001148a003118006050880403e0b800340d0068201001c10407000004205400036010804c19a616030740f4000940d8202c1c841e81c080200803d041000600036502c1c40102d1001404144c101405043c00503192585503400c6003020702e406100308501d60010742800e0140071120406801d040d8103100240304504c0c7d03a448514403680121b06e0856000d000c0740c1c410141c080003091100001c221081951501120610010070f56680c0c5215030041d00404030050703c81c01c2d43d02805540d072642000140d61360748840004c491100c01542c0300d00001d0304c001c1100c0321070b03c3e80202035a40013007220707444520703003103080c204020512000c1d9004446800324494020030500b005006044100400c0500e280f4010a100d080207260005a841c10350744c20800d1250400200005114030222280d6010344800c1000c2c8140e0380c0100103c0030340600c010300554841c00151604104030010116075111040046179 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 335301798 1250 335300548 335300551
    0xb0a080c0d060e0426160302150106020c0901050d03080619031203020a110a0b060105160c0303111005010f05220906060f0b0403020f0909160e01090b0d020315070203070b 75
    0x165020b00c00c03404d0000b00041c1030080c070f402007029038021042c80c401710425000c4d4010004403540e020b81c500c0ca82010188240001403800c21200014580c0d96110b000003592035031691030050140f4260400421039242449906c4c0701c0030f030300d5a0b42032040e590703800c203000080c800d4002c150420981c9032390100000e1078501c101140b140050383d00580b6a203c121004084010f562090149600131261902c08182003c1456500c45000e00300303690745d00e0300d1210860360901286005420100c480c0d00c080100750f030265030944000350030412034903016a03010002040341c40030321550074088403580041003a400e110044040360406071014996018034050702c8025909104000c88000d40e0b24a01403060300001d0360b5030710140110040c1c2ca802d19047d98045100041c640112070b10038100e80c00011014001045140d1501c43d490742400c55850740e404845015041c28082c2d05003990509480d04914281181a0003406800030010102c025005001e1080d1010190181d003c43c0801c00411020400e01c034541ca = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 335303048 1250 335301798 335301809
    0x1a0f010f120504030f0905010c170f0d020f03070215071b03050c010f0606120b06070605060303090604080604030318030e212406030d08010b030c0702090411190b0a080c0d06 76
    0x104520019880244048816000340c0e05101321070410f0030215420a81644a002b29858420ba8403190103c40c000c80303000d004620b404031400091450700703864083c0042c50261205800702c81d0b8943d0344e100703d210b544104680d001d00050110301110041c2d009501c109000b517010303080035460171050b09915403d40704110507104440d80c455404200440e030010401c00e0300141c011003040015040000240c03644243c00c3d000c0e0075151640e010440d5035a06100700ca045240050000e42d0b515a10a10380b92121411038040c0c1c040317031030200c01c000408421446103070725a9140c1d0360989550391040401461034440f0352190700040082042e0001c407182000b86c1d1094041c14003103a100400700c0e01000c210110010200d81c002c0d00400d000342c185581040d072081c159844030b80c031240c0760795601241000600446201075840030010f0140320500c000c503290010107170345c140c900c8415820004c2c8000c405410034030a0039000d000030001d24405910078030065801000c49401645004500706088094a0158214 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 335304298 1250 335303048 335303057
    0x302070c0611070e15090a0608030324040c0905060d06080601082b0c020d062403060e06040b06240a050a120501080a030305040201020a0f060e011a0f010f12050403 72
    0x340e541d8850400030304008029408501d44c0500e4410000f9941d032200b1450a40961021404245900400d402c0030000c0c1130044102c0b034903482c0036840c00102c0d2100015285400c4001e224800c120700300390140c0d01e1030454549640010130301e050b00f48803184c2e00091004040a0b40d400000c94008001c0c04214000d08002008060b08a25001c81c0740c00c1d0544503000340050a003040c51000d03280d40100348003446540440d41e082d0020218100035002e4003000c503900280c20092290b0381900d2045000c2c4a080d28010b8504100100454211a5542400303480181022031007000003080c03031030500b204105011483c800c048210186011442150300003c10800100c0c401003410145030394072001c481c3c807010601e041809254074140c0882c1e00e170310340408040c040544030000a015a40200300719405958400505003010f001c40c01c007840100401c040301b10842d42044840850030002d42c0600340b41c4000104043d10310b0b12050019030700e00503032450300b07020300101c080458800c00c00c40c400c2c10301c0703940039444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 335305548 1250 335304298 335304317
    0x2210607020c1c020613180504140a0b010e06030708120d150f091d1f0f0204140d050114070f0207050909061504020d060902071104090b070f0302070c06 67
    0x1000e400c1082d2034840d680120038500380c4521028031071030700110542d01507455690318103811614040382e44803038025442d17100c0c010441040700005507000328825400307402c10b1305d156490142816103035243c0f01006084610307540014442c44480b007454580215004007280e11032540c1d00186428003640b072600d08414400442c20b1082981c403402003400c050101203000c40d0701c0341056010490b44125002d05000c0c20754600c0005100403084c01501d50b0361240b401200c03042e1142e5403155039109260f0950011050a101a011014001d40266815200c01d801c00d480b0b03072901c80b0203102541110f02c4064a0070341d2900e461101c0c00d11100c01d0107001d03100c184d80300302d0308520500d406403a0041e1035000c01e02a009035010015030034170100b040c61304403c03500c0c00160058003140c0060064090208001c00e130910b0075400140e6400a58020183c8a204012003400402403000700302c00c6404145e40030f00b480c0c820038001381046128520307801c291001401d006051201c29242e6000a1016410403000b0698480 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 335306798 1250 335305548 335305561
    0x6270c04120501140903030402010f0305040201090f0e061801050109090902150406050c060903090f010309020f150406030515010c02010f1b0b0601020f0d0e100905041103070809070605030f04022106 87
    0x4130040c2d0010f84440294510305003580001d21203a80302e100102019a40c00118007160320500301e06001b80038004038480a00d8841e044030700480000c1c0c4403148503124617444d0591a40e081c0750b80504942058440b820300c02d1402100501421b04048226440143c101890300c0080c9800d0192001e4041c1d90303101621103e001c0c56203443d01d9005041d0070303200d9209225032a03495454420401e0009000c1c0f9012550748454400306240b80710660b98a64800b080703032101c01400200c3d6000c0c0040728040e5500b4010754403440000e0f410301c0d6254a00d6400501c4d000d40300c5004d5400f61402038855182813134602c441c54885c29529000354a5501c0444441c640c0d001484400d42e410054041c0d2800c40700040c10100006d4000a89024010f40056005d004032500e020103d07801090000001c150180003403140440300c2d410030744140c0c4121550004180102d011031260b46000603180c003030390403945401c0d1540c2c68a045d400d50540c001002240d0182c03170442c4a01807407c5c6000132065811600004240d03a0900c0c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 335308048 1250 335306798 335306831
    0x1803010e0708580806030c120c0a15120905060f18030408010606030b0907120b0105070501050f0709080f0d0305100302040c0806090c340f0c0303020606270c04120501 73
    0x1c8148004c1003512010b10540e6a00442c000100a10841c5c1c424503002d100666641000c4401c2a6107038012040900042c0d0600489090314003680d03c0d54039110048585402c000c215000c0042c088c15030b03846480010240f489440900703030449440c0b001d40d40d609000c11007503403440c0d000d600039080350b0351168400c1100c25010300800440705004c4a02400c686088038000741003c002131410303403001d501d50b402d421442e401a4202c0d17240715007103070003400f030380c5002014030070126803e4424100244003010001441440866001024429400a071030206088502180a4075018201440610f40340c800000103a8981c42401001d01035601c0702101031404108000c00304500910b0400200004c001055204440c2e6040d003880520f0942014079910024504034000101071000800f29500707a01e000061222048501d400c4074800c0d404c50b01207517194403d1001c490050046107582c04010f03000e400e001810740c1f4840e03500c8800504041d051550369080340d242e5103051001a110340e55503001041000646 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 335309298 1250 335308048 335308213
    0xc09090a020408030315040f020a05070c050604030f0605060102280c06020607141e04120b071e030902030a051204050102061005030325081803010e0708 67
    0x480340c046042c5894842103546910004013204d94038603100d41d000c91190748551110000c40640d140464444880300c038050403d40c07100c40d09446030340300d4840000f242c0c0303007410481e0f0039a64080892002d48210381d80780030203000003500e043c2c150301450380310396508885e11141c016006802c10760502d80f194036080c000481655074220108542240c8100400c05070809200110b00b60310782030300e40d5503110815102e1410f481015008030301c81c10000b4009607000402c4942070745503018020741d40c0103450305e000079101c0010300304000a1914000450380019400f03940b00004660015040e81d1401c4400da403a182001001044601300c1500403905200325641040250b80c0140c1d000404070819087c4070002e5628011400c420464110105066608200700032000c0705656000d102c20b45ca84100303084e18000064060714140c002d41c0b8001744000e8126000912104690126001c0c10a171802a2020b1001c1c803c485842085914944001300b07150700d1100a10031040303581012408408207040390389598454 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 335310548 1250 335309298 335309311
    0xc0204050f0709171204060e0a0803070b04060c0201020c0114010906060503040f1b1502072309071b020a0905100506130b250b1f0b030a0e03120c0909 66
    0x812007080007040e005030200090b2a50880032800340c180c070138011482d010507091201d100c0c0348013090001b8120b8110500407000d00c0121043c14640ea00d03081416030364010480040c09000c1e803030010502203106984030500d0060280300140ca031a9000c0b100500303540d0007041d00080700501d03d0042107038000c20701c00c003400703440c86146c091315504154403180715000000001415000d03442c0ca40480c000020800d2070003c0ca07042c80390310b04222040601035111001845810404139010031002075112820200c2071a115006200000c240c4940c84200c1d10304c60210003130b000b0710102004000140e078840e01440010400400042680d01d0295004034100c2c1c0c15510050185100303000c8080c18440540d00750003501c422030f403041c6d1110039120080d601003a40099250044580380002420300c0020f80e055849150440901144414061890702841da454454511802d4042c80442c070b00f0b003240e41000914103402c000b12030900701c54283c110508001500c0075100c945000400c060541442000c1765031020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 335311798 1250 335310548 335310571
    0x2205062b110910090f08101401240909020f030105040c08090a24050c1216020c1309230105060604051807030f1b0306050303160305130b03070c020405 66
    0x41d0009064112402200c1d01a8807450000202d100340c2840380120000801c0e284503100f0b211981c40c601991642142003200200c1d5048c42542101e1000044905040364030220386240c407034107114010a45424588001c50812a1502e80090848050b0000d0a09011090821507a0394034003030030030003101c807404800d01c1031100e22400c00100b4031010618140c1c990b001440301841c100d000c05c0aa074448076800c2c2d00b2061324500011301c101e00445102030001441c0034200c403000c079180c44c0c01d29011851091752a5006070310012a0100034200203408250380200e0703203004640c2803103a64071044044000300750300e1400e0341c98004a014841e42401110741018040d200309242505102c082000091640e07900c1465862000c0420101071084c0d00a180b100c0440c201004400341c100d1041d0b5901c01c0b81c84e0750000281c20407101081d40d01d000320031101ca0036001e440e180c2a1500b5980c05a54980226800016450001500151400340c48000b180b20b24455905d5214044862042004030741001d400c0d501c182 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 335313048 1250 335311798 335311811
    0x31c05010b120702030c010f02040915290f070803091009021f05070b0f060112140a0902060f210f070206011a0d060b0d050c0309032205062b 62
    0x11071200201d0b1011450200e10300b0325a43c038001c041c1e01d14416000000c0441d860011442408000345e406841a201003980a00c8609829001200d406c03c542c042c81c0d2030803503041e01140303490f0709151003d51529404103069003803001c1103000c2d110326041a10180c40c820707400030810110344000d00c0f04015204280d4010480d0f2006600030801204034140c030800b01c0311565004645180c01803040d511400c0e032020200d10a8503050455403031002c810b403001408906100007800703100860340901d100b6855140c144a5641d43c0d044036150140c4020641030ba003020003007049000f20040324004210000502030321000c0ca1400d20104030000070002c0085c0301d04403070901840f25842d03001c1041411180d035038445045441c00c0c980a05c1c3d09100f80e0029410051a000c03000800011b80806081440c081c908100301d031390b88181c041080c51104403480304141d0802c1001c2c5206010300b0604c986403114601d11081641c0e128808600036522035850b040310500c44500c0c19030130420f80a403640c0e10281c07250062124 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 335314298 1250 335313048 335313059
    0x305011e030602090114032a0906251202010c080106031b030902060405030102040f05030c1002250e0a020d1b0e04020702030c0301110c060618181c02031c0501 70
    0x2054203000092480f5000516a255a8402c45043d2221200220f070f00d60f03a030500c24404042818201d003000c0c001d1041161040b4a040c00304142c074060303800600b98030b24041c0302410107200c0c8043c800c5075040c941c9900c8400e001080000407111449011500002941160600080c0010005910000400d801e00d8501c07005524580b8010000448500300860365603441d10018980740940c0c2c00c43ea0301584041000a0903030048540390081b1a009c3d000c0d00c1d0106441c40c02e1104205020004a02580c89403403125501580405d100315240e6150400900300d5480344030007002200305850122680e034010035900018034852245080108021095102d4440070070700243c0505520100544600d40c0492683c041d5101400507904080006000b0042e0070103448103642c094100c240042000d104000000d1400d0801c006507107041800803d81c00025680d00e4040214211078640f02c0415014210484084601c0340341840052486c1c0d030051034031407001c60343d080c1c4961501d0002e07021080c02d11004111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 335315548 1250 335314298 335314349
    0x614010903030503130212011a060909160c1e120306060206160504030c0b0301170703020603060603041509050304061202040e071404080d03060306050a0e1e0a021201060303030501 79
    0x1c0301c0c1d00d400c2450702ca0340c82c914121420341600c03001a4000003005050380300c81d00194440d14014000d00f040115003000901440100c0c00344016450b0049150700c04221003031001c0f219902d500345207240a044c1c04010366640c2c0811034504c4d50004104000100e56420003000ca1043d550409842c60100401072400360020b5031041d01030b000c8a2605400020030302c6880c03284048501650300007000e500ca05580795500305043d802445224000744091403a01c0705c55801240300c604813a0014042e03030860701da000800c5440d501c0900210380c000c0808501018102c0103000360074100d4000c0001d140c079180382040c0034052003920844070550500c10001800300c00810641c0b81d40048281ca07016039110301282e00d440b414411034014180728841c084c40c810842d68146c210000366071107102d082c040c0361907030324803032090341d2404207810001d070805103410300c8941c580d1803504e90a1030003c5c00c40750302812903004915a03003507030086403003245d444202c14400c0c95014040c01e8010805030b4a02e015040f24080380c04e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 335316798 1250 335315548 335315567
    0x20403210804030807140f0301140a180c1e0801050f030a0f110607150609060b190e150d0e0705010c02030304151701080a0203010f021c050c041a0a03061401 69
    0x8082c0138422000c150310a11a07400c10919051444129946488041401741c59410910814101c071140c02c3d0308119a00703161140f07134122800808071050344030468450401404800d1100002c02444401760010b40c0e00402c0f082c06400e003030b5110a4800d5052a00b4000700301d0364615164004c0e840070070001c1c0001c070360348442040c964019158007040c08500001a00304d214204020b05499424074964200d00740c036510000840784905400c000480d0b80d5610185140156105401c841304407802d2407041d24003942d81182c49902c004d0000070201c40d14958403600e6040100032040043d0b079402200500c00701000044050a02400e029504c4402d650000c0da81344103602070300b94001141e03007080c1d9049001e4417498111301c690240c416220743c1c4900c0e000d640c1d5010000d00703911940c01d0449440d000c911610803205441d0b5614035040d61038000b900308901a0070050202202008100000108000d02e24030f001d0204011903001565014221070003030542c0c0c4242c0060b502c400803e1802c00c00d5a80008406 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 335318048 1250 335316798 335316803
    0x9030a031107051c020d02070b03010509040204060e0903221a0c0703020a0303080a0f050f01140f060d0204030b01090c1b06180302100614100e03190501020403210804 73
    0x840c1040031401c11145a00801ca0300a115100342500c81100104050109a000ea15542100c104000c004000c0340da40096120b5501401d004000510003801c10109180c2d01c50300140c00896031a0b660440f05c2d0800804450f0200a5040401c47c030a800703401500c0b460010224580002e1102e080030340906142005012811302e0394000500e1081e00b034400d025040c0196001488203000550b2800e01420a10040325118104c40c80c3c0b92100003025018401d00d40120480d40700c408513a82401c0303042001c040c441e00f4540d404122485018820707510030004200005805c80c001d6101e40c075519280401080681000185604191429800c0c80d80302001280d04441c4040c024151001810084014550303080c0c0a80128045020001850b40000709403080107007401042000a907600030b000051600340590950002c00d07800340703009403441010342c4419a8001415580008810581d030443c0d41599002117490f81d4000c501001440180c0100c044a640d5812860f41168503020005110701d6006200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 335319298 1250 335318048 335318051
    0x503090d050405090c160b0403020102030145090519050c060c060402130603020d1b060216291b06010b03060643020a17100b0f04021c0b0909030a03 65
    0x20070b140100300329113003c0c5401442d05071041c08c00d414000d001c1d40c001d014007510b9920216401584038821042483c80c51765919a15903420200180b10640c840181c1c0e40300820b545a0403400c010900510028030300b940c20b44080e10b202e80041ca046802e049201040078802c03a01804181d0f40014080b41803039120341c0c1294081e01060361010500010842604081d41000d201c0c031404003049401d021650212041501c010301c841d82d1013100300e0340e91010700b201e044581c088400030045442c1d408051030100f449120303148101840c0c07225204841e000030700300f200b51503801e207200c44803c80b06000982c05490710080440c034500d42100818802d00c15a040e44114140c1079000c0d03c0b440301f419858080d59080f0302484c4801d4400805541601044210143e104000144001a00b400b0942047c0310b40d62006000e0140d261004c0d80803401081d0000640c0d800403140416100c0941e550f2004100140624035501100000c4410340d41c211100f0f6504a0b01440e44141400040100041940c0308000285070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 335320548 1250 335319298 335319307
    0x30c011e0c021807020d03060504060b09040b0301090f030503180313061107090f0b04050c031e0a090c0e07020c01020c0112020a030f05010e0915070801060c0f0507060503090d050405090c 82
    0x81681c007490812541e410f5018102404001540031403840c22400313565805100280c1c80d001000b04580c810712410131b01c130a04000510340307400d26820a952101c402000094024800d84950010011b080310032400a00000200020b05c5070056540c0f01c41110f01000b103050040d0200c1c85441e1341d046000b100c052120101505961010410001000d0010110140402a9412004405441c1e9040542c0c030607810100000c85a841c50400e80748980c40580100141262180fa0064410f4014081440113070f2156441004640d01d1104c1c60010309403980075103aa4034100034000d0503d42e101c1d04803411500026182c01d1a80e0b40600d4001c507400303010800580d80e45040c10150004d0507100784181c40d10741010000100e10411103c040d100ba55980309854041c00c0c1600032044240c411202792012680020051144030b1252101019803845400d1003012001541c403814506a110303070004000903c00410007625210901800c1031810544c06d2060034a400c24000502010008064500c120030106 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 335321798 1250 335320548 335320553
    0x3090c12080c1614010c02061803030706050403050a26061909090f02090903120c070206090d0c0906080a02090f07020a1205030f0601110d2d02010605030c011e0c 71
    0x1007150200350071070b0304864007060b4071040c030400c0f840039118001040540d082c01d00c400d03500400c0c071180e160b0750041000340b4002071000102d2908901074242d40c0c04d44010700107c030000b249480307014000c60113030319200d0720380c03100e024014030245207803068441510102c1152504003415030070301d50308140c040341c80c22518408c22410440907000c55121001407070520140406128000f00c40d8a200c60003680c4400d0566104030310550350344a06094a036100d580d91002442e81007600010f010414401804989072210520010710703031800d40c04090b500501c480d14200151031ba544a440018261a0b0251a01c042960000b47c00c40078024040b6040c0070a0301c002a400500c00c0c42006201c95004400140d504200c00008007a07400490704103105819600200d0710320341c05401d40b81e2075000c42d07500800301d002061000f11100560b01c91011040380c03e0b420a5014503440c0200001c0031881d40d4000034259190404043c94060310503107180c1413145003000c0944400e09120310302c50064a50401181090403031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 335323048 1250 335321798 335321813
    0x2120a06081c1101090f0210050f07060c0c020604060305090f01050915130f14070902070c090b01090902031609120206041205030405040903120f14071206030b010906030b0703090c12 80
    0x2620f90f415500e010150b01c01c000000c0b44c080303403043c020f5462078552110034909450b54424248050b107507640c1032050400190b5182c0141d051250649429000c540e11a40481c502c0c3c0c0264100710082500ca00c2000300c4400c0c10071031046c0000307002000f4840390030442040e03611422015000c00107558840002518420b11110920300640e001014411950b05030400300071071212803086141030300175144005011383c0345000f680d001030b402a8000c0105480c0c03503003080041c003c048449050044040c40018690f1152010318403400c1c07801c0a01c2d9214040c448001c0c1822955000f217000004000f100d6030140c3c8900301078034140c80c2000400c1d612038503a07042c460701d0f60040e540900e9005080520030403c151b4020018448821209800d115841e000c0d04664142c0d480904960b404407250000110400d2003107403c03c50074005d43c00001000f40e202d072150030703541d602600300003245074039004104100900c019125074000454642040550074664413001a01841d200b44c41500d01020341c0c1100b4403618 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 335324298 1250 335323048 335323067
    0x300c020f06040902130f14010c1425050603010b040e09120c0d110d080a1802031204141507020103020d02091e011e050d1d06090102120a06081c 63
    0x52000d501d42d80e5454104010354411100080407001d9400f0001d840600c0400f55000d80b103100c4d426520404040004549414403050195121102030340c604031415814082e01c407001c80040e041c1e94041130a03000140315800c80340e1086006107400c100400800030f002003914150799490921700c1298558690040c601400c0b000408070703803c0009a00000c0700c40004031030115510580300e42d59a00313402e9400c00d0301c82510703900d0503012400c1030300040c01505072503100801141c42d1525964000300103401007483c2650041541400e088005001d100b141f143c040030b01d5006104441c0c0c00c844c4013400100c2c111a0094420080c14982c0208244501190b00d030150780d4142d0000d401d00c100ba4003000807283c00c1c1401c00c00c12502042038481402840702c054910117860b2070340760b240c1d24a00b24828a0078401001c0151000034039244802280d0720142060241900030105400096101d140074803179100150070103030401d2115407800000708000e490110b0018040101c410032030010900104060321140391 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 335325548 1250 335324298 335324329
    0xf100201060f180b060304030e10030e15040b06040513030e03100e0309090a02030c070b090a08071b080309010804062c0106030b0c03040b010b0a0207090216300c02 72
    0x10904001c0f481102c0f050054800000c1c154050000510714410b1040c28803040d0b902400040099400144a00302948440e1211406240c005140c4230f02030107490501015030b0031a462000d840060100344022034071400d07000030044034108034504005107400410042408004d0521a50721101c1c01255010b10044075403c03041b0b02e0600c403c208110f0103d03203940c4000e0203e441448400042050112a842940c1c807134140040c900785021815150ba0b105d180001709000041c0c41a10745681c00030301d80c0da000c2c0800600c03c03120355a0301d28140c18240105000b0360000700041e8024007086000f80e0f03019100c56009038001d00c0004050680440003006003184c3c1e00e101400402c0d00208c0020f1003015030102e001c5074000e018141c0c050f21034030a045103901c0103a60140c07003801d40000511000803030200074414810b49004468a9940d03d000d141c041c1d8200500c0060300e8100d9101d6242480401d051b0400c00000c68040d00914041c116114109611074000182c10001c50750412000c5413128501d5102c00385 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 335326798 1250 335325548 335325569
    0x319020907090b07030323040c05060705010917030402100e060301091805070e1b04080303280f0c0e04150e13020d05010606090b190c0305040905041202010c09050f10020106 76
    0x40a9040c0600944400c1c84c07002c03c7c2141c0d005030100e05404800e20340d8001d90b8043e4404044c60310740030800c01d681c8c02a034800d4409540e10f17003104000820072101c4945503104d0702c044c1078403860709004110b02c910b0100d2591090003600306000d030031a600c010459040d00c4a0302d10000da850100b0120b03805034480e07100000c01e1849813450101e020b400003412140f1940a4803c451100000c0c2028200680158450b031035040c2d0082c00800d03200400205038084603074803002d0940e4001d8141070664142c03140c05c001103031840d0f640c207561009070358008039007128001c043c1c4007070148098000281c0403005152050302500c2090b600070842aa10300d02940d0006a001800004500258140b00b8000c1803940303d00f001041c8500d00000700d585102e0283c2d03c000f0607140780c102c62015443e50030b56500b20712890442c100030b400c01c00458090700d20b10540d0702480c01940188045048a18043d084440240c0020140b141c001410001d5641c1c014882d0500342d4144c0d1802c101602e040d00c1a4003600380d50300300c500f030300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 335328048 1250 335326798 335326807
    0x224041110120e010608031207030222050f0d02010c0b090f030a08090105060f0d031407060207030804050d09140f0d1a04031206030c091e0203090a110319020907090b 73
    0x1c55200001a4100e04038800c200500c42043e101d0302d0807a201480340030400d400901c808014403102c003154651126403400c2c050300d0100002200c1030501108944000c5546802d4001d2166040000400c1c94100b01556020880c40c1d07250000b8102c040c0c1804003c15400c128000030703000c494140041c008825261080300d403a520034000181681034111149020342d03190900155291400303400e80240c0f0f103c098000707140c14900741c03000c03191901700d08145054128100032000019105100800720140a55510040360610745806402c0c0118aa42c0400300080d145081c441c042c03242c1c1012030080b80132695000100141008aa200100200f000e042450402d24009181204000340d600c0b0f90310036a248a035034080c4c544800201e4455000142c03091001c0700d0309115892555214101c02203203040d81001465030ba80d40c0c481031780e10807030340b203401130704035801200c10004134507090440701600f180500044000f40c1d003040c0510304c07080c8000c2c0c401c41d50640843c2a95005081c140701070a041088950b48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 335329298 1250 335328048 335328079
    0xc08060907120c0504050f0a060c080d09050a0609260d1d01051609120308010e070203270a080601080c0105032e0315140a020d1e0e0d02240411 63
    0x10340d0030511406d40550503000b9840e1041c60031094107026189a51a80c903094800c9486591440e04100f0407040c000343d40d2805140031880400c90020000e00c2650041210601c900e042e0081041d001c55048120418414082c054100c11094683c2c070880d200d0f0010f20140c074151144109240e4981c0d04015500e00390910004980d552a0b05405001640340c114140741e0700c00e40c038010402c0d8000c1c080c0c0092080320050206d070312503081494002d004d62048078100460016542c012540300e1100305c81c1a0004402a425810499154402065503501514096240c4035030aa103c0d040c0b084824100800000010711480310200282403449803e2000f4190f03003581455441c61b52211300040d543d019004204004c0304800e80150030414038050b02194042d2661800341d000303500301141020300651124180441042580c014105d4908401000f00718840c60002c40340c00c005484c8503c0b0110342090514101c0380e068600402003108018410192565a030304001200c15000c10b03030564042400544283c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 335330548 1250 335329298 335329307
    0x103080405041113062f0d0e040b0616080f0c0102040305120304030c020108101706010518060d0b04020d08030a090209100f090504080c010c050711040c08060907120c 73
    0x903581c0548007000700080c2c2258008203070080d003030802c200c46080034040c040540320300800c00c0c40d0286100d003007503002c144070020154000004100e04041e80401101c400c8942d02007601c0443d001c06482c200112000364010490511481661440160f40300741c0007010010301c4d8040365009040c20020b580c45000440645011794410300c0280c0d200c2c8501c61160f100c0800100031240501d9140e00d8083e98581640e0041d508103000401c51903c3d22050000040d101030310b1484044044100005464590b05010070007442c6884021b01802c000900750402c030b601d80307800104011058024100c03040d01e076224030015a021910b10401080b000c0301109210803491303107401503612240708079618412603455940d402c01d14049417041500718000414100840d030b08962100b5000750207081241c6c9040b02d80b100d19400e40b110000e1000c00107130700240744010300000251120fa1440104c7d01400440300c101d6005040410161055124641c4000850840da0050911404a01d00700109001d5805956400740 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 335331798 1250 335330548 335330557
    0xf0d0c0306050c090d02090703090203030a0c0b0c0304110618180711060601080604020a020f0f0307030206010b0a0e01051c09080d0b12031b07080a20030d0905130f0203010308 77
    0x460250400340425074005149056070502400544145c601460316000c02c0242c01c0301a1990b001d251b91500d00c0000340c1c0301400202000481c0d5110500c11200611b011004a08000c1800302c0e050300920610001444071410180c0d03c04d41160400d403910000c81004000300301d98445154004140421584010000d0f00010b200382407580301c000780c1e441c119103070701e071207540850300300d400030740c8102c0054000d28081c8d0143c500b50740c1c940f045620807820100b0251400c502095010f01d80d60001c50014109030b410071a450140c004840301d641801c0058001801c800b2400b0343c1541817040100d249030f01001c206007a103040240581c41401404580c1c144250380760301a03805d4a66850a0003007114607801c00c500d542c104a00c48000461610035003020750b0034802880d607029200f5001300700740011108000c012007522036008081d8075118000b1a62021050a071a00c0a54081e0f0080800d00c4062500000400221745099a074034902c03c0340d00480c0801480e9800540c050036101100101c14480d1400241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 335333048 1250 335331798 335331803
    0x1203030b1002010c08070f11070b070209070518131e06090b01020c06030a09020301060503060108100609181410020a020106090609142d070e150a0c060b0f0d0c03 71
    0x520034041001d004909079044000030801082d0480c012034101d92007200c8000f0740781032501d40500d10440040c00d05003407001540c010140904042221030551902804954000b142418098a42101903030420f4101d40c9891800c0d10441c0b1a4400f00c0c007040349d81e04803141c0c02200b25643c00e451481c460f6094000c10143c01083c240300d02e000038501c11035000160f50210000010091030441d602c0110400c05400b6025080380c01d9505e8140020703035a1810040d4030702921a01c005012407d594103c280301315112603101504085c140350010a0307141e005502481c81e60703040f64081e5107800d452ba5041c0d140c02c44011180e40303030700e10000c0c1c1102c29a40c19400301c0c0c2500c4142c0070501c00b40341c2c2d070403500c42500e000892a50048010f40301003a02441a055816820044031580f03001076005000d062440e0380d000c8030040045811502e0344559490041c4990006280300c10761581402580b40000385400d450303242c01840103589008003451390b601d00100000c6107a000308040040480da1500c603001c0c00103803004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 335334298 1250 335333048 335333059
    0xa03020609010606050f09040b0603100608060d0c03080a0c050706051b1c0f0201060e1302030c120606060a0207081c02060a02030103020f0907180e070906021605191203030b 76
    0x301c1c00c000c0c0103002c1e2004070f681a9451904140c00b04d400500168098412590302c240c1e224098070954461501551203203000746078460301c091030200060305011000702124860415002d41c2000103525501400507603811001603a11104c12b070800707903540b5920300e00c0074000e403146600004017a0381c8a0001c0514982c032070019080c1d07a1590700403a90302c109a20700903c000141c62210848503225490b10040b240180c070001c1806655030010300200c0500b1348181404880b111130030021350408000007124010141ea90303028568140c071403240c03520000351a0610034100001d4904106208015410252140d031080c2c8120303400820600307410440401c1d1400241c003e0f803001130240452482501d040381e8001c1c000b110654442c1c401c001402900619040610194040d5a100b40144403c600042c001d0200340410905028038041e000700440d9101070210b501009200b0041a10345004200f141d1003541d06040c510800501a048140b407500009000c4002103400300c00d0550580100702c1c0204143c84 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 335335548 1250 335334298 335334301
    0xc040f03060911030709061508060d0b1b0c01060314030306010c021c02041a010305011a071b0b190206060d020d0618080a030204050f0f010c030f0302041508100e040510020a0c020d050a030206 84
    0x8c242d501550880e42e05501401480c04800810114981300785e116001d1480003c8005800200e00c0a580181c00d1081c0c140e9942c203814000c010781202d0084a042d0942d005600314682035000802e41000c814009005103200c1c0381d250450079030007002400840d0b0081007840440001a5039003030301220f001a2a00090a243c00000c1c2c080c0d1200318403103001c4d00c90180c0b500d042001d441e00aa202c0c07060319245070703040e140d1000098244203070018004240c8540703440700140104407802480c000300901140c2c440c0d0100c0c02c0c03200060791190510101181c0c8500d003c1504d0740180d0181c1000c4280d08800f80041000180b040c200541c15801401996005c0790341085900001050111031180c030120103000c80c003800f201c140420f00941040079048903510740503180640320001c0010061a100709030000c03c50341c10600400d480010080030140080304405061441c06440760f51791046110034040110341c0c0011400545441400a490f580b41c026040e0300105060f40380070340c2d039409000c0081e0018000c140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 335336798 1250 335335548 335335589
    0x102070b100906030b0a0203131e03020d030e030405040e030f0a050c010513030c02040b2412060904030507120c06050c04030b09060403050a03110d0f060e0c040f0306091103070906 79
    0x40f545041d69040801d04020b0343e2400b00440083d07102500d029a202c4104424400054907032201ca81d11119450404003039029600e8040c0c51310801000da40203060410b0b001003107144000043d03608840f4120b80202d03240d00c00900660031846540d5914003030240000b0b00c40242034001e0003c2c0796031540c82008110607614980009098654a000180043d5040c1b0348100580360603088005502d20082090820714080600c944002110038511003100b60003144c1c0b85201d4031419a85035000d5401d841400e007e10b09503070010101c1c410b2440c0102400d03264a2000c0c01d40e41700702c801c0f501040d80484200640c3c00c190600901e540c011380700842e42c048a41f00006c00201c0081501c90040f541a190b150410820101c2640900390034002d01d05600000d000741c0b124411036004200a0041140002641d2801d08801c00b041c9440200390b81020501040100641c0f0b4219070306a003103a401500004604016183c40502041c86041140d0302d4815000e002c2240d8100f6072100c01202c0c00780d14603131141d00840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 335338048 1250 335336798 335336801
    0x3060b1201081018030e060918061c020f010323010807030b0c0a080a020906281806080106030f0f09030e090a0608030d02090303070203031315030203040b15030f0102070b1009 77
    0x11844d00300d010f44103045a00001c1c06588406200400280100e052800701c1000c1009441c1c2c81d08081b204103040b405004140c10403a5a0920504140c03940103103010303c5402142c1509446081d031410075550b00c0740080481c85410302e500c4503003500c800702d640f0b03540e44000301d540e115100d01042e60030401840218202c100900200c500091058444140d02da170740c000b4043c0213410010281d50020810404c1c000307000207820140c2d10006001c2c0c5d04805013905910004e04814110141c510558070040040c405135410840040c1141c50928022444619900842c1e001c0c0044c120260200c40c102041c0d9010140c10100201c00d0820a41c0c01180703580e02e82c0740e00801e0301e80e24440c0d6005c82d0410882d41380d400949800800c005000070342100e01e0301d5801d90100749141c0c80344500d29200d0030023820038413310159020a01200324289020b50842c207042e1580c3c3c103d440b010707118151418504d12084c1003038a05002d00b002412040c0021510740806080c102d201a8045482c2000c1d07510010020425003400d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 335339298 1250 335338048 335338061
    0x4110306030c040f0e01020f19030204080a06090515040b040605150607020d050c15030f070c0c0e070908070b0a1803050624041107031115070c0303060b12010810 71
    0x5005046500340101404000c100e040021301a068440d0742121403041e09000814508aaa1610540ea06407585101086034a030b00c104208140c0100020081c0420004001c2c104030f030800e500190311246807400c01c0c9011100700c20b41d107503a4201000c110070700800d5458644107a00424049c8003903030710300c910320303454074a2101c106600001c20b014035400360a21a00684a062041d811910b500c13082800290201a140d100d268000b040001004041c840c0c001d1515044142414154a4441030b90b03250003484000d0b00403402040392038000101a40c0c0b061854500810012007540d404988036440003034141c1c41240018007050070302c042403060302d40c640011400ca0b034010b005000f26845030140e1040c1034001580f00405400000003683c15a0764030700c1904035081c0e80c00078003907071500035150203030044103000000543d075003200c1c440b1102d03410010702496000709a0319040120344c03490f240c194020446900020510040418590f221200000215040e51020400c64000700540400a41a03411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 335340548 1250 335339298 335339311
    0x30a0b060319021f0201060b0301081c021911061606060501030c0903170f0403120903170304050a020f01051216081008030d02070204021b1015120219031e02041103 72
    0x744c00c4040c10314100d07020308114041005200101d00d9607174814860b606034000b038000d0907494100c00c1e0b1078690271001012072480031440e0b00141401d495510700c0c0028000100402070022507506070044841c4d52004c0468010301d034101c45111244209007800002440c190013100c0c0400c0c1b81450b8001c00c0f074051265102102d134030120040200e4418001580145c11030f04026240b08020322011000500f980e03040a03c020041e0f0740e005101c0c0c55424103803442d82d0004130315040b1800420511000c2140443c12204082d010b503550501706000b4401204d49201d06010400c91610315018843d0405841c4012450700030143c2d00c020341038481060004800040d441a204140d008001b01d41c0c040b03c070364020b040c00d40d000410050402500320915a1980506102c4400c540c0000002e01514299072241c0d442ea02240781c8444c810781d0501400760030241a0703800c041e2003150082d941041208840c000c140107140c1c003040c0907540c1c02c012145d02d68180c1c2c0d00c48049115a081840d1f68100342c0c43c0308240c0c2d10400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 335341798 1250 335340548 335340559
    0x30507081518070f0b030f0601030c050d05090316140c090c0706090f06090b090f0106050a0306051f081509060402011b030c0b0c040f0b040e0c1602030a0b06031902 72
    0x32200703400d42c240780042911014a5000d0301c6400a0111510041140100940f0354001c3e90782c41c0c40a50b0312814440103143c1814149002c8481c800b55a02c4070a03504900a030080024450302c0f2291a02d107907019800100c541400313029808400c20400c00c20f20f8402030034070303030813945581c2d002020460000307400c650886103413009106100c049805504131105190050f60584410b110a48400099450701c44050710001050014002e00c25002c06c040d8120504c0c810081000b036003030000054540c201c41c071000d00ad4503111710110b404107100100c0c2c026540006e20103040c1e0f05a030303020495250b01e1602c021800c00700082d0009141041c011414a01c070310341c165260034600c8440940703900c541c1d0300c42c0c1040e82000784400c00b94000801e0f000200c0d0140158030003403070716207103030030b521110940c065000b01903120f900b480100030080314000d9194204d09030b90b01d040d071625140c0162851707480205a01a5061148503080c90134003000c030007a20301400c02901628002c140b0040d040841000e80007000f034005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 335343048 1250 335341798 335341801
    0x306081906181e030504031208060906010c08041401050c01060305010b190e042009040b011a120106080405030d02041e05040207050c010518040501080f1c0207050103020a03020d02070c0305070815 86
    0x1224201d0768015410310a0078506c2c1000c3d2030f40c03a440c8002480e032010078049144102440b88501d4558480c0754000c17070918090504c0c0c0a103540701501e40c0901d20402d140c0350800404000c040e0b01503c140c1e803075a1080d030000c000090740da00b0400d01a203243c2c07950324001e9107500c88400300581c15202890650b04401540f00300c540b15569980071411303000e0010b40c5a1200020b2800342c991751010172134022800f1308a81c14143d4100701040d5014030040c0c1404511900420124012200d5035600604442c2981004102c0d41d4540c20850b06610031044000b02c61440042c0c0810ba2880b110405d00c404c01055072001c9049465205020407407140c150701500c0e61b4010074500255600c240020f204407070f001e2020750070410f11000841d00341c1c1d82c00c0c2c1114860390454403628071100300030010703188204001130b900721040c00110000380d1100e4031070052504054000903034086803406a01141e0f09000131388411540ca04603411701088415017404100e5060003038034000101c10000180400100030040480c000c036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 335344298 1250 335343048 335343083
    0x8030f0d0b04020c0c09011e14150f03090706091202090a15170d052104170f070302070b0307020318040e0715030c0201050106051603030608190618 65
    0x69008030380310400325501c4184400d4151200e0002d0100075850800508030a030810781044100700c0160803d20f05506028810040345200010100c100c03158260311841e424907440100d0b040100c00368080c01c01c21030019401200c02840b00c0114404d0f0344101c06c0d04d905d40e07291034080310411954420041060750080c803840142c900b8080b50f5400c04451080090502c1c2d071a2250b886e603030400d510040e20000c1c810604030841c038061255400050700d42c90300e603140504007117003594282c3d2100c2007101105d00b1240002c1c00c101300d82c556030f02d6000800b400705445000075130070f2841c0c03540b088074201d0040c002c948000840b0403140043e40d00a86054001c1c6082466010120a00a11a611180e400341e1514a8008060300130300084020b800000c807900f0801900040150944460141c000116890032004002c02c540c0302c0d080d070364480b80443c030a2280418600b001ca000e4882a00002030ba40152480c1a2840b42003c8400d00e4191144e50140a9038026808110004500703040140c8400303141c800040341d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 335345548 1250 335344298 335344327
    0x80601180905070c0606120b0c040e13050a05012904060b04120c030b040609021804120806030a02281a040302060a020304080709140a05060f0f04141e01050a0803 71
    0x83c8000545810b4004103c2c0f07403070710030548141c0c2d880007103514500d0000c101441611050b556000710342890762841c0030b19140994401000062418540c140e14450325401c01c182845040409500710009002410408001e2041d1084003002000940313191308215075035052034081d10084442c88094581003078a031503003222902c9070790801101e00c24007182e404070006203103200c002e01a038094400042d0b5141c0c1441070142080411041c2c0e10030501c02000c010020300741c900500d030562914604032481d512600003282c40c6ca102c3c400300950081c0d10200031501d034a2001c01100c04115001041611301e40e0701c4c1411003d01248004019401804000a00150611000404000d130592048a181c26601c2d044107080c516242c003c449025219075440700a0044001015007000c00142c0800c89402c140d000240c114969034040c6025000030f908030303c500d03650340c1e120340f2854aa000011409240603200c02011646c1c900c102c80a0050400c00814141003408600b8180e9415200461400850701c40c3c00b103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 335346798 1250 335345548 335345551
    0x3030604050702300d1104150c0b131a0403110c0d0f0b090a08131406030c070f06150801050a0c0201141306020f07030c1403090f090405030408010212010303080601180905 75
    0x4130211420040600f20109a00c524610355a202489548682c00d100d007400c02103510000c0f40302044152120300d00030a81c0300c0e0701e0903044085000c0d961101030203450b140780d41c038048508600c1719038501030802c828940c219114003e08040c641c2599900c014070000c2040110303c01074041d000d0309400441d100000c6015046541100682d01140c0e003201c295a9030030303295444132040d120281011482007140c8040c4220305480003400b00d400ea401d5141041c0000454050007002a19400c5200040001d005c1e095002c400b0440c105205002d44d0794544030045e02034107040c1c85408441c0c0c03910f590014400d1041c4200b0740b0030496078200807010f460320320614001350002c020a5481d0b55080000201500b0307523800400142c0d2290f1203240921102d030403c1c0e0b0203030501c4160030340150030402109100799101c00c442c001241c000c607406a41a1540d040030b5117940541d4000b00c0f01584005002e50340d0004141c40c850480b84070b550360344a05d503208801191b1420000b0806900c1401084042c0114032a642145 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 335348048 1250 335346798 335346883
    0x810120206070515181504121d100905090f090d0f120518060912030a090305040513020405190501050a0539010b090108120a0c0b0903030604050702 65
    0xa03403d41045403d9001c1d07040c0c0a9489460341c8012005e0031003244018080d20a0351001c10a034040c851815844581030b000002001e00200902c1300210b19400080500c1d12401801c0039001040110710305401900c000d509000315486190b210780040c5800e490820114171405107000a8040351242c0a419076000000039201001e200110804c45100100381c07250b02d116020f030540b10182c101502150b9410b014015180d08001c0c0c101c01c100305450700400044a0300300100380e50014210b08903080803174072801036401103031748040b00542ca20020701c0b0b150040c0054820881d42130303034050b80401c00c000040d50144100e07804610148004211140210090a14440c00036a001300307059040287c28131744441081014a0512030740151200448240311346050400c056030a031511b94113201280341d4504407840b41c20b02c010800100040c0c124442d12032111000d0340b04080e15403600700490030710780741c0d04101c900ca401b56251000003243c8901c00550a40c005000d00040c05511350700c000d54941b41d04024214 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 335349298 1250 335348048 335348053
    0x91a030316020d022202090f01050c07180f0501080a0c081b040b040e0a2102011a0409080c0f010209011202030c092e020f06011a1209120f070308101202060705 70
    0x352440b04100748500d2405c596007242c0143e42c0d5a04004002054801500190404c0001d01c2950008000060014261099440717141d004116000300309000d03000a09002003594200301c000600400b0001c3c840350000e105418800e8207030340b102d41c82543c843c00c2c145820f4645100030107503140303402c10f540024817001c800b070f102199115807000e040c1e18059101e00c00b110074865420100b821040d241901400400140c4002d001e906400c40d800e8038460240ca100c8c500c2075544412500070003041d40b04a0340080400d400341e45040d820860014000d4005090766400304410220f00045004288200c0380b05211401440e4200013000c818081940c40c1051345200368481010a9803824000c0408028a215140d0041c03280400d02d86409050210692002000895103a030700c080e102e85050980e4442070011542903001d5586840c1d40746400c290303c01404540000245402e8100340100003000480d010f51900f000d00c0e20388201c20102404144a12007040b64042c3c0340c400103103440030081017014002d008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 335350548 1250 335349298 335349319
    0x20d03090602040918060e03030603030a0e130e03030a060b12180709021303050c120a0822030c0617090304060e0d08041707060512070e030f07091a030316020d02 71
    0x15134100700c40f08800703004452030f0034030200420480c05002d0080c40070903400c0a14214200382000c25541d00a03641c4c0003050280000301d4140b02c3c2c84407000700203180c4a803c0103000301c03402c54803141d45903882514540c005605145000c21185c0340308044a2440d040e002d6116410303034480341d413800d462505500c182c0c454059007000044510050016101e041d40e0340000004052940c0350240c43d12560000480c0500c241d50194200480701017640210103401084160352400c00c0c100102c03552803003a003400700f100c3c210031000c014020740d001c10b18103581040d02c42c0b92585031941c1102c2d600c48000c448240c443e6201300414080d0714814507114058420241c85441e015901d5070303504816411070b4100c00c52140c2c1c0c001242c182c1d40800c002d55001800f2074201113150034120b806240d181d4000400060501890744810b010640741003081031008038848041e80c60054070b492421002c0c201400001000501d1070003208200d1401100b240e49240076007160480d0100302c1d50070701492078207402c07082c0d078009074006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 335351798 1250 335350548 335350559
    0x30601050d0c020705030c030615040207021903031d09061302130f0b0c1c050403120c081803061605041a070812040c0603050c0d051503030a02150703020307020d0309060204 76
    0x902d980e041c900b0307005000c4d0541058285403030040e4100400703100ea44502c0612255401a02e106000640160340241e0313035400700d0020581684207101c010b89403c00f03503040003051641c0b0604800100740388c8294a0154214802085061074040e0364840e07110004004401500c00164008c1086826142645000e00e6450b80c2c035140d0742c1c0300d580c480103001e00009280c00310b4001c03c1c04101c04210204003801c000106110700180540113501005100101100740c900140340078170741550807240d101c8111682c82605460416602905e1020640a441030601041035030800403088601c04049540c0c541c185440e092100c2c002e14030100d4458801c0301300b0880c86000c140c2c0303803004101301181e0124030341090070189040c41c0c407160f1560040003098900800d22043e02030003422250241110036004c2041e8a80c40d0802001f00390051100d80c3c1803000054002c8040c3d00402c010398910b035149131604541e03a0718a0f043d016844103d6a110044e00010000f0180d50301030b80c80005041c2c01150014180354441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 335353048 1250 335351798 335351801
    0x6120a06050d1b09020f07030f030216030309060e06061005071b080601030c05030316020907020705040e1f090b042a0f080c010309031418040504030302070b15010c08030601050d 78
    0xc40040d00c035030000503e5240002845030780e4400500a02a08501d0807a8450b04170355140542c100003000c01c074032001603015130b5100390169180c4040c03030f0030304440c1a412490050000c00e1058412540c40c0c0c2084a800d030060b80100c3c2c03461003000c002c0c0801e0b14560096000321180da0156900719000440c05950815049000c880d0304054051480180120350460404050700031599008078402d0b03004109800615800303180700d4084903810740c1d620885494140d4140d09001040c0c1100b50001d1504500c85914040058001045401c03c907d001c0c42a00c140b2140c1d0507600a4007018020424200105000800300710a8a51420310240d64100c4200c5d51045144180c940d0352080c6002d802c440400c3c4900036060114401e1030400342401c012160040e0f402602000c0740c04548000703000301107822080070741d50242c00d141c0d40200a104111f24509885c0c003900079001144185c41c642d104100003100e003038a103028440c603800305071501c2c03242d0f000e03e940d079290b5640001c0031541003202c01c0c083d030088543c9a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 335354298 1250 335353048 335353069
    0x61b0213150906060e0910063905160801020304080915070615060305091c080a091b0f050607051207060f050a0c0f090605030a020307090e0405010b0f090606120a0605 73
    0x95580e80484881d8000300180b000010302800c0590b8032078041040650b41281002782c403001000f101d00810300c10310340341e50204140290602c51a8100c0c080100400a02240038084c56484007800a42d494031801817600f03d010498006007088000c01682c181072414040d4810fa85080c0301900d031612445903201020399a85261b8900c400d102c5031030500129400d4050700e0f5010702640024416a02a0751850403007035a170800c200107000000300440c0c00a40940c00c24500d040d00030b42c003310052956045806524400d1041c040316443c2444042018070300002107030704090300580142254445118080425408184201c1f161503640c021401c40d40f03a54050030b88203049000700054910314001000d810b000341608280200581c440c0300703100341601b18060300e41060600e600140c49a42c0c074541555015456044820602010070800080150541000c6500f01090354014820200c032014008448020b507821030f4030810a0003101040c40070350002d2036004010242c00301d01ca607903820104810495 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 335355548 1250 335354298 335354309
    0x140f060a1205010b07120f0908030a05041d07021e010b0d0503190305101a070501020705071e0e01030f020411180108061207050d060905030d06061b0213150906 70
    0x1458501d052403450035125090040c0000c1019510b896110350ba00b01c1c2c0092500b0007481440321505013807403d80c0c4112505030107801c18004490341c5400c43c40c0007800300d030424400c000103003400311400201a40e40c5c550380c600031219500282144000741200030b0203a2a2107110114542d680c10b2000071942e921607514010900800c00703540c0d43c40c01051220280004250048141030410303040c00101c0e000c1d200403204440075213104186208000541ca03800740304030f080c041c1081d80080741d00d2007400804200e02003107401c102080c2c40c54603106280c200d96085207104200c00020640c004001103007030a094903100a10003800040c00400282101c21a40c01101c0b44402410200e11281c90558100e03032400d410100440300d40c50120038030465165074030710900600e40520703c040460401c000e131640201e00302c55841000d42e03444542c40c0d070b407650050940e845584c0000c0d072101c20380c0e603007a00545c04508090390080c00d072941c031403040c20b04070000e4140d845840c01610110580083e0004035440b41802911 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 335356798 1250 335355548 335355557
    0x220819050c06130303030c080415091703160906090305070605030603030c0d021605010c02100c03021c0c030e040207120e0307030203030408160b0c03120c040312120f15140f060a 78
    0x10308500f401007c07101120007500500500a06210120b80c1100e01c1c40030f10022120045410841c1e0303d416050001c03807110711040b03004c010040c0102689402c3c00c800b40c80c9299603031001c026075651001c0f90002d24911000e499504564030074806103214200035a80980098200c910b001e03c1c80f1071032440c0c040b5a00c0c0300001178010301080380b075880414131081d004120920345891582e80b1600000d4a01080c50f0014040c81500098841018024814090143e90300f40991081c074440000140040c0d8a40340102c1c0000c03113a0b00e10300603901d4140300752048581c011980c6c0c10a10642c00c2c05603803910303400c05166414841c0c45070000041e94100000e00203410b0310340250050340b0000c5500f2444d112260401422403d05202400d000400042603681c0c0d200c90102005094030b07110300c1d2184034807842d040034015042184460240c00d0304107580c165039203101031301040403d080000c0c9000321038048007181d00014450908105883e20181c85402000c0c009140340c100c0100e07c0b000412580c801d601640205 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 335358048 1250 335356798 335356837
    0x206090f12010516020d1e090b0714060c03070503070c0201110109080405040f020c03180105040f0e041b050a03021908011d0c040209060702060c0a050105070302220819050c06 77
    0x318075a920744c148900ca900092006002042c00138000d054100512420003000c0001c614510380708042a2006000030241d1503502e078004d013040324000d81120010745003881008e0101d108403c454040300d109800f180d0b40c0da401c5850b010b0003220884c2440303074240c0c1003260501810300d85103070a124501819102d80200d60382c89103480c0c18801070740c4000212900b00c910610078140ca00201208581600401c0a502c88103000b0000c0181c03114055070f001903002400228001c0358210030040e6484c000c5000d0290307860a40e000c501c0c000c1180e152401103d0704080c85680c10001414201515010001c1100d032040a1a8031017524508560007912942002c0680050300140d40341c0520441d4a08001501c00303500d480c400401145061261303400090003450700003118800c0020910200503038583c0b0100900c82e42c01c0103080200070350844074500481c91815054003180c80000030412049a41c00d034090103042e00c440d0030391010172484803000d4070680124035461105075541f50050480c0c18000d200380441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 335359298 1250 335358048 335358061
    0x21813030311030903041701090f0b01050103050a15210602120402010906090806012105010c0206010f09061a070c03240509010b2808150603190f0206090f120105 71
    0xb0740b61408800c11840404205110380044080103c0e07084c2d40c0481c62080042d2a4428003900500e100c9001814001c1201e42810401000c00800750499100b6601803080d600d0781018282210440341d141c0d0030b41c055500d030400517041c42100501d0910800c000e82c044007241601d550703003a40d000840c400b0059602e2000c110071503810408a2000d485145048445a41040c0c0708550b501c5040c0a01881d48200c4214400311203241c00e982c40303a0035070040c02440303070f031607800f1000c4d69480c1c080c0180a00742101c24008100030781288500d004444054458445002d84003444410f258030000090f00c01c0105c104011000c50007050841d40f40440c05485690440c015005000403a0300c040c3c06004075904000c1d03101400da407000b407050300c010351484980d104048400040d00002c1641e6110710101c0c0915501c031015154032149041c0b14000940030385034840646820070341c84665004c0010100d007038004410001d41030100c050184504040c050784551001c800006500d0741c0c440074203c490340c1d12941080b11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 335360548 1250 335359298 335359301
    0xc1b011407021f05040f05100b010905180402090c041511120304050c09070201021e0c0d0216060815060301080109020f040506010f0302250c0905010605040e010306090218130303 78
    0x81c00394940c4090b00722a4250303035060b100b03102c140340544900781d01c903804501807185621540351500d174001c08550b960f403424005040039105202230f140c04241e140b100016281400e2103680d00004000481031b1040d0740340da003006065200a04203000005003440040741035100301c2d010f4030641150383c82e003c003175140c200400c0386041c00c10400071201040034020702c03000a800055480380f40400b12184d80d103c0c0d45a51003280240900ca60030301189171000160031910290000400d903040c105829600d00d1084007006030b90b00c01255205076034102b1040c20030803240e40f00304101070b00080c194268094450340d030400a03102e034100381c001c621180d40d0348600c0b00461429920682e0f615a0a0b00d0600041c6080e0001070207091307002e06010203040d0005450300040706446030400010f41e220761807168042140c204000e802015024542015140c03400100f4001e000e80290340491340d0220b8031269a80c00c564034000135103185101280c008050b2480b008403443c610508030b100e6281031a08800460003800c000f070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 335361798 1250 335360548 335360551
    0x6060b19050f0f09010e040f0b010e120619060305010c0e0909010501210503160b0117010b060405060c010b03010617100608060a050402012319021f050c1b0114 70
    0x8041c0101000780b0081030242d00261100d180101c44400c2e1100582c900684141841c000d030a40d0080c42e00d500303072010002c0c580c0002c030b65000c02c1c3c3c0c964113041b11030030520604080036000d051441d07001000040300108448410025048000d40c00b203080c0d9680d60799a03080da44540710110100c2d80c1609400c0c81800c010220640c01102140240300b90352501340c9000d080c0c41c40c0c5845502e400c001a1456080c06010130494846040a0710741d4501762586044c503610350301080c0940307051002c84142040354070030b05024400412100409991400d450320042000d5036025414a5184cd500c0702840320040d917003880382100505009a14180002141d40c0190808110405140a5515105003031020000000718183e020802e41d500107216150b070b00051b03036071f500d071110240d200b0100714020700034947c881d101502085c443c0d0340004036001d45520041c1e80b20b40d6560000d40030707284c56074580075441c24180c0100360003802003a82c261400400700c0c901051703010194001a0544e450303500c030302941c803c48030080307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 335363048 1250 335361798 335361847
    0x105010e01030c0e060306011b0809010305060a0608010b2802011b03020c1e07080613050d0318032003070f15200711120f070b0316081306060b 63
    0x300200b2120120203030034160061304280c000e882c040001020b603401030403010741301e4491003910555255103107450005684052000c0b4006820603010841e98100700401d01c041d54070300e03214450260b0030042e0140d01c80c0c025508207400d100300034040a040007105e80e4481c3c60409180e00104031103004021001d6100e00b1914094101032040040b150342c4540401c42c0c1e8244460300d441c0601c443c0b44000d429140641c15040041d1382c0c0200c1381442001070440406030500e61103401500c4202d00c0c4140280c00700c40e051000404211520507403503002030320504020650303840c03540003000d0403112081030301c1c0345070050082224030140d010104014042c12841d010300204140d04280300000681a51a0b580e160340c01014400590224503002001000d542481c0341d040003030a02244141603003622542c0e0304540854510902484001150044407c0c2c2245d105101019a880511003040c00c100ca96080c01450f0b9413890503100c11050010f461801340100a02e0340030442078491810300442211641c00c0b035030702d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 335364298 1250 335363048 335363051
    0x11416020f0615010e06040302040c0c0b01090c0f0c210903150c0203041e030209070e040b030a0816052409060c0c0c042714101e0b0310140105010e0103 67
    0x3040f4a1450381001e580d080c1c5800e1034400c2c200b110100108605000d203401c025400b40c204220904429800324511100c40e0040c0081046644c0e91030300002118054615680041c3d203403902e050940d4000c4010310980340c411b445e20034654a080f521101c1101c1c42c80003a4001800c029400c00510150b011014100308888908001030f204124010b0764030b04c0740b8400d00000c500a541140044281c08488d00001c40e00a000030f4400d2800c1c00000749189520703d03141d8810381c03802105c010642000204580c40d40d6005081e103103004803240012400c6424a0411a000e204e10500310f41704542103c0030007050383d40590b49100c1424031381e4486003409001017508698407010300810007500d000143c80c1c49408020f86000401900c10382d0310180d400c141305088000860000c0208007008411840c0c036a000341840e0035980c0360405121000165604038407101e141102106c0d00b0080c4192640c4603141c1200c00400302c494800c80000245d05488011410302000580d8100400103540c000788481031904007481d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 335365548 1250 335364298 335364301
    0x50c0a02010f0b0a120c08060a020904061e030809061e090307062102030406020424031803050306120a022d0a080604120e1c050c0a0b0a11011416020f06 67
    0xb165401c04c091040030590004c40c1c9151003808030709050751000d045000c0c20744070346140094015002c0d5008001c198000c0c0d1803e036000a070751021070ac481180c051240f008514252039525451003d0300303c088041c1e449101000480c15554000e02406000807101203026100c1110400300f40c02c100c00d6911400a00210910303008160700580004046040352810060f125207480c100800203019a0700f01c00c50089071500c1140e0300110075210898042c1d2655401d0021304610110049a03003214000203000c140c040c00480c0b030328030b40218540b20500408084030099040b54000400610507048602c0c258544548800d040038036000e1078000200003a0740c54285107241418480d514540208094211918600e03520096446210340b0415130000504054804900383c882048100c0c034140212040c0c400c0711405046c034203011012034101d804450245041013151141543c0d920461004007406541e5840042c4840c00e050041c00d024180c45264070b0710030028541c01900d424540078540c442d55100302e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 335366798 1250 335365548 335365571
    0x50901020703080c1602100e03010e0304060f11100606091a09010c0b10031227082e06090c1101140105041127150a0503130201050706050c0a02010f 65
    0x1080103070004c54251803640d90745c0c00404110b424082c0c04400035408550700341d05040e8194000f40c0303483c0140d0110000c0000e84c6070701000aa030307446544205d402140c0e5080e0a0407240e40078400c016800d81824082c0c1c0e4541c901050203d0891f85940c101c00089021407001303001050810b501d5250483d5000921031901030442c002812004c8101801070003404880000b50380154007600040095500c52041008034400c04c4005d04071039099402c5a0207001c230000c10b45990302d6074404039001c840b810700150081000c011101840307039502500400d041c1842a000080e1510a40b160703400030101c640b80020b2040d840304c0014691040d1003109160740c0e04181c0b1106204080d00d1100d41195801c65000441c241508a0002d0324040c0c00420110180002003141180c041101c4040c0502d01c02c613080624006900d01c007003418001c21000c4c400103042407000500f20f040c20006200c400b0b0050418a0520000340d584030180c2e00100c42d02009217801140007480190240600380e042c4490010070300442e000030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 335368048 1250 335366798 335366807
    0xb0a020d050310180f0903050d0c03090f0b07051603020109020f010819050702190b070212030702030a0e0105040302102127140a0b10060815090718031104050901020703 74
    0x501889101c1d1511340103213950102694480b15031407041070400d205450b92418060070503005604640d003e00e0402d01d01c461082c0c40b911a41c90015440300f11080100c0d0992500490305c0d07402480c02040c0319003000410040f9111082100c1003e1103580040340940781d62051240068201200c541440081d0742480404008049031100c40300c551080064103135503c242c200e10709540c0400e07464401101111100500850011140c0300f40519002c1320280700342d0094002070382c403044503080c0c0140c0084c030195070750611424040c0820801490b240e4201502e9800040c06400c00c0e4421001103445510700340400403400f12441e03800301481c0020001c070201c2e00c21604142e4031180c00c40356071003050a8200104a4400c543d02c0000000b0412586040c005180841c01c4171000c0c0c03080101d9040328000016280c1c800d007805840380742002c41781401555100184001d411000d09000240240300100c110600d10f4100e2000c001c1d80145000c90001d000c0e64244012542c0c040d0654649900421006020a410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 335369298 1250 335368048 335368081
    0x10b03161b03030903030b040c030b09010e07080f04110901150806030106050f04050a090605040c230f040510030b1005040e03090303070312020904020d020417070302030c280b0a020d0503 82
    0x608022984c83c0740d92808800a005284c503442d4054034140c100140150305034821554440c09440b001210790700e42001401540301210101e000075840c10004124400c0020340c0394025108104900b1038504540c0003480c01002604010001d4a40c1a000785045520174040c0e9000801507008000c03880c18000810f130f50745903950b0b015000b43d8440e07000c1104004d241d40020a41070b08080201300700d00b00340c034040060304018891f00c003040d54080d842c0950848502c41c0500d84541c002c10005c00750b00c0e0340050001820f002044580c1240c03404900001140211010901c50000e0034201343e003150502e000c01085a80b2000e840407980d0040c0848050f0740c4001003221820394260a000b00c00e100381e004598080d10030440c0c1c040c0c005001049038200c0500b10340250040e1000f65000c1807613030b1040141d00e80e5600e10b0340f0000e94581d01585002100d4104a20701e45070900e0720000c60074000166150213980300b07019903c08001c21000040c01001c15a06001004190007580340540c51810034091141490aa = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 335370548 1250 335369298 335369303
    0x1605031e030d020f04170105010b0d0b030c0d060c03110403082a010c0c02040b0108040507030308150414070216140f12101a27040602070b010b03161b 66
    0x1100c60359408a1602041035440e6203625100035035071080318000840c0c80b03030820300c21070007004440031098140b80c0301802404c0c16a46000061070034100c02c5003041e80a82044681240c040c0280708522000d503e81c1115030200501403900826101d40b245e40050481d02c0001c0c411408150600c014400a000c4008540c051500000b4001c8080c540140d2032101d204031034083d0300990310713100e0745015880d040219898024001c880c20003081d40490011749130f4807011540100705030081407003400043e00400c200c540001105001c80040702c0f40c08003040031281e000440c04440602e0804114280340c0c1044402c048031a08120014610321704003030507032503140707118400d441000c00354030078215030310b90202d00001031071008103c5094045100c0c4034001002d41403244554401c0d6844904058102a4440d4454400704001d101d41050b21390200d0008040280c0b040307a510b43c08001000108541c600c0c281e02034440e0780142540c07402c0040310b0024810a206841307082c0079602000b4042442d00d115074950b0580c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 335371798 1250 335370548 335370583
    0x2070b041a0702031e091801060309060507050a0203070303051009090b0103060501140d0f02030a0204051f05030f100b0a03210e0f012001060f0f08010e03090607080708130e09160503 80
    0xb81d4040000305c244c1e000c5200c7d8081000c0035000060880d41c9500305180290140c601045251100b400490b110300c18a0b07100009607008100c80c0c00060320070b5201d11780c0600c0f02e590303150a00da1121600000d0305d4007030205540e1080010010b000388071091068500511030164041c144200b100b01140e50417000d0240a07100c1300d0000b030352a003551400c0c0181500154010810007070b620340318500d200c080b064000d0300b0f902d1820360440418641000200760042103c000010b0a0017501d183d0355502400150013210740100f03032801c000000410140d04411810f001503003600c4c1c074012134600200000d000d54241c44c499030740468407000342e0343c00040c00c501022035003d40c00a008205850280076103034944c0105900340f60014005040403a00c605113094504c10360082c00f113540c02d01c000300c0c0c2d00e000300c1450b03a511000030400c0000081f420401000700520400310941409101c12598102494640c0080400c003004010040031a40a01c002040740f120035026400c0d00e03080c000400c3d0b80b01d4020503d072403c5c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 335373048 1250 335371798 335371807
    0x61403090f060a2702060d0b0f031002031e1005060c1e0d020c0307241e09140d12051309060f0303200c0d020402070b041a0702031e 58
    0x106814400031060031080d00449001c0e041c46211100107001400c40d502004020001c141d050040300e5218a80c410780041030135003411f0061405100828400501c50b61041c0e003224011541e0b10180900500c598205100603240c0c94a40c03461182000801001141d034880c0804000354900f949a00d003044e107400703603000c2d500d030070030700090740d01d08800006002d07034143e117881007258441c0c400115811140d005900351030710013203c0c41c24182d4603c000d00078400d000307100414002400540c2c907600e0041402510b0721001718000380240d00c070340c2c1c1ca0740c154100002d15a60401e019642d180201c0740282203090302d10345107094003910780c2c25500c180700b0000d90403c2030004054058101e481a0f1002900111000300001a51061029452061031100300d004ca2182003411500b00856080b00c1640c2030100e000d8228044900100003e40110950807688070f80d0900c03090005c00c45022405116621030002c0f030030601500c010406425800802103000c6500801600d140c005850782c940e1996001000c0c240e854 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 335374298 1250 335373048 335373061
    0x406170403051213030e180411190e070905100c02100e06040b1902030307020a0b07021e0606031006060e010c0503161a01051e131508030a020610061403 67
    0x600ca08540d0700700091503c01030003040701c0c800940001c0180f00307032a1468200d10250901c0940410710382c88180070101c0c80005030110745450301c400d8810340f000b0000701d802400743e4080e070032000142e0000100c03c445501000350242d0440003074000380070111601c01c100791210700010015140c646009000d0300b114840340198501802046010500051003291102d031646242c18043d00140300248444039880c1c091480c5c0da00200480b4001c2c0d0710b03940540380580c259141c480d1101000782070001148104040c104047c150b0041c0c5e90000000c90028051604101c010189049015105165558a004c40410840c0d030000c015903545042801c20960404003401d140742580a410500900d00c05450040030400014000781a1011007150754003d280c3d1b2518148450f1160a9480e112406c3d121080c820301d500e00024010101076442101043c00410070340d001d09100746c1a400683c40c1e500206052200e0b54062000f240d00030840d0800d0140c50380790000c01851021043c401613442039000020410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 335375548 1250 335374298 335374307
    0x1122007032606060d0b01091a0703031802031e150a0501031506060806012006090c2830111503060319080c2a0301050f0c090a0e0f04030201050106050406170403 71
    0x9141c841d0b940400e000f427889d030080b1a0350100c030040740020318100072811100e405070383c0c3c00744550300900104034110540381018001924403a1800491140100f101d100240028009100720070001020900d54518503001c1542d109800e41110214148002417000b6540095401d40c0a1024a0f01c4a0f20010040810200000b40c01301c481d140d01800c0200321081c04001240c50302814196100c2d43c2e40c2840c500c2290f80ca092821b071009500990039400c01150800070080920890484c0210032815509002a030b00442c2d6031034101d520302c9185803a00071500c0d040701c00b1030f40004040d220300e00c0c500d050f900080d101d640b90070010356040e02c40107030380c41400420801d640c00c4101400803680a4500d0441c83c000c418800e940d44080d9482a0003404140c0c02c043c00350318007403114480c0848031607c41001814041d08024030042c0c1015a000c2c0014484074488030440c0601c9030b55480741841d05041c28000e086d1581604034206101007080100710b0542d112142c0070b2901c0480703000015a4903507190446 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 335376798 1250 335375548 335375567
    0x806010e1504032102120d0903031103100312110c1011030301060305102103081513020d05100602250b0409020c100b01122007032606060d0b01 63
    0x1c0101e00c0100c1c01108210a150000000d440001c1032031a00d030450b4131049a45400d0450030b100890700602c00c4516489041c0c1108031003520074107000c00c80d04200c100035035054000316040304086543c4e01d010002d02c1005503402c080400c20b0715141e0107100110810540c2c1d0003400d884e09010b0200800d9603440203100d481702c404a04041d0040d2562940e6400000300600b1081e81c0340d50701d00311059400154401c035508145c2d64041c0180341c1e0081c0e4085502c0075110b502c1c005103101d600152080d14858669260400c50380d030582200c00c0181c58a1000607072038100d4000070300e4003405a5403c0030500201d500090f003070703600442045015500780100031019040c079456030320503404207502280208407400560040d0401201c220304441eaa40b141e0310951042d036000700000d602041101000f140c0303444181c1c00010780e002c0d1110952035042040850400c1d582c0c03180300140c0006880c0030540ca4146410541000722514103040030400741410360020706103205000c142100c5e40d41e0340ea081e140c0c0c1c0e4043d88511 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 335378048 1250 335376798 335376829
    0x20f0301090c0303020601050102160902030403090f0b07031805010207050603070309021f180e1803040513050906010e01061e020a0b0903041404020c0304060305040c03060207050a030909020a0806010e 88
    0x80c0508071552900380741d01125400101d01500506001280d154400070351100840d0081d1468440305180c43c29150080d440903000f50701308240240041082d001c2584003900030705807a40410b03a034489508004281245403c1100c00c0041d50078000c020b00c0ea4002002003d4030360880b000b03503036521911010390003800281c3c4020341100380401e4000c140c0a01050120468106488261564400c404160b000309006d0003014121490440419140c9008006a0405000d1002101c0c5082e0320380b40000c0324940742c0c3e80f4540300f4540b101c01300140c441080c01554014103030340d1034004203135040041c05010100740c00c2a0201d281c00c550340c00c9601d1031003082542601604591030300320600b414420240c03250311034081c05054611620141c690360a040c0700f02d0f003810078010301541c00c4c43d0400b1021805000301a00c1511064501c400c04804100b840c401007103142d10500080c61039414514001c2d01440556114107130062060100b07080036500301c1c1600307078000402d10708504e00c0d200345d000041c0a00c400710f484 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 335379298 1250 335378048 335378051
    0x507050d140a0e030a02060712060b161b0305030301271b030b1905131b09140a0e060906060c030a03021b03160303050702120c0a0303050c03090712020f0301 69
    0x381c200d031204403500a0045402c49414000000222580c0c0e07038900ca143d2170300005074800000141c0d064400c401c0403120249400001c9810f41e035501142c00d5a070850740840961a011540e242c0800940710150031180da403014005030310070700d0f580b01d1544a000512521051000000050880c082c0d94107404a804084000c1001003029003104990300402e10783c0c80c600880d14004040300c01c0c1c80e00795859810703110701c140c41c18107490170a030910444088000541c14295140d070325400c0010b10458a000042c412a5602e40200d40b8211004003160300b01014a809034030440b1050000b00112001c0b1944440c0540300c240c0a034550101142c0b07140300c2d500c1504a2401301007130340c2c1d40765a810b400420044544119114141e1050fa02c51500c070710a5000152500c08403100c00c0300024040d411450740811103005865403c0c11030903400000341d224402214058204031032030070402d50148590364103c00b0050f01c86040d81742221f80560b0728403581c01100c01c1840c01c41c840c20300315624220301003902c2501500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 335380548 1250 335379298 335379311
    0x12010608060f06090f12030c0d050c06070801140105070c05040606110709020c03031909050304090501081605060a11010603150e100b03070509040212011104080c010504180507050d 79
    0x90280c0000e8a281c0d20840c110305030b400007450301009580964100611350105212620108034014a0741007041400d80010b00403410850700a011003a17440800d80c0b203c0381d617611178525a9051800c001d00c0f45040c4000040184002d03240c40c00d049070022170a00703290303075983c0107401c002490074600e83c001617000d41003a0340402d1880c1d105100c510401e484504684070a0303200d21500041c2e0050084204640d401407000949491814034110021801d96800140804007901e80301d00399032003508640140c0d900d40c401004114400c02060004141103c0303070160141c140000910284a142c00c01c03801c0000c01300000b0520b0784290b100000070340e448840451464070401910f000703000c40610083c40c9004006a581260000380030705600e14800402030243c0d2400e010800280002c0034009903049070001036028003c400920504682041c0303802000c2e15107103050000703032404159041490403c50140030400c0300322003209081c8400f81034901d000c652555110000c8403540601030038401407508041c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 335381798 1250 335380548 335380559
    0x1091b020609060f070302131e08030306030a080f070b01030b0411010f120f1d0a0b060102070f0306051803070302070f0807030f0605181b010201050f011410050d060f240206011206021201 82
    0x860a4424440b0040c40c0c220030ac1d517030000503031280001c0700c0f01034254200451540009004200900003040b80301021810100a070b121000070440c00d0708100c0b0740040c0e03079041c0403e020700081d41da0110502481c141e62049080000141001c039401c900603002c80e128000f5444519864110200403090281142c0080b80d0800c1d00541e10512000245c036a0541e04011804551010941c1c0c0183c940440c00021564039581d1001e0092100070b00b4280108d12240c0706c040f00610610040071124000da0041030041c4c201071000340c500c0c015038003880780d0b94840e610800010f40c0c1160400d0001d1f0300b06100003129070314884000700000e003a4401003800d008441da07401501d40e078640342c144c40380c000703038020803180d51441c1d901c0090076400e004001100007505444a01407401b40b040f080c92001c20f00e0480d041034001c6d03d070881a220039400c22199164480f000b4403042203400c0340c0e0303c01c0d9039149000b000d61003082c403000382d00c50f00b041c018a41c2c0c0b0034030640030109010f150b80495200d5110044041e00d250b80d5031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 335383048 1250 335381798 335381819
    0x100b040f090b040606060305060105030714040902030117060601031e0f0b0607051018030903021009030c0927030c0f030504030f12080a09082a0601091b020609060f07030213 76
    0x80f182120039504c1c021011407824400c0c440e80d4481c91060310f0342855525404819681e1210045214196420030480407900b9031050018500800c40c0403c8180d185106102642c10b10a0007482c01e81014a008610381e49103840c9281040707502544040028000783c0031034400054000c0b4100f5039000742c40040d502c01000b0002905051135a00c5600c10003160800302d42190162695800240000d1070462090000d0328054400003448025800c18440c0f0b941e40c0c0e43c50b01e400c6034159111003003450741c40b41418510103182049200c5080c03e00e018141052869801400010b040c14010302074050480c088000c140c0180221005942c00050f0380d085001c3e6440c2c10014010548209000100e100c40462440c503103500402c1c065030342c805c03521802c3c07400d400c1103821f108071081c2c0b4801019600003075840a070b400c2030144a010b0203402c280070640c0c0c110b45920755072040070007002804541c8403108005103806d0201e201d682190034540003000544680d98101c0c0030f4058009824046c0c0f000420000e40009007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 335384298 1250 335383048 335383051
    0x3020315040b0f0c0a050c2b03200f0f04090f0504020a060f0c120c06020d061415030109050a020d0203090f0d090605030c030a110708091e03100b040f090b 68
    0x8034070ba680960b680c00c0350045101010740e13200007180002d20007519a00e020b9809131244403044405c0b500c2d1546079541c00302c084546a640600075482032408130703000075030601540346c0b84021070008038403407100743c0381c6140c3c14403a4090a242204012820318523542c0d4400c100e030010002c41c0da00b0301c000003001c1200c2d0010882035504030b02c05c9600e400f0000c0c003580103050049002c100703612104510304141e01c0310940320142c08003210070040a074408030005043c92014021b1a0b5101c4400144030342000045070542c1c0d280d003407080c490510140d0400112a10340c0c122415280000740228068aa01d00107a01034080c86421213080740c004010003210020010340e41031406002411102845d095610542c0c01081d5405404009902000000c03400c0300d0f02c100650f00918402000169000703a6078032101c03150410301c41155400e4000411003400d2a11b007078242020b18000400c1c258000880c80000d6989070209810400c894540c00b0000c00d9560f40e07808213011490040d01848903e24514000c80070940 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 335385548 1250 335384298 335384303
    0x1806030b0a060e0a0b1e12070e090708062205070911031005060a050a030509100207031205070f0c03030f110f0a1103030618090a0c170f01050c0301050105130302031504 74
    0x2403400c00140d91038414065000700502c050502c1c9118000303007000c1107805aa011b05e21741c10070154020380101c804100010b50003000466214281800c100440508003d016409801c450b8005002c3c0b0190a4030503568100180d60400007150340b8800d498100c1c00c200490380104022850010f0b0b10f00000f410a000f07510548817107101507141611081000580c0c050300c88200d00145c0d05000c2d0030490fa0083c0d000a400c9200523003200d001e6540482010103a921024044000807190000e4944426450103415040603260900904ca1100390400400d07a0350301900150400d51102c40400794644254841c03850000761170240ca96609800c4414260341c1e20404451000644901e0190725050006c0b055038001c00000740305055200c0b20200000400307402402c0e60700140500c0c050800080c4924840100814041d2000e5880080c0da810740783c1403031045060750215904000030000745560754000c40b41900c60034203003183c0300e6132903181c0030581030880c2d003000f50180304486444c1480400f401080384103a1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 335386798 1250 335385548 335385569
    0xe07150305160e130209030d030b031516030c030b0307030803010612090203121b07080a0b0105030d0e1207050306090a060612080703261302040c0e0a1806030b0a06 72
    0x444004404803144490740c10003002076425100a0540c1c606500c54a030f00381d2461130090304040403140003900700248141c8a4000ca9501d41c4051881d04003400b020751880812140d988092070020790090a00e410780c0e000204040e0384007081d01c3c405010380c0c09508201000b404940303246449160078141e642c402e00603000840c0100303100300b465a20b07030b0141c41c80440d4040d01400304045042d403464000c1e04621032030b00c60b400030a20018000c9000300720340d0703008203000b6008004e440e8246c10820117148041c0c009600035040940420354850b040404125078041c20f48102d0340c0f0401c000482402c0c0315458114950501502d8240311017260001101000e10b40281030030011642d0701c0c0c064440c402c00c00a401854814188203010200303014044000c00a8031031503000342945804000225601d00c11903247c610b1981c1c0038641e03019814184a0041a054107060074a40801800c0000d01d1001d42c074410400315880300c0550749048105a040000111f50201c1c04110714102a01c2510251090f4000d000c8500b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 335388048 1250 335386798 335386801
    0x44205030106080a020f0d14150612030702011d040906050108010f06080709020a090906030609050d0207060c1401110c07090c091406030a060b033111010c05010e07150305 75
    0x24030341032041e03800700d030b10b02d1000300a480081e40c284882260207a0409078050790400a1b00007003041c4010b0700400350b0100d4060940034030148850054a40e0140c40c1c00d000e03096002c01010b40200010480b035809809091040c10300d0412440b030541c03008608800d83d0090300b400b441e98104552031b040213042e240210001d0007000c1101001300c0855043e40305000e030560101800304248050382c0d0091032800350f40d2070a0042d240e01c46400009031b482581c821905250b13612440c0007880800d1001100310821440070b4080c8500c1c0c80001802452103c0b80034000405510728505481001d500044200c1842c25403503855414940819450700d11038420107880b5400c00201040f040c0c80b82e130401c01034803240001020003072034000510815400040108034000d540708030114503100780801440c400c1802c00e40100c5140107045180070360169030160317002d203007054201c03010019036050141d038030202c0c1c20310f0981042c1c0d0b91130030064098900084000d106000d03105000c10f0000424080c1201d91915442c240100e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 335389298 1250 335388048 335388059
    0x7060605060f03010e13060c110d0908030a050904021303030201090b09060c0a110c0312090f0306060a030201050c160b07060e03130315020c12030105030118110442 72
    0x82c81000e0048441000c10001480700503110040b8607001100304288400040c40c40e80d0b9001114144282c0f4004164480c2c0540c4243ca01000100e03410352640c40d00c0101c1601e010300329903580c010411160180070010408002544403541034070000c510403032901000c1580c07810043d0003052052000d0f0f0700010301ca0005102a00c2c00078841e4040c0c0c030001c0c00d20340f41c03c441d05001c072205c0200000d5a0044d0142981010003507030700b080403800c04070160700302540d600015020400c40c440b403001c665019030080c00c00c03c2520307911400e0810840c0e4081c240107036110f01550f0b9140c18082070002c0c07481142c80440d13005c03400314450405003600600c6a403080124040029480c2e035a8000d459000c3c00c100985901130000509110310044000c2d46404003509080b01e01c8181800d0090700c1e8294140100301000401c030621303090040c0c2801c0d004c0c200c04041d02c40c01c103072155003004104444850085480e1100500c800d12001220503c6203031400e4507034605521010551008002110783c5084064420b001040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 335390548 1250 335389298 335389309
    0x20a06060905100602060f040f03110303070e040c020d05070809060f070f020312030103020306070c060f06240302030609070e0d0b0a0b01120b03030403140c150c06090106180515030d020307060605 86
    0x8001d00207c464895641c0e644100c00b082980c441101003220864bc4400a903804001444c058502502d5200c41d900500c010b000488506216200442d80130024040d00da0f5044030403601c106400811b050755030302d0314102103092031060000881004900240410510008900d801b1040f8402c4081d02e02c04066002e0300c4405000030f0002a41c07603045000800d00141c0107c0320f4000040c456040492114850052a4110740c4030340d101c1c4a07050b00c0c1010713103030111008106480c080801410304608600703000002c10392010000f080c56040c01000d6880c0c0c8400c1ea14440e907128810391150a24040c0e2030300c4114600075084901c16240843c0c84185c5c8204201401e00482c007110002600a5061078a152620100d250441c2550001400764a00800a0744c6410362030102508222080581d01c4603080e0f0703520701d8510700034660442a49004d8003407081f0080400006400c03800d00700042078540300d48160000815024041c07076494401d007841540110340100c003a140c81c1d405401c00300003865603441400f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 335391798 1250 335390548 335390551
    0x40f080c06070c050f01180807060e0306010312080702070801060b0a0318240204050a0602030403020a06030c02030a120e15061804151503050304080307122d020a0606090510060206 79
    0x1845558005400d204c1c6051448070034100f468140b40010110100400c006c3c2d0714510b03600080c0c0c6542000034180403040e00486100002801a401400d00b0740c1342d51220056030110221030b00800c001a400304021a100b0412078002e03142604c002c01501e41e50b1b03000c103c001d40c410b81102003c02d051840c01c102d40c1e00040254490340b9004069007001380c170a580b05003914240300442d22201c0303500f40b2000c0740d181c40d0401000040d1003541c000315035490850041280124441d80020209424a5040826554040203035401d20b802400d21941854228441a010f8194044840954800e02142160b14095542c00c607002e00400d98145041041d020301c0050740d01021903000d00004407110b070042e0510b07065409020041e2240f03a000710001c1c0c9a80d5040d04552003540a500e05510206028082c041d2042d06d40700c07a103909060650020000ba003504c0c1c90481800c00e040c1101e1450b4030803102044c000e00c80303110040c0c0c1c001000c102c025200c2c15607400407d020784e20000e0740183e080340406c1050000805a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 335393048 1250 335391798 335391803
    0x501170d020601061803050a060606110303090d0e01140c07090c0f1b05010204170a020103050112120804050c0a0902040e0a050c0d05090c0603090d0f02030313030e030102090303040f080c0607 84
    0x500843e8202107081d500201d10070204c01e1003e1100c1c100101045c000c3c01541009440390401296172482c20f00c004100c1035000c013082509030010004e000365410002080f4135503500c9400c10480d1441200c0040e03c11403091400281d10100004d0764421000c0b0214590056801d510020003000820f050101c0d18800c0f221740318401300d00b40c4480e0840c0706003052910f09440d485600058581504d4402a40160004000e00c401541c00034402030219a014026140504030381c40300030303440b00d0f40707500ea030001c00b45d680175058244842c081c0882c050107010720694910820291410391340700d98440e24803009500030b1044081d21440c000c04039040d02550301900d40071308041c9036103d05000040140360000c02014200e1001c034032803400307003c0c510740b114400b4500c180c2c200409050303254000e52001d88500c02158001085400400421014840483d45644442d80500d89807110041c1c400c0800d00910811a4043d410320021074000742031035039039900100340c8614200342c45c031034928601480b0b440d010b520f500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 335394298 1250 335393048 335393053
    0x7090501061d030f0307080a1707080c0d1506020a030306081207021005070f11130902010f0c030e0603100f24080403020a152f0315030f100501170d02 66
    0x400b00205a440200c5070b68000a040d240130301c14003c052071850380120401c640740032022a03058615134200040e50f4004914644114852422102c024120340700204030785501d69000c110074190120540c4008144101c2005031062507446060107546c0707481030281100081d01300034000c550f1060224603854240207124225042a07982e60806c044407144480c29001c01c4010702440004c41c008511400709a80603d54801c070008070304060004406203851760b00a840c0c104020840140da001101c04402051071400b81c0304040e070b9140c120b80045026403040d034402804028001c0754210940880c0456040c007042d000b0003680c8090658080400d00d01c1c44d40400381415203101114000c07245260300510910641b001c04906e6510314462084180701402d0407691109003455920035404880341d0711300000d05288220401180c10801c6100c000c1c61541d40d412464048100c58a0070410130f440f843c244015034206204000b20f40000b0482445002204102610031000301800132400c01da011410303601 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 335395548 1250 335394298 335394317
    0x912090a060e030a0602120a14041709030a0609060e071a160c0e090d030b0d0c05151605060a0606050702030a230109050309031e0607080703020d061202030709050106 73
    0x410b8500c2400307400381503058051030400c60000741c5544024005071203880c400b800141042c174260412104060041c00030482c04905000100303070030041149240c441200d220b603954190102003820080072110040149003005240810061141c101c0202120305000b20fa41d0940e41d00c0000c0030340c2840c1d88944042001c10042500c0b1500729040f8003072021700130030707804405580c1c07800304070080c0030100c07070a441e541c000c41c4500c881968140a10384948000f2505240400443c0e00c900c3c06121192048510440840000860038819038082d90404a01c3c1d000d09040b212103410031030f44034001111084035980c503205c004039440b4010825030700c155030050020100007040341d503481e100320f030310303012043d01d41880103240001000240a00c130f401c903204101442c1c64842117007d040c54401c125a04c08000400010320345200f020004241c7e0340f10030030f403901c0c1d03209803100c0a0680080c4215540301d44400d00b44000402c0703000200c02a550080e10035821070300c1c2540c1d901c1448044920a0141c20000b0b0349130780 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 335396798 1250 335395548 335395559
    0xf0a090603201c0218011d0c03070509120c09070504140d0f03030c35010f05100c030306180606080a09030e010e0105090603040c0e090a080a2607080912090a 69
    0x40d1860f2040e10181100d000c55860051541c00385500f42c0c050403049020b503902c00c030840c5602c0c2c1350a070040c403070f82000c6056050268000c0c0050003050341a50103112450107801c8941c40c100004281544040c001030082e050a00d00182558060701440a018090020f0001c00d0b0400c00a0080c1d000c2d006451114500c140b540c080300076140c681c1c000b00c2000702414644072075050310600070841c00180d0540a504000034100501c001300b0507488207541c00c190380403c214540f20004007100c207801e45e181450000c1d8030351506600400c0301e83c101003ea11420300502e2180111a80414140c4090b84c591071901c0d51081c3c6210300740c1d055440c00030001102c00d25450703195401103440d0303410314005040031802c000000c800b16226400848054540600c1900c040025400000100360410100f4018002d000c046455880c03240c41010002c004010089050302d00c1e00c4010140313034484d00840c240501c5203040c0303502d00820070700040d1600d80d040e004a45c00300c0d1199035030303000f210194440602801141803510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 335398048 1250 335396798 335396839
    0x60315010503032a061801060905090706080c0417030406170720010e03030903030601030e0a0b010b03070912110a0f14091308070b1009020703120b0f0a09060320 71
    0x113440b01c404034068000d103440007078000c0c40700c03a1003550750400e110001713082c1e070910500390382c1c680c0e0040d02502e1501003401401800400c005080ea0000d04219804e6210b03418071440c603200329800a00c40c0d80f41101c4a1200326000310040084480035030350342c2403040d800040b4091404007603e1000c0481e510010b0a03400c0614812081c1184041d140001160312800740f080d8196403045518003402e800000030460b040d038040c49051281000f1300c00074076142809a0740c0d000c11002c1806101090103000c800100b581d880381d0035480c01741504003003150301aa03c0d850524040550000220321443d031001d004112401c41c1c0001c2021281c1c0141c0000012074003074103000000364007070110604401c0c3c02d030900740416090002880403e110f40c1441202d850040e08007030100c050343d0440741c400c900410860000c242e20100350141000813100004400101034009400100c45580e00d9400c110440d60000d541c42e0342e6030106040724001d1401c1d80c8110344070600b1008603100c42513010740c03140304c05000c03400f4000703803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 335399298 1250 335398048 335398087
    0x93018080c130608070b0c010e0f1002070f080f0c0709020906040b0c01021e0705010506090f061c020a1d150306070c0f1b060f0207060f0f0c0b09030306031501050303 73
    0x8500005030864a82c03210f24101711158000100100c4005080e42c6940824899158000610390250400d107039120031041c1c071901d0707004450750b2064000c12100d00303100e080c070315800a15a2112030309035508851103910215410084c100c040c64015102e00040d010128000c640154030020701e503901c0d044c101140f0400356005008030012645d424000e12280000d2000307042780f0400380c080b419403680003a00c1c0281c00c1d1003004010038050800303903080c000350408050001d500101c04031a01d81850b01e96403080d2001400044000c0e40c8403031144d00000d04108014405c0400e0f091680b80050161384d4a800800101184604650180d00080c00611802d100303901850011b44a0050b084040f02903880720222004c00c0006046488514582009413982000f04070b49114000d002800c4402e05d026400380c020f4400710320340020b10922042d1144c1ca9031180180c00e08141c0e20845813451410441011a80e0340c104460b890702900c581c260840c0e0700300002d11264129203005000b180340c03180b5201d61125aa04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 335400548 1250 335399298 335399329
    0x60a0f0504050909010b090a0b060313080c010c03020a18030b15030a080703080f010e1302060a030e07090905060601080c0a0f210515040902090109093018080c 70
    0x1051001050790340d140d4614a00401d040b4002045a010340400c102c42c503840035003580030703a41c5080d9500e18270307480744801c2d240d200c6182c0070001400b02e082c1c1040761051040c41401d0655504c0c01c62032040d901d8160703002c2c1c510103400d071743c4501c00e000c40720b684001c3d00c03001404040d11078007046000900b02e001c10001080b0640028003500d208180c141c0d100c000d5604001c400b280464020800c200d41025821842401020122100703522400e268404140d00a0b0240340603004003000071b820040c0b107000b078010b80004045d86048514580e41c9145990041601c04030840e02030180b0f00100700340350b106000c807a02500010f010640340620884065071084840e002c0c030010705c1160004a80502c2e46030017103403e07640c0f42c4100410145800100d2043c40e00d0441c8149101d40c1ca0b011a5202507125680842d0644811720000124034043d401d04c000e5121070f1b0406503040443e2400d400305103003140707848044448030f503031514041c0000141c6600e0060200d030242402552042c0c2211495180c0000300950015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 335401798 1250 335400548 335400557
    0x80109150f0e030a0203040608070e0d030809280507060302070309060e0a0f170f010213030206070609020604030305190305310501050106020d110102030103051f0e0601061706030c060a0f 82
    0x1031a10703902c503056800075030f04e01003d42c1010404222040c3c10081c081e07400005840c003004070200c054000342005800c503402030b0400000a0005810040800c0b0460800300c480245108030203c40194240c9031400440440b2039005198000802601900079128000da150311840e00040c200301080b9840c240c1206140e82c0403540880019041c5041d4400402038441805540901130022400e140741c80902c100181440e0301c100074800c1c55010003503048040d25812074589545000c2824003e01800c0ba209001e944000002000000c00d0b4000d070003413040d078817000c2038004040c0c000f440a0b011200c085030302204018882ea030018481d420058025404065071071154805085a2952801c40f54260009800b41c1d1000c0364943c001500114a056646c040d180254550742c1184d540700d0b2110b00c440c00401ca502103200d0380100740040f5800c203802e200c00b1182200c0943d0ba56001c02840605500902c005e00301d80c0e040403070050305000c207802d0846e21000d00b1492500218500c00c07928a901303110140d0421 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 335403048 1250 335401798 335401811
    0xc03010519051f0810030c06050903071a030609070c0f02060901052106011b1509080d020712080c03131707050f060603060f0f04030c0c1d01030c080109150f 69
    0xf03541d0118200d1841c000c1803600c040410030004050080c1c00050408040c0d01400341d000c00002e890a2000c00c00d4600c2450403648402c00039020070315007802a004401c1c0f441c1d0035600b141103104440c025600c1351300101c6500f83c141d01c603500d0694074800c0e2032001900b185810b00d151005400c124004080f40101890b0151500c96800c103910355101c0111710070607a45000c4c3c801c1c49240c1d82e0025501800c4070100f4405d1851a40070350309e214212020300030103000c80313031030b090ad05080c082e03801c054660307000171071909541d49c00b00c51402e80d240040101c0000c01040a05c0c0106041c80e06400c240ca200360030f024a10b144503e41f60721418280340341c02c07019625510080101c00d0000300203018841c0b15807603000080000e402c1074000c0505040b4020540c840411654041010001070500c84580181d01820800c002995608180078910107541042a5a024005049040e2024510340504981c055140c903d00c06485000341c84c26908012070241042480b4064071105c03c07a00e0f4002200806c85442c00030701d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 335404298 1250 335403048 335403059
    0x50c07060f09051804021e0310050c07021302030105150a08060f060c030f0304050f0a0c0e0705040b03250212070206090402091c05011b0503191d070302010909050c03010519 76
    0xd0709034514034a0411340a034000d120071418a000c0c1c4d00c80f0031100010504ca010350407404656544c040504040e01c55480d0b00100301c81c00761072070881d84465000361510410080c0d02032040040e500c03c0c410240185c10a011900c076209031030060740c451400f50b5440c00015100c40c1c0410460116803003105034031050400c002100c0d010100010815900022080d685034902400e015046c80e2400b050055203412080c40c1e600000c600381062015551500d010314615100c02c0000c54460003035802002120800005106212002030b0b16405003410072001709800541240b8100d0b150030345440e44011082c020700c5400018504080038000c42600a0401800c0240000020f40601c40c503055460101443c81c180e070043c40028042c4000f0b2258842d09815000b04084000702030b80f00090000303a08144425015101410541040301c2e803000e668030070081c914170650940d4407058203100480c04240b111200040301f580034024a449444501001402d5030b2030302d4107018030912000110581c05840740d07400301d003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 335405548 1250 335404298 335404309
    0x50306150d090215040506030105150c06180c040606080c0a03020f070803041e0f060216020405010b09040c020f0601060c020310060e061509090a150e0112060c050c07060f0905 77
    0x9202161000c500c18905005201040484c1a000d801020b41004180066140d210881341103c00c1510280d131001c0c448034184020307019001300314420703005a00038001d91080d20003450500c1c0d008030007176907140403100c01044225002c0d440f503030021034000f0000442458a81002c0c00e1115020304002d071602c00910340e000300980c410001120b281070007000740010700c00040e61050828545c11000c1c1d1020366540c80d01500d002d646040200443d4000901100414448a4030001d20f03901510070b0080d0f5840c1d1115005c0d58000e1107055004500c1d222280020174800241c0000151025000d030440d6401c000d000c5800000f610300583c1c140c07051407107030100a40743e031042800418042105000c40e041003020050340c60b580c942456220f64080c04419183ea840901140d04a0041100012110007001c86c5098002050780981ca240c2d41102c00054015080442040001d2180350f0800198140540658880c00385481012151b030200e002401228083c1c042500c018182c3d0614815042c2d441002a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 335406798 1250 335405548 335405557
    0x2406040e010e18031602041104080307060b090a0b010c020906060f0d020403020f0a030201121d0706020606030705030706050a050d0b0d0809010206070f0c0204020315120a0506090606090705030615 86
    0x402c518620402403802c000003200444814014050351400c601226030141030701604401a12032681c484004521252440c120b03801007400700150383d00c9007528100300c401040d40300c06c42070003000c1e050001900b4031050f114002580074140c44085520f80c094090015420f00241a80d41016081007c0101c1a14001c0500003107518038601590300c6007107206200240c004103000d54002e4040f4101400140c1c1c02c01c00d000019889624001b88540100c5280300704940318400ca403502d401341c540c0c0801c06a0380030034500d02c108802c0d01258001c0c0d96a03418503558503d103102c0d50000480500840c02054070400c01401203114845020929291100000303040036005c050480c0c0d0807500090700710041d6018456168010580d003030551050140807005008031822100003841581e0010004001c06510002c084101c040a0721081203d005160100d544400e800b40c10b4500c2d10038080001e024050004000703200b118058022181604d400c40e0559440d00042c00036680210700600c070b90156000c000280 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 335408048 1250 335406798 335406809
    0x6150306040f0e0714042703031b1205150d0308102301030f0b010503070e01020f01051008070807150c050a020909070f090506061b07030b0903040501172406040e01 72
    0x10450107144c044034541d1000308030344281c0680d08018040380d901807c24407412007840090b41c5132040120a19048004002c82410350300344840100c3c1c854400b0f9400880d9103642c0799038031010001c681b160039000e1105683c040540d0f070710910a16141c0e00203842042c070340380c200516100010380036444641d1000200c0100310188600b0040200d60302407580c0c580149400340d443c22404111240b0b51000081c10307444020b1045c014080ca0074106c0ca0264400c00c130103081c000380344000300020b007442c0c007100402c03216038810391840c0c0c4150100410b41c07150101e58a01194030040d200030000c00140002d0320100c52001c401e44050040e00700700005612544441803140d2221000b40c04a04e00f4880d980c01048010341000000038504010407110380c5a610896125125100000140c0301d1080c005900d0140550401480307000d0f0801801141d0000001901c15158242ca07910034445601c10038025096045038224001d03c9094a007941c031141031960b580d4000340240003540b030a80c4a43e0140c803214401e0b48003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 335409298 1250 335408048 335408053
    0x4140d0f08030f060f090711070306050a050402011103040806042d111c1505150303040f141008040f051c0e090f010b0a0503060409060c02010e0d030506150306040f0e 73
    0xc021000820208580d44a0070441da80400521685c002c282044001000712091100300a0175400c05036007040010021541700c02c080c046031810441340806840d080e00c0c100d001c240c41da8401c0a5941000c810390302076903400c0004001070350315501ca501000b600300c00300c4c1014000040c0c07400d220460703100d1808071003070080820303a0441c46504240901e40a110450100980d40c00308100000342500b01c0340d507401d04c82c1940124481e281c4405a1203015060343e00964184030000e00000e00c00030b113084000484411681e0303c44034841d01400d00c90700d80b810008000c00204a80c0005002607404050507603018001c01c1294482d0558070030603400780c0c2e18442800c01040140540c044a07240030b41220380d21542000d00b07500607504d0040d820b0700c2805401b26a5041c0117000c000101d07280c5480d44280e00036500b129050000da01d0701d0310041d00814201080c11054003a09081140c86802400b40c58012000940b1000c20412124503803030050b0005030100c2e500c1070701c17a0ba20b0340301c0c0801c0d40500103600040601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 335410548 1250 335409298 335409301
    0x30606030503130b030105180c0c0a03080103032316050f060106120e0111070f17070303020316020606130b0609060c030901020f060c04030611090a090518011104140d0f0803 76
    0x1540d09243e0740354403101c58808100018030458480c0c0b083d0020500c0345420380b264540700d061611500d030045030090034941c811034005009056022403035a040380e000b612035441108080340058482807400c682030200351000c00c02c48503100803505803d507500c1c0c021819602517081802005013020001ea000000041c03080c08031907034811040c440d58142c80498402004403a08808190000b40500017024080302d585c00382c12000d02138142c5000782ca104925003480d0350341140e4030b0080d00030740080c1c031081005a01c0c440150501800050000d0083d0702c0101a1a43c0c640526005e0b000303040200d007410340041303007400500320640740c0001a0407803c1c1e01034080c5440c0d00505000a00d404001c1441c00f19035032201c0f090058002000c01210141c0ea007080d00840c4c850001401e807101c1d44118601942c0007442520300148050980d40068000c6050b0078003600380002c9540440e003a1501c01c2034031205c40d5003c2100304401003856450102c0c1080117464004d00c1c45040d02c43e01d291000445060351007050010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 335411798 1250 335410548 335410567
    0x30c050f010507021b091902031308030403121a03060a0e030f0304080403060506180606070204020403021c1412040b0c070b0a020a0303060e0f0720030a02070f06080408030c090406030606030503 85
    0x200340790010001583e103420740b454402c18090000c0e514030202c1c1f0005a0010100722103101d591003000d4401e03044207032242d4034181440c00400480000c14007502462811103260709440f821101002c1c1c460340100180b000e602c80b07507450030040601d1228241d0038801041008003230b588401c0590311850280000989070f034610304180054400c0208820710900e541d00903074007400100044140c10490a841460701c4940e0f500c0402d000307104982000c6d40c071600384039030165164186801d50f80100c2c402e0342054410030b40d01d10401e50b1a400303201c075140c000e04180810f100024841c805005010400c008650059540b40302c00100d84c0c1c0300d1800000141c106c17403410401c1c590940200700080c5850748000d5003900c0c10010f0b00d1100c2c40081d00e280d003000b40b0402c203007c02021145a4001704000301043e01d680d4580000c0180d07484540e4442c60b100d81310403800002c0c40b580507002c25441241c00580e19440d65841c854440015403144030780a82c080e5450b04084041000b51185034051440382d40110395074501d1a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 335413048 1250 335411798 335411833
    0x807050a060306080a11062b0b0a1d0406090f0b0a050603030712050c0703082a0115031412030f060924060a03020405040515010f0f0c030c050f01050702 67
    0x1074020100b41420198104103030032001454007001034004034100c0c000b098100010384107105010540d000095105c0c050060b100e40000401c01c0410f21500c100210070404041c0f1000078800d00c96910740e840d00004904c108545540c0095100780f18000015038030045580341080044d803240d050728203000c007a00b005055551071040f42d0b04120201d00030b504080141c0c3d2003444c460014032607041003000204504280c81c0c420445800507507449984192101e803e020f10001c002c01079450207101c00f030b9840307000c5101101071180c184041446080e400c0000c0c1035860703160250800c40030b00000341c441c144980034030301e242502542c000c103c50758010206003006410800c0c0c0400c050244400e024815202054a551101d01e880b4280380036962191a0481d1000a0f402070003964459508207040204000d60006031841040558400b40ca0303800c084030a401c000c0b250364103100140ca011490541040c0c010900800e0f1f807400027840f6800300d4032200d0050703070400e0030f644090b0f0794500036034042c00072192082800e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 335414298 1250 335413048 335413069
    0xb0108070b040b180901140103061a160c0e0702372003100605150c070501051e0c0c09010b0703091403010207020d0503070308060402030112060f0e07080705 69
    0x420040a455041200c0c03401d941c85103214034008020005100d075028000031642100c1240d000b40203420940c2d540c03003c01900d40800c4c052500007403a151000c0350500701841f030f9100004030000d504e8248102d4040c9040b41d604440704c203850300c0151110001d000800014840d02c140e12590181045030400c481c003406a411043d51035440707003487c1c40000ca6080700d03410740d102400d41047c80788540749494503d0121600d000c10b0521740500400d08800c07260101500948200d41090381c0c03411540003c41e081c075609002d0720b20010b003187c11002082107107611410290080c00003030281c02070139a420140d0003410f60302940000005400003480005186400803585004048803007074246030100d150f400034150180d40c0144d200c4002200f41440c4240c40c25410703141e40c10f034041c01d000a20302e0306082c4103950ba0480c0004400069101d0005400b5003864000c1d07074101d8100001e01c00800304665102c1001e4204962002c804a41d1001c1400310030104000b9000104400b8002e003071568100414800440c22 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 335415548 1250 335414298 335414309
    0xc0d03140703050f1504152301020304080304090b04060e09010b01030b0f1c0c03051515010c03050a0f0c0b1003171201261e010f09020901090906020706180b01 70
    0x600f108000e91302a62442c070550180481104450191034000043d0040011204202c0180558400070070900a0f01c0d03040f848905032031440811400c19003004982d40d1103107020346e07280c41d0002e000401200381d01390441785509000070804502240c1703480c5212002d90003100c0c240701c2a0f440701103d404c25601442414a258425541c41c04940c160300c02040725610203460a04524450b420300c10140303c4901003c40c090343e400404c1c0c8034040b40c01081c1201d080c0d4250b50340300e4003152180c6000201c0d80500c1d0700462140d03060311500e00740100700100703560712030142d8424002d001100e010000082c5054840301e120f404100944000c0c10b0440c2803403c42110344100035200300004218184980c10245066411501484601c043d01071081c181130f0340c000084020f0b000d6510402072008545007000740c056a40c4030401008000c02e13005d111018080c0c4002c4180650001c1c05030006018500180e0480c11256000392005441c103981540c5010480e070050841206444425107980c0400c9030030120f04e0300504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 335416798 1250 335415548 335415551
    0x20313030810270e011404030908030c0a03051b0d08090c040203190e120c0105040209060d030f12061208211b030627190c02071404020c0d03140703 65
    0x14140402d503188100b41c8850080d110901c4009600c0386510f079000000750203c11030090000700c4404007042d40b206000d5070304801080b10b0100205113032100105a075440b0040000906400d01c10381c0302900c00358440e8a09148c1030b5003207411080e4000082041503107200669441d1500c030302e400c0070501d003000044284640720314010020310903e4840b04013030458100c00240c0c009502c00d00003454901d41020032100e5140c50f0307004543c2e000004419030107244624000d456100880d40c401c01004011a038007200140401c94244c007100c0040e00c00c041c0001162403207500001c07000e4803202d01c10b89910b400300c0e088030115000135103503400350207030002151340441c0c064401e40541061800002182012400c081b5440400700c000340e44c503076850842e11030801c23604417460500d910035451030312682c00072550034201c0000040d22500c01e00803445030f19241c00540c4d02906800742000c0070301d1075006e42e0f440100c1e4810340a00c5292208002800040405051601d00003030201441003a001c40b428000c04010915 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 335418048 1250 335416798 335416831
    0x13061b05071e05090406230c070303050c13140a140a0306051b0c06040203010b060c070b030903040807120c0b0304030504060309020a0b19080f01060c0f05100203130308 74
    0xc0c000007010300646007040c10480c0481d99078500074410848580c0300381d80c0501041c1c10302040c8095903120380c002d21000e00310704111813942e410044051100391000d00402a04100701c5011034403d03800160042c031100207092a0550201d1040a90003080d04603490003108018040354514006508000421902c0843c9051200c42c00005900002600c400b4159a484034005441e6180d4815414881c48040d42d40355298020030481681d2a4001c0b40c00f24002c0d841c0c220405440d01c9c2c20310958070911490001440c10600b4445402b45641019042d5455440b00744000709840405004120107800c0d801c2c0240d00c00e20507800d000340d01366480d80c00b132002500100144801300751f00c5000c503000d8604034240413074031032018030201d110301c60300350b002000416002c9480c561031508031808a0001855584440c0a0380b14801c03058040380b030038840e407004503000702d1004c80040d0b115191940b14901400950301c80c000e07035419132400d81e401101d040c00c00c068030500b04402c141e0040125a001004600441c0f050f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 335419298 1250 335418048 335418053
    0xf06140904020a0e070909020714010c0905060a0c060b1f02070b0a08060603061206041b0512100504030c0c030b070f03020c060606090301090c03060f0506011e0507030e0613061b 78
    0xf0606002d1110507400700030004c1e42d00d600600129005003503030744045680300003a06003100e02c51205504460741d54200018124118800e002d06070666a000308220325003500754005031800605400c00321035964441040a54642d1504e038841c02c124141050582042005034000342003052a40040c0d0b2920002d00c1204061544070f0209640580103403040d558944480001400044003e00703100340503c225403c1200f00518202130743c444c500f010401034035141d1204100204406080e142c3c0031240d01441d0b441101031450381196801601070304000201907540d44807000048219041565070290711420711101c0c42e4022400313580c8a080380350443c00c5c808100400364403500007800503132040d08040740d5400315a40039407040f8441540400d10a403869076a01d03041020f0801e03031100000c410b05d400c00080303240d40642a072a4000100c1d408040e9a410082c0003550a5008180280e003040880d0700041116220100105800c000c142c0141c4002c600d0100f00621030711102e19909100000e81140800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 335420548 1250 335419298 335419309
    0xe0d020c010f0e0d03110712172803020408060f090a11011e030506040e0105010e2d090a0c050301060b0a20032107180b0c0a060f0614090402 62
    0x503280e024070701801084000716007101e6440c0408035040e8032695183c116000c064000081c00c0781541a007040d52141503480c040740c024a0003610001d8494114501c0d410160100a0010305e01e220300310320401c601802e01614200e0310000314000c00c01103940054180100c01082110951001a04494002e07034a01252070a44074480c0c85401000d015508184e44960781c090311801e10985040600328400703040300c100007030141c6425244680110b1420f0340020601406000715810b03506000b90910240e11018207080c0c10030050041900c038003446850035400b145103005854040c41410300100850140c82c100f441d0303000c0103544214401d81c50560200303e019068030980740ca160041c01c0c800d00445004607030080d07d100d41074106c041800f0010303950908542d0020380011094115200388000d80d640b441c1a030300f50303001c031040340307039072541d05c1000c10a13510410000c1500c084000c003550000d5185544201c255004c0000e0710301042c2d2a8141407002e03c0c0c0c0307070340b441104150485070f5110324100741e0041072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 335421798 1250 335420548 335420563
    0x12151802040b12010e070e0c121602030913020403141606050d0f18030831030338010503040803150a08060c040906050405070e010e2409040e0d02 64
    0x900030740d200c2c0d06080041c3d995074030300c05aa5510100034452003c84080d02c94540c0014003883c608a6516004500e00c8040031059680c6011601c1c101c4d480350700e503049400200c441141c803050451004021180300d94607980c401340107a0141788409a01d881c2145015007000d55103a90301c00c06540542500d50724a05081500c82c212001c0303041c856a21640c5020441c00b40c4007c074800c3c103180707090212107074101e0040e2404002d0b460281d9101602da1302c903100c0c5001d0a0031040544070101c00ca04180e44202411100c45829480c0301e800c00044555402c10f00c00c011518000d54414180b00d01a51060605000500250800007d2a2180c65403030f09655810b0107010203041071004d40524022440300303071160200308000e040c3c1e503811194603140c0100c10700c03007a601070f0060810715400e11a0025007030401d8050030f400790100741c8919a58219150044903208005504994082201e0503070210038815210741c0800100b0001490750b03550302c680c00380010f41c2c945004002256000d580d00d107420320742c04610032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 335423048 1250 335421798 335421803
    0x1523101b02060a140c06010302090705030108070e07030f0e0706180501080408090a0302060708130e040302060a0c09050d0809030d0504180c0507080f09010e0306010501051c020d0204121518 83
    0xf5140c800040c012070b0311140b0320500001e40c11001520414a03500082c4080c101c0303208580c90382d5a0f642c2d4a800325840d00080c07249892640c0881c038180a810500b8031680d0b41b000c500d02d40042d051058114607030a540c899403000c9096000600f007482200c1c1c4c08107207002d2691a5000c261001481e0400007055014001d20107841000c0110300c05181d80da59140300c900964000300041d403255494107011600b82d2001a40714480c005004c0c0c0060a5a6298426407082c1e8054018082d540d445034420170244ca01c40460400b0440030310320200d0300b65500c0b500c40c46000d000708803a5486070120f10515107030100ca4014034090110070302042040c09039009882803800888440410302a40440095841d40103034000148800d4010a01e140c407110000090805000c00340c1c3d40c0000000c1050034161144402e01070300340041c00400c110702c1006030405895006806c1a0b07001464500410340c91800c90301b09070811805081c2042d41101030250107551581c1c0a05d40460070880d440f1144011241d4182c0d070b1030300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 335424298 1250 335423048 335423059
    0x90916060c060e06190b0d020d03080402030114090c0a0e010b0702060a020a021c15051b0919030b041416060305060d0b0c04210b0a1523101b02 63
    0x240d41c20040c03250011414150724904556450910211100309052107007002e0035000c0c034040c030301d407400d142070394007003982c03503000313043c0b40b0b8506800e80f0103da1040c0700400030707a003540d02c2d0703030a64203482c1072002014401d0041c032014100140452080049075502c580c840280c5030110401800b40030b0800c0c08440c8540d034100c401c156620040002a420900c403140701a5000110080383c0004c0700641c00032b540c07140e200d10001c2441d04005c8014004541003071350036444a6104040e510141c04281f4000c2140040040080790051440004040820b66540049402001420600c42000710342d601c0c0007120300c0540060005500c2032491003021385e18501c500820140c48030b010418a8451500007110903800c5007503600706160140b0044519803061250020381141c1d9920714000004c103030484070b03c1c0e560001c1c0d80c2c42c40707482d080c8800001e00002601071801c942c0d480c400045d02c030341020810000c802e40611200c00c110501e400c01c80401440d210510500450f20622821444d804000035500c50b8100d40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 335425548 1250 335424298 335424317
    0x311060c070b0c0102070c060c0b0a020c0c0307122d0303150e07030902030c0604050d060b03120d06030c060e01022d160e0601051201090f02070b0406090209091606 72
    0x241e00d0089079070301c402c50070303103000401e6074000006400400c085030081d50f0295001755110b00c11107008141c4400504550700400200e071500c00036800a1861140c003070200d0f600300d0443c000207820041160700000c041c2030000310036800c0045540c601c40c0040785411400c0105158000c07200c0d05000b9041c002003c15076140300104030301191400420242c0a10350840711640b80030b410244c010601044260320038421140201c00c140b0349001160152600903003181c142d0700803a0f0300d90010700032480c40d542d130501450040c90111f0b000c1001400f0300d280b5007240421040d1850800603001e40c080e8020348200217411407480c80590f0001070309200c034000c0b41c0e040341d00da400358110000710041d24000c0301124059080112244030307000455400762540395180c10b8081e222200150f800b889407403078404030705124100401c8142a00e51100305003140c115005490011941e80e4000d20140c104c8044840c1c030fa80da0803d070154144407682c103610000c030b00c00500c604034174980303002e26480f076134400c0700c0800000f401c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 335426798 1250 335425548 335425567
    0xd030e010201090b07110f0c010c02120309040903091a09012a0b100608150319051f0e060f0903031303210203071b0206040509131a070f0801031106 65
    0x18040f02080e82c000400003440e08158000a1110400ca10b21000c207100d1800e10340c00090b404a01304000403c161641da50a1240b0790900c05c0b4101b051040501500040c40784481c2030302c450040c140c0640c400d60b0782e0702c802c41c189100621061107404020385240d4051048105230390b003011001c1030000039041c6800402005082c408c20058115100500303804411040c4001d48041588880907074009480d00841541d44c910301c8288850701c0d189203645603102c2441480d1004280d10581c1c03100b8003d100785c51051030003003000c3c0305c1e110000c026000c650b0f80d51000d0051070301042c440c082d0090040002016603013040c00d1615603900010b0042c0350300c64aa803100e0b00c01c040c00745095219100f0341411001030046c091030550b009400846028011848103c0ca840540d050700c8030421825078000c0400d400c2c14140810300002403c010080740100e0090b604040104220080c1d808940e80c8094207100d0900c0c03d164001c0607404524624401d02907640010310000b00400c4516140f0581559455116a901c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 335428048 1250 335426798 335426801
    0x8060d060f110309010c020105090c0603070908070f0905070f4506030506030d050403060b130e060406060f0e0f041118011508090c0d05100f0b0a0b090d030e010201 72
    0x24114490a4034000c042040e040080b800b0314410034401d4020000400e1001c4140d083e540304a9a030038090708a081c10446d40d00e0302c14040d64201c840e80c5054002036844181e0903203482000d0b040010031100004040100d110540039241e4041d17898600300c4400681042c01510079241c0c01c0714640b2080f5410300303104800d1075440f02c40e5032030010310b81b0401c905080c0020321481c40140e802640000ba08002c001244e5080010304046481525904c4030f01e032500d5502c0b214014200c01c85810b17403141842409002510590113840e40001a94015011600b40f924140b000c5031100d0740305e01410720341c502c0108404102040600e501c400c110380c502c02d490386c1d1f614003110800c0b00c0d00c0c1b58035440061a05102c89006800c00c41030f040c5c406c0110345402c07191a00c10142c4491100f10384000c00d41d80900780c10703180c82c100050440c0355544a00120b86818500000340d4050325440170300c52052660303405011420f850040c02c828020041c120762145000412400710704904038a9034043e092002d44800700400d64802d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 335429298 1250 335428048 335428061
    0x3090303150315050f22020307030c1e050907050a030b0f0a1e0608060f01030e0a02150a030b040603050a12111209012712060e2509090308060d06 64
    0x30350004904141c2c90346800700d14061850f18412441e0310b40700028001240e14500b03e802100040070140161803407a00d00c01283c00c9205040b43c040c010104000001f40e0840503990241040d90100580342c0030195030000614039640c0400e06c01c1000c6400d02c0050341e000021503500b554a8034008c00d09104010114022415010041d50094148000011068005100c07040c03140100200d00c1249aa240d00803103421405603000c50f0b0285280400341c4480d800781d171000514202880680d10855200c0d00065000d80c0318020907282d501d80040c11550b602da152103010000d0f0000ca404208107400e5449842d914034444500524104003440d8548116000b8607168100780720f810203c0740d641c92001c0c03a01c100c90b04002842400b003181c8100118600025002c2103030000414050905c2d1a447e01c1d64000351580c0c90303407040e6030f071903a1403441c0405070302e00f4810120f0103006041d000428190086450319440540c2c2d02c607020007880e00301750600003a0300410322908600100c4d2450b501024a0a001d03005110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 335430548 1250 335429298 335429321
    0x1090908041203020c1504061403060103090b0709050f01020703170a05040f0303030207021e09161110050106090e0c0306010503060f130b19030305030c03040f020319060c1e03090303 80
    0x3110103140b020181e00180c10b40c1501404c0c1d0301e907480003d0340c801c3c48490780140d020f06000306507440900c6506c40307000805154040c005250106040c0c0260316800b00d45501901c2c0c400005245100034480c50600a415007003101c02840104601451740e224401e0f0704d20a80740101d407404002407112900d500c50010740300035014a00362052101e560b494007038020750003404124019444024075040d600c10003103018002c03601c01752040002e03946400c4040d41c41c001c00c0c0c00481c00d1000c0d0b40211003220034104040b618001488800007030300d50405201a1000040d9440603842049640c1002207202c84c03102540e03008507003802c1c0a40c40752552400210302c2c003105510b082e0046a8071003080302c076240c240c05c42c49006c5401e907000f50900b1041c4007440380c107012a00014002c1801000407030011080200190ba10034040d10741c880c0107200300d0380080d003800c06543e589180c0700304845d4460180107040c07003402100d80043c142101a230f00004942522900811440014142d55488240505002e50405180c540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 335431654 1106 335430548 335430569
    0x30911012c0102030d06030605060915030d030c050918070801240806060904020a02030c0c030304150c03030e1603051c08130c080618010b010c020105030109090804 72
    0x20004607a14114442000303841207480f0240300e018003842c880c0c040810b40c0d040032010400602c1010301000700c03030841085043c4e01c50b5030000d50410908032a06002c230701c41100c3d2001342c5082c084c0e416081d03002600030b0920000c001a043c400c0d4407035659501c03103210590700e504141015140c59142c911400420342036039040d56003d180f44903803020000b4141482e0810180100c2c0c10390308a0400f04000d44c1c00403444c094104c3c02440035240c0038200790029814180b801106607070442c0e880d844074090000c41c510300810b05100380c00c0328404401074011216001484001e901300c180c9144015500c5001e4030544100e00c4400144c0084da085c0b0b140d5404100381c48001031080043e07004041111050ba1a580003d090a400e12050740b2602d040300c6000031340d503403a0090500b960400380c417140c10060020124130040c2c0e080b0342520b0640e0721000c400680000705190800043c802c40c5c00220524 = true := by decide +kernel

theorem cover : BRFrame.Cov 335251798 335431654 := by
  have h0 := BRFrame.cov_init 335251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 335251798 ≤ n) (h2 : n < 335431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
