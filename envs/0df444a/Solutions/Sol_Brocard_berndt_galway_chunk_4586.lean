-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4586
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:05:46.189999+00:00
-- url     : https://prove2.me/submissions/9c56f1ad-c63d-4003-b12b-05e2d287068d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 824640287 ≤ n < 824820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 824641537 1250 824640287 824640293
    0x20a0b2d131a16260a2c0307021504031211061815090f0106060c020a3f06050405010510060905180c071b060305010605070f0b06280608010e04051207 66
    0x1074080031144808240c001010b01510700441e43c800b0700441b031074100604c5d1808030395030880c00300b80c1d17546000a02c03500b00700300200061034480c0400901c510750080d11810517440340c8485c1d00c00c644071040c03a804203018a41e0380c2071070003080000079803100304012150540388000d0f5445031249003000c0c07460100b040361008207840080c14441c0c854050124402002590340c0c40000524202030080b040e402507201440209810201c2d4401c41200d40701407032a0717104420070000b484017480d004080c0010204c080da0b40340001039540c0c003c003130182c0d02640003c2600e0401b07020243e40105a50300c0303c418444130020420880d01d80281c80d035400300c9154214601660303600300c2d42c0c480344940320004200380540022190b441c609183e580e416030b4242c0d5010041030f80c0380d400554161007511005800c07400b035803240c14001240c001440d544010054004142080501001402c00a800200c030f0421080c001c13003809000c0c4d10558040c010180300c668820307182825199280c40d01c610340d14003c0c84c1c0701d000403c00c00b8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 824642787 1250 824641537 824641577
    0xf16020301060510020304030614010e01050d031b030e0906090103021005070f021309140a0c120206071401020408211e1303060516020a0b2d131a16 65
    0x30003001d460301844c0c0e00000710003500ca070310a001c200c40d42850321071010400100d160300780d8140c035a0f84c00303401070756403e02c0d003041685601d01504904001e60f01c00c00b8040c05103412105600c0f1031103a2141c2c2e01c0141a041003044a40e001003003036002e80d800703600410142e503400c4803100040c1a07030b0518903034074a503605001141c0d8000040c081e410aa011314030001210081e440100c20b24020040000030740611101d035038035441084400b41941949520600c40010703600f40c1d401c40244018801381c940784440e0781c0c840c1524880b80e0007004995000c60100a001c2082c003400800c50b8030751a03011008078020203c81581c1c09a51003e4580c52500b141440c00b2400407011118940082190404110340d40c0c90035a001d0a4219a90030b6669491401034081600008100f0082ea50001d00102c050b51841e01c5200013075101031740c0c58141c2c3c6000f076880500c910410901c5010321801030803500704800c43c3c104068080f28801503820841002c0c0208501c0589081d1031340425941403501c6078810711420001d0b01c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 824644037 1250 824642787 824642789
    0x18090a021512010e01060e01030c05220807120201080a1d0a050120040e151518240a0804030e1c03020d2102030a0207052a03030f1602030106 62
    0x500403480200079004201c45002a1048180308110700c01e1603070301c0c0c035400c41c1011800e2140402184034100d2414896010742c01452540c0401e180a9081045a90342e402c40c010b0b0320a66440801031443c01401004000e1002c01701038010005017400414160780008c14010008001240503036940d103410080c04403920740318541c0c3c0b030000100c400e641c2c12428100d000340204500d0700700103200d10169080001d0103800361000c9590f000010341c8180d850f95101c070002d02031404003650016001d13180150101c1c000c400780001170a03040c403001c002254801800004005010404e5020003080c00000603035480d5003c42c1da5400b587d2030440e0342d903111441e007a05ca070301800f0b0a0540c00f1714400030008242c000050603850302800f039400c44d442c000c8084000c0c2d8241951078040700740b40c1380c0380c078102804203416002150000c120120040c6010382a4454a017044625240b665121039030b2a01034501602400c2c845e40c119004901661a090321541c5010091090ba030b0705900381d0a01d41c0c10340d819035400b940804 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 824645287 1250 824644037 824644039
    0x260309010509210601030c0f240c0f05030409020d0f27110d0809012006070c032006100f051e131b0224070503180d0810060305040218090a02 62
    0xd4250b584916011f1404075003401380f40d148030542e1000092a180c2c2c0001010f01e0818207419038120322402108075618003100300141d8541036071880e40c000180707007040200002d1400c540700507202c0b40d84400c6401a04c51300000b83c520103092004141550b0000c040c0501020700b89450a98004898a80142d080240e04180c6500200c1150f41c44240900203008089903502681d8280607024141c01c26010319103602c010ba4800da10540010341124010f030040b0070054001d041c81061180c07040e0103c1c0c040546e114510704143c00003014014100109082c00d406451720282c0c5258442c100804600c01100000c803500e02d44121204501d010b80b1100300500c6d0701c1c40c09180c14013507101026485280503128034114401446070100c0b81c854141489049000543c1101000107d2744940c20100c0302d540001c0c18140655641c03c4110060030020406081c1e00f582c6500d405a1a16014003648001d51103a4855000c0c1410b09007000300503903032504001007000401d00e4030394903621201c1d101407800b5050704000f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 824646537 1250 824645287 824645293
    0x30715140d0c090801150308031e0c040303080c0c0a06052508090c0a12060507030b1f0f0c110910050d11041a13020f07020a26030901050921 62
    0x507585400d4204114260054403000c64032540c55124034204e4451110044200c035089800b440010b40c0303080151340148082402e03045000c8601020700103200b0076910340c0114400040d0401c201500905503960280555091604100c141da03049034807000d030464010506c50b5524001458844e074413024044411764100100080780b000072000c0e008807815512500b1a115418501881d450090340100603151600c1d0a111045140d90300d030f00150a0280c458824103444500d5072000b600c5012001c405050b810b80c98809220025101174501c60040f0b0141c4100302600e241e50003c0741598081e07000c420000d9400e41e1141d82c03800502c82944104c1c3c2c1203d644a124030b0038120900071001400c1d980b88500b101d0800074544131405c031001180d4450043c9402c0040d03101c410540303100607030140c62204400030090780350184640c00140c55215681080d601a0041843c0d4107400c502005403041d194211070045282c6a584c00000c0d2550140c0703281e5901c6149202c0d0603801d8000041d8842c41901035400c11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 824647787 1250 824646537 824646547
    0x702031c1e020f10050c09090a06170a1218120201090b0309030c010f02091f3b0d02090612030408010c05090111030910030b1c060b01030f0b03071514 66
    0x100a4a95205034560f10389441460198180041c20f40b280900481d14084442d24042526003031206600300188440782d00d680d541d80c0007540da401f415207442c118900354090300ca000c03054988074210f0007108548004225061290030601100b80740f0080a444941041100442440c40125800742e07180e00502c961140210030701c2340e00a0004040c0070030b042800000c0c403540c015140c0300c504a024800425070b004483c002b6083c42c254030815035209102c06407a110200580d0020450088816901c01c0320b4409030300701d141014403214121105c900d181c116401c1c490045940c0000340369000140c41e2911448079070208882d1000c040080b14000e04110009210b0001d03500b1028110750020611940070031007058a0010000c004070440d20a210002d020016280140908074020000036010341c0d08140092a12000000c420304402400e62052601107180300d1080001001d07104a003902c015241c1c10920304c0c10352942d02140e8002030b6081e4000f03841c1f4140702042d08880310100000c11801072a40010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 824649037 1250 824647787 824647847
    0x100306050a06140f03100b0c070509010509040c1511010510080d090e150120010501090e15131e0b0f010b0a1b15020a0809120702031c 59
    0x1541110000c80d80c5000066881c84290fa031419070090301520300c0002c01c04800c42c85081405036401001946450300781e99100d00039089141d000701c041c0d0207030f60b0180d0340401003490080784a80c0940815a940b0509051076501c8246e15400c60066201d03001082c005800c40e20310407a80c0034054001d40c0c1c000e00c0103003010f100c0f04505140c13a0166070864060380d07001744480c9000e010404221020038454060310340d1145428400300c01d03512901d504108024656055210000786d10b1598401d900d80001025450020107008507054450094195000201782d40300d041804c2d40307180d43c80b03045000c2c0001855041d10f881440200351802c502d80020700e07106440217120420703140c1c41c41030703444010310005a62034a20000b0b9500900d040540007408030400401092424000312490601c40d2107011140c12103078144a060b600702e0a45a00018104420050700b01010814201200042c20080c0c3c035000c0341e41c02203600e4489003810501401d90f5407501000700f5120741460000e0f01c000080c104682d0420b25 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 824650287 1250 824649037 824649041
    0x9010225050d080f0a0504080721020c0f06070206130e0117160e0103030e130501140307090c0f140403060207110910141909181a0c03010902181003 65
    0x3030010307240c1c1d2007401c0214040d00d0044807000d0241e09640c1ea01c0c0126070b124003008011b810002c01c212402c2d80d0a00062000403021000080c403081c418051040a0711130310070092500e41e0300808107100d01140316000486403522004c458059406940079075580e10800780c01034051881c0d0340015104440c2c48000203000c5200622001800d40440a690701c010800400e000d1600e0b4502481c17101e030503018010400640101400c451010010f07214000404080c0e85007021035000340e03c003d90010810001c01c0780c92405014900c080c4c6607045081241c000808001040b8000320005601805000c1148121003d03039a020f40e402154844400d550b1489245000505a020b40c140a030081c07280c84045880c090f0600c030150141d5501c8114828099050420405002c010074038403121040b4191000ca52804103003d4101030074020316400c4101002454101e104540c6d10044503007940000c1c0510582e00325a80403281107079007031540903885400d42e01d440d130f0078607502411140e4411b107045c10054140d9059 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 824651537 1250 824650287 824650357
    0x12020d06080304091e060f09050a1d070f0812091207080105010939120b18070f090f03030c0804260c0f090f0702120301090f0b040e03070b090102 64
    0x90f461121500d50905d80300da095030468081c40142d0f0302c080006201c0c00900340d0055500c90700342c1101041c50001c00b100c810080c00d610104030580c4d040717a0402d01c4006490100c0c20300404000d002801d2514004c80d41c685540188401184901000c0a003080c140408100c40000f6080d500c000700844d50752044850002c0c94079000403408458201101107080640c0422418814416942c00c1d0004101c1c0404a41007070300344040b45003013951941c2201c100e4541b8003400780302c10703101701d0754a0403800c100074060110001e84040000300003400f0002d0200398014002c000c00c5030361509111042c040c0740c0c80c01c0211400b80e0b40203c0c1d4907400c0304020380b200401c1c442c0300b0002801c00c00140e5070310348001010300c0002010a400c641c2c001e081180440c014100c1c00030303800d5002c0315a00c156200c2d070110450b131031055482a80200c2406886422162100140e48104080381404039002c10a60482d0315820f600c80c06202c0c009841c0c0107550340003501782c21080d01280d00c0c45c03011900d200b280a4042980c007482101c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 824652787 1250 824651537 824651561
    0x40f0b15040f0903020a110a210203060c040320040906020c0c010f020106080a020f0a0f03150b30100f0608060108151611030d0902100206040312020d0608030409 71
    0x2d00c40d0300324224a05229507891039801da800750903961021b8850520001d0441d04458020755018000240c030b40c070058680c60f51180100c0c12404507203990040500e400c2014000d020540d030100001c00026018000f09a0920002c4000d41c00114100d80040c0081c944410b000e0403543c000100740800e00c8000c1400c203003941090302c449400b4411a88102d00b25526405014043c1d40074002510240c0340202e1130302c488500080a603800f1503100c0c02040700c001125031086031407005050600048404c14040d040240b1000e844802d40554640c82407103000c03000310310080d040514100c5c0b006440c1814804030409032942c2c8030510000f12400050340c001c2180e4030400c2481c0c09000700200d85402d0214031401000400c0000b18425181c0c078104080743e81a500156052254420303500e0481481400605141d901000c80000d520f803403401880403040c0b0500c10a001c6400110400c07001a420484c6c00c0760f200840c00c030040e100c0c0840d10300d02005000c80c0e044220f46100200d000103500340c458202c1c443c0c0e100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 824654037 1250 824652787 824652791
    0xf090c040c03230f130501020f0a08270a02010e0d061406040c09050f120313120b070e031c0c05102406120522050d09080d0203030a05040f0b1504 64
    0x59202030000075800039a2000303800104c410125500a188200c5540c0d600d001c4c000040c82d200240481e00c807070768820341800700415240c504104100003e0f0548000c0c01560b100070700d40760b11000c2c90322a110002c03440000d0601030b40040030b4403942c549848241509130320000400690444034003141502c1801c41300c81303115a0078968100f070454030500d820011150f018001d40c031140d80c1c0324100036031010006010652840284107146811984c4820b00b030043c80341a400a980c50f030340303040030600b11200130496070038400e80080d4040103031400580030b050543c03403813882e003050000f0100484082d0307805580941144035151200c80d10400c40e50029007180d1311416621800702c00316080a5142205114020228a521054111554054006c16030281006815443c5c8000c140c082d682c69400d50241901c5651005480030402a000010400603014400040c41d41500c108002035480c0b10041248050b00e8031103010408100c40b0050451000794040d002c01c44610381900105503098800500b80d1041d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 824655287 1250 824654037 824654081
    0xc14010f0b01020d210e060c03040c0b0301060806040e120f03060a061713050313030501021801140423180703060f030312180816050606040509060f090c040c03 70
    0xd8000903c141c49002d25485011107044501c000e010401000205e0f61296505c132401d8204007003051002c54480c2c651100415142c0c106818062440000c0340c10880080300104010b00220750040c880c15480340d80ac0302c3c04101034076251641414a14110b84055900901240d030b104a400d40f000514400c0700306442e9103280030380e51b02c0c040b281001c1810002e0910b618603000b080d400b248003c01c110245010308120781c42c0210211503100040c50940c030a5445960100b02c0c00020f000c5100c0740325429100740b0303055841401082d801380321882540b29121050b207400300041840200201100c0b80316200034141820b2520050120305107180444040d40080c1c07500202103004400ca000c1681500d800d9910841100c504c682c01d10b0080a0000c08079003002c1440b508a070002e815040142018821240c61400001a62520500e0084081c0c00380c2e1059080c101002140314001a03031036440a07041241d42000e88420741600d0030200b8812085801500344009030b48101e8041c2c0209045034a8120307050156 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 824656537 1250 824655287 824655289
    0x20a060506042a09030f110306070f0206071209082b020708121f1e09180303090213020d02090906061207270801050f10120b070c14010f0b 61
    0x191095030000c001c3c90140401180c541000b00240b81411010707080010f01c042d01c0b0345a00500400180046500c0c2e10f900c80c48540ca41014400541c02080508003c030b00440091000394891400602890400c5154469140b050245030002d030301e01b64000c01034a5481d41601c0c001c014503010603a154a00f50340e10b0b42031080c0607540d8070881d2100d9070441032050400d400e4181c5241c668002500e00c5003202c50301c1a03942113015504441d50000e103070040c40440c1401c0c007251210385030b50507544140c00351417a0200c1c044240081d541001d00003641031400186110941c8000343d440885125204103242c808076444823202c807154010074501000300c0d0a40311030307601c1c001000700b01d00c62000c41c00c940041d20f0011900c15030190356403041e00c2d0300800c96031009081a0600c5030b03150489070300c0b81e0307030f242e455405101c40241e8441d000c5400200c0b2089148440c2c0c1000c0640840d02c03a001c0001f08040c150000007050036115118550a0b15403000000f6403142160f83c40070b0203400e1008112580c2c5142030340340543d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 824657787 1250 824656537 824656541
    0x50103110f040e0a060302041806150b1b0f030301060c1e0f060b0103060515070605090609120c010b0d030c2d0201050904091208010335030901060312020a06050604 72
    0x100c40300055581d450641441e5400454242c0030300b42010b000c2d02e0317100110050b5101e010ba15040501d242440d5001c1403241088c4043e1406d00c010052404840c0009000c01c48040013100c034500301e00074809900e04504140f0b01c1c549a01200c840d2000d01007c0000704d08207500c83e031007038070b40c1e07000e01c0270100c09030a05818500c0c0d203058000001c11f800c7d09802e00c1c00c0000c1e5140c0198000b18014180010443d5a402c0820f100501031040e010340c800c000600d1078200491845019041520b26005104520780340c0c1d00603075591103444c04803100b50400705042d2800002500300b00c0c0786400c080c010043c45101450068019140088200d0700d640002c5187c00c2da070703020512031442c040b0790740c00001140b8880e50010340d1564040c080841e0001d40700c0c1d11290100b005082e01d442500625900c1d0401585103003031244071100002e4000c00461419503000503055a41007898081b10b079038482d444c1c4c0d01d860350300100b07004221a500080c003060010404550b615000f082d4000e02d14080c200c03c0c085546c070b031010002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 824659037 1250 824657787 824657797
    0x108030414010f0e060a0309021e090402190503070f08150601120c05070605010b091206060108160509090c04091a0a030807080409050a050103031b2303071b05010311 73
    0x204289000c469940543c0304802040032802c40341003220103642c03594049880350740302c050044017207615501d1035021402d2245850ba0409015810507007040d0000303000802000000d08040c3c400d50145a010800d12801040d01d030050100608480701d072a60782e035124034104a0b40c402c0c50400c3c000c40d20f1401d00807c401400074481c0034160f5601035080d007880b103064001e085002c00c500c100b11051192000050720707841450302921b014208251244110403c108982e041d854082c02c842c0c021000740300c1b070390740c00903110f40d000030481800d1462510102c4040f5420302a4003441688071039030b00140096a244440203006540d5444000e0040c8240001140181103401c425030340c100340804810408030304003a0250000c0e0f44600401441c169441d1405819500c0660f030528000359203000400030550042c1601c40c1500c14040154140040740d100c03428480c10103121400718440b51480c941c0020400e004031031000d540645946842c15000c081c40c40783c050349024042c04070386058100c01e400403241c400d0310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 824660287 1250 824659037 824659049
    0x40b041e030e1e0a0605030c0408010204170105130305040e0c0903190221030403062004080f07140f010807050d02161401061a0a020a08030a090b0a1e051302100809010501080304 78
    0x4c00582c1c43d1800c200c480b54002010034100c0f030b2040c040403c1c006c40a00061005102c03104004803000341244009084440c040e2801e040b000300e00c1d02c07040c00281c00809440031291503101c0c5d000c5035614100f0780d001d640b0450400c0c40d894040c0c0d5480489200c0f4840c800d030300550080d02c00f10300382c9840207041c0b2407501c0002e1036611180d00034001000000c2c4183c106a02c1c03081028662442e000c074200c040107990300b1642100d18690000c0100d8805031030100100d40081422120480900440501080044007803008160400c240400015030b11409401100d0b22075034100d004541d078442c2c0a0030182881e0f501c52044501140340407214440742414040da80a440b1141444802500c1e011b030b0758061a0b006016100030f60003010742c03020100b50107130013452052002039004290142035140c12040303050700070800341c3d4182c5001221048540b58000907241c450101340001441d44440400d8429000d0061300203520881ea420305d2919158011041c43c0500c0c0140024070076640c940408503102d01550141c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 824661537 1250 824660287 824660299
    0xb1810051c02090a0b4903080a1103010f081e03030112030c0503030708070f1805010516050307060c0f030b010e010e1206010b03060102160509040b041e030e1e 70
    0x1d24054038100203c1500030040c4180060480300c02008584001c043e01401d442010160025403411100c0b02a0308520120358000c14800038121080b0351507501170520080c2c2008000b500081e0050816400030000a60440b40d4a403203680d40c001c4001d48000c280100700c10380c01101c2c90083c404400310708a0713024002d070202440c1583e0921001020342e10300b883d425010003000014a40220b0420b0000314055141c9545400c80c0c1e103000d54000c1c20170903105000c40304000c181d40020249120031020314050310801d02c0c0003a6540140c00541c03214046070a80130700903020000c1c480f010010076500c034503201111600d5024030391110f41030a07011941407006480c0424203003403650700c407903100d54000d007c8411700828005540180713541d0540307801e800742c0103120b4100d030000034000650f030100300e50001031400192100017681403c0200c1d28031400374000801c0b402c0414040740420030710840c90401e05143e0b683d540307805030090600614528800c0701243c000d640107040180c094032094414207000a0140030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 824662787 1250 824661537 824661589
    0x30e0f25091e020f121006090b09090711010e03181009141c051b0102071a09130209181009090201051903180f022701060e040b181005 59
    0x284044d500c03c005882800301d00700700c0c4180d04220307610b03018083c10031103440c8240c3c6820805c028086140a030804680d42100780540e003043e0765146070040c2c2c071044d141f60260040510320000d60140821440401d040d000c08241080c10860003062083c001c1d9040798094032980490701c0036245207200c1c2c080c05d1000720303054110541508100e0392a542030a1000401004144c40f0745800d4100f1601d481c40740741d198203e0320801055a81081408003424002200c40c502814090034180075101c0e40e0302d518050300c00508c0c0d1807200003595050703450310b000c040c080c00c4c012500b40098003903201d8219118409400c8040011511451a02ca1000303450760603101c0524201400246c0411411262180c0c5c0c200b44d102ea82c2000d044201e4400c035041d0900c50b901014640400d481080210040324042a09844a02c500420702500328074003107044654508005a601c500240400e018040741d901e03541d00088001c0748043c0403051410098480d00044c8441030420303071520104180c204078004c21010450f90040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 824664037 1250 824662787 824662841
    0x4060b0f180403140409020d0b06160f020609030f101107150504020d1e031d0a050d08121003120c020a060e04021204030203031905040c06030e0f2509 66
    0x81c006821078000e0030414110301c0c0380301c1521407544c400e800c04020749030042651003918015010f1034100d484100c07406428810507244003603007800300c454041c04010501d204081507454090495000240c098240c82c039404800c4402036540490201c800c907564649244840f42d0081c65007620285503024085502c0c440c0c183c04e00b00064840030308141da010300c508403564001030300706800880300c12840d098400148440c0c180a007032500217600840910645036402c000664070407105000b0341e041210a0325501c0380c03500740300845001c0c0800f280041039500c07003404110b00200011008aa203e59070071010011100011503881e240b101d8002e400091500083c440e0780d0141100303d8050700007400043c1001c5160342040c000400c15507040e400350300004180804410100c40c03c078403c01d9a01c03014002c0382001d641d01d5030002102d1045004043c5d86504c500d5800f0b0301070103d00005144602140d000440380f40a003902c0d035100f192155070110403031000280301601406005000030680c2104981c40c0c050034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 824665287 1250 824664037 824664079
    0x1306080c070f0303020d2a031a0a05040c0203220333231905010512060a0b12060f090607020d1b060603050706030218010e1e0f10050304060b0f 63
    0x140b10004280c44810710f240440042e0320100b94587c0e00f00d0403002c0c3d41030030300028003140c554155042d09848000b02d40b03401c503200d140e01d0b0f404a940a4500140d510b0b0400800c80c151300481d40016091801202a0412030801511880c144c0c2d0140314502040e4021212117520b102c102c0002000200203030b0809005183d0681c008201101a5190003041446041e0b641d00c0c01007045646000f20f010440710078909580c244503003400b401080e2a052080030020f42e0066070bc003001001d4000d040d85891054607580c4840c1013003440200c04400b210580e05090781d030000048003c85561030303607109d124001031219100180b411655a4651110841550440a03800c0580c002140030f643c21a128240023001507410440c030300050002d41c0e00182c131410b80c0c45a00d1044240d00001504120305280301d1030300e0781c2d84d042d084411192010b501403e4081c40c040441c0d00c180500d078070b0030b5008542452071404240c1000003544214441c5904006581ca600200300c80d5090681c003098005136082c1d180e8001400740c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 824666537 1250 824665287 824665297
    0x121208040515060f040606051e0a2c120d02060a02040f21170309070e0c0904021c05070c03110a081603050909040f0605070201052e05061306080c070f030302 69
    0x4e46180e00c4110404041744c16a0780d1036004000082c00050404440c2150b41402d0f41041003601d825461f22040b190001c2900003288000750040380485201c18484820051807502c04002900000e81442100e4103544c949104204035000b42c0200d40005d40701e10707100d02c00c68080e10285c034136410903c0d04001d10a0f08104074004a04002d00b82800840041150300708020203a02400020b11780e00c1c5070414460b800c10501c1d40c4040d140745c0030103003400075560600040c0c030603036a000d0b100140c9624403c4075010750907240691050f80d2501c0d001c10b01c150f10303901c000c9440d00d1a01945a42c0c0300040000016940e52881032000b810803c0b003405602c034004511030030003400c540a840c0c0a802e020b841d00c00244125425034088400c10f2902c0d40c10810400540542903210050740000c204520b008001302c51103103948070804492410340301c1400381582c01248414083c0001405580d01c0e40502034500d42840c00c1405044003186201c400a081303441c20f54110703405981e10401a441848456401394065004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 824667787 1250 824666537 824666539
    0x100b0d0209030f0f0c03070b030702071413050405070614030103080301140d1e0606091b0516150e0c06071502072102150601020102070c14040204030c12120804051506 73
    0x2940308a01ca0f110030800907810032070500000341400f138401c401010701c0e000b4a03070301c22502c01e5018010006000c1d0041811000c407011061003220500e14900049e50319505049001d07500c2d45060280801e01c10b0000f14001611050b4540302e08480c04103c05c044540030902c801042805e00304010700c1010000410003c4450003d040500d20074500d42d5011080100b030440324281460141030305081c0940c07402180c2c000c0402c03020400201c0b801032581c0340c0c10300c0304c48411810f0140c0010b04440b000180000c1801c402d400c40d62160380007030802a0030014101c2d04005103258410218461618940f41d07044407010743d40105014068400700d81c00c18003940181c0b0065840104030082d4402840200c60088194011a80074040201c9a84400500040050400c0c0d0441e80b05019400000f94800c0d403100c10750301c042100c00c02c0081504001400303486a908010300c4803240c1c010004044042031810014203205050480040082c40b1040b242003608480191040c2c1c0450b204072070030105c11100340e812500c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 824669037 1250 824667787 824667793
    0xa1e0e060d021b1f0c090e041b09020a0305010f0f06080f040203011404084906120818010203090a0909030207080303130303110909040813230306100b0d020903 70
    0x225811840c1c2c1050150342e81d042100e8003440c01e0074030301981392080240442050515601542c18404581440040141300402c0c070b5a2030340c46e030041070500a00100003080c400314155036032001c840000300070342028401c641a4040391000800d08400c0b07034011714180e030300e5550303001c04558481418040342000a481646c140d581e614443d003050145c4600c062048d4003655007141e41c0c1c00c1c114984c2191074040341541070010740c00e48000c61410320a045584d48051900001481402c546d07540700c0c002d28265001800c40e6540d0302440c000c1001c800301800b015101c0d107032079103134a20a02005a03140e1288d81c1d14150702843d074603c14801d500c003943c48126000d00910444414644443d00ca0703180d41c1c07054440c04420110000350404041d814010350a80320100030819040c1052400860004840904001e15603c00450303449280400701c68460001c1500d808100e0748984007040049042c400d5644450080c0205000203030a1aa0501204202c600941469181c9082002890001d4200100315503242c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 824670287 1250 824669037 824669077
    0xb09090a021c0b011206050604050f011e02150f06010c0303110928082a03190305030f0a020a0e151308070518190c0e04020a1e0e060d02 60
    0x1a02031034400c84442c00c0210004840310030b5000500314901c0d1760200800701d4103010341400282c41c0c1000382d0303084940c107480e00c0c0c03180e00c0341c200180c6141e070604a114038082845a1704d400c91586c001200d1303101c0020241f07400c83c152139450100002c100c00315400c0b404030380c40008031030000c0d10aa110b0f0014652811309581003802210010707481034088185120405941c08070901c81c2d103044407000008001150040458a03c00304103a0f4141100514a001c1404140e4240c7c0154a05000c0e0030500096082c00b030800612500d00a13007203400c2510b5000d1081d90301c00000790301341035a20856607408400c0c0c070f03030400200d140c02c1085603913500901000c4038602c05020b10500c02c41026200d0f0b0103800500b018010050400081c4407080282c88030300700322000c4600c14024020000f12511045459404000c181001606401d86442c000301c0304c920307005840051061380e890b43c441030b4840ca00144426004801c03101c040e00311060324259040e5580610f0800120560b05680e50050019052024178400d9031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 824671537 1250 824670287 824670307
    0x606010810031e020406120309090902120a06020a020d090e060d0503090d06091104060506030109051015030b0108090f07170a0609140d0302040f050103090609020406120209060303040b09090a02 85
    0x100010400c0700d0903c034040910114039140c01428094000e290101e41c06540603100208140c80f9441011125642e41b41500107540301d200151103c40700c210201c5400000c87e1601000a50110128000500980c0d900304140c610500c103280c11510032801116241c2c551804001141280107800c03900761104001141c030586800c3c4007410030074041c08001414030000d04107d1034003100d00185074072661800e402441160340c1c10701540e05484036403400044942e5403600e00300c458900ca40224800110082c150500140d064000c0352501c01d083c0d0740d4074140d031961200035039546a407421200c2c15400c5000148170803644d0080719151102c8220880e941172003140c485108458208909449140545040e81c0b81448100700780c014194003480c04620700b0b0702d880600c20112529000c4c40d810103447d50108c0d81402616080f8400c00f070340040080052540d0707440702070404400248120f000b07081c18070000b8824500441a10103c6e03020070a268030741244041000101480106407440e0707a503081c4010541 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 824672787 1250 824671537 824671553
    0x1050403182c07030905120a120501050904032006010b0301180509060c0a020a080d02040618030c0e0403051219060503010e0316020d060204030c0603110a020706050d02041e26060601081003 83
    0xc0003900c004042d5523003505607401081e0390120800034031480e00300001040303143c980d80645035026403d0b00c1c0c480c011513800251007802c02c400714040c50f018801d410000c83d9078125480158100e030340021013114040203045091080d00c00c201d90b4610721360040000600b10003021801000f98a440344140e6210348a01c3d91002055003003015903a00195005c20b041c8086074020140d03824020344d0160503a00c0d42c0c51a42c4207803000c00e10340646803e070051940445c0405014000b81c600b00004400082c28ae440d01c0c18a40c440c04680d0242950124100040041c00d0f0806202e41d08072400d04034065864114040420380041c81c41c2e11040303811001030119200401e42610141c000f440c4183c060710b000c54034000d4020103440350780300900180c040422502c0695600003403040300f11685424040c3d00c1d403a161036010000e010343e0b4030400340016625181c915100c009040207040d50940c8001c1e0307041f0041c54521241034506041110032941c0240d0219130340c0d602901030507501c10884101c001125480e6a540c040c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 824674037 1250 824672787 824672803
    0xf040b09010b030a200a050d2c07230607051905060103060507050c1e1e0c030d030510060503151f080702060712091401050403182c07030905 62
    0x451203000c0244413150081d4010042c0d044202000407412982e402d60101192044400420520000182c1c07210b500c0103d4112030200c504041d4580d58086213800561210b40701e0540743e4106005414010580074020540811007401c00f04c11040c01d07078010740620115601c0b46100f9a0326101c1e05030281402d000c13155885000a11072000f4010f2549145048002d40b0bc008d40018103105041c001004d02081c001440320949280388031415454044003001403c111616003582c56540050409580e20b020020b41101e100ca0294101d600e44148541c048046850640d0321389d4803040c0c04841040407520600103543c000180c0c00d42040200082400a03010701c0840c0d090814a84d00001403010194011489a0380403d850000c1e00007071910320070080207030030460410007500e0f6407010480180032014280002120804000301718078202801c02404a04900044011002c6c90b0140803501d00902e14005031500100e1805004d0100c000841d080c0100300108607404150b0707a1501000420b0040210714 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 824675287 1250 824674037 824674049
    0x30506180c0609130f0902090c0c0f071a0a0e0402160201020c0f030d031802030109110307080c090f180d08010614040f03080c0307050609030a0f0804050a020f040b0901 74
    0x40c9403080c08426107410549214030301c0d44102800d00403100c40343c4403203050031001e102c0740b0000510038070305001d400010300181034040e400c90101d00030020185140d40003007050100820407203405801b00e402042e6109001c0c0112100c96400080004c905441d00c0082c26000c7e0060418030740c0f110840300400d089030070170401c0c150841918605c2d103065503010b0088404484e41990f08420004580b800f0a0340c803020803101104042d170317911a141501c200303003ca172041560300500a00c400900341c100b031074250701d0380a500307442800303403000c00330345980c00040c0c903055200080c000126940d101035080100e288010800d500101c07001c80c1000e000e000034420103603440c5554031540499414000014040c0a0b1100e541e10000c10421007413000f441861660000c032035108102ca1f0b5601c000b000100d04601807c180240b580c130a00050004402010000d0210070300070355100d000401c00c3d4803085407102010707500585180c02824034440075041a4030b4903805040e0141010650b0344842012a60f4444242d001c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 824676537 1250 824675287 824675311
    0xf0d230a0201030e06062809140105040606020d1d0105040803121005060f0d2013030b1006051909080a0303090c090509060c09011707020c09070201050709060c020a030506 75
    0x1c541e003500c0740b42496500000104000c2c64000c003c42e081c840c202080c00880d10440d41a202c1c2c590384000f10364050403941105000104507061041180e00f02800380780c1c0715038201480810003503c00100d0484103081c0303941c0c10312410188241030580341c12010300c15040080822000c201c080c0100010806058010601810f07481d1200301c030000700c0925000309214020810040a12078440e40036194608041080081c081400043d02c001003190030041c0b401d005008500c444141100003131943c00c481c004c1d0030a40c4a07580c0c6004445280310b10340039000106000344103003886444040002c40c00d50380300c0d00342085156220f4018900d00710283c03000700c00194451075220200424900740400070144a1020701c07060412206c034544a000040489940a80100d41c01e54560310410a000300b140f059501c0462909084c60020b44416205003200d000710041c601040c2e41c544148a294402c1040703644078040282010000c65000c07003e060240e0b40003190740000b01c0440c10034850740340038818805034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 824677787 1250 824676537 824676553
    0xa0e0403050a03110412021c02091003050601050105090a03031b080c1f09020114030a09080a091d010f060e03030706020307090503070617042409150b09060f0d23 71
    0x4003e0035101c0207221843c203c070341840101700d4072072807003961100c2917811103580600811051051180c800d01d0000070794001c1c104000d00080c10803900d04001604d016030240c0300560f0302c900064030544a4101680d400c1001c109080000c24482c0c080310701c994101c12003000542020b51514602604010389101540e001000c00c4210488507084600c02d03505a03450a004094094001038200d84818000d40504000000000c588443da5885201015400301e19107407681007401006111101e5802a80321840c0000f800c80c1004040790140360407922100032b005401f03814104101c0c2c1640484c1c2240c0d0301840300b4040c2c0d200280789800550301c604000d60714078a0143c1342000309464400264090414003500d04240030908bc055241140d1040e04031300c41203061202c1d5016480141d000a10502102c0c2c030345914102000321a60340c411302d8641082c0c0510070030584504000d5a00d600740d80040d404400c0f49140107480c14038440e01282a80507424421114001e032041d01940d00103040e1140303c0f83c0200c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 824679037 1250 824677787 824677807
    0x20d0201020720060738060d0615320108330303181504060504151110051f0f03120201020702030f030a180506090130050406050a09030c0b04020a0e040305 68
    0xa1b016555800c00603400c08904000020548050b540c040152505440352121800c810100d07003e00300034039501074584200c5808140141c00701c88242c1e2520490070000751108655880748001c5070107150100540700c1c410000c04c48040003d12070411401c00d0403500c2644402513901480907001466103003000c2400d00c107204003084960600005402c240a10034801405403a512000b6901a94000050040c640c9a248005d0300c00c070090305040c00403403203000e01241c80c404091701304501901c0d602440f19140102e1040b10700030841240980020000440030400c08204240c50020020441740001441c090490b00801d040c54440e11a00c042c0b43d00016120140e1030707002c2c0d802c0c103040080e10a078042d0f6905220000d205417094043c03c504004201d4400240381d0450010f0b10008448554000031f00340c41c0025201c054001250151002840c00c4009414030b06107016a8440e41da1607520036016804940d1044d00310500a801660024510000482c1000c40303441d0b11030160f80241c0358552604071039a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 824680287 1250 824679037 824679113
    0x12070b0f0c01050717040b0c0d020708091201020903120313060c02070e24010e0a08031617030f1306060f0e0414070b0a1409061306020d02010207200607 67
    0x1504020411171010130401009060704103094105600403e00303281504c45601008490140d0242031080e140300003122410041da40300205144602980d6002e201102c00307664074200e01540400e10740641014240c03d008a00040041d9400710b400c01c00ca904201c401d840d4503044516a00103407015a10100090044a001c074051540c40384070031410f8450b0350000d20443e0300000110034100e0600c0342c110482c0000e81e49440b071100241605400302c0e501c1712500780e9004c1c12000d0706203054034200c000301110405041c8085c1100d21400d03a06031407400c2601c03021301c0d90343c4401c0f1107203040da40561340d480042200d11148c038601c00201441e0b40320240d9070409013800d80091a1500d00080c045c1d101d00010001c1303a108000342c85000e4542c2c20716041c5506084525400d611992000f150720090006103400f50803c9840c03130000380c803140c0c1c0c00c0f14441298020140d080b480740035000f0703000d00c1c4040a001e4080c4003c410000310380501900d174a042c89190350364540000602012411251034003401102098000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 824681537 1250 824680287 824680291
    0x10207150902190f03060231180501030b18190c0303082217040906030b041214030a230a0501050f0d020d020f030f03031008191112070b0f0c0105 64
    0xf411203090b01d14a42040c2101c0c1c5101403000805403900070400e000d0850f440f03080c0f4940a52200242180c030b100c01100d508800311107002d40311844c1c008203840d215141c1d680c400c0a068903032020320108651550307161100185144400000c0c544560f075100c6603086100d04407091003900c0b525403240d40e0350440c0380c09402540e00800c0b403001103000018881400f130340f581c010140c2e00d4028400c01404400516590407520660b04418030181c2005400400c0100494400348118090301d1031400d000b401b00d0080b6101c0341c031840300200c0100244086800410640e02c14080002e008a86154410056208a8151600704d0766400d10644c1d4030f00400240c01c01182c50312410400b1502011842856400200b40d00321040000c0c0c0120401c1c00e1007845510100044502441c41400312512403410b42e59094680c4030030b001b4035080740107040c032209003511228884040f20741c2c480d010403400700424090000500c074103050704516210b0f40c040001c0c0e00d0780650040c60200651000182d032881c0410702036080d5500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 824682787 1250 824681537 824681569
    0x32f1c020c22050415111b0303070f0e011701060210060806060a0e1005180a06090504020d020423070e0108061813061b03050a180305030c0903010207150902 69
    0x2201d1003200292000702c0030901030040d195000900ca454a04100312013240516414005500c0e115902455441400180414040291909510700c04414289440340015580c10011502142101640c680514881c104a040c10b2512041d00c469081c0400c04811080c1d01c081d025803c000e040c82080d405034041c07503025118000050102f400c0103c04120305003200d20601d10030400d8000818240360007411108020b10006160340e072000141780304e46d1106034040c1d402c21600c40ca4018006002d210340d0050b58452a001014441250401e400740b1000e80701e4890300b07901401069800030350145a48410600800c110b60b00c856090501d00e00140c401503000c4d02c140d114980300c2d0310301d10468010400307480d03004000c0c0001e02c10303403003940c90a04060810700c8050000c0c200c542c80d40e400701a0f456440345c0d00c1502080814810b036108041c0c007131041c4142c1e02026002400c2040010300d41003d60004090300c40700a000141340c420292112285a50024a02e04080d515442c2000c19860042181036403241 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 824684037 1250 824682787 824682799
    0x604030f0315060f110d1b11151c06030206030a0c050c010903090f33050c030a1205011403060f130c0b03250f031e180606080109032f1c020c 62
    0xc80160038007001f440c01003009402501ca490030004024050000844080e010411030800b600010302560041c80c64000640c001e480001009583c0703006010440740c01418652031601d812040c0c03c058180c00301907509001c030070040341d09007043c01d01c100d04d03419000c0d035030703030081903041108442182c501d6502412140701c558005140302c0d03200442a480c3d84d44904000c5801004080040d81c25001c0c81c50030341c0c00d41c0408034581c03031807a40041c0080181041404100040d80c0c0b61011201d003207540d0080281c06503c44000580340501c2c101280f84c100c02c0d0b0141c0500781c41400d580307415400595400200c1e4000c8044107000410841900d04c49426413070412048105001d00d0000744541c00c0240c40f1402c160700c940c0300b030b00c9500e1000c0200c0540d2800361070034400516003070701000c0344024503003048600034589400051220b8041c400c200c0c2c2c003545a42e0303ca0f280c00c82c8208081120784589035203450041168440c54500b1800c220b030001c0c00e2542c5040f0030801000c2c0300080d04120201d4140b074040e41c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 824685287 1250 824684037 824684053
    0x28060501090e04050a0c06090602330c04050a12060f0501150503190507020102090a0f062003160b0907050a060c1e080c25080604030f0315060f11 64
    0x380e0031001d04401e84030340800800341a0f0742c0f414803c2c50081c0364280a03201c49081000443c6055003e85060185e41007502100c1c00003070000b0128400002c1030b8516206050340710188000c11440900c85a088200c48641d503082603200c8001a000700007a40c001c4091702c9010b40c184040045d83d009c0c07140c0c51406078004100d82c0d8500081c80115040e8030701e5850400500100094900c00c50b07035200362421003028010800c9190694007c0e0003503211022840c481c107070302c020004d82c1180c07908400003610340302c4da0b80000c41715030031a0840e0241d840340c420f495540418096581c1c00c6410f40c851042850041c5000d110a05001114038100046604034078004c4800303040902100d90801000c3c060356070300405a400444103201751b8601030705c0102c2c00800d0301c800003c01c0068113030700050340c902000b1080303071100540200d0000b60040341d4aa00c9081525001040000d01081c081e500d00d040380541c2c0c0c103020035003900921310711f40d1402040e001000402c181c50b01001407681d1046081c15282c12150080200c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 824686537 1250 824685287 824685289
    0x30301031a040807170304060e01051510030b0603151305090a150b031015061e0318081c11030405070519080f0601080f0712150b09280605 61
    0x4001c00402003061420001c2010440d11208503042c040e04582141110108028055050b80c400e66080d10344504148201c0003006043c41018011b000d05050303201c0d001d404105200d505e40319662a81d051503900c40c00358407251144802188902081000c1c1d401c02c40e000410842010280c0f4210b0001a02d40410480c2500d000150220101c0d040030a84081c8860520790740080c00c003505200c2c1d09809102c0d14480500650707041802d4140700d560311080400d440320400ca959a541c003c038a6148140f100301580c0c2c2900950003150074001e4a03154580c03144079038a41e011641c0c0448803096420011201c50240a0300d10b10626508250034917665246043c02e07121150b84215030b00078148202880f081f600f16000c0150b40c03290080038a00243c602d0716010400d035903210b1a00344144142406249a001e58540000c0f42507815a800c0c5090120711141b04d8460903644400070740c0001500da940c202100342ca0b51503903500c81c81040700c5030b8184254100e0001c0c1075010840400c07101120740c00e14105002d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 824687787 1250 824686537 824686553
    0x20301050a0e04080d0b04021605010b0a080c030a12030e0d0e0306011203170c0c01140a0606050703020706080c04051203030405102c25150203070309050d0203100204091d03030103 79
    0x345a44920104d406c86d40e82c00050000d08c2511040300c03132440190060010810190800f2501040c211080c030341940e07446518645610220300c10703c0d0305400c030300d00d003000007003004002590074480791800094220114400364a00151100c0c2e0401155038040d0399100307071030108290307405841c133000480300d146084d80c0c0240101007688101085c0c181031000268802c5041c4056654a00740d8000901c40d0450000000200d803800b9140307052060b040480102c1c1013400350044460959042c0d0052000a1800c1001c41d10b0319000760242100e5281080005100d41da00b10365041802d0500c0040d40d9a82801c0c500a031070000c03590000e020660070b20080720b0301e0030340d17991803507a5a0344802221440f0b24030001401c0d083c0462a0f600c0aa41a141240d80c1c0e02200606100f030f0031390b076000754800060404007000382d03500d004503803005001443c0d807142030103e81840d0030b042c03a405201a085844050280c4103030424bd800582000f05107550341c40400c6c1c0100d800303818403181100c9044c0075501e194115111151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 824689037 1250 824687787 824687797
    0x52215050c120c0702010c05010f09210519110d0503090c010804110103150306050c030105031b0307030f0f0f0302030a030b06090a031712040303050f091c11070810020301050a0e0408 80
    0x6070720f190100710319040da400b441703010b9641c640c000c1c02044402805103400f00100301c82c01054801616503940104000c2120b804801a9102c0d40c5405041001070751801e8003071208240c001c01000107801d58603500760401c00034042c0c281650b85449840b803a02c0c2c07580034500648240300303178108003443c418040070440c0c0d8401c01200740c4007071030040784050003a04c81d01c84191103136000500482c0b50604010b0114181c00255040e142c003281610307021a4440300a01900c0d82580d000740c0e040d0403032141000040d00e07060981c01c405119403031820301010300e5151a9000031a51400b900941c10000303072001d22580c58400c22640c00002c5941c1401d224010010500401d114003000b80034030740c82c000d0042180742000564561110012101d000d52800b071a0050203004192400300e041c030300d1403001c00c40010b0007003294190090380502a101e61000604200d0b1580403c0344500350301d01500001280b050406d100f80440c0c121039000c0540c1d00d52400e02402440f414507405618214111001e1100050691088030303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 824690287 1250 824689037 824689051
    0x20a020a090f0b331201051009091a03010b1804121b0f06050601080f24030f011512350d0504060b040204050112052215050c12 56
    0x4400d03042c122682c006000d01502d29900c1540400d50a10549002a0700030301c0421202d8500d1510b038410800c400c203801170854080040d156030006101e641007a081111079401a0300c1c08a204668410f80c0e0fa00311030350b5124107044e448507030038220400d080900858540c0345e426034180c0811624200d41103084013024000401c40344a00c102000180d104440c0c01034031085d00e0b4100d00c2901c540d898410048800c140c1c0031201c00c0d05010019010b5070082400603c503c001d00e07001a5181d0700da0740d8180e10b0580d145205415500000002e035020380b020050000ca40700d104000040980700c0300c040100c103050380e51061039845800461f680004e0012006030300000c804150460302a80401da0b120742c280a030701c80704a000032000c10307031260181880e01305c240500c0c000c0c4002c00c1803480c000180826440f0b280140e5000c500c3c02c551107109090300d503101c5503104011103c5030145800302510380e8001c22a044050b00e95500100420180b9800c40c0300d80c9410007450102d0a00d0718000701c40b41c145590b0018008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 824691537 1250 824690287 824690291
    0x90f05210f09150f07120504030c1502120309010204170c030c120703051209121b060906090303130501141e070503071704060315081b0637020a020a09 66
    0x4a48140c5440b400403004040110f445074407000304190442c0c007070b0800380c4165482400da4511008982c0108112000d50f0b03042010300102034280984541e00a4545a55400f180b180764101c51000b10038a000c0c50003004804009a0f803585030015103482e20f44a40c1c0b1b8001c1540144102c203619960000c2c1c5803031a028142c41e40340b4124000e030005030900d02d240d400a819809451000c103c5080b10000500908000b158822031150010508580c3d0340c030740e507210101400920348240198900480905494980100b04518228155001ca030a64000d800d80c05044109004d0912480d03802220720600789a0030030002d0706100006000341a05480101d010349030100014044040c4441401140e11440d008900d1000080d01640340b0040c80d0300c0780c401c1e14002807503c3d40021003900220800c4048a15220080c18420044048030328804401c101c0c8641c4104104042000c0314143c0007000400310740c841b41c0750590304142100300920300c03160a5140864102003d1040166280140c4c4000d80e0300714200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 824692787 1250 824691537 824691547
    0x15051207050d240213030b01121a1803070503040602280b0402040e010c020c0102060a02040f3003121404050303040b061c0f20060304061509090f05210f 67
    0x2412070750000c06000c3c0c8003194000141d5100d40368044128004581c49002070590aa0703903078406c4d80e5a10114100140505081c180c481c442100c425042600a41801c207000140814110007500e15404140c04980d16000460308220064050202c0b104012840031419038000315a10054003140001c00000e20444080307000c9000d40d01c5a46c805821001d0740c400801189401c040069610680030312800c0c018031469000440e5403401e8003e8408884040d40e0034a142407c1884140115074020111464921950b0260000342401d0324440d070b1680c0a91103945034058000d07010f4007075643c1224840201d044600500000070000400c8961181e0011414441030b2200b20005246044000d00d0040b201d12030001070060045140c0302807901803003444008001d0301d242c820011035500000c1030030b501c241c09100007008100141c01009048c03410881e802e2116403503120b050101c50f40e100003542e0041c40c00b070102080000401c104594850000d03040428000b061f444590306105510315605c4200005c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 824694037 1250 824692787 824692823
    0x16030905010204090f050426090d0f02040615030501060504120b100509150405060a050a03020613080628052701060308160506150105030f04031215051207050d 70
    0x2040d50040c0c80801340034801c034a01801d035080070b0034080e01c2c00d603128038120b01d02412a40d00a400e0250008081100d142440301c1c000c01c2040d900c080318800d9424400d99404e181c01039541e44105009032141c00c0c036a00359404040002807c80348141c100c40c0900c1400c000a10200c20b4007045520310540c0101304609554500c600018060300c0d80d8840e035082003560041c807803080420048608603500980d03013000503030b65542c100425030f4403c0c0705e1076400c9140028207102504180c0300400440c040d050841825a656080c498074004040790000c459031039407a911440c115074014042c14003159908180306500f492580001401005035042027040c80303010814490707100a400072001581c211704165154584404804560078040f0400c861034000c03030000070b6100d00900f0350304503201810795905085980395001c600c009607001d030082e0b061103000d40c0c4d452074074038641c02491003498024108101c510700c0d140a015981c5010b4150720fa07540c0280600307008680b20700d190b011300142c01608840c59404158 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 824695287 1250 824694037 824694041
    0x90d050303040b2a0901050c15060f0a4515091a01050d0f0603050627030405060304230c0a08070806060d060e07270c081924030c050105031603090501 66
    0x100044d074260027060710a8111140180c640b92007544180c070b401c4160b001c124104038000d2030714082c155018031800600400348032582d604607100101c14040d1a44c9014030043c0c114800036580e04000c185443d80c1020a407001001e16800c000c211241c41881000a10060000103a0442100604200e0042030b00c002c1d68406810200c603461500004001c980d44a0a10700e4444000300c07220028850520b0440300501140014070282c06480b2000e1030900b820032080200b15400070708103039a030200607044510394100005c01140c0000310007008004022000c010300c0840b5040380e00100c0e26800c4003c041003240808140c42c0d41c84441110403410182041c80c00c8001040b100b42000002c0c461094081040802c0030980c0020703104260400421030440104078050350b1701c4044035800984210f000c22071080c91221170481c038100c23070000440c0003e0b000c294082001e4040300190081c022108081080c01081c8035001d01400080c40c107286140703041d80c200e1190b01c0e4140724200415590300002010700000f9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 824696537 1250 824695287 824695297
    0x14040203152d01080f07050102150c090a1d160917030f0a0f0207090603080a05031005031f1407090312050c010501171b1302070206090d050303040b2a090105 69
    0x2c07070340035070b81005201c82c1080902541031244510740d01c0c0054510b0000d4007108407201640240b045501604002c0340c600c0c4042d00c0c40d4010842801a80b00a070740c0d01c2501c030090b0116902c0c25800810000e401c0c0860790000e0648108040702400c0340120b25440404401510b12070401d45a0102201000c0c40c034600c12400040d2180c20b02080c2219916448401d412081e2255800c84034501d8481403000d0468002e403000030001407041020714401c034040c901031a40521501400680140c1c0e0704003081c00d024496003200c002c0745c00a41c03064040403240c800c1e08118100301000b050907180090700540952960f0001070030988911039030540c00c61040040710002148807000303124650f510382003546101c0140d81880e078503005d00d0244450f2016030b0100d1720800100100309900d100c03008211000298800001683c0241c030411041101f610741c05003014030783d032040f4000c43e9030749054144880d4040019088061700165081075210714986000645149140c82e0a40da5880014100590300f038815 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 824697787 1250 824696537 824696581
    0x1020c010e090a090515100807090c080f0a09061505041410140d12021c02010b0a1a040e0408120105061206210604030f03150f1205011404060507031404020315 70
    0x141007c0115609100e81c0c080b04544408085840540d101d044071400d4601450580b03000030240c0d000102450446540c59801a10500001403001c02944030202a100405180d200c20380ca401420005400c01e4420285100303045900401242840881c00c8041c008912881c00640184041c000d2300e6910a04070349030450b804a43c4500b41d10742004080d460380803c0840580415140c129404014010f000d101c11290004000300800b0341442d0310601060320515200c030b0310300018400032039420700070300402d80582c2c0941440b54403000803032520459200141c00050040c1c2e41840034004015043d888a908254201c1c5c0b803100c512107000c080350300303c145007050014a03c523402c1408181030b04141502000605070f03406001a400480d4200154103c61080d9030011020740c9003000010b241a40040895204100203d081e04460a071100b0b9600107036015680c665460050010300e0360140306100d101c0341403000141d80b40c40c080c1c00080e16143c545450007060782d06240020b91020000d54000702e8401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 824699037 1250 824697787 824697823
    0x405060a170d02060a1a100311041e210b0c070602031801050f1003060509010e030304030207061d0f060304171b121e1c0f05040201020c010e090a0905 66
    0x41c0c40001103a480040381040c03009401a1404100c810445000e100c54054040348106040d401103001e011fa9203104c2111035080550b6000051805030441c00240020030000200c044400002d1100403554866076010084046000d01d41d0f010790b0000c4e00c40b0000d4a90080790801c02551b41da046142c0902c189940113001074400000c2022241986054000d08401c0030001c100503601c5c16807100500c20142c27004001d5038034001c3d0400c00038595404c019032059280001080211442d4075241c40d503002500c086000d6004640240b02d85940b0045030505101c0c9803103c0d000b03440070400404e01c900e0115982078090400040010306124091680300d44400d503084042d90341d110105122210b02d982041507030b400d401154909034403203111006440a001c01f02e5603c10141c40303101d100c5842640a070131502050300d024241c00d40c0c0c05020740300f40340d60070400e80303008500c0c2d01d02440022f00301000040403505109100160310344070384410b05495403000c045400041d0f0340d455420721a2820340000300342a0094 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 824700287 1250 824699037 824699069
    0x1c230327010207023114010b0711040911090a0b011422031b0b0304020f01050c1606231e0306010504030f0c0305011107080702150c010504050706080a060302030c0405060a 75
    0x81168103001c0c5c0406049824180c00c000140c112060b42c903040c00300c05405060400500100c0e1100c00100086031158442c0d2205829200c0420140c0e404800151034800c80c0da24040c0003418031856080d400030494100b000690781280c00a0840e03c0490001100d400b4007081040c402c000b041c030b0803281d803140004800861a40d900d8000e0454543d030700c1c21280035400e03a200040040c0001c05482c02258028000400d00740594011101601309440d190028414482408204d6020f06c0c00c15010b0462507450031311003072199200c0280b01d0203400210001c40303401c104e54045c00c0d820341c0040440324890350400f640c1e83ca460004030786030300454101034155079208952071f0070403246a000c401101e100b03400078030104071007500281550060060280441400f00035180052910070740b0090341d0f480c420711203401e00e00031a44032821140200c900f15030b6607004e10350910811780c2007860705903c020040401e01c00241980d0110f0780380c5030031a015038022520f80000c00c03240d0b518540000050f10003403c00009203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 824701537 1250 824700287 824700319
    0xc110a0b1611030f030d020c07050a0e0f060f030307020409061d031306080f040f06140708090c060309031b0c04020f07151404080a021c23032701020702 67
    0x60001e803012214507a5480c2c1e001c80e00d080c0820700d050001a100080c0d400c06030010100006075126581c06c003858000c0090102d103507502c0550620242a18051904031464107075011b48a119002d011540700b24689220004070b43d40003c115180706505441c0801e0115051030f00c1406050b8540c00307845406001c0700c0151000f40008050160455040c1d681040d0503a0381000b528680e0007542d05000d004005000500400d00e03054105061902c6120f000502031040706492081c03d20558004000071001c0042c01010301080010014041040b41c0ca07a103103050824515030742e0700c1508218884d8099503c081c81c0c038101c052081c1d21805401410070f55854040d1b0507403070441da00445044034540c50210000001206521401c6c944803144001070580d0740382c940321101701e80c202180900071481401071740b05052116400c0242c403142e0f0782d1951114102e00c2c01c8004a14030010380200c070354140c140100503d05003103074844007034200c005840048a0802030606406842080c5002c0d4204a1400c602001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 824702787 1250 824701537 824701567
    0x2e060e01230901021c02070501180b0f180a0e070e0d080301062109020d14010b0a03060501090f020906040e0c04080615010f1b081309140a0b01020a030c110a0b 70
    0x10781c800340d0030b54503113107009417501c0c500364003a034070b040c00580c0510802d11144d4000d50f50440094081c0603e0000142ea80960501d00c1d80040d001c5044000c0120380c110315800b044092044d0074000312600e403912410308100d02000c42d0020828410000042c4010300349846405060444a400060542e03996031150400307880380081041c40d0721440e200c25124506108144101c0c00801c1d4000d026540f0082d8035143c0e14054201c001d0040b1140d543d4524580c002d950b40b214400c010762207904081880d42c5080d1408003110b01c60091a21001d0040003803c00d540da03000700b264169941101000342c90740703410341d421240d030041d500640c81034454032050108080e560103148a03501000d98520039920742d041003c65a054140910341072090240c103032200000d003103501400600c41116040707040e050350307074020a0135240d80d001950840c1c1c800d1000d2203401e031709501640c0f0f03000600380000c0482689a580040c1900f06000c0050301500c40014412200c2d594000e4030801004405460750f00c848142690b225 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 824704037 1250 824702787 824702797
    0x1b0203100b030f0d05030c030709120f050f01090f02060a0e060d050a0c141207050d0c0c0c0f0302030d0e0112140709051e0105070c030c06082e060e0123 67
    0x100ca4800d00302403a0f02100002410768500c105551064195201d840d0b10900541000d410141849a048008a070350200e02c044800068003402c00d9000c04040790030070700e0801c0461012084181d04211b4510003240c0d154080d00080c2c3d6054440c00d5448015080c1219000710341ca45003a0301400004030380402c500c2c00c2e0049401407078061404c00c403041188070b003690360801c0071084480a940134070202c04ca030f0390744940c200e03880300039814258034000c11700590304221a1802c0d002004585c821108800f445141480d140145c11040ca414282900315000a0fa03941d0041da8520304204400b03800c240c40b87d1040e4084071141100c0030090201451941400ca0415030071101340002900360b410008840c6482d20240c4050040152030000724100580111404e41c003121090b1400e03042c2081c00800980001a204020034042da6018142d081000c84410b604045a08101082404000c203080c405a01c0c0050b8080342e00500b4001c02007540c100c0180e418503458440090032080c40f15048901e00c5140340109 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 824705287 1250 824704037 824704039
    0x50403110d0201050f152e020f0d390c05270703090203070b070b011806030816021f020f010b010804200d050313091116031b0203100b 59
    0x2086490040d9049088a83c121100c040001703a51300811911a5030005240c0144406010781c01001644509100350903c0465406403080c1d89111020300d8030b41c180600c4818507543d401412070018002c000414403042ca01590400c0c0c2c040d154014415410486a0a800343c90030000e41130300949400d180e030f580401482003d00642190101c0c5104061410051398070310b10b40c100c510f40303d4440b60800c900500c5420402c80c0c162080e40d0011500000044c041c3c140b0301d10581d141e44996040075610300c12243c2d581c2d26200d83c0c50a248007480040c88a1058580c02c0074102d100380540341c290300003c0d10100141340024608841698404599035003c10200184881d80b0003d0060f400c182004646820003181c025050410782c60090380541011020401d0300071008069200180054580c2810f41d4028105010000b9010104121004160050b18071003088060440e0504a401d103004080c90501c000003403c0000482e04820441003070560000c4190700079007160500001440701d030004044405a503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 824706537 1250 824705287 824705293
    0xf12040509010816030b1305010513260f30060109120c0302040b15030f04110409050d0e010302040f0e06041b05040317041502060f090309030a081b0105040311 70
    0x46003054001981c1035490b0850589140131030b1550702c0b003220394000980610800c0034944001008900b09005490264081d00e032903030030003001c03031402c1152a120342c00c8217801410401080d142142034042603844490391000c2040d6a011a84205604003113003480c925851000310864007120031115240381c3c0b040784280c840c0300519071202e1041c0e20480b0004001005550070390340074001428690001284250003500b400041e0944e000141405c1c0c00403240030802501074020001484006100d000140409850401494039a92241c0d9154041400d0035802d1100c2c8424030704143e40f003581103400900302c490229031440d0315041e6070405c4003819550b5600c16410042d205507100418241c0f855070011544402e840c00c0e20319540d428501c00042c18400e0483c50a1100103512707124018014030205080c1c1c090407607841e107a820a41444009428580c9650082c45004590b0303d0000301c15610b541c1103250f0503110180c403104285001d2200460701c000354201010305c0f00b0550802080c42102c070642003a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 824707787 1250 824706537 824706539
    0x417070f0308010f0803160503090603010305160621090c0e010f06080a0c0804020d060905010923010e1e030c2b0513090b030c03010504080a0909060f05060c0f1204050901 75
    0x94095122507078045c81d40250000c1000c07168061a0003a24a020b6216005603401c040040f000a02c094009a00554898001c0d0300035860500e2500c81000143c18a42406440c2d448003106180f0040202000c000b6207d55803206101405203000c0410000c0054040c110351a6844410b541180010b61149030049040e070030201c1c40300c00030342c041c20348400d01940c0c90080982d240d400704940340d0841d6006075070140e92290345102040c0c0030b0140c07a0741c0c24003402030240035440c111521000c0b1200024500b415901d000c2910014840104510f240e1455505501240700d06000c1001d0071886048800c1c00e40d8810540002c000f510f44d1540d0350021003400f00d04c041c2c1c0301c080340d00584040c0720f00d01403041403841c1144213100007900c0780e00449074808080c3c100c0717007500000400329086030001d441c25208060085075245c0e503d03500640360b40c06000e070103809014041c074103200320301c107840c040c09480d02c18031002c503401071080382c2000045420074030282181d510440390704082503207a200340034050042d660580 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 824709037 1250 824707787 824707799
    0x120507020f0f030f070b10080d0206060a05220c030e0f010c09050901030c0b0708070b070e0f040c0816020a1a2d070c05010b0a0608090c03010c170417070f030801 71
    0x3c10b5132454201c1400307142ca8410141c0d02d00118080052550a44200d1031750b010070020f0341040200c060002a400400c1541803080c10050340100940c0300e0740c17040000c605194065425050161048030f85018003040ca106198001e80c09843c0f103800a01c0d1074403540201c510800015004030096031341644482e10b41c40c0c0c8403401d0041820007400064846465001c0400001c9041c200030300049020f0108541400000e5665924107a015200280007e000000c42c034600d1510192014411104840401250f1a04000a0f0036014000d1000f001c45030340f1407809008074028030101804c5a03021540c0c6807404070f964240c60103040700707580020182441c5039600741501ca074807694122400d404180910295a0f81004a40c64030320b00000300d40d00c3d500c0b07034115803450301c039104038401070081c0d5203822420b85003d901c0180351030b243d41e03a007501c42d81c10b11501040b0103400c48100c6031807100181a03d00a40e5a03414021140340200a21000050303000880b48280100070008107a814480d544004190340d84d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 824710287 1250 824709037 824709043
    0x406050c07030804031b02210708070810020304020a1a0319271a0109020703030e12030609220f11010804030e010f0207051e03060c28120507020f0f 65
    0x908002d0108522502160101e401884c04d080722aa01901c055040809580443c00400c180d407103284c850300c0e1306580b000322134000388401400340490f080188242441d10f10180d82e034a100d1703444201d000354000701190664542c1d803488005400701d041c0b800701c81c141c103d2100700030741d004039580141f42803107104840c1c43d074806009003c10142d0840f19044e07680c001641d42c8072428034140301100d90900381d290f040000d5070b0701034420f4000c1150490041c1c071800e41382405000e0300e440041c051280d0b0420256041a0520798094981100043c3da1010540d95058a500c440b400850031030903080c42600302c0d480812029510090049100e0400c64112200313000043d1800c2c1d0080c3c0b00203000c9810f0021802e21544115a40d076141c5280c1c3c81100e0155075240c0226940710706104003601d0001414103100c865007001c11034960040760740d240d0145090030010005003c007101c280381c0040000c0855003000c20510441e884541d80340419020030140c10001c034060750300e00c00c111020015014800c0c40400d40b07103002c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 824711537 1250 824710287 824710297
    0xa080f0d0c02130f0b09090115060503010308160c030602070f020a0b120f090c120c1f05030714040308120f07030c021002131e06020106050f0310200d050406050c 71
    0x10303226511100c0110b0f4040060304200c292030044582d00c1070b0789110f640d1842c41c118040d58141000155042190b40411288080c0da00840306000b402c00c010000aa4070000702d414040c2c0e0028010256442d0f0714280192200a61028024074004030300e103000d100140700b280009900c215442540940c0d80c1c0c10503a60b50007288040e012800d40200007642c40c14014010340d41c041940001d4600c49002d0b9000917441109546407168203600501421600e8100300c00040007410032084070b0b282602c41400010701c14440180a0000c1010042080007403c030324500b40c40c040d40e40304a40640321040c0c013050340c6a408040302c400c030a45450300042020103000303100d10901445558043c00340048a1048600a9070000e0350000601d2032946000640910311000c800311050040c848510091a148000b403d46903c0d811507403041203c01a00f05e101d58002a0806c5c55290b020b5003c103002c40262000b080c11562102c1485036a48001228040c852040d48254407843c0706e04000c0145480d01d9410002502032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 824712787 1250 824711537 824711539
    0x1011010605040e0d031d0f070e0703051b090a030c1e05010302040503101d0706050c0106361103010b0a02010e070303200f011503060513170c0c0a080f0d0c02 69
    0x700d4a40e8691017486908440f5400e007075410400810b074101a85d0b1442d180264480c9603458000780c01c14401c1e140d400d410a42c101400345428440340c02c110b0170152201542d1b0f40340d441800c0c0c0009028400352500c5000400039034100310143d045550b40d008010044401d110304404a004aa03030204075903009100f90360075100040c000340000356000d50345070000c168071120f04290300411000c4007501d6108010450280505039520ba44a04404040c142900c20079080802030361803070902c2c2800510440000f15403038442c1d0035484041080480280c004201410140500c104000b0002c42c0c42c026450040800c220258000c015080d14500c0e110349078021400000c0009a05100182003009072815440c008004070041ea8210340e0000c5403242140d0152a801a1141d0b22800c04c00a11040b8880d807684580440c00848000d201c2d55140d4030100900154014207a5012980511008c400c11404002580290641d000d03036440300b440c1656400185002c1015208407625600104d100d050410b05040d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 824714037 1250 824712787 824712793
    0x50f0d0b0a02070204140a090b0a090201050f07060f090c06090905090703030c020102030c061e1810230f09062508060105071a160c08120c04051011010605040e 70
    0x1ca2256980c0658040c04007030340d0098448082c842165a04103d03a4001e401c0c0700400100d0105920300400c8032000104000519440c110030100940d8001d401c5401d40e02030050031340d80e980f00b00c1c5810801002e40c40d4070031541d2403904111000300b007101901002175800c95200d06030315a54410b6060203540007141d5034080ca030011041040001c0c016411286403a105006403401c0c5030740040b03000c0c540a000c6034140e002d8030424005891030701c28107901c1600054030201076110325180c0f01b48250348403039500805006641e25011511060030000481d038034030641c8569800303903091040384c800468030140da82c0c1403a809641c0104041400c03a00714950440b0084100d4020305c40c004500340c072170010040031513050000c03c10407040001e500303860030711658004c1000da600c2820304810503100800c0da40c1d51102401043c51240d8003007030782102640d10788072101080e28500d641d68204c1002901039540003d80107699140c10407a6260004640440c500841000300700095540c400c02c015101001c500c501250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 824715287 1250 824714037 824714041
    0xe0706140a09030809010908120403031206051c23010f150e04060905030d0203040f0302070902160807110d15240314011b03060306200f180a030309050f0d0b 69
    0x403060005881c917008141800100309980d403200f039050800015060091100000e802e0003055000520034401c0341411008000860400d030200f1a09030001c409201d0fa011010454410810320f400c0c040c1c08172034141050090f8203c5c0041a0f401382c103507107060180303250030b109a020050b41200540001c41e0300300301d6540c103180c0b56030315804020810000159451f00003003004c0200301d40c85000031405907201310b500501c4d0107442d080080c1001030a8000f9031a41c0e004214820b0140c00342243c03d805660440b114a81c1c641c00340c03400c81c84030303d40540050317004a040e81d690014080c1056101d26003ca200320188001e00e00c0c01c1000445006840566207050701448041c804034088064010405800d10000110242e0207001c4500011403000128002621440203004000060007448103140808241060303c0c0b45000c2605058021140c880d95091000300b0003070a14010306100700d00c031000140c1042d6146481c1e0400901420440c010315002d011610360780d91030f40c200038412030005600404903182075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 824716537 1250 824715287 824715293
    0xe1606260f09190c03050d030e06010506091c0b010e130b0c03040f051002130e1e06010c0611030114061323041a010201050105010f0c060c0903060e0706140a0903 71
    0x7900800345440f0718030b0008003144203031074140c6a0501030164205a0b80c60740c94480e00d4009010201d0040500380f0454000303100c1c00043ca6815242c00b205c0c0c4940318840b034004240c05900f9819201d5510b80c449101c6424004402c0a0506807502542c0550055231848428080c4c0350030300400a10354241d400c001080103000030090764019105070000141d51200307031103e52801c0000d40740e03030701603c0c0c0c001280c800148441100c60000d1011082400a61518140c1c2d201c01f81030500c0c0040243c4152800140e03036a2007520707011140ea900100c100404030a60300a50f2740c03500b007406142c134502081c006000a6107444070546034018400a042138000d800d01c1c0c004850510380c07900141d00401079002c1498295030314018100c01b040309844003a141087d4500080c00e444042e031003141440b10010300c5141c0990700841902c1103581102003c07a803a500c01c18101c400710700691000d00454580b051454444001050b903600302e032003e0780d03460180c490000a11707074a482008402004109007000030000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 824717787 1250 824716537 824716561
    0x1516020a0c05130e161d070e220207060507080601090303090302101b0503040e060901030807060e120705150612031b100608060f06190302040e15040b01030c2403020d0e160626 77
    0x41c0303901080f500d227140442c14442c10143e81111030119803031900e401c1004203895114440302d900010920f0003844840ca0f40e03c01600e01d15240c0400390203080302050030340c44103000d80740b03044c80f0b00d4040c0b80d180f6200d070075424101d8803908a401400050b005840c045081c3e0f160a040d0141030340d81001c882480c102240e0384040003000c1c045c120944501403010f140d40d9484074072028001c06406507000d000248080703226101c5540f0018010b0384210b90000003e00d240c46c00006a49210201500c19403007018000c3d801440e040c0e8105544044900300400404c0c0c0c088003003032680c09000c0320106403e003521108104014408404c2e00100b800d06400020005032034581c2188111420310340a40f49600840070801b85594021a0107941c243c410b0700c010410050102c05c414010070000c000d8400303110340d40c0c1182c00b00001c08101c1d482010b0300896124040f210036800050b9078606041100e94403055041d1580c0360704080d1082c1d4011800d44d200007610300040d44e00b0783e0610301d01156010002e80d114040600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 824719037 1250 824717787 824717809
    0x30b0f061308060a1a150919052e0e010203180d08030408070507061d04090311070f0f0503030f25051516020a0c05130e161d070e 57
    0x740291100c0020409810b0001c5401042011004110004a092600d802424002c600c600400d00010301d81c680910144c10364600d84da08a5489100c4a122000140900e01d190012580142c010b410342c2a000440c1420202d281e91758841858181111b039016105484000041e5015030800c010149450008514254100314000c041424911558840c950690002c0318100c81441001031164140b200400040d002001c0b10702c0c00c020b0010400542500320040440800e005985424040e42014052800e6440c200102c1084601043d0382d08050080d03480395204022004d2400840071542d410301200b2103c418114159642c608240100107035040b60204031143c092040c11284900021070078000122030210003c6608114180704170360030b0b000d80d1200c07052001c1d54040000b00d40060241c1e01c0307840468004485c81188a82c40c00c2a60010349965591075086006818010f00c60080a10412060301d10170b0741c110300300c4000c2c0e0185100381d02054803000007041c0b45007447c44a038a401a5182 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 824720287 1250 824719037 824719057
    0x70309020f040f0f091415190b040b090a05060a0b0c061f051201020c01060f03020306040f051f140a02030c030c09061b010f0e1f050a0b0d050319030b0f06 68
    0x15213882d03640400811100c0140702260744254400f00420707103040c10801c034440d1281200e141005401c0c40d0780c1c4000b414440c445a40c91054540102d03030b61656455014291141010348840351500c0c0804000700146811510140316400190000c1348100341c50f4152552440100000e180c117807200540401000881c2101c50b00d030608204002c05d041d200d11040000080580001584440d1000c1d4114203403081038101e200c03c240400410405641d0020b003258002e504680c0c5807080c050981002030600d203124852486003034080000303220382d081650000206104180c60142540c032404240c40a0b440241d5800449900030300101c0d1200015500500200d0750041c425441c1010a11410300e40c5100360303e600c0c4550359100261100310782c0303070300071400d9400d813500140c0044401a00005d210f0115038214044c020750745c0b000501c04135650b601407044618010701d02084401c2c5840c09943e03e80c0203059450500e010742c1c035500419406801142020315005060082643c21801032103120b070820340c118 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 824721537 1250 824720287 824720291
    0x106091a19080a0c0801140402060a05090427170a020d0f02150c0a11070501050f07080412140f070e06010f121b1d0906011110051e070309020f040f 65
    0x44220041004440350340c42138440c0300d1581e05d4608400d00f150044488007020000020030040141d49103021238070b160300c1c030b030820b543c0b58240702000c10002c1c0800000c0c0c02c041b500d4501c80310311800352222031120072840390148240a0719040901600b601481d900d540c00350780f00ca40d8111485000d45010058500a44119681e1468140c080c41c814130007921514a9810000f0702d40c1e12542d44480e4070b00e0f52440307071001070880c9482d1100007001845151883c1c3c107001408038055003044001012500144051840107207140c1d02c2d0b040c513210f00000004040e86a00c50302080d813510a0001c0303015000c0329a52400b40e00c5a989140041d110501d98034505420420044483c406403c5103206a040440c440b40f99440032144161002d0300c12400d45001c0c013850b80109502c0380140e03840015076548aa821319280742294003d09810745482080d40c0c00700c1100c0d0070070040000c0c41c01141c654001c5496800400d160ba5101d03402c5c10b5003140c1860704043d401640c1c81d4209041c0d0709142c1c0264090100032000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 824722787 1250 824721537 824721539
    0x906051f12090c44030f0d0b010323070c0218160801060903051011120c070c0f1511071e03062a1b080a030e0106091a19 53
    0x4007103819075078003215081000e220900088800c201c0e026602c0c5030502e5800f50540007041d40c43c4c03031440f0716513401d03030281c180c1c02e0300c440c01c58003d01c103840107180b080404588500040d50035034007610300c040225001a140980c2400c0600c02000c04951441c6808400780a0307450700542128641c4d9004070076030308131414070b03e104075407010f4001c0c540c841d0070104a01d0703840070350407540181a04c406174400800c0000340b55080c000305e403000c2410344400406603c0014040100b4120800c07030b000e407481701c2c2c0c14107040c02c2c01c00600c445441c00510b102c40c0702c1d20790812001d8a580c1d503580b9101c1a4040c503842050481c1354480107034014001030301d415143c50103e5100300d59401014440104008a80300c10031440c182c20410483d05029811940c1d4002c003080410220082c111120403001509d40400c010700081c800701c07280101c0740c2c910b07801a0400324140d9504660031b40a8050090000203440544c070b004800180d00200e0b06c40c0404182d20303490802040b15400081200d02140030354030b00707a00c003030040b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 824724037 1250 824722787 824722817
    0xe010b06073207090b03070b0a180801060e010b0a0e040608010e011a243f0721060918120903170f0c0109060b0a0906051f 54
    0x140220501c00c0e8004915180c441c41210500142402c0c010241440d241400c1d008040210307100c3c080d01c510010014900000d80002440c0648a5101d07607030b04000012041000c82d40b01d1449004403241c19001900c40780d4401c44e0500300e46403440380c1c2d540200352000502020002d9801410b410665290543d2000629400281210001d03480b02c4043d030741da03590041d9910022b001e403441145003c1c440c0e0740c3e101e62010201d14421701d09410748842c0e002c40c020308101c4401c448240e0310381c00c0030100b941c004850f441060b0055401c941c00002214012a0840ca80208a03034069a02c200d40755030b9079015013030b0380050040320f400c4143c600070388a0307803038101c041902c2030390748904014a0101400d03d0b02c000c4032800d01800310410070710400100301140d507060011403058008141202d48501c182c0d41c2d01c0742c0c40b400d014068064003c0841c0d01754200301411080c42225080901c14241c115003421115554549040c2181d00790b00c201c50f0001810041035401c282c182d02d10034801043d50801e4546405546 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 824725287 1250 824724037 824724049
    0x903120c070c0806010503010f02031302010c02061c05070e190510030b03150717070206190f0903020c031b090109090204091b14010f120905190b15030105190e010b 72
    0xf400c0064213600410042150b480c0c240594001000380e5a0218a141400d4200117046e040183d0080d06002c96030403001c1c21900c400d41201d1000501c0352920500c0803003c3d0700341001e00015100715000507104c1103110620700c1c0c041502003142e0448003100c40c60510308420f000b800c0c01040c0c010000e042d542c40b941c0450f80c0b800d000160f0500b00d149034a03a40b500c0c0000b8094240402c002c0038140d000c2091081100003500000c1d15504546503000b160804444425888054208440c0e0008501d04042c071003002c154001442c503050110031000d0b101e228000369010480700001d071001e1503001801e20b004011072203c6501c16aaa2400544080340d0244680c9440c080d52902000280030b4126201c0e003044051100409022a284240307456091407000340c1008040d2009425046002035030f882800041010030402118540c0c41c800c0e220708007030703490b0500003400a03044603c034141780740150046003180340c10b1180910504403038248203105405d0680280040855810414156599101074049aa10b030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 824726537 1250 824725287 824725289
    0x3060922140106120b0714070804120b0a05090c09090102070c080d0908160315090b010605072306070804080906030a02040501020d03090c15020712030207050306010b030903120c070c 80
    0x2030340e80c240c064015801036403c41d101c03544081c0c038040315810b01e100003d04558080790800340750b10b085001032136100491541486108030083c0035040020380061441c1c1408848000c15000b18a24801039490a15540a039403007110705451a42109016940d607284ca54603294011114000060038402159542840c008154004111540c00001d83d441c003036500c13011910140908402a00c43c0040084200f0303960051800024107486089103000c01543c42c40d804001f03140e0300700080c410a96940c810203080341d4030500302a18242c81240042d0881070080c020b4900c0d1403039010003800199141d200482d055103001d0011202648208208051543d9040246018644030030300140d5a61812001a1820840d10119800d02d0305107040580031500506031141190580031008088480f0703401c04a04010700d0341c1058845850424007034007490340c0068010183c400980449050b642c031103080c844540000c882400c5258800c10030300140b402e1310390201d03400c0503944034040e04000b03465590341505401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 824727787 1250 824726537 824726543
    0xc0901181a0406030f1407060503060409080904050103060515180103030311040e040b0609090c01090303030218131b090b030a0b010e0d050609100c0c140c0d0521030601020303060922 80
    0x503001418080c00300301116906c031203482c030b4000e140742864074001500c40d0000520a610071a0381d1982e5800b4403880104844260030010410441580c4a2810030700810007070700e0081451800f01800011410139580c00502d046100011120741da103180ea084002c0c2c40385424000f00003101f448005030700d08418650501562150790840c06600d000000d00000d40300c0148a80b410f903000c02907602d4540d8004074102d00352901490090396640c0c0d280c00c4004a045210545500104c4c0c0c00c0034090042c0460340240d4a18aa4070400f6080580c2484201c400b105140981140030702d0030030100311806001e40c0304000700081030410300014088440040c260716150281501c1c150020f030704204004006200c1d1509000d1403d404000640350b5040c01400560000740050903061000d08820311040c04200c0c0310715400000b460540b10540b140741c003c3d100d01446002511114982c01c6c2820500c03c82d0042d648540010390003541990750f0316081000862000d030050031111807400751520540000c50104803c180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 824729037 1250 824727787 824727803
    0x18150d0c14090d030f030e0708011505040c0512101208030708011512090606080616030e0601050112020d0917040806060913080c07091505030c0901181a040603 70
    0x55264018000000000300d07205401e00411122500d41d0318004000ca0061301071074010700c050400b54040c0e00811001c86500400c2c07007002800552a01d054200e10246008201105000340d6034400784400d841401054501042060140480b1000d50340b03050303540103100e0282d00d070145607100c92591010b980316500365440080002007002460700a0540742c0100310414000340c4110f201316004054000c00c40420800a40300c102120074070071103401c40400f070500301040d00e0490511089481c243c0540380000d501003810450b01880f1b114020849504944041e15000e4010403042d0000000f98849041e80e184141c2e00c0740c040000c80c03035110030003001400e281ca1040e5150f060005051400f00028843c1d445000b02000b00101e4125441000c6001e540c018549502c84d02c240e9a09401c001c4250016145189070a0259104404683d80b52003101c4080d03050b200304106407000c1c455000824018140070384045920101000c2096001c2085c20924600c0c403034020b0500300000c2c050b58559401614485 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 824730287 1250 824729037 824729051
    0x170106030209011b0c1a0c150910050c0f2206050301140301090f06050723070308060103200f0702060f0c0f030c0c0f010e13060e06030c0618150d 64
    0x350300302050204c12144404a05008081c680d910000811a40503406002142940d075415030348050003178031000d070281c2c0c054480c0021301c05051292064100c4020605200d003060006203148184070b014028180c4480039854140800c500f06c82952141c10b01d0604504003002c41e840c028180318081d0701609403981d4071540c951410030013000f2584604001446640740041130800100c502d0f150400d500c0e4040c01c080ba96907258001650b0080c043d6504821190030080440340c1611440020801c0c90301c00d4541c1240707070703c40c400110112451500c03d81108821000103c607480342110151084810700444103140c9101d5078041001034020b05506004040040b45200021006014200c40300b04005c0042d401d15800403903155940401e07040c0c59002e18005131003424141d200e6141c4c0b00d41c560026101040c18092903202000600d0540704942e0075078803d074041003951501143d0000c8036800140100d0611314140c048641640c030701e0910542c0201241b1950356070b121820094040c20f040c1d008005040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 824731537 1250 824730287 824730289
    0x1a0c01020a080402041d03041202060910080901050709050d021905060c0a02040608210306061207170601020d17131209150c02090c0d0902130b0310050421170106030209 74
    0x7a601c6410041c2e00446c441851041060000084d1012908040f8028440d2401030001c103a01d03105120509400c46270031351f5400800368218944500a4200700000c010f5a658080203d0f007410303280c00380e00d602c5107044c4008400340c0b401c1c03821f46954500c48000a01165a0340740010090390144013a4001c58100703600343d0040d4a0148a00402403115078054407164140c1c40e038682c40100f140550002d00c01c001b001181c040c3c0c071a0b1081e10224180b601e500720650070302c8600a01f604000640100c04d1030120310005519504c0800e00c28544d03135003616100480221403510040002c4024503d05000281d10b0b642e0001c91903d40c540642e409490700e84003045030407e40d202c0e10140e54080210305000c080d6902230f0060b103550f9038491740040350b00d11032a120083c4814007000340009003006035200c18a0520084005d80d80d40c01143e40360703000c408841c1005080c44d0100c094403000c0318090540b403020010105030014010314440d0502d9540b410758002ea14140d4a25511032b801e03001680020f601003400c40701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 824732787 1250 824731537 824731541
    0x50405130302120c120a090515070203061830130608010e06010e09061903061d0c0d0204050403110a08041523091801030f060b06040e011a0c01020a08040204 69
    0x2070f00385004805150450b8803409035070716000040c0544d070380d080002c3d084214520400b010005494010714405007101d01c003080036002d4005c1c0303400341e10a000300700210b482e1184d8480d0100212100c54094009141203030409000781c54402c4600c1c10600e0701c49804050700141c81c0c000d141a02204e51035400301c1d4108400203102007030581054034020a92403d100d050b81e0400d03c0f0f85810f010440356160315964600c08621f058000003108410b56054540210401c52150400c3d43c04001403450b51500c0c100c03001d82c555685c80c2c542d00d00e540042104400750098223141d000544e0080c02414240c40c1e283c42d500c1c40034a0241481004d90300c046010034144801524210801203c0391a49001c4d003804172030101c002c008800d4981e18503101540002c00c406c0a0301c0307041c6003801c07912030120003259a40e5a82010b81c254400c1100449095142c9185d030700e40c501d811070603102034074200f0721001a581c3c2407011019402d0080302014070420018412400410000d000400c180c1449541c2d208890900d4814002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 824734037 1250 824732787 824732803
    0x10e030c162c0403121b08130f06050411130203060102070e0727080a030503100b0301030f12120504060b0f0604060e06070212121e070c0302010810050405130302 71
    0x14070702604902085040c8800c214107030102da036550035400c5464925058891030018400181c00d00e0030318035801e01801c0d11041100280d610381d02d03a1100c0e41d9801a0408460701c141da4000c00c400c05000c0c41102107195a07024982c868400c5654440780c0e0940000140303414602c0c245820f503039800104211455034180704070b10042281d0381066940e070418071030103030280d204003401680c0d1459010180c0d410302c08201800303000741551020f9400c45059410010b00c160b100703c42c040042001c0690004102c07010340100c4c3d04990f001044004202d000381d42e045040701e4038502e204204032600740d071001c40701541d10605009074415100068001c44100601244c844100381051203681c080c4010003e040d00f00041d510440c00440e4116511903a6100091040c610568035514611410010a40c07001700e07000282002c8003019001c8248001400b01d035212442055001440c030141c0c411700b0401075001e080896001721007462001141c917201c03404030b003c480c2c04945015109412a484030207140d014080c0070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 824735287 1250 824734037 824734049
    0x1d0604081b0c010c0b060312040b12090d020c271806071701140d06060803280903060216050d020304060e09100e1e190605011e050c010e030c16 63
    0x400c1441d00000007a05020440c60040c1c1185c41c4074000501c695030911100700300c2500404259240c64881c0c0b04407840d80c0084020b600e01615000104461100001700c40701c601f036055000b004010044c0f42800075190031260150041168217001d030407040190102e0610940b007191509680e8070b450707801c0ca4a001c9028103600d0a00030785a44540c00c141c0e5446005064503546005602002594004500d000c00c80700400f9040c28a01000403c8100000c401021603038000030b0400010b071040c02d81000c940071614405404502c0341c110802c0000c0054001d403907046504500c0b03000105d40c903155541801d001050200c0182c100040c103100c5a41c200c0c4080880d020240c5d0420050b1820440c0703d40b0811940c02801c010800210009034000010003a040d8024622000d5220704e0910100301600640480c4000c2005801c00c0e401103000d5104142d0f0401070400728204210100b0200c505860302d911448104040795214072083e0ba540b2401c100900f008021180144400f90021039420503a0400b9000710b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 824736537 1250 824735287 824735293
    0xf06090d0806010f0804060b0604210302070b0313120306121101020601090b09040b060d020a030b0405191203050612030f0d141b0d060f0303050306210d031d0604081b 73
    0xc40003c90303000600c2641b2507481040028400300d0440000c0301e40c0107980c03020040822507010304803040b80b00c0f445660a280b04c0d030200d03603405840d102070f407c5901048801c400000b100600700808600728440d41840c001060030002140781d00c1d19101050240f10b0038040d501d9a00d0454202c4d03403540c0c10040c03d40182680c940400c0104000c000042c80b40a02900c040d0081d403002c00032520b1643c80c504640100b56009224209182c0d07240b138154038286080340c013500e042c054451444503007000d000004040591110f42c100c0274829400301600100030292503250000f69628a032000c0e810201f000340bd00354089291b568440407012075070015542c1240d410f00064500d4800e100420704007120040e000b120682407103071075400000e0755800a280603406030460700200e410010601d50044010341c010402502c1d030350104100e60b01880c080e40380000b0120010b502040700c1495992180e8429122a00100b00b00382a000b100c200351460b100040c0c1d01629000d100003141221000b01e10400781002c0e01a4010b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 824737787 1250 824736537 824736557
    0xc08030a1a010f0c26030f070f0302210403020f0601092406050913020d0501090507020c100905130e070b03070f0816030902030a0c03050d03060501140405120f06090d080601 76
    0xc4c060300800344002d0903506040c1c203040f032032021343c1c2c070540003e01c00200054807458a00d082c0c540c000d00a0340c0c035001080e5005003c4500c0d911a008640c13201600c0352140d04140004403c0101144004006500b18083e81428074040340d805d10005001f4010713181d020a018401d40d00c82d030f5030790f484400340d01c41c21003925400b00111500407040c0c45042d141100c044080440f604d5080c0081d200d00b01944001e03620705400400c44881d00e034411402036609600f100d02d030f80c0d00c0318203001c016120881d00e4404215010401c01051502d11500c08a00e240e41002003182e0b05030000f000d14002e280c2d00800e0b400c1e90b01208100d400c1da444030190111007002c3c5080c0c68a41000b01401d001c512084041004058840c943d03201903490412042e601d0580c03050900702c001d541e0b03082c0181c4440d0402c4a101c000390070803000294035845080003118404500d50030724079045c60b00303080040160b40e076100907010f1302541d44146003081045c0100c500c01c0500d4405001d035030204600060900308001e108a06201c56205c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 824739037 1250 824737787 824737817
    0x6030b12060c1b0a051011031b1e040e0106140304080f0f0418140a060815310204110a050702040e120a050408150108030a0507030c08030a1a01 63
    0x500103402109214120b651101c403480d100c01d59000c1c0743c5180489125500c001020450001a100b03c0203110880c108000c06210384148468401034072801001e080a4104402c6440020000c010840300b01040441040304d18079a04119045a407014a414900c1801042219080460a12200a80e80f0640e16618042d91541702c580284001c4903102d040102d40d100070f0306034107400c031009454460302100c0e200740c00c1103c9001801144111340e40c0c000006003c214005514080d40381500c0550340909000100b0119400c103076030004100d0080c00140b502006001c0b60700a85039451042c40900c4e40b8000c04250040c00107803500f2075401444505c08020940511340d00005582d00542d0441e000b01d0360840342a01145071281018000c500d00704005094113255802400800c1158443d20603500ea101d0802d01c0450307014000d105031a031607002008803210642c842c2e40100b9501c0e03c00d052440105981c5c0e203401c81240c00c1154104285a0384905450000e02400f00c0d100750180c2c05d10b803004210300b92003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 824740287 1250 824739037 824739043
    0x10050102030711270612280309050a080f16060914040b220509061014030f0607030606021c080c130b030103030305040605060405190f0b1e091f031202032206030b12 72
    0x1f690000300d103913001d003a0808040c85422444000c180c001c00c91396850f40c4134151141c6940b40d1081d90901441a0300311036140892040c0000b0845e05075440390308040c0d2900c52458104010081c002d580305686889186060395a040510540c1d03c03144e030100c8040c0ca10748055001c40d41c01805818196202c030b004c200e10404180210b030306450010b00e64074000c5018070301091424402d84602e0001c2e0054104010703206500d43d00c0441181c20a500b2504400c801480c0185000040c68821001801000008611004d05001400085038404400c450599180c2c40c40105800030380040740026100c4061106002c03041c018590401d1086070208a40e05014002d141008200d00e24914101c2c0c8620010400c0708444d40816803080c3c024101f1107c6603290542042c6c4c450845d840184030314082c5010a04c54200e00000d00d20700200802c00070419420740c0c89103c4482c440440c88011480100040c07820043c0c0c801c8070002d001c8403404071041036410441c000c2d081e01c01800003a4022400d031405010001400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 824741537 1250 824740287 824740333
    0xd090803040303110a050708061006140a050c030c0109110103050a140114030705220c0801140d080403050a061a030f100e0a050307030206070810050102030711270612 73
    0x16082039000c0b0303111031074005d00b00301c4019000313400c50048110001d011640480d086116005190090301c5e43d0380c4400b0155400e469494007220500400d102d0241c03c240280c008101d071140f0321040728100b014420b40c89003900d10610341140c6400c2014440580c65805001e03c60300902c0d51320781072059510100b040c40048038140f15119003840c402c1410f049644050250310301801c40500798005180d02e0880c109592020a003040098a203860410340344188208042c50603200c2d00003602080860f000200b000100c402c3c0c0094481c0d4004200c00000030f00208400c40b8494402d44001c50100407003110360001d80030043c4402d0094200e0900c8000540e0701003011101d060f80b081d03002920088100c0860b01d442c0c05100020301078480014030000780b41d000603040c4d1054201b81c0e45c0800320750341c1d116040304540192142c0350150b03009000380e400080106c48000070220020304050603091100e120740d050701c1c0c000c40d404a142840841481118146146030305540141ca1001740483d41803040c40314008010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 824742787 1250 824741537 824741543
    0x9030e09101203020a0b06012a170a0c0c09020405010905010804150e03030a0c0c170307020c091006021204050612090109061109100c0206030c13030c06030203090d0908030403 77
    0x5000003121604200094070140040d000103011000c250b1034060b5450150b404140d62061107400050b00c03540c4a2031110540c0c850003140c031110315242070385201c0410500c031000c4030f00162039030103101d1290150024211101c0b4030b5480d010000d8490800740c0f8403070025000340520034010803091000781d805c240300b0000c4401c00c2c80c0c5000d0316521800c080c552816000300d02d084084c244200c1e800031000000c0654028107000c50104500c00388000151004034014400030700385030003521081c2254020354095580102e80c0d00644042403a40400a40c21123822680c4c2544d480811005000c901c0c0e04103c00001181d44005181c44c0a0030a00014400e000c0c0d1480b40080340c0500002a0300c2d002c0a4200d0710240d98000c1091084800703103040c4200903003002d040d8038018001c0e0401341c02080d11038401c2c038035525006800c491031515242d1a08034641e109414400d0368075001840000001d010712801c070700606069400688030b0a1100281c0d06120380c640a80081091910080c01003507004411101205c0c0c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 824744037 1250 824742787 824742799
    0xd0c08071b031e12050109020319020703120b0d06062c101202032401090c08040f0204020310050a17010c080c1207031416080c0c0714030c0a03030513050409030e 71
    0x4030402080780c001449685902d032003070071705000145c0e44c582c5401841c00780c00c084001d25004d04800d007950003240240360010b000240c608200080701c003a140e0101c2808840034000d500184180e0700c0c1d00e401ea403182e0307009a210389582401c0d0075162000c403150f00045042203c00742000d0510220b45040c0d01690f0040d82e003501080004102155420401125a051040300e00074002c41020584904c1031070901c01d1a413007600300711262441c54070480420380302e1540408030490b12005030b02408029000101382a520368142c07032010526964100304040106103000600b00f031540100b52541c00d440c92a0b520703500303020589040c407900d103220b401a900da40c81d06e613a14110603507420300c0c11400740000311414041d6041401c01d01804119400040100320101d4131071b98503a84507410748070700320311983d0041c3c2107a4002c80380c1803168031000c042c40d103500075000b4202c450142c81e50001883e0b0300341540c01203002ca140080e034034104a8104415000422040b102000b1144c4c90b13480250003106680c1e0200d2140c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 824745287 1250 824744037 824744087
    0xc0608060d0b090f010506040231170606010e1c230106030b0a06060e01050412030509090408190e0a261c1407030903150e010c051806040b0910050d0c08071b03 70
    0x1004200300c18000c1c042030b01403d007803c50600266331901e00c1521a580098810b111013007441c141050710b10350744540074955013482c1000d516202ca40f00045400004400c1e810304c0504101102409190060341c0106000b04460800d5110300c0e0889901d903000c07000f40484150418449d0303030080140c40489004400360f121110b02890111141d124410105a101c3c0556040c08140230014001d0154900c00310754a1000001024041d285030320072001d4180e100040310410301800202c1c800c1141c5010301842a044540c3c031a078560340c1015150240d5401f088120489040110b40c89040c2031181c22070740f00414508401520010011a03081c0000340c0740402c03110140d500000c90313510090300300d080314008000e1039500b1940140305620095200445600ea8041160305282c1401140d00b2034400d0551719241080c581d00340142c14025112500901c4400e000080100b1500c0c0108a2201600e0381c0784440ca1a140001074500102100c400341d0044070303501c5500011b900002c4062010700030908108000e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 824746537 1250 824745287 824745367
    0x324030f1509010e16180e0316020103020f0f030402101b0f1b090f0e060c2203060e0d03050115020a03080c07060e0105220c0608060d0b090f0105060402 67
    0x14007100c01d00b041c0070340700e42d140714003030005e1003250202079825a454030150b0303016038040b078410b469907100164101d4000308010b01c2656280a2607008540c410705025040c041100441903041d0040c010301d1700303100c0d4004200021031400741c40d500700c0d41e041d5090107502c803840301c0140076100c110314400511940810003190705001c0700c6d503880c4110003c845000010b064440540001401211080141d01824521b40b81211200410780d0b44c07041d10b107007200d1030500200c0d502c621000c4c800010326800c109056840800820000d0060034610b201407002050a00c42c100b0f0010100d46059002902003801515400c0b00e081e400b00b0a07420f40b80d00740c034044030142c60b000410a41407003800d0000b85941e25240c0e001e9051035064010b203208884011181188900340480c2e0001031805240007044610505818000d90380a00e03c4583c0041018040d581028960350f41e410080800380c4d80c829860344101e441c40d5a032003003400303480c0d4403a505035001e40c20a0b82c2070320006a0700d0b00012642d440c40042c210074070742c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 824747787 1250 824746537 824746541
    0xc0e010602151b190305090703111e1e010f0c41010f0e07030203030a080c2b11210901020d0903111c08010b090102070b0324030f150901 60
    0x840f101044040e42c5450940c028845215031820900c04039080c000020300019001c50303884101e0350010f013425480c80c8500d0400146c1c0b014a421201000d4101c5000d8015445031500030408000000c5640135203465403001400c001f19401064041044445120b00065056240c0740310084020244818032030a01c0000d0f1a900611520f80340001e02d0004100102541500403030300442601004012020000f248241c941d100380c04042d4256104214030049a0b2003a645a40d10444500e1403905000701080c01280c920030b15600300561446040c1c3c00c002740c07181e600c6200102c07a4000d1030b1030316090112002800005001e42e0000001018100180f80e01c0c030290121903540c540340ba010028021a450701070104080d9407407425032445442407641d01281d41d56409010807009032550900c0340e1a041010700f09074400c1c00d1183c1180141d400000d0f100c440b01d40558060404600e00c01c081c40101e900d24403c545040c4000c07842036002c60f0398000052000701c0c103020034407601c2103640425901c400b50b60340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 824749037 1250 824747787 824747821
    0x60e0f030a0b07031a0d031725081519060c0204110d06030c0b0909040609031b0305090112152d23010201142815030c0e01060215 57
    0x900200e001001826581039001400d040f1605c2c1e00b03a03007410031000034825a002071035001408200c40800c2c01008242c0c042c10981d12a00101c2c5000300507004608140c4201e42d04071413540810201002c5c0b104c8090700c04800c0445003810b07984103e4109048010007034038142d5211306018812101c4a02085d51110307004001409010600280d40e80740d000d984900800345884103503003d00740440c0110b00100b6680858042140082c050215520303540c030361400514200c18118203010140440c40c0560741600c01c020ec14034080c1e115030381c40e181143c0014004209903c0b034a01c403a450310503000383c40c1409680070b400b0341d0040701444103030b0310113194100854803501c00005d024151607440000e200c5544032015080c05204803622004510850040e400d0b5951320911201c0c1000c0400005d05c82c46030b00c21034541c241c0c00740c0658403c035150980303003408480c444102e041c41c031403811105006000c60a0300041c001c0960030704040c02585440070094840c4000c00c1302c0c0107130703440351400b03d00781ca294004070070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 824750287 1250 824749037 824749043
    0x1e0518030408070608070c0c21020d030906020c150f03091f0b01020d260714041415040f060810051201090606050a08070e0903120f071404060e0f030a 66
    0x40d0381d0720b8a9114042d900c50482c854400042d8a000001da0b21603c50729440e00c2142c2e2110344592030606006100c25440a64040c044640c0304621155006d0703a50a4000c180d55402500c41c1c0450900713140f0006c0c140380b684e00701e984c06090381c02d00b540541c40d5604c00711420000c4200030705481e5113996403504d040840360103001044000c6404010b45100c4241c0c40440c45d07032026001c440e030102c007412058940c481907101c10403030304000c87e182142442100380c0717199200c001481d0002074810b64450300006904140c02c1000d11603090000840310741018044440c0c00d146c507a8440707081525007118040c1000a6000c1c0004020040c00420039980b030381074031030014160040002c07900035000d0034603030f000346034604040e0741d003500f011000a82420404003920903101410013510516050000381161002d001e0a90031b030a10041001e074160401c0c40c0d1140740240c0d0341100340d4119041210005024004481c0604080d00c01080304210f020f030450028a601c0b02d0990700b06c49440c6440000034180380d103901c1c010b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 824751537 1250 824750287 824750293
    0xc0e0106020f010b03010b0a05041503080c0c0319020603071b211d030c0d08070213020c06070206010e07080a0917030106021e030315030a0f03030c0807031e0518 71
    0x2054680d00801c2410442d12441c0c001c020340c40301d1500301802e030366200c0300c0d4680085000c94180941d0805411040c0d41c0d013059500103000720798a50b510b49580d0b0011031400300c2600104a6004103207070600100446200e04200b003e01c0003080d40004089100150004040c4981d41d0311194014503440c200d101107a4000e140100e00300c55001705030701e081103440c42120000c1d54200e8416240f002c807120240389600042c00a0161403006020700000900110040e030b84081c003407200d400141e440b45110346212080e01d40144c2c40e0310752800002d02d440742c003030010802d54102c1e0005101c07011240d90340d130340e10142d0703480c06000715103070000640010070000c540907007417204c12811405a104403074010f504030341d019401c45e01c01e294043d1034040324180b030004840300f81e0070400102e640d90000030002d03c00200000d098a483da1465641c404800b0400754040300401d13261502c1c0c1050701d0f04182101e40c00401414103000c5014000c00d00c068886240d82000c400a940d40c0200d80c0b02c0492402240042d1020811 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 824752787 1250 824751537 824751539
    0x210403021b120a031206091806180f08030a020705160f060c0506060d02030102091003061a040303120c0905040908120c0c07210605010e0a0605060a12090c0e01 70
    0x2511000315159819155001216600e078605210a80300e9100c01040060500c4481a581c100c135000d0350065020482d035101e09000c0380044136440f60003034a2109a0100c1c0800c1c000780f5000301940d02003840c4c0c800c5012810380740c2d004180c40861981000e0360108145a599403079a5801009000d0b17040080c0103072003821502003100084252103001e0390455415003c0003940c412003101c82400c000d0f8014160340218010482d01d04041500c0c0740550310040000d400d080d02400400c060017815004840007a0b1965410021101c0c03010070702601112180c800340c0b402e41103407405004100344403010710140741e941842602141c85011400050f01c4001c0040c00381c0300340c60a0552042c0c1015405031f444812000110349040c480d00100d0368600070b443c010b41580d42c9064075205800c0c10300c141031007104080c0c948000014019100c2c03180604240c1e03030144076500703001061034102c43d0981c1049016650030440c420902d900029883c2808000c0b0708041a807041a24240c2c1e800f50b1254012007841c0e001c100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 824754037 1250 824752787 824752793
    0x30c0306150b0708070b01080609030717070b34051206152b15030b042604080f060105010207090f020d0c08180d12020703110a030201060f050102061b2104 68
    0x18901d030740c046d0302801c0c5141d0300d8800b800d480d450241c0c0e20601c29441008901d00242c080e4000080604500d0001400c0c82076640f030305202d03040106c413140c160800905105014806280060740380d1030040c2c00c40340010803039510150480c8640303804800300154140000d4010f50b80c0600c49064060700c09080c43d1100d00e00c2d8410511070520312404424600da580701c0090317203401403051040380d044608010414038503644031000090000361080c0d4072040341c4808420a11080e2032681e10311002142c2d0315548a10b004069030410800b8017650449030000d0004000c96030380099840107481020000242a05003803101e10002d10a10464442070790410700b03503c030029001580c441c821418010303807003e1520301e0925176480350341c0b04484034003141001080e80c4600d0010740c050200b403071003030038042d19844244008500c0c004032031000305d0050b03450702c00c140040d0340004480740040800307000030030703142c00d11410340b054040015251610b02c9801050354410100c0f80540b941c1e00d500036070500c80302030074581 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 824755287 1250 824754037 824754053
    0x10203030133081b0306030c061c0501030f111905060c030417061b16030f050d141b0c0a0602090406031e0b01170a060509010b031005010e060a030c0306150b07 70
    0x2180311502c0c4503150589010144c04104403032055100501820702c1c1c503440b00802059800280100280c1070031b07050040d00441d91803090038040c50081c000225140380c246400038210300c49043c1640078030900882c44141e51101d048200c2554403c0f00c1c92901c442041c40d42500e1030040707a006c8035802c0c0405901e400414030111340c0500944a4107032100411044a01504241c820500304003100702078000d0342d4000c0f9229040c4040b22043c18500710b0b182401144012065540c48010450041005000e102d03040020040c4040192122074000d820038034892030003034955420b1100036103566000a000c000550b01c079071103940038550010709840e8803042480b030047c041d411414202c803016040800440c0030321480c40d041040c010454018581c3c2c20f0030b9035510000d8200901042d89940d03c803414005141c1d8103101001d00856a4540041c0350341c034103010003019490240209000b9070f10110300f80003058100301090f0a40350483e10106060944404901d44030340b055001100c07101c00814030f40704109800c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 824756537 1250 824755287 824755291
    0xf04020d021206040c0f030506210f060f01050a030f08071719091208090301091e0b0a0b010804031805060406050715110412020a0e0a05160e01020303013308 69
    0x500300c2d1501c1c0c1d5030f0401404212a213800302e00c0302258880d211141064841d801c5039134800c5001e060340c071802d4104d0307000b00075004080007800300c01e4000d064003031107019003000031560051030811100419490200070a00d001c40360302000d0008108100750f5424840540115582180d111041a13081e87d0b031202c11a415800c10a52522103220b81d085400f5510700c140d2800050b1100d0a080701c03e51101940c5103006540940a8107401d0354a620b41e59010071104812140480184c5001c0b9151200038600007102d60b038000c000301c9030546441c2a100c03003a603100800c2644076915007800a015481c10000d50304540c20390b4032055001000080100729994800f0140c02410700c944d8900070051140e041078000d50704903d03440c21030320f20184006c00c000000d10300d103c0c80c19400908400100d540300d00318004c8408040310b907440342d03585400900506442d0a1140703035014009140c0454009007c5000035201c0c8010b100320784083c0c804100316020b1528180c2c04000100c04440e00500c00030b240700c4050302100c81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 824757787 1250 824756537 824756557
    0x2030d08010e1b1917040503090f03061b0a0c0b04111809120a0908150402030f0a08090904061d0d030501211401024e0402010e0f04020d02 61
    0x80361000c02c1c0342440b1000b601d43d00826160060381000034500090050a44ea0a1542c00700907514480d44000020004480e00482c015801b07141d0714141001400a024410703100d02d4060f5011100b00143d072841d94020f60f03003440714035605c50340d950f82142c811201e52201880246c5110308400600040120b0401d8882c0c44020660b580e840e5445540c190b4505540d0407900d44040e60415089090180c16120082c403040c44941440c0165540314541e15203400c4500044442c012820000c3c0819440c0400120700303d0f603030640040c446410f0581c2c035002c45000d2465000e003e0080320000c40c0401030150800d00c088146852141041501c807081e11f40d44485442100e40400e152500124000d61130a01c01204405540409104100141d40d01c614100d20307803210600e2035500b80311540d40030240729100c6a40074400303000300c4a5003031540e5a281c209640c01c0c0b074220001401c4150315000ba860201c0050b403094090901d030114100980c04203000d40d44400c80c1c50780c440e200103041c9881d00990790140c2181d0381 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 824759037 1250 824757787 824757809
    0x40b030a0f06061706270a110f070b0c0d020c1b090c121806070903060e0a11040b0f0402030901060603060b07020d120207081207061a0a05010e010c02030d0801 70
    0x550501d850454407a4041d040c00a2060a01c4590011090a2107900107030302501d0304048165101040b94540360198180180800541c2448000b2142e4040c60280c6190050414a81044191265071900c00c21a009003c4903070302d8000384428500d03405441010001c1d00c42076586402203290603496081d0310300c544001d00d00301d1414190750709003007107103503c20f880807011645050510603035a480d42600901e400b170400d19040510040c20428802d460040d0303480d840f1120000c0c114238100d402e490110204041e80d611030304110001c5030500d00300182c030f480150350000d20751045c40e0104009060741c0d41c5c0c064100f8000024008018015480b81003112a00c2da01000107a0303c43c0000c03401d031701c075084002c0e51040c540c0750340710003245541e081103100d10034a004645000da699007540d410a0b01d107102590134402c004c40c0840503c80b850041ca03c040d403022108802c00f90311807000030034002c52402100d041211100040b2007030390148800c41080c0e50004c0450328003003010200107100c10802d00038a41c581e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 824760287 1250 824759037 824759051
    0x131a011701050402012c1806090901020c1c0c230c0603190e190c0303320d060b03010308070c1212180e09150c0a05040e04080f040b030a 60
    0x9a041c8202d0340a82e9059407032104003410034500480601502101e0100c1d4064200c20b41c14995613007400c240440110803d0301902e1410004100c00050000c004408030f0740104850700114601040440107200c650b0344400448034103a40407030b107154450f80010303c0346088440181c24105030000651000e540181216402c0721003d0500c030f06408155034035401045403290030603034071400e0341020b40c000c100103044071409641d10301c00c102c40390080d150036102c1d105003000a209260340207080d11030b444400c8a501d104081c2052002800c141002d002c4c000c6894007080050007500150408001426010800d60304e9503183c2c00e09410540c03150504488050340074500003090850308096100d843c1d00200c02100000503110140c44001980c4841581d100103040e000c1140c40e130400b8183d00920710000200341c444108000d0b54016140504480c0c0408001d0011042c0a903104048505881c071503a0a800c080e10b441c50002075038018112040c00f07154002c90045400d82e80c18001d14818146d0030000d00183c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 824761537 1250 824760287 824760329
    0x906090a030f03110d0906201e0903120306090f0112170d0903020c090a0b1302090406030803071e050f0f16051f0c0503100e0402010e0622230108131a01 67
    0x84032380600c0c4090285000c0c050030b11045c140d43d03044500340103482442850110180c0c0080d09105c41000d2031850980f000c001d0080c9814212495680301c41808520328665041214060b440440c3c4c2400510529040600c0c440415810381500c01400c540e00c818000a05140b80c065121030005182500038401c040001d545070029010f1010b02160241c074110011000d03054800c0079620884806402549410740000014600c000840c030a500390340d104c0401c08641a01c0c1142c2d441442030b888200602840010702d0701403c582160308203404180b103a40d130f07010202c495121040355503101505074050501010350003900c40c0d0f0024407811391000c04004241c0c03031041c1640c00340000d0700c82681c808030011007845100d4002c02d001b6001070050404043c4010941d0000e1441c2d0311118040c45c88401c050980760002c3d40001d030070005884842200d940f1300c00c0894101c00710440c1111014100704104d0040303030542c10300305507030050540c00000c220180b80050301e503081d44541c00c0c41030500c20b11185a840100e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 824762787 1250 824761537 824761571
    0x90f02271006090512030403080708121506090d051501090c020609010e10050705090d0c050112020903100504080c03040308090907030b0f10050d0203100e0906090a030f03110d0906 79
    0x50310400d0300e64140c102d0800f03081c4069107140d4a0b168420381b104020200116800c03002400203907104598195854001c01e4240014901c041c200d07130142030b40b210030340d031b4140d40b082e0039694442b006490348201410141002c924083e061480f20004540100000c100e00d0350940000c01618801d0b0201c6070f29854182106080316503080319103001b504440c05c42258400d50703400103601321302c0d6840c004d0b062014050000c2d60011450004841c42c451600c3c04000c2d6581140003446240c9500b00114100041c0c50040f0391290b42c01d80448941a0303071840020704100d9900c0658400d00c80301d00840f0b80b12038407442c00c1c040d2540314401981c41f480000c5e0000c0d40c0c00d8882c3c02a40e401040141103151100803807414401000649840340742480303800d1201c00040c024034800b5520600307202100c0c5211a16050402075400e2015221090540002c0200407c000d00090110800c0340d047c130704103211040300390342203000b00003840729101d174500300041740c6007801e043c1e03044030318024020f080410203a0074a14032404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 824764037 1250 824762787 824762789
    0x901030c0908070b07240c121e110c0f0c04111612110d030b040b01170121140c091006170604090609051e070302060409090f022710 58
    0x915881030034141300d03400b80900500303402031243ca0007074004103c036015880307207001000b4200c01e455954482210302690020380b0344094810032504025007a0b00700201121210311820701400c450f20b80c0000360200102c031088074941d41520059036032107600c104500b82c40c3e00203504610301c00c60404a0001103003200b07004843c002181c170006a8032001c2140e99a4482d22412000300003842000000c56400100600c50000c0b200c40a81d000151032221404102c2120580c825040c1080231000d07284004078941c2a507a8150b411001980720000131424200e80b000344d1600e8001d00b0700700d600707042030b00c0c5a500140c2e0b900c16841c1140c0191240c1c1e9200c400c0000c2e0100f92040c0c0000500070005c50301040c150002a6801c0180940040b031604c1550312074109492040a00b1151a48024a0310b44800150900c0c440d003a22805c0203013503201d2841c0c0004580340103a02460386525921000c0c0b0701048a5400107541c0c00742e01400201010602e420801c0207140348ac3c0b0700b2207009006c48009208001d020a8801c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 824765287 1250 824764037 824764049
    0x50a0506011d010e12070e0a0c020a02010c0c09021303140f03041703070804031b0f080703030302031e07081b1204030806180c09010e03030703020703060e070f0306020901030c09 78
    0x103032a000e600074180380c40442d6414110705100f444800c3c03003035039168000c010203081341040080080034605143c0411103503000348030811a0380703080c583e5a101580031550112031502482d05401d01d034031030b0900a0020102da80007189036440090f00702240190b07903000ca001c590040d03110014103079480280075294000c2c40b440018642081006010b1f55240031640c040c04420901280d0030101d05568000d0f103940545c100742c8101c24884200c0d00c080c0380e000050303006040c080300e02441f094078041300c8a6580d90b8030b01004044c0340e004000240e03200c501d01520010001031019644d00382c00c20345030103420960300780ca051a0365818009207041407800171044954108018510400740d558680b0101c8002d0805030003a54401d50726000c0951202003408468040c030340d400b410550300c0c1c0780200003604040300c065010f0300a4100340000d4001c2900459540201da81220300800c030840f0101c1c40d40d09125058000d902c03031408052011042c84201d40c0548143c02c001c1c2ca003040a0a07003030700b00396281060381c4034103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 824766537 1250 824765287 824765297
    0x7061d0c03150705030c25200d0204020c0f0105090106090501120b040b0a092112021206061b0601170607080f2403030d06031401050c1b0712110a0608091b06040f0e0109050a050601 79
    0x80c6005007030336030050039031402c410252010802c0c9001107600707455040d28030006583d114282408248450300c42c09004121b29901f078141441e00c0d50710850360310001800501008001000141070184903044520b1003036008082090340440c504502c0100000e01d444000011441030050242d402c01f442241c2c0880500007802c062070b41c6207810483c40e9880143c4c8948581c68000030041c01d01d0080000501804e50100c03d04a81058030103030302e01d40340b0b00a00a0040000d40405d00001881d080301e05904000c015050001c078400721a90300b4500103000c486035030580b000140c29190402a50700c010b054a106402d541c43c03954003000c955003a900140ca20900c114810010080215002004c01e240b28520000750f408240e6200200c1d03540e081c220405032004111200d0000861808551120140289040000080c106040072a54a140c400910250140300f50a295041d07030ba06001d40c1c0c001d0545122680c82e441c1c403000300304041a028801c1c5400346040201240c0c1c4030f074446c000c50f80b081206071740fa = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 824767787 1250 824766537 824766559
    0x50a020408070905091e0a0614040c0302041d1605010813121805030111030f100e070f050c0f070510020c010509040207020607061d0c03150705030c2520 67
    0x1000900020b440303503403540304140f0200e0010146041d030300c0d0105030000103880c4508503808d0240599440d548488008003203241000f00103031034000c6100640b90107450000744244a40703a5460700501500e441411446001251380f10b5183d54001c00c4e0036903000faa26985a40c5688040b8195580d0b0404002c0130b15940e040001480b034498145412040b841d90b81d00441140c0d580c01190860b181c407400b00014003400810040148181b40005070082c0001040703038502494000840101000507001d901005416125140c3c80c0e445003040d1540e0900e2402074810f01d0030f014001d2550b0b0b04480c400c1d035010309a05242e1001d02400404c469080c01ca040e1501480c0102480400000b50b1008800b280d02100a010100c0400c80c03501c0364020400000d080c840550300402071680c82c08407800b050910981c00074002252500311154250703005142d40c1407481d182d0b1140703148107581d0b028025442020444c050b200c640c0024229402c5ca00b400c0c02207003030004881000d0040404c6894500349039421240d0303000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 824769037 1250 824767787 824767799
    0xe0703020c03040b1204060605011106040311010207020405090133050d170a080a0b060f090d020d0f1b0f0b160804081e010b03030c0d0e01031e0f050a02040807 70
    0x9011641d45402603d1506848600c2c006098000100c0c480c0c030440c4e4070301000b0400c83c0e02e1007100042c2609081c181951a0791821055031008000c0c801420481a0742511155000940589101e581d0050051000d440c0500c1040e00030810841c20b82d1a0200c2c41c40642580c5140d1580f800ca10b00c4450380d1041503d080006024400e610514119415a40f00420381036100b8001c001e0060500340f940c90f6505403e043c064002583c10421035140f1485040080d0101014020101c0d0300d020402d0720001c1d10018280005403031030b14080c80c058000002c04c0c0e142d0042124a0f4400d003462800460309003c140d4039940b2a04040d034081c050003100400c1049141041d841c8400304411592007501400d26290325a8095130505030552042c189550035405581c05e840020301985014480c03d400860802c030b020032800351340b0801103500354180328100c481c03000c1c1644650440710000e001088040c0c0140c80c0110b8a6009020000c00720080c01d1508000c1802d500c40c034001c4170202c40d1003100800c45207007404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 824770287 1250 824769037 824769041
    0x3070504020c060a11191701150507061802271509130f140724020c09090c04020a200105150621250201090804170a06090b18070e0703 59
    0xc0c5c1290300c103010604c8100c00220075662041049000d030366910300da01815440101004406810521311100c5c8008201140d503401001d941c0c801c2d402002c080742280d034814035074542c030203520710194201a001100c583d880c1c120748030104d003101e0000322400081d039499001c4010030815092903035208660502090048200f00303d01028640204034407807502c0e1a640c1e44058002c0407441c003034040c0c2c100d540e0030002528000321000110f44009600700c412140900d00949441429001c00c0c410503002012440d1003c08010340807510802030000c554500038810007500300310840440f5480303071100d005c035003601180c1802828040d200d20501c22030f0082d00d030800c014441d00860944010001c170300301040005c1300e94600c040e008004030402528402006441040d01100c0e8100b00f0055a040c08910790010351440e00312411240c0704103801a00d1040040414244446240044d101d1070400850400b03000402d601c05010302c1006c50490411046101c0aa88412427482481c40d220448030000c0c036058000c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 824771537 1250 824770287 824770301
    0x3101203051210170f031603121a0a080307030905040b0310051806100b09060d0605100e0a06031a100903020a08070e0606030103110d11130b03070504020c060a 70
    0x24208941031064000b41c80040781ca0403151680a190680701c1007041c4144a083d4007004d0070b040c00500041c40286001559030710a20f0800107218000c0540312040c14480c001100c080c8000482c140300510707024462800807441101414818150f049000610340c80000813035080503032544800b8001c0345010100401400040082c0360540111030540080309000d1049900c0f800206550b002e201303500180052400d600281400b01c1c0840d0400203108805820094403e5000c0895401c0c1c3e446101c0d1a415001c1c0c00c20794007164020a105a02500003504120020035050b019101d0300d4446540341021429101c9000011890f28181900d26a4500f0500c040c004071400a0070035141ca5981c030ba0100380c04412660000c00f1a80000c0014041032151300e0003545c104008450103030946d4107644408146100c0500d2140c400c0a07550106410002d910007440d0842e1002011740844898a442d0a405825600400380c8640562240480c1600c0c251080c0c2c0c0c1c00011101c0108403ea48440c4420300030014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 824772787 1250 824771537 824771543
    0x916060f03050718240f17040f0b0c0712080c0901031d030a1e030507171b0a12060803040e18011808090907091a1602120a020a0b031012 60
    0x500074444c142d141451580c8401009103104070410700c2224450100300400e802c8807070702006808110003108a030300035494181c0d8003000741154069200d40c40c3c041d400000310f1900624455500d000c229440c40c4003005004513301410b5002000340c0880c000700c1d02040c0c00c46010409030b00601440b82e40e0b51107544032500703400d200605091500f03100103002d8555082580d00d04001030032030300d4031048904004c100c2040e18840d81000d10250a040d1409070210840007030200400344280c0003d1000c0a00004681c01e140c0e016241365640e0f0a0060010401025142c041ca185410244005420b510002c01c480031243c002c3c0801c1400c0e00e407501240104003428085000640d02c41c42da21001080c03842d8207002886c82490116030314003100041c1705180000806500501c038514038100519465001c40c50341640105850b580d0300c55400800140a0f07125101c0650011000b040c0c41007201800915a41c40c0d9000300c440104056640f00016003d01c421124450001000c07441004080e203118801e00010348 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 824774037 1250 824772787 824772797
    0x1a0c01020918071101090507033e190e04082b0f0c08151212030901240602030a08150d060c080a0b0901150e1203030916060f030507 58
    0x2500080c07080056051041c40b201112028464101e800102042401c42e90704001d00000f11662a2a500d4900c60f12000d0062040c0b403184407a000c202039410042003c20300c90b0410340c4508039580d01c40f0940c002e0500d81c083c180068250030400d90820700c6104a41d101504050280d89990b1840c03520b401c000000d1590138104100f903101407030081c000180d02c80060b4000542844c0600b40300003544d106240c92018002c4000900a50407405c0d2880721036850240c440301d00741861402982c2c509049840707200040e01c1c0120a0000144041d0000c1c00441da45140c20b20194410300e1082d42d05170803034498040075078000c0069030000c60003225200d03808121100e62041340d84403600814200c1a00c0401194829542c1d0361004800d60060111500004000c00401c0050319000c086205460180641070340311101e404c00d403004c030780f04050b5000c0780c80c8007034a0204a80c07412a10b00e9a00d03002515450000d0058803800c0303d5002c00008504200c0c1c072103a4a680c514034071440e0aa009040c040c00d4041040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 824775287 1250 824774037 824774047
    0x31106040b04080d0f0e09060d1104060902090901090e1c090909061b0912080d200403030212090a0b090a0f0605040504060506040b030f0c19170f011a0c0102 69
    0x42100400b0704020100203000e420781c1c800c01e240042c49910801000c00c148034074507880580d9615a1002240d01000c255510319241b021410941b140d8140d19940607800380c00c08a0104104400f60080d0580781c1c0260348082c401e9891304502c0042d070322100c10040e0584e00c5045085038440c03241c80c04072409c00880c1003180203e600d907150380098510f55001030b5155034948503103420400700350b050000320000900c4d00c501400d04099041ca24900301c01005040303140c020842031068046940300040404190740d80d4840b095916690b481d441c0c006201c190054082c203c86e205000688038101c440104006010510311400c3c10b46141464002000b02c540141c2114000b11350700d1840c03030019016200d07545a00791914985001c0000351140c41d0410780c000c3e071091008108072644141629001400b600000901d0b030b4440c48030704014010301d0702c1909000030314035401400c2030300070042449580d004507060100e5641e11920102d900001c0c07084603105441409904107441d8541d02800034501100300142c508 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 824776537 1250 824775287 824775299
    0xe04020915030604111810120305120f04020a090c050702060313020307032d120e0d0602190306141003180602130f050316140a0806090d030b120703110604 68
    0x19104a42c221003514980c4e08104a524041200c6d00440e007811080f03140030301d13002e1410700c2d0340d1090748a80e240d130030414459941003600032802c1d03c1f1102030201c0102c00a2412204000440c102513070264040e80c00c4a2000c139000c00a8025031440400c543c0742c079403a01c0c2a80d800d00c45103030300c001c1058400c14240d6030400b0059506002c41d400440c043c16241074030304801c05407000c0007254403030060301c0d0b03103c0c4100c000d0000d02002c0c0700150345c20721420328192260580020901210780018000c002610001e40341c503d45103d403045014002003954100102925a100b5104403441c40d02000e40c80701002c501c0845092003a00074210302c044504178a6110075440d82c900d0240c6c0c0020842100c844000841441558011524000100b104130002d1a050780c0440008518445900034410713031441c107849690030358440c9000d403001482075a04503821442e107850070b07684546807460580000b9007003400c103059500d0b017501c4040710513148401078440d2910307566940300032030381c2c9400c91504800706000c00195 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 824777787 1250 824776537 824776543
    0x7031b020405090f1e1207051e0106030507090c1d01030608030a020a1e12030b0d0f0b06030c120c04091103160f0f0f06180302040204141201060e0402091503 69
    0x2040d141c0c00812540c1080c03c1d003d8140207030180702a9000c811721200703012040d000034900e015020104403031541c03060a418054249948031000d800c0229002010341e6110405501101c22240901309551443ea150440d20090b94013418580c0d000801e80218003154010204440c81c0c01d510504000410542d501809800e5412841d60000541c03c814a20300a002654481e226255004554095070700455518540740e06404940c4e0300070543c0c0c40303001e8070041d00c55030340000c4d11a4109000641400480c500091101011111107000e405404107d00190038681070700340d19064900040d1514402280601c4010700c108801070f103450074aa00c50400c6034074240980424400440075000c98142040b080e414580c4207940910b450b6140d88404021100481070f4500507240e507460500221400f058480004d9841030300043d51161002400140b010401540d0b02e184440907112500740c51080c1d001d5074225a0a031140d20154444080041c005240603840f5031b07400a60700100b608000c0c004400b1901d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 824779037 1250 824777787 824777791
    0x120f031909060f02090f04060602120c07031a090c100509060f040f1721180303093304050f24070c090b0d1208070c05030c010207111507031b020405 65
    0x3044984c00140c0110a0500080c01d1030642c905031410b02c192403070f0005c001d640c0e074001c1041550803840802d55010380013050041c00b0046801c42a90340200c51680343c10503804000392070b40c0b050b0344281c03a403c01c200d0501c201c2c5192a854203450f0035007881048428403e13258400b9918201880e010040030401d01850341c242d4024201c8481d0030b0300190a09510246007000f0711303440e0000404204e01c9500c039805180202c9000202c0d4414510081e651000864a10302807914050741c4038050020b54082d4480c03c0c1d800c0d0008d80c14807103850855000d6004800c0303180c841d034019035130420a020640507083c148104100780c400c0781c40300e6205105c4180e814605964005680442d4a0202480c0410040b407650054880154003107518081c0100c00d581c0e0f6445400145000c0400e11035428001962079005100361000345400c0303802c1d40d98450008107078038000d5000072030031522809011014206800c0c1951030307900121005130720919140c1c1988081c1d51a01543c88094031700380c0e800072100c0042c0c5581c05458 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 824780287 1250 824779037 824779061
    0x18100905130302010c14030c070f12030b03010c0903150203100506040609060e090f0a09081c0b090a06060504090b061c0c0e040b010e1302040302091008120f03190906 73
    0x1c11101490001d0940356450f0705202044400c40365042e581d50760008a94004c210300e029035658010500c3d14000300e804c07800020f8017000824500c5825641c040c1c01600002400b10001c016940e2604400d81d031400c01d5000c0944042d0300c040c4d1003d8000155070056400c2050440804000c55070751000600690141c0c1007030780091441541082456040350740c644d1241d20894814180c0e00c0d1902c100800860010a150b1441d516980281e0038001407408881d04c4c59440c40c04c250300030f1030101246014281c51040d944c050007229000645a280c02e11614082e07480650b5034900e010300e00a40312000d84064200c0700c0e4815410802041c42e000d07201d0000d01e84811410000c40c0b48030300004d01501120020858034061400c080e4101c60580c0d10051442e0200021149185050303c1c90483c40000e014641000b90130085d99801e2183e099115551001190300d00400c4400703c204100309400741c0d010f8400300c03c3c0082c80074400700c2c00c1101881302d05003c5800d0880c0016145400e921080305a42c2d1080400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 824781537 1250 824780287 824780311
    0x18050703050c091e070c0b0a061a03060303071403040f180c0f053705031609050108010308070204020c1509010c03060509010302062d131418100905 65
    0xc00c1001030501050011500c00c0700c6a0034180b0304103203281c0a002c2d408100881960102000a00860007102502c003070a0300030f92440428a4854481002022030b801440308070040c8041e0720741045210070460f4403a0310040c01450601103e551207005890b69500401c4050109010204502c81c851818800820005410580794214000d02e1400c481c544014941040540340d50070100580003030840d018081c12058040d5201c9100620240041090701c205000844108000d1a002da120015501860a1a2181d041003001c05810f6620200510440740403400040c0104080741901003e860194009000585800115100c05090030101011800d08450304014480042e00034410402c07c4001801d04000d51420400051040281484028070454001239020060035000000b40325000106a0039691120803544d000080d400058648408041031080060b07458920002c030540c245014144c0d25039541078080704034034954010880d00c6101408000040c00c445140304240c0300b00180800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 824782787 1250 824781537 824781539
    0x50d0309110d020a15050c1902030c090f010e060d0b09070e0601050c07051003090f080403060b0f061605010e070602060603070807050a0b0c010b040f020d0615140d180507 75
    0x71080e40700740068107014141c65580b80005842d0301c48800c00b43c03801004500c02250700b06a0480701c0f8400c0903005940c82c0500c0107100c140780c05841d00d03950a18170031801c1d601d03091240300500a06040889160341c14080100c0100254004100303400d4000d800030740283d03204074807501c507511079040c10394041c0080d40c4180c1c0204003040308800e04903001002441c20b41d180422420646030b65100c3d500072144609081601410000d01960041081d25400076603084903500038105000d01d50000d210699034681400c490542078030708106444d02171440209000e0a0216a064020720480300d04001c4031035650f0740c022003101c2d150411018004008690051885142070400d143c00e00c2820703801003481e9840709609100c280d590304020030595a9030140c4c5501c80e250740034a0780c0540030583c0a40d0700540740003414200000c041e001000040f0300017400340900c42c1d550041011804606031910300040c1c0584c5200038207400f0b280100300490354864041442c0560485003801180e15080468195005c208 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 824784037 1250 824782787 824782793
    0x3040f081c020316021e041b030c020712110117010b07020f0406053706080702010e151f0503060c0a0921060c051201080318041505040b0d050d0309 65
    0x1d04010072880341c0701940c2403c90000c149011500f0b5204003d21616601a58803106c400300181e041e0140300080040c80682c281401c4200d28482880c0f1080009090411204071240000781031021622aa1800350b000b07c1c16480e15000043c504008038101f14142090903585a180071185020b4036107a030a0135030310006481048034140c507400c0064021428400c1c104a0355407180185041590b0311040d1061800c1d550030074444004c882c626110079584c00010110b030450b4007800ca644944000c1d00208050240c8a480310b91b240c0d00320000e200600400000242004882a1041c828103030889100c40a0382d1070b0b000090414000f2a0303188031503140414841d2045500c00b18100040880301007a006c2c001c15030f8600c1402e07890f8254054400745c0c842d010013080ca4410000ca403103241e410607280d003e55031907000c110386a40c440e02c031005040d42000b0381800ba514041c81101c02608031010b1024070b0f40c1ca401e09000c050b01500c2d0340580c2c003016224803180400c0042c0040e0600c0e1059550000e12845146 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 824785287 1250 824784037 824784073
    0x151503031b0303061c0c030809031204030507060f050c0c01110a3503010303090b070f12080a0e0309030c040e0a0b070905091602060402120712030207030b06010309022103040f08 78
    0x20540324042170759208902141d000c48000041c2ca810501442d0740c3c640c0b00700030916146080c0350742c512240c00014000180710022440006407501c0341d4030f40c000b21946d148101d42c1d07401103507407000c000d40050b80c5444942d802100043c07880c14090080d41ca03000226100d40a0380c10014a60403c85400f0034110750180380003080d003180f02e8400f628100c0c11541162001410304030039001c1c1030200f5600048100c280301b500100c58429650040c4040850408208020000801504d400d940c060600c2d01d40364403040e01006031011000301600405014100c1320400028200713040344035205005184404012130440d14046110361405d490710102c1034a04024442c0d0316600600c00982c00840282d440c0c1c1060340071900640107901103880410741c103411000c40341411103a42c449010000c045420200b00740d0081084c004580c010a19200a95202001542a9420300c40001e6010b010210700750700307046244004001c0c440416045030308064844c109110f0303080b000e801094150b07201c01840c00850b2111 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 824786537 1250 824785287 824785309
    0x1602071a180d0803151c050a02030d0504080a0326070c1203051e0a0b120d0905031c0c0507230913240f0c09080609151503031b030306 59
    0xa036620b5440110300d458070000c50001400e0181d010a24401c00c034299a01c2c2e8103c0e90740c0425414144000260524100750303280c00c0094200d000e0b014080180100c0d50241302900e085a510501501e558211507804427480c8a041c0d1000c0c501654100310416000002183d032403103101d10f0f03141d400e00c0b82403a00340f454124100c0c0946100701030408041001207004030041072000000403680000c10703145c01407008042d0090070082d61300801501942c01001a00041c00e10700c1000688030f511b043c0f5101c0c1e003419101c1e100d070313540f0300c1c2c100f050005440e01191107803503141240380c06034084c0c0f00c2c40c64403130045011556003140e460286440718051044a403502a0095800c031100f4003400c440903000d550b8030b070104d402030340400e540d00c80c0e0803862449007541a0003401c031000240400f089094024400071b400c1025074000c400c41c40c400c810005011040024050449040d196407480300c039502c1204103012000220b000076010b0005004020300c585110310700e1102c20300300c07030080c0d1707140d1920005200d446120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 824787787 1250 824786537 824786539
    0xc0a0c0f1719050c10091e0503190c150203031006031401270203130c12080d2c0d020c010c02011205070203120406020d050606030402091602071a18 65
    0x2a08108044881c000420b80d0702405216034100e40525141442400e051351803100e00d802624110140030342603030018425064a00340a0031340300c260350094400c1440d2400e402170130703019808848103034140000c01c502000c119204501c040c51054441c01e00d101800f1050840b400540d0001c0184860318a000060742e01074541032a04015842d02030910100c0d840d410f01c81d00c500702110301043c0c203505076030090301c00910103c480195a642030605601c40386104d50541650200e6102c0360219068038134068401e0002d81105201d0704092100c4041030040c00c003090440d650300742003001c0d800100180c02c802c049032507144014001c42c2c1e4101c030b4083c0c101880501d040b41040851240e100040c0e03042440e50400c120310020002d42c5a0360868140c0c5107118560207040744000e218208400c010301c5070010302c40d0341d1442c0320a100e991220020b104103404240c50080d40400c018000951f40b8200e80c0003410a00d00903c112100755503120012120b43c540d0001001c0703c1c200010341d048461404940d0502c0d1240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 824789037 1250 824787787 824787809
    0x60f0b01050c210c010617010e0604020901061d0a0902130e01080706082229010614070c0b0c0c01030506030a02090c030a1e05011805040519080c0a0c0f 67
    0x420300001684640240401c048285080c1c0703802283e901908041d40d01008146001300b042c01e86915414a4a5a4088030b60415600b00b89119140450128419000c1c1c0c0e4003400020060342491010368035010440c0340d0700303100101c98208046170307600c09031010010000c0d0040140d54030f9410501c40c0070041603800101040d0741d001d00400c4600c04c0020018210f4085141c81341c095240e81d0342d60a50030110701456aa00e01444204030300780084415450180340141c0595440311000c00c0c00200d2001c02486410302040307000318441d0048441e100241111885040c0d02c08581da1200445010b940110042c10505c1e4807400c150305443d6090321840e600060210010001c0424690020300310366001024401008408004102000b0480d00241c5030800201c610400805800c020360004017070074810409422040340c081c462105d058031951b8000c17a00b081c0601403904443c4408108002422011580d030320040098002d040400d01200101c1d5205000001c0480d06d0031030034503446010fa8110904000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 824790287 1250 824789037 824789047
    0x308040e150112090203010905070e07091a04030201030906090b0a1d01050411060c1204090219080921070c030b010306060e0f060d02010e090711071a0f030a18060f0b0105 75
    0x680c100801d2190f100d140500411205680e101090152070804c3c001010351080e00408030b07896981410403840352241d5601e81030704079030705c00f241000c1a200a14200501008100910165101ba00121051401040c01203003086a55a82e071a1044040b180000c100d82c2d1000b10501c24205200b0030900c09403403000910003401d0a803a0a100f50a6402d40113103d5280055462030209080c80070b080300d4505e903083c4035100e0340d0320055800654066100c0e012100680d0b243c0c1c458482c0206142c0340140b00e80300040c164110200b03800d100500e00c20f08418100c1400f48041c200042501514001540c419a020415549945003102c2030740d140e50000c82641d0504c00400800400e0703121441d9100904903500044042c0d1800162004001d442109400107a41000c02000e607070803135100b41d24201008103c842c240e42e180f540030516140311003001c503000030803c0034a100d00041d002660b04020346540000e000b040407212020020f0b0080e00407030b6516100d00c0c00a00c8000e01d8458015841c0003824800c1c641 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 824791537 1250 824790287 824790289
    0x10210060f090b1c050109020901120b07270303030e0f2404020a050603160e10090b0d0b100206040302010606181503110c1e01020a02030a0c06090b010308040e15 71
    0xc0409406403104843c1d48001c008031660b10070800f4a4881c02d00f0903180c0103440242881c5010740fa520307606902072501e00000141c082c420006410700c2c0c540052201000c0c0d103c00e401114250360185480010807540200c194503040859202c0c0002c600c01d0710001008400c040003182000418000d41c5140d400c44004400750962501a002000a000c0d010040a90b214800224140040c1c0c0210350496030100c2008111a1450550810000c441d25081c2c59030712510100106101f14450040020700c40100c204814411000501501a0680f402144110900002c0f5004075280c80240300142c0c0101c0a000c2810340a101d2480034007482d1800b0074611001142650350b41c80c40c2d00c9681c46810000da0b2011003581700f5807100840020300c410302540c40000090243d50303107890903800c0c29950611110342d4502201442200d1002d00160091414141d4248058925400720081a5252900c84214400007021059a60701075481084000d4a079420284d220302d08240091201c14075009042d598406 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 824792787 1250 824791537 824791559
    0x109091b030e030301052110060905011d06010210020937090605010e090403030f060b0309150411040b01090f0603020a030507020f0a081e072a12030e15160201021006 73
    0x1a40c0118003440c04a091940503040c036100e10b00070a0094245088004032b14420a0303000039040303440180d8070580e0030320740b00c03170a140400098482030b015a00c402040c0514040036005861582801000741c0d8400c0c404034440d199141c0ca905106c1e1f03070a0140320283d8102c540490f103400207040304103400c0088608080028103140600c11307039a88104980400181018469000725401a52a5005110081e640c0d00c00c0c1249400680301240a40503560a4007100452a90410304c616004244200000050000e100007011010701c92030401c04103460104000c1100c1c400340005024503500142d445440d41e400808a40020741900308640000700010040c0000050940032190010211640c65294907000000c000d515241019107110202d01c140c180881e10800341d02080b4800c204a0108001a038441c092090320f004004581099041031800b10780701d84507c0c00c140d10050008202c03220440019080f5403c13603000d030a00386c0120001030703046503414410007440031106030051000c81e041481e0308030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 824794037 1250 824792787 824792809
    0x706020c09100512011a04110702150403050d12060e0c03040b10180906050106050712540f17070f15030509150c0304020109091b030e03030105 63
    0x12040c14080301107201c0c0b0a2401a035002010b0090540300a001030a041c0e9000e03040410f407030f401507810801088058101030092041485009800324688000c0b582007101c1c24008020249030540305010100c002035082207014006101071710740c500019441481c41d0140c42c22604802c182104840030702c01200f0640050701d03080f6502002010440d030310407126200031038a40e4080101c04416101a5001c542103602c40522507001e06828807490f80c940100b542c2a11031200b00800743c0c00107440206600c1d10600260780081c0700910400d0a59400c000a00f420740c804030749582102c01c1401d0648100c00000d444540c844d000e14090b038400514000c4c0c40c4c41e0b802c1c0b0903c2103600002600c5400c40c0030386014030100c4064640c0039101c445850f103074040722484500030509500460f103010b0200e5464040003d0f00320400d1450b8003a0a841c2c0d40d00e40000005400282003241400740541e0003140c0341e100c40c01080c904418141c580c3c020b4035a1908001c054032100100706205410400c0140310603190b0f0a81a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 824795287 1250 824794037 824794039
    0x6030705190c02060a0318050303010b071509030203070305030901060519210302100b06070507031a0a1505060703120e0606010210051509060a031203060911090a06030e0a081216020706020c 83
    0xd03544107c0d01c0100b90348a0b040340000d141e40000000421032101102c00b40c201c403401294038440000384050385d4800c44400d0000507016078014801900081d118000942c0c0c40409240082034041d0341d100072032601c0c0c86c9803601a410402c00c2000703011200721400510340e180d4074035026070740d410407585010351200d10f081c480301150341e298801c1f40c4103511600e04982405612408482e075042d600d09140080c1c0303640c8108058102100c00c00300d0a07800180c0103205d0a0032401c592007405510b0030003007111940c03001c0003c80920901031540302c4036a2031846040151001c040190145113805000203040900d0b1060001d8502d26243c1031011080300480c0700d2881000a440740202510f440c00003030184401903200500e454011085c0544d081c1d4180c01100480701000001c0c410b07604020282503481c000c03c594541c10148050041100c14883d403c040800d0340c030750f01590800c0d82181c50300603042d40200041e01807070b402c250030b110004d10061110014484144003828009082c02402501d41d02020a91 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 824796537 1250 824795287 824795291
    0x40c1205070221030403031404030f0e1c1a01210f030c02131509090321020c010f0911060f1e040512060712021804150506030705190c02060a03 63
    0x1d10300c18001c001c001040c01078070342140071030002d4a02c0c040c40340d401110120002418a900d100340480715101882c0513952544401e80c08180c8041c0448000351511425a03200759400030440e018040040707042c15007401141d0b007a8422035075200d40071940c4410380c401d00c01720501e0241d10800c1211703440e0021001da842148280c2070703000b03070404035800b40301004080d41c80000c80118480d80c00712603100f40b00200c8100e01c02d09800741d845030a8421107103040c2014004c21580c00b18000007140702c50501d048a01c075050014184040306289034212850010208038403a03440700304500b84503188060506075403048a10914040000036030420320301900d00d0201002c1461b1031126007c1442d042a54050070018081c0c9444120350112a90750300c2c0c00b07a4990b40030030002ca0429071151607030b008545a070785000200c890b40d00311481c28030000307180c50001178040107003030500400c480c0e64801c0114010340c00b60340c1c0c598540c4c0c25004c10120b00c12001d083c0d101401103000c005401030700c400d01a0b46600c5818140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 824797787 1250 824796537 824796541
    0x9050a05151818010e07031109040504230d03051602031c060801020f031603050907050f031c020705100c0f0b0a09020a08160f0f0e100b07050c040b040c1205 69
    0x90100c0701c86007140c07241e4024040b41840480c41001c0150a040b80c501d50174811003a2140b401c158100e13800c00400c0c010400042107401d6441c14140c0080303170014419004100c0d061403560202001500d504040b486542045074002d00d415854007940385c0115610701050742081040030040d40e41c1c4200301e540c6014400c450311041c02e411050340000c0042400200940d03507103817101550380380c90b4021180203111322080508800c01c1c074802d1003800d100d10100001807500f2424002081780c50f010402d03d01d507240c403c03488042c1e004070006084981c05500c0350018448181042c040100204001403d18200060120b2038004503041d10801c3c240a9040300341c0c800103803201c21000e00540000080139410449000000a8106000450894061a0a00003a0703483c6c2ca410f034060207031006103d01014003604200a00402d0050b004003034203d030050018080d6283d850ba00002d86412200c0e0030340d1b168001c0706440000d820315024180141d24201c80400444000c45400340565030a06100017080c0d0761900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 824799037 1250 824797787 824797807
    0x1113031403070804120201030f0209030c152116021501050607060e1605090a11040315020721140f0a2a11120a0b1f030c060c0309050a0515 61
    0x100b16404603400500480d034983c2c42d010500c0000005560072800030340361210490703a94196100b6164004d03c001c000e021110302c90f1040284110071101038020f90801004150510130074031000c101c40001d42c1c0b503440198030306070340c00e40b090659140703501d010354025800c280004502e001c41181502c0040b1100d07500d8628034241f46008001041101c0c8031845003034100314110340142040d004803002224200903e0ba41c0080f008203407903920380c0c5400035a409001c1440058a00c444010f420007802c10014140400da4640000c20b85c42164401c00c5280b0601816050b15404140307092104000408246080b0310720118038400d2060b90312200401030010b45020301140060060841d42081c0b100034401ca03016400d0041100300c14414075803082d003110070805000d10010034038002c4207800100e8030215640b00442da80c0c90000601c02c0c442c02096110000c000074014901000241029503981d000c4100c9610f405030040c0f845410070f078400d501c4c03500304000d0703547c6928614020721842c400050b01c80141c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 824800287 1250 824799037 824799043
    0x10120908040b040e18011104090b0d02041d190309030809181518060901030305030c07020901120b09010605060405060a02120a11190807060c3011130314 67
    0x140100e4420000000d00041d030416200040717004001aa2040d40c05040d00385005080703403900c0d0105402c080003840200410701496000c420036110141c03140042c032201c4e6000504469004416218128111201341d40302542005401c21800f01010b01c0d006020082d1009400c06c42c0034071000f081d0ba1000142030000b922085a81c40d0000349055010300d0b0ba08004140026401540d80b1240c041c0c01d04501544110b801e50602a0040340041d103d61850307425614215420b51000700282d5841204012600050300c4040801e8000d100000b880e1480b10240c3ca00b607000130502621110889c0e040c0325048c80035998100444088520485501d81c2e03880210700240d04040c860181a55060008a00c4907943c0e500a0103280e00c1c1152038055a143c0d0402c1028003000884000016186503014009100000d086030310040414049060034131980d0341104845000a8000303884100c00c90034003c42c01124651030151504a000d5050058144507224240703140c0c884040c800986650b42c4c0b005401035202042c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 824801537 1250 824800287 824800289
    0x10503060c18120105011d10120c0305070b04030b090a0510050618090a0b090715031d010f06030c06140d0506010306051005031605180103050709091503020f1012090804 74
    0x580f2000301100404001e5000b40303400d2054880442d02290642641c4001440707061041403943c0074088610300f02303a900a46010368031411100c1d0712201e00007001241d01040030714020003404039000d41e642c0c20340c541054028405003020400342d10199503040010400304014510150042c00001c683d6621400111040311039000788046030080014002c46810100705401503d00420040080c0d868000034155104058800c80ca4080c000c0c440010107244a90880a581f101100c0b00d92a09040600307814211140003641c1c50f0310541d20182001009002c004001c003c1220f400c149002140200c01e074503d074800c0502e00d0304001c3d510000500580c1c040c1d8400e00151034080d0823420560b10503680070f080eaa00030f480c010030740e00200000702d811a100f4001c540120741a020203425401107900194081c100240144080c4003641e280807681c45003500c41e6003408206240c01e02c2c49203142d801444111032014080701c1c040c41507103400890454100010010b003c2e8050b000003003140d9541010340040c015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 824802787 1250 824801537 824801539
    0x60c030f030b270405121e0d0204180203060f040b01090e0a09140a05280b0a0e030d062c0f07091d061809071502070308160b0708010503060c18 63
    0x8600c903148a4011801d40d03d40c4940e11400480e00c0c0b040365130511b1900c40c0a00c4420000824060401060312000341000d0726500c0803810000d41055101c40b04064164043c1c03001c20b55866000c810880280f46c4040161000d0741c05881c1004441030201c0000c041c0c1545e402003040c40e0f034031200420b4045c1c00a51000c0344160300820110034441c0c1c01880141c40f03604402e01541c041c41542d90304003910800e03125511030503030415108649010603540701c8505540080000c0041581c480051407010401c0c0010041041041d10008090742419500c4e607003414038408402401440b80700403075190580ca0401341d08050080f1051860b603a4070f8004036a1b014903030704a01d600e18594405600d14800204d60355001d5641150900e200710044685c0c83d00b40320040350f65007083d91282c0301c100018065a8080204581d551050790001030302c1e61a101d03483ea019040c0b501c061480c541c00309060112401e152500305106181c805c507a549000006541d440001c2c0022840003000941d582c407d00500703615282000c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 824804037 1250 824802787 824802829
    0x3080f18060409020423010206010e06030102090d0b06040c031b030b1f1701050405150105180604030b040b010806070905040c0323012912060111030409020a020106060c030f030b 78
    0x520782030080085c0d0428884e00381c1ea0121440d50000d00c008448061019241c1030780203004580c030784106441241c60140c0004c2d0995420054006207032280041000564024a0241800d0600b4130911044913070000442c005c0502e0480385881e05001444094007404041ca40803818144020000d06c08513440ca8801d90400080b03800c8003800c5400c4206142c11802d50b2480044e1a80c0c2c0d01c00b07000540340d045511031161408044044032540c041e0b4040c2c00800c1ca90042e912070700f0307410800300d6a10b0307104e500261a003103a4441040200280010460b0240440d640034007030a0402c2d641c0644403003503500841d480395440c0c0c80000311103446a4800138400c40c24110542c09480b235089030549aa1003030141055489041c88003060402c0c01e11040c4686d069003d4110349811300603143e00c01d640300d0143c1078504014010001c818507401c00c0001c1d20280239180001030703803080d038400c0103402c56030150f00000a102072034800c1da000c2a00216038501440b11810701248580b643c00000e604000e80c2080c400c2129 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 824805287 1250 824804037 824804039
    0x1e03110c011a010e010e28231f0c05100c0c0b0105010203031e0901180b0709050307060f030b1212040801050a0218130f090f0203100603080f180604 65
    0x200c4150449004202a01c01d000c0400d0000381c01155004600ba480d940440c1c005040c1030580c0c20304400407a1803604c140c40b000c1c070441d0f181c0342940c0d06007081d6005034120b0b4808001910310b400d00403d02d51030000c0407a0300c1800070300059407030a42507005101590a000c0604519424043c2c00d000c0305a111145175000c10003a404d0240183c0b0f90340ca40c500a4406608040010803d9400002184d010312a1404062401480c03004c071101c2500e00180b0401665480c0d02000e6541c40310b18850344020f41c0b0580d200440c5241c4000000d04c80000c80d07003c0d13480380e402500300300720054201c101c4100c40040c5160114480f80301d080031440c1c102140d4034412091042c01c00e114921906e4002a02c150ec1c91000203003c0b94585c41034840903401502c040340394410078070b551400c00345009a1403000c1e05842200109050b1400da165104039200804203950400180310118118602030219070f0407644d401ca010031507942140c85903034040c0112440003480c4400001c04c0d103486613070030a041c400098020102c582d62 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 824806537 1250 824805287 824805307
    0x3210e011b020f0106061d0f032e0b090a0b0d020d06020310061e0302160f06050402100201140403110a08030108070801061703030708100302100228031e0311 69
    0x19480306a040d4014018000c0c01d0f60b60740c00600840e401c42d12240d41c0d5100c144c0d4504071141032816283d0103254800c00741c6540c031030b4980b400d00c224600c0842c1007048070440c01d0440200402d142c0d21004694100340341c080800003a0796001000307600461030500014440701d010001c00c004601c41d0b40042c1d0702c84a03031143c2c0d5040240300c1d0001c511030280400418540d17175803080d06803843c5010850040034129060780825047c0d11035409400c07a41441280d116143c8555100c01061421803901662f80355100c0b0104001e5091035941e2012061a52000300b140603d054022030b11408041d0008007008610040d4840c0008100070b00820560004840c95480d41d4540d2510f9460515124051165003000d0700050b5000c0c081100da07200e103074600c000d90b107507a5682c14111204c0c80000d0000100070000000070000d82c07140c45400c8100c0510380c0090200000d04141040b503400760241b00704454030280003201c0005e17881200381c428180711884040c00107120303a009a0280c040c00c3d000c1105008041940614 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 824807787 1250 824806537 824806571
    0x1d040b1f02010b03070b04030b150901180b0603012301020c19080601060c0803010b300a050f0c0a0e06160c030308010b130b03070e0907030207060f0903210e01 70
    0x1641590000c00480c3c0c805014940c90300080e00c22a4890041800304002041d4110f01c100d500600c0c1364501c890598403d40000d20081003a040142180d2103070560302c1807401d0394861107040c000126511410756241c0a49150b13000007002140c4c2e0300d20080e03460590980d001b085001e2201d20300414072281c40000c040c641000b40300d00e00c51b010f2248268000000e202d405080c1d000d0500b0b400454003880d681c04d00e02e1140d0b0700d030700c542c220700c140030080e050120300c14000200c0040001c001151948190405603500426100050040d0701084680d009100c80342ca0745c03008544050415041a0010401e2440007030414000ca09202001034140e001c510104080c0143c0803050324402d4a60802d9641c88898010aa00814a484851707076000321060100607000c0c1b000c2e40e840512403074520381c2d280309140850391070541520304401003600490301348104241030080c000710006030b500c1081100c00589005015031a5425134944c0e65184240c58101808507030041000806204003c5c407040d01e0340c044803d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 824809037 1250 824807787 824807839
    0xb030703060c170a0501050d0318050307030f03034203080c07061205150d0f02100806010e0402070803130f0501020c060103030f020c0d11210102041d01061d040b 71
    0x22640d043c030800181c0c031082921802d4143c40025101138a9000031340d03401d850305019841d50a02c10425000300003015541080b12001841c0b194000d4403c541c000d24028066070342613201c80741e140c0c2007a00c20300c18070400c950f0f01d140d4030480300100354508150600420441d01d081c0d00046d003d8180080c024810641c0010301200b22041541ca801a0f400005448400c941003078403486101200180c00292a1a10031701c1c501e241c0d8024022032000c0c0500390b0006100d83c403940c200c039004c11010020050150b0308804010541503080d1829440c1244559551407107100c014841c0381c892424110200501009407400c02c190742d4000002c540d00c2c89404801c136650b00003488110700140e1341c00220040c052002c00c20b05040e00703020b80a614041000d075a00c8440540410886030090042440c2509483d0714845051700c45075082d00060b56641042031b0304045940b4444400b10002e0030700010060180c0c054204014020b1401001024600078000a03029003070308906c0315400303400c2c00500d0412481040000c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 824810287 1250 824809037 824809067
    0x150d11040f0e0c1c180303060f0512030f13080d050306150702060313021513030506070c050d0318060e010c120c170a0605032410180b030703060c 64
    0x20309410b03980c006590314030108440e0107078450020301ca10081003040d41c4440d00e286041c00804a9411304a800c00b20a00e22204410313000a5104c050403c110410340190314080c08e4103481810f00700481200389a62071168045880d805800001c01d444e00e103848100788000380070a14203850b03041c401c0c048010643c1d0415102c2900c1000c10314030051000c8100001ca0310b520780d004c0c0c000e504503503901c511010404204601a6005040d200c80030303a045103500e006200202160b100d901d11320741981015464410300600c50401c0c480c045020714041040043c2030605e022039031601094405000c4e01c0e45442cad13241100000d04a9041c18841290b48006402c00c41c0040c9065655596100180152006a855000c403c0c0c0202c0c80078464004840c42c1c1c0c20505a00880e000b20100d01e01340c0c1c13000424a001c64000702c8540080b6568408a50125007054189d000400c20704e01c01810340c2800c0d2800c000b00c04000c05230760314030fa4850010310395403801d1100c1c000a40d00100c003000320702103600003d0071007005002e2034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 824811537 1250 824810287 824810309
    0x816060806030307020f0d23030a0207090e03040e180303010b091017130c08070f0509071d0609041407030b040c02010513030c080409020d02071a090a02150d1104 71
    0x1030030790b050000a83d0360307481d001001c0091030084002805600501540d00703032880c0c90318140b02e03000040008a20000f0454090045030340d075010001c02428106a904410304c0a03040c040f10000c80140041074405840c81100e103800503442c0c4110156401228045140d424000400001040314000c00500a848000c0d5404446010014005c80d048040d007040b6001c011070980100d41070421001c0314802181c8548108140243c407951880d28040441d804000300c2609450144018107090030569084201810540015100510444840c01d000722003076008150218100e44d40d683c4035044881c2c03508051049102034101510010090602d0b240c80742d0040d03080440014840e0310522440b80b16070a8410710f09100e425a5504482c00d000508003a54088014030010645641500c0106650813083c800140e894040b454800e1301e0b4003d014100d4031800d404010021518004100588015411260540c2c5603821b184807103454010070807402c62880c5858155070091309044020400d681d104242 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 824812787 1250 824811537 824811541
    0xa052d010e07080601230c030715060f081507031803020115060c1511070b0906060109090e0309040504051603030207260a030c03050409090b060a050f030d1808160608 73
    0x100343d907240e03002c0e07031001e00064241d400307551031001c0c2400052522100501d02c40c945650034075140e1030743e0420001542d103280800d141401c2d044280c41584001c001c03003111030b0350040c0752280080c0c5880e6040441c80d000c0500100140106100f40e000000360703070849001400000e480d003030090003004cc0c4105080d9454500801017002c1c1d0240100d410019445141300c0142c200700f514210140c004644a489103071000d01044000440040d150351003100d12500404071803030301a000418041d41640107402540c0f070b088d1b101c0c00005000c4121414000141c8012039540c80b580b912501d40f6140c840c1c40d40307142d800c0b1500802010b40c01f0420200701d50020b24445000c4032400040c2a81010a01500d0140e6104407400c0c00041c1c0940c55058142d40217003012401c10b540e5640b41c0301960503032002155402c490320304003e01403030114140c401800080e00c00c8410b01200d1004640d44074807009420040c041c000c000f00501030224901e0a01424651013034402e020900c5030680791443c0c25028040200d545140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 824814037 1250 824812787 824812801
    0x40e04060b030633100228080a03020306010908010609020714150f091c0507053c07030c09020c06070c0f02090720070510020c06030a052d010e 63
    0xc1003805401d9000c94103d5051000c0d13142100b00c8a4080e00440f001d55201102d400e6590f02c990081003184150081d08070320080450f2854601c0d400222200314900140081c00070074a45015120101241c1c1401070b500d4071140c0040c2c490034130a9016030b50179802e0242c08a124455034010300901c5102d8911440380c043c081c8111522021044440c40340b400745040004d000a40754071102c0e4111608200765880740400038a41e41510780c00c0c940880c00f207030000800404202c4108082d140c0f245100400003001c2c0340c1a000d104261000d40c9103a0401001d40340c0d0b030030280a09204c004002d541c040210740c0300640d140107010194104250003480e038022400007030041070048400403070b076a6003c25456180040c680c00c00141c1e02d0060000801c1002c0c144680010407855030b482c40b8030742c004200505141d0318040400c040340300302c080300c0021500710030100809500c480043ea85c01c03010010000c10b003a641ca924004007180312980407229201d03145a0128109907044483c0e061b118000071000c5a41d40d803007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 824815287 1250 824814037 824814043
    0x1506030f05130206070f060f0c0809030a0906030c1704050105010e0105120d0302070f050118122a03020c0901030c050a0e040f0330020c0601080c1309050111040e04060b03 75
    0x2c800b405119428a064401850444000c001c040c0c401e0f000009560103945501e4100c5040740c0d01c1d03200e01a9100c40a04009402a1f074050f80541c0110040d450b1011240c00104010303540e20502007030540711030034448250301881e503403400f458252120f60010700d4141807540c080c00f02849030203c440d040b18008602424008803c0c440928a04014058100d0b0014102c0083d444440185c403080340c80c100751000075170300780036a0303440d009200e4010440f00341d203040c55094506020160401c0c0000095030b09400d06402940300c2542d141c400c044041c480309414182d09000b122003000754080c90401c000700400c5200ca1514007626002d80d20b900b07800f07850b070900036180300c02550f002d0706459044500e280003034400d0415005c00d1124440b90861901c21310840b103a04451400300c80f0045402103501d8200007010860b05004240d070300c0c000c10b88010040c001c5610f00803504106250141ca80d1501c0c81840002d4000e000d14001442215981b99030752822000002c009a800f01c840608140c955031b02840c0c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 824816537 1250 824815287 824815291
    0x31a1002031204030306052116211406090d2318030a060606030b01030e0a1a0a020f0a09030201030c0c02060d15031703010e0f01081209060d1506030f05 67
    0x580c0040d0320740041c201e07100ca2640710041c421000c1540300d034804902503d9800400d4031205c52401c0d240794058030304042c07506041503000002c1100076911001c000c0307107040b92090341f0006940c0145c0712555000c1d0400c0308240307100050509441c443e960501484010009015201142c41d036a4000d50785040c0055007410001c00b0801c0708103c106000000c1107110340303a1003814000d401030807241c08a080d940c507042070ba1101e500c414042603480c581000a560940070f040d41c41645c02000d132050000c2940e5400e1403000200780824460a4480041d80300f20181d03040340c0210403000c0d03009031034200054004104003018001240068200300c0040691f034010f10307060f80621343c028006401d00c1031080d07070342000305881c0f0782149070603c1c0d00100001140c00000351501004003201c3d2107030b880d81400702c2880c1c01c0700e01600d640b00109c5003800400c400c40303000c40e440360440304440d5103941d54508900011114010300c180c0d074151a03d0b00c8100c002d95500d2580f034000b200c4081c0c13014030a0100b0703015650221101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 824817787 1250 824816537 824816569
    0x230709060815060a180803180d0b0a110d06030803101d040809030304050a03060204030203010c020304060509010f110d0906140f040315021201092901050703030b030f010c031a 77
    0x4068240d010383c40e181c4081c04481c8150302d040600c116801c80c1c0100007400980c800c45054100149860038a41c503500118101807098a0015100800365110006080018104800590b0399100203408085050488034400c80c8210140000c3c0d0710f81c285020164010707113440c9040842220300082402c445e22500400803080060011603544944402419038814120982e05010800020a40c2c0d9114001d1002071801140016122803c1d881403500b1286140c10300300a550085c003041101c1c651120840300174400a2038a00e003030726a504800d45080c0c0b096040802203004000000c48680e0340b0040050440d55660f039100c1000410380354654039407003400792441401c402080148040380c0d0300c08088032040c0320702d100103180110004603900000d8007a040405020384940030060f40701501056810010080303134901e0388240519002070841d125218004080c1515811101950f035810300c47c6010502820000380441c2c1f0034408000c1c028400304100c1c01c1040c0e40c0140c0079283c0e003800b42206422081c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 824819037 1250 824817787 824817811
    0x405010f0c0b2707090b040f060e070e0402040f060203030405251a0903030304030f09080c0f0d050703080313050f07080703380402010f141c2307090608 67
    0x194070700d948598010308002403c2900c3c0c0900c250103062002c008020061815800014080d0341c3d060801c015282c00601c02085103060481c01d02c136400b1454070b0203030008983d040c5240c0c0e00103a0702c00704001c2c0c041e603404031f4540007094400050f02c64011000b944200d2080b804c0d1070303805501c5801641c074a008040300c0c1c81d421121150520030b01d415080103113002a2103103d9542403c4100300060b00d03541c81150300301c00042c42802024076540d00148424054000103002e44130303c01c055400324450741c420403016482080282084000d201e8240701d0f40300a5a0042c10312035403440c12060401407807030099003c5606c0c3c8290940c1c0d030b0100c500450344c1c4081e2440c0d040500101071440d01c484c1200c03440c004207400d1480f0026034040c29550320070120743d2903c0201020320007614050001404c400b880990322001d010b039650503068408811001c40b001401400440007440000e106054002e20a41d01d4a11000202d0514190310b103059602c8644115100d03903500a440c2c0e121041101c0c0300700182e032a99a404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 824820143 1106 824819037 824819041
    0x50f13111306020f101109040c1e03060e0a09021903060f0e06070207230a0905040506130302190201121b030c020a020913080705030c030405010f0c0b 66
    0x2003914000713071a00411100d4003544840d81c030481c512203907503996804807464507100700380d906020000e4801c110352449500058650328151103070060166044000a8030180709010f9a009d4449410406a090f102d20010a0140c80340e0b5500300d0f405001050b41c6443e0010034099880254001c80d4082800143c084100088a00b4442c103100d10360058404c0200c0242c00042000031514015035151403016188040002101c846003d01d0b48002d4144c1c0004400042c0d40009006a00803c180c91003919030610b81c008442e0380b480d0013005600201c90742040300800000030b60090340181000795a80401d03c140004803410400c030f02100190a2051042d0140d042c8904400309107680010035a41c4142d030005070f138501c1c0003845681c81c12a050204c40810051405442030554041d04032511025458582ca8480e0064001c04c0e001034243c0103000f0102d4070404800f1a01074000105100340e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 824640287 824820143 := by
  have h0 := BRFrame.cov_init 824640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 824640287 ≤ n) (h2 : n < 824820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
