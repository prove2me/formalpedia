-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2323
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:21:25.798052+00:00
-- url     : https://prove2.me/submissions/31d07b9e-ed0d-42f2-bbbc-2487caa30d52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 417625899 ≤ n < 417805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 417627149 1250 417625899 417625913
    0x9100b04090207110904030e18092d07030f0c090b010c1101360e1501080c04030b31080d0b150316021b030309010e01030f1a0f010804 59
    0x426101c4051001d6902c0c08581002c01e000e42510040c03a500055000c144010143c22840034080c180c010303141d94440c3d80d00d04c502d1142030403040f2104d19440d0090b0f09080c5a4aa01c1d02000c42f0400100b90519511201030350711070310f4001c071508200d07400c0f45442012424000b40c414414001e01c4089014401c410025000902d40c010340075000706524600000c401440e0300030101001c03280041a410103602d484103003100c41120401c24680c8100e00852070124851030318410582c4224540094941044400001154111001013003155800710600c404070000764501d20080c003400e010300001e2944440d02155903808440c04951140c8509040e68070300c001001503003610010a007804000500002d84800700b000d80d10410040e000c090400010405244c404000d00701d85840030341c0c2201c030b0901e442c95065980102c0b0700e0040750706a2007805600c041358428069402050f40600d40800d01c04082c0890005440800c80d01d50700170343c00c03200094210304001586030001142468590039030f0800d41c44a031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 417628399 1250 417627149 417627157
    0x904110f03030421020a0801090f12020309060a0203120606131415120a0e3c010e0706080f1e090f07090507020f010e03030a09030c0c031109100b 64
    0x2801080d4140c104061603030207000392002071400384442e0350300c220f6040d415a14540503940481c03040c42041d9011075841e030144540202d03650b201d032445040342d1440d107640c21005419030781081188030030400090780383c840c80e01824105080b50000d6440720a01d08110712052802042c582c0210402c4c850407000520310b0504804079104005030386403500d8410041042c90882944121480000055806034030402c0d44203544075811083d0100050030700813031a03e44a00214041e80368001d2420484018004200c2698070ba4011401407040198205243c250a440c00e03481c080d480c58000c80010080e094001c8580c99101404c00456901450000c0103904540500c803603548101600c403000500d00241000200a8183c9035006c64a8a0f80d0b12289100a8207007240c0d1800180500071007044210014051880e0150301400554150b40e0b0302c0c6820300c000c04e0101c10036020040c1c60010100425282c030784900281d07020b1401041c03c081d0719024044d15141c084c040310b0b070001025404010320a00e12040d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 417629649 1250 417628399 417628433
    0x20705010f05070507030c05090702010e0c010f020a1505160903080a030b061608130e100e060a03021806010f050f030f071709100b010e180a15180b0904 67
    0xd020424007403408503128001c2c0c0303200600e284140407000c0203001401680e401201d40484400e44a80e4824004a00f41c50410765004401d80c00402160081c0d8064408140c4c545001c0c412110176450544600d24048041c2e03440440b100d80d03401c140311044030403c0d00342c0380d100340e9401e016180610f5580c0700c04507440713440a910101950f581c840c0010b80c0c0c0d050200d402d1628208a40d00f80c0c09005c2c2007030800e66008030f509101604e120b490000c3d486105a010610071000a40da46550350b19000501201c0b02c801008954000071149000c40181c0e18404540e001d6060000b44089614103400051700110b10303210720409103c001d006d18a901c040e10341c01c507076215a50006c0c140c0c954440c0c40003034486d1010620041e0354010700d00c2c100007841c440000d07070302c9440d40581400c0c4141118100152110b0a90100d866007000e00002100c1c04032164503a1141c02026203040041c0359401c00000340300c0c8500c00d8010a801c10f00c503e159031b2031981140105108034000b2204c01d05503090a0b030703030555004622504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 417630899 1250 417629649 417629657
    0x21005120a1d100e070503010c08062403150901120f110f1302030103020f0306010e010b0c0a020d0f0615120b1f0609030b01080714010c0222060302091006020304060507060f0c08042102070501 84
    0x4640410340041950003c40c001001c0340315141d04140cec0500740400448130b01c15018840c0c030700000074802103034101a010241c200f41c000c09111542e460700150390280412040d004009940304000544840700500070101000c24016100e50451040154a188840e07500d031090b80110014025100150000b034110344524442940e901c800c1c684843c1031400b81c007806035001803800b8048062040099010625a206001c100704402042043d4803041146001d800038002e6096041d900042040c0c010541150415101d42e6100718546800c46008505400aa00107011aa01007040103090705802d0b025040303000103171400d1414004c020003410680e507030301810442d503e20302c0c4007076448440000390a285951400c085031500064640041c14182c88101d0140c1c020900042e40b10308014004070689545a0145142c6460100210780d070f5009820301b615510380d0340c05a500f010b0b10300c0c414514210304c151110040c529090a000d031461030218240c504a50f09403258405559020a509080c1d03039007420 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 417632149 1250 417630899 417630919
    0x1710020c250b03010b0c0613051f02091903120c02010f030b22150602150406110c01050a0603030e040209030c01051c050112021005120a1d100e070503010c0806 70
    0x400010704100680c41509918000000032580384a120002c20150842c03108544070b58840131820b900380300507400c0181058000d060b0100b071455030010b0403d01d80d10805e40150600240c00e0018800403454000c80d0682030504408100b040100384045240810038203103d90070602980019025503000001c03c010903030343e50b106055035a2003512680c01100301000c2c11500110801224008094401c1d00000484407440005641e520001d2841108440c0002c0f40503d0740f6a6601c0c000030344400200e01702c80070003d0050940510003489850f02c100403401000c40c00504c0c50070040d0205081c05900c900503401000801c140c0d0b02c00050f0004554004e107041070781d9100c5464105910300c01410350031074482c2084000580303007c0391100b9460b550300847e2008514142c240080e6820310070004030080d6030783d007100010000c4842d43e00400c024000c4059a69414078800030b000d04144c50321510500c15992a000303011051001c0000e24061f103403c0c1c0007000f40d60115a0081c2540340d008128030b1007100d4510b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 417633399 1250 417632149 417632203
    0x1050d0204090b0f0709140604171c09030317060f010c0311100519050919030314010e0f1014060711031c030509010c09090f0b0a1710020c 61
    0x2e40812921a000000b26102d401d04001000e0032890503120000000c03540000440d0010444601550780c0c03d006000742d2415280000b055928614010003044500503c008000708440001c1000c0d5083ea50b80e0314000e90305e0861030040c04250b00f0b807250324120441c4404114450726100c000c41f00d000d609003400b025007902460104c034503496244040425000c1d000703035801c5480c9c00380c00c0315008015401400d104014441e80700da0890303001721854105a4050076182e2000c911803140040568080e10300403e130003208000e0200e1800b0280e0014462070741490400c001c010040c046680c018840f2426094200e00e4200400031b1440c140c160580700e90400201c41041180602e05120351060142c16151040c90100d5005003a075002c6102d1000710b800e00002641620040c401c1c2ca020b000d10340c072640c079103078149049800145410b242469013281c1d112480035082d5260b840b032030020840a4800300c01c0c90160003115003004020120b900d00e0300e005002c20b1442200103d00d154048901c0340820703041034030403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 417634649 1250 417633399 417633401
    0x30606051c09200405060603040803040209100e040309060206091c050f09030d0903051501050d0f0501021e0c07210b04080f0403060203100e1614040503071502010c1701050d0204 78
    0x2d004000e000e4082c8a400c4008006181502035a200c0c045900308610f0340e0384810f00039144412078004015100820000300186061b100b81500300709204c915441c01d03500c640c4003001d40d078030641e000d6000c038030040000c1000320ba04000c2c0b90323408000140580318082e07000c0c20080e01001654105420302c480407507e03441e100b40d01001d0710311030360700141112403c5441c0203014240314100d00043c0d91a000e13088245c04000c0c07020080e54103d80000d030081c0c55061542e04d5018003500c594108845c0355408110358071006182c49441301900c0b15440700350340c0d2610100c01d2985040e4142e4450342a41c1000c64007005421550b21000303048076002804030131159210f1030000054803580e10b04042e03540d0003190200901c43e096018501c20106040c18000244d212648120f20080444203907a1940c0b44202c2c1c81206403040300e5440306d501e42d00058a00380b545550000781088019001251088410b404180d5001d40c240039403072503001c00781440341201000420208001d0320500446002e0a9408003070780443d115 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 417635899 1250 417634649 417634661
    0x50d06052d06091f1413061209080307020f06090111030f040201050403050718060b0711010e0415120501272004090b061503010503030702040b040b150a030c030606051c 74
    0x20803861950444031000c00240d000c1d001c132040020b030002050900d0400100c1102c0b100c620404140304000d24201c003c541240101c02c0d2207510304e440c2e40b160400603604030081e50143c000d58020f09201101c1c08641850664000c00051301c5a06243c10355643c2a01c0d07008403a00000c0810702e17410f032586c4030b00041e1600d11a6501c02001481240310024410070b0b0328500c048051051201401340581c0d1b0300000a15014144029081e8094140c12804560080b00460745200d0050404108200040307052081001103500c40c03401d1114440c80142002000e104080d60514081d54080041160b601d2034103009540359001441c0100a80030094801e40042950010401c000d205100c4244580b40030000c01e0402d9a4640c0070b00000f61090b03440303502c50420b0342d05031480a0300940c1071400030303002c00020b40881541682c1050351140d1090040d29540c0034028011200c1001960340c0304018802412507a0701501101010b1400c601403048a82c0441140c034000e50480004015091b01040e01000f050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 417637149 1250 417635899 417635917
    0xb1806030c0414031c051806190302070c05060f0a0210022109010623010f0906051c0b06040602010e06070e09190b0a0f090c0212030103080a0210020703050d06052d06 73
    0xc0c51545d00000154400002d18844c5030b80c2c03060700c01d2141e401d01840042d00481150446081c44000321041a621942c0a4440c95001d0794140e0045660754002c20420b42c021808a02c4080c400039905184640400c0310114401c0162011454403078000b5184030f050903000c0107801600350740408110840310075003041e4043e00028400d6800c0c852408a215040100f843d5554040742041c0400340040740a04400c40071100d158841c1d40c034040740b6000c505218080b515070504000d5641000800d25201e050180026140e01e400011303c1c90803c6078402d140c044018200010801034104c0c0c10780079280c800c03a55400519100c00d20b032417080d43c284600b014260151141d03800c0b141113200000c82a400c002c0712001c45051060401c10011500003c0b6281c007a40c3e14070310560002080100f001030f001000900440e10140b050350140d040d40d8145400340c0e07001541c15000298041900864002c00e4441c150081c41c00301c809580c8501608064201a00709031611400310003003589200c11074503041c080710f120034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 417638399 1250 417637149 417637183
    0x1b060903060a1d0d181e06030b03070308040909110904050d050d0209041a010909021e0d0e03040605040e06120a03120b10030504060506030601121502070204060b1806030c041403 78
    0x4941d2000c005c100744215540809042e908400c00941c04241e15900108494100090780010741444029070181c5000d000094040c8174048001001c02d071008003400213000d2180c0c0202e00c034882410704401e0450401034040c400c60b080c40170721000803030008086c003142c211400c2c11500c03034030f2684410001b80130b01e035601900035040a03042280541614100e0712a40b40136241c0e55226600c5541e400e08a000d85120703480c1c10403555408068086c1c2c8140904455108201c4c04500000c1e0103402505503002a0311600101c0c00202d800d0007105424400366600103029285150324007000a505036a030a00d400000d014002021411880307400c0d6500115400f01000c1d100c020300380382080b0010000c200460707040e01c2543c03800001c1509031a021a5840c1207540c10309a407030480c02503480b181c08141501e1400c000d800e0b400c004901c01a12540100401810b51089103030f01c802544a900340d000d98001c400c1442280c1c20000c000821390100269820380382015a8070991641d21400b080c43d0a2542423406288 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 417639649 1250 417638399 417638413
    0x1401091509090c03020702010807090812070204060b160c05011404050909010b04050c0705010b0a03020d12030b130b010f020a0206030a0f06030b0c071406010302060a0e0f121b060903060a1d 83
    0x3e2074141d0001c1280c070b4803e9899540c0395441600072203d520a034021880107801c4401540d100e004841e01511810b8002480020003544d00c41480d07685900c00403c2103030795504241e104080c0004902e601e80200801c0c2400d8401504010350700040c0d1255000e224400d082e00c1021881110b000d61000c0400e0202400402003420f00d4006502150403c1e54101c2e410740c24080e0030006410000c80d587d0850340d014180782c10b162802d40c0c1b40803e110360384001000301543c414640311159284030440c440140911400601706001c5000101005d0007002040e080d54001b110400c01030321071004883d80b0010456001460906c2040e000e00548240c1c0d0003e0020000b1100b4400d040b081c48004090070383c840c0e5070510200805c010343c580c96400911002e58055002d1100100150041500f60120036009110b160803006100c0040c100c082402c04008030750317020050540000c585028040c3c0049012a21035090503450f01c0042c3e5504c2c00105840c50b440d841e40d0729013401c804048880090308000c2d505640c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 417640899 1250 417639649 417639671
    0x7050309250f050621090307050d0e040e0102030601021b04020f040e06040627050709080a0c150e0a1208040f09050604050a0e0a0f031107090605030601140109150909 73
    0x41c080c2a40a0500800e070440030005851420704119480ea00c00c40e1281c0c0d109010300f50210320495001010340c0d20b20300042002e040012024410400c1e001500d44038245c0e00105807050004072041c1040c0b041480e8810401c0c0302007a80c00080215510b0501c1004801c2041e4440214019000386c02c2c10300207204001c42c003c140c082da400c042500c910002c1c0c504009507030750303030000340324001c5501c04c80e41004c0c2750b8180c02492944540c1026a0000341414180c50130360391000c182d458601c40500c292400c03000401c00f801000200d24400300d50011700d02e410000c00700c1140001c0c806110324032039881c102040814140411070910140c4000340500030005102c241c0da613403600d02601c400c4a4481c4150301d0400095050b050318801c1140e00c1c0c560030001c12284d8050354038001400b0740c2039815424070103012110200c0e103c041007580060b04050801240c49803030007080c1454104103030482d40d01440b42010b501c400d0b0364410300080803290a8850b01044240400b02070b03603460786da41c2280418605003042021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 417642149 1250 417640899 417640963
    0xc0d0309081f0c022a0a0509070f030b04110a0809010b120709060b130b1c0f0603030206090319050d02130b070b132103020904020304061e05010e07050309 68
    0x30190b00d90700060100900b40007041361600c82d035031000d01681900000d050004040c28040314040980900079180341c03900c560000d01001d008803440c00c000307903004400904443d414002c032901600300f95414010044410020750003070141d03030606010820301ca0b00140c0750704001d411002e0241070141c8000c02d01c1c805001d10a889038413600034503800342d080c100005001c0031040100c03880582c1c040380d60752034507040c1450282154001d580904082c0c01c4036480785d150104500c10100f20810845000039168035503c0d01908241006142c0d41c15900240140c4102e482001c10700e105084580c0b81c07507030350b0b40c0265101400074040d8002c7c0000a900d200004030721488118014003070507000e500090103035995000c1c0403075000c084500044c200a5021000509e03480c003501c401c0164800c0d401e000d0700300034000780403500700d0f002214140c844a890b41e1204e00c14250741e00402c0001b40da50b42d0b0501185d0b045c0a0340101c80d41000d0049402c000c40003001a0024a081c00300006000403501444a03803010303020090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 417643399 1250 417642149 417642193
    0xc090302090c04052107120323090a062a020d0c0803030118090201140309030904020c0304030b0705161e02030f010b1c0c2105060a0509010c08090c0d030908 69
    0xc2e004255141d0403e054030305c10440146081e070307401c0040c40a98103181c81c1c882c1e45583c0c40e10403001e2026414882d6081e00001d10000c94a0440070840c1d40c4424104041024854981d88000c0a203c0c003825a08a0740071800540d26102c0303100320034400300142503c085080f021100f5006440610303161000310b003ea002000440c12100001480304084a00381100c0c0b08131607001c80b009000c10068010320000300515006968002240c90540c3d007014604404035007aa4040c0d12680d40e542c100040072b0003040340305801c6541100307c84c074140d0b042183d51000f00412924004025048903009681c600145018502c1000859130140c280c52a0f209208200c0b4081d080300c2011501c03c1510b0021280100e01142c460241c0030780103011180803600e40641a034880900115041c0c605d1640341c06400803500800c0600e001e02d10803c40080c840c81c1070070140e800c64508030403410800200070140b18001030000350954440130308032000e01c0707240028078040e104010103600c903034241c2c0920030070300028038044501c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 417644649 1250 417643399 417643409
    0xc061d15061f050306040e1006090e01060e1b091c1101020127110604030c0b03040b0a0902090a0e1501090c020c090c0f1b01050f0118050601050901030c090302090c04 73
    0x150030b07242c0326004082d4540e403011a8400184013400091242c0c605034010002e0b98505006440729401805d4514050b18070756084601010703211558928503000034030440c4000c162903610b986070741c141070200280c05c003203c2c11a03050621020810700b0140c0c4d190036200482d6407030b04c00b5040a21030607240641204c08801d1410340554a404401001117822140110003e080512241075002c269500c0d0340c41100381c0815290000c000b4030000c000240b045803101c02604da103c03040d40d2245860f292595039903800034880e00d401c500301009040140c603040324254014045010204011040440441c80c140070000f140400040020000480d00c049a1080700007460039404d691840b07944d5418404000016a9145044442007203c1008100c1e000040d00a040e0225224084420358011711070a5440c2a40c10011004a520041015444100103070f424120040c10034451840c004001910602501c00c40720306042c1c6a009600c001d6106250680c09507a00524279000c0b42040003003014235400c83d010fa = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 417645899 1250 417644649 417644659
    0xe0619021c0614010914120705030d03020c0601120f060f020d0f0605040f0b03060103030e060c06070816021605090601050903070b040303031d1b040e030a0c110d02010c061d1506 78
    0x40f901c00f54403c080c250240d8050202c20600201e5100070302100308134801c2c220712240110140816140d40030f0050075030140581d40c0c0503880f003d120000c2410000103a0260703442035a48c80c00c1d40005080240320180d100c1c0c200c1c9000070031910344040d010107446022981da4801d403421480084020030b40d40200143c030b0081c0d408106800c0400d44440c01c07902c41d41c5040e50b01d6402a030041002034444d11041c020500080c0c805410440b014401e90300d044000d0b2401e402040d0640c0410451250002e04400344901d58070081c206448820200d8603089860b0003440c1c0601608000501103900880807a101c01030b0242c11600d50980d5003c0c16181c0341c110340000c400203801c00400d1a0404c00d0040031203c40d00703940000d80813103042d050703482401c0070004c4e50068005e6114842d41c03e002c001803002d4002c0c105280c5401c02004c202d40b40580380c056862541c284203280b180c45042c0940d900422040d203103030340600c1c006002c84013014207800d07104203036119403c1c0d8880c5030402181c2c50030b42c02a1902460301512 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 417647149 1250 417645899 417645929
    0x1a1207030312021b0f0f012019030e0d0e010f05040e07110f0304081b04020403020a121106030a0507110f0706030e010b06030103051f020f0f071a0c070201120e0619021c06 75
    0x4001c123a10211115241e51418049094500c2203651006003483c141d00740000e601c09082040f0782000c52800b12a00030448500351050f6958000c4520072147c80a031502c28685418038002d80e5000c90050910000c02c000001c041c003001c4000c01189040129100c01c503a251940d0340c021560f00c0c0050112110b00340241e01100c0080d05081c000d4030b058983c000c010390321541c24205503001c0d28104c0b020a46203904011540101c40d140c02c402140540504100450340b40350181c1c0140c0740c01102d080040140c0d20040040380456408940202074410928011420744405440980900803205080d82d000328000000000c0000000b10014003120b00c01440d105841020380c00e100320700a070251440760318001c2107241b4050010a0090040500c02d121310755580b101401a80c0c81c0c5030003142c2203001d1250001d404000d40d81c01030126414000152010300140c3c4504440d0ba40718040070b01a1580c4840c007804446c4050030036011390f059490010041c1c0840040b40d120034029000034410f5520801b130400c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 417648399 1250 417647149 417647171
    0x60605040b121f29030103120809012003061f1218150e10090b040326010602010e191a040c15020606040c020a110112020d1a1207030312021b0f0f01 65
    0x1040e03034100e0f6088460800158230f0f07034505440309140180029400d5684002e101062880a141e03d0141a03079142501d450b442c2c0901405054660700c8120009034900c02420146180c2c4020806451000b221000c201c001c183c8240c0f92090b0100d050082803c1440ba19070b0711030031819807051400c100e140e422107500c42d0000c80040f00700d4442d51006005003011600040100e03002e842e0b60304607030b04440b0000c1d985074240c0121502c11403080e044000141d44400c2c0c01020140104070038880413000c03801114510000342d5500018a110140d05816940c0400019050042c0b922880000300740041d550001100d0114000352101c0048900c50320032483c0c19099043d041c80020000d0816034040888100484000c0064401c861092190701381240c00304a1030540760100d019942e2810aa4221a040d200070b19007008450305444481c035025500c0b81c0c3c0c08201190307015840104040010034016524814204072020750703002c66440c3c20940c0b02c2d4440c0c061190800007400407041e6042070013000030751000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 417649649 1250 417648399 417648479
    0x5040605010f1a090d02221a0a030f02010302070213061d15010c020a050406030c03020a08010209100503040303180308040c0b0306030c150c120301030501060605040b121f 75
    0x2900075a044603084400d11899082e03040f0041829000c0200030240300e10840d40018420f003220b440b01046c94000410400c072016044c000c102c60b15100805100c0300c014014081015118103200281200c0c582014076003d59019074111400d032038024110311168100712940c80003411581c4154002c00799800c1c0021303d1101105000390194070400504078800e8070080046421101c2000c040c0d0b40700522103070004550b60b80d881440011032281c540821100c0ca14010000a50300c00e6102a01d2a40100403980c856611a45241810034407418460b45907180c50404a00600d0f128030110324446c0201a403405164101031303242c0c8203a12400d08031104039124cc225801c42d000607240d0390b407d9441188440b056260910b0030420701d010788030b074040c24140d00c10401c0e460646c000150b111410000801401445030038020380002e04280c4c2082840c00d4988040601140320301555484840740c0c44011441507240030711540020307841c1e0715041080369140e425022000d450340710400b80501700c0152416207210300c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 417650899 1250 417649649 417649679
    0x15020f0304380f0405070b0307120605060405010503130f080403150513020a12030315120c080316080304020d0605091f050402030c01180b0c07060306081b060906090d05010504060501 80
    0x890b90500c04142c40302607000e41202800340003140c02e070092020109075418420051423141507950b48601199080c0450030044030f40c6604000c1c01001c0c104018400ca981003001c5a80003002061901d1080c400d6040880d8240c60303c0000514041c070002c2c00009019103000203000e03580c0102c07820481c2e6100c501038000200040075000b501700400303000030403110003001400038170a070080c00c01003250011284000c4003000950800d13610310176100d181c503090140300d80212025144081c010b42c070f803210302d10910141c40200c600007014500300000150440d00c03003442c0340d070302c40303911070342c10712603814003034101900c4a00d0141d41c0b8503240c40c410380701c103d01202c500840380281e4000d8003401c0402c8040b00110f03a0031100810741000d40c074040748001002403204000f020080b0408000d400010300b04031005068030a198490031a9034059909200e040d82c50103a0450050822a20159101c0c0130a012440c0c0307006141d6050f03404106031031034000348078040d08030342e1003580300d0002000343d40c0c0c0314251920702e107036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 417652149 1250 417650899 417650993
    0x3030c0305071b03030c12090c2402060a0c050c0d120506030a02090f0c0403140a060609020f030a091b0b030a1b050a080915091b0a060c15020f0304 65
    0xc0c2c05240342d0210303005c1d51001c1058035491030941a45031481e840e03002940e0b01040210b60250340a01d0400103501d152a0152900c034501e0304100005140b264025a181c0c0b019104520307081d540c800742c1750903502400490700e20000c40d100b80d03001d00b074103e01c000d001c4540742542003012509260001d04580380103c1c044012300e0703004107040c207203440300302c8050050140140000c003503440400001c000304e00e1035241703405a03000c0c040080800509074505082600e0555005829050050000c41103024241040d80d92246c1040c06c0024488542e04000610001c810500d15248061981c0411344e00c403aa4002c1d84906a0380341c0334454041c2003080446030b201001103e2000440610402204a100c1da41481e0060041c0c81180e0a141681000e0070101406440c41d6800740e00100e40c0b03825010010b103410b079000d0703c1220310303c2301c152500c180604098031341c01c4001e002c1450028040344d0b051450f4107540421105404040d203034a0540780c08980740300003040c003038145c2112121000e4101404290421221 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 417653399 1250 417652149 417652187
    0x6030d020d08040c1703180a050f0609040912030903020c0f0f19030506150306070e061e1b03130e1e040609051507090501020c180705070f03030c030507 67
    0xc2007003401102c0c0d111001d00103d54001001d240050850102c09201d4a0680160041c642d901d9006000b03400390341c0b8901115015074660740040183e944e803070000144502c1c041d0f401c150303602c1d21000018010216030000a00320341c0e010f1140c404059240e403104080c54803035000c44401601c6c41d0200300c0004a035102c807a034000300314811440765007440f44201e440c0c440d00300e0611051586a940c0c2c40e080c140101d4648541004c20b0b2061006031404001d05a00403400c0c3c1840124209a5000300b500c03131284a4852282c00010f0048040c040d034030b40c04540710604814409811484c0120b010b07601e1790b115036055540221003035004203a41aa010001d4002c000041a0f0800c3c401c5102e049145008014407c0c0d82d81c1750740d5140707100880c409104500300c0300700800c03601000d4902840007811402690700154110350111021100944074100311410b040b0981e03020954507690320504486178030504400400d108100b14a010805406810a21880303800c0d0f1003d010340d6517800c01c1250b2001030550218808 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 417654649 1250 417653399 417653413
    0x50a0219021b0a03122109050a02011e0e01050a0203090d0804030c060809070909020f10082a16050c0d03110c011416111c0203010c05071a102c06030d02 67
    0x244d0207000150b0880800c0b11080620405400011b0b0031242c4a4000b56034036088600701108542c0d002c22200c00c042c03415040307180205240c00c0e00914020b008004075050103400245030003064001c1095401c090002802c1d02c0609510f407404400ea80c00c00d100480b4090104100440c07914020a007251003070b103141c0000d0012901d05202500540700c140003d81c1c1050049442132190740311034001c51030111071601e400100c1e01300110395002c4180c2141c0007041500f9110102051700c03614200310341f02602c0c04c0c04d05036040400707420900d003040320400545a02101c2c101c2c1c0c403c200358102c91001030440010090700c0758440058015a407400040343c03072041c1d041b420001a01c080c03d9113021030000c40e0041c0000038a410b0348201280503202d40d039610601010326000c2c44011841c2c02d001c0e01c0d1421000313152103414034080780d07030f00e41000c015201000e04015008000401c0124452990300041600e0b40c04140c610000041804404c10f9903030714908034021040006005050016500703408845550041c0f8030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 417655899 1250 417654649 417654683
    0x506010c111305011e150f05030a020408060412020d0206040b1305120c15060303120c0307030e0a1a09061b0f0c120c0d080105030709050a0219021b0a03 67
    0x80200400780e03035400b14019030907082c003031680d116041c007801c01400307580c101d001c003041c00b4168041240d004604c20000b41c040c90249990003000114001c4150a1250f00e17511210702c410068002c540041e403291064034204000d01c0811000600c08561a0302070b02d511303a07140d90040342c42d52001c035805842d65034920040740303204a40503034041555003d03070161810030020010b1010143d01400790003a10f54812041c41942c40b02c10b00f40d03250448012030081d0326007081181d40303032440c8000030300545001201100203504540070307821a80d0214040c005485a4804e07a10f071021811216003510130401c00b15000003490b884000540e103005211041e140e41d000b51b0340f5032064600e43d002c1e0300c820041603401d110f402d00d03503202003144407032480d0581070356a15203404400c3c1e2850113540f544008100042d20780100b041e82c038085034010945400403004961642c403540c801c406445220a07030300e12440902c0300424a141d0102d8916540e0b4541c2202800640e600010001c0c002101e02000d0f18484c141080c15075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 417657149 1250 417655899 417655913
    0x1401050901050c0102090a03291506160b1003110d0213020c120c060114010c03120b01140c15060d11040903090509041109010506160f080f0a030f0f0506010c 69
    0x1500720707000c009850b1000c201c011038181c00301030b0300131600e0994030f041a031320401500301c01711000109c40e0003091a52601e560642808405404c075217000d88000100c2140c00030700780c400c4550841d04400740c281603003030405654464007020310040c0c410f4140310810411518140305040310442e0000c1401c1840d10522070101c000f54000700034548c05215604079070251001c028041c14021401d0009005c03658034184443c170160890402036410030044940040c0041d42040c4054108848404002800403800340166044016408402090700300828031003405900042c109480e640c00503450021602c07045d040c411110300e45040103144000100c83c055503030600d9484400d14034001c0c035200342034640d5007003c507401000c1030b6803d85151705220308a07201401d05044c0d5500402c019108246040b404507100000c200343e0440c0100961850348181d010700c0120410b4a5042c022a8071899580e0000d480180003080000c011844a41c18001514600c00c5a40306443c45024103071a101403603005a5151a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 417658399 1250 417657149 417657157
    0x117010518091e03130503010b090403050f370801060c060b0d0f0c0e0f070903080306030708010e070513050105060a21091220030f091203120709140105090105 70
    0x100c8a108080f108240030340c020101c03480341440c1401450b83c07035484201c103008500c5907400850003a0b0400710f03240d00c20780381c0411480d84a0740502e0100e0320f80079507207410300461140300c2c2441d0341da160f00f4a4003083c401c40c400860044240403138000c001c12141d90130903102d6940074440c0c100841c00720800d00f0702042e55504203c185405c001c1550040007910303902e024080d250b100e0243c850240d48441880200c0200c00115000340f1086200d00c032510b000710b0010f11054180c040184035503008008540b003600c0c100b00c4540a000e030040207000c42100c8625080d0b460a603407045c07071300c4ad819811141c40078000910400f03040c2c56010b0002458a0050a8182c402d0480c1e6106e40400724150214001c01341b129100721700f40e40b44140ba40049141245400a0515600b5001420122080d21460000d050000103c980c8207103500001c030b455155642c0007a0011260190a106d40d00002031b1150750044407209040c0301c2c0c1c90545400c4038548c1c40d9100c01150126903401703180805c1c810005140d1940c003c5010f4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 417659649 1250 417658399 417658411
    0x30e04390f030c0c0203060103060e0708060412031a15180d0206041710110a0f39050303010305070f12080f0304060209060a030e0607020f0606090c071205090117010518 74
    0x304c1c5010344643c082491700d5804d91096802558440c2d42c0482e8480a11100c0c0c01040c900b0300070700040c10542c90720303d4072441d1440010180b6a0b24206401140c0101e4010708401d00000c0c4a040025040140030840390b0090784822186102c520501da0f00c0e00d003482d00110069000340038182802d085c607640d01c00c1266640c0d000000c910581c940c9418004050207440101303c2c0c41c0c084c0c41d131205120740e00542038162002c8828184000005002464038403005c041c07503041004007505030900700080a007103511031100800340c0240000400401409800580c0f08211000d0900c424922580c03240c03001c000e00307a4084010b0034481c040002c00300b0207000380f0195810501030038005140aa610780040e80079030041003010040b070740300c3e204044410f03020701590358031000034005803020824007420395860307030700092416104100030004501e810301c460003a261724642c814410034025840c02c03c040d055801010080b80010000300d00c0b6800c3e6190024164101c072809481030303d5006d05036a051094500c0207000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 417660899 1250 417659649 417659657
    0x307240905030f011b090e190608010e0a140d0503150316030501053306180307060c1101050703120b010c06150f12020f0d030e04390f030c 61
    0x4042450b660601580c90a0074500c00002000000d10583d45481100d8040c18000d02000a00400140d580050803503404006400f10214030510400c20100070b184a030440030940d8a0800d20810610002803000d03c868005c8081c46070020300303c0303241c5550b004040c41d41e4002407001e101248040408200500842c0c0c001805c0c4c07500304240c071009c0e060005141d030054400703070744031410700900d004c10001d031061081895040210241c40d40ca0300300300148080714035a01901001808407012510b444441e545c1d1138005041e1101c265540000500f0401241401c0d602d01e03d58440e05a01503014008580c000c541c1502c40d10080440c581c0c011006012088510f130501904002c400000352203881240020300421181c21105400e000d0750707202c0d01c3d4043c1c12101109082d2600c09002d0303520211800030400b070448603807000340c07042d25003150301f4651401c1117600103040202000c0c207803010041000c500e40c84204010b0204038a0504a010403206602481c0801d41664007058014407a401c881070ac0002824 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 417662149 1250 417660899 417660917
    0x2906090142030204060305180325061b09151707050c0d081f0506090f0a0f0602070e0c13060f02160b0c160609060804140102030703050603010605030724 67
    0x1806818440c030403007840340020750000d030901450b505485803d40003030000d08000d04c00d8a0704120155688600050340321000441c0c0305101841140316500160b0543c000818044843c50081550740d950300030319200041290f80c42c0200d6400c4e00c000340e400441c00103a940b03890003e141c2c4800b654001000d400c2c0c1007044010000705420007420845c1144024140d980c0c00c4141c44c1c031120140c11a0559403442400b00010f8000300b002d80d581c0790a0300c1500300c08507604141074003603400068401055030700c400c4492865850000f005500454550304941015010b0307050390369400360202451140543d00c0c810301d00c0d4030009006092081c0032003180420382d0300450300510b15007040700c180180c59502201c1d02110008045a070200c2c24041929541e400030b181148850506401900d003009901800e400c04c02a0f100240c1402000141c0311601200f002c001c640d242450180100640421140180a036080c4000000c0504001514804a44187d2a50082075041c0300160302d94102902c0071000300110f5003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 417663399 1250 417662149 417662249
    0x50c0f0f0d0b09151f05190219050606010807030506100e120109110a050109030312090c0f06020c0108010b0c07060e0619020a0c090203010e130f29060901 68
    0x300e02d280241a0600e051a0349681300c810020124800401c0492940381c0a2541c0c00c40742d0840d05884089510003140c081000c0d06107401c07844d0900b40f0031101d508a11448082c01072007004903c45018280aa8490000d580c4803907041c1d0a60340b0640b141034001c80c8141c0f280ba440c504c600d0301d5030121140107140b1210081426040740c00d641044009941c08804140008203501d008034a080c01002e0a00300b5078001e61440d01c0141c0003800c03030780022403066110f200750020040a076901d07001a000112001c80362a4a424000756524441241d10707010031200000840c0014440d820f071400c10310660f0003050158203090040350581604111203400c140c00348150008526001c81110610829500030309080e2006c2c184042d02145c9507101200b03c0d84104014010341849008442e400244e50148003a03a006918098850100140015194180c0c0b01035042c07006030b0503001110041c40901600380c164542000f00412140d082c0314000010b000c2c400c0f640c0541c0b40410b40404141801c0e241401010012 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 417664649 1250 417663399 417663409
    0x1b0b01180e0109050312100b0a030c12150b070c091b0f08091c020f070e010501140301050904140f01050906160305090703061505061c050c0f0f0d0b 65
    0x380c008410389800d5500414065806201e50821508100000c0c41101500c4c1c640e02e803207119071003251200c0c610010001d41c61402d20140b9100921407400245d5444c1600c003001401010f14002243c0003448000d061200280e050141040f009000f102400900385401c0c0701c0109548078610442d49043d544900040c0b200d414411901203d11101c4840d0345200115402001104405000d8040c003420b00305024000e04005500c1103000150b01c41c4e02801004650160b140c100051044411485a8900400c45140c5006041d04981003030701c965110f030040703034911070700c500090044507007003c0f00f000001c0225020602031910032000106403225018020000390946000700d0320209a03030f0000090081080d00008004d58416591030200510b0504c195419202c02c0b041c40040c1a07940c0710003800442548064264000b842d00504550351140e03404640c0d5075203002d6280001c843c525010026051003141c2c41210b040303030003251805141107000d070502401e54208080003a05070303580d1150401e4030703114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 417665899 1250 417664649 417664651
    0xe06100f0905040912030b0d08030c070317040507031103030c031c021b150a0e0a3801080d110a0303020703020705040c0309050c0a060f051602091f0e0c09011b0b 71
    0x164044c107441c8100403174080c00752240d901c0046d00031100d180c4503101042084050329007001c84060202c0c2d0350442c0d41001c4910341c40480111500480100500c010060009040021644130f25800d0b104a05410f0401d070700c80c00b0302d01d05010290010052003c1544014000005028004c0303001410101045880544500d584400f10702c1d41c0c0c441c1d04c118034950b84180d07580f0340c0044a0b810900281a04403903050b00c504142d00700a0603030800c1028110b83c15245203203421890f0141c280c24a0011482c6030040a1000031300c22102e4500681d00c000a010b0304c200b510401800c0080002d01307890b5030382d41c2c0440095110510075401c5001d4801302050300e9440e4000e4260320141581d0100f2039010908045080c480c030142c078144102c000a008000b81c0b43c1001c8400000259418400c2d1200080040c1408141c045580254482000c03400c1080240c0c1c100340307141c5551031001303006c245181c940d151421180020b4900034081c050900000070158424142c01c041201d184079100788858540e9070b080d0103d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 417667149 1250 417665899 417665903
    0x5040c1505030f060613140f1c11030c010207061101111305120606011b0f0c030605180708100e010212090d1805090a090503071202030a03060e06100f09050409 70
    0x400003d009060011507600c44c1c200c81c00700d03030b054600041d9010700e4107101480e110303014511200544c40241e5548100b030645401c400503001b24a03415611032218441d2004d44011107018942c02100d0070103080000f1645c100420680041164505150080e15041e4451116608a40d03c0c0c001c00320340074540c00e0180c000a10392009040f401802c11040042490941d098015554882d508205090fa4000d548601040407007503054990036103418007800d103031031a14003d03040c0241200c0c00400c00c01c0d1948141d00c2a03880092450010145c001b02d1754071002c4a2040d405250300a1813681444040c0d81d1001c40c1e205105400180380450803079103d00c0c4520115172001d078580064110340c2005030404900100f0a0f800400000c46a08100000d0b0405501400244425686a400e0303020400100300301d039151a01305400c035035582c0722417500959980c04829460002400d003040022a175001c00f101c0b6020303a000a10f1042407031460b00c4215600d0b000e00020300e08000cd18000010603448521508100314 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 417668399 1250 417667149 417667157
    0x405030d0e0c090703020304030f050c1023060907140306010e12062d160201060b1209011a0f240c06041e02010903080906040b0c0102070b010602030c1005040c15 71
    0x40c46010008091002441300007031500400420000aa00141d40d141800042c2803554580ea10400054541944104100c041e245004041f0f4071440418032a9042013003c07042d00321107951001c0a004041030306860300c001081d244040c100d5030344e90500c0076590201040c50b0040d90a5075500c005010303089403122440c1180c02030014403001c0c148882c00040ca1182e0080481034401c0d0050705440d107007030000c0402e0500c2c642c0742e19404166200390040402030656150184d02c40101c14140301620000340c0e2158829840c10343da42000b0011480181444000241628100381c0f0310b00078000c010050008080c060900161a0328443c02081c02505104051030010004c0307151518050040c40c428411070340000f070301390f2078090041c3ea001e1982421b4030b07440202540c0710105036020900790300664200290a41010a2011000c1015805000003c0c00b4000b403940c20399070707110705913240d1103001e15040031a041031044207025020398000d41c0c0c2081c410012516a9640d410f103442e407046613410080005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 417669649 1250 417668399 417668413
    0x902090a051504151a19020f0c030a031b0c17100b030708060105130f023f01150207030b0a0624050a0e12070807091a0906090405030d0e 60
    0x501080b8956a5840c0540f010041c0c0f241e0400354000d064528450041000580d004820b030410068050b115060358902121a4a202000303010303459601031003191a07944500075103d80c0c071785000100300c407007140c04d42c4564210900e0103d402201c1c0030624000d803030240d400d1800003280a910405a05c045c07032490043d240542207403422409480306980c00c9071180d48010014808680c0110310385044500440e04031042e0107003030900601802c00e58200140c860310110700c05019060060f00000b0800300c1c0000c16400da07030402080100196501404285990104010b0041114050020a581d180c2d4011541c0317255681d035400b032410b007003195503940c00d90702c9590030082105100301740302000c0080c5000e00c4440e0400c00d0018082d019402c0c0340c2c001c10000340c520701100d4503401a113820180d0501f0540e10a941c680102554400c3c00b4810307254150302c0e092081510550044007040d11450040103001183c540d4010010080c0d030203041940d490200f00314240781d8440f0380c8594081d00c40e0400160102e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 417670899 1250 417669649 417669661
    0x1090c06030515190509090709090f020a081605011101141f08030406021216021315080f0304050f15040e01030627020909030f0a030b1017010e06040902090a05 70
    0x8005140006805070101c01030a00300d40500042444c103440040c0c541000755510b1504491170000f90b07a11440b48545007400460500c80e1b068099006c5078001e480e441121a40c2d1a0010758070b44020100c4400c85005503010300107503200d03120203002005030100201e8900c081010070b0048040035280e190203201c5039858a21803503522032442e802080303800c02035810a8a407160181d2a54454460004940c000281d10190b002c00413107441c6000350003810300e805c01218644004001d05d07184050190301c41c044a0001900d07078000070b1007915903001001560816142c403045c085030b82032010365107a00071000c10101424600b0a80075100411039440304c0ea96a502d1428803108482111140d41100e501504800c9000803090003800140e95064840100994820545600f907020354000c0b48140340700080c079407000c1d0381d15400c0140c003850220b801010080d240d100685105d84c0c5650902c1011101038010043d1003039000c01d0552140c8060400700d4402c0c040d0b40080c0107000100c8804000301d55650601039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 417672149 1250 417670899 417670921
    0x15160507060801050603070806130c02010509150603030901120b0d030507060509030717310501031406011707020705031207060c03140c0706021b0c09130803071101090c060305 77
    0x4028801402c00c021a541800f01080c0e491100620704418481f980000c1409500ca0f9a032481342c0d0b801c0303607208214103204c11000030301a0906039006100c1d40b103600e10314085510940c01d00b5024010003401945400c24150046d92a107400944840b00706541e980490340940b203450788800210710075a00c4070303030720340c03440c40c0140440328083c282a426610500c540000202d00e51840c4c0c3c81c0c0c0a060702d506031280e07902000003400005407814451031407042c01008028030500008102a07803000d8a0a0042007882140c03600360050441e10365000410030210441c030805410380752a082099403060360129030b15800401e05d0a009074400d03500e11000007071860188030340b038410075400d01d01c1850f0500180c400c0380d140502c00e180c05441a0f24424000607903004011586d4100e42c0464121703012000341ca64601506510751110402d0a8052109140007030a04141c442c03012895a0307001e0756490458442080031544103001d003040002c6996201e01e00c40200d10303540d42c44002004c495402092500e0300101a007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 417673399 1250 417672149 417672163
    0x40e0906040b0c1e0c030d06030c090b09040209060405040f050a050d0314151009090905060105010e060309030301031e1b0906060f1202091504081b0f090f06151605 72
    0xc6000e8109111018040d03840d00760340b0f0f1010f084138048075225001c00d8407542c103501c941c9440030301d00b92a10302c002080000200c120000c40c1d14810003044030b4038003441405411141207500a61054642002620b14580b550000e41c0143c0200201d80c001b90745540e40354580410b0075000d44c0d03a64044013100c01e415616003d000000301d00042c1c0c00c0214100514021303030614104d00081d11070f01c80700042030a054881c6190340c00400c00310000380b2074000d0504111303480344000e01a40780012611580c103015401c100c41201d0003200d44e64000c6107182e00c1c43e2180840344c00c50451460301e1010810940010425203130002c0b510384a04d0b5900da01c49407514112108a0304c0d150f002d8030a100c00c0900b80c003031240d00000440064110010702603662104040050301940658104010410740413401192011001030224507080e403150780359042610480400c43c60061090031940d00104140000c1c0140010203480b60304140060031071020340e006404071131020f401452403028100b2480c1c8400060040400c104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 417674649 1250 417673399 417673411
    0x903090406090603030c060f0b150d05010603060e2d0f0901050601020f0a0b060409060e0d020105060f060f0a140c0a0203070e100e150d03052101150f05040e0906040b 73
    0x2000014513541c0c0280901d03d034058043c0070b083e5078402c0d804141c4011b0b0009050000c0041a600c030040c803030a00c4040a410170101500350618000010800c68001c0c8522000e0b261003c941c00e2407079643c2c14002159449801c4008000c4034003101260391460204003070b9000b64010041641d0600e08076450500311100148428115401100c1d207032034010010031091103813034001d00929519075030b08001c80d018041a0384001c00b040c0c9000f95020701d04601103000b150048a95009021030344440702000030b46448405001c1e8003140422820048500f041d00520050860303040601c0c0042c14250440042e800a9000f00002e4000d586104110302e0240401c0c1c02801058030b403184d8600700500840405102401682c0340304000c0008100c0c80c1500c0c8200b01d1180c100100030f03921358400e91500a040f5007010301c124000400031103100f0a1345002580150580d02102c0c1c200505040c179810031205c0980c20314190081c400c0402004c98a850314010300307845103004000a00641c01c02e45046100ea240041c64 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 417675899 1250 417674649 417674651
    0x403060f0504260f07021c0302060103151104120f02090a020406090603050f042a180b030c01210e06010311120604030f082d070210020901050904021b0303090309040609 74
    0x3083d20309802c0501511144500310381c003151181824404160071580030403014001c1c003100c41c0108201a800034050341030f82e203e5034940c000e01004c94005130035255480300d031b00e03402c050030300060020303295aa103940940c2d4021041072002481e40d8001c58010030341500c2e000c86503600010203115480d0480468401817036603107020000d51514072190f10030040e010f44024039407180d030000c3d1180d00c6100440d840003040003150380c0003d0b0782e480340e403840b0103d091000c03180010f0801c07900d030b005842d0114400b4070350401070711544401d41002242100f90703070507081d40c0000c803a83c6444440200760304000c164080c0d40708107103100c1102400c00c20403800c43c000b911803001c02d9002601b040b002950006004410b000320341000701c6143c4408800d0b00d90003071a02900d0700200440100c40203240c90244400d030140c0d01e55002e91b40303142c8100e0700d80307401c0c0d00c15022401c0c0400c008000f0072015042903801040c90303451981d107890505840e41c80aa0542e4000c0c1c902c081142c4c8041040300c4545054440c0300001e0041c010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 417677149 1250 417675899 417675953
    0x150c030e030d0507020d032703031d030a03230703020f06100f06050306030109120c0b0901060b0f070c050d0b0f1e04020405060a0510110106090606050403170403060f0504 75
    0x38054481d1102c002c0c002d42e000c80040c410140074082141d41700f207120a00c2003044c88c03e140c21914030b401602c1300307130001b0b14101c6140b90080321550030310a441e1805800f402000c0320607142500d04540c4010103000404520302c0d4040200da0703e4010700b1400f482507010b08041d00d21003001510340340028009940d9186070103001c03c411943d2041400445a150810343e0b16a907407403001900600e11200017505581085c83d2010420764402140c140749031081c03140b42c280da12501c4499007200c10070700811015080812070a1a080041c402805000b40310700c80c10700142d03071560081450900070075812540c0301e1481003882440203940c00c0b659441300d42610f02200a441d4612841800140035002030701039640c881c0803ca054554070450b201a10000d0843c11070a284810010120a049070707800090754039100f8003040c00c020078000c0c3c504403059541c0d00b42c00c03d170441d240c0c4c000c0383c1c050004076901c04200f00030001c0094983d0181d840000d1840c1c000090507c0c040c100403d103600110311728820382c0f0103c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 417678399 1250 417677149 417677173
    0x40e21070312020405030a03080406090b0c0901030e0a0c060e0f040c0801150c02010e041109090412030b030f07061404090c05040504060b0309120904060302060705100e06070c060213150c030e03 85
    0x1031f1030f404d40360700361604140d41d88a90400100801a441e005050300784c4070381c00c1100c0c44001d04002c02419400783d07020041024007850392a2a40c101c103d00421104261904010781842050750078030121000b40b020a09405600014007243c40400d00385000c18441e43c0100920b0051580380c9910145a050103440c0c0c1e001036000030141408a030101d8401e5a940d1291490740140c0d4003038845c2c84074007420b0b03d200740c10030b0b06100003949003030802d000001c0d00b8010025014280490f207400040e4800c0c3c01440c0560500030180e4401881200340800d401c0140300028280d802800760000010003511002c1d9075604010074041580d145422107071030418200107101c2400000980d17114802115020140c5421020300060050907003030380b0281d03200350042200410711101240b206802c0002e00810005404c41140b003540761401142d120300400c0a40d41c804010403000e4004040c100780d05501d8141aa407100c041080c5403100170240800035040d40b40000c1050b8001001d00c8903850110000c009800b410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 417679649 1250 417678399 417678403
    0x170a03080f0a0914160603090503030415020c03030a090506010b0a050909090106080a0602090a0f0609060c05010b04091112070b07060b0406051c060c0815040e2107031202040503 78
    0xc0d104001a6807003000242d0844103d501100c0110382c0b0410300c1c0403004619001603601c4000d00364554604051100024186000388149610903510801843c256607803902d844084010b0111300c0401c154003040780240c002000d00c015442004216000260f1082905042e0300d0014147c118080c512020003d803041e081e00301064551003d8200d070140c00940c1c52a051030301501c0c89610030300d41441030f9024082001405d801034514910709030388a04015940d1184040781c0c0341c02e0f00c14000801c21310401800304511402d901074200f0301450000c144601c940000c1070480f0300402007501c034030700c013080240114a003003454040c1041d1544001c011039030910801c004940b10390070004002075500c1c0400303031240c1c880c0e8002070000d0000400c0c094015441300754403c121860240308440c078520385402c1045041c022007031140100c010448120010805109000040c100400d404030b20b8420307074100811789000100d080e20510b001e41c4559032195901e280103041c4000020707a244040340180014031a903100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 417680899 1250 417679649 417679651
    0x1b0613150e041e18020a0b03180303010f0303020c010e150901110d030c110a03090335180a030f0605100e07031d030901210f0213170a0308 61
    0x80803480c2024410350800076120780c0811116140c0081c10082d42c0c0844050801c110381c004440e4080602050300c0302485070314201e00702e2500a40c070030890101440408447c070b01a40c0d01c8800d6215a0004000255040b45550800d030710280000050300e10520030142e06204141d078a035020300b8094050b041e1000000c154901c203809440c10850041000324260384603200e01a008400b20b001d950a80c2a5514001c0280c5911107406010981000b0803c2010744009514005140c25964180846007507a9800100f050008610709041e91140d10030f802502e030b440d94131080340ea2683c0106903a60315a0302a011000f0300c0d0029140700c0c8000d030b082003012521094401c0c14171a4403100009013036071816080c0d103480c00346400c0142004400380c200071200d030701540001c40e0700001095020800018030300080ea179125420b801b5000885031941c40d8000b24540040c0360161100b50301c08240800504000812600140c00007828840341040070080013140e40020300395065a5009040407110984018006140c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 417682149 1250 417680899 417680909
    0xf011809050c130f05010206060108072307150605091006090302060a0c0c0f0e0f06060d110412030309021e030303040803040606030807050307120e130f0216051b0613 73
    0x5240c500090b021102e4204403040701010402c0754a08a07160368030b41c24000054020700d400341c865032011824660081403414881d002c86c0c0c2d540003502025504891200300043e1a40241000511010b00022605d0b010850b05a504000c0003801da0f250200f0000c0c00c090103010481050786562f014801c082d0300940c0c86054072740540780d042d51080700410480e99000d00060141c400300c2091808540303a440d11402c0341c100e0360459030341c603e241c42c4c00c00030200284050b15500d61103c010051070048030427540140c00d4492902c0c29450505540d021003108044081d10220002555039001c0000c5142c000c4805800c1071002c0d0f074030b007210488200403035620320000d40054120f000210019042200c103801c000e010f141d01221003034a4540d141b400070b5480c0c10044044806101d000c48080c81035100d106030b032102038001028107446920103440c080c020208a4488951940c08000b0001012480c8440014951068000300b0504090f0700600c1c070480c0228001c2c0780b1400e01044150050401065050240d603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 417683399 1250 417682149 417682151
    0x9100b010c06052205100c0540060302070311010501050d08160609060b0906090f070302072f01180509011401020a05010f050a060e0105060f0a050c120403020f011809 73
    0x41c0f20070360a800c4005070000002c4081c1c1390000305104000c00071401c083d201400a5060084c01c1440c0c4042e00d1600603e040d44255103c0c1021480d4444000341c1c0801a07021071400518050303050099000c1501195080440442e800269000406502c000c04520808a18000300300300c2d41008005030264401c0d200142000c030000c18001720180d4607000400c10355a11107001c001208140c03621101a100c802001031195080c540081d95038180001843c2c861819420442886d50706c0700c2d41a8000d401140e000d482342c00225a140504c09101020303c80300801d80c2c50f1240080344030b10001800152a201c80d002c540300d031020200459104c0d4028541503641071314050f4401003000d00100c1c0781020601000c1d00c2c540c00c110012101a90340ea010030b0290030b0304102402800e44501009144140c280320326038000070100810030407202800090300171041c1c7c1d4030780286410400000103180c0550310101030000c01c0d0005080085160144000200c1503080c00c011401c441c01100c03082c0701c0c104601c150303001c0e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 417684649 1250 417683399 417683401
    0xb0f190605090303130f0f05030102070b01031403161b061806030b010512070c05010e1504120c1b0609093c02040f181103070309022709100b010c0605 66
    0xa43d414010b450101d035600303843e21605035484001c1a40343c2d4040c4141c0c5101c0540e200041002d08040c0216010aa0800d503250100c0e407a503500da00390300400b01c890b2025800305026100400002c008903421240c082c5014003106002c1e4a04524221960340c001428441001c2c00c088076490244841c808840d0300f420000b40511110006a5962060b0000e0300d03070000854080041b029009030a6640e40c601650082182e030140c61091540c0700850030802c5409200c801c00100000c1c040720f02281e031140c59180c541600d1886940d4035400703c0c000705030402e800c4070501042c048280e108000360001c01000c102881403444408012481000c4580d0040030104401c00c21214280c4001352280d624010761170440d070396991001e41c0c0b2203020f49070041c1b00030105a4860480304150900a030301d603056410f191103155440c0e6541c02e40080030080822a00a0104d0000c02e9224100160b948001e1420f12880342080c41c10040d010f040c05050703030301d007a82d4070701d0b1036211101079030f00c0342d80d810b80c0982c05000041e003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 417685899 1250 417684649 417684667
    0x105071e05070b0a05090706090b0f0c070b12042d021e0a080d030e03040e0105220c03060e090607021b03010b28060e030307020907030f0507030b0f190605 68
    0x6944200b00020b060080003505001060b609036021501c00c032280401d83e48110740f01c420441701c0328030a10403045111014400311945410080040078903107101002c4410b21582c42e660750b02c1c02e8100c40165440c840c02d4604110610450401c03400000e50040b041c0b016010740310804017000031440c40081e0003595a41c0e0074811001501ca41d2070117100340100000c00c099502c42d103696603900d80c00042d03400641413142c0118054400400d581c1035a05032900030354168200018480b07900c034200d0940c0c1a8001d101035200c0c03441e13128455002c40c0c032038503980444e0450800c00354184011000e0421105039001a040010440d0301246500484880c03640d080c1e2800a1500000d0140444165065120072103524030480c0c1c0c1f5141e401c1055005003074804903400380e07541c0742c1610003c111840c5c040c1c00d50800c0106c05c0c01803400e540d13403070b6001040d4100003a207a0003404130703030045840486200b404207540b02c44e10225868a0740d0205250241107488420700c060340e001000d4511214413400d01400400310704020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 417687149 1250 417685899 417685907
    0xc0206070b0103080319050c030106050c160306050f010b090f040b030111040807260c01120f0f0f050c09031e0309060708090103111809100f08010b03010b030105071e 73
    0xd0382041d808005542c590810290540c419211007915005412030700b0707100c1e01107004040c8140401c61070642168030300b8009442c0344c2c0c04038803580351501a0b40c21300200c054042e034050f0091070140c14001034902d0070301001c800c11201a0814182e03100c0601a0641640c4d42001c402100c520903640451f2252110021038050248480c1101511b200418041095100014050210b40900c04544036402002c4440303640010351168441d01500905402c40c03c035406540b04189000c8070900c0000c200000041c401c080303c40c0c0960b6840610f0316150000c03203a440764000c05402240c43d22180e854910359800007961088200030100e41d000b003945000360710040c148282d407400403000e404a1380c2c901035880d104000d5803101d90303454082841c203c1c4801d4900041c2d01511051804101401c0101034100100200f01c40300902c01d950343c42c0e0909010070080052034890f00100203940010800d220305000f014250744044000300d020360300d420708220301b46030302804290030b01d0900b460101000f820400115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 417688399 1250 417687149 417687157
    0x402091f0f0303050903010c0f0c082206030c020c0102160306050603030d0926070f1511160b1503060c03070c05031813090b0703111606020901080c13060c0206 70
    0xa100c030180e00310000181030308a001012081002c40c02045078450080054400c0c920710348441000032903e005450002f0002c1005200780d56461316009002c103000c8844a40303281140d000107000036110008200c1c295010080d201d06904240054040445410000c800c490381904c4003822580c0c89502145041c2ca061080f581441d01d0550240110302032802c0001c000e441034441c0620710003100840e805002c60f0103084d6109554400b24801506180d601e40078500340041d03481ca61025640e80c0d10780e0200c04041c00800c4410101642d0100015070ac0c02c015030740120091065440d24009685848999001320740301c0d030300c456040c43c9030742c581c2c45006040701c044944403001429803000140100d102c0e0440e0740c440340c1da16021a00480c82c080407400c50003d4900d10400240054041f03400b24240c40e0286d04003848004c13a0403502420b006000c51082c0e500f1010540580e0400c0d80040d80394140e590120340d4a038001c0c2d121a41c0351034001d01e80d4000d008080704d0321418007046100d0102c0000c40d5160170883d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 417689649 1250 417688399 417688409
    0x91519110a0e03101107060c20240121170309030304120c050606011b0b0c091002120304060c0306181a0d03090e04050f060906010f09050402091f 64
    0x10a88607205418003400384801c90700524400e200d2007241003203000c141d00030705198001040b410f0b400c041c201d54841010f89201160681403018a00500e140d500f165840031242000c107500030141e80100780c062280301c010048410703a00c030140c4c0005100d180d01c400041c20a0b00c140c3c0354500512050340c00d04026a03000c4017001c2018100c0002400300c0004000003941c0154019004040104017901060306c42c2d00070250014004d40243c80002c4813580120000180c2d140400d0495008296030340e24640d621204540aa0340c0302004500d010460821040c959400003440c00200b820100000a1100500005100030182c42e19281c102511912079000740c4020450004107001d5024070b846084054501501c1d00800244040108041c602d0300c89258802642c051711940d2600b0b00305440d03c3c4142c9002001510700b403152000881c25100100b0485105010110182289505004000503074101c10392000410350304000501001d07a0722090302c5900a085080090401070646500c50724810710340d408 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 417690899 1250 417689649 417689681
    0xf300302160509040f0209100503010e01090506060a050303031b07021002011415060904020c030c0d0c0308010602060c0a030b01030e03041806361514010206091519 72
    0x111042640000d02408200d05210030a5042521034042c44400075007203401414090120240030090304100342d8450300140d0102200800d81d440d50701003825105031955034485d41e9503401800d01440014407081d80c200008a8000030024a02000682d8a000c040c0c0014a44541002c480c0080b5010000702d814055000d0481042c036480301e84003900820002034010681e51000300000c104081158031303603511040040c601820300c0b0620092000035003003c0d0380709280b880300700409106000d08229601103201c0e1540c400140d01154078004081c4801030b40860700390b501c080107000541c90748909880f500c00711860000340d071403a1140101c01806d0980c04444031804000380101c0e0805155444001514680105000d074986d21105a640d050b4800c040c0308443e4446a400742c0c00d1164015815244841c1c000040b440403d90328110410b00901ea009171007080c1980001560303540c05020041d4485020400341042404514401d040e8407001440c43d00700648604010003820540d80c003048988a1200c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 417692149 1250 417690899 417690989
    0x30d0f09180e06250e0d0f1b080114070f02031c0b3c120303070306090e01020c0a080306032509060b0705120711090403020a060509070f 60
    0x101d4401016201c0000702a40104000541c81a00f040d1954001140a0090085618065004540d0300120074490b5500032160160040404c503c41c0385d84150a01560740d01c0d408050317040201080d410750340e00c141240c0e4101080d58190020008907503138456841d0605013640d05800740101e0843c8640d43c2020400610705070000c2120b4400c2d0700c50032140409658100c01d144650340c9140848080040800c0d0036410340f1070b800100040c40701c0419107510080d01019003107480f01181400c58104568076030019995400400100c0301d80d0042c0000d81030f00030021498070f0070884820b503e43c0066403015022403400400700d48262020040c20180400642504030203001c2e07200c0a120040181c420f044600342005400700f549000c0d1011540820307401310050214540e80d1080b0300c03040d005101c0a0781c006c0e07000203460700647c07560426648600d100350b000d030540d0000c0f45843c00172508082c0034000c1a03801038005010704c00d425446030042d038903003003143d0a11540440254514400310360301c4c41c1003501c100c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 417693399 1250 417692149 417692189
    0x2040b1810080d141911100212010b0f07260408060117010204060f0825020d12060506070201050706021b0709141302191e0f050303030105030d0f09 65
    0x5200c00041d60b40c02c00c01d88038460740507501107030b0b025021031804298039010802d00d001e81c41c43c03018441000d0b080d0f04155803017000768008141005a900c40000320140c0020f4000c56910280d0f800d030b0301400419084604102c841201c0488900404400418641001c440d0342c141300039918041c590310307400b010461b548035101c11003140c0307ca800f8030450742c114041c603410f811550070600070385040e107110b5691942e80401d8440e0131101848080c14074001040045403900320040103207200082c0d43d803907030000d12034690100301c0203044811103036080748194907005041c00030f6030302c5504881505809282154540006083c100700034842d160718039400c2040c00146203013840000c6004800c841445604102c02031260729200c46800003111800c2c9100c080083c558010b02e04075140c0912200c8088100b48bc03a038035130318109146881d02d00c400001181d812000c010440d508250040600b02c1030f4042c41c02c552401c0040b82d0740f0060440003c040c48840c46520340c080340b08220900007884034030203c900c442409 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 417694649 1250 417693399 417693421
    0x612230a0b040506030309100c080c0709240602030316090f0306060e0a0509070501080406140f0603010e010b0f010311160305030403110105090a2d0524040f02040b18 73
    0x601e020500503420640000c401c5e160102c240c40c213118000d48002e1206503262400c81c4c10000d0484100c81d20441405403249075601040094003030900381c080000d0402c03076181000007064400c94108249106084103001440e40030041c0d0303070000c540b5607036440da00006000986e000c0300c1a402c000d040c1715004e0310002c01d100403600140200c1e288400c0ca91020f0302d071194a00c003a2001202c08080355800004104030951050b413409605c41d010b010005442400ca15500648100580303000711b12119080074000907240a03c0b8071042d48449100810202c41d00302c01003502c0200317040b64181416074605900600180d10f0b02120020802408000380e410060300d005131246c1c205840c15400514245050160058140b00d20740c0114440001000c0c42c080c4c0b59151a1310040310101c0144420015910b10741840700282450758032482200541402c00700f015401340d812200381e580c401d141c0300d46024000424001e00b00e1445c6190107440105003c40b0b0440415448001241c1003601402603004100c1e0311502 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 417695899 1250 417694649 417694661
    0x30e030d110a0813080a0c170c0a031412150d0206070c06090902040506032e080a05010c03020f161b06120c03051b07111c0302160612230a 61
    0x450f0b1100905074a541030020140c403032464000707140d02e60402c490f44200740a0303e1501082485419219100001d2150042c0f4940240301007140c1644411034000825406c0642c200c22500601011801d0814482914500034409172866001e20013181c002c06d855207502c071300a80c5c40c5030040e04980c0e032000035240005100400c0d01c503800006648560202e080c0d500303402120100d65006020f10304645500e0600c129110002e0318054021505c0c4240c10386079003030251208002d207219000f51141c0c01301c50a0440c00e603620301c800b5008044c070400112000e19582d00640b410b800400e41c01041b4900d440ca0440007011485040d4954125007100010314039a02095042000081d42014404200089400d60503280156881c3c60b042c3c6600302d0902c2101e00940180040701e001d6450710401110180206015015036a903c090f1185580b414800707154040100b90328079142c0d0306040c20354510b01a00100344100d6403841c003008640340e0320400c030f154000110a0009038440c044c03102d00f60500c41c0740e60b4001c00c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 417697149 1250 417695899 417695917
    0x3140a080408030c010c0906090b03190c02100f0621050708030d020304110406060203040b070807061803110c010806060a11070602070614030f0f04020a1d01090506030303070906030e030d11 83
    0x800e0135400a1b40c5445004c02100311500c0f621000303541d0342001d080c10000d820003000c503500100032035140c14828800340503600c02c2c480302e50094a400314240300450150352a141000c101e40d410071104015526845603881d2203030402a529000480d02c034681141070100325801a070951001140e848080f407450380c0154040c0d40304420010683c0e030902d05200560b4000c0c418500940c00c24001000ba4101c07000040401901c1850b40c5440c0c0030040d9101c404071b41210540001200301c48040b2010180c00552040e0300115800c010440000c0480008189400040c0018040d8070040f4801503054040c0003012040140e90040d41d04554407103000941d00d10183c410340f00025050328100321a2100c4404036401a0380c6500018a140d03246038401007001d001401c1203030090041030002544040003c80c044d00c0d0142c0d00c8a003d195403401b10bd1070166032025104611907007040041c080300c0c1e0341000c0c5030001c503040c070300303020943c420340000a500b18001c04140001303c0d41010003509039100c3d50310003405003031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 417698399 1250 417697149 417697151
    0x1009050c011b15020a0507050a0602041d01030b1b0d0c020a0309090612060c090e0c0c24040b0a15030803090d03020c0a0605191a0108090c03030403140a080408030c01 73
    0xc4000b0036090b000542000002e040d401d1408580c40401c40c440e0010100c0300c0b65810020305e44407803946c0301ca1400060f110305980641c0d002c94140b00da0b41c4440f5106a0030300da444400f04c0c495055490f0000312100c06440c40c494030858007140c4038816011016150444089242080801e40f000006915440e0300c2d0400c4001580c04040030421020074401d50099844c25210f035200100d01da5641c9000b021400880d038103200c01c10900090640ca1064400d02c602c0c282c1210540320031201030218138050601034451161568a05c00c00d036810722401e18030340e000341c03c00b01d00c11240d111000500021f10113201d2255441c180b4071000300a01041900950040015004542c041c20000c14110700301c0c040d501380341c01c1c03e41182d11004041005a04030380c0e044036541d40140c2c82100800c0d00581110003034005140c002403084460300f0b496070007280050780704c09240e000c0c101d01c2c29684c0000340c5074072445c0001020400140c980c405160010030039240c806501144060f62a034450300c1c15a0381c1d421002451240d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 417699649 1250 417698399 417698417
    0x3060902090705030912090612010f030309080601140904061d0a0308090f0607050a03140114030c19090c0201140f160e0918030c0703080c010b0913060e1009050c01 72
    0x443e00c030b9012203118017410805030070b1250021a4801840e80090700240c2d001c0001d025002c1c15082c00e4003410b0080c200910554000d514518029000f04004d501424041d00105d004100d6501c041c0b500680701e41d0211403c50701c4c2d6545142403c0184040711020440d0356400080c051420000549540054003d0700c3340700ca581e80b0440c1003903440b01c1301c69103a0000e800031000305171014000d00c050b02684029040115410054a000d140c041c8026809040e0740e20b07850415084a0406000f218030b604016288803140000c9401c414600d20b01c0e41c801c0b4001c0c19995041811118030070745c4024a0700701038141440c2d081c1400c816091460406681c1040340041c0804144030040c015048603181400140c4000f80700d6682158028081d07681c0c0071441d002d0300040140e03403403a110a108101c082c1d0702c40c4c8101e50709e0b1b80b244a0310700d003141c0308414200d0283c800c1c0703000e01200a9a442c01e6000c5903600c0000400c008000601035810301254415443e10329042078091800c02c1408140841d40e0031083ea20b8040d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 417700899 1250 417699649 417699661
    0x3060a050a0f0b0310032a060e090103020616050601030c05030d0f080402090a1112090c03010b01140322060504063b070b041d0901090206031302190306090209 70
    0xc240d00c00d20802c981d04107152001c003c001201c5000c0c1d07901c6503601c25600001c603505d8a071b401e420101d00f080034002d51010100d502c188000901e1140c05440240303814846543d4500101381034400600019204000115441221801c40e805940c2865400b2050743c500396542d20f064206c0048900405e8442d0050b61591202c9500c10210415506419612261682c03102e80a0000044020740184109502c5503012084106810010121040384003034104240c43c0c00c516040c1012408034503a8400c1c2d06140002a80c1e82e030140890f00d090300c2c81007000b5074a407502c0703000b44024070340e0082c450b588506002c00c0c48103000090344100e215901400c000e2100c00d01f6100c06981880303003061421040090056a46152024082c143e07000030700c0c15080702c07202912075401d130307450303030000e5003c51100d11101c50981c141150b1018025000b0700200003e214000c4240d0000d070090000034103c610a0b20350449203030966442d0b03001c80e40203146044c0c06021182d01d03824194007400f000c586c00d0340140480004500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 417702149 1250 417700899 417700909
    0x406080a05070603020c12030906090c0906221b0906020c030105011d130519060b0d030906050a09050409030305041b0b030a021602042408031804021b1203060a05 71
    0x403280e0322002030080075041540a80007904116088a400c0c8207901d281400c0c0c0d445030300294096942d900082035607191080440e032070110440c5446019000b50414000345071901500c0c2c2030400740c501c80c0f084200b03047c241c03008000d00d40c400c0b502444081242950b10841d410201143c1598020ba0035541e2516200f41031600740c620030b01c81c0300300040078800100c2d1424a40300c0010f8024002c8030007a4401d0f6200e03214a860a145c400b01e0000c1c25613452847c0e400c2001d94031640c0340401081d15040d02061442d1005001c080d01803148400340300b0001286614a07205d040041c010300401041000201c0090070010024141141c040308c00d0b0b800d40c8100261082003101e00011603010103507151841e1707142071405019400030803c180a000c040003805005030303114000c03903c1c2c80c5420700000b000b20342e010189600e4980c00d0b51010070550402c12084000000100200304c8041041d02c0140e51800d8601e845052000c2160081115000342c2808591000516008500406080b0340c444c038000d031240104a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 417703399 1250 417702149 417702163
    0xc050d0e060d090312060e160c0503090f0a030b1311040207120e0f0402160209010b0c03030114060904020a020f060a1413020f100c0210030b010c0312110a03020702040608 75
    0x2070307407016040c04128081002a042040c0c82c611a00d820341c690360320001d40701c040e12072603000034003a81c004108110414015119601c8103084900e082d12048206c0d450781912840b03080c800e68040c3c0340f150402542130300c80c0e0440c1030041d6401001c158283c50f02130040c000d0b0403410501103c1600028040c01d60504c5e2a000752023805800c01c0c075640400d005040203847c4039600350940c03038000c640d40c54985010740da503101800489141400c0d90011a1300d61042004012050b0040403005005024480300d0b26000415a4155141d008040060101140c0040d040380101c0301d980c2c1d40640009960100700f0360215100b0210300414040b42d46a86401c00c90006a560307600035014205038840c00900b43c120100551052540050038032000c968200000c141036510780a800b1003ca4170710900345046080c0004081c00907042e52601300a11038456000034901d05480f0390140800c0604054074100307400d50360214851619102600c0e0307803000e80c034078080c01030740000720141d10551030301c80d0005019401064071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 417704649 1250 417703399 417703427
    0x9060203030f091011040e0604230a02270405101d0a020706090b01081005221103031801020609030705060118061a0711120706050d0209040c0c050d 65
    0x99401c564030380d0741d221150a80145440c0c650320421070b41000402c40c2d44184091003103c0c40940d95940e08100481880d00006020b40703010341d140542129900c400650b4144a40e13000540d1031120341c4480f40c4141c042d018440c807036008049074060742c401c4407620086403d42c0c40b00079a000d0000f55541440003280d99610711502c01c0b808911070941a165400204a40d4000c006d02001130424042c0c1d1200c10403a045200c04680301898000184400c10702000204234004101409101d07a2800001504d10030038003c0002480100d90700f1078104200741c4c00f110034400000681107907115105034a0b10076040c0001c5600038003500626000c11104070022045504283c0c01c20300070318569282a0340846040289109401c0c10703981d920002c5060080e80e0180e01c0040020020681c13943d40c8c0e801d1540354007910452180c07140d2080c4440780207900f0082031010448540f404d1039a151451580308401a126074850250f201e4074042d0003006864200d068041901e010314101c0b040303014607543c2650202b04070034213 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 417705899 1250 417704649 417704653
    0x14010305040818150d1d070f0501080405102a020a050d210f0621030c120309021305090d0f08011202120d02070503010b04060e010b0306040603080f0304060c090602 72
    0x4408060083c480e20f8014031140900003968400034041d034202d0680041188880c240d4917040d0040c2c4030041c0351004018280d410000d0011186081b6404036030020900c070b458140b0101000107800e00c00140500c80144004001c00d104a0220070008070030829210a135009110800f4082c81c00c2e07603c00100e202004e0b9102c0014402d803605903509582e0704100520300e440640e0340344421605241580144d5251010100300450060300b403861168020320940c1e038103d04840040c00c0d02c004a0352040002c0907494102c03424130107c002d044002c9000d801c8028010b5040030300815031500c08245944580d100d5095030090303440c2c001310710400700c030f000620f1480d03000081c02080040c400001d0600c6241d0100c3d10040008258551071002c45042101100105c009030f00264010007180c20300b0302560000d040b044800300071003403c044100c9043c95042c00350000640000c40040c2103502d513503000078061a00f02c020246c0343d42148002c0c4c3d040d40c0c0100c9044504078241541d041100e0300443d02001a903c01e500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 417707149 1250 417705899 417705907
    0x106050a1a0d111b0607030b101d040f02070807020a06090506040902160c1d0702030c1f020708030f04030914090402040e011b02101104050303040b0c0309031006140103050408 77
    0x19054001d0b02c0032000f944074074001000401c80044c0c18222010690380a5005826149041440503080b143e4606015004080400810b241c3e0b41d401848441c2005860041c5000c2c079981e43c0104000389a40104010010b10016220003404403072405005c8c2680b00f1204016180c3d16003c040301e40840b28480c00c0d07042142400107100030300080c4c014208075840410030000c01d50413612141b0005440390310000700e0901085000708640e075100d5600d5848040f0380002c2d4a0010301104042e50303001b0708c0038031031000320300481d988041402075011a2040358001c0c00e020703182e00344115482200f0b402950210003140b08682c1c00114a041101410700320740d0300402d0f0103a1603442c0d8082c00003600c46c02c40166181c1d50f80da11610304038911100750000740725117030340241031000c0e56080d0341e002c89000c0d4803024459170040c00108055540001210700f80c1e1601e411240d100c4007074180b07480c954041c1c070420641c18011000d102c2050903495205904640958800b40708802d4158015400ca42080c0c80c040c0140c10208 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 417708399 1250 417707149 417707167
    0x70303020a15110f030f090d0f2706030203010503160602190f0f080309160305070314151914060f19050a030f0b010f0f15090909050106050a1a 63
    0x151101c8108000300780c0c0800c3d401c2250103038403400d504c00d004003102800003105029600800c03510140d80720b08650b001707000341c0032250005450f070300c4031714002c10030800c00e4582e804110081c00078483d0703002842c142c03103261140c03181c5020b8042c0d0001d0195038081d120380403980e1085a000d81051080300d07090780103840b08030029503081070761924804e0191008541c0c04031071400540540b6100344841d0040041c2c07603c07804c1c440e80c01350038295403050901a03002d03100010700100d440419694104c0382c4c0043c14001c410361010100d411319401e0700b0840070103207118040101c82c1241c50042c1c02d051280483c02c03c42400c01c450150344400c2c05903600c1d070b04080462a0b17010141056490100c1c2e4030216107403141120740d1a40040d074181001d4104440382018131000c1d600304008028024003603e80c0c075100e802401d00f003400300301c030580040c803901c590195401d840b5100c83c1d005541c004054800c82906002d080c0f9141442400380203184a21805506003c40c00940b41035001040700607100c0c82c15240e4603021140d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 417709649 1250 417708399 417708413
    0x192a03050a090503030d06050f06071a060103090b1014100e0f010302040b1c0e0d080a0903050702210f0c0a090905010e0a030c0c0506030c0d1d0f0304090b03070303020a 74
    0x1d565140900050300340100321540c040029245a60310410b0200b442400d0600381b0400b40340b50070300c050280005000420000c1c2e80d102100f017807510000301b01c07111681c03080012400b4058640000d0080000201030000070074021802c44142c0d4060740c01c11380201c3c220400e104030940f0000349840058039203a004003851500303041d42400400149005800d2980b201c000341415030000840d180d8100c40c075620307403003980302600400801811201c00760419161855018145410082845104c41e9075013551804040c02001a01c0e00d031500606010055100c18092020352003811486c01d40c41d01c00c052032900704000000d03003540403650140c0b02402c0c1c680b0300100c50000c2c120300c6008a4065484480302800c1d8601005000101ca00a507951584402c9504101c100407140390003281c000c01040081100c800b09074011189000e404d104000740d94031045141c640b00c01101c000c9030700f15000c1d40034040d03542540000500152451024201704601d0b01000701030391500c60303120050250f00455407401c007281d40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 417710899 1250 417709649 417709657
    0x528110f060406030213050607050c091003050106030c06020c091501140d050a02070c090207030801030f060e060106021b37090f02041d041104051b192a0305 69
    0x80944940c0d550a00840021160340003604400c002a5000ca1044800c2c140f2841d40c40040c0400e9038aa440c0040b00c2d02d42c0c3c7c1c1c07285200d60349103000d40250408503980b91007070801880110703005070080000030386078607007444012440e01c107050041c0f10303c8500850501c0c21200150040315518100806c141100d0015240707081100700c2d0890641003440a45411030035801503034400c800801006a694580d4980310b0100300e5590052181c0f280b041c0701060009030403009180c1134942204040e49203504500d441005840d10440c1c13403805002d1701000181c801e0f0002010261600f000304100d41071410001400031012140703a81c0d441104080161000c10840501c031590036101c00030003040015100e407141e20940e4800101186c0712640010108000d0070901555558085503459150440c1070540702c01580e09a079084a070701c982d03078900c081000b120320080314402a4441c040203544903940d96446021020101c07044a010480600040680c1c0e00000d441030000f100c04050420440b101e42c50484030f52308 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 417712149 1250 417710899 417710933
    0x616180603112107110f030f0315130614060703020a02060f12070503090d080708070e0f040606121802060706020706090c171b150310030606120528 65
    0xc000c0040e41140d02103010f18054074210110300c4240d5080c1480c0c01031103484032044008190304000e101c008440408030459514110701c861580d140c3d2171b084407503845035801240c00e580c00440900c0c5003848400f030b600709404aa0400c40700310411034004062142c0b511039148001d0060b041101d0b160018540180503119511406241c582071035000318035449035031010744008001c030b50007104100d40614100106000c92125140c00e0009040c0401d028240f2440941540e0511283e035150000d00d03112491001080440200b041c0b0400d0780c0c9030300140503040442115040329007000c2000b60b04940c001580d442e0b16901070080d80c505181e9465070f60003900000c10858296458801020200714040d0540000d45280900581841e00c800011450111044c490010079812841d0b10041969088100c04546642401440d6a40d644040011010703069410041c0b01914008001c1051170b03040d01c200c0c031640c1c4038908440144103040740100040c2401c1d2542d052041002d0307802c0c03001403030107210880085 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 417713399 1250 417712149 417712181
    0x30705090c09030109150507020c1804050a0510091103030901050a08090109080406080610020708030f180303160c0e25030921030b220c090b0c0616180603 68
    0x110b12000039007502d41c0c0c10f40949440611100e240b541d1300e4103100311500054140000c040c201d0046001c100403200085080d444807024400180030f02c80e0520180c001d03140d000082c2c0e4402468051881c1c000d05000b003007580c21425113501c140440c10000f0498461101c16150f03a405e02e1003007a000c035103404000b802d001c499500da00d0850300044000c07000d0009041241c88000c2640340840034802101c1504000d0411548040400c2142d40404001c43d0046822a21615500e60802c00c4440007204880e041c0c0790144800906111850301140c1540c00d007500c150044080581d580c0d00030303020480e0990702d00030100c0d090180c42480720310408403100708122a08000c140360722542c80f041100f4103200c40388001d82c9024030100c404c41e40c0c948552603a20381c0440ba4603e01110380003c4c20440c4800001c004511542d512103903440b28002d4151000803c10b010b0782568803c880b44041d03890344025203c000c100001001d8803010b04d030042911146143d03000d03054000062400d40110003800002c2c2e00c00b0303110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 417714649 1250 417713399 417713407
    0x180307030f03020307020f04020a080f07170906010303110f030a030c141b0607210c090b0d0603060605100507060b0a0f08061b03040803010e071b1103010509010b030705090c 76
    0x2454028101074010300a030051912182d4500620041e00c0035581094402c030701c1000780c05911600900d2090300a10710303d80d110f01d641d0b40e220040d2410085690845400d070924010480c09040004400d03042e82d120b56510000c0c2c0e64000c0b041c0703a071144004507141e5135400c20b10032000c1581c481d0303022225156441c60000c3e011aa05080c02113035a004000c03004016540000382c0e0503440701000b010b50401007618001d24841e0038a5912080c0315610f0012007511500ca02100140380c0c403c0140300c0c00703060143d01f1181c0e251400725455004041c9440101c0d095070425000081c103140600e400c4070001c015803140380c6440300b42d030390f82c00c024110f010210344d001102a0340440d84000c000d00d14409030001c4d000501140c101060344480054441000c4030a2007030030020407000603521011340f03044501c5100d50445940b0f4412090701d51003062074401c402114000443d03824043d440b054000010005d5000b0007d48c0c0303608032440d09131072101c9070752a019841030070100030901381180780c0d542c007400c042003460170 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 417715899 1250 417714649 417714653
    0xf080403091a0d1d0307060207024b0d020108100e010f06140918070c0f061a0114041a07060e01150608190903031b0201150b0f18030703 60
    0x2c90100150020003002000c1079001d1031040318030804071a5012404010801d0000d0500d283c5c1e02d1088140040c0425001309080c421901c034070719000c0b012041d01c603081845080c3c80101c0030254800e225081e2504000c2c148900004041000120115070058210b0102560640055414060107880307200315014685000804030188107a55020f41903042007254640d10700034004050344481d8215452041e020010002c40381d0b0760181c901c00c103034054a1a00d18680d40c52100b03403902010b0950140c044102e522000c2c04209a503801060940704045450540300407031001140c50b0311421181c0042240d00300028011480103103969183c01560210039441c00002e87c0e44c0c1000d548000c018040b03241c0d180c849400319003040e084070030041d00c400c0ca8020020720b007401c3c3e1400010012880860f004d581e6400341018180720b6002140591400403442e1000e2040c003800038002c0503808040c085d58100c0400105241c0300d124222014030b44118940b508001c0300f503204883c041d62404506906210316500000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 417717149 1250 417715899 417715919
    0x8011406070b0c0a090617060d0302070801022a010e060403030b040905150406060605030702120304080706020313030210020a0519021603030302120709050d0314130f03051209010f08040309 83
    0x303c5441c5030301000f62075000c81070024042e0b8032942c106109010000b02c1c82104601c00061150707000a0840e01c040d910369460a05034201041d80d0001c1134254000a55000001c40b40b5100c00c2c0f071200442e1000c1d21441d4204c0d081401c944682c0c0e210303160342c1c00030f5000c200032034807079003090803541002800001d081d030390380d0384051030304282d4580580e6411201c0200002d101c00c0d80b041100819250500c5451032418203030003504da10b88070b000400010004004201801240001c1d20300d803d82c000350841d42d905164088803580c07090b2800c124010320901c45410500c4c0c03d24020b0380c0518100d52a2281402c010011111104022409510444c0308411124000d0701c003200c0c0103001075001c2d0701c006a5400c54000080b00d00c820003001c0d6414001050820011500d440381c442c0076940c1c141c6044220003000b2200061203206203261041c0c44001002c000c204509001300181c03c891048084800c2483c012410b518503006050709107010404c4002500c651a0083e000d90383d0083c07003031805e8038105440b091603203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 417718399 1250 417717149 417717151
    0xd0204030501051e01050d031107170a060b042706020903060705040906060c03080c030901060306020a0906020c04090803061311120f0603300d0203010e0f0c03060108011406070b 78
    0x80c903143c0d110720620a00403180c0401288103104410759924a41c107040c08035141130040c040c0101002035580c0103181840301400140054035000c000003840d8080d00a03007070790300d0004820583c0c8503450010716403d40d02c0c280c03003070b45210358040111807961200a44020711034601041e065840e15000c014450440c0e805104042c03041e1504d44401d070322907081070002c0d01200c96982180b8240b05c1c0c089070750b0011a82005107158002c000c041c4460782ca690300c0700050b0144c20590b1009140c40e00100724203c0c481c1d000701c80725040c0c030210340c01c0749d4642d1044000c1105884203504040d210f43d100300003040c00c3d8100080003000e2034400360030208604132118020b01c2c865010820a1841e05a64001d10401708000405035070000c1045008102c000c210001c808a0340b01c010309144455003004580c100c0c0391098105131110a00e4541086480b907a44803000002003a08031103006035170f202c00b0005402030030a9026207008940603510200d46070700380b500803018140d0b50702440d0742c04136083c05179100140500c80c6007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 417719649 1250 417718399 417718403
    0x318030504081504080304082b02031f0b0f0903031c020a030e03070209180705041a03060108070308070204020a0507050102070c21170310150e0a050414070c06020d020403 75
    0x240e5640c40c6084001424074840351114820b802d0200c050001144680040c2e07500300d904a000195242c6a0462440586402c0003100742c4000300c40701c054602181e90380c00b55202d8140e1b218100001e0a60003140c10080b42ca5001d0100000000d02894000a4039100940300003030b40a400ca0b032070860321140d0351650100325860700000b00d0700014900c1b503081e490701032070b01880c101d24011030408a10b0350001e0344c2004000c160403910b00d00190b60740c1003240f040048400810b00034104020809218104480c5400c280e840d96019100b100000200c81c3c4000036603a0072030350420800c0303041c61156400c000107540241c41207000c000d03080c00b40001184082c401032902a200f60300c400e0b00b1614040305089010420300300c1c2c1001000340002d0001180c001107102c0d042c0b03288a12416529918100d940751000900c0c0c00c290a0200d03001c4000c41c1858003c40e0f0030b03802c0d900172500e6030801a541c60811040d40c06e4000b507511101c00f00004154094003500d018000c0910070745015080c813640c0210007040340c200d0f900c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 417720899 1250 417719649 417719657
    0x601031401110d0c09060302040b030402120c190905071704080306010320070501050c1c020f1308060f06060a0f0503060a03060c0c0204140112031103160b0f0f0105030d0f031803 78
    0x10007860681040d030045c000c10a0b410b0641c107040c640340d49450300e0b0100610107400b600f0009121503004109224142d041c1c04e0040600304000919030b0050b5810005005a0724a54070341000305202c03600500042d041201406d02c2c450a5a95035961442907420190405051544490754004900303841c6c482c806c409203a603007219441d601c45007011400d503031014224142c01c02d410846c032060680d221580708007209031036001503a07035011420350144500c240c0410a890301c12108002c568000040781c600c0c064050001820129100c01d41003000500c140c802150104029440030350f001382c0900040d552041c00141003880701586d82d1102e6007a40d6400c160324000803030846015046107000e114908ae031101c020344200d031941c109514003507401100301c03014050042c19a08841248010404c070740c8034010512030315402c102e00340340c00c1e90810019649402c01d0005040051402c414080c3c001e8121280200106086000305406036100300040001d201016219003450191004c45401800e03c6482035803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 417722149 1250 417720899 417720911
    0x2010915051f03020a0605070305090a15020706020606030d08090a0c03110a06090b070237231f03020c0f0c030c01050711010e04060918110d050601031401110d 70
    0x404801c8803404a1082d10000b0000341003440583c854003000300558804d418402e6403004030b820240d030580280c0c91101e62000304404003103240d40000c908941c0c1c0f02d8164084030308035078481100703130f8464400b1110590140c1c4a41040c140e02d504c80c9205640040c81e80041d60b0840b40981c45031006200c16420580741030400e01d540c0c4505007008143e010080145207022884e02d414200c204640d885501d0000c0c0c4540311800351044078268503a444018054104200c02c042c502c1000d0502078100c0b035201d000c40d015041c680403c601d00c01598182c0b001d0f00c008210a1452140f0002c140c11140061201d508055003444003214a070010800e103a40c0070b40e040001c0c440e42000303104043ca01011018241d04010f014414200054601600140564002d0802006400602000c1002814030754400620141020003101103280107202000819014421100280d641c02040c04865440a40002d115a0101c801040490184c010345140c951103040085004405008a401540c0000c41140c05444d40c0340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 417723399 1250 417722149 417722161
    0x703030b0d0b070212091e0102010b0307081f1413030509030106090e0f0114070e01051e030618160c0501060f0f090f0606050316020f010203281802060a0201091505 72
    0x3c819032031800024000c2c80e00728060046003404100c040e00c60051080d01420780c1f916070003900400005000036045510140e65005103903501c10780e10441c0074103000501c0040c06801000e00030305003002c418001909060301c9011983c2c0912110b45010790801c0b105200e160400d580c20b0165000030f00d200300000c2040c4666024081c240b4503c0030341c640007a131406d0703c4502c050904800c610340c0500182040981c0010203c010b13101d034803900d10040c0f209410000440c510080002c040c6000e10343c2665803295005c0e840c030f11800b40c2c0000395000ec0c1500542e01401314a9440743d88414450381c0b1480002c61400c0d5078101d1041803403020740001e065000e240001740100c3c102440749414014400c0c5007480001e240903405020361102401d0741d88007401d0001c04500042c001c0004036258a04100210f60301e2810b0b1440b464903800702007a0380450089500704004a9150303000c0e4907080d22040b040780060208982c04c2203daa403100e0340c0c050941d5240e01010001c607000205000b090900894081a04d107010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 417724649 1250 417723399 417723403
    0x6050a0504020322151103070f030605030c30030901111b060901030e2a06030c040902070215040303081e0f0703021804060311010e0108070c06020703030b0d0b0702 72
    0x390440c0d80a1071041c4100311807485181600c0d012008030885102c1000f4060400032500c1d001d42100d00c425a0400f8200d081680c2e9020045224521650f58812802d450100c11030a0791400e01c10f040c3d05500c502c281d1645442e008420101c002d03c56551451040d584c69440d582104494801c48900e8002240110295800000030b8080c01010f0003c0c00e0000c0024482e00e000400d1308200b2800741c50082005151070340668095050308000e902100d50f100701514403061315400001f1481c803100d41481000005080c880107403401417190b00491400c00d81045030805c001c1d002000c0990780449984410316001c0018002840514007940d18503c10385002c4ca04410280e02d0b125031080d1110001c803c000d01d141102020a8118500d4030b00540c7d11225010f40f05060004800c50651007444c01c0000410403a030804500800c05081e2200d600c850310b603c00554074060111081008140010040c000040c007030340c01450003034407070300b0002a80b8650801041c000c0d44c00210032a403402d056420f0107100f50701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 417725899 1250 417724649 417724669
    0x3071407060206010e0108120702060f032809050c0d06110304031215080c010806042705120903060a09080f030103080d1109010e06250b0703060b041d0621010605 71
    0x2061710a0091545028107a564030b405440c2c101040d01408525602190f413040115514034154141d840c0d282c2c24644e0300a081040d40401422420030040665080b0041a0064072086074100c0068804000c0341d806229528070103c004440881d40c8000c5100c5008645015501450080c2c4d58140ba654030343c60584216001b4800308034079500b400000300000d000024158500b04401e1130401e200d80c681002190103800400701c41481c42002e000681e4150071132684059644c0c0c020800c48031a00392a1807009242d104100c041078140e0007820004840c07a0399508010f400510841c00e00340f42c400741c1c884840d0190001e0300100c039010b04c00241c03181045000c0c052449504014040c8900e80214030001822680d10050f401c1d00074400443c140780409010f20301d0740c810491030102d04200a0140c80c10702018007080b036888006c03c1c076004021808001080c10f0320150f0b844480080d1001200c005030030a5030300c00800944c0c2c4a04481c12540e00715148042c030f000704032a004008650f9504000030031510440f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 417727149 1250 417725899 417725909
    0x60501020a02130207060e07060525020f0d03051e040302030c03062406160305210106050304230a060c0f0c08040b072906010f02030c0616020307140706020601 70
    0x22104401502680d1021560f070201d070307040c07000107a59420790320b0003001816459485120030f0003020350000380c940d0024000c0c10025018501c0044c04500c500c0421006c07030b050800650492030318407070a105428603001c40d82101c0d00a0400505101c00e03503802c0f101e0643c0c0c8005039240440049820011130404026860741420120082c02e000d1828460001300b40002001071600f201c500b1503078400329224001143d0245000c0725900a614009040261443e4848000c070180b45903901c1c141400102c9020101e4142c1d2015942e0514548550300c034030813100e415001da0f50856000342d04442d100d040401000042622554008c9041c81d4071000143c61501c030020000280600034008030300144050040750140d5040c0340885481e0280c03410650450004000401d03001c0302000c0d040b0081039512080d440c41280241d942000780e500110003282c40e4001d071050300080340c0c0480003203450609540300b10b040b108100c2c41241d080c69940d403505040c0400a01107020150401d6005000c1c00b60305002d1715004d06 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 417728399 1250 417727149 417727153
    0x80c01080c070b0c030709030204060b04050a0803040f0302010309060609050f0708011e0909050f031605010605060403051b12070906030501240605030a02090904051509010c0909110702061b0106050102 88
    0x1840540f40e009a81c2001042c0c00403080380000041d101d14066000900a150050400c10440da11421082c4941d4080c0c0140c40c410714a940000404182c0001160182c8418402190800d0716690065028205801003290302940741d24001c0744000082c440d2500c6840d50410840303503400c01c0f64001d40454010380244540300000450400d0f16403c0303200d003004907000318a000038000c2007030034294200940b40070700181c2d900000403d044c00d24405400000c1050080c402009155690801c2000d140704502c03004003550001001340e41000045940c0906050000e00b210301030500700c84500341801440d4020f52150780d91504280f040c06001d220354000783c0003200382c11549896041c0180701c4011984120802c0120000001d252200d241c0c040d02e000030740240c00303c0d582e828546851510303805814500901e205c4410f0000d90484014010029134a000383c482c0b00311541440a03800207041c02c904c1c3da0440c010104071420060315a80d00602d2011607004440200200300344150b401c0d00c3c030941c0700d0b60440d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 417729649 1250 417728399 417728407
    0x6020307021506010315141302031311040b0d03031a04020307020f06150603010e07021c05040602010e0d0e120a0206190f02060106051213170c070e010305030301060c050a0606080c01080c 82
    0x800303d02c002c0816141d940341f26032000204c4c0c50000b41c401035040d45900320f450000c420b0029075804043c2d007094681c41410a046038030305020a00c0201c401031030038268807001d501034500220380039034044016040c0210302d2445114120002c80c0c1030340d00a8800340010303804821800301400301130154a4101d003801500d0f09000c8401c4001400c2400180281910400b0810108000c03a0080048000501c80c2c5038079a100c0f254019070107004c0360024465840503508000750352540e08230100b81c0340d4120710306444518222040809001e070342d0000b6007132408503100e08801d280c05030b905c600140402c0c49a0003001c5e40b040d4841c4030014040441c2c0a0000107550006005000542d040030036580c00e90240b09202400f80c0d51041039450514507501c0141201c40d03c500c5100b0310743c403401d0007400080e052008a80409aa071803844192000901c0041c02580007440180001d40c41400315501e000d00030021640d1030300e0b1039201c85040b1940d583c4442c4079644040420b001c0d55810140059010500228060034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 417730899 1250 417729649 417729671
    0x11b110112020708091012090309030b07031e1a1507050d0c1a06041b0801030b090703020f09070201150e010f09020c1e0327040e01060302100e0d060203070215060103 73
    0x81c0c004d80056520481070711b14580b850307920505062401c1191020309104000c45418090304002d4207020990f00740300360100060070a4002d008982c84030000c2c3c41c8690b40410141d80c250024446030821030006900c45011b801103640320768444103a640d110a003196174240078078020340303001a145541d4090200320035204002c10100002400bc00c4244a1807103203503501c542c00240248081c4600c0b920240340880c524a080c0d50041029060340e00c184102c2c02242c5580c0e0302d01c1c1e40c0da101071000a621040c1d030301c0400d886003849148960052424000410400b01000000300000541c1d00142890362114004024102049141030000c010b442401c41c03030300076403440d085c0c0c881420000c0440d00095660400501c0340c420070441d450422044488421744407a4440000b14181000085200d20f0910000502060045c4204002c40c2c1d0b004000b100405e0800c101968408401c01c0082c0d4400500e160080105003980000c5204061315800f030460303d500b04036100045840549080e040500d02108040703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 417732149 1250 417730899 417730913
    0x11401080118020f13060807030b150714071a12130c17070801110a02060906070819020403020d0f0219030b0a020c010902060c0a030206090d0207060509011b1101120207 74
    0x1420340d01c1840944e80d4480300065291a215075403890a207041288000280c4541c0107100d0340c0601c519035418070010f1042c004001000412500700329000c40204139043c0043c0f40c42c061000e00049010984542035540c40c4401542e504510a10740003a90005580248100601c10710340c1c0441c4007411f2285038075454460307451030b44440c000d8050340046a10400b800480c104155030040c0741c1940240070041496520517800d40000300d850002d407140384040b40001e0300c0840c8440c0701e42070340d69038252550b80b440355003a8004003403105003c046501700000320258851410030784007035014104080a000c0030b8414031600b1074580b140c400314441070710300038000103003e10b050f150401900c04000d61a409500c3c90a8010542c0c0e0000941c0203c0000309410746030004505129018025025075210740d84c0c4481d40d60300d40e85031010700401600301d0003087c005140100c001e81002201032400f100300706517003842e502201e240c0700e8069502900c1816042d01c1e640c0d012544810700340450700b00b98185000c03079803655 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 417733399 1250 417732149 417732179
    0x81c0203070312090606090b2103030f18030a0207031416230a090b150a09061b02030d08091002040303020a0b220305030a15080c0f040204090f050114010801 69
    0x207040190942e090500359405800c03083d031117a0008010003409070780c0d07a0404002c003044c02800f401010504040f6820505154200c04050501c074040d62560303507088002c40c1005801040d805142c1e4080b00c01c01000c660400241000444540060034881c0c19030901201054640010100c41d50110400007829200080d130350307084544006059444622106001881c4402e880b00217030081d5000e480020a80866004041d80180230360b20484c80243c4041e01e511203105948801e004074001c208100809441034112500891100c2248a20820a940080d06000144041d407000a0058090245580c4140003c0403840344542c0210b01d4146141d401030b45030071000c2401f0b040b0405d02c0d4009501220b10100705010103040400c0c0c290380c108180f03030141194106996403000d40c0d150401481040c18000799840584100b031005020706a003c03400c0200042800c4d0072590855000d000001f403515050081d20480782e81e06001003041e45c1401c40c00940080350940140c10840080300400c030440396600f9007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 417734649 1250 417733399 417733403
    0x1d120d0309060209060c010b0a0e06060414010509061903150f090e030c07060504090c2307060914070e10031703040309050d1109061005031609050a0e01081c020307 72
    0x12031070301e40e5070805030000d00800701c0540d044000094251207141040d070058540714070450384c642505450300f00030042014120f510640049081005200310b2400e600301248800e070514045140407505400701e006608404c0f0f00d00c417941102580341c008290940900c11401c11000a00d206c15481c110001f504400c4c28030400302010340da143c01e4603440d5020700c11658248900340c102c5841e030341e480703000908551141c850140b49602d0801c00003a0709120b80300074180180307150b403a1301000c20780f60350103401c80d408648225049540c415150380001c500100c5411022100d401800d802031600104507800321f0010407120003120450700a10004515450702d10410703400a0a4640726034681c541610010513070b82002e5407140c89003c3d040308210503613001d11016041500d0002183e20307410180085007484450b1000425401c0c400541515030034900c4100c4048903140c00e162aa54a00105420030314075044805606550320041c45220b1040014280c4501c0d101c0c8608141034801c1d80c0251a40110540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 417735899 1250 417734649 417734651
    0xb010e060f0a110f030a1b033603050303010504112d160b060112020c06070f050702120106060e031605010806010507060c02060601020c06090609040902030f0601061d120d03 76
    0x10361165200d030f00103041c07281c000700c00c0302c00e071941000c19103a41e81c010100c1000011f1010754060410280e40289403e003940c561180300c030741c135030f4a003407400c4910511390030b400c0c165090101d2044c4400c1c0448514001d600407006150349505001c1800b090314912280500c82c0402008090348040c820941c0d180c91a54000c00a403819610400c0040e091040d1404423000307039840b000710006e000c0f210050301d010f10f100343c82d00184801c00c0408a07099008061400050390022000240304038001c14030707000c0c0d071015445d000e07191842641c00601c100002c8680d020783c5a542da030091100c21341040c40c0c0c6407542e4048000300b11011a0381000109182140078090400540c00049415a4068070a07150f05540c022130500207030340050b600940e2144115000e90061244020074034a50500d0000c0b0307440c1042c06800d00f4a00312660080c4000b034003041404981502c140c0110010010003440b503503010380050f5440001038000059110312402100f2001071158001d080300039902500010101030120381814 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 417737149 1250 417735899 417735907
    0x309120f081321050a18030b0a27060605040c110703061806050a0e160815060a03060216060501050f090609060a080d02070504050906010515070f05010207150b010e060f 74
    0x6001c0442c40c5901810700300c00c1a401040f808099080400342404140341e54a925a240301d2201e031b039500c0852848050301c180c1825010036078808054200c403a45107000701e18000210f01c0030b0188051015014002da0320a40c0d160030600191603d4016006100708500d4501c0b490107090100a84885240c400208080d988a00c540030680d2440880011142c000e0001c000c10318140c40004050000c80c01041c1c05805140714540c1004500d508003010307500040020320300001881c00703114410001529040e441006940d0000000e0700c240014030700c5446403987c02c8000762092800a0544106801139032207441c040316048060307103030000800e900110468400700152100d5011407250410340c0c006050900071000020ba055400042010450320141d42c10040380d501d9000142c0ca9000a001c0d140c0e0054443c001419150280009400702c0d40c010b62031800e058138144e403118226404503d084524038940281e40c4d0348201244940c40b0520800e003032941c40303c0281c0d8001042445907640141000402007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 417738399 1250 417737149 417737153
    0x705060307260c1b19060b040b1504120314040602010b090c0f070b0c12010e06030f01051509091f0c0f0f020606011d03010203010305010207052107060c050c0d0309120f0813 76
    0xc03d0006118110f5100170070440541000c1d805800b510586501450400c01c03001d441d402d100100f1700e00c0180b124030441c207050070b0090007080f0701c80c6180d0235010420600d104c2c0c0d5021000d200180000c0c21950000500e50f14003006104252400801d1140f00304400e000007c84604c03184102e0b0f44050340700c80c3e010059034903903149001c64001e130b5904800d040b0a02d4008110180c0242c03640d80611811400c440c5061083c4401500740c60f022201603040461a1440701282d042102c0030a0300720341c3e000c06460f220440c00003080a00c218201d001341e1050344826049840c44d811803490f03000d080a900d4110075020308110040e55640c0c001e0045410004941d07101c0b030501000d0100c00d044010010000c1d980c9580d00d050070382c040d401c00303071060350719000ba15521304820000219660100c98040041c908004240c6c60300c0c001094a03205400c00e014003080440040c0d0f0081c4400c20020303000c5c0d100011540d6003400d01d00c01c030484d2022410144100030b1089801d641d04000f880307502411600c2a440c1d006264 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 417739649 1250 417738399 417738403
    0xa0305190306090903080f01090e19021f08040c0e01080c090a15030c051f120b040f09121103090d0f02060405060a09030b0a060b0a110705060307260c1b 67
    0xb540c01400c68601d044000010103070301151503409031180054001d616601c0d07072218070469146034a18051503211500800000806c1c4406103146400141000700d000d44c4210342040c5031810386a001d00041d00c0a007008200071003000ca150142007c482c00c240d40d0743c14100855500c0709040502841400503100240320400250882000500100d0104074080c1e41c2c0d281c010081191405064442d0201452030f1a01c0a05002019040803095507101b610070918150070009000d5020302c0f5801a072207071000c0c0010b0400340522000240f16101d01443c41280c10401851030a02c03074440c12864100f00480c680769038461000c101c0080c0c020781507200c900c24610016180d0712542d40203603006000441d1040078140c21800510445e07008a080e040c6a40d1040c140000300d501030300890403050403e0290850301c4d4450040d2541400c86c01048a44c1c107900d80d4001401d40e0021207032040091440da456880061070a511002c4d0021148000d683c1400c5c0440803001134081c41203a645800c5040c0c0100d03041d1002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 417740899 1250 417739649 417739661
    0xd0804021e12030406140a08130c05030604200108070801050609190b0c16030203070b0d021b0d0905030a0512070516030f1a04031709150f0906090a03051903 69
    0x42482e41c01000c5000c0711600ca4110b1701c9420045049070b80b602012501040c01c50311941c025544024203030340d0b02c4070b051488064640098520000c0341c04042502c0d10108207040c0035501a0000b03118000821440324000800c7d80c0c1e185041080c100140501550000308841c15684203d0340d140c0c40390210402308511603080c401c0d46030755580c02c45000443d030902d41c00901c038450f5200b05a40e16000e010031600c00d40100c0b448025016070120b9010041741d0a03c90243c401e1190402d0050314050302078508074280c00941001100035000003212024858200004100401090303000e0120b0aa09441702e0340c49072031800d51403d03c2c480c001000c01c2002414881701c1075112481c2103104d1450344070305100141455035001110540c003110403421074898890b505d54802c42d49951f81c180d010ac80245181c0c2c0c2d0320805031401805125031302d04501491901e02100b4418419440032b00424601460380718642907001d0169015504940f59000100f81d200b030491315144520400350702080c0c5050b600300c0007009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 417742149 1250 417740899 417740959
    0x1b1407020d0f120521060f030303070314090d05180102070f030b060301060e091e070f030807050d0e0325050d060515030c030d21051008010e0d080402 66
    0x145144825040108101d02d880341d0502480e0f40106a2003018802d540500c182221074030b800000000d01c1808007a04103801d64880409000b04081c1c0800201091858000352740d03200210b40c1320714500d2130b0b00002c00e50aa6103d40c0600c0200b00c080300324000034007203202d40485641d10b441d040b80f040000703034000c0240ca0f0050240e004070600080e600e041c07680e000181540c0145c820350030568006000180c8075400fa01a41440340644000702001c1c03070710651b14000c000d100a07103018484c030000728103c101d50300c0401140115200340c0c1d1020301c2c3c070f80941041944890b802c01c2c080d00c41d0100b06561400204034505101e214074000e00405200ea043c54000150341c01b0650080011003101c0421049422050259203003604003402c403040142050788038401c0755209074040e4018012064118481e030700001c03408100c449a03100c460301040d881c0050b1036003200c006240d0310740013104200d01202481081d54151084000e4403800c10b030303044010304016019002170310500e078145040546070a8440305112003d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 417743399 1250 417742149 417742159
    0x1909050c160c090507090f0506031305011b030f0603081218010c03020901020d0f0f051b030c07030b0705040b07060504060f090c051206060607060c18060201020d0b041b140702 77
    0x81d0491074184010b0401c0c0c01100c00381401c0802281c070140c06074a02d5000d45800d100d900d14611b060205000854000500b0070144141d117400460108030203100ba07200321600000c103880603a1220300040c05607070080407001c80c0507107405401c00100b4440c41c1a1024010104d4001a2039211b006503c0e4038104c11102400d4107501c0d01d02d600c2a10740d00b43e4006c0030400421380239121210309402007581d103000441c1c1070001140070f020b9010215840350707004004141c00c20518034541c010324040249103030002c0400e804aa40300351418024030007401110340d404039007071518034500b50418035041641e00500d50010f01003900c80c40458100039035034120ba203003031420010800c40d060442c00e024100d11080d114181c000c0340b00c5d50f460558170b0000300340d06103d504c1c0034100710301e00082e59075004c004048a031408400c0100003601400001d030302d00392000081c04207500150310340709041108001c490060341101c0c8141d01e420003402c0c501e003d201c03a04091404a040c0442180b54005403145244a0000025400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 417744649 1250 417743399 417743437
    0xb030f100203010f050d0f060c02010204030609152403080906090d0303051f2601140c07060501050a05030a1212090b090601050f03032b05010b0c0c1909050c 69
    0x6481581d020314101d0f040b0030b100c801c219079181c1c00e014001c035060f0000380003040004003c401060142d00300210700059440010b00d41031741d90f00c5d20170894904007411200c0700e03031400d04440c14154600450440c840070a10030004010900c0e81604d4181c518840244440001b00c0c48100c0d5981e140300351406d000d005042903245c4d007001d180040040108580848900851200c04201c0036044007290341aa42c9600f0102c03181038004405142074090b002c62030362290340340c48902808840c3d05400c0c81c05a100c0000d4070780c490000745407000c01e17154160001b81c05403082800030000b0341e030000341d0708850f250000c02c2d81c180c000290004880094660b00c4641c0720500300b480b06400c018ac2103d10b2762285040605644960340ca034802c109500c00f0355049943c4c1684203003d0340441c110002014040c83c5440c01e80c103420f041016107102c00380c0700240e10010641c103011a400c2010b141c18401040c2e00b030030448002110001041c00030300580e80e140030b456200d696500c00981b540480340115400e030100c0b1040fa60320 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 417745899 1250 417744649 417744673
    0x80307050a090608091513060c110d08040c0509090709060602030d060801061a0a02010b0d03030c031a03030417010207051005012d050936160f06030b030f 68
    0x10351000707620100003903959000290b480c0c81000e2040c0104140b030064203140c40290b00800c8803c074082c1448100c40f100c4021070002440902c95028030500715102c1045d030382c000c003c400d4144003041b00c000c0180800c07400ac100010306411000d0b020f45e001210782010303540750380802500e40704c4541c1044140620301a0081052a0008007406050948030824800b0744d407502003490986030140706082d0002c0c1c0c03280382c074840c1c40001c40140515000c60720001547c0201c0d403000410103807010350b050703020a035602140c03540590f050181c1200d4211001c6404083e000560129503244075520600d44044402c134000109008207404a540c4c46420104680b59131140030030060080c0400e01c14580180340d17a0003514841c40400c0b901008000354444003400710345c58202801000240103091040c40d0391400f440f00c101d102c4004d01e41c00d1070500800164403070340300d4130f110514003d60000d41441c8051010001c0004da4056101c10040c1c40e02443e0100c1c0e81e10030349001c81c1c81c140c1070b03032543c106900403110b01c42c0f4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 417747149 1250 417745899 417745907
    0x190603110103020c160821120c09011214061008070f08090705060408012319020304080f07140106090b0303030a1d030301060e090a060b07031d1504090b0a081902030a080307 76
    0x80e46c02e00700c040d4141400d2450030783c0f030000d2190304441d1081c450a02e0008482744482c1001d040c4070001070408030502c3c606401481c0441e14234100000040d20102d0920206041c41080799900c4107032400e140c8028200400040c03d44540390344040104299800007450111003480b21900400300039060780c0c0c0741c5417a00d450314060441c4888403605458ac0d440020709150750900c040d07000314407020080c01d407586c030114003001075400240244c1e8042d2041205000a0f1901001020303800d0003068039000000c50047c48609640003035004c1d215240c00c1091244a940e804403c9980041000c6000540c002401c0000386041c3c0d075400740071086000200000840c503811810719148154119203030840b81c0d540c60340e01c3e411103071980034602c02c040781480601d00190007036200c0000910224100c4400171003550000d039080004000501c0b0040c4082070420003040c0ca80540d51000308212941b010040c1406101a5204000000001400103240002066450a0004040d600e82241600d81d80349440c000c060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 417748399 1250 417747149 417747163
    0x140703110907080106080f09011e0209010e0613050d05070b0f18060304030906050a090f08010903030f1b0c082203030e010314062e08190603110103020c1608 69
    0x5030080031100700082165125203121816036000d41c40d8580517171154400c00b0b92006005002d89111341d80c403036445124001201e10003405000043d405641c80c45c88000041190119100440c000c0030280414111414007510100039660181d511034020302070780c28490b1500c085640018403e1400092a60701508040d0050090b1200c0141e05a413041c424003d2000310f100882d0054001460301c2c60602c841d40c860401000010028907182107003540310002c1c002c03217030504c2e03110910740e0f90344100b15810107805000b120000c402ca240c0401145a0f200f242101500c001c058540401210f81c4e0488200448103040d00d4829074689800030300d0b28451080c0d9030402c0ca55000a0300410152014404150303c640100000c030801404050143e4840d1000d102890109a626034000c940086907030a01c0562400b41c1c40c4021115500c00155090800c13030301c2c1075000203080d0f0f20565810f00710140082580d02d64940340149080c60010307950801e40b00c180b0b042407000c020340c0728031810105000909a40c002168 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 417749649 1250 417748399 417748433
    0x102010f050a05060a23060a0c020907081501110c091009050a050403140c0a110604080a050102220605040b0313020d050708390d081201090b0d1509140703 68
    0x200700c58a13202c086000c6503041c006c0b8480303414180c4c03510032210303400c0032030117040e008829003030800003418075a0000c2c080c498103c0e90040000c16500801503410b00341852813103404400c1c00c00b0b1070340c9003804600c19242d031b03100080b0900445d01d00f00810f8a8482036031000005003003040040055007000c0c3d070344001624043c0c9081d400529507100d02080b1514204c200e0351401e04000040090b40c0d0240d0320003864007803407000d03c0d501c00d0040c000080c5203481408000c00d201c1c4245e00041c1d070345103020320f40c00c2d140d00030b0b80c44c80c01c019009103800c2c031125410904840648003007101407a242d80d10700e5080c05810907c8403000750030880d100303d240d0030000300241060507a001002513800d0030a070101090701e01c03102d0004124164411608000380d092021a00348803100b400f07450030300d45240329100d0400d02d07802010340303071400c150076001080a1001403013000d00ca448112141c079400c888644400091040c035120215145654010f610100312042e1140c00c03012070100140c1e60165a6403c3c0490b0382c0040d5124 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 417750899 1250 417749649 417749659
    0x101208070201020c04140406050c161a07081b1303021f091e030b090c060304121b0b0123090108070303090902040e0708040303020408121b0d0516020102010f050a0506 73
    0x211038052419002d1b0140703404a00e00c0b4640c00381e890b910740350003912000d80242c07000c50042061b1040040116000107290b402a80c9150000241a150641502000701003a041000540038000c1100650051501c480ca0a03582c036500c2d1050761100d5034290702513034030017075220132040212000202000140c441081041d05d8a040c8c8507640d0700e4900c0c41c41008407044c00760403100c03442400042c140c444142d804c2001c1c43c048900c1c1742031440c041045688140c80580301c0800c00003002502e958040644005e1052036500004100310b00ea440703d0050406006280000100c5150024a500f01d070048041541e00206030803255691945074944a11150000f680041c005800100b582d0034203000302c40c05c0f5201d500c01c6507816561054105c8003030300041c208404150702088000f98031042000ba0400c1120003589580e610301035000004070f02c40761031043ea52140c0260001140582d000000d07100c15480301c10001000d0441440103c1c01481e1000030361411a1a01c020300944034155402284200c205a075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 417752149 1250 417750899 417750913
    0x12180304031406070e030706030e0c18010509130302060a0e0a200a0f0b0301030303090305040902040e1602010c021b0d061e0c05070b010302062514070f0315020310120807020102 78
    0xa4111100c04010585c82c2c0c06034030483c01044500d00c070364004100805a0300588004249100020300b06c24500900103400e50444401070029140c05451640c022018000408042c035840c0c2e40a5110003008003080a400c1ea244103502c0806c0d02480300da40c2c5564424144511154603c0d118040c034a030103420103029149040300480e041603c240310074203039074442c1d81307039403e503841d5540450140064520480c04c06c64140400980c400b8140040c201501882074031482601c1d00d00b0b640512003081607184421681000e1580ca2226008580740701c0741a811400500d400c0c0c500004520007000d11030005149074038040c41c01060150328018a04c05640041e000e0000c2905601d0444d06070003550009440300800000400052500700010a000581c000412680b5410300301c44400803030511800b5120110040015807030848280100e034050706919281007221fa06681b6801512420940141500c83d800000b2403840564030001c0780c0100b0718106050080079079443d000b2020b03004000100d015100e049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 417753399 1250 417752149 417752161
    0xa020a05010c020a05100507030b0303042405070206030a0902150c0601030c05090c030a0b01091706060a0b03010b0f070c050d0503041d01050904030f030e072907030512180304031406 80
    0x7060b13141085811100622602c5032483c1c0200080001a0a903024581e441420043c0b03a202480a40020081c10007140401b1038184103018010a00101402c01c1040412a01c001642c649050304e0300a01034100002daa6105840456a84683c4500c1e88a40f04404642030340303100b90019103e03058a04c682030075049682d0300c10501030030707000640301c000040100b400003440303c41080d031003200312503414900305200a5030740560700c0780c00200c1d0f54040c6943c0c10210810040b4144042584001c2c044460040e203190b00d0248020054060703428501030481000481c04280030310231240b03402911006050020340200d43c81e015541e9400b501c20541d06000c00c503800c5480140c00e21605040b00c00103401206030341e0f1151ba0456000c80c00e00821400e065482d403541d40c131000204000e0000e001e00785641e00c81c100c0440480005991400401c01800308104108000203034082c0070b0700c3d0780380340c0b00361141d2040e10751440003480b882000b100b240c4203203c00b080c000180b00038802400a132034148019990581c444c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 417754649 1250 417753399 417753403
    0x90312030c0c0c04150515130311011b0b010909020d021203210702061b0c10050601120209061b0f0f1608010e2e022809061b060b03030a020a05010c02 66
    0x1d045c1d050b100840f88000f0059410081b02c1c1c0d4003070141300c1801d149031804581c0030b2956400c4640003501d40076025160101d0a503000300d825400400c103031a0f031741c0080c0c0c1d485d0780f60900c00a05010ba01c6a007500c0c0c203040003c546030104001c1260f9402069501c3c000c0140745403594a42204c071946842c402d40c000303088030642c031136079030103004d0a9564080d0100755182c2052500b50840390508140c0d0107010413245600450521014092018080002c500c5040100004015500c80d10900c20304600c10000d4a4040c1c4c0c88000300c41402890802c0602c0f82280641154200842c10114540901492099019481000c21810387c440361488854404236140e03441c503800c035490156041c0480d80801c40045039035400d02c4c81c859a4805508280c4800100e040303a0320b090303070010694103111400c1181d15030322007007040340c100c0003103000340c58220461482d1610040818008514062007404006624014400660005084c400e40541200d56a03002c6541c020340d5148040e41c01e90b85035207400302d154449880 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 417755899 1250 417754649 417754661
    0xc07050307080304020f1305040b0a0c12111b01140c09010804062a090f0819080c07030804140a060203040b09190e01060507050c03160b090312030c0c0c04 68
    0x1000003507060104598445842e54000351090b603010100e01200300aa03500c2e000140c4440d000d03000007050505040c50510f80d00c08000d0314000070f490402e500280c44581c403540065056400032004a2030344403000d0180100e02c100d001000c58800101d40c44001d280b030542010000256451440c08190340b088100f00403406400c103050300280c502d0003c03070701190840d004240070441d0207a048900d60040e00071000c40c0360800060300045594168200410001c0301921f400511940015080c0c105440031080300c4120001001088140c02003011402101c04003c00c00103190302010b129a144c0d2a018141d10086440c4480e0748540203070390000c2940d03480030080c0c500700c5504a04441c10141c00c3e0b42040700c0908485292807003101009000644500b48242550080180b40c640c035513180040c0c00c1c11802c00c24805021402540b00c116581c2400800e1040c1804880c10910400d03107825190000038101100c003007220341e5a04000c414480034004580007000c13107010410450710f12005517400d000c103a9075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 417757149 1250 417755899 417755903
    0xc2803050f0d0c03090513110408070e160804030c030c0812151e0409050c0907051c052206290f0901140f0a120c0f050f10031d03070f05060c07 63
    0xc0d50010806c20360800e4050702814403402d81e40070840051441086c607158201c0d5100403c0742c1c1c00b1000400c508103841c001160000001031109441c00000fa201805080b0f001c0c01c01000c10125112400506100e021154881c0b980405100d584000a0030f0100e50b03848107499070780820400702028502031408000c004000c0300048020642310102c1420030004050f484070907070f802e0188a0540f440d40d80c59200c107a208186640b10a0745503401c0c480100c003d071202c4940118001d10b040140015904910341e410459812040c000a4074019840c102d0041c20003003804019040c0d03011a800c0c0211042c0d0101031b107403403059030f00140300040e01d0104201c0b09428400e00f03c1c100d00040d1400f15500704888400e442d40c2c0c0140941d0003042c0c1d02c000d041c90400d10141c080c7d400f05100c65040c00703010a0040d0038001044100c1e00507480aa070500000c0810503080110070a06a0380c24560b4000b21711410b00761100e900000659484000d1424441500305900700c1c1220b0600a02000032006842ca0060b43c030215 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 417758399 1250 417757149 417757157
    0x2206030b01120c1706210a0b0903040b070204020d061e030b090c06030402040e07051003060806070c11040b010306050a180615050703080a11040b090f030303090c2803050f0d0c03 78
    0x10018200c1c610001300c02074011904141002240244120000c28224000d0582c200602c03001506040c82024400080d00410654100700010014207102400361f40d41140c04540040c1e50394070902400c002817050f0307031008000c0c1030104480344101c015846010202e070b0040300c820506503104060951114521054558001c0081c80801d000d402c00d540018580c01c43c8400b140c140326128800240c2120050005000003a1101c00501c41100e041c89500c1c2c001501c4d05249001c41400d0b40d03000203010300200d0060080340d40d4118103140b80e20030f800c41c4000b45005000b400780305843c2c40c43c00c7c0580c00c6041250100c94207000c2e00203545641d50034203211440c81581e419080c040b440c1d4044078006800f80c0f45420f09a244c505510441c41c4d030b900207100030840f50446595400c0f81c4828401c106421400d40c81c4aa00180f0401c9014200414242d5000d0012240c3d0601c10143d0f848920b84161016403008030310120300c101104200c40002e107180c0943e104405ca0b103100c420282c080f100e401c85613000030001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 417759649 1250 417758399 417758417
    0x1a030127030c0602040f0e090d02030304030f05130b1c1503080a0c08040b16051614040c1101141b040510050d1e020406140c0a0201052206030b01120c 66
    0x10a1140d150740b01e4a6114420141c90035a940490403010f40c055040400c80b0043d1100340001da040811840f40d1601050000c0c508514058038040c09030640415581c050040003d603503014a402c4101d8200603100581403183c480300e00f26000da146691424480501074079040110107480050a900c1c0102e07540400d0f050701d0421207210440f00c0c4081c0702001c032034541c000e010100e4620143c030003810051012070f1360721800341c180d820020304e0081d428009401d0440302641c18095105000290902901c090340c01280443c101c800488580d1601e8421904951034005c12222171044034070098002e00b900030074158401c2d465100d641180c41148143c55100b00b140d01070034805402000900841d60602d800090400543d002151942803211801c04003130703a00140038421036400c05480c40401c0069041142891410080c25076500303844100030f41440008504e082c60322001c040d8010300c913041c50100880250f580e060140240155280c100d000c2a90801ea8070f0300f403092407158105600b4640d480c1000c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 417760899 1250 417759649 417759653
    0xf0206070c0e0708190b0306060415030803150f060f1204170327030703120905010b0a080d02061501200c060a05031009020405090106081302041a030127 67
    0x403644030003000c4440c04621580000d410642c040410300c110007585800c0310a18100b8040442d5840308040c0f05003291405008184035200018415071201c0150740c0020b4180d0f408001c180d84858690004040300700000030054501c0f0301031100b8281c040180c41d40310580869000f00007450096102500f258401401410503a40400a6090b0010300990b0b00c0046251681480c2100381d00403111031045850080c4400e00c2d518040424081040b4488091820621582e500030041d07007060340c0044419441b1900507041c0301080d0b101c1c00032410000d06080c40c2c65a1140c00c107840c0c000d1036098a02600030240003944c05560003114041d2000140d40e045001c804071341504000680b41d0061614500c207030204016035848410050040010720f8840517180e21300790000502c60354980c1c10100c1d01c14010300c001c001c03035102d003082d02d4159405c40c10403100c1d5680311915210888288000a54410f041c501c0c00c060954000781d28005015090307000388042c880c1c4095003000002c2c3c084d14686081411405600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 417762149 1250 417760899 417760909
    0x120613203f0408040e09060601021501050d020d08190c030905010905060f160803090307020f0307060c24060303050405040f0501080c0f0d08130611070e0c03040524071701030f02 78
    0x50b109101d40a12800c20f6215000190780a500b118000c0080c2d01100030b0100f1507804100601c41000d401c0003541c00ba60600c4085007206801041c0240900100230441e0204407a0710159030009030412290141d0307001c0003038002d1920914603001e5002c101c241401241340d502c599507400071358401030100e80c505401c0040c0c0d54041da010000c9140e07903501d00300c4c210002544050040d4000c5624400442c0c0320440c0d0300400100d5000352039024820ba10a00702000b2481d0003801402511382c010a5188924003041442c142c1549445441d18400c0e00d00391000c420540c0010181007550415202009660000d101031000c4034028083c104081c2d01190502c2d5191611120700b280d01240034242d40789003c8160780d8403110750491980c1038080741c24a001480703040d51101d185014100081e0050800070b01d031500c0381105030070107047c119420400000150900c0000c002840c80e0114075444980c103180003041e0050445010b81b1076200003815082e40818007511082540d042e40c1e00f0034411080c00c1e0075542044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 417763399 1250 417762149 417762151
    0x90a030201270b0d0608060f070c1a040507090605220203060307090f1a010503070c031404180c090b040f0902090d082d120613203f 58
    0x1c154840181400350070308520001c03840144458142c0b9920384d482c00c20318000342c4590741c1003041c00c0d90010b010000e40400e540034413a001304071800c028101c0400703814450542d01150352141ca141d29180240410080002428800c41d460f0b202c1c20010540c039042002030800c195070118041c5500480310841d00d20b4298011608503000404503003810b40d84007070840a82c0e1118040c01000e582d60450744140500b0040d00e81c107014024038041e4503514002c28007514220130b41c0c1020b01000600c01032000c00703c10403021100500509944500100d01e001d0001001e0640a9038050016045c072000065210800042da0140c07034403d00035414803410301b40c00d038000390801014264031010903001d2601040c050b0340140400794119189042c40c1c0602031042e0506940120f4810011404000c103070581c1500f440d07480c0e007005040b0366401580700b506034024003620b000000d2540c290301100c58825859883d40c014490b00e07a25040d03481040303041010713013180400303560200840148a030030312011103240b0381611 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 417764649 1250 417763399 417763427
    0x1150906080903070201112a0a0909020901120c09020c031b06100b0309010b040207080a020c0109120b090f011503020a05030f0316050715090306050a0605031b03250f060302090a030201 81
    0xc403000a242689a5084501c003145144050704c088d025007035904020021101500d402e00081c04000c501c0e90100310400703014441c0b00c81200250712204c0800240c0500c00004112080c03056441c1c3c14140c078a580c49a00c00c074080d000f100c0b41041d035401003c0020030b9131031282c10290084c800842c64442c038018983d200038140c07504d6540c0d80c1c410016a41d00c03032002c2c10a050241103850303194101000064684500071011505101684ca020020724203d540c0c50351402e544800d409000d51100d24850b883e09101801c030000070b50030701c4120b9400301400000c0504481c000c03503504840c0e0395200709041d0ac1d800009200780c0184c0040112641c4800700d546042c10481c80340341101d403602e40c0d500104a4165640c0d4040d000102e4032401001445558000c0355044404000100100f03454400000ea81e101910134031881402149a07082c0940e44c2808440005400080042013100700e00c407035250016440d010394203810321311000201c0c510b0710900c2512110ba07405045088084d00307580040da6900000c0310380d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 417765899 1250 417764649 417764653
    0x60f010c0c031a01080d08150105071506170c04180311031603120b031b0f15030901050117061509060d05010f05091207030c080706140115090608090307020111 70
    0x11051514505100c0080d4449001e550400340f4003030810000d10110b108201307c40003808001695110301203030400090070b00c80d9035801c140c642003443c1040380c507004070142e1502d140001d03103814801140715209041d0041c0c85600101d03004000c100d4010070500200412503c3e229400a400364448103107444d403410440381051180c0f005d250b418114031a04800141100030300703c45101140c092120102d404034003404200808100c5580c1c0e0b900d0f281c0b0428801c1060340031030007068a9011840c0c10719903500b011142c1d6890054240b5000c1c21003032140000241c008501d2060394000859000c0c09800c0080d0184441d007189001c1007400f000243c00f5544c0025021201c8000400c00d104200b00c80d440d00c0000314440ca4100c0c5550304080c1c8424002c5440c4804100d80310000381e000302c8107070341e0755400034216881c0d007041d040110081c03011110034103090442000124907014038a408494204d140d664028a080d19083c0440340140140c4122016038002c1c0054401036000ea41c0100100d82d0b0801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 417767149 1250 417765899 417765923
    0xf02040209151207140a1202041a3c030c1204031e081608130b010b070c05030c010906080601120510030b0c0c0c120109290f060f010c 59
    0x100148076078825001d1208801e00006120540110f245402c0d5400701d41d6080501c482c0410b9001c0081074071079003403070301c1c1000545540100400e15075415034000c1c0c010103060280f42c0e1000c81ca6641c031540301c0c42c10450681003a882000c5030100e0440200c690f08445043d078902030181d400242000d03000948064041c06060041c0c10041c1701007601c141c07081d4004e507180400321049201302c00503441482140301c03c012602c020040d0091621608078180034051620038400c1d52988400741c114055001c1c020511507900000045085450021300415401421450707205030751503082560710160810110b000c05c19401041012a020743c5a6a45c000c0341810008800c07949a9403207011143c1c1282d10a680fa15a650284140440031020301d030322603180702c50107142c507141034201035030380401003641440b461b06008000302d0110203421808076254440624071007040c000010020031880f104c0d413a541f1089903000034901200712340b09a409130340f01030301c087d20898119004481d060405c5c2c1043c1c0e42001c00c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 417768399 1250 417767149 417767167
    0x2010e01050c1014161d19090609020915040e1302040b09010314120c150403120203011214010b0108070522030b0601110a03051917090d02060a06120f020402 69
    0x4010502481c10801c03a0050170718042001c1c1001c5440d924801e81041400ca14842d605035501c1c1c01008038441c04c484406a0b070722504408441107135141c00044401c0c0c14800005586040c85c0c01400484508855280e54125110110710b114091841003c05115001c0b01049001c00e6004405001c540041c102142107070102d800f0601060003070341f0031965241c0e4072a046c02d1010f42445141c01e0b50900c10b00032460850102c842c19695907440809407038003140381000c43c08140c010400c0815800d0710a50035034503507a580b001042c8441d91101c040d1910241d901810700801c10622038541c800d4070503140c140594542d10400c80e0240c00820f020701e881110080c1c0c241c1d2040e5000c2c0c3c1240110302c2001143c1c05031034540001007643d040100065025802049842c00090b04141903402c004c240e00c551008041083c03000722204d03061030b0350f00141c941240091010550001c01c41c110300344255022102c0e9602e585031110100c40440c4036509400d254105c810b00003801c08078040044a00007030025080c21258 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 417769649 1250 417768399 417768401
    0x4030206071d060a0c030201240b0a02010e07062a031d01090914011409010b0a0305040501090209010303020f1606120f020d110c1b0904030c02010917071e0302010e01050c10 76
    0xd0203c5000324203401151701c101603090190042c1c040807610320403204403041071385843d40e110901420344a1100803a0341c02c1c915100754418141540c1040465609650b11480500080132a20300001c9002c01c1d0007090320112154400c00c620301c0e41c550f40d00c40205440440c507100c2e00580c01c040390b04200707440c64001070b400c200b40140000848141e03401621540741505607070303003446104580c81c0908a19001080a2414001a0742d0924280d040102c0c1a5490740f034000e004240c4008000d5001556000100501d54002082c8100401c00011a00900c020b2405082186018852a070001d6056400054021240e40140275088040d80c1c015041111103e48802074519038a101010310700041051119404100003000c0c1e40d0040d24480400c50480d400800c00c1c140c0c00510107014403100803500021644904100342c0244855003000d140d902e0140882500da840f244a0754181c42c07010001c240058603507000e1a4202c3c1c3d4142c4602041c4400c1d0001510303190000c00220140c0e00031503100501c8c20003e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 417770899 1250 417769649 417769657
    0x30a15030c08010f0e0c06071b08060709180e070b0d1104080c0109060806030a11032e2405010c0305300c1c1e02120105010207050904030206071d06 65
    0x1900011a44074100307100c090807900b404103080c190354841b0701d40d54065120042180c013a5604900c91940240b0400341d4000c1604141d4491600380c4504010414440c2e80002100300744c4400c480e84070007000108812000381c404c0360090310801e80000c0820041d0341d81c020000c101c040c0d01101e0114048801e00041c000d40d0f00503500000b000e4101c0c1c25002010f69000701c203a8003520090402500d2400d0604c00319940f5404050002c01494000c40e90a01c0c5960811001c06480011681684500404040c100c05030310385a00c0301c54514282881840801d665000141c206103000209545242c43c01d40111070341d140f1131a066090000c1004542600842020760f8200e032123070207104854500300c4190058600130001d010703607124841441a20140581d20040e032110b02400e10010500d065074001c400c0029842c08000040c441c4002a103030b140c80c110a803803034102d079826001c0d42c90540e560341c00d000704e09104403030050042e00004009605540689a400a121440c0d125014151a40404280c0702d43c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 417772149 1250 417770899 417770909
    0x32a0604030c080705060a0f0804080403060903090e011244031b03010501020307060f0b0303040303030504060e0a021c030c0f080310085101060e0f06030a15030c 71
    0x1d00b82105000c24141088a10024001911414070703201341ca40004000c2501025180d041000b0840407406103e607150544010b540c022500304510602d40c94081d000742400d20405454141c1c0500014100382101b0300340e4491a00141107039243d4041c500341100b450040c01022040c0140d4400d40d50081190102c0040c0d40044a02074559905024a2070b00d106012021003400240c000c200512050740c0c04800c0d6541070354000b4020403968030f46000b50707025003413280031150075220225001051540c140c11250050f40030714406c20022200180a40c0ca9a0b1181c8010f5006641c40041c0d62507220f00c0f206140415010349400001420a50381d0001e05010000342510500f038040240000c400f041a003907002410407030300170100740360141c2146200c0f0590b041c3c00c1230714641f81c1c4034001d80c441c8441481c5950103140002c5554140c980c9880c0c80c8580028050480000c0f980d0a260b0b4613401c0c1080c0c114a00c0c4001485c0904540d200300654000e0109410030040020080c40c001002480703d03070010b40580 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 417773399 1250 417772149 417772163
    0x9180c07060b1903021c0b2802090a0b0309010f09030302070b070801150f091e03210c14010f0e0601080d05091f11030a0801180b032a060403 62
    0x146241007450964000b40d030b04030300c11010004038201403101c0c01e200108880d8162030080c40d4201c610300c0b407174448505000160501103040300700300840c0c035400c0844001d24000b80c0e0704154103856103480d908a014005c10b8680040b0425003c1c40981440c43c061759114114100100c1c4880d2203800f18002d40358404001c50110342c01040c0c0104002ca4241c0c0d05522102a00c6c0404696240000b40c0803100461b00414050000c1c038000d95401c54441c841040281c10119411070003c1301c2c0c0610600e0440300d034801500c0001070046621903015801e0444495403100355a070070f08102080d01d40400c20710b2240c0300d24440d1b640e42c0c0201984203402d8018051180302103005002030358540000181000072030525034040040411494a20340c0c0d0369000720b00d12030356030a5894014000c0c150705480e0302c080750001d1b140501c80410300408041e803004866050300c2d00c03c03110794603080300d0107405400d80d411500002c1e850313003142d81680405111641c0e00e06603c0c82110704a079450b03e50401044a0350b003c1c0e00161500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 417774649 1250 417773399 417773407
    0x60c0106141804050604030e04060f0f03050706080c03061512070804020a080109051002030403030b090108160501030b100e04110c06101203050d09050304090c030c08010503030a0203040b09180c 85
    0x40c64030070542c1602203240c000d080000c2c0783c1662a1511107000601c0141400300e07441c4103140700d850301d03407210000d0a1254203009245403100028840039050b40700844903485081800f2a07206d10940c0e000d402004041443c07800c41d240c600803c0a03604441c201148140700c140501524a0030040500d402100036488074102400e140c0140504548590807201e4036a0503c040035001510000d0b03c40800718070604010b03100e49441c5403c401801c1d904034050fa01429400000c150107001280300c005007412034038044c88c15580c1d0300c01501500d070503c00b200d6000c058142e0302d0b44000c0c0a41008558000300038000100141e444500034800d4108040c0920702d40d02040420144825500030040a800745011005000c2d0540d500201030348102e03040a012192660303049420004c0030001c0d600900421002485040c000a00c000c00402d945103010700050310b82000007903d0300b00030044079120503550703002c1c62500303080000154035540f01c40d88468000030340010300c2030455a1042c01c80e018440c480f40203603407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 417775899 1250 417774649 417774689
    0x70602040b09100e06070308190509150f0115030f0e0f0309150f071209030b070e091503101802030f0c101d09070c020d1101020f1b010302030402060c0106 68
    0x1c01c01c007a1400f5010301944041070885030395502c1c2500da40301d07414034069440b0750314044400c1c100d8407410041d01103a03040c42d0610040ca071b07001c41d000210034408000140c0301e40e03421103110303c03c803001e02c02d00c0b80d08083c1c0380401005a10a811404007038034400c8000c915144409403883c60415400410b01c0c0d5a0070100340f0040524000e113580781c41d268061400f030b08004460290940030300c603070207006169201c4041da10401da4010380e050402181c005400d0311b40c601c0c010303034003420407160501154460041a00080c2082100280d01d50001e6000f034010200803490700700f075000030070030b0581111011401160b81001681c04021031082482c5a501914450045500380220801c202004005000307501d1720a070886151150040d410b035604842e03890103a01c4400c5d06849166041001941081d102a8004240003002c1d03105640e800c002e0703007120041070a03604116240e48003848810003030f080c007203020f00d01d40d031085e0041c603001400145014a405034406409084074007540c001804415407102240c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 417777149 1250 417775899 417775909
    0x41811030d030b1f180b04090c0804050a080c0c030609030a0314150402030604060b120402010f0507030207090b180403080105032a09100902120a0c03020408060f0c070602040b09 78
    0x964810a0030140040c280500c0040c04050661320450090424400070150082c13040303420710000c160418044a6181d01d6201e6031815520030b01520034031307506001d03c22600f188103405403071140750804007500d80d0348081d5541d0f004d40e40c415901101036102e00100e0604a940601c145802201c5400095039604415803000e01600c3c1003440c03000c4d4005150003000703228002004c13507100034130040364016035035540e45002034010600c1e5004229011400701f4900b02090b25003042e940298005d880782d030034112007140100c4152250b68802001030300304440030400001d458008010051000700071415a40c40650120060501100d080c1c0001d01000010842c908041c044040000c800e40b2580055400030400b0101d4014a14445c5014400b400300081150300115503000142c0509401591f94030510f05051082e1203003590b4804a03a4940400100e01d94084c0c8210703012503110314090806951f440a0a448411009150304001c8400300100300020354144010005441002e18290700c44903d4000d00c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 417778399 1250 417777149 417777163
    0x100e071518050904020616081e0a080a0612062c030301090c08040f140709020f0a0305060d1106030703090209041a3303070305150124050d0b04181103 66
    0x140200f503040288030250300d6403412110b080c00d24090866800b105031034600b106101c2e08004011032161140341e800c1d43c09602004040ca0003041d6100b2001d92940242d00e001c1311464807407541480f00340c0c00d9003000a2840c0c1c03c14402440c2903402d5400ca80d850115000d41c24030b00314404c2c041c42c1c20000042c03029080718032848007054014501204140340c0b030366400c441d5408850003e04501000d06002c40302440800144024121030708055441c0c0304280181400c94101207007940201e030a1000050050600c4024018801d40001000c41c00818034418010540c2c0040c0c088030070903459030700c40300c00750300c034030f990b060140e0700c01c107940324001c0c80345002030305003d10240945542c69001c4122030329440140c01c510003008400d203a019800c03900200060300e01151940002e0a50042d8124202c005000003500c41c100c40c84c10783c000b0b80050485c40401060a00b003104213000c180113220041c81d4074000c2c0d00c2f00083ca003020b880001c0d124101d192000c0400303a240001c945c00c02c000c051520075810f09100c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 417779649 1250 417778399 417778409
    0x6060504091a0d0804030b1806180115060201020c07061b020f06070b0103050a23070e060109050409080316090605040b21130213090308010506160c0e0115050c100e071518 75
    0x110a4034a808c4810340f1414094501032103004002020313a84100207500064800070001002042d0513940c2a010703010350445030143e64030380100d4000090450140403520101c298220401401842542c20804041d1204aa40d504098203228a10016103070150042c080d5015500030440c6d820545010300c00401107070214603604084102c4aa50a900000c043c0191a08a801e0030030f1070341c50310b00403194004242d00940d445030401c0c184200380659040254002c0000c9640f032141c11880130320950388030348984a445c00007001004100031101d1003802400203072241e01a10480d550f01c1d0030102001c02e40680d00c0a2001c410300c6012811032801d0f8074807035281c2844090a1001005603100075000003014407460f070044800082030a03109064819102c1119404200b410360030b42c94000070174440f81d007409443e2141c1821500d02d004180914152044400307050010418040c01c50020006080c2c2c10f0403030349003031290b4400414400380c01d20820785241c003036640711880049140b40540d28221076901c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 417780899 1250 417779649 417779671
    0x4080307201813050f0a030e0a05090c12071b03050a080609100b1b01021207080604050420010e0301110d0f0c080403140c07031101020f0106060504091a0d0804030b 72
    0x41c2c4100c400c0011801c0c1c2c000d08640032800c0f032510f5814030740e040c034411201442d528000d044c0704404254214030764803d025000d8461440301e80d2644148641c149060f140300701c41c00014026060603801b100422940030742e50b40303040d0140b000325940ca42300054074007908a0111b200410010a0303682d0160006511440443e4a5445030901600c8501000868004d03102e6800d4000b805203040c2c0c0070078000000325889000210740e81d551034000e8040000c001c0d1600da0005106a0100b40689001d0140314011608990180070056030303243d0702404440d00c0c00090341406902e1180c040c3c40d560a00c10011101010070344265aa0a000030700b07412a0030f14001c0403082854440205802a031241c3d900f9030160740f5080c020b200380400000509030380900405103520f07124105000c0104680c140160888003020b808a61075500c0c918036650984140d405401c0c00117809000c1005901d0403500220081c86071000314403040710000010841d6009036032020f440440c00040e0400800c42d02440752035111349620a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 417782149 1250 417780899 417780919
    0x30218100906121119080112020609040b12100f0609060305030d020a170910050f041a1e0c091c0f03210207030f12060503120f0408030720 61
    0x340291814070640030700e038100580152580989030041e8050b030b6903404144450794407a9140140142d12035000d8299100007403503d400018070010040110080c20781c01021603062006103000d2200904011450300d9101b425214542c294903402d1003135a601ca1440324001c14003502c2440e00b02c041d920203510450005251805c10030100702c011042d00c1800e2220314000d65203410700c2c1c0044900d5408005d011b25540012010311040100001d40e074100c04040d61002d005540da480340c0821100022a4040c18101c5001c0e82403a004a08280040d401020300b0b0b003080400402c14520420034404039580030319104009034240852410901c114a25000040207180c140c6503a5a4103940341100607005003480f44a814a00100540c40500d42440360b22440843d110007060400821040d014040d10010402d0032010086200e240e000b80d800342c880c0900100100d0b0900402c6401d41d5118603480d0581c084203101c0030682c070106000404103280901592203480354115072210194010160030761041c00c601d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 417783399 1250 417782149 417782179
    0x10318050709051f0602060103051002160b1801021206030601090905100b06120c07150b01051e04030f050706090602010b0a14040b04050c0c070f080606090a0902030d030218 76
    0x10754405490041401080369102c180f2401070681a1a000000b0b0300120800480d040e0b900046441c101c81c002e41c22952a0300910369448220f110f00e40441c41002c86603d59000442d154461541d00715090804905503001c44098040c00c80c2c2040c01c0314442d00c412001400498074040101c54090600600f082058800d240e9403070b980d0790744240d281400c860703d44c10385c0390280d5990070a031503002014080107400c41ca00a8940140381e44180d40403201c0441680381c0c210280c60034803d511140314181c441625020003500d080c100ea00e03582004c2e8800190411012001450345c031020f040c0c070341c4220003e008950800b500500440c040350080c1085a141800c42d203180da443d159294202c40c55140e100d4080607040d004107019241400c001a0014104410711140401c45401465196502d00a850a940e2203003195900d004080c418521694032400c081506440e100c2c0b41140c202c0ea0707814000800c00205e0340400c2c1041c1980360f40b440469400f2500707038103558041c014050940400c440132001d06a1103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 417784649 1250 417783399 417783403
    0x218040b040e3304060e1e07090902060d090b040209090609150720060109060e0618060d050a0312050603010c0c0303020307051b101b080a0c05120a06030201031805 72
    0x1210f0340282e102c0b40090569900c00090500484200c000c0b0503025240904108015100d15018103001c2e01c21200d0403660840900b0f4640900300c4002c010f024464035204150015110944040c3d03403010081200c8104082da502c43c810308507201b505640424503060041100b402ea0041c03410701036400c804100040d165000c21201403080c1c1c400e83c03c448030f8460f80b03011a40c0000340c035411031b55044803c007901058080004cbe20790413551b0040c01480440d84a80b001c40440c00e0903140359070041c021450103200070007907103c500c6c0d0001e40034020029203031054461601e041c1e0416015004100d184002c000300c200c0d18010650302843c160028081c0c20401c040083c544d480d07109000d41007560210114040038403407402c41d14050380ea20446003c2d921800d050a40381e9500d44141b40390b691400b0100340c5e80041d444038042000e07001352107803001551100490b501a100c0c14104008211040188808888404d40300e00d00640455900182c05c03030842c4009021103841c2480d590303807010b42c1c1003e20001100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 417785899 1250 417784649 417784663
    0xc0105070812040807330e0309040f15030807061b020a020d030207080109050c09090606010212090a031e05010e1c030b1206090d03050105010504050604270218040b040e 74
    0xc09803030141c2e5141c0c1806401030052032402800d009290030307500070001c5030507880406c1c286004604c0c00e403000d014982e04101d0300c00e0403144e60541c0007400105000d25050380010801403a6041c08030f2300101000200b58a00b91f250021581e0400104942c01440828420482c10f00c584140340c10110108100c040e5844682c068001d1184107240907200805100f4440c00c00242052002446401300c2c074a01140c0f41c420511a4030700421480b800a00850800169030b8001c01041e00502503c004c50301d6046e01a0780034400a5401c14103652000002840080d00e28001520640c0d07014040b110518065003541d0001a81300d580d5889030001690b03041c80424401219607071418001440180c050111300400c0c1c02064a800d980200781c10011004d1011a12400e82e000a80c0c0800441ea01c41005503090b000768080c903074100400780014003808090025070790740340505060900004900b610b005060381d02000500301e0019a0720407c40300c0d03050034028480110300c119030900c0480003003d5125a43c500c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 417787149 1250 417785899 417785917
    0xc170a0309030b040201210c1206030201080c130e0f060102010e070324200a090602160b0304080d051008011103040b1315050408030f070c21090b12090c01050708 71
    0x10f10310100301107a000c1e40300c1c0c50001c024486940748458400780c00030000c104281e02c10f00415400e440003410541e261184401b036946c141c40d0a0340c25180d2004441309030f04610184a00c030710351a40d001c82e011010410309880381c2c0310b10304000035a1400070002030959203c07001c0000705030700090081c000625110b102401103105500301c102481004207504000d00200c14808000c0001d10304480304170000b0308000c1090005584880c0881c50340c400c0e040765120340c101d0f2100200454540c0601c1401603103001160881e01400c565410514812808800ca91013a9115030010004040c10030000740207014210b00841944030050451400da00c524407401402001080301203029002801001951030070700b402490143d40810141c98686080015680156540c84046038080f00090715280f14081074032101c1d6000814251300c0b42441e09402c0148280c010720700c288800d0300d00104104103080301804400c003510300860210b00f000e00c0c00038245011401c0031810003104006110110340c081040311002e403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 417788399 1250 417787149 417787163
    0xb1201090e071e0e0c0f180607050d0801081020070f050a060204031e1a040507052215080d140d0e0a0201110c0d03031e090c170a030903 60
    0x406148600d424103400e0f03004104000f194041000004209400391021340b004e41900455580b80d994042181d0b01071900c003407a10032010014403060400c900300c80ea660110203414903003041000c2e6200c600301900007a805000074003140041162070020409045d400b60385c1d00c1c1c2040000030141084621000100880301c105800040300307810043c0b07030400041481e07000801d5456022861800070060f6015100070380305c003101581903841e034442203c5822a601d5100c240b10030b6401c22074940040e00300b002071003903031280110344000500e5100c08001d180b6140049420300b624060040303007101203074020b17642c2c1507180d414a2803d02c40201d000421181c40741d181e050041d094101110300c070005e032007a0013050034018205540d6680d008000900090014401d8a840e500341d008401007d81d512115032100b9402030150b1017450100740250301041072100c800114601c030014030b0303440400b541c03a0071604803821501e02200304105000b50054405078510b4a002c0c000b0000c641e1002071036001d042c0006002d0f8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 417789649 1250 417788399 417788411
    0x1905010212070c030b0106080a06051c150b100201090203070f0f05150d060f09050a0b06190212070f030f0503010503030f0901020a231002120103032f0c01090b120109 73
    0x4002011150001151702c11118040c540e16958018003c0030b0513200c3c415407609045010a0618200403600c4080920880c0c50035164080d8907041034211010440c2c0034084c2e0795802420442d200c840340c0300440907203500007145070181441810f01d480d666602803091092000c00070f100308000605a20221041200d159081e0b000080484c40380f4403461b050042d07002e11309080050048040e415a0088820b4400b0402440d41c682c0c08031001d0b980d2544150350f00640c20004c0202c0144c0b4940443c034200990310483d1039004110441061980c04144c06444648440c0420340030541d000019017484040361038818119403600307010030b5903409840e00a0500072008035244a203a4420441c034003020307070000441c1c0304604001680e646001805415402c0502030303a41690038a040d58000c0f540c0070740001e402c0d01d24580c80c50320f0480d03100c1e0860a0114800700300340c10812001e50204401e420708035041015080301185040090012a00da40c000e10f0302810501100c0300d046000042c1604482c3c01c01800702d50 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 417790899 1250 417789649 417789653
    0x40507080109031701091506030e160f0302030c0d0b0a020d180c0611030c0703470f070804021e0a0905150a0305060714040b18190501021207 62
    0x18104940c1012280750b182464400502da40551009208802c1080031840d0b039880b41c5484c01540c00c100c40c45085180240e4042100e82e219501c03005540c012001507601d80c019001c003c3c00310341110f61280c6c0008080000a1007585410701c12500301200440c0c0f40d001040060740ca0329854980100840400c65010425010100340c41d040022110014480c001c5c0e5001035107041c00148065020380800100c012074190014040001140c0d0b021003444018440c0c68516685c81003002040c0164800092032103000580703002041c416020203030300d00337540c0c00511300055003005002d0100410b4503020901c103400340106680c20001d500d40141d01034030002006255008104110082140c00c2d40d0840d000e41000602010260b00150141d030b255840708422401003c01c00980499a00002d00f513a000340c00030519550040b107580745a21031040030300c0d0034250740c4c0400c20080d401c440c04417502c6131401e4128071404e20301545100101b03c00c000d41c91201d981000d00003035940803204803143c5040d0f400100315003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 417792149 1250 417790899 417790903
    0xf010c090e0613020a2613170f0a11060a0605010503161e09030506010b03071e020c03030f0414010309150207060e0a030905030601170c041a090c0406120212010b030405 74
    0x580000e1040031340d40c0c1c900980c00141044071041c0e0501c1d2149120591404006400305031a0190f0038840c440c00504490b0f44440c1e80e560b034000d8020f042031000700816425644220087c0c04400040d441c1c1030481c00029114034202807004025420b03503490f04e207003400140c1e04002500d802c0300a00704202c80d80528801c0940d2202006615181c2da00d102c0c2c586096015840803541080d6031041c001d440103a640c1d4149035103240016107a107004600020800304009100703298948445002d441150041011440800e040d0340c06594110300800d40002c080c801202c2817050004c01c00403c3c41c0c00c0010780c03c0c1d61180d60501101100340d040722500000c944003401780da9002480c40d12a12000d071000040903190242c84038200348a040d001e4015400001444142003442600414002c006002900c4042080200a044c100c1c903c0200241d801c001306800c1d240c40c00d8441c40790296248807030f80c0d2418000003501d0b2144942502910600401010015001c00d61201c0e04541c0800080d03030b1241c440d460030034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 417793399 1250 417792149 417792169
    0x2120c0a0201150e0907090515100212190e0306040c0b0a05040f090509070b0c031204080d0903020c130b1c0c0302060c03091005160f02030325050f010c090e06 70
    0x583c0241c1c40030004282c8180510485010311108400c5600c1640d035000340300203450381200c0301408044c0b2100b80000c281402e035000c600100a0348191240701c440c2c035411901540091070410340301282041b00c1140c160300040070f0803042000f1001000945840c1e61050124400c82c080c0c070b03001500104a40101c07030300420036240a41307000a00120700c0340e01c3e01c03a42700048c201214580850700c82d01c1e2001078840c0d0440304940c102060031b001b5518049078000c10741518a4050400c441e000c400700301441c0a0b00b142d11500301040d03c00d81c09819400348036400c020b44542203050500c210792030807820500d1665960940c08840c81200340b8100344015070305002507000038030b520194200e80c0000303114442c0c0b0b070f011008100524084a581c11070040d00d440072940c5014005a62400c865812150004984401450b9610600c0141100c1c80c101902c250b40b9000305524540000c258000c10000c410040180010000f004124008002c140c0c0c1c2e60320014004900c600c03036614401c0310711000c1030894403280640 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 417794649 1250 417793399 417793421
    0x709150f021e0c270c0c0c060d0e060106081017100c0804120903150e1c020c2805011b060c09050913080a0e04060504140402031002120c0a0201 63
    0x54082d0460700010a5191001124010301c1549030150100d072488843e540d0b440c4441a4030800301c2d031a83c8400003d41184d01c5020750070342522525410f5120b56031588002c0010748540440400c0a010f911641851f1002c107800c45010301c420071081101c060302080c0050104c035118041c010b418005460064205221196460840c0341007002d0b604e2038503004040d450080348204425404002d442c80c00300c0b20083c20340001000ca0611140314032000c40345810416481080f0010b50b089190904555070141c104400300002603081195800300c0703481e004040741480c21000c09611486120481c2c10720196407640a01811b1100401100b00074150316003014001036400181004812000714000d004a0760902c5803600c0b40503e00002405200090000100681c1c44100fa50410300060815140d0b01c0c009152542c00c0b5a65900000d030b1507480e03016075080e1483c09030710886113007001d00500d0b01340b516181a034070140b40100446412920540002036010300350360501e0740c9500c001e840403400b6190705908 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 417795899 1250 417794649 417794683
    0xc0f0509010e100807120608030d0b03030d0f0f0b030316031808121305060a0f080606070c1203030c02030c0a0201080a020c03030a0f1d071403031308010b0103050709150f02 76
    0x7000c1103c1d40105560703004501039102c24074130400b0b40c07910710140e5500d0301514129070400d000c59180c21550707030080803010000500343c90410540841c10800c0305c1d000100c2801c1e103a11b590b5058a03201c400e02c282c2c1d800c20b100745d02445c40c2c01c01e60100c510780c4400d480c8000b401c00c2a02c0500c21401e0941500b4130b8094940700c07080d03d8983c64201c0c0078070300d00d030003540008140f1000c4500024641c500a011118100c3c00e03601c40350341107903c182e01034896a9000700a030303070840020445007000031032022100d0064a01284030300032042150030020b044400b0721a52800307640c000c00c0f600030450f80c009510480c0d07607030920b4440019980d4086d444040d0043c00015440340c440801400b0032001c91350851403114901d208100070094013034086e614014024203940240350000e2005002101c29811003050200000e0f0441c0e1421b03516010319190201641c3c03244202d83d640303040c0ca8000e90703403500801d900200189030012150b400d0148500c1420303102c4040d40c00340046a561451050700030b2010802c0d403509411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 417797149 1250 417795899 417795919
    0x51501060e150903010b03030c010501030209160807110c0402040e1b090901140414090f0d1818060b0f03040318050a0501050a0c120207032f060a030207020316090c030c0f0509010e 79
    0x2707190341c0605030a0104921403c0d0210001d03d544902c00c44800741000c2a6a03280c8198540c050305a900082100b04009103005a148110240c0c0312400200b004041800b00d003d15890b122203a00109070040c0c9000b240340340100200c0c50540d8501003803605503050312010314404241100010700900070700c00014604d1700e22508004942501180303101e2001c00c1141994080b0001c81c1080fa001c080c0d85601038070342d100c07251092013a07a2000c803101c2880171f040c0e100040d16940f10000308809403c1740c44071810a2400004100400d9842688050301c0c0340911011b01c2c003d41407000041c0c0c100028002e0504005000c540c80840c10300c40c20341d020000783c0080d902c214450345000000c1d1100700700c0c0829900040041c0d50301e100c000c008030b83c070701c0050140a1003c0c034481c840e02c00c01080d13500c503a40d0001056024004036015076001d004410b03005180038404040da5282c10780c0e00080e81c1000c4804400d040c07038001c883ca00b0353382104980314a0600303442d100d03607914180401a20f500403102003240d00629010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 417798399 1250 417797149 417797167
    0x519140111121e0a0209040b030c091b0c010207080a140703080609070c170a02120c0703170d062606060904060506030a080301080a03031d071a0412051501060e150903010b0303 77
    0x107030091071180070540e001e0261088c1042407568409500c000d46801189110026258008401c111040c03000a0f445451a100da82450142685c00060050341ca800c00028800c4085401c9592030014400c0d000b405424411181c03000f40c0550402030006004000080015100920628518440e1030317104602e0500c10071110541903040e040364403010050f01c61300810068844000c1c2c00e03101c0840070100146900b038110741d140c0101441200c4e1100059200b840204407048281c0908009010304842c214231255054140002804544840100d070780c00c8042800003a495102d000d0b40e0050300260041070544031200480d190104503980a401030304084004900300c00c0200e0302614280c000d903010300c140c0d1103609100040c080e41c000e159079151b0215100b082030101000b0303210500458a040d8a0a0598810225108900741601260540c12520b80c010a40c61110f4030709015080518000c03203021400d80c0841c11000491100c03580c03100003c2104255560250420000c500000c1d00742ca44401c504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 417799649 1250 417798399 417798401
    0x4030f050901120e06011806051f1808210f030a110d020715060902040e040f0206161a07090b1e07240506011b06020c0106030519140111121e0a 63
    0x81c0581c2c60141f4081031801c481d01060f00510301a100010500c0642211030a00c10f4400d02c90041c1160900800c083c0007440000c801c40864000c0a031940a03040440440502c07005200d041c6010f580c03840002d004c14071201745840b00341d940c824000040040c14206802009000e4001d011510070304078000500301040080c1201d504c07201001400003848296120489141a0b005070300800201e03042180000c0c0210302e80b42c039100308550000d04000e00d020407040680200d05c840440c181e0784549808040340226100841c000c1d440616441c00519a07400e0100c00140d41c4241d2541c10351301d950f048211221422460222000d00fa44142c1700c05206030030155000380411207504540300382e0310348800942c4039406a00d80092070410051215002c500c2d81d0745100083d000601c454915669507440440040c10820100510761204540f401c0700301d8051510104982044007280c0320703641443c01c4818070083c4801075591103c0c0b514250700040d92610a80c14100405540c02020a40b03a40b0501410b2062 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 417800899 1250 417799649 417799651
    0x3160c050f0f060105031b0108070c0b07030b030c0906011407021206102d060503090a05120d0f11070206070314180a0644040b010501020607020604030f050901120e06 73
    0x2d04203880f03240c2c0e40c0744d0400da103543c000318134501100e108a90071013196100304d5400d5806111410110007007081502d03220800c0d0001c5803c40046035031813a0001e164a020062521050000c0f903400780c0038540b2800007414281c1d0032041d0072030410003298090441da0340401e00c0442c01101c1c01210540d03d45294101505070035840b51f50b414000992245e18890b054050144840b001100c041341e001740f5040302121a54801091030299020319103644e00099428400d80b0f034004030410080d900c03070300040440c0341200c642c1c03080c070a00c3c3e074a012080300b0074640310419a900700d50104c1b0556242d00c4c141c1401c1c1d03449102c842600b480780c0350004805c03180180c1e2030200c1081500580d2a902d00644844060303440c1d0008108100110164007981001140724684100b805c0c1800e549070010303184104400e80c40303004269400c1b01d4880106006202c41d5038104400c0754014124401070009003469100645000c0d402081981004030002e18191264081c1510001c8850201c40070000f40c0101d030340b42c175200e04c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 417802149 1250 417800899 417800923
    0xb0102010b060304060c141e180d1b051c02040b01171905160c0f02010306090f0209120a08031329040b0a020903030409050604060b0403240c0503160c050f 68
    0x559074101000310007520103130b9900600c4100311802c8480442080e0340d0640201d2060110403400d062050b0080d201c1d000c241d44203d1050301c524038036010800100c1110f02850300400d000341212441444185034514140dc030558065600007024070510780100d6032810b00c0c0d50740701030051110060210f041c9aa40000c8138280804104208a45513120010f01444800c14020001400c001c070100208104503010450280b050400041c0c990b940c60402083d5500c041445110543c0400c890a00c0d041094402c1030100149015104000459544002c00c0c0130141158510b150449000010031034025050302d00d044a00465030030b251b42415003420104000c643c2260182c5045010411a80c51b5009840e00e1070310050142d42030504100303242000f0103004010310392090b143c040010f1008041c0c0000c1020358042d00010640040301c044288540782044ca10388c20a501e803251010110f0340c082e043d2a0031018004410454092602c82115807074032044010b000390140c1c81c884415200b000549500c096 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 417803399 1250 417802149 417802157
    0x3071202010b0301140408090a0314010b010909110406051c0212160f02100c02031605010e0723040903110607110d05090a0308091f020705090a0207050c040b0102010b060304060c 78
    0x403500b90241030a0b52240765081c4041c0f01c0100118002400780d102408030b415000c0d00030140e841c2e80340c0360505401c001480300c0317040d40d5440b0300107242540d1000f0a800038040c050f42c107024202c0c1c044451032003803145200701000c005000c43c0304160105443c178603840040c0c2c1380c50706540b500d603001c5c0d0b1000d400b20107440044071280058100c0600724000c1355805120012038020303003080700d00e605080e80500722196184045020800003070315091007600c0da8040041c000c500003d40c018624544074030304a50b6800140961007850ba5000071a480858103114000d000c0d200440d12102910b01600c8184a0320340c00b0361a80245c0040003c1b45500410442080b01030310100c2c5d010104030030003600e581c891816043d41111441d4414008940210018000c4000103082c810048001c0000d01112700c41e04aa100016001500d040049140010055403c208421401c51800a0039551036a541d070f080903d4074000e649641503200241c1c000c0d40900c06140b0041c007201e0703403842c2c130b4900700d0010202800c1c440082 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 417804649 1250 417803399 417803411
    0x1608041d010f1e0608070309230717071503090503070f05010f060b0f0306031207060e0d030e150901060b04031b0801141f0f03060e012d020f09030307120201 69
    0x30b043d4440c00600740c550100d680321800e0038904111220030005100ca13003030644860030003000950200b40f060f000c5900020301e103d400c0e90b40340c80d2408c00800e6031001203d0340d001c0030503080c036a401081260448020350120b4801c0344000d00709130301600c44082c0250140c007020a00d0400e000458225200c594420b5000300105031001c60990211003d9001d181192001800516100511900216000302d00241141e211004100d00c0140c550f100181c2107a09507101c045580c05940200704003401c0c10f11038103041c403019503900665580d50b14074010b240c117808607060100300c48010a5110501402d444c5903440d41d81e607224108110701400741007c0480181c00c840c0000b82c43ca006200e640c0b05c0c3c00400745241003a4440c1401c0c0036101c0103d501800d032101201c100010342211180410b00254850381c00490302c20a018403007803c607006016401030600075050b080d00600b800030364414480e88041f100584a0750794640c45029030040c00000c50701031000090080521081c512040c1308045594024015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 417805755 1106 417804649 417804659
    0x5040f0605070c1a0601051606110a091a1809040303110a09051c0309060f0c30110307030503090a0b27030304081608041d010f 56
    0x200304002d84200400526a0800c052089514499501890004000381048c881c20251000d492103000000c8100003255100c160386100e210545508c030b80c41d140d0007030803201250060098140c101d200d94405200021f085800c44a8840845c0c0002d030101001d110410001030000c8003419105c00390802e082a420014000182907a03481005c10352034502030058078540744035040d2501c40d14020400c0403d402510240803600940b07485034042e112107201f2a040c0d034040744024103a011442404001d204640400390150170b040d884118a070320f0340002914020004150604c0c1380d0000d00041e408030703010f10040c2d0b6002c0c1301c8109a510301100342d40c1e0040c6410007142c0380e602a140e07419260805c40e60204018020320174000041d455404d041e10b540c16039000c1d00b241c0c034046503100c0300b801c000c100408081c5c1c1e0090946c0841040d200100ca000030301c0e618400d0241c640001840c000000e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 417625899 417805755 := by
  have h0 := BRFrame.cov_init 417625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 417625899 ≤ n) (h2 : n < 417805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
