-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4874
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:01:10.394588+00:00
-- url     : https://prove2.me/submissions/88e32f1f-77b6-470e-b4fa-8753b152ae5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 876438848 ≤ n < 876618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 876440098 1250 876438848 876438907
    0x150507080c03040510090906080607140a0207091a040e0724020a0213050f0a0603210509040e010e16060905061b01090c090f020414040207050709141603020a0f05 71
    0x141607000d06c4181c11211101c01c01e210300c81d91a005182c0710002902c0c2040020b0141030550101c080c220010300c00b042662040f03407025543c444440c800c0300c1100f0f8007212011080d8100314464502400b940300c0981090015051951034298046021021400000c03034035130142c00c80b40701481c000d12107841c170185c000e4041e4903d800c0c0c10001a0013003000300d52250741c10320901d0215200c27103643c0c41100152035000f040e800f001c8142900580040400700d0310002001402c0090801c03546460050b40310891240d80081507150409080c3c030304216207083c9034000c0c642d40c0481000407960010100c0111a0155885907440c1c1080c1010700359005c11000718001e540c01c04102c00100b0840c40c03030590807540060800c00903094403500001c181d200e148241505032018001804044c0703401e0703004001940c443c50445084642c0e0b03600c2d210540d552103e410030060b08446c1085042c1030311828094880035030f80303411458404d10000c0649011041c254507410008046801200c8e100f00403c4050170309402d251 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 876441348 1250 876440098 876440119
    0x51501061713020d030e0301110d050103020906090408030a0b060f0a09080106090b01020c04052512050a02070209070c0501020f0417070e06030a06050a020912100501150507080c030405 81
    0x10300744140c076482001c001800707400050a8082e880e95101105907000b0800500f003201c0c0d031801c440d0a005070600310b9055503100d51409003182050000c00304455109000b0030550b00d0741c0104000000e0051803540225039060400000034020b4080300da01283c4568000307910002c80c0045260b0b40a020341c011080c89000615030005500301c60064111200c020092086a8680080380e0a807114007041030f02691104400d0b840c0d614042c2c1020354004104504c0c041031800603103e24801c02c1d500800c0d000403802005018031002c10a0042940c00314641d0425032510000c0c4e400b241007240001c0c041002c001142c80d00790304101c4290129002800700707007140e03600c0e16110242e90210b004401c0241c3e80c50700c103003000000c42190001d400d500c5020f0040161180040c1a110100640700040140414903030800005140da6a09002055020000b4004248022028114004550043c9c20100d0320030783c0c8a00c040400f80e03209044503103183d4002e580c00d4641103241056841c5010300c2c2c010325480400210b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 876442598 1250 876441348 876441359
    0x80615090414033007021614040e15150a03020a030303090f080318070e0702191103100209330715090f02031204240c05072303010204050f0904051501 66
    0xb04d0303d02c1d1182d0034031401d2105803240c0409a079104000b807441200242070090422000da01c2c415400d0b8481c0c0c01500106000a400c01c0761820b00b182c0160407a50030124200340f04001040b0900d81d03040d11820b68052071117504540004d5280c0d030461100600b0036881e43d1000040008841c26404103a600440481d00d9081040700b0442c2e45202c0e4a0711603192051180c0050001c4862a82d14050400c03500a004c000c0041402200710401d940c4098a188841c60301013102c0703840c108900140c206800c4401611018814104941488030ba07002d4110354500070300d0070a00750074086441070200c00502d00c00755034605c0b500e41342d481c48404210740c003907451501c1c0104c400c1c0108040b4410f0024400ca050b544a0b207035416264070540903900444030329142d4031400f5461107580100c0c104801c206401c00c01d20560803680c0342c40c0f800c916500402491002c0c8154a00c3c1d00c04c1c0c06203e4030a18404400941c1000d0905020841d900300c4a031209100d8103400700402c09114052101c00744082e01c0e100e00d0f503055030312217 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 876443848 1250 876442598 876442657
    0x9150807080723120f0d41030708060108060423100803030a0c020d08040b04030e04111902010b0312030a0207020a0b0a030504050d110a02190f030c08061509041403 72
    0x1a2403481076400b8111001c80c01c10311424210500d8159004038180c0300481815004500c40c0100500003c204000c004100044810024603c01c9e400d5aa0f0b07148240b8203040010030004c005002213001d281004203000305014003159850400103920151291981d840307440080544080d03104903500c0c0000018018200440d401c0600c91114540860312115442c80b0120f450300b404a80142c1a503282801060020340710380480403107400e0081000c41c03121a0569200c0c065800904200d035424074403500c5241954080c01140300300d040840c01381620801ca0264130b0040e20000340300240084c0d00081e0482103659042812020700b844041036600c884500c0c0026008180a40c3c00b03982c607218805d0030309503151041d410101040c00040c040c00d1022459030a01403c507944504400910303d40b20000320b240040001c03c0c40007180580342c0902005d01c0d00703481c01d003080000307082d0400c00224413110400036100c001e44140c0007548884402920304c0100241c40c114014180801154041c0d108095442d842c0b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 876445098 1250 876443848 876443863
    0x60a0b0406020a020307120b010603090f120c05060108030f180d05120403170315040e01060e100e0108060c0405100e03011104030203011524030908040915080708072312 74
    0x285d04844101391500e006503503490085000502040c008001031060324130903000545814803032030b90101e4080803607440400c9801103a01d640001034064142d802441320411190b030041c60140040c6241c10300b492a040e20381d1050714070b1450340b0144001e010790140c4074101d401c46480c0e0441e05841700c1e418011400015640070b880709459050f01820a010403000c1601201e0042c4800c9504010418400d024440a8141709100b0341c1c83c3c0d5683e070300000c2c80c48107000069204007624100c804043d400c004a9000300131068020072006d81c400302c2006468042c4e5001c880988408a80c082a40343c800c0b0022101540180d00c40c9401d9420280c102c1c0d82d851102e17000d401541c1c400c8000380034011040b100c50f2044100303131207605001c240f0101101c40940d051580c0c04681d03001451b012032250f1980d10b508019601c20b60255901a42d230f041100b224580003130108000e0208100540407151030b2000041e0707154540d019200b4514103144094400701000c841d4400da1b00805011001813005890a090301c5201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 876446348 1250 876445098 876445103
    0x10e060907050a052704050901061e0509070e03030c152403060c16080301080c0a170d0f0537021203011202040b090f0915040317060a0b0406020a 64
    0x4801000c00d0a00d070041060b1188406950703641810041038030030a04e04101d00345042d00705c100413144103001c0c5071164080c0d14410740c0c03410008207285181c80e0146030320704440200c00f48591480c000a221940e240c10741107400c50501d1411075400d0703c0c1000081e06502c101c400c410498890400c8145e5940601145280f040004940a9078441001481100c501c002050700903415044800000c91000006e1302600c00400310200d10005040d0603070b6212100d52080c0c111340d039694820210140d8030325000306e041000e0005c07461003405500325210500d80c0c0e1a05000410240040490400308240c0b00b8026100d41e00ca000c1502443c8254000d180c03051503284040b00728009070201039000400d400004e81c44034195610400e20300e180c0c030700a414100b4003414602240c0c0140c4030b0b030b1140c071159942180c00d402490400030490182c2012481c0d2440d0074480203204140d48202c0b010040842d03080400d000c07240d06503406504c0356540380d0002619480742ca40040040d2000030501060450340002c2143c40b152 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 876447598 1250 876446348 876446359
    0x3030b030c0919051012051005091c0507020402090d0f03031d0d030b031c090e061014030717010807030606050928090204090b090d0804050705100c0506010e06 70
    0x5002032003120a800c8640a04407410b500f00c400364001144c1c0b00316031290b074000d19624000e40715030010340240c01c0c1407001c0c0d59503407140008062035a114452103400042040c001d0007a00d038200c3c0d00c02c0210b842c80410300d0a001010450a055440710340456440b40c0005107181c1b81800289000d000a40c12402c0070307400285825a201c1011051090300459025140010704c05041c24140880192282e00d41031038160007800603254040b010200403080d1700500c0d0f2203c05031107081690340c03840390780020200b0b4410507100511103174080d0003140f0300c48075500c0c1203074241e44ca542c0e010701034410702004012100d49a0411000154100000c9201000e90703126460600409555804021680c8002d0f00c0400e4017420031202c0100b1281d0b01006160030000c106808100500a500042c08542281d4000d54081c0c0040d001c00199076400d108605280c1c1040c2451942d50519840d481d5441546018807402846e13594a526580c03070103000394003212079215044a80a607101d000c0080410000da51650180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 876448848 1250 876447598 876447613
    0x32402070303090618110d240506011e05030a020d0b09040302061503010636020310090b011d190506031006031808070b071b110a210206031e0403030b03 67
    0x1030070084803501c0c800d800522015207001c10300c6c10491200c10701d8800f1212108420700c003003e4003014690005130303201c5824000a1902e0810005032101d81132440350b00e400210b40c51800f0129800c1425640c1100315580c0041c0c0710303ca02e4083c0e9004105a1031032580c080041c1041004055000419130320410301d184e000715050b0854011b0601342d9069002c1c000300034810003c00b800c40404990900c8512558188104e00c003d0041a000200c4e84184d40b64007201505c04030078403154005002c1e405641d1800e05e800c024190718144503400065006594511500c4071031281c44800e6402c003503107005000000d02d800d0766030800d000f008441c3c1030309104110210342801c545890103030791005a0081903401034402481c10b40345980c2c0c5581035000411600501045600c00201c6083e100c1080501c280b0030000c110410381424108100b4400d160300221404099020885140c03607010190001d41e641901d10940300e4554103d090302c0c664400e00100c0b00e25003800200010303d0750641194040d03120607016204034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 876450098 1250 876448848 876448871
    0xc0f0f2703010606050403020f1f02150f060913060621140706080c0a17011512060803090402031512101803080103020d05120409060f1e0324020703030906 68
    0xf6500e0324400c0b100030400a000400c09807c00d80448140c05400a0924010504c1c0800c807045110b02d918940380140d009820350500d140040e00c01c2500200123076240b1090345010000689070300c60061058198000d8200c840040144030f0b042540a070980145002c4c00c44c800c0c01311496038030015042a513592142004200f424480460004191605595455220750742d0804c1000c659001ca2000d01c10030094513142e02c42245030301c400c98003803c40c0d2014154050080e403030080520a0f080800c08409103846800c1010120020407a21140001d44000d6142e0340c2c3c41311381952810348ac44440d50400340e40d005000c5910300115010f0704030210710804000c1c0c50003072050781c03245009048000b000f2a45082c010700c050310344076400307044581c440c01c11070f400d00b5400c0e0220780142d002a800b0040c102d0b100d032070034404200700320008806064800d032004050359607003a060031141c0d01448050300d0001e0070b0442c0c1203005806101c0c62900c2098480940d503a8485280c018001c3c4200141a280540703402143d514 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 876451348 1250 876450098 876450101
    0x70e0103020f0105030c090307240305010b2d0a0e100f080a0e0f01140a0c2303060102030c0109050318010c0507030b18070f03020a05090c030c0f0f270301 68
    0x6980d0040c102145240402c801036440d5400603042c681c1c224000d200503d21660704100007809408503800b6425484402102340d21040d031038103014000d15080200501c520704555040d111700c8854020902612003508007806481c1035199025401200b002440800040d000310350201641400d8a58400b181070b5004125881c284003094040000d66040110700400da240c0c200401d40750181080ea081d2400741c030f444508481799404c81d0781310282c0d40e80820081159901c45c12100d1111400c046245007121481c698545800d02462404840040b001c20071592003081501c1589400c4030003040075040310b0030281ea0f00c1d0001d8a00c0c00008032003000c20f14495114001c1c100100c1e61040c01842d07994195940c05070405030040006001910840e084000000300b00201c40c01482002418030240c0d0441c0140030b0001344580080f8002c3d48440c0c14003002102c1c040449501464544943c2c1c0c07a200f1072500a140d42c03080141703c140e1705002040f003104401d481e0134450000180002c992402440c008245030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 876452598 1250 876451348 876451351
    0x50f0609100e130c120b090d1403040602070c050310060906090903020319050f0708070507120b13020f0a0b120105010e2206090e0a030e0d110d060e030c010e070e 71
    0x31910800900455003142c807000c41c3c40d1010b8400c00414010b55205c01a44601815022040d60611401024003940c2c00040c01000702d05a44c610300810825822017000c41c0910004d440204030300da000900105100081100c0e0002e004002c0540b0300803015100c10801030409400364126a41c5001c1000445528512031b50381280d90503000b8605105540d892000b02a181c01ca8100c14010200310611030b041940c0b000b030141520543d04030780c407003040307007400d41c98400c4540101e130301d940c1108101d42c0070840d86460340750701800c803c000c4208407486101103040b40403608403403034002908000c08100e2230300c281c0107441280b0040410039410fa80e900c2c01100c0350840e002801e5084241180c01582040074401464040c0442c0080462155a00c500741c0c1d045032400050b0f42c11a41100b0080010554032035030541c01010121382a00017150030751074040d01d440e01418030f24400d040c1034001000f082a035804c1000c40307203000301c2540e8848014487c03440c00380aa00038180868050a000880d0145000f501903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 876453848 1250 876452598 876452609
    0x60406050105041523060a09030510020a0507120905030a0807030807140d2d090308132409060c0e240405120f010203040c050a05060304020d02130b04050f060910 71
    0x3030604c5280a4540707603141d480120740c0c1c46025036080c10006985400d401044e0016150740c6084019207581002030400050064524865004102034800d0301d6011050b01d03111074012040901100c0e101009503411003ca60241c0e8050141c0e098140a101c85680603000003400780c2c4800115540c0c2803021299203440e40b10000c01d100051012000c444403903881300d0032040111102c5003140d200150041c844040144101c82015190095441090f501c1059103400000340403c2c1c19801125654121f44990040e2000769103805504811007280b105801c0812220b41060040041e5505400000d04d04a44208280e001d10241e205021079201508558103048442c401200d04041c03c0100f0401c8090101a0000032841818081c0040f140e081c401075026500ca0681c2ca000c6501d02428000095050750001d440303400144100405610303009600a0344943c120340b1914881d000a0242c801001042c1441d034105141804001c0300e84008085240030b82000c5407548800c0c4c4e00c030040070701d034010b450040703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 876455098 1250 876453848 876453881
    0x435010e150702071d0403020706230d141008060714120402030304030c15081e0412030e1e0f030a090608040302071a0306011106101a0d050906040605010504 69
    0x10004482804625003150780343c03040c1c1d40038540d540382e030001c4c10160200720020f46044009200405804102140c001d2505c0d0074520300c00f41d03003111002c0840d02e03207440411608800150240201c812a4800d0310b1a1090758401d01c0b50781021502452000b40601404411384110700105140034014151041c5c0c0011901600b8a00404082444c5603000301030000c981500c010310003c00001d01006880002e41450705800314070902550000b4141038020304840c40f40224010700010350030414854a074440d8114104d101035902c0c464040707008010712991003080c2e0040341481808089030340d01d4284240a01812a030210b451065040e489218007454940460309401042083c81d000d682c1c03c5911030701034010b4030720302952140c0380d00c683c0701c0114240340801800010410150b800c85030ba0040705051000802861400d0341443c0344202c0035000b802d000c9014400d10040146400d011104284103a6209206906181071030a9461310261011a0020305000003c82c0b60b0405208070080d070003901c444c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 876456348 1250 876455098 876455113
    0x10e1003140111190207060c031403060316080a0201090f3501050703090510051603020f070c080c1203090102060408090310111b030c0c0f03030435010e 67
    0x80d541055880c0200e105142c0d529214014208200f040c09004400240d015079003641203962070081c00e014094105105200c020010100400d91011040e5002c41c0a401060b607a511040300007480c103504014900c6050107950313404503445501049071001a40b00303880b09040c081d11000f044a0301005409802901d00c02001100408015003440c0f02e954010a14451104214019102e0960340d003240d200000c651143e9003c0b01300030342084a4010780c4d65804041200e81010300541c00317115110319440d4200b6801040c242041345000c812911616407054900d45d00b07d90301c001c0309885d0000000642c0c410000c10700c1038158071801200711006040141c0c041c0c061176640d5980c1c4c0c0f140e9000104010f825104081103602d284207140f0a081d000540c03000d0f200d0f110360041070090741c0b901c003c11040360703960028001c148030a0000036402c0801c55045903091104044180442d10b58000c60744600030244131000d920042c90204101031002981c83c50b030b5a80f804102c0c0224a090f00c030807180d60075044c0d12040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 876457598 1250 876456348 876456353
    0xc0f121806061505040339030c0e01081c03270b18070b070204090c090903030b0f060703090e1f060c030f090602032b020c010522030903330e06010e1003 67
    0x20300c1d0780000150004071485014002c28244c1f0401494104640c001c172031070b10030300c1b0040f51002140d0060100d14001c190503441031f0601e08014150140030014540c81d000f03000d8986520b042071414041882000c0540400c6600700324040020940351001c5181c0410240d006594001c1900001ea6000c00f10315454150f07580d081c00000c0038042c0301621064032419000c108458140a1440114026600030410a842e42d00700680b688640003d680f04d00700c200241000039410041440884544079415141544c426081c40d0312214080d144000e400d620300310200c0c4468009030070000450180d03694404220b90a00243c40b804420b0090310003583c0140071115422404d0701013031055040a24000c480b182180d940d10b401d03030b04600c41842e040d9442e40704010440481001e42c445040f00103080c05014a00c40d00c0c068002d5810340001340c40222803114074940c500c1c04030b214080103004281405107002c07041843d0380c000c101c181c0c440c1c0e18038043c1d2000000c1510200c11054040c0c490010f9070f0621034070f1075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 876458848 1250 876457598 876457643
    0x120a110a15080f07030e0a0f140f0708060109060311190b0a0309060b090105010f1d0910060206090c01080c090102120a0309020907030c0f1218060615050403 69
    0x612465201412031404075280d003001c03a0300707140c85519444081a60601c04003010000000901400c00c2614001c01625800c00c0001d01042040c3c00041c0540c4802803130510501e600081c2c076460f40940700d0305440d480d00000000f032000480702c20b60196011a603e41c403c0b2000d07a007091001802541c0102c801080c2c40c035150801c005040940c491000790306603600940c40e80c07900010f031040046940c9040c05401e0041c0f600805800c400c04407141d02080d0704041c00a046020307041a81d1040041410100c20450910b903214400c029000346201002d203480c00c01111a64858042c400040c012080854682c102c00035840403091416101c100240d81c48484180e5250030141c3d10b14114810b044031040400c4500d0024481c0c424150b40c042540c0c092030040c030918002c040c0040f02014a4210030040c03144e4000e24184c0030031423a14044026900b0b074520040a0034030aa4095005142443c00a08101007540000121502c04883c060300152581098556006511005c0c14034846540382c81072510743d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 876460098 1250 876458848 876458873
    0x40e01140906100c0609110301060603020f040303050f0706062c0412051606021204060e0a05070b09060405030f0615030a021507080f031504141e06010e0315010311120a 74
    0x844c40c0080d01440c044d00da84050340d00c0982d00b80d4040c141d200840c2c40302d090a00405c000382c1111700b0203600d42006d0402c0003000f88186d12000c0e0422902042d003580341840e2004840240350040e0701400b090b034031464503140395042071210710003000c3c1a205000c0c641066901c03103403041740c10401000c1e030010781000640d0070754001840c903c114155030225a00003025071024040e420241a40908039141c5860800122464900b490289610183c101d00000d10300086100a41d07242c28000c94403007200c08042911400b03503400869060068409c007820510b0005150f40c41402d41c960800509501c010515880c2c2c43d01141c040e41140403900800b035103044d00e00041507000d100c0d001482c0307081940e020f00500c070340060b0b5401c1c070202420b03601c40c0d2030b0703160500620f81e60003043d040d65051401c111810360042d40d507281104042c61303500c10000b01d07540e0080100b460103002c040c1c01d45d0000040c942e5070303981e41c9100340401c540102071415202040e0410b11034920307801d10510000c0600ca002a01c41c419400c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 876461348 1250 876460098 876460129
    0x3110d0905100c02060405120301150c0312060905041704050a06031508070605040e07050f03062e2003070201020c0108250801090c030b0a0603020a050717040e01140906 74
    0x242c1000d041d100780070740c0b2541c0d0001c4000e6010f000d56044c5450801d043c280410090000440244014408001c480d40c075a0071240c800c3c1015804807807940350a6070031001e0061144034880c40c000d0000340b0410700d038101c50322440c89090305065a0048018001141c066406643e42240c02e4640500c0740e6800b950001d01741042144a00500f1039a88401c1494205250055000194003140c00c00442030311041e040e400c4445818100d050040d500300742c0100703000041025201d104002401c0031003c5250003480040310f40e41c000800751001030140502041d8460541091080c05164250a100e00c08010b83d1002036050340a440304203610001110300315000b03041c045d4420000100014802d00303001c0060305101d1903850b1150b040d0300d1700d03a1440032503041031545000d041c00e00000200913900c40c860f0f0400d880d140c2c1001612500c48400455950003030810092010760080350482a842004000c0c100321690500b020400d85c3e00c44503000f8901403003072010364101280e9804140c1c2441d14040c54400701c038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 876462598 1250 876461348 876461353
    0xd02070305030906090a1e050933120616020f010513030809100516091430070f0302090915130201030e030304140106080d02030316050c030f1903110d0905 68
    0x45c0c47d2003542c0749008500400d05000303004a101040b0368107024a81607031108454550121414003038458420748000044480401c0c540345a03039a00703a0340c4500741c03595140f020b401203654030715000d065414091418a80071000d07201e106610564201c0c14050903225080c0c6848000421100341e806484840000e84441c680b406424450481c4e1125032003050320441284c5180c1c1c510040c0150050400300f0a41c1042007200b042c0304880b803868403850501915007840c03404000382d220340e5814004050081081c100300500412000151603a005001881600d000b200e44030041e46407850300c01d0b560351300300d24503550b2860003400059a50a1131400c410042d030041c1000b04429010360100750a56004850880d145aa5002c010248030030911a500c043c0482000807d12019620000f03942ca0000500e030002c0c00074a507800307079101c504c5041a60b920242d514110f0f501c4140d21000d0703c0064108a1384000c288100c0c041914286220740900c015840c1d800d01c8640c605881c3c46141000381803044026540c51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 876463848 1250 876462598 876462619
    0x30909060d050a060b1806010e09060609030a240501210309090501180c0e011b2603041202060606090d0317151e010206060108070909060b0c0d0207030503090609 71
    0x14414840c0d202400d210f13020003d8035900d40300070048201c0c000c01e010412424244200a00c03070b6000030b10009a88000c82e0303201d00507501c400002e5118400c91840680601070711141c01c0c204117003d01e02c800c441e40c00e032103103500124250340740c50100e800911414200c810501c280c0b003001ea19102e040d071481c1d03000f803800602168036801c0c51020b45400382c1c0b0000c0d2541000008550202062042001110700c614112100000680c0000d007030360200c2100f41d100d09400700c1c00030100048660030740d440702c050102d440009841c9000030812600101c9003954208a45000741c0444c034404504e1300d00c00c140042c04a81000e40644c1840f4228200320b60031418469a004034031100c05e011219240f14855000d1000507007490081405001e4090b10419280c00b1428441111140c0e00820001e88c002c1003881d08051030795540700b089501080c65800001201d04d4150040366a20a00340140383c441c0c807070b008842d0741c00e44035803040341c1e00c801c03610001e8502d402c10301907a2440d02e841002440c1c644c40c010048a02c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 876465098 1250 876463848 876463853
    0x50c030f0901021009030f0e03010605030709020901091203020d121812230f070f12050703080705070b0a021305040f061e14090c070f030f180602030909060d 69
    0x4551200c80500306045012600503040c2d030b0704100007400e503210300c20140107120a0ba940980824144560ba500340420580602c0d86601d0951142c2c0c0200300060480310180d50303591b4110b00962021440c180026118070300411785c08042504503400f80d90650080c203540541072800c48400e41d8442060224036105c1d0820301c00700101c04e6000c02c0880c001c440350200d14110000140c444540c090340c040010f4044e02c1c460b64004540801d0b112032060907605650354240506d0080d40705641c4646c001c11401ca141c5460003010340c0000500641340c4030b0b403100522510f4101c4180c07950b00804a0041004042c0340c006064049182c02801645200020119000e61110b000130203032000c0046a03140c20390783c1e03401001400c084002030300744010020f1040c1e000302d0801d0080c40c0580c40c030710348040c0102c01e00300c04954541510002c90f00d400e9080302c108a601a5580741c01841c2000600b60000010031810f480700f10030f801c80300100d003200c0013500190324212030301d010f0008048008003110b6000c03084c003200310301 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 876466348 1250 876465098 876465103
    0x323040b01050406090624050408100b0414010e040f031110050a050c0f040e0705040e09010f0e0606060909040c030219060f051e1812010e10090201140a050c 69
    0x558480c062110300c642c107140070f00081310f004d54442d102c8141132100401080701540345a0154103000a02400059031400342038819204a500000c01842041441e101c16129035000000e2584201e0381030054603240014884181800e0168031112800d10000c00c002420b24600f040d03220b40309007802080d5942560380d00742080c05207050101840d8952041201d0820f9501c40e0381c2e84420703c1c50b0f03440d00b018000b00200c15140510b0044444002d52007000c150654003071802d440080c9035981c010b0003d4601818401d020b0012341000460240c142042c01c1d00d00c000200707000c2d02c00d00000c1c12036802d2003802010000c61401c0034109030780e420aa6031000c00984c8544c2c92807400b4601c40c0390882401454080e000302060354612030413081120512000c103009035900e108030f51030441010342684070050304842c4032091100904966000b8110b240e142e00008041d0031400284405009503211094005184410f17141c04e100c00034009401803030b20360915407400d00500000071a45c541203040096840880d80f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 876467598 1250 876466348 876466351
    0x70809220f0e010e010e0307030f0210090f031704080f0d0603080a02010207020a060905300a11130506151b0d0206040c1502060f07230a03110a0f0323 66
    0x4001d81d0300c034900c2d402d8001c0240954014111004000c004412918603802d490740148130340107040003d04514239015920801010b420003200340d10812080b0143d00d4001d00001c0f0340002100030410500e481500211000090751189800041c0c941c980324032f80381d4039170484e8070181a17812165507800300803001c1011341026240c0b035823254000699507500e83c0100304d10344615501c03072170420144800511070382d01c48403a00040c0d518030003d1881001182c0e501d0103005121556520464410b2414500521140c803026490f10b840a8400c1a03086a4048150b41540d000302d56854120703105c081d00c0700d03c14030908001d240e25589445100003000104618600340340ca0203510b0401607000d58184000c1c00001401440140044010b140b4400c51003000a92034150082000041503c103c0014020070b000390110000c0e1400803984841c00325180003290b100d500100b0766100000c2c54211080d08100c4400c044880705c034044c5e1601c8100c0840640d084028100081d4001c5510741242c0c42e9040018142c8900e0303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 876468848 1250 876467598 876467621
    0x60f06030510230c070b0402040929010f081903031119020d0c02090601030c020c040e030319090206030a09080f0a0c0201020f0610030b060307030b250507080922 71
    0x1142030000c00100483c0f29481d0302c03141001103001c40600610b200d10804071445141d0001d9000483e40e541c4c00024000c2900310409054182c1d454203c01503015001140c0031129a201200e540076600d03100301040f0545a4007641c60503600030f0300e40b1000301039450b0500c80c07401e20a180c0440c650704440300c0c003040d94220003000001d108402c03211032501c94050000500710609440c0181d001580c0e600002d00704d24000e1f00c0c05061598400040640030710a10505410f40c50107172003401105000c0039043d64a50040f10082911100037401d204400c0c0c80d40200f42845400410040c00c5840e401038403001030688030003c4843d03003420440d1000e10001d01020300b0080a81d030b200c0429a141500029060a0004607100b816401410400504d54a1241c11000362508040c03401c0a03035454201080c54500a5007010b842c00d030307900b000c00c41819a500c150003020300c038a503000c6020aa50a01c20b4482c1d0141a600501500b41031241003d40d04101c001048140e032a038500e4100c0500403040c103400c0b40c0c0790b600300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 876470098 1250 876468848 876468851
    0x81e0f0703020c04090309091a03010c0507020315040f120908070e040b07080f010603020703020313090c090f0305100b04200307090e0402100819060b09210a060f06030510 75
    0x884041c190140721203000781c4801c0c2e4081c4811001d07590010041d40d001d00400d01c0340340c2d4810300150005800e0751801041000600201300465131006c0c013504070307080110102d210f0f04c118105400c0103804440303014011a40700344c103c3d400100582e60b400c48407590360b203200c0400c9a06d000c001092201000b84000601c1d0400041010f4109803c152100c0b0031300a001070180040842802200070f82005810704413100380c0b400588481c7d0500d07003241944900b1041520020200c50041048901640401c90114403038440784207a50743d4040000d005202e602c0302408079008401800100c2c0210f070441030002c04018000106003000d00d08585032030708100090440302602004000e40180c204807090090700c501d11041c0c0381d9180a42c005a1030156500e0f0000070080104003290341d080c3c000001d080607040310941401120b0303d4021103601c80e002801081c1c4140740c0f8002403140f0203001580110414000009098000135039107a000150540105444a07607640b0340d030000c0461401e0081c2c0c8000c0560810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 876471348 1250 876470098 876470107
    0xe0d050703080706050f04170c01020403060e011d120307031d06070801050a0603060305060604090201110303010806090d09030b0402150f12011d0906150f04052805090a081e0f 77
    0x10305504840b402840400241001028000404d24060341540300c1c0c6481f480c1c0e59035276182c00002501a000343d60000f40254100581c01000c02c0c0b040d0002d14140c848d40d485034182c09920024a6955250382412030100a002c2000c01c1c2803522030b8001c11100c1c3c4800a6400c4000e0034a5030a45c90448122400f00c00228000014000e9203091010301c8010716a0f4070782403040c281542c07102c5445103409011030f4865a9100120011a40215007071b200c602c0078075040d81d80380e6035103580030350708c07800c0c21124000340e402148040d0500c1c038000c0a075102500c0d0040c00549080e9034603424000c0c001c41000c1c01180c400e000b4400c1e0b0710303c400740000402c0f855a22825400031755240c400c50b4569034098100140e11490201d080008420001074220f9011110901c0c582c3c2e222007003000714242c07060813800c4680141c04c1a007005480d02c5101c0c40412141c14500002c803021986080c0c260071518140c0d0340d00c40343d40204800002060942026003410b1440680c81e04c0c54808090001d141c035444007404020480000c00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 876472598 1250 876471348 876471353
    0x90506030133083903240c120408070302010f0513151a010c060b0d08090913050d0c0813080c0a0e0c0702060c19060501090b0604150e0d0507030807 65
    0x2c0c250008104540090070a4145504003a04100e10785044100701c194405a0031510401450024854600542510010410400c030101c15000301c6018100c03c140301004500f007041d5120480d400803590300503005151b1110b59822807190b0000001350304640d2102c50807410040d00e4411103004c0c00144809a01e0020b0a10340525552151a11903009900c0c08904031300a04100e00380c0c034228442403070214001c03402d600c1c00d48003c001c030240d00380d0401101385d0b81c50100308508005011002c003c0f649145682d450303150041d610107130030b60010601d4000b02110405a402040700a2442e445001c81e103090014420b00400c1ca02c0407a8810041a0700078030181d103d90400c1a19400901503107201000649044c44106160788200d0340005c1c002d01d8001060280b44134248805010b4140840d880700882c40c060a01b0000b9080a00031042076500e8000201d841c3e103005000c4a00702c0d8242105500c0f84405004207985d800324598403160000342c216031034000a43c050120401943c4504042070301c590603070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 876473848 1250 876472598 876472691
    0x507080d151e090216020906060c0a0b0a06121205130e040c050f03030a2a2109050105040e040204090c08030408032d091e120a0615050a0905060301 65
    0xd502003ca858410400e05c401ca80c00044241502501580d00080ea0b0303c81c0c001140c2d244c401d42c0da401da018010002084204042c1351241801407a00c04c100740102c40d100c8003001400c1410b42c0004100e24000040c5580d240e0052001e05212108a810b0f405aa1364801c2c041c505440c045a040b03a01c00b2403a50103001a00e800404030012040540043d810021455006002c88401c1c880410191071441c0d02c50f80900c0038286107401069102e02c2c2d0505c82d400300b90080e030340042a080040042849140c0c003243e254403d005507012904500707a40200e58407150240401401c0040d4180c81013a150003002c54088801c00007000140249001140c1d0382ca401c0301e1402034140700c14000f4007808400d800c2c55080022a43c1600c2c06907104031014a41107010940d54148083d03102c134150340017040c402030303030410700c0c4007107009665140120820310070686485c0b050344900025008095100170b449030240f0103040c0340c0d440f4075441000600002009105603404048101c0c03000c6a20400701030340740e002b21840109 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 876475098 1250 876473848 876473909
    0xa11040803130f0e04110d060c081506032701021b06040308090c0901050603071206060e01021c08070507050a020a09061e0501022a060705070807150507080d15 70
    0x1101c00f440710143c00c0143e15485003401800107031541c0f865440400d1960740c0c20718107140306940080b00300584603003244040c100c0d4604403040621440003652260701c0b800c0001c2102c0c070440c880010141c10440c2d04500d09400103000c542009559800d11101c110350008185035045050399000400c1e0610f464034004001c42d2008011a00315005141c020b0100d4483c603100f181074079003c42e403140c2c883d41c4130201110609268907029841c2c41c1017001c00592a600b140c070a0a04000030303030075600c1c6035449a103c000441c1107a01c20f480085d00328030008034910f128101030003d20303118000703507180108145c000440c04229600031810b150f40d50b140812004200405405981c111540b120010505c0c1c600040d455141280415a00c91032102da1303080001080c84ac40c0c0110fa00040c007a07510707402d00d418015601c240c18003960016114001001c10210b2030716510002508241c0d842c1441d010762540e4105494000c0301c201c3c10004c0d2200c400d004028002d84800c00a403000c0c0b4000946e42c6003107114200c201e81c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 876476348 1250 876475098 876475109
    0x301050a0b041503050a0e060a0c03151511071706160c03080f1b0d02030412080c09060d1e0902041a011d010c020d0807030311090d0303050a1104080313 67
    0x1802c200401a0140d8164558000c180c075090000300342e03035640c81c10401703841c0c80c411070340f0507001e540104010032100743e000000d19600c580c1c080100d00301d20210300b0100c28260155081c01914035001c200840c1c03084080040e10b58048081e10b044079a6000c5521640c14200e6000304142c00401c100019103c00c90b6020030704110500e0b00008078850703034074042c21484000c0c1c0203401c0c90340a4070018000f00301c070080340b5000c01419595940c0d03654503c10410000c1d0003e0314102c074060f011800c0c1c01d01162003240c099004014a40b030307007407400042030104812a801114a1001e064941b06101c050748510116440c0c103841c0c888010444045900c108801c4075240c8403115600303110004014120f0341d200009095004010540854039071912006845401003558025480800903d04104120414010700000b41c800e403028460703140b000480d45401d018150183e85c00118841071100400c0c403030381010b03801c074240380300020b031001541d0600c48460348550000f081643c4005013072800d41051840354002880b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 876477598 1250 876476348 876476369
    0x203060106030c2c1201110706020702040f060e0c1c14040c23011b2f01020718090204060806011d0c04081f0b0405130b06030105090c0111030405060a050301050a 71
    0x2e0310382d01c0e402d13042143c880441d8043d80d1981d5601480d01c40950140000310a20541d1540b1044580b030b041010f94408a8101c0c040d80c01c0408a504000d0039001d0801074500220b0b00d01ca26659190284101d0f41000b030141081401440c600340e59120700b07204841c00c59042c0f2042c0001490582026114181c1c164031141926141d5811000e84158000b0724540160003443e010391100f080c0001110a01491400a000f90072003002c1000d04810800f00c01034116106c0803042a200780c0503005a8452100e8492a60900a07105000c00444055880481c02601c020400a81e182d00c13015542d10303103039090f04842d403588400740d4907241d540103152080350b2140300d14a900d03180c207045c240d44648803241070409000c0e184900500c81c0942c145900038104584001e0002c200d24034100501040c200c140748429507031213000c8004580142010300031544250000b030010156140c40400440300341c0740819255034140000d00000c18503598600040000b1081d1b9941e2a40f25410001040b0300c1d000180d20990501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 876478848 1250 876477598 876477647
    0x6020a030903180e061005070602220608090304172103070318020d0b0903120a15050324070507050307050c090f100603020a09050d0b0a23040803070c0203060106030c 73
    0x604d01015594424400e5a241c0c00041d41040309607010700480303600600701c0e030022403940e100e0600603840c1d01c4407990402207104640d503901800e5aa42c18166641420380d001008180140408403000030031403250031040714411300d0411500c107604004050607443c6524000140f0544a905002d400016140c001c6811002c10f82035000900009c08404014a40c100110001c1c980303000503c00d07a440048518040e02d018a80000c50340011720400c9103044032841301303a82c04100f0b4100020400310144c0c2c035451004640207041550b0307403000001013141e01004000c00c80580000d50a01c081c1085a203d00d00070b25101c40c0c12000c000030780c01d008046285840402041000c25044581208100d4040d0700340141c1e251150b12084900361071f10f1f04202d0700070700010541c0c020807540c4020700f8401d24004900b0801d000082030340095a4240c83d034400c50003010300c0045004251814000d40d00454181040d108116040c0d000c00e0034044240c1c0400d02081c0d650078400744541c1c01900c61544140141103081c0107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 876480098 1250 876478848 876478859
    0x7030b1008100b0a0314030409050708010b07170408120424050703230406111005101701090b010f140906060403331d0d090e070c06020a03090318 64
    0x499826421000d4855100c00c40c030340c0305071184210794005d150020060300603000d07500d18069503036005208464800d031400c8002503d036441400101d050b01c241106c642d103018103585600c1c41017080b4845400000204000005104074100140000017100042d00c030344541c50442d0f14120704c1400700745074030200321076211841c915501600701c85146a042c1071100e6800c0303c070104204800182409044d80f0800001d02040482e0400481554504c604040318042c0110155000564909a90000115526840c01c2c0548030303c510022115800d103800000c1c80c40c0c11038481015821003070b0b0090144080d80310050112a950594003000400c041d10649910b0030414040b4440d440703203220103082110b201c0741c1f141c0c8207000c42c0e0b05010440710100c03082240c0d40c400384071800240f0003900701e07090305809450040310b10200883d190500c690a600d4624940340740004000794014000c0101007042102150f000000ea0035101611440c1c896a03000120340d80d10746805410480c1c10000d084240c11104810850b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 876481348 1250 876480098 876480103
    0x5010b04020c070b18030604030e041b05042934030e2106100801060e0124020f0a05030418020c0607030f0e07090c080c0c060a0c0e060a0207030b1008 66
    0x444e100210030300d80e139031513040282c0360855102074440d078140592024001415406a20030320030281c11102040080c40d0f0a280e00a042c0901620901066041c4400c0219078070b076003c8050040c000548494404847c9050f807003442c1c0c031446280d00c40c02600d03000745829000324079070500e088201c41c10034021901140c401400301022035000072700c120244100076590400303881d45600c0c500c41d400304030344640c181400c100c0581d800f18010200d49601c1c28000042c130070305008074130341203508040c6407801c900c20746100d079020303600042c981c00298424845041c0466800b0041200ca66002e10040c644450401408032680e154404400c2c00c1c01c0c1c01801203203407054020036540d8004403030f4100004d244a070b06480d2030182c660700c03d003e09580100c071000101c00280d81c0111040c50000e03503030340700c565032001c224203003d0050030005007503075204200041c3c201e0700c1684031034422000d42c18214640c20000c00047c01a9110181040041c0c000361010070400c1801aa40740c1c0104060300040c85c03041c1850101507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 876482598 1250 876481348 876481363
    0x120117010608060f06100e03010903080a0b03010c08040b040303090f0c08070909032c13020702031c120e031611040e011802220501030b07111506010e0118090905010b04020c 76
    0x103100b41c00684d506c07802e17140207130700a41031100054020710008003642009040f21000312000d06c20642082e03000c800a140601c40c40f0192140b03922680b0031500c0381d483d081c82c1c03014010000c43c10b059440f014007000c118112514984144508c05801d0494209940c92703081c03050641c010350380703c0d0500d001e1100003070300004010524002100111108800c00c40004020340785440b1580e0841c0c484502c41600709041d0300100680750080d011940000d6070701ba9009213501c4200100c40000c0c91b03604015034100c10039004508100c40030030490b410468074100c0450807680b1a030040390400084034200000e03080500410304501c9001008100020b480d400000141032944030013031003031105d640031820f0210308401c42c54500d00481000c103c290384074900303190034020680d040c1000c901c000048540d08140000d03e50300302c00000c1d4003014281c0f2108d00568043c251340d0409418840940802c00c501854000d1080003015042400b185081207070901500b19400c01039828042c80c01000400942d230000217150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 876483848 1250 876482598 876482611
    0x1326040501050a020c0a0612062102120106090c03050a0e0a020303040911041e061706030316060b0310150b130611150c0d051815060303120117010608060f 68
    0x30b43d6801030fa000403400c00465685e071380d501c40c0c1d07840030200b011540145228100700761030500708841925944400307042d40c0b001d000401c400004910030310050501038600444000040300101d4910380700d1105500351020200c0000029a582041009041c01c5024500c050541040076288070340741500440d843c4d10841c0501a00e881c0c503014802c2c044040d5004440080c03035801c00400706c0b00c20b141e001903032651503071280000040584c08401001e0255030440f501800c130003401989040c01e05240401200d000000560300d2a81e42c500d13148454405000300c03440d07074084140000f02d90045c40502e140b007404c40e40141d41410303c1408140343d04070070001150241c842c507007080040c00001411092500d481c0040c0c0d00943c45903141404050820240681040780c0e03005000c1c00342d607039030070100046903035006104030705079000f00d1445028910810b0016003090020f0152860500e0380000048015804c0c0c0c0462021506090011103440081c1700e01405048a0700140440e0704202020070b00d00740000d48070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 876485098 1250 876483848 876483857
    0x40e13021816051e071a070f0c0f0f080309150a0b0a03140a050318040f020c0307060903110d1d040b360112021f0c170f031326040501 59
    0x200681c4034028004c414680054580c80d90f4941d5417502012162a610a045110b0f05030004101510302a103101a0000f0095450340b10500442d128800c00e0741e00b004056480da807902079040c010071200d02c0154801c0003c50020710f119a03182030848030120009048055146ca0005003801d69940c190b64141203e070018000e1401d0350415403000e0401d501c0305001003862000061000941c0c080d805015850a4215003c2200425040401080c0d104900d02260359420802c24071001400652000003030034068980090001d064440341d925105800c542440030072402145140f95002012150341001800e0b1000d00450300500c0108079842c964841c40001070588104026203512094000100102c4041c0601901d5035144620403103160102c00681c0251000c200b0409159950344078404c0e1120142d559210204603511407031a14180021000f8140f80c00700003001130300090314041c41c010b00c1c82c5203040d07800601d42c0c5002030400f24003078441034003081d100400d201c1c01c4805a06440c2192000e090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 876486348 1250 876485098 876485107
    0x91406090609030d090303030e0613032003040602030c0105010906140111030d09030c0201020d0c170f070b150909070609030b04021c050606040606090503031e040e1302181605 77
    0x4845024540b031564242c8202d001001003998491102d0381141d010307803410032040b402000c19580b50501203400c8411809035040c040b00003481761820381c11024044941c064243c5000c40541c4c02c650040e407081005078004100d4484a1900384201401030116001c1004000e20389010f8034800800821401e061100817429141100001d004560355049001c81c10401e4140601e0050242110f0080aa00511480b81440380403406003100e4000c0c1c58010324032180c0d80c4000031039641c07282c0c030107007038000405030500c20100040c00321f40e9501c4c000c807440d079110880f66041d0000e1280c140d034010320349a0a0390240741c0820916400c002080143da400407004409070b036460012a540e40314280401310211080388140003030010205003035010300300c103c6c0d003031044640d01d180440340d1a1050150342e0b0f02d82c10400c4040c1110358400024440c8407058075095040c82c0e82e940542200070002c580c00c80c0c00c811003507100021403900120940803451240e45a0f1040d0500c414003411112105003e00103001c40000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 876487598 1250 876486348 876486367
    0x1508150c1b0714060c1b0a05031606030c0903081603030219080910150509100b0c01020a1403160804020613080a020a1202370b0c0d091406 61
    0x242140c2001c00803a44810280e9056149296182894800c01200c000c001c2801d0303c980c503200d82180d01c628411402400c0501204407500070341c0708081411540006a81c1002582d900c050140b01c0d0810746544022006c5031400c00040c050301c500c0c5100c05c0c20451001c20500014401c0f030140e68410742c4004c20301c0060390162405070000d10403902d14845422518a00070405607100000903c00c80300001901d429960410310071017a9855001c4001c9000401c120a0100e4280203040342d41c0a00c40c60140f445095413460641400e510051075101c145e500028014030290308060780044031503429002902c2c41c13528440040035800ba0460030802c103c51080401c066640c0c0750300741ca000700700e080000e00a8541e00c500256881f80b52280c2207008414200700041e02c01115006182c1043c0c028103c01400c0032a4a02c2a503003903008500784da66014a021079549849020100300040c080303034000070b80d481d8841c003200303850b181c2c0540524082000d2001c0c1840200c0c0c240c1d03846032411900b511050380310103004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 876488848 1250 876487598 876487621
    0x13140907111207080712113403050616050f0d050a09080a090906140a0303080702070e0c0306010216140d0314070b01050a09050103120c050c090c0c01150815 69
    0x40890a004040108508081c0080e110007802080d03c900d80c0e0000d03600c140002a120741d10241f851003030315005005818100d03548180562130240000c01e04d403154113240344045207046c0c5070b43c00560705544044108565401c090200c0409182c440c00c1c041c1c20905c0300c401e640b184d0710074840c005501d0340d01c603404240300d21242c0e001358030040d41c00707811303a40c4805003004000d0601c0302a1040c445014101500040d18010300481c420421601030020100b0a00f10b45095810740f5024140808500c11070034000740c00100807c0f0103008003aa400950b0362400d00c880024a414010080100095100707082004007141c86100c850900703905aa0b402400306050078107490005a06007244107503070001849104004800031082c0c142c65044581e600744545030b0b602d10007150004d00006010380110f0000c0080030f80581da0120485109400300c40d00071080034080341101d00251804850801c01140060440b642800307400c002e442c0030000040810b00d0b0011096a8400c001008080000c80c1b01c00305d40e0540c0712 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 876490098 1250 876488848 876488863
    0xa0206071103100603080c011505301b01030b01180501080a02120c0705070e100b0904020408031909080a0c150915020a0b0c160605060a1a1314090711 66
    0xa12010005185d903810318410f6a4485a0a12515441d042d00c0c280c40341d1040e8038034016210007a012115403031403080c4034143c0f030300c1c6041c41980d8a54001188240b0040400118110003402040203001c491202e00140565114400701414090300c0e20310149421404012042151424030f000ba009444101d1810001d1150120324117506028034104904680103100800d80c0610590450380141e070384040141c9228000d40d914500070074020410045121854094094400d0050005140a5a50826916644c00054200ea04060071804019501d8101c606000144600c07800780031304e110a581c0741c640b0b0750705501036604094925521030150920030b00550010f01355010380e5260a00f038990700a90303070700f480900460350704c1100000a10a206901c1c103031004500c1e030103062102505140d4410340903010007060207410000e010000100300040d120604500f880384030a80b9070340c203004400318a203203000350018140011844220340c1e032a111081499442010781c54a803825460301140395061a01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 876491348 1250 876490098 876490123
    0x80904050a0e0f0708151603090302010b0d060504031e0207060302131a041802160f021810180e060c03040c0f1d0f060a121704090501170a0206071103 66
    0x4901003007903107020000c4c1d200e080e81e034401c0c01c5441601280000b61061401280d440342010303049420200c2890282d080065003074400d00000c590005000041003010080ea81c0580b00983c56500b4031040c981c0018400c030380715014040758401c0000c02c0c14013039a00c0001e4410ba001701940001c4807009507410360343c1c50b005010007040b00f0000384007500800070710f42c001d03006480d09482d00c0905a0880d5002d4421034000c0904e11155050f41e030b0340742d1900036180034003250998011101e428141601540603280f00e1007a03001a00041e083c9080a44038280c900c901122408214a44803128161880000d2865400b01600b03821541d00c1c2c0e04c602e000903002140e581b095203600e90400c00400c440d00e405811200b0769440b8044020706035074074118528607038815101103410495010040c81810096140c0002c9640036880d80040100c074035540e401c0c84d42c416442015880d6980b030043c00044600d411642000466200404401585030001590b87c40fa114000381040329078190350f80c2544003480030225400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 876492598 1250 876491348 876491353
    0x12280c08030301060f05040503070605160b0f18070509010b1308030307020309091513020a03020f07060605040e0d05090918060a0921050403080d0b0a03050706020c0a03080904050a0e 80
    0x6594a4003260380e0b401c20f0203200301084950100a010a04c41d005403011500001d0080196a02c0c00d9002d40f0a58080001340c55016042c1c4aa40c020034002022a030160004403800800c619040710302006004d143d0100007540c0d0484002000a590380b68082e80c151003820400d00d54501c481d00755460340030202d5020f80040d000c08410010000d401001230000c0b02d1040d24516090340e03c0d14102034203480200d1041e41d0148080c822600c03007000c20390240400c0180c60030018a440c5080c40c0300d5110350018039040b00c0740d5031614401c0c4200c0c10b0030f01031915004076450050080504110020704a170260145050181006900007800c25220074042c01c20301d4440310a0f5001420100b60013005030024680581e54007a151301000d0311411440a0f25031184410f070b542031304080c03c6a440804591006504104068690065010b980d44042c01080150f10400040c41e40d285010b00280c1440e01c00c405281c03003080b45179010000300c0c01c15021038a24082c12a00007800350356140a40e40203080c81d03403114101c0d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 876493848 1250 876492598 876492623
    0x150203030a0f0e150402090f040503190302040504090c050a0801110703030c0212030c090301060b1c0203061813060f02040b0d020702031e0c0f03030a0f0c0f06110909061228 76
    0x11126013a10b0302441c02501c0341110365840b5001c803003515805171002000d0351320400c811b01d50319242d030007440c8460965140c05450b0550300c4000034142c50f5030903800d0303070311413003980c01084180781003a550001811000c0083c0140b502c0d41c0107030740c8503008100c030180c207040d100e058211141d0b10038401200103090031b4251580720b08029400e4045900041407542c0a90302c2c010010820460040a8641084c0f000615072062400e180e2854080d420280c81290003840485078100e6940c001c60308a480388076089100035410b41076003403480a403203004003e4105184100000e2201c1380c801c0088071f6001800d1040560354030507610100c0c1c075225401071149901c800607400c42d40c50f084086400310015004450745a43c0d6828001015100d21540d600e0b500030815158a80c91168021480910464041c0c805050041b0301600d030740c402e1b07540501480710a03480c00900300140745000241d00b030300b2074000d07101d154070742c204c50743d003142e45422210708034600d14001024161710700208900b02d550b403980580b15000b01d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 876495098 1250 876493848 876493873
    0x7030e0601060f020c0f0907110a0501050915100e07050a02101a120303010e06041812020d03050f0402090411060d020f03010303020c1c110f0d0f0b01150203030a0f0e 73
    0x459402c00d040e04011700400131405a145440440705c4110f40004102041c1903d07100b1060700d920980c00c14045079030080708840703000704800388079040c030500d0340c107000c1c010000800500307481c40fa0700100f42c24400201c440b014050004180001c55103d0780310305010b40e856603601c030300382e00c0c11050010790b036103060801601d582520700741c2c00441040d40e02510068000c10001c22607586900090281c071132032000c0d100000d44280f030a17070003890380405001114014486684c5500140c3c1d143e5040b140f01592101203151a440d41c54842c240d840b454000ea20b44a0f4202940042c40c1c90602520142c621803101c1c86081d06552418111282d090302807030115070b248840400706d5496002444140c0c094060380141c04d107142406a61040ca10845000c9900c0c0c84809507a01800c282c1000740c01e07500414421080760041d183c2c036013803d624501940d01030380842c8a07440c084070f0410050300202100500c0024400f6800d030000180c5c0e800111051010030002c143c0c20042005000c1032413085428400c1d400d010f0382 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 876496348 1250 876495098 876495107
    0x4020f04080f0a03020d09080a1e08040605130510020c010305091c090e0f01030305070b0411040e0105040b0c18120c18161701150e060406260106020a0b07030e060106 73
    0x83c0e074440d8095030790302000914103480e01055886424101d07001103a0031000070f0140a00341e034a80c1210702003800d08284603100d071220f9801c6500030030007140c0c0c00102c15407031400d00312a000007002d044602e20042e45106400a4854036034801036818103440d100420822001448031140171025502000401d620f00b600090100c40c80d8070443c031030001402c000c60440800051041d06813600340d1601c600d0620b03c3d0b601c2803000700f0018420b48035281440340500c2190380d80d0107088203190300c0304008501c506007800e007462994009490030030240001c00c0808811a40320101c0202d450b03080310301400c0d00d11603160f0720741041c0e0404405507206980124284018580c0580030340603240e00204440c1c42c076506501520700403012002d41070403204600042011004c6a902001348204e246488203006100c9c0002c140b060b0803640041021420100c950741d800080e800302a41440720f11048003115500d401400b80d101c1403840da02403d940b855800050000c2e0103600002c998402d041c2c22622550b07501c400082 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 876497598 1250 876496348 876496363
    0x5030415021603080108010b030706050c070e15030606191503020408190302190c0b03090f150601020c060403020f061e040306090b0a05040c0e0711011107020405090706080604020f04080f 82
    0x60204d0700c8540085003805c1c0c14170070b46a40c4040a401000014149241902d5030740044281d21080c3c072429901182104041c0c80d82801514901c40d90781e44649440c0405050500090401e4081c044103207a110400c041d00c00e2480031107518107240d1000101200702240a0700c9240c0040701a841802e82e06040603078500e001030001402a07080d0741e124044014902a0f440d40713400040c1101c3c019680601030340c3c040200564001003d18212201c84080004040c1000c9210806402400e000c1301080340e5540c051245580d081001c851207480d05048d80d00150003080381c2528a4000e4802042082102c0401c40070030446001c41d611980d162650791420300701801a408003111b08140d0400411401d4603d80a22030066070320401240000b420881780d4203130070714000c00c07840401000c0716890520640a02c900702e03000030f070240c807190794403000d0040c04140e0700d014000b003040354800c030006c20100354840180d54001c1d004030703800340e40d441105800304914016600802e17070f9402092848420b80e8030008081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 876498848 1250 876497598 876497603
    0x1b1c081809070507020415081905010e0a020310020a03110f13090203190c02070f030605010f05030705060a0e0a030827060a0e01110102040801021902010b1f050304150216 75
    0x150103261200c014840305410550b1400c0201d00240001001850141c1002c000c1481013209005803554800c4001e141c6030010032a0070548174a000c030078007032000030302400407140c01d008020800b900c0c4e554042aa60b910902e184c039000c503030200310203e28620a400550200c0303501c00d02251120400d40c0c0384107035584011040700301e564818000061042c920700035288111703808204403454a884c072074480058030300001074008501407208042180b00e800c01100d00558001c200000d129070521050001105690b04000c1c031035817000504100c44d90703440d0121600d90b44c0310720700203050306c0741e101c0030464011441d08010400c100c041903444413003580d00c0e29640c4000c0810104030350034290300140b18840c4030305010b250008030200c3c00b40d02da0f54018203c1980c012008800149000c1d910000341d401ca0708403070103645200101c0c0c001c45c602d42d50b0900841d031045e0030441c6c61910380017824141c50724038800c200225090002c080006000d02200d40c280081d002601e407401e6540d01118007022038041d4411004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 876500098 1250 876498848 876498877
    0x7090515130209210d09060e040b010e040e0109060b03031e1309020403030507020f0a0513021b010f230c0a14070f03081b0f0409050c0d0e03130b03091b1c08 69
    0x517841e01a2281c1441c0041f40c0868658540350284002480040c0c000c4400d124103120a20500d02c1d03032911076200d4a0903405002000042e083c00798038100090350a41c0654a01c658410700807006000c40c1034012180072002c000b50103a82e10380144c038401c44400395520101e01c2c540b01140c000300780f5821400800109108403480101d40040c01d042041d000312a00827503802c040c84508000c44205aa80104034007c0001c0c0100e060300c0200d42400d096486003403034092100c1d1540c20518144040e240c03600d6024040c1c0c1d403c0d0800d45422445541a170003002801000c015a0071400d03288421400101c40043e904542e002c07100400f00c0c01c0181c603200d0181d800c2c1c006504460320000300901003605440003103041c282244e16003894802d040000d458050000303a800c650400c03c41d6136a40c0d2078451703410161100d801075501c03801e00c03120006960300c0c140c0c056034104104004104500700042908000409040854142070303003a00003184511020b5400c41075404805641d90091107044005000c1c203981c1ca184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 876501348 1250 876500098 876500113
    0x621060a090c082b0507020a080307170a0f0e010e120106080f0102090f1e1306030203060a0923030c070602060115021504030309050a1e03020709051513020921 70
    0x50882c0e0b107136079000700451038481d83c2c65a203015214000c1d4415030b01425190880c01d2482e20340009440c610154444041d41d40000b03007100030480b4851180d541441c00001680c100704810b40c010f0f00340d03c007008400c2d041000c01d80b01141c0d560f0099400d280f46420150814516a0f41410103a00802040c0103110052155103044091584c050084840014018085040c6880e0030f00c14840b8124480940c41d001e003950704281030302511980300212805142443c0820309a2860041c10b0070600c01030005100e40d8100050300c070106100000d4110303001d0341149003111301c82c0801c0b2041c1c1035004030781c440c9055000785480040c00d264009038044c16a0500560b118101a144006aa8410390030584109a50b081400100402e0090307000e881d9450041054070b044003004d940ba4000c400380e42e034004daa1040904444003e05074100100005050321081c00c00050038196401d50071500705011480c402c411030000d00d140e640b1660182d41040201600c409081d00101030600149004184000114490041e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 876502598 1250 876501348 876501359
    0x20c010305150604180b04020c0d030b0d0f120e030615010e031c0f0c020904120e040c080a0b06090d350904090212070902040f0e060303030621060a090c 67
    0x16000ba41100c2c00800070b520701490003002e82880e60403035102c220501d0b41e030800d00d4800c0d240d81c0002d003800030300074000d8550f4882049019084401102200380140e0440340100002440d1540c680e9100740c112800100c2a000d2800072a1440b6250910a80600400003401303209040d500c0001c003030203403d80703e031110b0301c01707071402d15558440f800d10101caa100b0401d8800e22050203021f840580201c0792074040f074410ba482d00403c020280c250b03011135919407920142820103902c418103c003c42030490f001d108808035400000c004a90183c10800604d6070f892450380540d9600d400c4901c804130151500c0c41e4209a41840321601010740d084c1000051200c200035444004d00c40b00342041c1174411240303030410820009000081c40400001c907008603241c0e200084050301045540001c2031b07410009a0b03600d003070910a07690018240d10000f04e400403241441681d507004030949601c50010741ea400307501502e80c0344504810074031040c103004a0060345c06000484110f90425184140202c02e00d52505a580 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 876503848 1250 876502598 876502621
    0x609020313030c021908100e0109052505030f06040201080c030f01060e0a0905092a0303030a05100b1801230a110f010f0e060109060e1503120a020c010305 68
    0x440c0e11a0304030034100307440c2000900481c42503a04a00151041082c03054444507040b0110440c1c01500740341d0f04c07149060402809602400400c0700b0054001d11400303402d582d54a949409087e50b0303101c0d0010081d007100e088600d03501c0d607074018031008084440344e03c600d00b000c40d224081614103a000900e4100040d2440480c041120f005041c818150441e581c41c04400b280e400069030b100680c880061400018030050a0090f98001d0510b100a420031421140c0a00c01202d000040c0b281d512005140003030059038040305507035020f501d00300b001c40d890b525070a120140720000c0d04030351140840443c0d10100700807604403007845d034102a25005c0c140c90038038014034140851524030f401881d5080019103000b81c4245a202c80340e40010089403001c1107001c8055094034442e030a136410300ba13518040392032146401c0148600421016400308501030504484403c8904018a0031039400070901549270180c60030800b42011203040395000303480307480006000351111180c41940d80040d0410010541803082c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 876505098 1250 876503848 876503851
    0x60b04030f0b09010b2d01030e0d0e030c0a030f0309090203010f12060912020a020108390702060a0503090f0f032205030609030a020f0f0c0603131407050406090203 72
    0x10818292080352540e46007182c40d94010030120a55403034103190703d1983c56803d0b03103040311800464440b0420300c1d00203800081d800d0907076201c0d04050030941d00b644290804601502c040c3c400b4a82540d000707581d0300100385050400c40c0365036081100141d00109005c0004004160140f0940c1c1d1003003000d84c3d4403000030a0b0301007806080c8488100c0c0008110400d0820b0440f1210b0b031003070101140d4122103484a0f04045d0030780e44488050b80042c20040119a13000f103c0a5101c500d90316424000500000c94002d003a084d0070043c00d21458010b190b0402401013000d4625a6038000d10166503800c0c00c5100420f103800c19200da10382e62280901001010038042002c000e3b81c00c19000460030700c02806021804204031084c01203500c049068041001d484c03e001e468850400000150b0351900d440130001c0ca0882c10303d031400e041da00025186509a4000714105d1300c0244111b50390341d180d4990480d0400c0a003403800008100c040d0b4400e040ca100500810300101b180d4080341c041240350b942d501000180d220 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 876506348 1250 876505098 876505103
    0x70312092c070302070f0218090f06090a0308100801050a1a12100218030a11010e01080c0a1d030303090a0309060504050f0603090a0f061b210e0c10080a060b0403 71
    0x400c0c10000b1034040c8654060141140500303081e2502080540200301d085444d6540d03400d450101404102c0c5c00d2404101d815002031441d4000e2095203070a82505407034524021004042100450100310103040a0400d1030150034020020092030801038141c0c1c00910078844151100211105c85686a00d860401303884204400320240c4940c4da02068510000e505c040071000700c0a44400c000181500c080020301891440f079030095545e40c00040004d400c40040d5020141017007034210820080516030421b54030b0340c102a090503860082110354541c0b0351510203c1498040c4800310030001c0c1c0090000c1c050708080d003c1d80356403071059201c5004803041c0c81117004071500304140d0310841090b828450000c44d484501c2000790b404804255035100f07003c0e8902c40302519980e880e20036860a113180e5140790044105d2314203141001c3e68040f510100031030780005200352100d40d182254100d020307052162947d080700042043e40180340b00c40c0042c0103400191107890003507160040200f00030301400d0484d000d998 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 876507598 1250 876506348 876506429
    0x907080f011205100c03110406020106051306030f15020403350301140f18040311150f04080c0c060d0c08100b0f030c040f1d06010807050d090507031209 67
    0x1e40340d03040400a410594183e0301010751f103080402d0347e01a0703c3d0142010301501c0c0e0000c5105e52034242044061000c070081850018030f0624100002552003031902c00440d0322461030031160f0600d9094a00a0069034000381605200c41815218102c2d80d41488007081c4e45111410130310814021200c015010900401c0001c07c0c40c0012040c0354a040394203140d1545005200005102401c0059121610300b03072421008201c0c0c00038288800c0c031091040b12800741d05880000e00900d0001a00c402c02c140261010342100800682a804820700780043c8803041707400381c01940e9074008945c0b903c3c01041c0c155010000205818082070101c208954084111080f0b07902082c200300801d0b10320001584007030003200c01180100030019082c4005d9035404014036041210751003444c00b2140d0360309096001420305040200241c10044500e41100507106c00403039040c070001b0141c510b0310f00790b40350222a8102502036411210000040c80d841801101521010095035178031441032441d807400810044840303800d20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 876508848 1250 876507598 876507613
    0x90311010524041104150f0206070504060c1509031d03010902030307081b0d0306030c05181f030b0a0603020f120a0b060a0b0a0e2103190e0907080f011205 68
    0x10030982d42041c624107000380000b034140e100035a04030a50f401907202e4400600192400030b419038111000a442c0f01d040d0015001519294138001c1803032003070b405a98103010314003100c40d041c032103c451017221040c5c2030801001000900c2c14064050038038224015801b15000340e41d042c2505060103401803507503000e002035040900585d5088080d4224030210b040280c40084c5045c00250100544400803940c0e40340010034500394104450780d82969040b050251800300c01c032024000c0303110840c82c0d008040c102210081c0e20441c10140c0034892581c400750240c030102043c480c0e4007600e60702070b2086a10888007071100010702800d00c03e08189034040e2209580142c0008004038011190440d80002c004100421950b00c40208681942041d80b180c400203aa12000b42c500d41080d110103000403841d03485400088405070032040d503e201d24082d1000a000070008198014003403000f408010300002c015442520300080d004245d800202c903250070309180070b8000116022055002041c5030b40017405400f81e07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 876510098 1250 876508848 876508891
    0x3150807120f050312010e0103020a0b03010506031b1c0608010c030b031f0603081b120412060b0402040e0108060a061e0501110a0534050f090c040503100903110105 72
    0x82d14001d01a80c1900003042008030a01204952a001e4100c149102c6215411130044c000b81c4210b0b0b03000165038000400061040341d5440050303c1d0f1265448200140d4042d40c2180262580902c0031342440101407601480c442074210340007182074070041c1c0020071200795110700c1101912002c5100d150140c000401100041d038070702d2090603159130841da011a240307980e6a9011010f0b4001c004644501401041e1000b1441d03043c4180d1920040d11040780d0b09141c180607800c100803521420051180f55101c2489a00351120780544c4c00038044650044055a51030b919651698400c40e400000540f510b00d010820810000d0b0841407450f135084007021040c00c0c400103482240c841c5e203107910341380300301c0016400048041000d1011041c001c0340075030350300200090701c00318502c4041801516807008170041c40316844a50452500721412144903403d0b80340c1c400d050803544134642010760503028001031014495100c0d0400d2814901c42d40d517155044003001c60303c9089075402d46040002c920b044100905 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 876511348 1250 876510098 876510113
    0xf0f0203070e12011b0305040b090a02100f140c0c190b030a0507120903020322080a060c11070e0609130c0b0306063009031306050307050705010c0315080712 69
    0x144200b816000081c82d1403443c00a003042c0060401704000242c59004200401542a149a40040c424801880080880c0d4005000040d003031442c03004000074418040c10f1540308500b901b621031800103010703035240209494603443d01034100f00540220710940c50466885210304000045803a01d90341030707086890300c206071006003002400d00010440303591680032906c61180300c2c1100803072181e00119550fa002803c2400104c242901d140c00e04036040ca0708022003280401d803000403950082000882c9941e902c01662083c0309540716070440c2c400c0c00004140c1c0c9200030b490300d0080000300c03901da2144d80ca41c0e10203c003851603103500400380240804104040c0c0300c9080a141c1140c0c006017060304200d000d40b5490044a212140503a0020181a0680d00724529920054000c3c2d1080003461402803581803904004910b446a202003100000c002010a441041540c807450790100091110142c0c00000801820113040041145610102d002a0499000400c03100310342c42c44c020500240c88940b40c140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 876512598 1250 876511348 876511369
    0x7080604201201030c210813031a040506012c0c0409110301090605010c120c0f0c09020901080a1b05030a0e0303090601091a150310180f0f0203070e 65
    0x8403194010001500e90030098466160440012016589981000d81107000a903018000a1916580040c40c0e41010b482d1b210034942c100c1801c5d551020000f05602030016550320141609944012520302c160050f142c1a028070b00441c101c801c5a62900802100c034500038000c1c03030616100101100301020701010782035102200007030081c10f1660b84c443c210161145440030a00240001006020350070481c461704000c0d00d028604152140e08550b0b9040300880340001c210207110600c4184420024440440d41840e1f1b807041d1000700c196640d03042c1030040d40240003110b010901c080300151481146200701c1150b41603035109403501c681000801d0f5403950001c0c026050113901c3d101c45016405c010002503010780341d1074000f082198035210340102240c400f83c42d11548642d09040c2d007012a80e41b10b0386207200c034002c41754090380c9489154801c0f1000a084e80040200f003800030b940b0902403101ea104e80194002110700f40136410b200c0c0600c0e0201c3c8000c49101c00860303904440e44181d401c0c4007800e0f1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 876513848 1250 876512598 876512621
    0x7020f150a0f0e030d02070c080105040209010b2d04150c050d0e03010207050f03040503070b0f040e07110106080f0705180a020306061e0403110306070e1207030609080a0906020607080604 82
    0x300d01004034031684c04e640c071a00d5008403258001428508115010100358002c00501000300000e040c540d00148400c071042c810010400004540b05041c80c02c11600c40034031402080d4520400d182041620f030301900544203140ea628100803450f194940a52040802c2d154803101070034071411404026242c00486011558156600340800e80000d0003c021941d081d10f9070b13100441d00c80c2d00e400201340c40c00000b42c105018a68080c0032040b81c2c500319209a900395254000307621090750798440304403181502c1040c83c030380542c00c1c601d0000380c0c4200400e0781402ca064000c10b40c0c1c007454840090100c000341400d1410b00f0718003806e002030903480345540a0f6802040050a075440c040b11000a030b141c0303d10030300da092410000014204108514140c40c010203140c00d602410040c43e2100014000e01c50b2041c51074050300220f64a07950518082c8200c001641c3e2000e02001858190b091154036608122280c00c08142c0c10700000c00e0761030001075541e200b02d016030751300c021544c0c0d680188006000b142401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 876515098 1250 876513848 876513851
    0x602031b03010e16020f070509071715010224060f1f08010806062205040c120b010503010b1206040f0f0b011401170c0706021303170307020f150a0f 65
    0x544002002050040d4001d1100c680e1603007103402e00101c800070900d01d04c94003009561042c030120250381404180c0104a072011101c0b501c3c1c80e62584c501b601c902180354a0920f200c1c01190400950382d1504140802010080e400c9644080341000c1a6080762101c00020001d0001000007882e80e14241c440c860706000094807001d035002000b654450140030012680000c5442000180042d42d4100300881c2c1c070840481b03036041c00c81034921160b0b030500710f84583c00841948480000d001d12070514001070050214004100600c00b603030420a900c44402c0c080d45101e03500300020241075190204101284080c040302500b030684841d238802c00000600d90003121104c49283c4003d011030359000c0104d000b0030140c042c2400300020040014155070403821414620900d2406004e141d18181c02a11465940842c005039940e04002a035944c425555100802c100305048004000b540707040301650003410b258088842e0300040200c03654454000004111114034402c00044546030280c01007088403405010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 876516348 1250 876515098 876515131
    0xb03040c05061617031308030604061e0509100e060d111009080606010206010b04051c0b0c0702180103080703030515042d0b030601030303020708041d04060e19060203 73
    0x200710983c01c07104114104029161481042c030090007440c801616075501210324524092a0f0940e2000340050040c064040c01310008809407a15486034014001048040b045200741030400d0319034aa05001f1280105010070200f40b00c0440002c42c035041c0c605043c110b00490b40c460041c006065003c12050704c6000058401c0c041e1600c810340c149024019030740d10310f00010306103030342ca620701040542424119030180004000b601000c40681e0150303001100c4e421804444400845004c00d83d910002c2c0155140100b03002a51400c08001e2105078803c0d142e4840c0040078410200c080c00c02440041d000410400c503810000f1711170780c08280c0c4080c8841192051001c0a8082004c9031a1103548520f0400c0c08494020300022041c0d00c402001503402d0103004002404011988404d010300c4000c00703041c0c01180b004104030091042e1400750a8142d01842060320303040d0030b907400303030320545042d00c155140c0a1582c038030311800300740d54401d011145045c42c01c41c0c0c5207965030340080d44002c05480600c0a03080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 876517598 1250 876516348 876516359
    0x71704030f050307060e0a052104180606081303021c0c140109060f06032001091502011e020315010806130e01140603070302010c0f11040e030a1103030c040b03040c 72
    0x115540d00c0701c0c092002152108000d19014048569034041da07401a803001d0400710008a00150704205006030700c86100384030500c50302d40c5031140030340c2d0000810981c0003480340e004151310391b200da400c4480707659400e0081d8441b901d0740c0501b01d42c9200040c0058001c0d0001020f560701a1200905010032072408800104550300c070a0120001d641c0c4822180e51680030550520915001c1c502c03980703140d520708025003460359030b4094040681070f5119000800000c0220b60b42da00503c44100100408000070714a1200024024001c0c661009140b0310245003444805108540d0700c2928032900e50220181e004000b068015504510000c00365544241300c1e10316160190361500524101100b0600049032030345040070648095440240114040c1c0e011440400250781d012084c2e200580e040b00e240449603509040c05401c2c9500b0100f001d4025040c040120f6401c40008018894000345139641143c400e0500c0603136440c4d11081d9900c1e44140b0084c402070040943c21402590040c0c403a810034903516640c0c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 876518848 1250 876517598 876517613
    0xa0614180a12050d030f0b0a05131104030f05100c2c03010e0d0314060102070303080a0b1e010201050a0c230408100522050a0602181201050115050f07170403 69
    0x140b0701181e450304a00403264405405028480c0ca240d06020184109408000400c50110943c40344611032282100381d000262120380c0030707021101c048070500f95120b8a900f0518480c000c0c0700e0b000c542d288580501001200b65500c201c980e880b01986e601103c090341c06606507146003100300d40c10f081003170f844003c000030b80c0c0c02d01c682e0040a1540303001d840c0310b400541d0043d0441d9010459003000a60032002c01c0102da0340490307040c0070f032581820180b42076142d040b4542c0041203d085c03501d4201900640080300c401c02c0341c030420980c0c542640240650743d079103407a520075244220301060114161184201c0d0074442d21805d9100c11121580d01c60405564182c090720f461100c422a828050782d9500384000340d020301142100c90740320402c201c0f40804441e03451540c1c4100864010709916804181c0365000300001c00c90703003605c40004048060003040070005034004c04c030a204106c000130708400701926050058055506a080106605040c9422600e45046407400012803090b4a081008040300040c141c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 876520098 1250 876518848 876518879
    0x5270702060105011803261608070204231602030d15050f030a12180801020c15060f01050d05090c0603180712081c1b020307020a0614180a 61
    0x8035802006203514000c000340012000400580400034042400d0001c560b003a1140c1d6400c1c0d18800c0340003264140d16500048030702444a65080124800400800313106418020380003250003120700700301c0c1000c000c441d80084084070303030b81e45440c510881c0010440c0d140f01c254001c1000c4a40107680c5404e0b01e92003200c00b02c038011100b0749010440c00794180000d04141c13040c4544020f00364004c080c0d0542640710b400e03012651030001410400806c901640c0c115032195404010714100c0e000b95264040162100d0f1921102c074100e0348200c0c027000c00554a85041c0d0901501140306031070741490f000c0e9000780306001d0400141204078620802c103040b40380c0c2c0c0f41c80e801917204800c0341c1c0c2444074065840402c2420981154010740741d0ba001000b242d07010034201e000302c5444c100ba5059800d04030403005900c1d4003078418042c402101c100445090452107401000800e6018422240f420219464503000e485801c230b5400904905c0740d062041c0d0070b039000c810042c0b03540804010181d00419980e8071010245450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 876521348 1250 876520098 876520111
    0x12060f010f15030e030d150810270f0213090204050a0218210613200906061c050c0702030606120a02120a0510061701050105030d0f031e02090108011e0527 68
    0x10003482000700420503c09c080d8600e41842c01448644460300403155408202c0060f03a103494000d0840b0010440030080c6900d109a01a0000a6400e115001c0400070b020a078410303406603041000040a8100c54401c4881c0c04060035140c1581241c03401c1030100f00503d00a40c86c246c104041c4c81032001c10000c00405100b07100c0f00b070040c2400c51840c44c2070300115492040620080c40a01c066400c45e0ba180c0103055440007040d030300640c9440e828181c5440034410020200c0c4140d00e00310500c20020b41c5100204803441c0294200c44c0c082d1a0b2400307000c0d0188100366041e8842e0003240c070940041ca403450590840c5a40081103801d0b121854a5582c240185221180c1d641603540004012071900740004041d2201c40c18000c104d90342c50000820b0f160030700d58000c3d40c00c2085020703c2c080c8480c02948a128494183c141c18940c61442c0101c100080d070004000c240460303c8100000b0321440d094525581e103c1c0030b5110304a0003031400c000d011a4400c2a082c0d5101007900f44011145c0880041140c0d01c0740c074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 876522598 1250 876521348 876521381
    0x3072d03111905010206040f020d12021e06100302010c0512160614091c0207090609020c250909060e030c0d03110901270512060f010f15030e030d 64
    0x1002100b00039a038508060324000c0c101a01c48100f040f41e801050b0180c2c4150014603904407440940f0010f400c04d0000e03500106944251249048201c0d0300150a41e0b203600340101d50242854095039070f50b500e52084410510342c400002040c0f0040d4821070460046501c920211ba2030030b01303d40800d43d51508141d4240b51403481c10b003500700900600f40101c440f005105c0d0102d42c100d0070300443e07494440304440710942c2000e040d1100700c13104d18070800003000140b400c0c0c2c1d02081003c0e140c00303500d0040e60156400c6c0c3c03064494444000040d1102c003240c03070145014001c5a6804030300d031201d010081d104060050f07410f030381d803010314031031000e03042c001004a00c4441020f00300c070700c01c0040c015048400e2035112101004080c4410b10244e600800d00030703039108030341d20505c80c000302000b20910701c8a071540080b07400003440c140b20340400c4000a04140105082c240014181c2e883c2c9101007101e20162290914915600742d1601c9040d00981c425414158000309692404030074948401c10344000c44060031400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 876523848 1250 876522598 876522623
    0x1c060509011503060b03130221010e07090609020309301605121809221a2503020a090306110c070503010203060901061b050a12030b0f03072d03 63
    0x10b5501d4131600e005007800070703441411814045010085c100c24100c000703000340e14842c0c030a500b040c805000076035200e807541c000340300418074880840d03104c100702c0c46050040c0c0d08080001c512406c4500980e03114014510041050b10b424803c80c001e54465809140135010a1810101340341c60354a0040000c5006c800d10618031104503d44285040c41186000c94120418044102100314020014840440480d8810b4040d11500c800300c7d6100c1d20302c484244101000440001081040070380032500c0e02c4c0c0700c85040d0319039650000b04015211200f550b000c10b0744005120104442c0a540038005944451405803c1241c0700c1d03030703088101d5403004034280745d03200c010030364022000301007000354003030b01d07080d00203508600302807002c00c49600c810700582d41400780d252041c0c1c0c20143c40f10088422070382c100080351080380050908401c40c91007400d12200180c20580000e1282c1002d0100c159441c00113001018600c0c0303020f501c2911401d076007106c0d003c59004079584201e80f961808044c0c010b54000c41da01510b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 876525098 1250 876523848 876523889
    0x80f07050d140402011107061407021908060702150708040327090e0d14120c21010608070c030807050307181d0f1905040201050c0d0306080d141c06050901 68
    0x2c440340c903520902640719587c10320100798840030707915942c1181a022510b651a6100048044045a00419030f440014500180e81c1c0800038040e0701a02c0240c0981e040442d800004500280c0200c1d48140410038180c0441c00092107100707003910f01000030000180c3c000c4204100c124044441d84511203407600c2e00c00c002108481403100ca406981c0030b05000d40311000c41405e403140e6000d02d055800c0c0e25405140040c1c883c0e44824125941c103206c46d408403e40c0c0a03004050316444100b170142c03000103034030b02c0005210b1a0250f0101500c45030540c803140600d81c0c601108884039030005015500308041220324007080300c0400c84401c058004291034003000701100c155074240890081c4000d0103040108107104020034103182000d909143e035400410507075102d00040e14548501e00850101d4402c4180e0714900c1c07035040d8042c4040d2a010341c1074840300444007500f00c5115241c0c2c101380a030b01b43c0410500510040403500412400001103010402035a2400000c00e02c01d800d92200102d05403644117441c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 876526348 1250 876525098 876525107
    0x71211040603140c21120f0408031b0c01030b090f06031606020f010e0303070909090302121207080c1801031d0f03040f0605040303120504110a08030417070501080f07050d14040201 79
    0x4142c0085c2019000c3c448000b000c00e5620000c4c1c4584c241d0000000440b4100222200b0460300600724210450360748024805200740000d12071840f100c003034000c64240700c401d5842405410401c1c80b00800400c43ca8031100740b00001c00d44094400b075403620400d520500501824440100281404e802400351a500a0340007403d4600c100c40841841d00100208100c842d04841100140c0304103032000503010f0100c0c54103a1034290381c400b02420745800810301f2071003184e40070012445182d0603902c0c4249074031034211541e1035014140d004520340d8060800101254403c2c2d1108659407010151901d108104100482c1807452140e1841401d400000382400303a0070a000000d4000d1003145000c91520b89152002000c04004c503d22070b81d100d883d00d020400740900d01030900341c0c040e80285a80e0049a41d0a9150758030b501c81e1140716800d40d000c00d20b0303451400000c152803044a406841d408611340d41c00400e0326044000034614024003800303200c55044a0b080d8416145c240c914483d0f04030a9081c50b000250 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 876527598 1250 876526348 876526369
    0xe0f090702151803070312060e0a0c020f15010b0f0d020307030504140304030201140d150f050109091109010f0c0503030a0501030b2503200c0618071211040603140c 72
    0x80321904883d503600824000304503110550149020454210009480c6d0050001507001d00b0107207a50780c2c24010201e8007a0b110740c00c803001720380840d004080440450303501c5240341401e0b6419036501c1e5004014001e9040006c000710b141018445140041c44440c8004a0304140c07104000a5a200308003c20001905480e100180c00c85004604061075540001c144c442c0c2d1110b504010759001c0351250310708020ba044580c224052900c041c00007a120310580310489040c1c03103901c1c0042c00c011400034038110302e8400e000c4a0704856440d149070000a1006483c0d01c120b0f85284001c000e002c841180110b4001d00141d0b014010141020801c4e524608001c01000030142c2400200c1c08070075100144000f64102510500c105824080f540c061041c031007038018010300c50880e1140100091288003a140450f44510501c00303041306903040004c2800881d514140ba010b0102c0b000d1100070321401080000c1107515406100400200d0016100d42c1c91283c030383d900b2250000150310404401d9110300c1c1080300711 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 876528848 1250 876527598 876527611
    0x1209141207080a300e0706050a1704050a02090a0515040c020d082707080d09050a27020f09010e092703040b040b0310090501030b070e0f09070215 64
    0x110309003212502d90014a00c940c10040080c0004521081ca01042e04040d540c412000000782092910755402060b01411004184024500810701e000c61014050000e544206909030707140880031415011a4040c0c0e03501900998031481001d140900581d94070300c00c2445102509400700341400c00b02c40c04004e000b40101c81511a0342403e2041040f5a07000030550082c08145c81c0c00c4043e900c074068074034010b0150001c0044240c406404062100e28000381b180f044490450031503422084d00c4070202c0d260059401843d0340081300c41410000c4130b5850b04044444441001a081c507507017400c8241c401c07a0b202480541c0190320102d240600ba40e04400107051040c0709580f45042440c00601000310f031500c07440b2060184801c0d02c40c2e4404140c0c07c10548015000e0703861601d07076494031180082d101d0b4101b10744030341d820040301ca40403402c1c01490207014100c070390100701112252a5180292038100e0392510454200d1803040440304190342d50b42041c0d0113100039030050b0031181411b101c001122000107120 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 876530098 1250 876528848 876528883
    0x1407210314030606030a09171603080609090718022208011d0d03020a1103030112050d02030c07061407050a0c181b0e01110604081902150403050a120914 67
    0x10041c3d03a0700d0300ca00700da5108521950000364016145042c0d4807808000300c2d01140f01801050300120509810001c4840074000d8a034440c20703a403288108900c05d14200c802044c075411580003004000d222810b88503a11107042c2000d41014001c60004d2021406100e6a070004240c0100400041e40e0030321941003c1200c2415000d0b0400600702d06030703516200144082c0405500007850040540310702000c1001032540c0d01941c0d501c1d69554a0a110340b403a0000540b11070007120505410715000008542580703040c0c401402485191140503641800110003400f29040304002d42c00000e4003d100c102c611510411420314100d04000015801501e546040580c8501e003030b08200c0310f01140c1117400ca10241d5890030809041e0208012240142d20030352035025403064034103120801400030301800860483d8102107140c004460070480e03840656420510386050181c0116020038400c000401030008039080400c600c21802c1e4030300c01110300459098035450400c03520481e00c48000d0190340300130f0809110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 876531348 1250 876530098 876530101
    0x60a0515041503110a03210206010608071b02120102070b0a0c020102040e01030f0c1509051026040302031e0403021f1205090115030b1008010c020a140721031403 71
    0x200b100100072808080e00c2d02d202c4070300040701e955030016008080c0d40e00c5894032000c000450501c060001003040c05da4054020038001180031031040000c184606034a135a80400d91440030400030498191130303820b0741c002465100a0324888003d0008201302c07849284001074a10300074100c0030031142c494940c00b045900400007002605420380c142415643c02c03407090a800d90242c5018070342010715500080051031010914900703d80c101d8043c104484060f2403060b44407010660456100d5643c00c141070300341050340c6908803070b4049110141d51062080c0126450620170607005406c949501010102a00000405004508180c9a201012001c015400300c600d050500c0c0905030b0321042c1c03d40f8031825514400075480e454250089180686d0150805615a44074140744a40e24411508480c124000d00000190f4090510030480c02c81d545502500704030201344c0d140b520100f110260b8040754800e8400c007003448940100d2050b0300720b0281170002c1902150340741c00b80003440c420703d200c65040c10520 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 876532598 1250 876531348 876531371
    0x1103061003030809011503080706051b0a0804050a0804080106050f03011103010b0f1e040e130201020c010e0a050406081c020106084b1506060a1b05060a051504 70
    0x10405000d403541810310060b2a52802056170062104004101504030301030400418010044000c002280c000c00b0103001590f610210500ca001c164080c6200c4064108101d20380144030304c4105410600c45c42c182e604e001200c1d2601030721900250880c0f98142d640385010006803401000c1d00ca6140801c2c3d00034000c0703000c10390240b2910b010500c117002c1c41080024510501030344ca80100d803294060707200c4140c2048821600303c0d070b150300300e405120150941c0700042586908082600c0160030343c142d009010307040c51310340111800a44044040c1d004440c0010105481d956801860090a8184000c01d00581c0050b101120941540485030569141c820f040c0001d11020030040d581484001108180c0020319415200441c151070004040c05060004806615011008400d1485151048580c421840e500450206005541095100004006d62000e285c00340030703258914100d407034844141b101e0315141d160900710100c5460049540c0e5000300b002c4d013100181030002802041e9410840f040242c2d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 876533848 1250 876532598 876532621
    0x203060402120304090c02160602162601050a1407050408060417070605130606081212100e040b0603010c031109090c130b07120c021503040812090307110306 69
    0x50406800b071007101100c0080580100100d0340108020f00007088600301c0c5030002910350f280790703c14451401c0d0000000841510000e4641007450118445150780d82c034000340b042c1004d214801e00f0710368410b0012a40742c0501c00784203440c4106004500801c190f00503103101e507101e2400a24502c02d0000070300c018801c1c13401c009845e590080d030006610300d408241040486040c042c041008060074109800c22800f286150f40f00e9403100d1142c001400002e4450942c982c5680114211045d100d80a00107284003080c0d0443d0280c101180842d440f1750291241c2e81c24140c00000c95068440311741d16000e004440c00e0900c03680c550208580f03820040d000a8062401e41442015107091241c3c51410210301d13003003492002c0f80d2841820307203c4244041c0d0b9401da607821581003100b0950380d08103980315540109014402003004140d00a06610140b410142c1d90300c000e400240083d00c0c86641444041518074a01c46800d002d529044c0c000c5803175802910388004205002d0240a010342c000b80305001d00d11090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 876535098 1250 876533848 876533851
    0x40b060d121b14010930121103100f0f050f100215070c14010c05040315090f03120b2407030320130821070503090d0c060905030109020306 61
    0x45240180701e04990122401c8810b007000710103000d808101d030101e0f09140701540020b0040b4410409162400307024003400d07108a034450030480c2c4080613615001c4506202d0340c0204480c5c2100c403400038811207202800b034903641048607200240e1500c12020301804062207001d00080c0302c0604540c4085060401003203a409c1c5e6911094044c8400715810640075009201000d9840c002e84258201c03480d00000090410031050000d0341c000c604d54002c4821118180685d52000e50640c540c1231900d481d603520241035500007511034551540d20606d1000040e544410380c9420350280d81c41c007002034510340503070089600c0c002c6520720550a15089512003003c0224410f103102112010380c0c1c44001505054020b050260000101c20b107240145801c03030180c001c09030000c0d40d8450004600d10b51281500c640e03824000d0848081014111031f0542da80b070380b42008000c000c0c800d806a908184040b030100c0c620070144141102c0105030741d881405140c1d40000c07200018001100244011035040d00441d45400c2c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 876536348 1250 876535098 876535133
    0x50a0f06090e0c091e210604020f030f0607020d0e0f0f0405060f130510060801120803180d0e0316050609060309150a060305010b0105120a150815040b060d 68
    0x6103080050b0000d0f4959058070603000010746600280700092900460301815000383c20321640040c8908200000c00c0b00f0000d21022402d0005c010644a80d002c100c0c0e505030401d0310b5a4144900003800c0300084050007000d0081a05400130002200c1d6804060454035810f40241e01404282c201140ca59413032207002a80d503030b42914002020340307625010444a0001c1c41d420f9800507202402c0440700d03482c0d503222511820b0722009101025072510300c1110000001c0c070480c82c510b0000100c1d20b0100344200000c0d03810056001c4080c10300503400361964104085880100041001d0407030510071800c0510140c80720341044085024020b052600007a031500464013400d015000110014841c8802002081c0f02034145001010742464801e5070580549920f0004480c075500301075407c0915400381c410303246860610b040c0842c2594521020000620300ca80d555000d00e03c000c0700011b0805414032000f4420000e900b22025540760605203031040c0c01029010700d0155040c90018808071300c00701d5440d15000e8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 876537598 1250 876536348 876536369
    0x11a09030d090305121c05060112020c15090304030803011505040f0e090706020c03101107021c110117071b080c010c0905090c04060503130206340305040611121201050a0f0609 77
    0x13201e00f0300494ac0018480d82011003c0e10014103424103c60003c1c6000040168402c0a000c95403007001c031039107900461000800d0401e00f8001403021074081401c100c07980c0c00e40d103081400c090b42c0340c0e040481c007003141d801940d011950500303200300400b0900404014250300e00080000b20742e80343c0448da507034001030200750800d59214412143e007008802104c1c01960018550301c01114090b011015410290744215450b010b009250840c65000385140c02100c0f8055070b00716035075955100c05071030840054030214000b5031100c0c10ba200144000010300b00260040000180e5900b409a0107070001910390406445035502404100ea8010907100321000d0380c07850701d817541c1c0301d48074440c5503603010f0f00d4501b0095010300081085854074840c0c1c50350380ba02c1c41480082d115070707043c100489400c5000900b0042e0016100700410301511b40500b40704d490296180e000c80d2035400703403207400c0b00c2d08d070300008000301e04148800c0041025250a200c0240a4403901121001142c5131010180400300c1601c01d610005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 876538848 1250 876537598 876537601
    0x5010e100e060d140a0506030d0f05180d05060103030216050103050402090624070305130608071e0e0409080d0e16150c050109030324030209011a09030d090305121c05 73
    0x203030816101081c4504251303c3c282800185900904412078010b4000c5c0b00d039081418500e07201c2e9005100039000c43c5c440a00e80b8002c50050301c2110a034030442604000c3c005040d60000c0c0c0d04000c071070f0086021741d01400c41c3d080c1032500701101510551015041504000c107000259448102c455044034048030b0f51000d14444000a100ca400c020040078103016021400e038041c9a00310006110140c0301c001c907040c072183c81c0c1ca4150764a00c4240e40317440019007541c18481d42c0d1021590500b0080c2d280307051008803400b4103800541030380c0b0b01410484164801162940f8040c101c1c0c02030594512880014106030104a07800c2007109985110710680548500400c0001a018498010703000e5049402440800100c0c100a40589240c02601c54015a0004141d10a144041c010f20589034014a4201542d01c0c04401400e01c00d90040308003114181007009100300d83d820811985c01900546800a00303506c7c0d82001424015841c0c0c0240347d5800800c42400c1000700c1c2c840020a0242245000a05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 876540098 1250 876538848 876538867
    0xe060301140f10080d050a0206070801060c110103021c0b1207030f030f14030108010203150a06051e0d061712070308011e0e0c0408061005010203030f0a090606060905010e100e06 78
    0x100050358080f4001740221090000758607803041c01089540c039140c003100c880b0341fa00c04c400c0300c40341024402e071070004492150f404002490261040d801100500d0007508085035001400c00385c1d42d035000b1408880307079565916001070406001b4242c000076003001908030103255481b09521384842c000003c04100314404010035880c000d0b02c0d41c4024010014a641d201d60f183d01c0400c2c000e6100b034a03c042032078131210601c051071030a10200c5054844a9450354142184041181c480050000f020010304038140300c010b018010900c42c10f0001c2c00381038205402c1980400d1010b0620205000b540c0700d03208200002030109030810200c0d411104442030915103001012504c0d82c59201ea42c0102203c2c6140400b4010341c0a207220290013078841d12000c0e10b40544840c0c0d15121030300d0710380c422280960000d1000a04079524401c885030702c00e000b8080461b08040d079942d21000c8845680003080403402030a0240308950703208980d90320116040c1c0d020342200150700d002403c01c4d1217100502d441480001480c07440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 876541348 1250 876540098 876540121
    0x60503060118150311040b10140a120e03090108130b1501030f0509071a0702030a1707051020090d060507020c030601030c291215060c070e060301140f 66
    0x281c1c3d08007000c028a903180e14009510407600c05280f40701c0d0341401142c12051801040c0024401c40649400c11294081081142d558102480c0f00d410b0080140805030b0546a41c056040484805c101540c3c3c2c0300803a00001d0040000a0a00b19103062480620400a0603072600036030050b0701400314003400c2503020300480240070586801c110040c00c1c00300780900c81e00c0c0040c0c040180d4928240908421130013104980c400e0082601c00f9501d5440710b01001c0100d81d005030030a81da56000c880352031a291054035164945481e5038040c2c040340e541c038004071000003140b2080024500d02e014181c1c1c94410102d001076044645c61001030b082c142d4076800714503014020400d15141e40c401505865956a490030300c544244010b01c00c1803501c81191444414404100c00036142850350404080e0038255100300f04d55140314000c05442c01341e03000c0110304869a8490014110920314500206129801c00001115290700508402d019a042c885021904441000e1140d400082441002e40c42da550a10288 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 876542598 1250 876541348 876541361
    0x306010f090b400801060501230d1107080307020d08061f1803060203060414040210030504080403061e06081c050d1d030309121e0d090506071110060503060118 70
    0x40d43c94545080b4101d1800201014000c80d4006402080703802c2c1e42e03400540d110303c0e00c2194001d400c3c0041049040c24251034010f440003403201c0c03034001f90030f48034422002a250302050b4140e030030550210800100755810040580c1c0c001192411062608201010480302c050030030814050b5505804200107491081000c0c0c0d41c001e0307100180c0111542c0d00c0c1000c000a40c0142d0f2782601603402c0010000c1c181e030050680e540250b43c040c0000c024007184074401c0b401000094402c460880701000b00001249490203080001c2110703090035901e01d0201c059220440d9216803140c843c1e42c22460b65450402d03810822076103d4000ca04201d50b9a5210313000c0c2e08018a10203080d0114050689051030042d0000406103200f2240002280d020300d00600302c06450780580e01e402e10480c05484181014480e1141c00780c003103000360b00004174210503d0354400d414007030211031a4000076000c00310494814401c012003108603110110800490342080e022039110281405000340c0b910b00391070392001c0c1d243c0c2540000e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 876543848 1250 876542598 876542677
    0x10615030c171302040b101418040c030e0c030d02030a03020d110703091d0613090302154f140316030e09070905010f02070e0c0306010f090b 62
    0x1580d0b00e1034080030b03031101400380f04001da0180f441e0408101c0181411000303148000e044ea103e9043c0b1169a02201c100c0350700019600c41c0740104da0131108200c5d01c403406054001c58403510040390b030801840c002c1d841c1c64038003101d10b8407a900403440340c00c20701e4020045601701c075914030300541d075040c2001010004e00342c07185a0000d040000a804001d06501c020180261064508900c0c1c00c005440c400c4401c2c0142540d43c50b43c800419164117844c00c41c540d121112051007401503442d0080300f40392080304c41c507044818500c44c01004000030310340c000d4202102352120f60360005119600c0a540c0300103a524080080a60303400f80d0b100c0003400e000d6204100c82103c00c1202c2203a6481c032907141505c51f42403200c2c4044012800180800445203040d5484030b108104554441c1e854a103403200460f4030000d41c03401d40095005200c404950010641e09031445140744040d126541d060001c0018401c0040c84610700c1007040c058003c0c004042c0d8001181d10740d0410520301e40c4900d6026004644019003d0300e003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 876545098 1250 876543848 876543887
    0x618010305010504110916080411040e1507020d05160c080708010f05010f0305030702130e070f1508162f01090309170a0f0602040b1614010615030c 65
    0x801c101054020307512851041101d0700912440c2418410218425655440300946c880102c078035203842144101c3c1d01500030100c04c183d41c100d40004c00c04403001e4040c0056035810007070b04030343c054804c4100d00da00240d8510090100c03040d80b000013045030091204000032990030a01c0c1100b44148484d00c10050f010f0141620f842541d901080760013070680b039401840c1c160825000150700c0c0c1003032074810110f80e00207014529080c1c1c0366081042c070310140ca8004800b1540c4030809500d040f01009000054404804c0107668942002d4034410b20341c201c204900204a80001040076600381c0046050200403181012070080c40c0503e4400d040305078601900c05210b20a41e040504145c054022108039402619a07004c203603212804046c0c00c0e1040d080440850f8000f40360080000c1041c0360300440c00d8003030701e80141040c3c0c60390031201c69540040089200c40540b0030160741403211030701d54011040b040400811000d441c10066400e1400421034540a05548181c2280c0813070040c00d01c4005507410440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 876546348 1250 876545098 876545101
    0x301230a1a040816030c290f0406030b041b110a060f090b10080309010509030c0301020d0501052701060f0512071206082b021501142d090618 62
    0x58a028a400c184143c900903c0f4580c2e00303525840b001c9aa08007581e0b000901902d83c80d0421111080b41744d409000f1000b041c1d5000480c1c14410980070140100000004402e552240b80442c02001d543c10880c0340391140d403a094000c00012444c42c0103017800c1140c1e080180c00403034820441c0b4204603001402904050034405954517102180d8001e90703015210300c0d40800b090302d4115070840c4582a9000d0000190303c100180c1c61298025006400c15150041c1110403500303045001c00c2c01e80e01711444662440751180d0041c0050701d4402000e080038195409950003120003010201c650a006125100512043d0b200d9081000c0c4941d04031541361844901006050800d20002841c018104510302c420030f180410108010001103407003507001c50752054101721440707c44005140d48035008a24415446079004031804c203031114800600a1182c08241c04510b40510140215428800d12044180c606000100c0990f075504481040008040d1500d490720754801001c61a1b80b8545c503030103841d074204e520 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 876547598 1250 876546348 876546389
    0x51e0d0206071707020a140d1119090501141008041707050d09030303150501021c20010c020c0604062123060a0f05010f0305100b0703020a06110301230a 67
    0x1c00800002d40309980d2515002c0e82c545c1c00b03500012901f481154403290301c0a091001c5090070a0180e22448000d0071119200e4441c280c0ca8003129003507002030a03054072500108850b003a501025070001401b07840200c429490380c10004c0c500b2a00034401840b5050101d0016038070000c0e90181c43c40c072584002120b82c00f5600030009010f44160340300440000f800c0038010107584cc00546100115201130700242400c80000513400c11b0005800d91350810412029000d00008000040c00c0191440403000054102e04200c0000d0516011101c41400341c00d040008005c400d41c80300000c40d001020310f01c2c5412250580c001c02000d4001d03a049958191700c0d480440a074504d44140c100d01404003240c2074032002d950b640d0070b1248940c0500c9045e010480242c20210311078000d410031540019003006442c4213646400103001a40c001020550047e4840700c210740801c0345620a080d103619810140700c0c00c540c50254200b0f03544828661400600000c038904281949030840792401500007200a9482c1c01c1104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 876548848 1250 876547598 876547643
    0x6080a0f0f02073c110306070908160b2a1c030e0703050d0f0908060f0601031401050604091802060307030915050705030414150718051e0d020607 64
    0x8481541c00c29035801e5404243c00c040702000581d1030226418007005140c20180884203c4400b000f0345c0c0d5403000310740704521581c00b4040380f44101203d454040aa03403c250140b4a4a0180d506035142c21101000c10b02503001890140c4003154102040c2600c0c592001d804601d4061000032a80c00500c62020301048413422441c490012101e5950200000ca20803803030950390792060711003d807940d00103019018030540305401036121560706040014403941d482200c07524000781103e032100464841e8080c03000640e854001c0300c0c0c091881c034515032a194100000543c45200d03130300c80e203210181d451409803901d6689034a450300e5a42c00800340340d16840d04c018080e001d050340d032000b141d40040c00c00e0310a2503490544500d602074a40d5a0b074040c11540c55641b80b42c66510015403110712445000c403201e20182180b00e4152154000b0303a6110104c0d10f000d00084000300e6607800c018407030007884511240401d988028104202c0e001ca40207202d0706214004a5118404c4290191207032015204005031102c02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 876550098 1250 876548848 876548857
    0x1006150f030204030b07030c050415050405090a021e0d0f1410120506070305060d08030721060e06100504170a02090106030c21180b2e06080a0f0f02 65
    0x64603500c030a1180a60214201e106900004001001c0503010940d2039100754051280000b6908000789020744840400032691202ea00303c0000650000707062081e03041c20b40030145c000841c190158205400d0824040d201c180101c080400e1201c00f107030245480380703150071505d080011001c040207402c15001200b690b03410110750090000b4128400001da81c08410200d02c0b901d90441d01900054807040011405030001624007075020140b2806800410307001c03002140200795548610141505510f01420744080d100701d0004001c0c92b00d0804c1110b4500850021360004080f039036411034031401c8405480314090741e000300104414000511007070101c00030b07800c1403044c02100c2524040e130341c90804030191102c4c414030130009000c403200800e2941c03461500d206c540f000c8641c0814600c201c44130381c400306068076000f510f01c2c20071042480b45800f1508a0304140d00c08030a0700e90780600034500242c103078400718400c1004111032000005e004e0b0410b40c1c820b00035a0f1945070144181007030b0b60040c01c044d410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 876551348 1250 876550098 876550139
    0xa08090d050f1801020115090c17010518040f120801183602150d06291e030709090507090302010e04241e0905071d01021006 55
    0x40c220858050034081d01c29500307148403035920946071024221010803088804901d2a05540d20360018443c1c00d00d28220000103046110000145030300d003554004c151880441014031134403e428018003941d290342d42c282d620000c20038100105500e4900e0b1010007445a0740c006808400e02c0010704100a034006010340c121345609040302d000301124400c0404a44d40c04641e196264040030290304481c00180300d4100858510181c0d840c49281500031640c0032802e0245401058000214038080a416120700ea020304a0250701660001c20030300804030658140f840380407100d0300421111104100704020180b802c50f5075102c5074590a0511019214850a018180d513050a040005002c0b03885042c10108032601607682c00a0001200e0034400100b852900c1c6609907824a132500414110b800c0b4107800400421851000340040c135403070703494250426000401e440381400b00b44194994030202ccc500e41d11354a18041c2e14004a00c400513841c0ca2494039001140909004000604144000f240315000e81e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 876552598 1250 876551348 876551353
    0x60e10090e060108060d0c1419080601030816080a03050601090509041115040b040b070303060501140f0906090d050606150c060408092b05070e01080a020f13020a0809 73
    0x1210201603603229014003070405030305162030000728250321400c807031a01311001802c0040c1644050b12001c180c41600d40050315007058020f0045c905080c107040c40e0600700c49082c00d060129003416541e58540310113101c080e100c507001040d060904008007006880c03e40e800408240d03035000b07008026001e468212001804940c42181c00101d5040090200e44502c1d4410948581004410100320307244550300840c0b004034106100104441540780f004102a1881d003d9142d20390030140382c01010345102e5042745040040c201d40300002844070300280c420089020412546442240020850078000d8210450f4000d900d41031050a02c64007180b030901618080e03c1da403250030701007030340940b4500c985a0f20b411356034400000500031842072005001c051800402035401800c24001c1501059401038065000c0e20103500741d0402c00c83e00300189002041c0b401842925980b503c079070079480b00a00c09020340181e560722074040300c0c0d9171130810000d000c1c0f010b441d0031900c45888420040c510141100c0b40c11051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 876553848 1250 876552598 876552619
    0x71110021b07082107150903050d060308040503010509011806020a120903051b0d050706390e03010c0914012f15100611030909042a0e060d1407060e 65
    0x62591300032940741c3c0d82c1103921040c01030490755a00c001440790201c19820080c06015148040751140200c4004500501440c1e88036414030041500f1200081d11124050380340c941900310114202d24402050760b00140010b071500b0544000380c0e4180c2054641030b05036841e2501d00030405412030302914400c1c0c1032186840043c040e6204107034ad500d09115400022130b205020f03c00010b4401d4005640d00c5590740d000c204620280c8118580290480405039038121400c540800d021b980043c0454440c04110001d01c0700344088030015043c5030260141c0c5483c40d10301e6210203500d0b40100809401c0c248800c1d0b4090500308540c000c0780c03000807000111074060040800c83c8002e00c000468050061190810fa0540c0394a000000e503040c00a803d815072060001303005c825001d03542c0d056101d2055000310102d444071508108030b400100c0c984100e48a0042c40d000f000d1114862121245030311040507600c00c8190ba50a08042c4825a1551418140d1744164440840c0499200a400300c0c111420b64100822 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 876555098 1250 876553848 876553903
    0x306080c010903031b15050a0203090d03061409041a15011412011401090312180803030f01030803060a030c15090605030412081b0a03050f071110021b0708 68
    0x14861600c0064005084015000c07113859030003c0035000140700f0000c0440c03074000340a084064442c200c4420407125070200400bc4024030520031b40b000500c142c5020841713142400c480b801e802d141c00b403569018410550001d000c001c1504100040307554103c8070543c4500c0c00160b007880b08850f803c20b160002c2d0581560120701c6010300140d03181050466024040f5a0808150301c8281c4040b548060400c60352410010200b11b103917480d104443c010f40d80d40b0030841180864201c401203140e0222005500800400044001c090301c4181940e500c0f030a03596498a0324400180c800b400e0f900b028110081105000441d10b0460740d940001039003584400303c80903035a9009840c6030004071005001c0c0f1183d01066480b0520030b000a0307611010044080904001540410106400c0303044404042a45c5000b44044e990f482018954052a24940014003100918a90b5103c0080c0443c8201076600440d40c9980070f0b1a440700c0002c0902d40200722a4001da4034003400b036861103c0300c812004c2200c0942c81030070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 876556348 1250 876555098 876555107
    0x2090405071a0f04290d02040503011103011202090a060503030a050c100b0d110109090e101d0c12070504051905060406060527090901090308150307030311011b0306080c01 75
    0x810030365440c0c40c2c200b91810882d00340c5180c003086250404000617014020031308030319010b0b06400d0303030700d940040e104c9084c40140f60842c0c189010504001d1804c4c0010403d000050004104c0350707034103840000071a100e00b9401d0340034103002e030002c5501d0300010900402c0075034080040d00300c2421040c22200c0202da001c805504840d1114031050f044030246004001140c21149203c008990601d00307000840c0e600d4a8075021182401c0d00142c0e281c005d100c404080d041d140c000e00e01c06400300d0880c040b02d035640403001540d0303004a14190b801000782d00810b03c144001480458000c04020384217002615141004000610010281e0919586050003040d000d040038881e00007a904070751170b0715150140c405500c140840c9045034448881c2c040b05c00c40020743e124004024040c000040000c15941202e10307002d042003100502d8201c2501e10119404019640010584126a00b41c00c0c000b690f544180c00c4180580340345148031303094001455100100c1030b0b15900039411144003c060759a03441d001001140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 876557598 1250 876556348 876556357
    0x209010206130c052107030c180c0918090203010e03040501020d020a031202091906022a060a2601060206040b0618270703120e09040503190c02090405071a 68
    0x1e05210201d0b8041c4545e0422040c0071480240d0021220314a15442259500c0c00c070031900100d80600212904011040b0b010090b000c5408040c0020b0010721138420380200406401d02c02d80c0580030705031210b51180745159014038010364028009025200c04d43c07020540d2940a40300c0c0a005201c1c131000c840c1c101348080f07110096507178103503940422502c24001100181d0802258258400340b4441a40207980072840d05000804180c2c029001034072140c00c1100801c000641c005007030860101380c030441552110b049075400c1c101420007598002c0d681020006500c1400701458004d4400c10020070095000a40948a0791250354074131030555801c0180310800383c0120124481c04a40c1001c00d9159904013040e08113040c44000658941c52100c00e020b01d030015a50042d034103d25403e004400c6aa40910508507840c030a40d003103040c0c3e09190f41d41958921902104400c280458252804d80303038030800444030b40b00c4d0000e001000c1d03400c1904100c0e0300c0d407045104d91000c1541c002c6003400b4556501051303a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 876558848 1250 876557598 876557603
    0xb0a0501080c030c0d110d06030501060603020f04031214030c0903010501090b03060f042105181f050306180403030b093312030a091a03040c0512100c03020901020613 73
    0x600396101c0d041c18480170781200b07540c900075075102d10a0b1000c50308008054509860051004255030b031544c2001d13030071250300750401820517004010613212181114115812203030711804280d019102c48a00b107410754603160b05540c140d60001b040c01039400320742000c0c108600f000c400801c034076603a07840c4080c1200e09054240340c058103c040001d044486084140364001c3c010f000700c00580c22068400c0150003241c81542004c107002264481105260000b4628604010b5960700078000d482000101e003000709040c50310400c01c0010000d24503469a0080c0020944516031051403807d01d844c0260240c05a01c08071401810b96038001000c1c00601c0a0800c002804011020f040460b0380038882200007026802580101c1c0010202d40ea0100420061106200c5036603002e5420381030040d88617020f4103917450b606400c0d500b1300c280400b1441750307110b110440c1c004031460060104402051403e080d4078121541e03605291501300d88600d45c040d001000c070224260700b55841a50384464130b0f0074150145002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 876560098 1250 876558848 876558871
    0xc0c0801051302120f12040906050a0302060304121b06060501081f12020d0b090a05060106030603210c0f0c06032a2703030215012313060503100b0a050108 68
    0xb06005428034404412030a0700c2001030350301844c94a01c0d080d01c1c0c0a0000300b10741c140c1100190400c00400702d8411070014010072500c034281e55185400140c03440c040a880504561708540d8011103940c01401d0301168078075812450455074100342018801001a4803e041c046100280015107801c01c02540380481400098034048a40c240403400c050101c0c0310008a0b040708a1080e0306022405050030789101d003149800800c00070f4103910706a8103220041e4850400d0508200c400d100203848101c180c0306106d81607a4072140c00c50401411a03650146180240120115a2151041c0b0803286500400da9443d42c6040c0402400c1421209100010021610090f01d00028501c0385510130500103900a5011040b1400d02e900c0c100900c040030b00d140c0c0101d01503444806ca40920015800049006003001d0081d481225901e00827840d480e249011070743e110301054482d8840a034210380c0320390043c0170060105c501001800c400305000300103012019105000e031003000079181d1700c5410464400d5100c2d150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 876561348 1250 876560098 876560131
    0xf0c020709050c040e0928030f0804080702300a08220807080706020c010c0f0b190c05040314010b060a08040221010207060c02120a1413060c0c080105 66
    0x61070002031001825981d80b41004100010750700200d50300d02409150404050003219400302060800154800300d00b41c601a8000b00c05030109070031403245a4840c1c05401c000b150356030b40307151002017841002c0001358411041c04d101a06108a41030009009a11111200c60010350741a483c3e6a502440c0004120010400c0044550707125070300070070304840d00c440c070744022103407660f54072420022560444940380d44050010400d80b0350411241b070341c40070203003000000c0040503200d1441c44510583c0c0076140c036042d400424405510742110181c590a490001c110149892100503e10b610038801928100c03004194011908410311a01c020310000030002840d0101d40541601d40ba10002c0c0141ea0103024400400041580130b00050102c80003e800140c0d0740e10289807001c21140351907139003421544030b16400c0c803100c0c03001c00450701c105006040245020600c2200c18010348140300d8403016001c10b102001072000e80000510102a108a0720036801e00e45412140e402c8600880d5614490847e204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 876562598 1250 876561348 876561359
    0x6071103060601090b1b0304032103050a15120201020a05010e0d080109060e01120602091c1a010f091d0111121b072901030c05040b010203070b0a0b0d0f0b01090f0c0207 74
    0x6049240c5c2e0486c02540d080a64a407241540061222606c522568510301c40401195140c41000c3d403000155500300941c000040300401c0030540780c09103141781e84c02d050005003503a0003009a0702515601030001d2000c0798203208055141c0101000002c0802c0b54400046010003490160b10252a01d910602e1a26880c2c1000c04030344080429041d107816908001410090321503d03040b01c1114100d15691680382c6451410000320281c804089ca14900400e0042c815201314000310412103681c030030f0204100301c4016002c14001188840e459441d031901e00000c001d810a00050005410003202c07030452690ba040403490040010f500e880900c050800080c0c00043c60f044d001901024000f05850503995481c460b06c04401d403c2e00f092b24650030500c0104580c0c5801c1c09050803081081c40610305103c810345c0c0344a500a0003410312408030340c84600300c3d0800e80307800b501d051641e030700b019072540e0020041c145000303007c0081c003d4000c0c250030500403602d0704030a0f004112030108030b50300803d409c600d001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 876563848 1250 876562598 876562627
    0x1b0f0c0103050c0f0403300c11010306080102040801060311010519081008030c0708120403031718071517090c041508120d060501020d12020d0b06071103060601090b 72
    0x42c03a41c118400c00f480385880702c4d0001405440038500c40d1030011003104030500d03004034051104008440e040021004c4a80086d4001c241914403544110a1920041054011707806040700f0340142c03030150702c0440c0c002076000381500402e04685c02808405071901182c401116036114060403071600c80e02a00c0845007280c41240015030200c4588518400281c0355010700342140e000c546600241d0303100d90350074054404148800704101e10940c3c903c81c44d15185030307000380c0844d0a50030b11060400303400d0001800900901202603295480070291484680c4800784500d41c5030400c80d002d0000b9407c040342855250201c028103000d212421b006040c3c546245042001a01c03040c810178860b13903541382c00000c5ea41001c01400604600c64804075441d0070b04c0d0701d800d4049814650103d811588500400c2e8507440d085183c46107070214101025a0342c46140058502421030412415040706000620030709000103890703000380b4401304400360b420783d0f04d0340d10046460b107500d400759590001c0104100440304489 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 876565098 1250 876563848 876563851
    0x180615010c0f1407050102161206060905010f14030303060f060304050115082a1c0807020a0b1801020a0503251a0720030414040902090901021b0f0c010305 68
    0x524020580040e1580d40b800820103440b03085031900c0c8811101c09030010140a158042d100078401011222090601d00241e158903204658a43c0042c0c00e044052103102d030045006441d5092080c055540e580c9030001c4820354622500c584040c0d840380c41002c1e031401100f02c2c2e01413a4002c004100d4410014100130040c6d102400443d42596111001280070001e410f1a10080c00300300054820440d8074800e65184102c00c00c403120120340c02e001f040c2082c0d40c9a0101c990940040c0784020307420620341c81c2c010f800b071007503480295010a001a0020b0704040d440000c14030030701883c91005102605000590703376100b041c0d030001d00a07001880f529100d0390482c8a016000141c0c05182100400142c803140a00754071a5070b140d5810b030440081026880d08200440407500c818100041b00c1103040c20f05548074012130042c0c0e0740c0c048400100065541d501c3e0458101c80740c00510003081410031005480c000d6010294901c045061507412a0b90608041001d4005440d41170241c00c450b00e00b000114000c00c1c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 876566348 1250 876565098 876565141
    0xf060a0c06090b06030c18070f020709020d0902130902013219020705121c091e0312020102070b011e0308030702010207061104060c03080c040503241806 67
    0x10394109010220745035008005109000f5050440741c1e0800500345418400c0e0038100d207001d0a810060003031440c80c100344442e808005403800204c80c40081c68101d0501c0e560b5848070b4a202d002080760300c040d86003644042a03a03442150fa91610110f002d0310401a107400302c801030b01145100d00311101800318805122041d240f00b0711002640180150000080c1d00440e04020115403000c11500e40c141d010400c01000e04030440d00042c49298243d0f1807079031003052401185101c000e00b4412140540a035405001500c13050510340e0380810600c030f0300d0f8042202c81c401520a28103010400f0f00380340c018800c5900107500454480ca00b6804d0500b034200181c0d45002d603041c51000d6039000004aa4801c000e107004a4a603800075a43d8030140c28500d040d915284ca0035074010000700410080540c101005604965040c03d121505945200b80500746004903030250381c050040400300080e0054030447c6a200c01a141da040d10f0b280c4a40b05001908048102c3d55110356005101142d00000c0c0d15035070b0f0b501c151 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 876567598 1250 876566348 876566357
    0x11a10020c09040224040504060f121403070b070c03080f0106051803070902070f12090e06010806030c30010c0c031b0213020307030507080903220806090607020f0c0f060a 75
    0x44005000501072803499240d800c00445c08070703061186140c540144c0c0006c00c090b101380000581030515201c1859074000b07000b400c0f0140e041072550840424010380c0d07070a503004000d081403032504100c090413016200d80114001050440015500602804803038141e4040783d03526410701580041b0b2150b1303403801c02481c65061040d0000012654401c0c001002c149100d6800c1014485283c80c1040724451004982e106014032800280104014601d17980d42c0100c09103082103254450303801107428181e0403070545404c15180513031065062804001030919038450703120310b110000d485038420700b20340f8000040c40c0000c0b20a031442c0c0100b482403a01d0303444081c0d45010101030010a50015400f002014000c2070700350340200c01c12945507010320509a001e8954180b0702d0032880c00600b02c1c2c0d120310078141c503010601098a0140f0b18905414204000b4113030000454040341410540241d691904840c440018818004007103506030000c1010b100540c00585201004003000c820441e454000416040410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 876568848 1250 876567598 876567619
    0x100b09040213060c03021209090601030209120a1101090611030d09050f0303010f09060b0913020c030f1b190c14011110050106030501050411121512011a10020c090402 73
    0x9480c00035100b0010409a115402400a18500641855002c3e044090320b144140041d119584900f412107070b0001007403800507519030510000980d0f42880600007010b92141110b40c600300121541c42d1440d10340243c039850410fa640340000c513031000807022840c5868005002c1140f0400d125081801d5003403143c816601890b891044242ca150800d03401034090300041c0108003c050703070030310403103010f0403108040e28542072402000c2561800d41042d81042e244d40000c1c104102a800e2090340e125090000d0420303910303810104405500010a01c0c05a50707800b8441e41d214480d810b00b420103041a41c001080c3e10010f103400c513002d98030300c04852503a05000700c50091902c1e1030380078040c49401200940b800600c550404c00b0060032680705810880c003c500d0100b075198417050300b506480848200080d01030480d078805100302405400c02403c135802c100115800f000441d0706400241e401e40760722002c01c0e80c4030346080030004c040d03440e107110002680002c01000e17500e0414520b81c0360310900262000c1003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 876570098 1250 876568848 876568867
    0x80d1e1106040f300c030e0604060c020a080102040305060c090a0b2a21070f060203011511031c0e0a05100f050112120f031407050702090609100b090402 67
    0x20003008407400c03036060f04041400001c0190841e6018030882220046100403a0304214615100e195010510140300303600c51618101403060340c84944118026001540712541c400c00a417403c91001800c07131040e000c1c02d4020030b020005200b580d080b241c200b0024005601e03100340d28160f95010451032900184200c801003042c10480004100400812b89081101c4068054400910348001c25185003a0001e004074800002c44080b001410800070b9403036980c03440b803442e1551709000c21180003801c6038004800021960400000b0301e081100c40e0700c80b4075002040c2c080403a00c9103c4c1040c091140c02c0e0b41d03c86490b0141c1e00358054514414940103c84401c0041d4030707041c9c603040c0b44007820240070343c0b44c02d2240c4010000380070700307401402c2c860b000ea0003c91260307a502c40c04050001c60355082140b800284030402d0301c26005800c10301c0700d0300304164103805d00b884008c0c195805400c099008400d002c0c0821102e082100300301c2c0c0314400d0200c20120b00c50504241c940d40c0e5103e4030809601580a0010405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 876571348 1250 876570098 876570103
    0x90b0312120c0405040921030c050405150d0c2a0c030605070302160b06030c09090a110a12030206040218100e130c1509080f030301150309060c0e0a080d1e11 69
    0xc070078061780c64614007c03138001e21100003d003a01d2010040506180421151503080400e540c25608103d603002000c103406a0001114040c803001e00a10724100b034991404a03030481c04045000d4039440c1c01144000041c4902e01102d0000c4000600a50300d10f401000401c029a0205802c000540340c00b41ca0041c0300140c0042488031160240c130b84000020600c0102d00d010050081018000d90701c003640c51416503030454548101c190060300c40702c2ca880b440d920302e40d500d40002019050700205508a04403506000350340d0001100c049005414444000740420200200c551050290860403030340141004404081001d01806d0032040d6041041080d00040c1c41d0f201800180180000c990781d181c810000040910301c07158008445500204496805c0c201d020040703074151034071303000101c81451003920228010844160041d20040c941035904244a48c00344003e4021a42192500803098658520a445a112003003d8022030308881c501c1d90028003001001500381c3e890700b42082c2c5a081d082c1d0460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 876572598 1250 876571348 876571361
    0x3090c030624060f083c010905011a0a030c051c02090f06071a09030d060602010b0a0f060c11130c050c0f150103021c060c020304090b0312120c040504 66
    0x25481d904002e06240528141800002402c1c41d29191102d208002400341c0058001381c0751017028441688030301d50a60b104c40103aa029001000f40c002501c010380d5800c142580c00303018070b42c0740d24105030000924800000001003280b03000030005103400c9074007c0c168014030301d400406040c0300c000e20100d40e02c10040010900f0811080304007681c1c0d01c0d48803080014624503c00400e100d000140268008181c000c460303030f00c001c1080c5c0b104500700e8503400121440c41c042c041b00d280c0d05038107000b40401e03803a03070640080108078006d41d0010040e03501d5440c0c0d4030410078030f03019060000303000d5600500459030361540420398900c05041104c0324900c42c03a8003000c1d10351180c40b02c40400c00024400580301d90800039022508010400f03007070074603007180661080030740621019110745000041c1f820350040340500a001750398859410420b50240c4040691243c02c00c0c45460a454600b0014201034107010070184030001e80d50395240d24250b545029072103802409800d12103804018040420562a40d04c62003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 876573848 1250 876572598 876572621
    0x50901060309113f120406030b01020f1f0603080a0207050a1d0f0603010b040614010f090e0106350a180c0302090603031e03011505030903040603090c0306 68
    0x46030504407400e28103440015010500c0c0a403860b5a25400f00d00b20080c1d2802c0111200d01060180003440101d41e01d200c544981112005e0207107803018841034a0003802081150f01713035201404000411001645c03200c1e070f0603014501035008400300c0301014403030400c0e01000301c0d50302c42c001a00641300d0312400c180c2c2d0084070304140940c0c4080c1342032160303140c0813141a00511034083d600440003800e410304808500040c200b1a155a007400c08074400c3d55082d040040c0508002d0b004000140e502c08240102d00520505580440d46a080c80b507915885a00100180c8003c10b8580c1020f901c0e050302281c2526901240300d15520325a100e08519548180b020561081c485044008500704008644211545921540c0150340c402d80d100d40010041c0c1c40000c21a90112640c1c5c10703580c0c841d804281984181032075401e143ccc289491080900c09400d02a6041c0c66040240280310100800c05903014403041c0e503c03482d294400c2c00208841446608099074051007901d031003065581c1e036030760b01003510480b0503030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 876575098 1250 876573848 876573851
    0x1a060418050313051207060503060a050405090604030e012a0203071e0503010c050702010f03240b07200904080304081b100c1e050702040905070b0a030501120b1f0509010603 76
    0x283c51280d02c000303100c00713084111000c1d010b64851400003561411184104010700c80e020001882c00c1c4e607041a01002014007a0041c40340e0310f05207260f03a0300c0b040121800c6000c40e82000d041c48440d4451141580e20b00c4005d00e960f6801154179480c0b2017003600016080768503204861001c04c15003408a15554000c400d00482194282400c0405084d42c07059901c00d01004428440c20007d80c0c0e2011a0514084250600140101e4185411041c842c1c40401a0006514100001541100c240003d105003800340c4503d5000d00303070895071841059844019a81d20010303140200e404110104002c1d50018030940e0303240d00e41510300c410002a007c4040509246801480310840707404998012512181c207980380100c40107800042c0030b60003a1411382404200030010034480304544132079004502c034035009011224502d9032000c4090141d400030703600303100181c00c0500006e65040b042d46901401c0750311161b103040316503034148188180d941ca9204219034a0b4041c1c80004c80d0745038010a107020300303c242d50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 876576348 1250 876575098 876575107
    0x40f1820060a11010e160e061c1416150e090415020d0906020d0917160803061903080c0d1e03020a14031003060f091a0604180503 57
    0x60030610100e00d1810340a05400a10840c48195519800c680c1c002006040a00071880b02c40e030b01c03600618a00340642400d11030280c88801800c41c030300f4900c04407039075020300200c181d40d050b090200d03041103a400d1080308441402e00c3d000049900450070300f003620b44e104984010002803880541c4102d00d030f1103510090f000c0c00e4480222640040e001c00d540c0c0080d100c20905090556a5506201384030300340c4400551f01107071819415000c0c0e04107600c401c0d0080010b5484800c8850610001d154001d022107844903580c01c11030946121005561400e68502d0719210700d0301e900d440b14455607000400310743c0d20040c521604c1c64045010000540a140500c0440c0d8940385c1440400b03113030009141c80f40d003e01100c1c000b4045100f0024401034034104040ca00540c071001e0440d41074580e54440c01825600d0f810220400c078050403400c24003c102ca004840502c20310190110b0401211400d15024011108208103111030300c01c0d40b07019030341001c0d01400c0040d00b0516a910907104bd56610381c101c0c0c80741c20006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 876577598 1250 876576348 876576353
    0x309022409180f160c230f1204180216121d0f060a03091a060f0a0608150303041a032703030a0e030909010b0706050a18020f040f18 58
    0x600d0103516000d6228020b083c140000c29660722100107100e0103010b0783c4c001400f04a00e01c0741100804055011002c0703030704910b0a800082d00b00c11011130314003141c0f050540c0704108101c00626a1281c0c4a440301c13240c0703040e08154440c040514411603d620b52034080100c05003000c0086d001020160180007502248c009803103005060306c01305030241c45108a40103481c215542e540046448100c81141c1c819601e001801058002c0e281c4584060841100000345040079070714003103100d2086400300d6138040c4c03060045d400c010b110415401058005810100001d200f040900c0042030a0800102140e082030b503101c5030464104e04510040c95460b04c08814007101042c0140520799002e402444c83c10f0074000b4081c0e041e40ca0100070105140141c4450741100181030600440d031a0f408041e02c40711407507841c5c5c14040c800e07510801d400c4074031610f0300d400a40c00030040d02c81d4840f418040082e80358411442e4080040000908410076441562103541e10541c0700d107845442e04030001c12885a05464050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 876578848 1250 876577598 876577609
    0x5360a0f0f110402090a060e030124030c0b0a1b020a081f0b060c1f02090a06090e09010b0916030f0c0e09070807020319180803040f0909050a02010309022409 69
    0xd02c041c50007240180310408280d601d40100d08103a840d81c0c900b28185004210009024100d0030001000d0504c2901c4100e0700c0752058038000099900034141808100e542d4203140600303104414580000544507014664a68031240754a5180c038002800f00e090035850302d01c440d0400f25003508203600382c981032220750301104150140100d801800c444250034020303c1354040c0d40382c5524001c00e020031518115000c03000c1c00640d040c0c034070f8094054140c4000b07036290070029062031300c58043d03400c0c441e10900024034006414054001c0020001c0e00030240350700c030b003040c00c1441ca110000076018903440b4600e818440105200b52046402941d0380e45250400413011300000520140c220410840d8000030001850b030000210707061b0b6500d51128800500444100b1261801485030307042c1c1e070352004000040c03412000000389c0b0a41c0c03e00d4101e8140ea07035072103103601c084452408000b050340d040603800002660107684100a0039002074125050581e174a00c00340d108003081c5589050010300446d0150170307410031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 876580098 1250 876578848 876578873
    0x60501020708030a0f050415030203011d13080d11131d010803071b0e0f040209090c180901060e010312020d03060501120e19050604050105360a0f0f 65
    0x2800503140071800c1240041e00c0c1d1040841403828442080c0301840401e116000711401031070791030841c503010440900300901944c001e1203256a000c0300440c90884810542840078000c1e1064070b0f41c400354100382d5640d140590014505c0302c4205903201e988040e48201e51008201c104c01141d49411858100030132003459807000d01d0760070013a1041c880117000c40e42c1c0004c1110485500a1044011842c40f8122070f14a054030b0f81002100d0b42211040c40800800380039880c1c091071003101c400c1c4c400d41d0f41c000c0d410f9684010f0b0001c81d0b0321051203100d100c41ca0151210b0742d0703046000384001080c1c241d128549184108000e0b481201c80034072000f101e850340eaa043c8510020100185428400c451400d0002807841c0f00311651800d07095941e040c8204042c0d806c002c080c4e000d0b80200040300241026040c01030b140e400486003070394254200000505601010b044a241c1e40302031880c042680b107043c0c02003101003000124165604e1041c84039944c00301e000d514401e05032900c01d90401c90303215450718262454441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 876581348 1250 876580098 876580109
    0x312071e02010e070f030804090509190602130b130509060a05040908120c12150f030709020c0705150a1b02091612091e020f0a15080c090607030c0809030f030d06 71
    0x11704034810b2000680c00c00881301180d0030624040751b00d0b142c810003182000e103064500126502c1409049003004120340140510b01090044080141c2e0b0703440310102d0034420741c1c907668010140f0400500040c1303400c011440e0841c40103401d061070700d0b44420100e012201125426125418040b41c021601150300120381c0d44004514a41d40c00e0100501c000c4400303203400b40c005040c4007003031622403600c1d41f20a4a81d041101d4000c0440d540c65a030303459204001e40c8540b88410b880e014281000c5072030b040c901c89030340d0a443c2407440da6162a00d1818121101210301440140c1a128400c0020250f51541da0850107564060494500d01e122181d0207010300c0802c900d4061407905004220000c5880045000300e142600300f040e646000b07641c4009281c540601905a90110b50b54402043c041104052401d0a01140e00c591103991500307140d03451a4000c0c001c4499202c00d0802800b00000c0c0b0401001c101184510600e50400018900281c10301c1e040030407102c078075030012841c0042d6481c140a80402000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 876582598 1250 876581348 876581369
    0x8060c070201090b0f0c012c0c06030117071d06010908010509060718050310020c011512060207080403080304120e060c060103080a0219052d0312071e02010e07 70
    0x2195070001e0000003282c840e550180307502180c01ca603015000c204490052011500822104000b4403580c03034400c030720044000300b1040c0b107051100f1140c8001503c008522004001a0850f86000521160440d96580f070b4200c900521200080c2c0108099900c400d001800c107015250389000f2000502c02611640800341c10382c144018400c00c0e9401084840d04460107150031410176000400400f1400e44a50015816105121155004002e180d01820400400000a11001d010518252946845406814001d1000c0040710300042c400341d00400103207100e5000c440c10560b8030b0322466419002100c00b628a200203500381081950f00c003018610552041758000e081651140000750f4406e01400000d0030350307800150f20001381d802040700350314802c504c0d542d566080070249010354882c8110000602e5043c20303114015031400b000000c00c95102c10b120025400c0c29100c00031040c011401800c2402480300c154020362844c0d8204046d80d001007900e40000c1040c001c004420341c83e00413136510000406 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 876583848 1250 876582598 876582607
    0x25110405060907030b0a0f0e09010f0c0504150c0b1f050301061a1b0316120e18040f0c08210702090105011412011820040501030f06050d0302030408060c 67
    0x142e441c4008540c100d00b4030302d0002407545281020450130410741e00600c5501c1c4821100180c1105c0c1c5494180c82440341c0e80080c080d8035255000001a11450340c0b6001c00700d0803e22090181c800312070807035090358850b40b0740800c112a040c0c0303c014440200b9a600c502c00e00745451881841d9003d40a80c01c0100003c2c0e00030400145040c0d421114020044c000c00f42d0070703800061035124042604540001d08032840c00381c076511342d0305440414010300c4111084a1038080065043c14850084000218281018041002082c1e0141c00381c1e8460000074000c62302030f40c00006420205940400e00001781040d54000e012840c0744c458050060044a00c0140c4000c1c010020300c3e0040e05d4100196044500070b00744280302443c225130002e02400b402403007810403200c410001500503480c070310b84820f00408071800c1242600c801d0410081039604070891000041c100020411075110703a21010035045881000070f540c079100c0000440c90014030205030016400858140507860003401855000b691034004240385c13 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 876585098 1250 876583848 876583861
    0x30c0d030f12020d061e0609060503040f051c11160b12090f0a081908073f051605120c030a092f180c07060225110405 52
    0x70400c00540e19041103420760300381c61078004580555050303920310101400140d4490210541c05920110b11030711072510520000f81c0c050240000400741e0b561a50b5052456449880d03001d400481c10804980c144500d0800700010391002d2100c5110b51415640c04103400300d017030340d42031174404030359810800154200c0c402c01040382d90401b00c6021180c500242c50542e92049400380c10035407000000c0405002d8010080300b0058a04000d1400320391828101c10f40108448080750a2a0101e82403404980c00c0d011200068170300d410144012074a5804440f201081010540301e407004008900340030b280c0b83c0d020311840d8445061760000c07141c89450418144140e4071481900312030043c103602140b40000000c1000101c42d40c10030118140c00c007000c0d1418007503801c03240c403490b401c0c0017020b107005640d000e54440b9840c7c8051040408020950404455220403030f240c01c003903105c0780d000c80e0141d50801403440081c440c031100b05050800d002c0b8401209841c0e0a20748000b0800111030b034856480d05042041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 876586348 1250 876585098 876585107
    0x61b1206060c1502040506070c0801050c09090f181005040606050904020105160201020c04181a1003031d040501230303090901030f0c050603151306060c080307020102040905010e06030c0d03 83
    0x360b65000010300c01604070700e00341c940003031041c0d0300b005810000005500003030002000c8110b00b00c0350410000c00040d52030740c511040038081ca802240d44100d200b000b1030f0030101124407280d0000c1780301c0d101d0701c4c24102b0007841c145403540c62802103443d03646a000b0402407202138400e440c0206002e449880f800e14081e40020700ca480b132100b0b10300e0380d94104c03541c2d441035910030480daa04902c2d010300b08002443c80070100f0705800a203588100d40002d90381d03485580106d44071165a00540349104000c424504554080d900b6941107600d140780c40751103441c60f018503901ca0051900900c1100845540f50070500000c01c440d580070340483e40603038001c00c40c012481d100c0c1560319046075081143e030090504a4a4800c100b91841c0d4400c541c0100e02100703020861820644860580c00202d950300e180c88059008041594601e108110115944c00e160340c02050032500210f51040580c400145000d89581c02c50007100d20a802c07020380301c000e00702004114107040102c00443e09080760035a150600c0350340d0042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 876587598 1250 876586348 876586367
    0x60f0e090403140307050903010501091a0406030206090402090105070203060a0504290a0b06091906020c010c1709010c050109050a330b010207030206220e07080c070f061b120606 78
    0x1035808000000681618406d02c00d0300c076600c0f002402445256035424104001d46580b070803004030380004440f059840d1900c1d1044a007241da000c2d000b642005015401c020007504035107603260601c0010414140184ea040c45907a10030b1240b0040050030f400c20b8108113078800c0e0160160b02507040d000c1000510201c0b00304c41e02d5804a503809001c601c40e4140d0303022840c20700800e10040c1e00582135400d80742207841c031440041d0a40da0680d007260440d5040c0001103c508501100140110003044040030142c600f0f100140030643c1d0604014a00c40380d603682d80c5003101c0981c04143e603143c000c3d040f0071040040f03600f52401c2c01e51070500a00c244c0040f94086010241c05200d482070305a55030a003c200c1a402844008001c40d0020300081e1a80100c8415400c9848010300804200c0486107011958449440f83e04c0e0148000e079560141030b9035814541500d030342c0b100900b40c407021080300042c4d001520340c0c068401c4980c40701c04408201c42e55410041d2400158030f0f864000581421028040b050340b00c54802e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 876588848 1250 876587598 876587627
    0x80702060a140309071701060b0d0203090a0f0609061a0108060427080301050907020118030513050607060f0b0f030c0d0c0b0a08090f01060b030f0916060f0e090403 72
    0x103a41d14a02250181c0350391488000c5000b5555010007040a03503600803a05000b2a8452850b80030711406280219088032213900441d00f980b0024000e41c901c0c42060b034040c6500c44000c5040702c07d400d0040c0c98001d11048903170300403501c0e15200c0004a04001d4940242140b03c4c18044a01032403500d21000030308407020040c03540d80625918001034001c914440c44801c0c01d000007175610030b41d41c0c0090401c0441c40e0b0090051364000c001c4000401e190610500c0b4404c180b04e80c0f401c22074100c0c000741c1d40c00c4805a01880c22200034148102e004541a0b0341d41c402007280501c00e16000814500428989090310411b075150342c4281000001c3c07240340c2e00c001c0380c9849070310780c2141e1090000d41e81d454090200407031a001508290000324000e15066006030880e4002d00c030080886d0190880d140a6501340d444501900c130071803805202250f4029803000359644c1040150341903620380c1000d02d00c00c4041218079840403001823000d400c0d08010580041d45007490180a50b003080c1946016180907104201e002c211 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 876590098 1250 876588848 876588859
    0x62c030a050d0f030b1309032a11060a020706140405040c03050f13050715051c051015230903011b031409071202030a06090c1a190e03010f111201080703080702 70
    0x2c041014130541e42703009110540080000c1400100082c0c031440600180119000701d810f40b412082e03850410140c07810f00003203900400625040c1074045910300307543c0c11508103d100612000c58075660324007035000c602005580010711464107940c819003001c0060000c0c420220620100b0020a0003c00d0b4481503445072254803034055004d1500720748500c01c8113864500110070351406002c0803144e400080c010b1060381030b0000829110b40103000d594003030000f80b102040240302101051002c821800c1c1e42026400e010605060910000c41d080d2000a00c02d011066012001440c000b901849591804483e80030800031502d404d106180d40d4001c1401075080c0d1a40c6503982c4021035408121580c800c952105c41032001401d140b400c0f1071610020702400c040c00c4003800c01c5400403000341c0181c8241c140c0380400601c070840c0080064841c8190581d60a81554898200030010850703402110700d00742024540594402114885032000d49068120f1115500001e400b0800f060522050b40c40e41038040300c0c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 876591348 1250 876590098 876590111
    0x50a12050712180e090703060b1e090c04171020090409140f01020a030b010f081314190c09140a18061a011107062c030a050d0f030b13 59
    0x700415030f0301044c1d001c220802c401a0030400a4100440d9010869215210078050400b0a5042129120301d0304010b0204590750901c00c1694503240c0c0354241c01807038207031644e840c1a40381c4c00b2030162110b410925640da9800928885d0480020707200300c105100f080100381c0714151498900d5207513440340d83d8800384644d88602451081c070000c100c1020711a0380748012103922100200b6900c0c00f03900819a10302c046407810381504099402506803030150f407903c2d070f598003007680c503038040c0c4108480240381078800c40c1c4800c41064520404100c851050003561045d200110030515004030600b040d0b4115950140c02c0c510081c540c024048012a0482c081350008142d40842c044400062880101c01503c1c56050142c08016801003202d42c8000300000ea170303080b4003070b088022a06e41e180c486114100000d41012445418017400c03882c001c0e4103e040004c2c101d8948030740c0700001c0c5031054030798080e18150400c81d50304030761030307040070317082c6a8131250b81814400403078500b001880788601c010880b4001c036182da0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 876592598 1250 876591348 876591377
    0x4081b0706090303080910090507031b140108070215010807030b2a16050709020306041a03030d0218040c020309120627010b130509070503030f03270a050a12050712 72
    0x3c4100d54060381f0031420445d015050034980e50342c03070540c802501c0c3c2d100306c2c4808805420f8030113040d20517241100f8001041180c1c003001125450001401d990440c014842080551900d00e62140d000740002c00042c44100d046003004800350801400c1d0320001415503030f0700391103000b0380c000881c402414a841da036100c111402c1c603810104980103009203203000b8050081600c0210b03034061401000161070800c000001420a03c0251902c0b0031340c0c90b41580148904681c189054000b480c00700080c245420100350f100f000300c0c040c2e880241d014809604049031300546410701143c02c0e82a8440070700140b54506009071210480701c01c0c0391240c1b0300b80080c3c504408507044250440410700c400600315403490000540c02100500c815649031034035001d26440001c151800101392402910842e40b60b91542e01c8121001c18424050030314000b00825000407820f010314280300501c6c045000d440a00f030210340c5450540581e002c8485448240007040c410900802c103450002ca9a01c0200e00744030884030b10701e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 876593848 1250 876592598 876592603
    0x403020a050304090c1407050c04150806100303030b010c030c08090604080d0e01030608070e150d08030108030a1e21020405041107291f030b04081b07060903030809 72
    0x10002900701d00c40068000742c207140c01c1e070011822259554071000340e4000702480e241c0500c00c40c000944141d01c03498020041d85000d41c00b82254010443e24110559030710100c450030620704440000000710b00010400034181c050085041d00c00c02444c06003c0505942d8025003a07101011000d444102d010607401d60a40b00d0b881182c01801c2503408481c0500300a48000b032075403040c081ca15000074281600051000b40001d0070354181e4151103e80d8606944800001c05c0b154081600960f0081844001c140841c03541c10046005c1c140e49006150f550704e0f002d20103003507100394402034013000481804900003541d0100b1900d90050202c0102800c2490040e0401c1c003038080c542000da8001d1604a280c00d44411031f400500d4000d00c03a564034600300342c2d0501da414a0528200707840ba8030585117000202103518200010441c900c840c03a14107103250b220344500d6803c0301e049408640003500010f00c0320580d4983c0302c800760402043c10013003106a051007001850000107201c01002e01510701d0105100750307800d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 876595098 1250 876593848 876593863
    0x91218090a05180609340803030a06050307150807020c1e3d090e0c222312030706060f080604020d0809030102070c09020a022e05040302 60
    0x14800651420181c510340001c14041d1424000c01c10700191154502c940400c2e01d44c4184103410140c03200344130400a0744c0c8415801c104440940c0141c180500c5520360008040016080100056850703150828110702140d105803c013510903030102e001000218200c030040031400782c503481c20803a07644030360a06034500b00c856480c5590210b0000305903001c030210520a1550610b0444134928001031190300d15520451540d480303d01000c5000f80030750a01d41d4804190440300305c503d00001803640c0c41c2004842040d00b83e81002c00000d0010b141c0d105609020100d5010364245d0b60a4600b40f4070b4001d036089040681407012510041d403a01d104895a680301d040c1d042192480c05a036aa41010700d03008000b40018001c11815400006000c43d81d0304d0006903c5200d6075018084108130403070798890a03482d4210b19040c0b903041d902040480c0001e15490440c00050240d51000742e128058580301900300612041480b10451450f00f003401a03068000a440300d105070f03250005003c2c6c51700c2c1000c07400c0c0002c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 876596348 1250 876595098 876595147
    0x51003140430030b19030224070c12020f01170712020c100e0f06090a0807080405060d060e0a14041e050d05030a06060504081c02070f0920030912 64
    0x310380160190b100e070503420008441030116540002816081252980f540b150b00001e50814a80030542206c0380300420700d10f01c250952400a030800c1d00e503070f80f0300e0100803094112490391001d201b010811400c02112a032010102402c00301e00080002ca1004003190700100800104000c1c6245030b40003000e181e04071440320107040300342c40b00e032141c070006d00c1c0c054403807103041030030b80c0c400c0350085a4080390215100d801550f000c1d0240102c08116240c00c45550042c0100f030b500c80008202c005010368801e07006088410b11654045151072030500300080c5010b005040368503c074246001c1c50310401c10320700c6060b4031030b501c84014512206040784400e8103d4164038028003d2040d43c00910f144c0e900800514401c0c5d4410005100c0c0340c3d16010111868051886060a1a0300c503901c0b14540030150340c000b040705000c1e0720407030700403036a1658003000b1010554486601c3e04d80e030709000c5d0304032404c2c4104100491380044005255042120300d056842d000c210703800340c0383c0380040b0b01d86a6103103d41298405112 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 876597598 1250 876596348 876596423
    0x2030c03070c030302090d050705091509010306270f0201030c0206060105160804120b01030c090603030e09070e0a06110f0c0d030804050102120a0509060901270f08040801060510031404 81
    0x87c0070380340156881840d130103403501c10b490003000034421207a450100090400041d001017041d901c1c40d5920b401400812251000885982d422525003501001201014600490030030743c000c000e90001400f2030341d20404900840d00000d040140d0f070390b00801246c01107204044060200b06081c18400118012500950340700f080c05070be00703020310a000c00700034141c0780505025007030150b030703a0595001c540180c030000b404180325503403c82c081d24009050590019a6040610342c0304616400949210255041040850f1a50780501d40d800020490404940716640c010840d035003956001074052403076640010104140140010b081000039016241c0002c0511582001410074a01450280404a8800003907200b620000790001d2414011a090002c0303900503440000e4468400c83e0754102200c8042c1c0b61400d044411900040088000b4801854034100000c2c445003814100842014628615801c060501100c030850744907000016800550050450460040300d07114100903810f000140811030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 876598848 1250 876597598 876597619
    0x1b06050705070c0608010501080606180d050325050705060c0316050a1e0b06060a03110c030a11070303021f0608031903050a020403051b010203090d121202030c03070c03030209 77
    0x498101e00603280703582c414964114030a0729100111620082481082c0c001090b00780855602c0c14840010300d051070319015132038420001c81c0d020828400302c180c03048496030301c00582c0c002980200241006e400c104500701541000f01611801d5a912460161902c43d02c00002c02c8a1881d504004840110100f401c0314248081d41d170800c1a1114003500d810354500c0c01404000d0034203c0311003500360035158450141c0308152104000d000903504101c80072803d241d5984a0f10342803095a0700a055050301c8a00155600c0c00c020b0b600520f103180c450748084295015840c00d0001a4001c00c0c003154000203c0e030480c40341310f100c100c800e02910183e800000702d40400261050f20142e08070079180d01020313588090250f03869202801c2d040384514400504550030a00d400d0340003200d1041240b0200b5014411242000c2420380028104c9490381c0d400c4600e015920f10003401c0f030340c001c554003e4540c44d503007045042d440d0070860302705c103880003c00a508200b0300a442004140c00ba40c151201c1a401030400d4201 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 876600098 1250 876598848 876598861
    0x60a3912030501231201150f031a19092906040c0e0625020a06030e0607021c08060402040b12100806060d062003070e091f15050d020a0302030106110a03020d1b0605 72
    0x280000d000540f40b10803814120500c0e030b90400390396800744101900304036003982021011001864403605c101da8040706503000100dd1524410802402c500c401d001300d8140c10114100011215981c403180c050005c00c901c2c2c02c1c9a40c1c1d480b01502c00300d0b030302d5507001c0c0c048402840405c40c40800c100002984941c0755070020030a2581a03101410160b40714007100e5141c0c0f100901030b61344401d6061503200d890341d100402c0304060320420b5619041a40608050304250301d0341e80711022038221030072362020202014100304c1c500d04000c411000400b1031401520450800d41702048055010540142c812500c4e4a042800c0034214249500500348a2210300e0702ca04004d840200b00f25071071044140705115400104600c50014120140078007a564001b8079868a060280314114810000b105c0a00c00144100090004203000818810003035580050b80c030740c186034014007101c0d41d401c5040e807246e000002410001c0d40003d143d5540c07034445e090084500c204247d82070012010084004e26540c14042070250 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 876601348 1250 876600098 876600119
    0x41401050f042f010c060605060724110f0304030c0f150c020312010905220b0f010605070203070e0628080c060a391203050123120115 59
    0x30758400c400211003900c004081c01003c0c5081404403600020300001d10019601034030f0300f4088144681c00200303440780d80d880000c81c50341000304251080607060142030070f040400d00d1010662040c4001c10003114442516800c041e0207150380003244107a00201103170905d0301902c08503030b201d079000c500c80728041c0251034040c00440c650001406a5428002c3c1080d101c3d001100b5180e0742025490a43c0c816840e0a02e000041c1101416070903030b0390711210901c2134000c00540000c0a59014244641c841c1c208608015a1030505a110804000d001d03c806e000503907020824101300c030205200745401e078490100158003e004111040c90545a00d02d84d0b40714090307051003103001c451850098841984c034640901c10907203c2c402210307002410710a00301e4600d503080038802e050140c410b21201e6440c1d4071910b039441624a40107040d11180181d0020303000040c2d2502032140508036009411503201c510701d00f4030f07280495203c88580705a040020f42c03040032100354000500381c18110b02d18520a6541c0c0c26058 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 876602598 1250 876601348 876601351
    0x1a1813020a091e30050d02160b03060d0f1104090b090c030102030610030915050408030910110a26012309042103060b1902010b0906090708041401050f 66
    0x1c02e402c410302401a0a42c8000700841295010220a2134002007120402e5004070040012510b0340702030403508001c01ca0400105088100b6a0020801d0740b10702001031102507401c0d808000e80c0b02003002001229203031080c3e01017145a210003e046004100d1034600c03d6014120011500285070038100000e01014a54850240e1103450685034860782040a25090f0312041f669150020000340440c1c42c00b40c840e5000039805801603602c41c05800c20580e01005490060300e080d21031102c044180500d0310030600c407580d94410680720402240550ba6409000c0b070240c0c0c02410207004480b80c2e0010b4009050300d9101f0799503c00406d02555607181e0740c003200d9040850782000b46072801e0400940c024201040c03494001c64120070000d02d8403644d400034513032044800411908042c0c581d10000707458001140909403405038561108080c404011009003151041c11720340c0d00c0b8400e8802031024640301c10680300d42209081c82c10b48040d990b00d081c81880003d4080460f03032158a044d0400490703003000760b0442d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 876603848 1250 876602598 876602609
    0x120f03031f080c01080c030417070f05010c080907141f0203030115030513020f03030d060e01051c1a1b16030905030a020a0e0601021e0c0a1a1813020a09 67
    0xe038111030302c0d1184640d80d007201c0440103010485203030208158055020107503030302903c1080d1b81c41d1071003917441c5841c88941004208607000312003800c1c60002c100c828083d10034540c45504d401821490003198040c0d0b141d1061080703c0c00e220207142405107580703403a8038020450b20f54060301c19213406c48050080d42c0360b10900c03407200800d1014502c84202c5201c1d0103254014900700c05403d885041907000c0002c100154512a0f90602c8104502c01c03082940c1d0080c0c078020920340380c880940d50314010078401031502880b030310608424808030540003d02012083c0c101c81c84602441c0c0c1e0f5650b1600c800a040d5490041d000940941c003060000d820340c90410241d50451081c0c6d1903800c3c103550361060543d103080c03c8030000c1d80b003810f1300350030300001300a503c0c4c065100a051048502c2e55044031120580955007200e4285076412160302c82d20182854000900100072119102c110403d01181c844140d01490100c881d003400c0e00029a2111ba8a0444181e00c1140764401155030f044540c60140180c00b00e440766 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 876605098 1250 876603848 876603901
    0xc0c010501080307080a0f03021c0504020a080102071a07090b03043005030403081b0729060a03030e0301020f0f0304021005090319061d03130e15120f0303 68
    0x12030702c100c0c0842601d41e00b41e80710000ca0b0814203092000d603400c1003248110010035030709101c201002d041690310051072041c2d000001030136040c60b0060106031100c0790080d401d640c0c010054000041d11410601c20b10115001c00702c00c050700d03510411103200050b41d0283c1e0790800c0210600042c0901000c201c0c042c00e1000101e0442000c450848480038200142841c0220303000b8400600841e010301307141ca9104000d900b11206036881c03104400e507560464181a1842246904000c482e5506010003448d5800070821050751807500380006503c0b0b442900000b010410104007020594500b5015683d41500c043ca010343c841c0100c44d505550764008480c164882c0350101d5506030140c0c00743c022140010b4003d0f0143c8480000000c2d284020341095600702c902968400003000f0084003c1d03c1440c403110760310003440e60742d004c01c81e5549800180b80c020640f030482c1d08080c000c850402042d8413650301c80c240c503405414100c40c1150b6041c400c00b60703500e00c17040c04000100000421403251004000c2c103040c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 876606348 1250 876605098 876605101
    0xc01140108160b07080309070305010f0f0f0e0c101407210c1707030e030316030908010e060613020c0a1211030313023610121203020901020a0203060c0c0105 69
    0xd01c1803402e44074494030751505001c0145102140d41040119803002c601400c89003c9903890b0383c3d13036003140c45101484401c0b40d40c40001150807084d40c055000c0c2da441141d010b100b440034030304019031100d4800095501c2880f0510010212038000c19111180c80043d400c4561603000900344a0f401ca0b5000b0304200140206000c5402c4060048410100890300b0a00511504083d0224600f6903400780e0b500350b040c403130b403600280016079080000f40740480265018100d192400e1802412811203508103e02990400000030050240000d06a40c461401c4440900341012031042da0f00034400c503420040d440c02211a000140003a8504000740d40010f0740c1c41d2900b5910603038940381c480c00207544d01c03420300e4a8454201c015182003013011111b102e4080074048032099008405410b40103000c00b4103000c25501c020480311141124002c4001c14154281c0301884282d6078a40740144040340f003d10a041d8080b4100125074402c122408005038050102c0751070781895030050455410510000c06503608000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 876607598 1250 876606348 876606373
    0x31707150f0f060b0c06180f0618010b1c02190b12011e1d090f0601090c1d0102061b090409030305060a050a05091603110a05090102062a0702060c01140108 68
    0x1005c4802c9814000c015114036194091801c541c0c8400804103020b03031107120b000d103554030400e2203810b000b04028401640300340d015505041c250388210603040d00c07600c586500324001c109002811100158103c03100d489198444000b00100c1009821001e44c0300d40125056100c903070309058150580360f042d45c6042880c41c8030701c9080c070710300214000c00c402407102640901c00c00740600900c58107c204c1c9000d5804610b03106946030b242a500341c4c00b40803100d4803044c9190301160803c2d080320001e41080f010018400040700041d40d140b03009489030b400750001a00c140300b034262910607070300110300003481402640306030b00b801005400f041d00c944c2e00c1500d2400c0001807600d070640d0800112000502245041c0d9244813092003080c54002c459000d140d118414124051142e20050a01e81d41d6521202c1d100c89200f000240340510041005010b810044c80609070518501c6070ad00d515000031084555a0f00c2c45d2020502d2800768482c400c3c015030034090201214440e1000d0355044e9144541122100c2c507090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 876608848 1250 876607598 876607619
    0xc0406051827045015191b110c03030d0b0414040c1502012d050a0501050102100f0608070e06120105132907050309070f031707150f0f06 60
    0x20703040341513040e00c042520101420210314280d5101901d50500500301d003c2051541400032480b00310340c003e4840b03020009482407209880e9900b044125040101035281c2c4200b402500e03691442800340701800c000c507410580d042002c1040d40e007010b0103036030712890b00703010340c00241807090505441030303083c440383e2441c040201444900c182c0d0410b003004512490420b0b841d4100d5030340803101c011552102070890210200c0992402845031003640310400d2084003c100003264005400003260600700001006241e0b40000e1900780185000750019000001c000064005d103456440f860190045000000e1891200c5023290702c43d880507a08041c40460f2402002c0c02c89404030743c0d07a03092105428112001c0f40b002701c98141903110241e110541d112025840741c14505045402c0d10010320004108640300c031041c82030b0310082200c1d90005010900356520071600142c40380101740c501001003690020300c551008110400340d0050020000d50740c440d8807079005058031840c006030150900320001850300342c0307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 876610098 1250 876608848 876608903
    0x27160201090b04021507051212060d1a06010c05070905011d070f121103150a0602010902030303010b0a09050d060204030303060e0106051b0709020c070302090c040605182704 76
    0x440030040459030f030382d42040b1020004c040c80e8401c10500b4050100000d0040092060000c1090066074841054210480d020603004150901510003030280c072000a811034004030010a10400e01d400d1035130340c40012202c9030407000020b022845840b40c0058903ca15078000b9050f1200300c6090182e09503841104265814140c40840000e1444c15a1410f824420f0800798010f46030784502207060404040d40c0c607000d0704113423000001c01d130004450150500d48040080c004005070b0009001d0000e65070002600c03800140700340321580ba000101514101c1c482c40b10341c00500002880d071141707401941460300080d0464001240402d10340100801c0721340000b00c1d058103d501540d03540f0b142950000f1030341511a42d030400c620b85407180d0740000c140c01d4018009072105c08440720051030750504d10b00401080c600f001d0160180703140e081206000380b607440022141101c0d80c0d80d1181c0d218a010001060100030303214450074001585d041d08012044804144034041c2c0d000303c0f22600311205410311000507429 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 876611348 1250 876610098 876610103
    0xf090102031017010f050405060628030f15140109060f1505130f060509150301060512090c03060c27060d0f090606140306070e0d02040b2716020109 65
    0x2205074204030071148030241e00f01a40c0c04030000300740300c15a85d108030300343c030810360303040b16141c00181c200280c600f01740c40400f042300020400345a012000045040c4050424040501036041e044008400d0201c00d28140310802004a4200401071000d01d610801c000c0c280a100c0e01c4605045c0001a41210540804241c0d0300d0300450754400c22094600352155480b001c1d100c4442c40d07801b08009100d0111441c1c00e002410b084d05d42030741e203005e40c5007001000c1e60460343c0e01d5940c4a00384018020b00b40e200f03040c2c0e084050340440260f0161215100305250101d0002581d80c103204550401009000010142141d86c488241c4951000d0414a52260300309034a101c1d90f801840501050030400d1498200c0b000c07080b0045400101c0000544a1006544081c0c210030b005500d03071a980105030404000441c0e01019034504418803140071400204c4041840314087e00ca681c541c20b901c500c035070390a00c0303680203840c0394862940f10301e00100d070f800d0a981040b100956545000110010440c0c0107020b510783d22035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 876612598 1250 876611348 876611371
    0x60a0603033011040906060518150706050702010213060e22061a0901080c1303080906042303060612030706021305061303060f0e0c150d0f050f09010203 67
    0x20104405426070000c0d290001462032442c102c0c946902c0030351150b00c403100c84a2501a42d01ca00700003000094560550150017008401c1103400b80300c120300741a4520030030003101e0b8511085000c00e80c031040d902501c81c010388070310f00d04000e2001042c0c0560080c0a0741e04085140318406540303030303000d442e01c04440303e841f034000c0481a080303000e10310700611800070607010000001c0c01c2925045801201101c41c800c03082001d0000070a0350141d81c0041800364440d00b10b01e155807810150150700d48501e2a84c0c030008003800c0c00850700b001603588081c00d85010701448014192407032503510002204810340802c05001c2d008a10204885040004580410f6910710340154540780a42c1e407014002d51201820040b01643d5070070105070f55641d100200805000c0801c0040400d0a41c00c020086410648010150901e00000500c05410209a108402008540d0b0b1200c02c5100b0300400124415405501c64952424031480c502500303e034000c03401210205040d44c0666a4589280c1c00c034407060700c0c60307100300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 876613848 1250 876612598 876612617
    0x62a030b1c2d081315140703030f09110f010503060609010503132102010501060504031110140c1e010b1c1103100209041a090105150c0a0503070203060a060303 70
    0x140c0c440440d9080380840c120342000e003030800d02e81e1088825842d0b5003100c040c44001400607901e00b0340d0380c040010707089500440c1850310010101401e070307100980d80480c0d140c002049800c00d041c0268000e00a90215200510109442c1d24280000740e4502c05078034401c032010120007a041d40301c2c4050724441d01001c0c01c12407401c543c1c10019243c0307400041000c08a020400641800201d140c6000c1b9203c13000200603040c4c180c6515400303425601c058102408201d41440108085003005080000c0e180c8295000d4100701a11300741100d0014528080305078211000452000070070000a00c564440e28290701c80d500200117140c06820786501000c41d0703500c00040c100e0461042c0d1290a006c505502c9915003070300846200000ca8244041d83c003002440075400b00b040a00c40c14a0b0080f0042d480d442c0403c0200024406c001911054060180c4e070700a100c1c035410400c3d0700300341c1c07803c449918503400300311241c0c1c1016180240c0e0300c1d480308204074080c2c0501404180c01c2c600d14040c8900b620784c542c0b18107568 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 876615098 1250 876613848 876613853
    0xa050111030903071706131a070e04110d0b190509070c050604030e0108010b1e0306010207031a060a1a070b04021f08090c060a090909062a030b1c 64
    0x5044100320094a41c08100141c111540e0b0030030024000f480a00503400021502200c41414124010100c00103020100c00c00780000d100c003031035088030f02104107070443c0c10786691004a40f000c00c0d1851040d00300f1303d030035822240c001c0090041c02000811180c24000307a90441c05014040300e602280c0e008403008604184401e2414cc00400d912819500d41003000301b0140d12124074089058509401080c2c180400c50b01da540e11413510f80c00b405031030001c1e62400311309401d81501905482e1850310b0018022000c00c030b20380c0c801d2201500458000c84846100c00810081c000761110075103e07503200c0d40c0c2680e0001030382002c2c8640e10600800c0d40480600380043d87c0c841c82c48008008004a91120424150300e00400c2c3d44800307841c43c2411030f034410240f454000342981c50075a00d0350700d081c80386805021030040c0640c0156032600340c510000e800b1034410410714213a000741540307540d00756a10040c45644160b60745d00d0301180c83d900369160b500344030712482d44040c400224000c1c003261003101c40c0d00f280c1001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 876616348 1250 876615098 876615107
    0xf0c01050318010e1f05281d03040b040f080109081e0d0f0c09090506130e030d090302030a0306050d0b1302220605090a0b2206260d0c020a0501 63
    0x10190b01d080d001080c142000350450741050301580410402c1d106400e2003104050451060642c0041448459103d44c1c9090b01c00c4100407118828030700000b91181d51424800d00d00c60300404202c40e40104903521192541c021140c1c80c0c015020701940500200030004810300140580c2040540011803c0d01d81036400c0b41240d505c0140c41ca2805034808100020710a1602901c038040480c801000d00203000800319400a0203040d40394404841e01c0e0401091044070783c0c5880322000402803502c0c0000d01050b04070512401d600071910112034240c035003c504000d154000c07000708030901440d034003005030b5504c1700c0411a00c41031402c0e001c0d140824010000c0c1c031030a0600581d00d815400101941900000c2c182c070220f00880403000f0b40c003504c0d00c80c0f00420841c00d2840e2899006001050b00b8401c6000210108040b010640440006142c07040102111506580e00c00d0b0054005504070700006000c101e160800c1080c1c4503c80e0065100c1c14414030b034524401c20140d031010381d0003018600b009280500450b03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 876617598 1250 876616348 876616381
    0xc08060a030c0513110a1119020a14120f010e19120e010201020903120c0d0519030902011107081f021810090b040e0f010e0702070504050a0207020904050f0f0c010503 73
    0x13401d660f0780c0b803034500c0302c8900c1c046e0205031056070f107180741c00109001003030a148213003c0c64484d0840050028006a80303a81403c001d035004c0904c450302c00c42c500800607542400380c1c040112030340074851405000312410b41000300b40d00c3c03040d4111036000040c0c0d0740744540082c1c1c50001810300d01c22140c80f0600548254903c00c0b40389014400541030902090003c2e003898052808045040000030300340002010a101440c086030316418428140034141800742d400310003419a203000c00d90b5503881d04046a0041030f194000c0072140040307403c0300e625400c1d15a40c8115002500741d411990b01c00f0a018185240210b68401c4403021103108903140c0c44042c003000c15015201e1b0024021422404204214410082c1000344804c604004c8541450280b103024054181c0082043c000540d00b040100303034000681030304483c81540c002a843e030f641c05d00c6800902400d500258415184400d0009001000031700c41c0c1b40c1104001a262021034407000c1c2a600c155803041c29001c141c040c8002800c3c800c0300d01211 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 876618705 1107 876617598 876617629
    0x6050a090203102f1204020d0b1303030609022a1c0e0a08190b04020f0d050d02010b041503080d0f020a050309010c020a0c0909051c02010c08060a030c05 67
    0xc5900c61013410460260300e081d08001c5021501c44140708c43d081c9800c0036030340324141070006030705c4144d814409041d00028205000426014114400c4502003894070040ea42130103602c44e5a15642c40c0390240e100e129024030002c1a494940300055101e00313200c070380e0b5003608503d181c60070000021050f4106070880d910500080c10540289044d00401d0303600705a100c41e00e60f40d588002030081d907020140f00d030020910a41e440402c0000201c035801d00c100d980090268a4102d01031108031081a9194080034000340b904001007100e860003010701161203c40440d03010300920000f07059a110a0000d40060400000c00904d40b900380300303044403010130340301410306241c6580703a03200340040a0154080d582e82c0d071080308041103805c10503021080c24424815507800d510160203030081030074030400000f11b0722400016145252400c410419a580b0409203800c0900746418080d000c090341c13102 = true := by decide +kernel

theorem cover : BRFrame.Cov 876438848 876618705 := by
  have h0 := BRFrame.cov_init 876438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 876438848 ≤ n) (h2 : n < 876618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
