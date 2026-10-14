-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2232
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:04:27.10845+00:00
-- url     : https://prove2.me/submissions/485a1bdf-2c38-440a-8f68-feb39bc79afa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 401258992 ≤ n < 401438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 401260242 1250 401258992 401259013
    0xc021f090f030c05040507050d05041406011a070f020307032001080112050c0d061508010212101d0907030b0a0b1003020f040303050708131203090905070c03050a1808 73
    0x1214045004044007000100041d141d91142c0044400520900780036036103c20006042d03510030412680a80105030f820442e0b8141402e183d01e200e0603840091810f80720b00700000c00d82e00c1a1074142c42080440300b83e00c91030b0000c6552180307000444444120b03058881e0318404000249402c58a1040d280c12044420b0b503400020001001c020781a03200805888440c21080041000486d510004d1107003a03070781d40c10a03000c034940080107020005542d0518418001c0100d910030040d00200704202750404054500d4a400e0074081000342d0314860f00282400075940c1c0c01000a16071321041c1c0c484402000d0f900101da890312010300e0031600302c07208025165129a40003c0f860031004640903001c25140840c00d01d046841c03002510300c034034000076061110220381c0c2402c2084542c01c0740c280c81d40840a10259940e600600c1040c50034020003200840c0d030111000c20b14a0381c41c072a442c8100051394a0031003007a6075032015181a07004210940c1044182c5100e050100306954041c001010f1000051546040b1b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 401261492 1250 401260242 401260247
    0x1208030f061f1d040204061110060509041403070b040c0819081e090a030602090a0b0703090303030f0e0d050309010c090806010b091318020a2705070c021f 68
    0x10000e059602c15100c00300d980000314012196524490002d0a1211200d0070764062181841c19018a40358000c0c000500899030580c0240c44c200c4000c0c181c0216507880c00441207003000e4132111b0080c0e607001060302001a0101d00180701d82c040100c03c10f0203036444d0002c0c3d80c0301c00081007000c40d0141c030ba240540104112240041025003c4160780200c13498142003580c0e20711010740b00304100b00d419400486940000311025104036038580350700400e040785040c0e50780751442c00380d040f811000c0c0c426a4a4140010294114400c9810103a815a2402c2446003190340980c01050b070600800d140781d503104516444200200316041201110b91038040c0c0340e2421207070f81800d61b45020b41e904104101414100b0111900254035419610079000e480e403103004074004980c030b80c58a880c5a01d081c90604d9003188400d4000e03d8500f0440e802030fa011044a030311003480d9903a040d407100c1c0f60740c0d96038806002448405813691000f41c00826614101038030000c140c0002d54582c6441401c240d1810800101010458 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 401262742 1250 401261492 401261521
    0x70c03211b170906120108010b010c0302030d1805101b05180f0114040609030201200604020904231005060901030c171c0c030f080c040915120803 64
    0x44003841c0c031041d03101e0940500c03540110035820003080e0003156041000c400310110262a8400300184c2200d0700d95091400c0c1d000c541100384140c43e2207500e003c01480440d44140c041240c85500f40d00154548154288480300178902c544411040c2c1e14681031050000d4000d208002400c008254003194440c1401c044800c03211020720420140601081190240d080c903070010740e091503045074541a040c155100503110300585001c100c0c00c15800060200d051508410b4107020b60b8000ea1350329958a8000703d1518180c19400303c0c414581e4130110014006192041c001e641c002c0c07040c5082c9048401821143c0f0265403a4802118103800c004000d440c40602071203540d601840c112130608055155445100303506009000343e0b4440b00280b104200104c5082043c0d0b280c021b400001d141d21041c2d0058020300d01c004a910440001380040c0c207403202544902502070140c915150007501d0646000f600400400c260200400801080c10740042c45118050a00403428040d0040c207a0300d1806100340300810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 401263992 1250 401262742 401262803
    0x203120c0a0609020f1009140618120c030303100e060a0b070b04061415010809010e0303060f01030f0c03140a052206090f030914120c060f070c03 64
    0x2424103000140262030001005888580c00200c0050001c907107001151446400c0d03101581c0084a00100004440d80310b8519004c40743e25070010402d07100f604c0100110b920501c2081190300141d400c442c1c4c42d80c03412844071041a040e40048075408089040880c2c00d5030030890781a000190960000c003c1103442c1c01c01d841d807080c4200c031820040350800d4040c81c2c1e0ba0044e950003030104904080000c04010881e4800c0426501c07020304544281750102103184201c031f00ea00c43c2400900360001040c00413605004850858200c00042c0d030842e503503c810300082d02135205500e410151120800d0610b00301512403820402030340d550100380802c0c5022a0f41550310040c01c0c6104003483c2500304140b00e0b02a51484924884001440c010503005040c80d0028103503001010b0903200e801302407d820103400000c04000c4903440107034421040f074800d04000070040d40c20483d40d52500203e00300f0032030380f8040c402042080710034160113040c1116074441c0c0c0541981904112801f009400068140041000211100307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 401265242 1250 401263992 401264023
    0x50102010609060b07080319060b04090e0d08010512071805060a1a030c2a06160f05070f0512030103050a020f0a050609120106051002031b0a020604031101031b05070203 74
    0x40d51400420126a10500e8800f034007840000c0b01080d80d9822340c111104551518000c00e0060a44820040314141e20034070640e15583d01d0404410f6003541c021a1010341310180727484511981e807074401070040440700013000300b03900d0041c400007141081e1546c407803c011002000c000105c0e45065018003001d0045038120f6201e081003025008102001182200e52040048180300d481e0303503104441309100044241c540e00034086039000c425040310000341441c4140d240c4542c11401d420181020f50b4040b100d07001440001d00100807030004100440b04503002d03035104408030f0380200000e04003a50310750800e0f002100c0d160418103400c001d40c40c0440807071100340d81c01c8540301d80380743c030304000540d0790b1045184080c0205d0b071858403015156800e60210340200000381903950f48400e0080001c1d12544038103410b044d0090210320f0705003102c80008a03c200300ba400b5195516081c1162924000d03905242c00041c10142c403410625a160303800b2602c9001880c0646071581c49003e00d00c109800d01c074050314048070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 401266492 1250 401265242 401265251
    0x15060a0c05060609090303010605073306240311120f040c0801051005010e0102071503060f0b0c0a030c1b060c11010815040903180311012624040c0504050102010609 72
    0x170300320002c0200c070f04481250500c2d0741c1e100520b160040b40c1999907485440410000540ca400e08a0807505588046848180410a003a10340c0100760840881415410183c00c0044102445e2400381d48802c150100f1040324900b8098401580f4011840c2111610606010320f014032041003035104d0500054078884000780064913000d07107001c0750f03c1c2c140d00c585410400b0038540441103900038440b07400034201a241e1008000130001d00540500114402e0300301c0d996440c40c0c00141808101309460b908000040900940001031b1012684a181d0000595601071000c099001c00f040b241d0342a00100782548801c1c00c45200c2c0e00b014464903212000c95030600280d0810030900a2940903901c40300382089900090341d182a00702180d28050754800699090b241c4035011040c040f515041c00d002e01c0099803654000d5050706401c091280d00c420004100280c0e400116160101c010300c0150f503001820a0404010406d100043c261a43c80c00b5030004180d0029003800305590a01903a400340000c08010311 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 401267742 1250 401266492 401266501
    0x1c0603020904120c0c09020a14090d08032203030b0f1e040e0c150909070212030f040f0204090c03020a1a030c090303041701050133030515060a0c05060609 68
    0x1d0380d6203401000180381008072201e008841d8010140030900c00c1e040301c2c186a4a54031500030740001c1d8444150100410607a41c11000c60098410444884a40250564440c1030311503441026070381014021348200d688013140d410795400f9110f10754003254000d40d80031419400940c140080204024126406404003051000314171046995040394418203640c00102444604aaa41000340130700703003c1e0303010881e000007210b031944210161131000c4045420f0072903600d03104c1c401e07aa41c0c10418000c02e440b940602c0003406982d0620700c090760003402402841c009112540c002021509000400c0703032001a40d403014030a50030f050840e0805001c9024501e0040031540c201c503d680d000080240800210000b20b2802584007401660300408039008450b2510b15001d03a100d0180101f409200b00c100316481e00b0403025101130000603140c0e088c2c409075203c082c44402086018180051250410101c83e00c031400540d2035003402405074441c8c0d60b448003840d40745440c00500308030000d04003611074038080d814003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 401268992 1250 401267742 401267749
    0x3211b09010f110a081b010e070303030216060c080f0a0c0203090906040908130e151f0207180b0306090610050d051911030c010c030203162102031c060302 68
    0x4a503980340034244400318003010401150f001110101d514054082d2210039010040d070380020b04a010300c013901046102040c0e4402d10f08aa6516084080340d03403041c1000c0020074002e5008021000070410700f00b480000f96100e940988003591903050005906404004d2082407140c80c1c1504001d00f0305062000341c0755410001d541c0e01900680c5881044940e01040c0355a85561100c0314084c1d0010ba95520742e80c55010b14070b0941c500c0c3c420f203120b0210141c0094068514003a404c012450000d2502113055107001c02d40404060391200310055201d000d402054042800c042d401c54000306e1080402e424051200307150a1140140221a0660045043c0076400000000060030398030142d4842c490b41e400f03414068a0004510700c0c3d4200c00d9881c986c084140090341c80e482c11441c00603001c607511b2810600046800c0481c1c10009001a0810310415625040c1d14402103c44c50054298980c036800c0444c0c0c2c030000420000d10749000d030740300040c0511030b0250304041000443c0b030340030200700151954012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 401270242 1250 401268992 401268997
    0x3021c08070e060904090605090706180905042f010210200304020315040309140d0b0121050123181915140601020618150601050c03211b 60
    0x15040c08181082d0101c0c0d41c848005075211004004d206000601c07203030401d2030040c0402d6508502602030944080b60300c0b8054a401600b600390296211800c1c1d1030140707110001c0c0310207401226020720b828440089032400042240d0000340c43d10808843c9629000003a01d4240310f00343c50701b2031500703140500b5044811034400c1201e800d403500f041c69482ea203910000c0d04212442d0310030003c401c444810300c410b06034000e02420540b0b5042c012824032065440030807200100703a6030010500c40207500184040c428102d070900f14040c003240340505030040c41c2d88a5003034503841082424400d00281c1e500c0119011001410340103000e03a00640f00695814902a88030280321400c03441000c0d00c900040200182410f81030002d40010314100040071a003030502c1d03400e68080da000c90042c03043d03d02081c1500044003184501c81e06500040c1941c00d0700c01070030f0122080090816060102c148003081c6041014402020590076103112803007083e110b840c2c00300c000b01c0f0180c002103050302042105260106500308 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 401271492 1250 401270242 401270251
    0x111008060a150530010605030901110f16020f060d05160309080d02090a05040e0105060f010518010c05101515261009230a020711011404030803100303021c08 69
    0x10030707110158001130070141601920344044c5140126000001c0c1107980580518001d0040c40000c0c482ea08201c4000d65040c00703200c00c45501c802c0c0411801c0d607032005040301001154070142c0202964a1402d0001b111500b286041401c1e99440700100401d80402408091800210341001c0090840c1520fa40c2e21901614064200032540000d00d00310703561341d80301d4580050800500500c00c0403141b100c0035005e0305064a00e17502070600c01c032840080b0760103982a0340302e88480c2101940035120b403000444c3e2003400030405445501540c8080032605032103000c0c807a004840c9006050060740740003004076458044c00c6908040213178600d240350840702000700c81090b58425824414046c0c585519038500e4075026404003400c60f15107040543c0c01800c101451060412240c0d051041d80d45c0c25400034160b10034144020688000903e18046030360080003010780d80c85900740c01c1c030300701134990750380084c9a4004e5402400d03144e81c0220400c20141c0c104009502c56070308076400d60030100c0419019040e6180a403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 401272742 1250 401271492 401271517
    0xf06010e19020706020c01050a1e090c050301020d050103020102070b0f030a0209010519120b1507020d1a070201060302090901090b07120207150209121216111008060a1505 75
    0x1000300d081540d005103901e0480e40e030300c84119650400da140200095000711440c03941542040002040f4865a2040c4180c684040c2d00301e03001c401c141c01c490002001221012590240303040004115a1400d2003c0c0400c600324041c00141e95045000291030104907a11640b40450100180000e20803120f0903a41c101c5001e000c0941c86a00781c1006031000d0060b40342e05501508000036956000b680f00100503910076100c0c03800c0012048083c00c1c0084610711204540c0c081c08100005801410212041d100207805003051002e000700302c0c095110500022b0780e01e070300140e440720130502c154500000076580180030b410017042a8045c40c2c6c0c6007250100000d00c0e181c2800782014110701c1c2622107404655581d944071200e00507030402c106050000b9005440c13600d004481200c1c002d40500301c00034000303c1c201e010441140c1000016404480085a20041206d05100c4003002d482c0356268127042410304019616030300c00e185804818031001c8045a0700040444501c010559400364000003140e0308984401d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 401273992 1250 401272742 401272769
    0x130b0421020a0308030f0703050606090a1a21010f1202032e02070302070e01060e0310050c07120f11010b280f0b04031406010f0501030209040b0a06050c0705030f0601 73
    0x7400002c00102d100c3d0300150121030000100103401d0940c902992245d00d0540f402c10498541c41e09001050041012180d04041050801d10040690301000d86d440c00c40c014405180c405420200009a4001503ca0b0440c03041600180011450000800094084004003614440c45070300081d0b81c4510400c103045c1e00788121041c01c94050980c1410143d03410701c8400c155070318510341c50000c0d80c0340418801d00448924100000c50303198411200f25403551001402000340e040d03080c03292002800c002d0311002000300e041124034005030b941808400340d4200e58403041140081101d0240907942e00003c4410141d1402550101550f5200800205015002141c60303241480e2600507165855680100190410080000801402c180c00500c2500d10810398189990b070905010b46d0baa01c803c0c00361401c2ca03111400140801e501c268058202d4500062001c070384070124502140000400342c02c1140002c60018580b15a11010020800280700913030003040140104100141c6905060003403400d6071416 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 401275242 1250 401273992 401274059
    0x8060306040c0306020a0908010c26090a141906061806030512070212030409051006020105011802030a090c0602100e03090a0501051c060b040f0e0f07050d0906020f130b04 75
    0x80c411f142c094110a40200505009508040c00601d100001c40760219002d40346440400307900081a03010b11082c500a1141445980e100181e4082c00718110200b0700c600314003080072a49201700e0644560240e640050b000d400e000c242001e03683c48a12040299040c00b104000086c00020315100a070140d941c001e807150303050320002e4144003c04000300454070000ca00070508a43c241c0c080b902508110807003400f150382c0c80c00180d085c1c690911030007842c04540500c4035507400d00c0c0d4000f16401541c46030005a42d8806983d5048501c0241e0000001030b4041e1603803280659482c03003200012203045000350b0500c0d503003000007103174002c950151034104a0041000300c0c0e007204004803010503603400c02c030502c2095168440c0c095582c019100f100703441c05450782d002840d07058a603281c40c00b41c00f10b03105420250391000c4003900d96600100762522219035465818004c11060b1020b00304419144402da55a40090103400c2d01001881d08602000c81e0104000c11103040c612590b02400c01000b4196135440e8407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 401276492 1250 401275242 401275247
    0x906110c0909071205030a020f0a0302060a05070e0904060b030105130f02060912030a031b1b231204090b060c031c0906020f07060c1b021311040b070308060306040c0306020a 76
    0x400c0d84c070010380704001c440c02c0d004100000c0060f04628a15600302d078100d40b00c080c1d496555450070280074025030024008207511800c5a0006a0302c40c3d401d08001440415440c00f0402e007100031a0240e070b0640d41c92144984d81d140a0107480d8108510710500a0b000b5590b48070200414146100244224000a044955510750310991080d910303e55082d03948034019040040c000c0c21301101030744481c500303604504511034000c01e83c0001c50300b0b20854003840404507680d80c018079903503140701c01140306402c0c2d1461400b40040104e0300703203c1d2058031845c0d111b07480c0076140750903034a5000e00c4500c9040280108081d1150000a44031501030310001ea041c918980440100180b0005001034101d900003c0c1200a1003141c2004048440c840d0b0340802c40002c809004a80d084140d41e5082100d001f50315a06000d498405085070200080040008130faa204d100056903952147e400300076809000b195103400d054205a07100c0e80a00150080d18403440c0c2665002c1906c3c0603400010310f115070110700c0d240010b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 401277742 1250 401276492 401276503
    0xf1206030611130501050304080313141e06010905070225030230010e03040605280c0201020f0105070504181803030f0c0c02090601260709060906110c0909 68
    0x507080074040002c0d148401c41c20b18030b03a1261018120102510b8000501544200704603031299421030016401d58407901d28080310b05c055000161000c40021011002c40b074800e108407841045540d42140341c024490b9200360030518142d20850a01d4684020010066000b151890b01200014400c039640f403041110484e42a400b07800103134010503e0b00d80c407140e500d892042120078143c1c0011607458141701034145420b840140881c05103d400c20300c010060180500b010b4422039100b8201d80c01a811151105c810355003904e00342d0740003e5880340c001401e5503010701211030445800f600170311003441e2a03c400392140c851031064081c60a444400302d102c0140d243e00c10a41b5485e40c40340a0304080070b50600038003402600030552481c4d80341c02d4070203c1c803a0141030042079056001d0000109580c903e001510001001e07400c9012890001d00c0002610f00c83c400e81a00c40c41040d101c40a5803414214000c00d465a541c0000c0240206203001c005060170015000341d01a204440d002d00c196540e200f01400c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 401278992 1250 401277742 401277749
    0xf030703082d0f161706010c140c0f09070905010e010c0b07031b0c11060c0708070e0a0c0801030302030304120306170708010e070614030702011404030e1806010f1206 73
    0x2150b01c200d82c10240040601c1d075000b065081d540d00d2540d22000d4a01134000c000c600d2900201d40c1200112040040e10302d4602e9000105050900500e000d6483c2c44101c03490104020030260450980d00500b85071584000000d544155903544085c80c081c08d010740041214041c00f41881090f841500341a071007511101da0050303001046402900701020040d02030010010014060141c411000140900c502009002c00341c21200c200c4000d4680014040b569021808807010ba0190400116074008104010001401c581c00c90414500d40a4a980c2c03c90ba4000074a0040000c01c0004001080c0c0c00400c1d83d821942100401d816080400020340060190758050751078100c01501c505007800d40400c1040c111014500280490030800354201c1d201c10444c05100003244016103c2c0c2d0958401601a590103200d50000203480a501116a40d2031b400c1142c0803400211100b580c401c003420552841141103007800504400b901b0800000f07480020b0681c0e200080200042c0410754040c200e40061004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 401280242 1250 401278992 401279041
    0x411040c0804020a0b0a0e010302180307031a0609060109060806041b170c0f1e090406030f120c03080604230702011d0a02060904050c0714100606020f03070308 70
    0x9040c40d40d02400c0014216070a92041644050000c0e013031101c07008548084030707255a242e014042c00f10065009422400429030400c1030b081485585850400c401400b40d1f00520811041c040002041c81769000014515030140d1150b1051140990300410084280c0c4c1080c2080c465942e01d65011500a042d22000060251361040c1d10580c900d82104c01c00c031a05012002d650311540d01ca204100c150700c030780e0626810003001001904514210850304460a4243d10725980c45c000000d03002078141c60702c0d0f4105458003041c448450b8200801603d04194503001801c1484141085803000f40048038002c000d203005a880c1d0802c01841c0c20100310ba910310b0240c030342c3c0650150606d00c04c000e0003480061001003042225549107095a00006100000541e000305040d2610720b040003403201406001c0e00203036520f00c080c0301e8000020b6248003007000041d42080200303008500301011400755441a031141c025900141d090801c0050088205c46005400d4200002c07a0349512502c0c149005840031042c0a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 401281492 1250 401280242 401280251
    0x70f0507060503010501170103021e0a08100b0a0608240a0803193f0e010516030f0b09010b0304170c030c07060e031c02070b04242105041104 62
    0x310700d80c20802542c103070b071001c1e030b14085d0710f03c0c0e04800319030540700a00010b540040881c001649090314828010140344001e0107501100740d40c0c9250780d18040740381391101386c010b03100c03071100c03000d4101040c03030b60300402003880d0855550620030010221800c15101d90409980d100400b0301054035010000402080000f04480d61070381c0c04414200d400d129442c108000a02c80360414035003c00210504a48020241040b006030701d0080b07081d03405c0e07010550400080c0341c48961109141c002032003000d02c240d4190142d242c0c190071180c0c00408603880d0b5444500d5140c0307010900025900c07001e4185043d80e1b41d29207038036038986076800c1c5005e90350311411a60441020004c4c0001b60442c010004e0302100c29603c044812550326048143d55081000f4101905540100b030300b4402034007152003215807507945005445086031217609610303a55201d5003249030310811030402e10304014500c03941c031200200c891030480c111240358064132078950171840c1b4884503640c65002017014440b90350409107030514020310412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 401282742 1250 401281492 401281499
    0x10b0d0501050a05061203040b1c181506080c04110d021612140910030e0d0f2a03051c091212090804090c0c060c180f050a050402070f0507 61
    0xd0180500300c0f0401c03281d90400d03000c02e00301d081000042d0f40300711301d400c0614205420255140d85e143c1041c580b80c0030244030880068002c0000740b05070340030000b420a150560050b40c2c06c0c400a08804031745c001000d945045801c011410000c5600071a0a10489012403110042c109100700b50286142031405644001041c600502c4100101c030f51a92084800103c0030034054015242c181000c615a040d00e5820440000b132464070010038000300d20301d81070000b10b00c01d803014014680081d00742e100001c40c0c02020104800382d00240f0340f9102c0d006007040151440c00c240144100340e1120300c402000d124010030f0040d1211002004484211869041002191910300300100900c5220000390040b460211034440f03503440724061400101d0b04602224600303440d0543c0e12000304028000c010070803a000303070000002240c502507200d43c1e180c5940e9440c2c8809200081030740048180c0d00885841e4099881000305071140d80d0058115139080f140140c031403030141480040f68440080060490140e1440171 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 401283992 1250 401282742 401282753
    0xf15010c050d020f0d020109051e100c0f11070f060807050c0a030203130b0a08010b0c2a0108010519060e040209061303030909060803030c160c0603140c03041e05010b0d 74
    0x5401c03014562003200c5c610391a4410907802c0b203150b108094072035004540641d219007100c449412410724003d0464500c460000d8152048030582113580340060704802060099645c80030b985540d4813101e0f00905041480c051209100502520481051000c00c0d0300066255019100341c60072404022709860003800b051900940740d920040111a0600310000045503600448060b00e0500a16480b0076649034202008182c050b000203441c3c0b601e0340f0a810039210b0101c050803104455071a841840d980d400d107028005445890141c01190007660014038880320007281c41e00d400101c803070500305002d52040307000100b8041d202d500d0311950030503000240030300f100300c521403280100c80c0281d071050b502d070307032940d00d0341060f43c2d40b51203a85e0480c1e2040c008211070501140c024805107400c0c5820700e030000c5881d5103c190b02c030640d0b40b004012a9540c069a51054401d0381e080354030414003081145149003070340e6001e9100501c055001c100c00c000e102020108076095200c1c14092400902c810060318a03850070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 401285242 1250 401283992 401284003
    0x4030507031203150b3c09091506030c07170403050307060c0806010507150603020a0b0703021b060a0305071215080106050301060b160c091d060601080f15010c050d02 73
    0xb8240040e1801c1c00a040008040e080d0300140d50501a04074507000111000c082c681040c1c15a500d5030400a19900003801c5d420b404c141035200040c10420b45480955080010b6044010013548240348007081c0070506c6c0d910030703003160751040301240110707142d806a040c026032400140d4841000720100240100501a00001508900d407003004203000390703501d0b4041103c081805075062030100b4814410140002e01d0140c40141503101404001100b80e566000261048840d500041c024240000c0351014035a040c89100302820040e242c40154070301000203d00301e44a1b540040d4100b6540e4030102d6082c03445070803075034412404000140704a041c1c00c3c0d01052581e45034468604998603000c00000e01d03007818001d4200301c0740103100542c00c2c0142034401c50303124665070200300d80600010a003c203071f8901e14814824034034003409a0f84074840b10800190302d4174001a10041c10b002d440020440442103002105500500c6c004032408400c8005006032800c85036650700409a020b004001d600081c1d00292 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 401286492 1250 401285242 401285273
    0x1e04051e0603010c08010603020d022505060709030803040b07051612020c12060708220503130e04110609030a0f110306010e070203121003060f0b01080108071809080403050703 77
    0x510142500c40720201422940c2d11551800440c12000040020718000c0d40030301001e190b40c50015141c14164a0440001004415014011600e10010009108d41003004036030101440c01d100b820282192a4050075000c010f100900f200c0020300090062481941a610350030240c00c00c03011800c00902c0c0c06800e844030140c3d0000144070b44001d542c0c0920302040540c00c0c200c80301004d041d0380e4890140031039201c000204002946900382c3c9800d2000d010f6002c103c8100d41c040d8000d1034880041d180000c408041c1940000c0c0d20a444805001c00f02d9201111000340e41000c0b00d102d0382d610440e4020070300781200040b010300510482d50030a02405400b0b50b00044c034440c100d064440303d070380790b12505d40c1a42c429510400180c0c010711421030050a64800160080c104041207001030303541e5135800041c1c544015600f11080e0f16002460255600040118050300f0368071b02800c07025060102c038501e0310486060306081683c48913442000d000c1648115405550414180d070042c2d601e904000c12850041403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 401287742 1250 401286492 401286541
    0x60a090b06010509010c0b0601020c030a050a03120506060d05100b130503010e0a08120c040f0b0d1506020d03050a02070b04050a0b0a0203100e25020a020a050d050304051e0405 77
    0x30010340790307600c0346044131320400d8161030386c444d03626041d101e184140b6802040c0c1d60541c030800b0300455445e07900f0814580b20520510041440084c980350040160b824245d002d0320359030500d400d000d0503544034070039950300084c201d40c002004e41c0c039003994003800e0303e140c3d1007040b9042c1d0005044911031070001c0300c901070350015030090001280c04e10b100d40d40e4841040015109000038054a07055816a1059a800404484d50b0f0380c2066207800743c0700448201079029074208980043e0b180071081c000d0140f03910242c0c40c1342c000c144051500c0790181d03c803800c115051040641e05c000040040280354162a07a894000141405628051800a41d1546c80700d00594070849044c00141d507840306030084910900c0001a002c07552490304151241c102800342c081481c0b544001c90b41c0c0600203103046c100c508400c2e1075000705100b01a60062040444081c2c20850103000752440100101c2c10000c103c80443d14145c5000106102144444e82400702d5a02800c0c4e100d8205000d20500304011451150f220000c00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 401288992 1250 401287742 401287763
    0x7031a0d0f150b04050c03041208060901090c030e030f040602070f03380a1d0106032604030b01080604170a0e090c120c0a0906090e0103060b040e060a09 67
    0x1042001189008500300411400c206401c2000003442d400056203600900040071070068a580c000a0659400315842070068030040704120910001071100c964000341824549100d00380140030880500c414001c09010589810103804200c0c401c1e4070489242d0f540900f602d860700c1c503e0855501c154442d01c02c1c3c0005215051001c642a4144032150080303e9106403100007000b441c1114a0005800350740200002041080200000c00d1040005204070381c164000541900960120b4800c4050340304500040d038948807050001900020007043c040421280c072381d8110508902c52401072017240c00007002010190000a81244000744440c000d074456013000e03091003141025a403e5004400420002510349600081c0504140c0d0b5545d400c0844004203610380450845500c400507000e0301c210a03a002e00052080000b54072001da04003400040c41d01c2e072a854540054050620300600000d0421a51100004d24990f51755109550242d1104d068070340302e03e0b00d070740340d8002005c00c0d48007524140030a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 401290242 1250 401288992 401289041
    0xc0a0812010314031c0519090c080d03020c0712020319030e0f100507021003020c0a1103100507091401021029010305071b020402041d09010e07060503131502030703 72
    0x1320031340c0c021103003040b9201c440740c480344a000301404010f0890050300c0c80c21076031202d03001520b01911485030300501d401e040191400c020545046e20721105078003017500c1803008009110b0041425000c484030801d000b0000003403400001c4c180680c0c4084210346e0b0b48003150242c101908203001c07803e01c1008980048030130000b60305100b0629080c3d9030240015101700403550062810201990148025141c0141032000540c00c0a02c0c0503403124050f18010500c05440c070030b601e4100008011001c0340740f420304c02c5007099a806800181103009018801c0744103540044940d1080015035940c100c400000c0c8208614100f03c52104010021144007402080200510700c2d4020f008890040441d6502c0d02c3d06c055800803030300408840d10748102e034015000c00000a450348040c8406c3c0050004070103108a40c14480d070352500316001c2c651000c0243c1c102c0103080040c2600300f002c2e85d0340b20003240305485100800b49481c0060b8400da0071495200c900c08000c2c8401c280d450b500c003103424030b05c1e907508200c015072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 401291492 1250 401290242 401290283
    0x509060115140d050702010b0a0b0d151a07050123150102010507050a050703090504060b210412111e030306030d18090e1504060b04052a0c0a08120103 66
    0x2001103203003941c00d04100f00b140c40d0400e5800154840013900c0000351140703a11000034100803580d8046d50201401242e80d42805190b0720a10010849900d1030300c42c154a441e0300d40c08001094100074000c10008200030062100a42050b88850300020344600010400c080c03501a040d030581d07e640305940d8407401012907500520815009400e81e844050510705d00c000215602d0340141011404c02455110000d042d80f140d00400340940140c035078060310b442000800710962484c007902d1410140306202404041000c1c0943c0303c440b0f10403441e14105c040801f550301c030304d080000700420040402c008106480080c02001450060f0000c80c01d4503480e0b17200c02400c80703400203296031034402c00b20300442c100070440c40b607405140e08250403420350390209d800d00e01502c4c42e1b40049500317803122070311807102d800a451719205143d8800510403518040014160010055042000405102c148001503d00c004081008082e8170340b584004001e9642489810a003440c0c10300784001c560011400100052040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 401292742 1250 401291492 401291507
    0x4090e06010f080303240f060301032102160302060f0c060f0106020d0c11060a02070f0e09010b01050a08060f2b02180f0a02180909010207200a030f11040509060115 72
    0x142e4498002c8800d141d003103020540046c0400301e00c0c1c0c40650070100c440c494481d00050350095010304060074040d0418a21040003043c0e0200d40002c640040c580b00700306190302d0b0005003c1e40e030161004c91300c904910490f00c070382d403242c404032200701c0c4111010407020611102803141030341d00070350945001052001d4143d98160a4010007403241c20780000d4981a82000009407035404007510407200401d46c2c65069010014150704843d10003a10b01c0c040041c0c1440900070404d90a200f8a44030740760900707804005229070405098a84501d1007480071080607594103162001c1c1c80da42c40b003d20180c0c0c006140080d8031844204080340102503000b160f0340041010508981f081e1310828452150359078646115000350f01c07440e000390706508550358a41894581ea1003052244c8468000103a86a000e82456680840315400030403860080a1841d031458840f140c4840403258810744011240749c6501d4400e4007803041030381c883e40040c50542000251710000030820b040b14156036004c48144001c5c6c00464211 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 401293992 1250 401292742 401292751
    0x4030b04110910140d0f0506070807090b0301061107030b090307140727060f0f06121e02090307030506070c121412130212010f0f0509070603090804090e06010f080303 73
    0x10254031401c000c041c444680c10594a0380007031001710b50411643d1134201140c2684401c0d10240e0182e0b0030480410340081c0040c0e00003940b81000707144039181a11010710380c40140100810000e051481503401041001100f000d15840303108504a840c03e599460380d40c2d04910300c252240c8000c00003100880d200440d505007a2025008000551426502a44042c5508205040f916680c0c3c3c42d000948a00500750080944415901c802c1090701d0120001c00c0c1c01c1c551a015550f040c6014480300c0512070036407103403c104030040c20150b10340c102000002e00700486540040c096021301340400440d203501c41d054010407032003044540d80d18159920112401455018a0903180c2e20030001d1031102481c18441c25401000b1540303120390350b00c80f507002c188100301e1322460001c160344a030700c2906c0344601401105000491900b0800841c41d201c12072030390b20b1841c1d20518042c1507071204a0018880328108450142001c60414000800b5450302e03696102e80034410144140340d0604041452103002c411217016 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 401295242 1250 401293992 401294011
    0x318050304030b060105040b0307020604141b010819020316030e1204180605060a0c1202240a290103110f1b010b040c080103050d0203030601020d2304030b041109 71
    0xa01d421a40c40c44400c04015146a0503c1014000001d84e0044a80118410040d980c050551418545003206050a02d414072030900c0d084014038510140c84035280c00006402481c2c001ca05413030305080c0302c0c00300801055407110700f4000410091965404032000501d0052980d040201440141046441c4d01c0f12072070f49059914100410031055240b400c1c010b491003802c50000a15643e00c80001b030306544803010020200744900400d1007440100051404c20324103d002900d917403813041c4c2c128a00d02c9405d402a02109285c038000c075100031250b0b4030113141d442040c0d2000003030a10150540415039080511240041d041c000e0303182c1030751150700a841011408074683c0b030901040d4480040c10340c91002e0a18401e40d6030f41c0340300c3d140d50b80301c1c060204103442031f45840302c2035410360070810704140060018006661042040c0302d0142d0380000c24031608c01703c603e0042c0c209000f0024014240412082200202c3c2002c9008801d011599241c1c9004500c5100e5080228025805018143d03004587c840300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 401296492 1250 401295242 401295247
    0x8071205070b090f04020c01150b09011416050105041b15092304060f05031231050306011706060f011d01020a06060b09090106020a022d030f0d03180503 67
    0xd010169030281814500080120075082403000210b02207807c044000020740e91034a281c011041401c940c11406880921a07a901e0104c0040c00a031065201e070b20454584600040e8500203410780c07401e0128400e50002c0244110b09183c2013404c0710b450103188411000010041c0003601680726000905807107543c3e00c40301030051402c41401e20b0002c100b02c1100e03201070b0051200d641c0d40c6d00ca100d6a005040a900c21810303550800080c1854002c60701c2c48400e20900410444030210840d46014505080c0c040030301d003425038017581c104901100d69101d903070035108400020603120500e091110035801e00030201c8802c3c0c0c0c0c400e020014515580056240482c070600c81c60313040e561002c0b2100200c2d881c103004917100c400050b42d60300d003107444a0740250f4820302c02040c01001407500000b07181c01031905100502d000b001a400041e0402a42d08081c2ca41490a040000e80b24610604070145100001e09031650707010895416625080e499800e0303000280740a070515001805520026038241e0842c3c025070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 401297742 1250 401296492 401296499
    0x3030e010e03100e03180306060901140a030507080c2d04020309190c03020102060714030a09022107030209091603080901020708030c07051c050607030f0e030406090807120507 77
    0x503005802003030a29058050038038280d022400e503000d1070b491566040011a543e609490010000c8469020647e129030043e2041c8412542c401300503905407030401a00100c803120580c001460004143d10040140c0102600080e0142012034000f07a80d05050780c0c003034520070346104071100040c036a030080034030110b0040b210348280c10198080d542c044c02280443e0744160380e00c0c1600b640211624011200c02d800c450050045590500c0304580001e07441c00c2c03107003200b1801c0211250710701000307150705501c80da101c00c81019541d42500800300e0580e9040351031407015000301902d0b01c46541d400107034001d07580000400c811101c00210400701241e559003c510260569031245030544c00003944904622800c400441d02e040c00340010080c0c2000c40c0020a40c83c0d2030941481088020b042d0889141101e002050012403000b060159000c1041e15002600c001224880c0d80141000a141d00161001040c0880d001d0742190306801039802140031125082c0c0c0d100010461010785240003402c5800018040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 401298992 1250 401297742 401297747
    0x50d0203030a11010b210f010c0518010203070803040f0501060501050c0d12110c07030308160906030b030106031506090e0a0c06080c0903010911130c020318040b1003050105010f0903030e01 83
    0x1c035043e9658400401c015504500085502c0e001d00b00d800c000c0d03035800c110048070780350800500007400d841d04000d03c10088000000741c458061050303108024480b000c1d8407107007a8401d000322022141d10641c903644a06080c1001640049aa14211580c3d803810b8800301c3d10350300075800d5071200034262005158545804c42d00701e40c116080d91a0405030303515210440040103d0348050700a0720075820003000c0223855418002c2c00740708040c05800c0010001082c1090f00c5030b00c080b90f0000c1e141c3c50304010558103505004a030042820f0351001c0d211910450b48003590749260b40082c0c046504061080c017030700e0310810ba215203400c4940002450b100320842c0030030055000c3c0100c2648040807801003170a001f0380348080380c00d4882c044021200e00382c002401c1001468115052403030400c182c1e10400a103103001c84080c0d0780b03208032210040503220030320700340202c0c0d507560b04510501da0001c0d0a11f070140d4240b190103405400280a0319001c102442400140103201c0c44003c003c03070f5055030702d8001d880c4005006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 401300242 1250 401298992 401299007
    0x1d03061f030501051806010f0b070b04140708070807080c0d140703081603031107031205060f0604080606042d020d0209090403090609050a0311040e010608070906050a050d0203030a 79
    0x1040040354410000040b03182841040d114031036040701c2e1a1200080c0850700d0070280160000720400f44806028007020844900751164998840c05026954589007085c0061003550000d07420b9510a2100100b003114000c210b9504441c00072080b10b026944590000d9120785c00f0743c02d140d0300b20b80303951b0401d0b000c0742151510055402c5540283c450103600c03511024042e40c441e0148a2042c20708803940020107a1500c248401180000c02e000e00380445694010504000c8101d00503449031204003090703a65442c5007100c40d40380401046141c0d01d5958460703160f220070301191200d200324907024403202494110100a071014180b00c2441e80b40c5801045500025041403844940391942800000c000d900c8402c2d11a01450081d00d030349000c0c5280c00300c000e00305035203234102c43c2c002c800d43d00c0208000ba03455840d0040c0e49c01d040f0380214403c0d140409990041c902c40d0711464240c4620000016000d00d942d02c61400e8440959034801c1454480c0148644c01540400c000e4260b4400c202030444240f003000c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 401301492 1250 401300242 401300281
    0x20115050609042f040807050108063d0908010f0b1503130c0305010f0506041e0e0319110c010e01050403030c0f0c330e12030d020310061d0306 63
    0x4240c40481c00ca90760110000d0b1144165130f5680310004062004400401c5040002e00003403030841e0883c9040d5000c2031240d45c540c100283e0902c02c59003170f11507440c91803041400300c1b081c00313515040704c0f188690001d248a045100f03042195207440c4148004a6140c0115001c00c24050b0082c2c24901c09092202c0807644010248160500c1072140e18001a420000080040d03000c0c10001c0b400300260b52401084a8000c2c051911607071401c025aa030f414408400f8100c01c5001c02d800103105103150007401e065100308400c0000e0135103883e00d102c2e0403e030045c2d101301d411000042210017240100c001540c0d40070801a206010840c240410000a4030171041550600d110b1440300002e118250f89440c050120344e00951110b034030b928803c00000d0300d04100401362800108445146130079500b000b07840c0454011035140568408034a403a48100708000f00c841c2040c2086045549242c4150401c00c103001501655000940185000c6120303252b14a582d12424002001b500090b00c81e00e810b148841c00780503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 401302742 1250 401301492 401301521
    0x13030203040f180b011809020c070e16020f030309060411040e0a08210415111201121403030f070f090e16031410090506060c1c02011505060904 63
    0x100100e000a1040b6503000207004640c0a1540c00100d200141c040d0303100e2418090400035654011180032100c94550401c940354810016a20009401c14170304140c1c1c9a0850301c141c040101c2446054000f60154140807041503090314154900044c0071510f1384820f580241d070705c0e4019008100424940403025160752801807000900500740912141401c0c44100261403001c00454a580c0e034042e02520300140900400d100b846600e4280d80305565044110220750810303507107040212059010500720b4242034040004589503683d902001c0b5072001d0100c10440f080c0030541c140848640c00041500c0c010280000e00c1070341b640d6039480454082460003000c0c420400203210019a03080d080708102d01882046d00395a0325241d0805016081d120001d9440f50015442d00400413801480b0308544192a850900480d554a8000000326076001e00f0002c010140104500119034940c03074603420118016540090060079a043e102100f130800510840760415010403000945241990111550070f9800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 401303992 1250 401302742 401302747
    0x614030604021b0d110609010605012a0206070501020c1209010c0311190515252d080402040506031b06070c0f23040c05120910051e010e07020613030203 67
    0xb541c83c646841d801484480100300110b140b066510414002940e2060b5844000d000c8145004002403ca081c0d0440207400300c142c894041442d01449111028000d03002040507807100f5007030400754002c0d840141c5006c51881105030b41e92a81d404074080e104601d005845e41050044652419500b003c59400215014011007584008525070041500c1c503960050006181d14503c003561040e5107503000c0c00060710b01404024101c040022043d5600e204811480d080c40e2515000c00ac9070364020b90071a11031100403009084d040c0b041d0703000207010700c01ca000f10b8050066413204000d01d5110082d541000620128014020139181072480060030312034412044c115140e552006015100c0000390010546844696000c25000150b040039406100c011070f400c0041c2000b401e4003600c80d22994100400d01c00c100780018201207800c1c0014003004c21081e00601c21854241159040c4200d00400d4020012904001117801d00310100e25a12994440d0003d0486440f408200780c010038101404a0861004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 401305242 1250 401303992 401304037
    0xa03080408091f0c17071713080304090c201002280305100806101a070210050a090e040b0a020304020d061404060c0203092d04110304020a061403060402 67
    0x443d5411441d0034120350325042d1940091614250304040c00444800741c144c20b0081001180001000c49000001e01f1180e942e40c00005440c8400b8081c1941708900500001c900081e6400040e00407000c0070b0410f50300c801802000c0841a103100d004815140050f60090b580080041c0301c6900800d040200e2042c2e5803503e281d00c01441c541031040e05c04c0100042c1e1039505001c1a5202c0c07080c80d40180c20928050b0031203141841c1602515075141c03042802c100076079070310095182601c000315403d032030b00a00a802110356542015006900c820b01d0000050301903040021110303000201b250050368807003884030564448501c140080c0d08040e20590384002c41d40040000101c041c418072100d00440c3d03c000c5024545401d1910071603c41010b00c41c01d6410421654445981d038154403981054500c01085200d0070f02e45c0030755001e00d880c80f500c0d60031514105040c2c0080c2d417a000514844c0c1d200302e40f1000b00315101d05040340c02c2c151381b81341e0100000080c0042605c40c501030300136165620b244100d48000300d12 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 401306492 1250 401305242 401305279
    0xe0d030c030204170a030f1d10090513060e06030a02030601030f0c08030d1a010905090601080703061d04110604050d031b061a091501050f0304061506021006080a0308040809 76
    0x10004c03400d80b9584a03408030010540c21000341450700b0424109000d005285d1003004e203480070b60020702c5209207189110b084066000e025401c6c09880044e00748039490010380344181c000d14282c01021600d030034110002d20540740c0010290300301a40a000340000e64a556190380b901c100002c000c0361260b21517400403891003020809081c12030303001c0e42c02040207110b041c401440008900c0c21503040200c094014007007501e5580110b900001f0070310300300f4015a25030108400030102c40d000401d110b43c8146c4490070482241030414010340c010143c2c40281c030f020ba41048600d20803031003103c1d0490f22031001c500110780505481400e031000e00c14010f01080c5280d0315207040780d0b54000d029034800054003840945040503d45640e11120440310410103050030000038056004038075203034100640000008040000d55041001c03011001c144a080d515100d103806074492080d001120845494544001001000059890000c94140d100d0f540701d03071600d4440d000346a0019401c0781e0410700c40310659041c4074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 401307742 1250 401306492 401306519
    0xb2d060a0e250504090c0306050f09090f010509011d06011a0a02030f0304061418070b0c010f1406190b0901050d0902090403030b030d020a1e03110609100b040e0d030c030204 76
    0xa641d950f03000e03a15403c11005804554200999004144c500340060203140ca40e80b030061760742201240c40c001203640d50160b080ca409511181601194208800e00c4480c010541080c44213104035000c0303440c250201240140d580400748108020a242d070040399500352181c1c0c0080c00c141804d44182c0c0d140030040c841d0039205038000c0e5022217250755036030444a03c042c0c1c44902141c2103031b04507003c3c0408019125015650360014011003c003208001a040f0341c0d88002d41c420810707640005018420039800851440a03d0340449440d40140175079150300c08118200e0700c0c2e1500b41c0300d40c0d0b084142040015001154140c02020103041d007a43e49440d02c0c000751740c40041c000d115600c43d03600860081180801c0c1801c102010f42078038259030011a1107000140940c4100c0307035105071091120800031003420100c545030540d0030014614003860060061350800803840c01d134160b0100c4024801e2041440a210440e4450065000d081e00010b188001081c807035001200039041c0723444e01608290720b5176075200425 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 401308992 1250 401307742 401307811
    0x703080301060f0905180610050405090a0605040b09130803040215030907300b150d0503180d03051b01060f06020a02090601140f0304020d0b2d060a0e 66
    0x2c82000f020200c095100200001420003a64007418161050740503940d4828090710071485001503400c045c20032840b8409980007002c2c001c0c1021260309248003194005c119a00850740568206013688446003402180240a04038810450951075802e8071916690780010740100d03804410907c01d00c048142413400b4501403118071020307200052420014030018110b02040c40f242414103000c014450005406d000c0721185c001d0382d03580040c0d5a9100c503480030b00c2c0d4400f0182e0b101141c0c40660040c41000000303062811055401084d06284200030040034402c10140140050002c00140340e000c11103013a4804c032200020004100141c46600074400d01e032154000000591000f07810700c0561404821198001302d0a080c100700740f40d41109030a0706c5105461030490301e0080080420115118106c01c49003080d00705020450a04000c03030548108000c004680e405200080c4144403241c5c65941c500d0301030080100347c40422454064000b404c884010510000d102c00c1c00c020b845841c3c2e054210700000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 401310242 1250 401308992 401308997
    0x40b0409030216170309012a08031b04050904060b030a06111224010f02030c190615140d0501202106030a080d0f2a0e090406050405070308030106 64
    0xa041d01c1403071810802c00c2e140c2c004244131030b480e01d003c031241c90702008a4003907202c2864584860341c550310b141c0204075880301c03c03800d1306000c41c241c1d48240103564028500440ca06441c1d0003200200c030420043e00e01560003070540c45151a000714000501a40c0540e901502c042c0075940e26160f0307034a80310100c40022140960014001034500386481d0b00c242455807010001080000d01100c1d1a400f1504014a0b005581400440603d42a0442c02002503e283c10406400c8a0300300301d4242080f651a0007000040756040e0a14004410000081760200c003660001c1e104d600401d4800340402c840580101415100d81d50784e003d00300c10f108503500015050321400c1900c2a500c107100340c085241940c40240200138a140d050910509540118040f22401c4e005805151550810032106006001c0a18804051031405a030311105000f5024046003449006224091351401400c05550888400c2c00840e403141c802400100010101d9005c181c125010b0421604210348035541c8160781e41c001e8000703002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 401311492 1250 401310242 401310253
    0x90106050301051507050717070b0d0c0e010e0f091306050a0b0307060f21020906030a0609060609120b0a060515040f14011e0e0a060305090c12030711040b04090302 72
    0x84c1c1010480500200d06140311326140082c03503120240c65001c0b0340035207600540c40c1040b21200e0030301042682c0152100c040b00a40d0381c140081c0340070043c000c804503003001c2080002e10f100903601460722107100e81000740500b4458409601041480d8500500d4000424410b042d04004036466100b840e1280016401c0015109001000c152030140250301c10410007800f100784040480d800700f80c607581c00e01244504644508000f13420030282c00b4909683da0060703c08030800c116100907030845000c640b1003840c10415680c441ea0100c5140119001e42140c48501d10407100c0065415501d075540a01c0c1100c000409070344420018124510404640e50008804903081c042c180c58004024000d08840700140d20307204114002a1803250004850582084561102580e2074002c002403003100200510304d2062945903040580101029a40da0016108a8004000d5030404021654009074082c00660a10720a80c1d07442180c12002c1c0b8420750400d48602484045071264014401c086119801414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 401312742 1250 401311492 401311499
    0x180409060f240b090d2904050c04050c090a0b0c03160804030b06031f020702032d0c100c080c030d090b060102060a05040201120b060c100c08090d0e011d090106050301 73
    0x11040c61450700f001c2c000d00c0c0c0812403c131590380ca5802c0e15002c5c076070100c8006514141c00b12802c0d02e8584414074000c0c03003001c1e402008200100414900ca00c0c65040394200b10b41d860700c00180909000303031401c960300012000418080c54002c03002a041d2034055404403031500c03030310141d10440700c254940c0403112908081814000c0084401d840b0764400c401341c0c010300c23418401e04d5500d040c400e80080c1c0e000384030750700044c24001e54800340301521400000c903d9207000c00c849900b0b01e11a0601030348280200740607c00c2c2e84810b9181141110507002201d6840c00e01100064813161000c1d401010440440e100c00c009a821481c0d40b40a03405101d1700410700703e2254a8444006407c005009050b044028a06000c220050b07801001105444481070000034100140300701243d498801c00d0301c803030210720600c2c4900c280e071006034100b001e010485a60f08461a12110415960f9032041100d000101e1089060303589954803d400d4102000c007882c1080364003881d0000850802d100a03044040041c80000050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 401313992 1250 401312742 401312801
    0xf0c060806150c060c25141005010510140408160315020702130f0b04091220120d0207240b2b14030307020105040308010506180409060f 60
    0x2030390806019034501e1030719020f004190340381c02d8000c0039101c00c41c002040d101c1c540300f4a021013403030050000100541840d500d00b81045403801d0300d0486001c1d0300c04c2047c141840004c900075241218400303040710700303200641d60068034000203020281c2d851410600c800101010100000c00700030f140c2d03407501c21f4141e0950402a185a00341090510b245004018130001078030340e452a040b244000040000c1c100601e0f12911016043d1507501a42c413038180b00000c001d21030102d485021800030758440c00d141c4501f95216604d91264880040b0044c3c005504960300030491000a1510101540300149405655602c1280e5141c1b10781200ca80347d8041d014015048503a44541c80e003044044a0b000101101074011604611001030104180301d269a0503c042200c1c0006c10440d0342090410741e600d924001d04000e000b06000c490580001c0e180100025880c103280f07044030749007100110404800d40c080d038180009803012450468403a40d0b103848901d03151285124540c095580762100d03071112511007020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 401315242 1250 401313992 401314009
    0x1b060c0c090e0a0f0302100f020c0105070f080f15061b0105060102120702120a08040e0907050f0105041511031b011b020c13020d140a05070801030215070f0c060806 72
    0x71001481c03410b08201c411401c005581c4001c141d106401241d98862031808909007031644601411950900030301d004070100640180c0800002c0100070000eaa842440c200d54500c4403030611804941c40c04d0200d040940c11003440c542c0301c2c91103459042c100020360040380722640007070512418482d1942070244848420300549410900c24070082c004c8126110406480f0702c1500402445154050b607144407001040c002002c004d60040d00558845a4801104a00905c01c0780d000116025030800800c90340340450000c0045481031351071601342424001e1031080b1440c50b181038070501c05618942e000c2c0040400051441507001d4188032a0099016800342c203554407103031902d507030700304160f20ba030002a80014585082c00c02228548002182514900002c0c45010324400e04941040f100e85a07050f6100f02c00c0717010b003072011400c04c00b9558108080302c88903000e0200951081134541c80350824820300c00500441402213800081d07811842d6603c2c061708055510503c0420f105d0800c00c1002c2c60401013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 401316492 1250 401315242 401315249
    0x2d15050906010317180306090312010801110f07050312041209050603360a0b010609060e0a14180a0c080f090712141b040f0b06040905041b060c0c 64
    0x74a915410744c3d5400116008280660b203884001080240d440c103403024508481000117000e440403410b140810305e440390b000714000d80f1003048401c000100c0490500c20b0701c41040c16180e5550400301e00707103000310050b44142e0043d1002d00c4144504480031910311056030080d4840e41c10024142c204601c0a010454564015131240105204012082d10920380c0b000110821040d0345154092200c40e411100b101e100092aa82c0b0410b800700040103400f13590f180c140c45c10303030b201d04c4280303907032038004844100f0612036150b00300801c010100041c01c0f442410000361032004001d68501d5000c28035001c0b03952170464a00110b1a2034900d2014119000206103802c4540446010068039141c03501030703950825032140307100b01d0300000d0040c0240702541c1006d0141d0a00f140a441000e82035030814080519100d4466200b1441c158207039521003094851200e1640002e802c140c2024903080c0000020300d030081060752045c0c080491040c1c031640703a01107140600182c1d2545001021223040240c03002e50141c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 401317742 1250 401316492 401316511
    0xa0305060306070c0b150a08030406180e040807060b15070809040f090b130507090c050c06060f03120906070f0803010303180608040f03093609030c2d1505 68
    0x8020105da609020305a102281e24505090280040041001d8501581c84001c1a02011402180059103c1c000e03100030500a5025500345481d0340f00d00e000d0308401c1c2c5004122203001c00600340000d445400c1904e00d5a0014a450081c40341407010046030783c0454000c40d07268000080300780c0f0701d107080d00c641c0d003864518080412182031565100c485151010780055100b0608650000411004205000c05404502c0c018800b0b68020200545241c0015910100c140200c5000031040e040040290a00e1140200180040789a5420354481130380f01000841e04120200122008038840c6411a17548602c40c440c0d042e681e62541c02d0040280b001e0000c4084500303011501005901c4c1d00c0a0001c0d04960000041c02c074411041c03030103540e0760240e584018035103440340c3c104140d800003550805c91501c01d06620200003094617a0102d00f00c8010140050102c0c04000d0b9001c04280d00c07200c02000741059101c85441038407034180c42900000c15440468400408010f5004429a180983d0b508569140c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 401318992 1250 401317742 401317757
    0xe0c2d0301020d0617151803090d12030507022109010c051509160503031803030d050403090501121e0e1609151d0403030b03010204030b01080304150503010602070603020d0603080a030506030607 85
    0x181c10804040d50050b25840390151207803249440101e050040382e0360361500900c000d191042034a807030740c1c4901422122f80d0100e85800d001414190000c41c034804c5140b02c00303a2359040b0f188848800200c5400200c001c40c1080b44102d007034000545c0402028440b07111034074040340380d03161a02c81c161912400d0b03a00343c4001203039082e042145031400019520141440d0040d090103004402c0807a00d94050303411661a441d0510051005240d0088215400c8d10402e030b990b101ca0b41501c254040503074500405010034101040741c2c1079440b1007150b2055002401c901c0680c1c00c5142c510a1082640942d908801980d9544902409880c1d0b410440a001084440c1c40500090010a03001d003801c034004001600380342d01d460b0207440740d54080d81264041e42e4042000c0e08030356112805680d8a81041c09520440920240c0303090f1611b01460a50b8102c501c298000c280d503c1c2052811400b94205d000007805568440f040400050b0381400601400c01c0d080c4e0b00000e091924400f007503c2c0c0a00a007000c0d0920041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 401320242 1250 401318992 401319013
    0xc0102030c0d0c0f1a150303070b0a0902030705120318040e0624030a05011b020105040c120f080418061401020c15040b0c030d0e0c2d0301020d0617 65
    0x20600300364000490611920f07240c480e040904600c02c4080c0010101c180d0b080e9441050741d40700a210b4002c4800c003400d0a01d4182c14000c0c141c0e40d228040010304524140c20020780321082035000300700d44c5803028040d41d902c00c0d030f510007050041e40c03e221041c10681020400c441c911014a04005291500311800d210284100603459202e04d4043e09031007002801030700c1c1a07508844040703500c5444002034110340e400d21260a041c1c0c0242605032400c10074108882c6410394180c81400f0301c81c010b580010740c00c82560702e41a0b2881d9000e82e080d00c111b0f580302d8a501036002040900010300001d00c4412607480d4840300c076142840c00c4542a0b00300044001c40b541940e1001d0340d00241c0031030301c841c1c2910b181d124841038050298841c000c035401038003000d0f40018600c0100d84040083c05030200c403100309004105c00650610740f42c62124000319008844501010b5841c05803500100c40e081006c4522181242008080f0f400c0e6032111b80a12000b0361501b008001781c06c030841d4039031142d00114010300701c1181d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 401321492 1250 401320242 401320267
    0xb0a11010b06030112080901030603020a290702031c020a02090103060b09090604150209060d060602031b010903120c050d0c0206100602011107060209060f0301140901060201020c0a031116170c010203 87
    0x11008050031150f4040350301f134a564041e074800d2001d560002c00c0c0741e040c01e94031a0321500001680d0785158085295a050310004800203060780c400e1a4020040d08802c003818002e04060f034003807e00e01c0d0842c45105080c0b030258440d10f981c1d60295015841c0441c00b440401c00340704850078090488103455200c0002c00000c0740504080100040b01c01c1005655a004e0b240011100e0068100c40c0714110f2510741c1c00504250000020f100c3c548141d064440795101c17848070309007202c1e0310300c4003d408101c4099055500584552110081c184c103400c00310308104481344060103c8282000c1c0c0400750380100107000500a010b16010002d00c0320b44002d01103110404071455007030245900050085801044000c542e80e1000240c40b444102c0f400d000c0d07165a52017121016249a0b02081c0b80036406100001c2602413040c000c80f24035004850050001164551b005c0320212402d00c5400c070380b4081c0104131005064200d01c500003e00844058140f18000c1c1c0d09401e041801c2c400c40281558170820185c144945c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 401322742 1250 401321492 401321519
    0x90a0e0c04091112010501210f0f200a05030a02041508010810061214030408060a09030e060f09010c081b2a010f11120c011b030b0d08130b0a11010b060301 68
    0x410a1805e1071128288c10019250148054000c5001070f00b40f880d1001c00c0c1c91185c0c0003410080402c10b00344490084003103410541030200c011150210800c02030b0651350703400740b001140c201064040c01441c20760b0718114590030703030904040200014011401046000c608014403071803400020420080b071480e0400030400d2700d03840c80d03005103080c00268a000f08c000701482980c000b03150900c2501d102e440d180d0b00b400002e14030044110b000c292041051041401e00d0816112010204605640f602c0d00540040d2004440c1002c2150058020094684030000020700320130781c110300c00c00900b144039060b25403102e041c522a5a4580340d89540e40209016a4030a4115007524800e003008041c0c01600b00c006030800201302d51030b0200401c0040c0046040c18154440115103d03100c80c150304614060a080b01521041981640d1002c54800d2a03c0814016002002208030f0741a20700e00c131035070342c0181c58056004024441b010446040210034485028020ba499207041201c040d4a10b605101d020903222 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 401323992 1250 401322742 401322749
    0xc180f0504090f050102031312080f070e0307030212010b0906031203010303080a0b1c1b0f090c050403020901120b13470a0f05090c06090a0e0c0409111201 68
    0x80c0d84a4a00c04144910f0208000180b80c00c040255564604490a0000e50f02c00203812541c010300013004800d942d210361080d0b0700806211001c41c07c5525245011101c510007031506582c1030091a40000c016500c65034464514a030140010581c0000740040040802c40100010700a030040c000c001d0402c03420800300e80c1541c1c0d150074080080c1c1c075901c99420081c02d041448580000401c000c0015240189c07403880c40b5144180060840801030001008002d44688568090f0360307a100390034010328560741c00000d420b503424544242429640c3d0000b520052080c3d001443e0080b243304030500f03001c800142c1c1d03503110700454911600740381541d8520311400c10701c03400700b103945200c03846101d0300144c044c0350044d440403203424210700e901c1607081454400c8416124069224a402510082100d8501a051141107500d0140000c00d240c1d03405d005095002c0b00342d0680c40b0364050008210740b44d81c1d251860103000d11b5a00552102d0030700d0202c0d8100c0c1c444518581c0450414024980155840c440140c1503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 401325242 1250 401323992 401323999
    0x127140102151f080109031e1107030b090f06010b09040e030a0c08091507030f08090c13023103020a06030207021f03060803070f0512120c09011209060c180f05 70
    0x81d500515103c07074918a882c4c20a0105500f000e5042c0141540200080700c00104884901205980c10340c0586003d44480004c0d101a00002c80070070100b80d6240245501c1400602078403107092150030010304101003604221150007010542d440c3c9420139200b41d02080c0c10313110007945002c901d40300151030300704580d500500e070140005451521b40c4404400c40b8000d1101c000048d2103252500c1c0c09404011140458000a500440000c2ba00d01001441605203000688125514045420010040e40c801e080c0511007a1204650703181d5803625198480c0c2e84010304600050050442c4104940210903031b118804242c01400500c016a890083c070b04101c2800f03034407800000046040c00e030040e00740c507408000345010101d04503081c0896101202002481182510910209500300d401e117402102c90b03000d0547d5400300002c2070941c4100003000c400c1e805040110200c00e8a00a1b60260b90b600182115140d4480041000158100450400e000e0800c0c5684080c80d00317109002d06602d4051140354030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 401326492 1250 401325242 401325271
    0xb060a1a0a09091407030e06130303020d090b0c070c0803030606031602010905031309060f24020c220b0a0302010e240301150801090c0801050f012714010215 69
    0x1a001e029180040003060b90b00d100307004d46110b044030000c84410440383c4201090800f80b841c40424800f04040d48034a4500314086401e03141034a084000707422141140d09143e81d0303000d10402041c12190498895192518400d5440d9164900024007a40c076074481400c5500c00d0080c0301050341e03072400b80c1c2d9000d050a010034100400c0050100d0140054405c042d0860200045162000310140c8821095590406051021a6542e10502e07056400e522620021101020b41000c030a0340004810203e50b120788100c518008d5250b000801c04580e02c0c5038005880120303070300c011074200540a40380b040d0f40c0850703400541601e907400180c076604049404511400e070144160101c5420b500d6804120300c00c3d0701d6000c1e100c0d80c488420500458030910020046490080002801c5020340190081c402c416a1404002c0c0d10380000c0c81020320707000071214140001d0886404500e00c1ca1185411407003071400c0c006102501c2d002c00710040b020f040411904640000401040d044191440290811000c605014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 401327742 1250 401326492 401326507
    0x506010314011a0904061e060618080703061817030412030509060103061d0a0c080f16030204050c0c0f01060f0f1d070c0c060f0909230c0f0a0c0b060a1a 67
    0x130207001c00b448003611021087d0015140c01c95002c001611104d45610346d075001641c08001c1306001a02c24000264443c0030107000203142504541c080c4e0340c802d941d03001000703295a070752400d4954452034401655004410007051000d01041c03500c9600c00c6003001c010f0303405e00c00b4060340c80e5581408080c2c01d0300e1f110280c0e244e26a00805a0300b4441c40c0b1542030f15040c00007072400180d0450300d0310a41d4014451680140195800400c0072020103100b40103e20302c5030b142d54203000140c04010440300d000e50061100d14280801485888186803550000056850070568590188100782d00701c0c55030344031214014000c070a031244401e003c10014034034002ca035641301a0304a44207125002c1c000d11040e080c0c10001069070300043c084041917102d0f180c5c41c50701c5407299501701c11101c065100034154114411682c0b00e0140b40080250000e02101c20940340c00c0140022001e40e600031011000003c1e0328041140600890f0400c0c550442c2003119150300b0240340c1052820450321644071100021800507020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 401328992 1250 401327742 401327753
    0x130f0e0406240b03041505160e0301180311010f0506010e011d0d140609010506010c0b060d0c120b06040b010e19030b04061e0606051905160506010314011a0904 70
    0x40700c004000d00301d401c41c1c5911190050044d41044c1d03000c9985403240141090016024020103100d110b00000750340452050000c100e840c003c00e040702c0c9402d556940a4060034400007544c149045000b81c0794081c0f4148421802c90844218910a54195203860b051141aa0f032204414030042c0091034075011549414064041e49002d02468a0303001140814030f0040010240c0d00954041044060302d01c1640c402c109103091b1201180d03e03c0c0054440c081580000f4501d074200394021002801d081030800307480c0c0c0d600e0b02186168107c0d940c420a001c10300070030041030603c03030390f4800c0c42500e080c071010b040540042c001c600030343c8002d0310404036102d07241104040c00d1000d10080d03401000415203428030f4200340008000f41c481440241c4e20300c0811306201a0140545001c03100940d4410b403900b029000c0116809103078591380020480c0411000511030186038000130340501480203881c581d407440c41c01c10310052001102e210b150b4104140d00e0908204460641901c50054540401580d250b180c40d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 401330242 1250 401328992 401329031
    0x10e030d020d0c1109070f1715010c0503090d0606081b0a031e1506140f0a06050c0703050106080606190b030a020702010c0515060102192406050d0305130f0e0406 71
    0x4268000e0412010004801d0384116103c11f5a456511006401c50211072081038410741100c3c0b04e204104010103815455201d0410411403501803400d607402e01c1d0100000810700044240300f9507100d47c4410080c4105e02c0188008940c0c5420b410b101c44900007642d01180300c040c4c0610001d8554014851031210000b0045141156683d1040a41c5c0d2203c0540410b032000707141ca4041c1d69190302d0213070300c08001410541000d401c40708005142e9400036141003011101940b00e001035205070700400030000300044090103100064484a006003160380740caa010700402c44846220700c44068100b1408000d8a0003200449400040f040b00144e610140f600060b1044001e480e00180b0601c02c0606220156030341040a40c0503440c00da00b92109018103490341c81c800c6030320710000340c00180d820760500c003006d01006400a0ba49501d035030115606030303039200081030341d00c100d801a00410300c0001d14600c02c140e90007801c0c3c040c0c01c054402203041c40c1000d10031040c1328801040144400d0307943c44880381240c4103400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 401331492 1250 401330242 401330273
    0x12060d0501021603080f0f060612040c050310050a0b0105031003030507030e150309010c0f02190c05040504050303010f120b06010c020f0907110f061b0307030e0318010e030d020d0c 79
    0x302c00032101c0c0d40c079008000c1034007119101201b00c9a040490000c00300c071209180501c1004000700d003441415144481080c1000e00102c0d40340440f42d07000603694505001e180401c14240d0000540c0e0306d8007130214820380c1c42d00604103040080c100300304551340e0400381040e805d5076014075042c1e4071041140340940d0f00c01140151564010540c40300e8a101ca14008002c6100d501070174002d01030301901800a4565401014002000d60007410b10482c45001d044900450213008a0011032410342c1d450215040f078805403000d4819410000c01030010704140010707030000b0292240340180100c01522007200488024186504010040c0c000e41c1c05d65031184460818004020720448a50408000140018900708102a403c0c0070380203242c141901c0c080303502c0d48038100741c9441e401e0003154a101c031103039580000d00030010b159403030340f0041c8950030030809000328100145034070501c400407800144c030056244016a100f584580b9902661503404111810409e42c035040440400c1124a88200120320000c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 401332742 1250 401331492 401331517
    0x30507151503051009080405040b1c0503031006020a0b0705030703090629040e100504050f0105040501150e15010e0d05061f080f07120c050306161412060d050102 71
    0x400704201c007511545901c0880384101d0803140c03441030b001e8203041642c4000401600302e200500c000c0200303080980000074044001440b0096072090301a841c8200d48060400703646950001c0104003208280c0070044014004030b00013480401281d50718442c2d0380d0001403516041040c0803000c644014000c0d0030411180d039000c20103010f41d44103480307421444182558404501c40c40c0d11405090307400c061092007034500b0030001070519803001c1758017100981b04c0900201c0e9188110701c900000c00c14284201809188120004500002100001103200240d41c001e6818410114140580a00021440b03d5240002e0914504261803c0d0029000c00340c0d0752005002130160a0811802c407852800403a0802000c1e003803540381d541c9460b006a640c804141400d81a58004034080c4181c05107800b00c2d00380c440c45120205609070f01d8201190078420701381d50520040d000c04684101d03654101c04845400c0c00071500c0b05090564800c200e4107220300281890340a503460303419100c1401020b4040b52900f42036003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 401333992 1250 401332742 401332751
    0x901120f03170f040c0b0f0910021f022a100509070b0f12100303120b130603030f0e0316030201050904060f0e04061404120302160c06020c040b030a080703050715 71
    0xc02481030002e2013150308444402c40300001003818a61701c3d055400d24110358008605121503101800f406032500003d0800b13500c2982c181000c5940280300041d0b0003080c4040245c1c4440d100c039910b10504114107014000c2100b0203200103110080010080001c016119010485072a100702613070409080344c00c003038980d80c00050141c40c1d030031001000744003c0458085a03143c42c0e0b12410002c540c20ba25020060000c0e0175120341440400c00d40e00302001403040106000f0440c0c01c03001800c002c0f14020744c000c40108601c0e1a03ea044146c020003400400340c81500074007031418803081c0300309420f5028003009044c000c0100300c01c003240d2038a0340704401a1060b103007910b9009071645062004428100c404486050170182c1c00183c031b05107800018092a40035040b00d1941c82001015030282d04009460340b641c0c010402200046003101c42c1c446d0040c681078001e00b5400c1d1070b1303209000030340f984c100740c240c025404480b5440014804e0030441c1c2c0141c0d0149016900d448962902e07005c8080c3c031000c22800581803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 401335242 1250 401333992 401334001
    0x3140109020102150405060118060f060c0203010f05060f040c0203070b131202010c020303070e130c09140a0308090405070c12090e0a0b220b09040f0b01050901120f0317 74
    0x5520040040d4001d03000c990300328008407520400700004480c01420b60300b03c1801004481c0c1a40c005040000300080c003ca21181c8a040c9119509100c2d80880000750030141c00c2c40a600702841070702480c105142c024091071401d5404078201034100c80007030b405143d503102e641d02c4061017841910030460348140d040549081005100c101d42544000030364400e030003500040d1100c0d005100c0c108090f07042c3d40103182141d80306a03055890724014042d00ea042078008010f004145854420388108c4045600c1344420181480f00f10003c504000c03100c1c07801403000140030b00100e4400b1090f500101021180420b495035000c40844120702038420041c0240c000d540085079450304110814159114001840140da075082d50b0901551224080c29400c00201030502c40c0312903192881ca43c0100d1a00c001240065402011601010044505450310104404404c00b00102c00c43c625004020484901665506280941501250b9440000d0420400c0b1480d0b500f098014040703545036240b030b580c82c07031001e02c1c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 401336492 1250 401335242 401335283
    0xc0b03040204051e0103030804080d02132603091c0c15020d03270503042112080601050f0304020f091f0e01060e12100203070203340f030903 62
    0x81690200c2c42241040e00103000c5a08039070b0a64030703201012007803022076440e6450503586580b024000b80c546402c100b064100322402c80c002011100c08803590f004030a842d003100c40d0243c0700981d4159058221aa8a504034076000006560300b40d4000c59540340c40c0c4200000f114001c0c4221600186800010744c4000ba102c200c0e0007000c90b01100381d4007540e0303114a600c0002c42c21140011010600103a80441c0305025000c0040391400061240d02240d00e0580c803680c42c10b03048000d03070f4100c0781d484051000c0441007201600501e00030300c58604007003041cae0400c80d00180080c003441c485040038aa003c800075042d943c501030300c008028805852481c0c1030500440300c00b44030900b0030303024204080e450000103600c80e041010b1412204150b481c01103c3c0d400808000001081004140281c42490044540f0141e640f0040d409200e16400559946800403003105210390100b03581d10f040444180b030080040c00000b240c83d84940d000284100e1640a0300d010386003008990800342250b1190315041c3d00001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 401337742 1250 401336492 401336497
    0xd050a031d010e06031816081b0405040503030f100b0a09050f09010302011d12070b0a110c0109030f020d05011113050301020301031707170d021905160209130c0b 71
    0x2500381200c9905030310301c00015602c031041c201800307400000400019405a50220301008032004003021f48102c1c1d1070b015404416405d0603044800706810180a500b9010001c01c40752001001c1503409204030b180c503464094481c0401040c00112582c4000003403180344007049503001a15400380c80c1c580742c1c105038500501813501801003500465642450710b006242c01c400e03540c1201d070f059699541c4e4640c400c0740008015601c2c03821540100c4c130744100e400c1801b028001c1784054071611000307948a200159004040c418121a0305002c0d401282000d16181d80c00100b90065903000042c0310700c000c5280c0301049100e00360b01d00140055103018104040300c1c0b00c003001046001514031b58825510b45440816080340710078800103010300d4810040d40204980d403006400e015000f0f101e0003819a203d0b04151095600c10016038064503800104a05c861101f004440c03091400c0d881d2050070000e0f280200c895003000c110002e8880d2440300000b0b15146240c1c181c0034110b50348070702a0300781240c0d691a219000e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 401338992 1250 401337742 401337767
    0xe1b0a021c0e030a060f020f0d020a02160e0f040c0e0907030213020c101505090a0f050a050105100309140d03270201051209010b0904030c02041512060b0d050a03 71
    0x241d0540100940c1500c101e08072007a2107001406002044200e594240042009074184c0b00540d40a2101018140001c4041c00c1c001024240240e41c40122800081c100620280c440c0c01000482200740710310054406855488546000e0040042d125410021104000b95226100b0705149008000c3c0589020a481040300c0c070a1b03540c13400f00800103c1600c183e000f044411002c1c3d9000007a22103a80c061600319803940b840303405e42c500d44991182c1c0418003151048403251400340c0c8072540003610311040d1007178070391140350000d041041c0d50402c400588103280c81100d000803d600d440c5443e05000c1d4081c5e01820454081c4110b503441803001d00702501520590200ca00c203024580b02500302a4407001e065068a036059490f01c0c45d0440908955410000c050a01c2d00659a04c003440101034a0b0032040c80d000703500a80350109001701501c100f00980c0c01c009002c512070301409100300017141304001c0b400d041aa00440120b480900d20003c2020034a81c10720180c45c9210305050340c0249500005420100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 401340242 1250 401338992 401339023
    0x406031103060115050d05041a01030b0403170606030105010c020f040509161a0717160606031103151518011e0b040305100203070c020a090605031908040e1b0a02 71
    0x150382c0d8503c4540c460704241044c40010a00c10014050114025886140e0140c81007813441342c15440c111200d00500000d800480d54559450203120a050300210000b00556071002081001d181c04004141e03540018455203051044081d600e608540d503100310420720301000340c010002e9140030404242e482a0400700440c60701850007002c100c59161203600030503162400c0c02c036842c081c0c25980d0f1144d960f40614486124200a00c030304980344003034481c2c00a19034040c02001c80d0840c214103101c841ca0a10080c40d61007588406030710700148103151042079010a15400941042c140703007000c909200350284101a140d400000041481d0580d60260b45104504e10301d020101030321076252002c148200d0202421039800301000604515040c3c00a65104106180c418603000745540400c10804054011710070710780d180c1d03100380860700301000f0300c10400342e00d60024201039082c0d445a00300e81c462401800c4d034541d1450005402008680c0244901804680006076a10098040251a841c154802621 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 401341492 1250 401340242 401340253
    0x9040f12021f0e0705121002040b0a0306060509300a0b040b07110a060c050405040507110c0f0607020411040b070b010305010c050712080a0b1003230103080403120309020406031103 79
    0xb6440224402e0f06450b584550041111504000400c90101007032010000648030382c4007002d220b00c0f03440c0040c0008000d070400c225241c4003100780c00307815203c403a0800da04209003031010a1a0380d9500b02d010701c55142d0043d03802107e82110940342443c070440a5406ca551283c0d40c404c1040001c4850340603c82e80c05107101e110342d0713201d825089070b00f40003107451110254440c0501070046010342d8401c00d090f440b0f42c20181d1a1650310303004a41036a20031a5800c001c02c02d400c1c142100d14405101d500081d0004590311070300a00c4d50000a0039600031603002a0050f90f455125400c4001010100e07400341024484050f210305ca0784c680300d080c1007400d000848142d401d011498018500a40543c0c400300d5004004e90209554094101c4058200928415000c1e454000e03002558076418001d41e160811907602045c800c48000c081e54010032402000802c0c41002c0b401080441d004409590680358000e50407074486c018810110041d120845002e588140b030000004200101c500c459011000242c041d6034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 401342742 1250 401341492 401341543
    0x40b0403230d05040b0a0306030606080a02040c020c0a1412150114010c212d021603030c08131a07030e040507050a0c021f09061805060909040f1202 65
    0xc1c0c4402d0b0326042000820341c14042131000c0d5544102401c4640b100e4500044c2d2203940f82c407a041640c0c0e00740d00000854100031013400c29810b050007100600443c0c0e00083c4401100c50700402d901200a2060341100442c066545403c0e941e05031801e403085050f00202c40158003d0060601200004c3c4203248070b01c0034003000031006502410301c0340740654114025610700302c04083c14403900e4500303074009002c000741402e13084200224500300000f260ba2020001d813243c0c0301c031b010103450840810240042d11806520400019501500d0300050a40c42101d0b607440d0101c00f80c45025150054010709000042c07521813000c101019400f0744042c43c040d80e106a5004035460a0104580f01901c40c4000117108011072003559020b0112560141c0c40600300c01103840069011490340008420301800180410f20704000c02030b40300c0300390451040701c242070011492030316002951a218044009024800030780002c1c05222000c1d040b10710b170030740103821003003080c2401800a440320a0712541010020240b05940c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 401343992 1250 401342742 401342813
    0x6050901210203250801170a052a1503040206130905010b070210180317120421050f0a0f050c03070f1506050901090b06191812031d0303040b0403 64
    0x200c030181e1282242a400d00c0446d01403003c0604d0700f0141f500c02c03281d030100010307400c200e030000741000840074104004410b020007100c8400341800c46e20407107014111110001207101260b40103541200e115540e11030304c000b1001d0050b4142c0c01490b03c0e601d02000022002c6102005000040c0300705d86201c40c1c04442d442c282c8481303000300c07001d0103036919000d81840003c90b407240500c3d2019000c1c00c0d0b80d0420407002111400708104507004c81308256030b030f0b54480404a039110b0352500d88105003090b41c00e00d58032400443c0c690040e4610700e0104138006691507011400b0780b0071030340380600c0c8006a0740e548519003080142000100d00499007003083c0003c2000440c4144204d401f540d4000340340807401c0c0d103000000c0b0064180c070540c50758002d40400002c4103030b031441c0801000554032911401c10540c6008440b507a20328903544402e10b120290303150400002e03403180040e0340d21024074002c051014000400303e491401240c001c1101d2680c00900481445400322450b00003802c0041800e1040c1c0c44c40441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 401345242 1250 401343992 401344051
    0x906100e0403180b0a03020c070609031208070c020d0302031206040204050a030609320c03030a0e1903022106090307050715030e01021b1606080106050901210203 71
    0xc5551650030030011500182c452504540d0102104120030030142d216109402d445e808011810f000c2640050914148032052010000402e06414001c01c0e9900d9915003143c00704014060104101c141000200c5083c090070800c444540c000e00740182c07885407440e019503698000c6070b1400c0b103209000c001403074524160086406442014155901c90352441d07540c48050a4516011542020406040c01c41c83c90342c98076903500103402c14007288400e201c4c2d1040c0c0c1d081000d2440d00c94003e410802501e00d945801c00000061000c05407000e07456954071043c1a903103c001c9402c0250300c50180c4410102c07000c2107141e10b040c40d0f074074042500c1158490081f01e5559100c0c045004010341c004030b42c100300d40001c004045c4040c0e2194280860014010f58200342260310040194060f5840c110850f6051101082010811807200208511310390910201400b42501403280c0000c0040014280e40d0b642d21900c03403080e0500e0000040040e03503034407000000c069041107030222074400c07034504007102c0f000311800c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 401346492 1250 401345242 401345249
    0xc150f060d080a122406080709030305030f0402010309140d1706090103080a090b0706051005040e1e011d060103050c060430140703030801050d0201090b07050708070e090610 76
    0x600701d2810340a003105444c052082404164800d039160840c030f9110b0000506020400d43d44d1181d110000e0502202500326600034101c44100410718109000107600030782145c0d04681c00c074a11100380d950301e00c0100d0240091070cc0051000310034401d0064481d02c0040c0c84018000d80740c82d010006100c00c402c00040860494860b42e0000c1c0c9038004001048a00c8d001b40700700784d540d113040304040b034a4074000300035a8041038041341c0d21541c80e070400000240305402000506000c5800780040790b1808401580e803c4030001c122107000c841c0705101c0d00c00100b58400002c107444a4140080d062180c1203135030301d5840911003075134640645084401c40e0300d0050100c6069030344400549040c00c0c0c00d25100201e58045160089196910044440c085600f0142640300114000700401200b8154a002000f0007810b81c0228080c804c1c1c10807120050781c20018000607603540401a9480e00c0303147c20000c1c90314186500c0303020503000e018000703d25400407070000c0344681c6c00c201c00c5444646480009001d500c10b03a12 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 401347742 1250 401346492 401346503
    0xa0201021009020d080c0a17090609010e19031a0702010e060f070215010305030a020d031e0b0f04020a090305010c0207060e09090a0b010b0c100903080c0304080c150f060d 75
    0x1020090401075034000c44115001820420f008040380d51000341030303803168002100903803001420508008140700b8020680e144a902642080c1c0340001141c500e020f80507144d814001e8050361200e642d02c4116088031000c01180039580358a55134102107056108012020b51500504800100258014000c9107034a881c2640140306d50340d904030554400b078401a2080d821401140e6008800113891000c25028500400265a031140c1e510300203894000d0000e02e46d0709150501504502c0c11320302800c00f02065880141c00314840c1744550000f2103118450001d107a0007440030542d1520ad6520074404420f80344505c0003002590b00c903440c26a6201040c4c070030f01001803818900620303036043c140e40315604020b100382214030012a80d40d400300380200c00d03045401c111074082070b00001d0243c20450045000c2c4891001c1002007001d4034020038a4030004e02c807a0303a0030f00c00404102084101c0084644a41109060303994001a00f098040003440a880b4420a14514004280e5520703141c494000c0d41a40031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 401348992 1250 401347742 401347753
    0xe06060424050f0307030507020118021f051903090203070e0f220f050f0d0915140c0601141e030d080702070f140a0608160e1315030b01080a020102 65
    0x507168400d4100c410070501009024050f401508915002840c09070060b03071804a45807070100030080c00c45e10400d1031040001003503920080940c448610101c0003040c1c2000b000c80d16850f2801c180c07124400c10082c20340d8000e0412004c500ca82e41070388007d581c103200b2001d4a5001e0703a80ca90030341080c1c00540c0c5a5841d04100300126020a9441000c480d505038003001c16407032403d0302e4540741c00c00034901d07600303a5240e0881c0c40c8a00081006124007102c04025092280042d828450007070703400540082000240240f80001440c0740d801749058840c1c0d0211074088880d40e41c0c560181e0710b46030402940d074501a4004505018051a024081c1003400f440600101f40d5a10b0782c2c1c2080701c1189003c0c0040b825401034010105d280305584110303101074000d140c00071440ca0641402c2c404902d4503a440b00b002c0007015818030003d58807a0400141d0003031141380c0443d151002000061007132507000c48452240340340402c00b108015400e074009044070b0140e0b48202c1503a90f103008507500c42211103070003030042c0c000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 401350242 1250 401348992 401349029
    0x20703150504020a0306020d0f1b17150a0612110c0c0d060b0607050105060f06030603070e0c130e06030f010e03120a06030614090705031906020703030f150e060604 72
    0x141d809194064002040c2c1d52801d50750351502001c980c0051110341c207458441c64440c040705d005019102042400c01090b81182041200040c9880358100180010000c1c03003001c01c2d01503000c907640e0507100f1001480994465aa00c0c0c000d0119181040100e44d1a070a15850b0800180104d0a440f11000c041010303000c800c143d1010800320940003082120b24076a80e2903004c21070380703039407024107a02840f880000501d03080c282c04000c20300621052803440355408004004858801242e0401250401c1141c0c0c100c0740c6580000210600698150030307a0b6841d05100014a202203207a949d000b80c4064054171049007011500c1030985040d942d01d440c46910400c50000321600b40c2c100942d03c6079980034009451070b00c1c1d51782c01c81500c01502080040c424030380184020104140218001001c04400030200b00944013042159070f45260800707000c560307000c1400750906d4081d40103445050158142000b04100c118903500c8600454081c0d4118400c081000030503500b4400304881c15100e1024002100e40003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 401351492 1250 401350242 401350283
    0x6010b040605121b0d091703010312050309010905060a05041109040b0c070201020f0f0102090112061406070219030b1e0112081303080a0c14010902300601030b16020703 74
    0x1016005000c6809411402d9071400f5004c00608100c10a0503000308054003d400c00c000c0344041040601e50424042004000041c4802040d1001e944941051a01d9136910b9175254010301d034003213000e0201c0c02000300300100d030000b542c0401e200d24452096210400c0c02e400a010540408440060001014034042900183c503000a0074415105104685000c520800590300700b03107180000703091981d00801c10301520360300400f250001205680d41000441e251410038240b42170040302e034502884000800005545580d00f4400401c80c00240b40c0e0400c60352880d107046185421554183e041c3e500040500d40090b0289029048072403040da5160b000943c2c0c0c03540c804030707800392490040c40945e50714008002100400a480d00c1000703901d41544111160a0801c43c14007240301c005404d900d003402c401d00595401203507055a84c84d25000003d408098200070403002000300c4149a40c0c4101c05c000030030007842d01c1c90588a010005203100d104c15a00308180d0b030390261400b00504098035000000c44052 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 401352742 1250 401351492 401351527
    0x30901020d180b0705010204090c050a120902121606020d03140105092a0715060e0f0a02042106060f051012110c16060203091503090f030a0c0506010b040605 69
    0x204140906204183c0c1c0f0b8007040d5195108030000c0b901a50042400c1092071001d210304c5d164003425050440c0b034410400d60040501c81c11003562443c10b0303911080c200070740d1100d880c0048696600d0b0300b01c442c00d102002198040340c40c64400e080051060130710311002903109000e080c44210350790420345032690a000422000090003052541c0303034011502c4021810a100e1502410b181c514040035645100c0c2e41000b9160400050b50b8820301814424100040660303401e40d56441030f180c11209086480b5460b0810181c851a40890404030b8842c003a030701d41a4010885030341492042c50204101079031011541035800c4d003441542d0f444044942d121140750f0186100082c802e11180000a800000514080b91500010005215a804001054209040c08400314046c001c01e00066080401d0309000031000c5500c044008040400232001ca410300c40e040161440480201040da9124031002000031b0046034064400d8030603118540c000280c0420100489060310300d03d503074181c504002e2180b040d000c072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 401353992 1250 401352742 401352767
    0x40b040e0a09050304060f0f0906090504091401050903130504180201050c030705060c0301060215090606101b031e08060114091207030c060f03020309151f1412030901020d 75
    0x99498410720800a0f800f800200080d000c2c81d00e4882110680c42c00080020f891200c42d81d09000d04400b05010884e00010b00b10100da00440d804620714002d450500a00513480441c10003a40c02c0500740b0802e81804030181081e4240110f01b05280e1b640da10800003900e00d4160b40951014090b642c1c07001651103000117004c0c030141c3c8000c491500000741e079010b01d0040c04032452020b0f08804070051002070380c1405800304480442e905c111450515094903900d46501500c898403034180ba400b03020b0f81601980440d406081d60320408840c46070300d420007501516000381c40728071507001c1505103d035660203030a100780120010b1f03440b900c10441041c004007840c1d00002e4503e901003517100c841c54200c40200510000f031440b442500844900d4a036024095868485101092500510400c0081c0c48000b52600340a00c50201020b4070351102c00080b2012201140d098010740307003070000841c00285154081d90001020f80302101500703140c81c455512802032280c510b005800602600e43c0f1f1901c912045140d5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 401355242 1250 401353992 401354011
    0x604050103020a090b070812061e2710030c121e0602190315150c0210110d32090f0a1203020106030521040611011806020717040b040e 59
    0x617510b410b003203401c40e0084281141c2030f00c3d001a2200131208580b1547d9005038056030700c41c082c40c503040301100461809544041c01050107602d412104009401035002104c140e00b00081d2505201c1c01ca4420143c841c08240d805402d42d01c0b0002d48041024020301c10540c0100010051410521b03e903c0c640300b244005645540d0213020301020b03100c265113809140314058500040500b17001030303280381040e00c950094401d441b0301d060765250700307800c02d44000030154116075280484082c10030540340507411041c442031900ca4904049444c2e60010000707103202d00d098101c004107110018103a44c032030010841ca2000700005200c1d11046003801c50803082000b00c01440110001e40b138910062017850140c03030a40050b91181010006e00030300f80104c0f80101c85451000220502c0581e20b0741e003c1c0700354440e2204100e1507100b424a001002e50100c4204600c408030700c05104150304005010703400001c0151a4180c0840700c2d0b040a2071003000f01d50440d0190850581440e2078410840d4820100402503c103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 401356492 1250 401355242 401355257
    0xe071710050a0603330605030307110402071703040311010606091e090513110306010501080708040507031a0121020f011b060213060908060f040f11101218020604050103020a 76
    0x200d541c1c4c18070400800c003034240582c580c175001e078524070030001a01c580d0180303240610510040c2c40100880341c00c590003411500391002d1003c0454002e101d0b240010301718003d020803a254540d1040020b5024500a44d2400440d900c00d0302c0329400ca407920310070a000703e40d00361001c0041c15440300403194800c60300080c00403002c5c3c1d0b07010304200b580c10803200306000048000661040294140c000c007200d05094004050540c10400007a1509002400e1401448a048005020000e040114002030760303000203150f090204448119152840a016110341c012488507a1010f21448500d20310300d094000300104031910005006580c1c0360105161141d14408040c049000304030b25000800c0642e800949802c040b13890030000400036813060300b1080b29900048240404000340d112001d80040d0054000349440300d440c60071290301c8000000d004d0300711006180000d01c451300b0443c20004096070320030502900d5558051885552090074009520850920007031002c0e5119501400c0402940e0038140c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 401357742 1250 401356492 401356499
    0x1508060a05090a1b0807140c0304030201030e0a0c0308070b061002060a020d060b04180b2e05190f020f070b07110109050a080615040b061e0f0c010e071710050a06 71
    0x1080c642c8403c12a400308105c08144030440e03900180800e00002e07814015400d1500f110400c0d030322031150348806410141c03580010310059000340b003a44001a0b01a016240480d941e01e05440306400c0f4840907206242d071000020420305000541d1196110f860b4080d158558412403d05c00941100c1003c03100c01d566504041240c9000030000c00140c8141543d8401407100c4000035019a40003164040c003070311500c41007014805c020802e10704e200084010211000d003001800725082e0203030354404903050107005140b00388103030045565005040580d00340c4126001c440c1c2c81a54800c41c0b071040000301c06003000500003107407820060011880051504108455482c4005905004a03401400036030300264240281c00305403904003400000152024041ca611200000b4140e000713505d078140046001c6403440c082c03940d042040307a1030141d40d090745640310071200c549103000f020801300070b4005200701400032501c100d1842c00c0f0b500c04c0074201e0051004c542605035400107440c02500c03000c1c400761510000b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 401358992 1250 401357742 401357771
    0x50904061d0f070e01080c0907030f0f060b030603150903160204140403271508060102011d07092007021e1807020c0a03170a09150305011508060a05090a 67
    0x40c201c82c11031500504a40381061810b81c03562074103920100050344412600042a155140525132000880c1030000d501d14800d044800502080264040c079146008804148424100040c5009a5069046131110452005840300c0c10b0310a8480c12041e030700034000702286541c00c02d0348103481803014002082046000348c1c003a00300f00301500c0403404940b442910701580d0000c41c0d1904200000e2403829800786240c015440544480e903240b010810200ca00011040c0c3d00075045900c1ca04034004000d9019250324440980f55000c0d070050030034447c1040041d9000488580215080010f6419064036101c680e030308202c01410029402e00c03801601b1071b810140c5603154107414104141051004a171403034080c4000b820704000500c8107204080c1d41c03131305001007500b284511004107000103015540f00651a8291510000c9078054201200510b1000c030071164160440c80c100c1c1c4d52041e850520074900c040c2034441183c2200d413550042c40c000401c0003246026826039402c00c913070401c0042d141c1d08000d5413 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 401360242 1250 401358992 401359003
    0xa1107051506011803031b06021201031104230a05060d15061d040b011406071509030305100e150d020603040302211309151215050a06050904061d 64
    0x4002540c1d001d074200062075810a603030407042c480001e080800d02c0d0550358040e10140b29121008810068110280d0810521740d04503091074880005a03c4c4960b074a05e410395240c0c600c440001d002e00d00344101301154801a0a6290105c420040888926902d1415402c01014014070041d0702034414820340300420300301321035a08107800d08540402d105040102c0d065100d4103030050b00c07401c02440c40c108008965402d851a056403584c040c1e00103199640000034201d40118140139001075881c0119600100d5982d10606401e0f2194800f407002e40d0350600f00c9200442d441c8140450088800300299404121103048030352458001c1c4a100000d84c1900400c0c095001280d0480146e80000c3c400080f080c8010203d005026040d0000f603d44103400b00d5007080740740984a2420110b80310854200304c50120458000a0441c0c9100c0203484000360402551034140240c04007001c5280c0030100384840602d0191a0a070750001d48a034400e5244c41d81c5040041078084100b070b4091841c0f00c169040d40c4003d100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 401361492 1250 401360242 401360263
    0x303040e04080d0c140304110a05150d06050f030d110304031e02030c1203040306090804030f080d1a0f10030f050915092e0e06010605030702150f0a110705 68
    0x2a10780d2034204040f0900120b13000c0c440e50718144141d00304240e00c0b1007030140c112903100d0f61112103403194a00f00000700e070740b150858008070360000441448064070741381c41014140c4000010004d2000c00d03665402e0001154000c1c2441d501500400c1da040e4071036009410708040030100a04072440c00703039652114011540704692980344000c100142c2010740c0740c10401c5d9054074104841c1c0c0258410601381d0a42c0d6403096201c014045500c1b00048010b1043c60010b85005607085008480016642d140c90100c2d0341c4201c080b05603a9180140a04100c081c1281c0808407c001038245141240300d442004201e40b040d4110074100740d125941003490781058040c072030069214030700810b00301060351004800070400070b107010301944c010301ca002145108002042c00d005181c0403180300b100705054040700545040c0520344440d200705000028502c0d4000003c5114815540c2552602c0303c00c20701d25608100d094408035410000900410500002a03008000c071201903000c4c145409807030764540307090a43c1c1c0c46 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 401362742 1250 401361492 401361503
    0x170a0507020405061008011701060b120f0c0c0703080903010b131e0203040f060b12030403120806011d0112020706050a0501030c0503060c04030f151a010f09061d0303040e04 76
    0x84600442c14540582d9030003a00440740f80f8001010414000c040c410140701e15015028541824004540d0a500100c003519915014690701d00c2082480c50880c0b1042c1d501c01e051b1108000020310740c00091040e04d007103100c0c0c1c3e00074140b0305166803110b100c1500544410741c0d0555891200c8480c40e547e00d451205001a185000300d0582696240c9205a00341c0c0d80900540d80c2c0100104000074101003002440b180d803003040041c062a21001090385071903038a40d1340a4500c00003801005012458409220400f12581e0b4502280e4580004490701028500e04a034020b00c01c034007005207503024410300701c07484a08000040c2000031946503c02070f90b40694161900e9551080107005101d540346120b00601004e400070b00c03050030000d2035000070b803103688800b42c0180340c0d100790740080010107914080700d0490b00006010324900c0e0070950709101101d104860100b0380e800006000c15000d6610103048a84545591008890040f03592040c80d00c0b50401c20fa15003c108404280c00802c07050981c0900d0140c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 401363992 1250 401362742 401362747
    0x14100905060901020a050904020703031503050a020319032c03071e060912030c030507080d02120703150303050c0f030c03040f0503010510050111010b10020d021603080313170a05 78
    0xd0624909100d0040c11881850340100081c065840d008401c80e030700c19100340c50050b683c900b0780c10110001c017080d2689140c4020040000800e128001440c404418001c030141e0302c50100501348014104d4240c0030040100d845800000000300703d840d8056464521603c50301c0a0040c0c0030000703070604a00c1d4021009603000f0301080100280b040c2c041c20b01801480c00c01d05201428100c40c034007001003090000f420420103010100c10184544150f4400e1a0702c1207001d44c80e41c4d02c64000070040e4014524a032002e5041d0800200d0310751080c0148a0040b001c40c42c0381602030300755102107030141e11440351001c45205004a2020b021070410083c191011014042c6440d04d0401ea0b42d00c0c90001d0660000d0320a82c140420701c010014600c840c0720864909080101410a0f107131b090f1809021098000c55000f58020b81c010b4486801081805072450641d00b03482c03501c0344030006404204128000a40003010900008070b0a90f0500060442940600c150001c0c1c00400c1c00100e01541c4106940c03400107002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 401365242 1250 401363992 401364011
    0xa0905030d0c020115081e0a0f030305040b132d0c0602010509100c0807120e0d0203130801110d0b0a0f181d061b0d02030c040509070906020303060d1410 67
    0x81c8a109000d5850500c025110b900d8200c1c056500d441001c1f1486000c95108154480702104000441038a03910446803080d1501c3c0d0705010740113000450382036415110020000703d0110140d0003513400e1562000c06a4001180c104000066210014400391104072021b101008550880382060051681d58008034007442c210b07032414201004402040815424010a80c1d00142c10001896014400d0700d0804282000d100b4060041c14144181daa56070150341c0b02516015808401400c0080d0302d9200b00b0640d59455080c20300300d695950319555030700000d00022040c40d04c3e9801c2040c2c0c2100041010440301c2d280c015000d12005c040d0300040780f26842060325058008a4014451513101c00041c3c400d00f02c22000c203c0da2281c00043c06114180d01014424020b41040310942d520f810301c10600b19281d02e0114401e15a40d40310340541403180030380c0000613101c1840b803103d841c00e5540d2035005d51304644407d020704c44500048242122015241c0090600d585001c02800c820090b4285001c11105074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 401366492 1250 401365242 401365247
    0x2a01030207170d061205030d0b060405061804050702070b040909080c06010603090308250e040219081801050c041e090e0c091027020d060303121401030f0204050a0905030d0c 76
    0xb03095004603002c170000d8402001003440401565600e92109002166951450002400600c640c0c1c1101d0340c0180040790051600c510140c900b014034200386c45c2040580c1304c15005076590251485042c408940410003841038407059001000094070a02e5440d0070102d0906440d414030100742c000c500000da40e40d42110626a101d00c0407a040b4504651503607045c50b0449900303003507041101e0306400340101008901c5e01601d0b0b5504454140e88195108507440c465081c3c0204100070648103007a480c1d20201d50304074007e20601c18903005000c070b05000d80c81c0900d003514410201064403000003a502c680704000404c86114024035400c4aa6000a0a009000c54080003005200980240500d14101b4070600421940014001034403d203222909000c46001c0182e02c080d1007101c4108100504101e4000304050304140d1583d210b82e8121400e201401005500280f894424803003c0c114911200304500542841c0e84000d42105041c04003003170101c200d4440b2840e65000c20030907a05103a4550f0348403800f03075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 401367742 1250 401366492 401366501
    0x7020d14100207020604120f06180201080603010c0203031b0d050106051b06040305030c22030b04020306070e090402060904150b03011e0506071202070f090603030305092a01030207170d 81
    0x401e4040031400c105040d0085040b50140d80111b1403401341c0010f2900500402c10084203245921501c03c0c0468902c0d980c40b6210001c0c09d543c200d01003503083c004103215240601030444810700b594000d50550783d070310741860a1005100d9000300d0040c010060340440f8001405114042c010584440c0e5440305c04104c4107514800d40b126070015a00098188800207502004580e0090b0010344043e45406103d8988540c01540e0b2041c8051155502d800208000c1c1e4030711000d10542c0205c050722181e6807003c03002d40700c40b05601344032030f03001e441400014010301d0084040e204442d0b016000094040320003281d018909d14036000340c100400007100400083d440c40341265150003081103d041c03003a00e8000814118002c1c80342c01400a900400e214000a10070044480100040103182c1410740c0c0e2915000018a000c4c0402e030b001900b0900003403040c520000d0a01c03010100c3c40d1303260b0300401c07809481d54456074050360602e04160b003c011101c0450b040e1011100fa100e280c0d200f0641e00d41e40209800100c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 401368992 1250 401367742 401367763
    0x5070b03010e061c06050c0f07050f16060206010605210f1602010207020102060c160f062703020a0212010f0906150501030c17060616060b0901051c14010207020d14 72
    0x1081244540c40b00300c03111401d0134407520361044001c079041d180c05206d50014061814080039250000c540310086c0180042e8144580002c007040c6c0710328840c13001000107030300080d0007a5405680540010050b203482800241880240c590b25440c2040707a080c4504d02c80790045d02c441200a400da0b050003898541d4001700703d5015118002146080409e81c0044d40781c0500a00400301074a021692400d01814641d442c90000c0e4442d000c020030400710315100700140422000003440c18128400d40c1400748800160b141d906805400400c0c84000e16800c01483c1d4000309400c1c0070030354881c1241c01d1004814002e840641c1e200308400b0511038004400034403030703040aa11042c10903080040c80c65841e07400560b02103196840e90703240c01741541c42001090503807159040710f65455020041c0c007010301005034400c0b81420000c40344902c140c0d0b6a0010080c05a42700000311202800d5020500005855003e00100035086400003504100c0203400081e000d1078041c00540d100f210342040050544018005540c10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 401370242 1250 401368992 401368999
    0x90903020c061809040f060c12140f0c090a080106121704050907180e0f04050c240a0309050304170d030905100e03130f0510110d0c030c05070b03010e06 67
    0x43c41001122400000c40c00f81141d4019810703000420280450050101e00c810b801881c01e0251400c9800014002e50062030a0a07440e4a42011b211210480100c0703079004242c450400f00321502c8030316103440c81c3c2e40a0444164025001100010403a8003070003410010b01483c11071141d0b86089027816142e41007209aa442c0d600c2c2c00300300900c6281d881c034004e16080039035440c0122500e5481d03c1915076610302138000107400a040341c10421310f91703001710f0400c0c41288108241c410398007114084c001d150649000c0c50100003040c101000c3c40300034101c05003003052030514020420845940b0b440b421a84181c100b005d80c4102d0760070302010100100405452034029203020800c00045803220764840640403401021350340c403080702846c400e50030810360303076415000400702c02510360b50f60074440c1c503d81d24464503001d4400c0810703440090f4014000351600058140162007030210925040342c4040c80d2240c21030a018104014a0118104001241c06440705501e801d80e00e506005514041d140b00401c01e510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 401371492 1250 401370242 401370247
    0x20d05030414060310120510110406111504021c08031f0806090303130303020f1b0d022409010603080a05030114090c0a0807030b12060a060603020f0f0a031104090903020c06 76
    0xb080c0175842c01e980300302e07600c901c0b1125101c40107140480c101201010780104007424803444002c24414600100100d43d1280c4951b030300419006441d50701c0d42c0340c0550041d0310740b407108000f401504207603080d4200c00c164901c10340b40c420090395a003111500f081d1008000401c1100b110002c50380402540c4001c1e00f03614008001e03519080c50601c0d40da21000f8001c0110f1800c00d13003c24101406901a01c03009066084601d46480485011b1841d104071901151020312420b41e02c0c0b5a242c1c008a94000c1109120003030f201d0800700741038035080c40100a04184499940d44500101160040026103034441307450f5240341d560b51400e5245c0310f408102c00740051050f031042051000611818044922805203820700c680c07642d4640c00f050f0020040109a1034104400010b0000c0b034200224803144a0311030383c0c1040119030389580044040340104040400c580340308204a000b80c8030301c00c0140404001515000c100300003880822181ea802942c84040656110900c00c0100340d01886298403282064034500d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 401372742 1250 401371492 401371501
    0x308040e13230c09010602030307030501140a0302040921080414030f070b10031e0510020705070e090316110f0f0a1e0e010e0702100605010e01030513020d050304140603 74
    0x41c10b00203407911402d20061200450841c0c05100c1d603010110002c01000300341da5102e50281d2281c2c01102c100c40040d2610f00040780b2840301d01620510303680084d01c02403103d03045500340001884191002e0791803c041898407013050a1040c2080080c4401e036494052600b01890b007410482c954a081041070381041c010a5506100801900c100e540c02103400507113512206a0103410380101d4201400e02c0700030701c0c45400714003030114105d05480d1158044450030b0000c1c0d146282280100c0c04010407a42020402b00200095541a107030401c55140075640ba06500928800784850301c61400c8400000620b003050755482c201108442103c0190b841c4000e04451130005041d049085c000c0a00b16100c1e800c5803100c1d0640c43c0300d0f15004d882c040d60b0555665840c0d03840c0429440084820800600c0fa0010000d500881806500115401031311204400041701e001540640700040000c01c11074008c90b14040542c0e220458a038485d4080c0c0e01035a0f8039800c1c0211440c00030f0754564658000d290400900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 401373992 1250 401372742 401372753
    0x20a090e090d0c0f0b0a0c0f03050903030103020427030e09010506160602030c041a0403020301230417220905070c1a0405030705100e0d03050115030507050f040308040e13 75
    0x61090700c1882c90f0100c1a012030785050303003142d00f9001000d00b90782141c604102d015404d9600c1303801d1200181e00c69030001070b4180c03000c0301510400c44c2d90088170b8200f03000410050400d50040540c2c803050406860038101e0110120221034584075080c0d000a03032071400c0c17400301d042040169000d4003003680c04502c2c010b03414110866035040660002d040e65400000298280c00010942d00501203034807420710010305105807241c09403c14001a8402e5107010000101c042c50070100910714501c44207003000654031501d54005d1400c0003c0e08000c207440030030070303041881560b424040908010700c9130459450b003003051180489074014807450a01811031419030200d100603c0020b024000b41015064a03a00c1d842d20078150302640400401034842c5c0b648885030040b454000020000480d0211910461130000c201c080c1d91080c0702d590140c00d23100315100229482500f02e82da11140505240380342c40b400c14903038035066005034000e895800b80414140034009204400341c5d04540d0b0560240b4240341030b80c484 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 401375242 1250 401373992 401374003
    0xe0901090b210c18010305070b1905370305013011090903030a0506030a0f021e13020904060b0910080a06030c140f09091902041e020a090e09 62
    0x8208000916180d26400c0c15020851260704078030240c204d4000d078440c281c5502d4916020b000480701750161100103e404100081602d8a44134001901e00c142803402c441900d0650101c4180d1224200f0034520030711811101c202c002d14415a010180146425003c00400b01c40040c0c003e038101801006940c9100001c040444400305542180c3c1060034040c0c2c540354403407142c4140c00581000102c030800c2042c100120155104031403000042c07000d95a01170806881d8100618010304181355051054058144081c910b043c0f0007048490740c0110801400140107680c4055050708810b400146016150030310380504401000701c81c0010341002c2201c800608110001d420703d40400c40004000794042c01c11390030200c003c54000c40c2d8920b40c1515442d0481c0003c104c076170b80a010300c0c02280f11907803504008050741c0c810740301c62002c2c001410400700c5524800c1035803007059034030036111004120710040307008140780c500d2010100140d4840c0d99070800781c41c800180d4800132002d405081080605000407a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 401376492 1250 401375242 401375269
    0xa0f03050c01020d0515130b060406050a05041205070512060f0103060c0e03010f0510080c150c0a1a0604180b0601030e0a02040f0b180106050f031e090106050910050d020f011e0e0901090b 82
    0xcc09640b61640300004440901540e0710100c2c940c8122070008040c0a4040f905005651060707a09900c58070341e0003142039880c92f080c0c07500706544007184010401300f103c0380c2c4030781403040440c03030900703601400000000d0031b440020120351903040c1e42c0d074140b01d02000e00b43d202e01e0040c030841e00500100407003000050148000c440c480001d0840c002400301c25914184601d07504190301c404402c0d000c0d00c180014030388a00b8110b0310700e4061403401108c2c0c0803107448560044005544810035084d00d9840400460141400d4400d4042a10030311141c140180d0715405040300c0c10a104000140d01142d801c20021103103448001e030b80c2c1b036103003600060001e01d03405421504010042e0700541c0d41c9450700314a039140d441084211400d49031000040c8040f1080c103401440482c4c0c800c8541c900aa15529818a645030681c460701e03501048240004005041513541c0617502501418008000b94801c903204e84002c486002c20400151038441280447c523100440134058190300404001074580700010030b43c03031342c42c508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 401377742 1250 401376492 401376497
    0x6020a0807050a02030a051609020c1b03010f140a050105010813140a081b06062b0606050418060c030c0804140a120c02030f0a0f03050c01020d0515130b060406 70
    0x1d00d4905219040104010041d03020701100c01640c86030a045440c1c020004d05c44506040702d100c00150403a050096940b143c0d54040606401c04600c40100341d401d00d00f9052640554071071000b070004600f43d00c910f82940381d03910448440c52501c3e20107402200c45c140c000754103102c00342081c070491002410b581c08085a0240c2c1f43c040c24901c07840018541030458500520003031000440031070483c032010b245aa5004007000311003d54540d40100310100d681c02c00041c490004240c81e40300542d81c280245020700d4010000001d15513210404201500d05451880c0e0354801c1c42580f58040010a10919004114500c0c0402c211010b05034000c00c803142c003420280c2003528034241100c40d20fa062000c2c3c00c09540c0450195030311000200041c1640d120b039070060748640a4a280d500040002040b55101c096101100a91258403607074143c840d40c10001c62000e0b199400c0c0060741600b0800c0c882c0f00e000384040c4207091043d10108040014040044107401a441d05000c0c0c42e02c2c1c0c0d13032030362001e9605032201ca0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 401378992 1250 401377742 401377747
    0x40b0702060c1015230114090d0206040305030c060a0603050703080c030c160f0608090c01051608030a201309051503120c0d0f020c0d030e03030a0e041506020a08 71
    0x1c0201e01d00019041500c601c10b103130011200401d0240c121403000c903400c14001c00e580b9121402c0090b01c500814003864080b60441440c90300294a8100802040600420f01c03a9070981c940c003c200d03950801c0e002100c455000040311004c64004000c0c0d940d1040340d0741d405000c59811955203e403039080d10711009245480118031714400540600a039585a480074007120004480c80b110100d0404035485610360703411048102107034651084e8241d44c49610304100510040040030011a010f0b800301c2580900700c48900404070018040c003004500030344ca26040440c0c0302c0036000e01805101c4c010001c031403005108102c10003500140700072120071141d02c40e0000501e59905160301d18404629500385615018030b4942401901981d8083c0c00324165180444200840b21300081e200401c124200c840564800100666103113013050400040c20b00c0303442c211200c01c094502107440c58010002400c0414091116448a406d240c031071a5080c15039101e48484051802401030340301d001c445c5c0d01400d0302100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 401380242 1250 401378992 401379007
    0x90e090309060906041d01050a05030c06040509102403180b040605060f0a0603050414010204050a0b030a021b011b0206070c0204051305120a1106010303080f0907150302090405060303040b070206 85
    0x190340a85e0000c00401100f2000c261000494801c0352101f40505403003400a40c001040a08000624820b8864045c0519240a0400c41008030b80390000341a4001040e80320700100d0304003114030646900420140500c800502504805803d50f010607036800030070301e00c0a070301d440400d04600c0301581141d0030840c00a502d89880380841c0301e0b026203040310740d00044080030000b0f0040d45a4400c0d032145004d40042c00b00c0313444070f011789400d078400ea11501c2c2e448a1303010802e2210003601c80047d90407665440703005140c501d850b85d480d003240055600c0a4101e940d60320761502c0c0b20402d000d031200d04a4051020380462710305260b020b0945ca9011901900960785d500019406800d00c40707090807003a40107002c8507000d640c850b0b03aa0030158072541d9170310001505117031400c5c4ea45070002540d505880c0c0c980c036498182d0356004204060b4503030043c85910544a08000000d00c4154221100c0c4a01001d40e000750b56084001c0502040d605c0117002140680c1c030401040011072805c030b007a10320441c3d0441b0b00c2a601c014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 401381492 1250 401380242 401380249
    0xa09142802011e030906021303030801090203010b1e0c2a01080f1b0d0204120318030c060c020f0405040503090301060b0309060705090105040b13031401182612010303090e0903090609 80
    0x1c03100f001b03101c0c6100052100103800e41c0e0220300107c034842c3d581c071b02190703890b440000181e010030301c50480e00071418041e400b429a1600c40b82d01d090440c0980c080d0520703d0500b200c902c0c4c0b60b00b200303007802000b00505088560740d9981903805040b410070700f401007540c2032200c0311035080940200740e490714030600302041605010310b108940f0101d5101e4402c3d515292141a4034042c01210744d4200c010643c1668075401c29841b1201450460340c01c04400d0307070341ca0315200080d1420700c44481c0490303000d50020340a0080d81d8423032180c20301aa00442c02181c03100010000d050031161700360854020200d040c0b080001703140d03001812648c071a0544c50701607180c0c4c000d080142c8403405641c014004801012440c04004855804010304682c02042d910b5151844105041d00321070442c3d0031032100010103104103010885105980c0b221340c103191844008240100c4100000b03402a00c000c3c000003000740010800e0560000c0c034800a46040c81d201101410300d25601a0703240b00e4081943d005000c00b042d591076554 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 401382742 1250 401381492 401381501
    0xf03240c090405040506102103051e0c060103142b05070507080a1101080618060a050a08160f06481401021804050a09142802011e03 58
    0x34041c1040c850fa040c0342c601036441d00c0e001c0301c0c00c5a5031000312100148003103011064281801c2043d80e0800142c8494804039081c2e03010b110503c01107041c030a18070042000c0d00340100f200b0003444000c2c00055045180061422441802546c060792200121100d42c500032202441c1c074602d0312500940e81320320441c003a203850090341e4000c1c0c0302e0b010791300e80011030907000304501c00010710800741c0390603c1d01110015140500c05442d4281c00c8031007050140100f103086074039540c000c03e004014060341e9568000049080d107258108150640107030404581c016200c943d10409420920007100c0664101140104104001d10040102c0104c0c01c1c8111030400c03141a07404940c0183c1c5c140319500c3c120713000e80307550b11240c10307101207606144d03000c803e14100c0018425641002e014000049a100a500c1000043c000182004003000c2d0394140c480002119035188425000303603040500f00119850081c060880c6405408242201c01d54907c0f000603a405900071000c100401030000c5243c1460704120000c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 401383992 1250 401382742 401382757
    0x1204080d121b270e04030e0d1212090204051f050d1e111504031a0609010923010e19050c070b090a14031b0f0d080408070b0f01050f03240c 61
    0x19001660f020541842d1841c1d4540300d240a42c03214603140d5542001d12504c0aa0305902414a41c0005100d465081c82680b40c3c042d0010320100110398060300360001821110240c801411400c09003417600c1000308050980c00040c48219081c6048150700e17207400030346016800181d021410003003038490810140c00920046004040c180791541d1004000007800c2c1e6101e40001d4848643c2039010519103a81500010300c1030902500c000030a0340392031042c401808c19540c0c08200c00d80c0c90151306641408a00c2a1070003021040210300c684e0410100c02600c29850402101820b41020200000404280c00700c0b44850f5101c200c006940e43e6291401e070819142800080103d940360740030b1a80c00f0000005004074004a0304038002060a4901c1e00741e45022888944080341c200d2202c0d180318500507aa107590042c09402d80360320340713402603840c41e0740c854007259004070b82c04103600184280d0610110041c000003041e00200704011402ea810f0720980c0c061804070640141c60b1001a41136900c030016244078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 401385242 1250 401383992 401384057
    0xa0b041502040609090b04200c0307060213050f061e031504022a0a020a050613180603030e01030218190504020f040302100c080307030c021204080d121b 67
    0x1100e44544004003004c12600c034071034139103081015900356454680f1640d4501854080f14540080c003021901e803454204484041443c0000c0c0f01d40c0700401c2181c0010130020413200e60301340a807403c0408101c04c000c0110700642c01541c080c460011140400c80303050040e464904111a1681d0f118a815491900820000b6401ca4004190364200903203001c841d400c41002c22040103601450700d6900c55a42c041c05401940c0801007403401c111606001c1c006000705801000c0e03201d07100d40c031810903080a0352808240e4420703580e90907040003416030200809005260074a025458003507201400242c8000750800c080c80ba800c444154008422481c64200040c00081c105540307601d000141503c0383c0d0032920090740140701e41c2861080c401c3c4540301070980507600083c014215154550118000c0c0450104003082d8812621443c00030302882010b00020507202005000b00e4081c000c00a00340f4248444031103403d81803440d405081e4044011034000e000701c501c0c001c03030703003603145e400d0f0038a141c0800c101c0c01c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 401386492 1250 401385242 401385247
    0x503060d02040c020a02180c0901110a0c060206010303080c0906040b1605061e060a030201080f150303030408072003032506020705010501060813050304060c03170f09010e07080a0b041502 82
    0x241031300800d85014050085800c040c120f400c4012080307002000319101c5410a130108411f410315030080709000007940c4124200e940741d202d2a0744080b02000306412002c0503902100c010010103030300c610722550140c41180c020303040038910b00c0480c0450055001e81c921703030640842c03889140e40510740c054209075003000840b001e40c10844540303041600d00c50108801c14400d407001403001c4c1402c0541c1000c4030343c1079592080d0380d81c6030044003803001d1001d09581c42490035124200059034080000c0d45c01035018200301b9940751003d107009502c4108580b8a21040724580503660032503500441030700c802c4411140c1040210071281c1c6100701404c10f5120041c06176201003801d4051040540c1311506031074032a10b682c0c000d500e070704107070040045002e480100b03030f40d000300420b1100e180305c6e0b4002c1d02001d20900740309914668042000d20341c91811a143c0c031400c0d40e48000c000440c00e00340a290200d880e50703c0a0184e041c2005036007034442085900143c01020240d0203d806c2100f00c1b200300d65501040c000454 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 401387742 1250 401386492 401386511
    0xf130501090b010908120703051b2b03090c030b2a130e0103080405062514010b1909050c07050d02071d0c0702010e031c110d020a0506070503060d0204 66
    0x1c020a60b565510340042c1d10100d01250072840081c86461450551040b030381440002c4d9401c07030305d40c8e2000d0203103100003102901501d08030700104800301c8058041c02042c000e44540c0c1603943c171200c441c00c0d0f0280415041c8810313100842c01c8a80c1003425650840c0541e0155507030042c03083c060149038002c692441c0e008066a450054080010307010f410034038125110825910100c203000001c017800040c2050b48200310401c81407030980c00900d02c2c45c00100d650312030402140070700210903150080030b44001c038000c041c1e116218001e201e0103404101c2203802140500c40607407000144941c501504107070310703a20404208608010000c1d1101a540702040302c40b1111508402910b07a9418400c145c1d05400383e22079041c0b50031108d20640e1041c00d2154015087c140c5a17001143d24032542044d13150540910f20708581d07000e52103071075820488404c0e11252050950900380034600240c1403003103000c5410a5017800001840802d001ea0030070b001c0e00d81a40c487e00c4000004803407044440000354010314015001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 401388992 1250 401387742 401387759
    0x180703080310060302030c030c07030c02060f0309010609021c0e07080304060507050601080a020d08090a0506040902091f0507021012061d1609120f060c05031902180f130501 76
    0x652280c0c0009080302803241d983c081c10781c00d03030109540650814109100088000c1c50300c00250084501074a400301c685a07140d00824038941c00003c2c6600c22000010800c04240701c04d001d001c00070000580c3c00c40c0703411040001c82043c00c4c0c071500702c0050a40c40305800824200c0070400d02c0c000d080c503601500c1e03032955201c0b40039003540e10001048816006603000050004c0d4040f40a030102600030303180781c01c1400d03a5900c1000c10703030020390010391050321194040b60700d0312008064006030125000c0140c0e21074003d000c02c00c500061070142c00390306c0080d58040342c00c2640401a19602075042d580c0a416002d0441c00f691050600c0c43d084500c246030400010b030090552151103500861400319981603124544c0341446100a80b0241d030100e01e52203000c10401a0502c1c80002450144013014150b520390f03600e00064414507842000018408024000c90f540001d249684420b0000c0e81149041d00014041800000340341000348543c0d50400180810748440c0f500e00016050034004108568460f5040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 401390242 1250 401388992 401388997
    0x1141b16211e0504151106010b0d0b09060f190909030509010e01051201182304051e06010e06010309121805010306240c0507180f051302010818070308 66
    0xc9000091102c41c09030b6405940d0911060714140e142d45551402d820211030380e01403442644040c0801c4200841103c2c820030a0041da40600300540e5074590320710078070060301c0035500e00c6034084e072150b0504000d000c210799580386850041d0b602034034040040c80119001403120803041e40145100390074072024808140c0c0c00390090002c0b40c000d0b2a044d41200045004607410b001b01c040c1c1c10801800c15005000100d00780c45c0c00741e0a001c0171040400d422a0405410789812002020740b9a00d01d41c80091004000c803c1c0501000c45101030f0045a10b1030045c11171594a00c03040c070440c2c80301000c80022841e564032a81000c294150080c030780c101075110f00c00c80109030300141c400c9807000341e080d10030120b1998443d0089808407121007288450901c0707015170300e8510150b1540300c0028440c5002c5500c0004c0c80a010440092101a0000c500000030f07031140f034199203081c0000c49000d840c010802110403120f0342800c1c2803680a01c0c0c0130549039241c1003c0c036424449500b181c031462041c9d00d000400c10098200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 401391492 1250 401390242 401390303
    0x18050d030e1203040809042d091101080601021005040c0b2106010e0a05120a0218011404330f1811040806131b1701141b16 54
    0x4070b07000c40c040c084100c1c1d014001501c00800305081009a4040380ca86600862902401c1821074200903a0040c0a810f0044c020304600d80c0003511a0103075070500507083c0d0221030300c001c01e00b0819440d240c4400000e451f891404181c505041d5a040850240b01e40c6040c1c02e4081d01c6800c00300c940d501c10b140140364008150f003540340c800c003010f1000208154401c040100d04070b00e0140c4032880035410b10040011982807510141101d00c50700c1e5441025a890f15500c40900e49901c0226000354101815040034501c0b0309041030081d820040b14007207810b0010401d847c03401110484900c051201802c03d8903811082d4801031201545032000300301c800704038807031400c1303d44420020048420125210f041c98040da02c14a5400d030800300000c1c07040a295001d60035540d200300b40380144006c49a400710750503851354100c245e0181002a0300f25090509200c0c5024500010199000500d0002820810100480d42c1c1c0000c803103001c14110032102049a104115039400122003182e554120407002414000740c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 401392742 1250 401391492 401391521
    0x1d071101090c1707140f0315070809060108160b0a1e050c0106060305060a0b03040302120309061501020307050d12020702030601030f020f1c03030218310b01090918050d03 75
    0xc0000f502e06000030100100d4404010301d1604800480c04c00001155040010b5010700600310100600f00b152050301e481219191280303015400e010031954a40041600003180d11f60101d10b050b0304607201c1781e21010450b201da0140c1540c0e00000c40c8221098403507060402d142c4a4045008410150040050800e8541000080203d1682c0c0c0d101242600d200380d40c15030b04072649d403006011000000005650060081c01104c40100c024500020a903000310b8028601e50424014030940cac00c85904240184003091008608040540e2240354403103185088403070601c10980188803118046805441849400405a6005603075a0130440c4204a40040484c800e83e0001ca000340c0303500d0000864032100506001244402845940c00d80081d0300006144680b10001190103042c0ea98019180144012070058490070000103035402441ca641c06071305481e0541462400c032480c0e6401100d074000c0320a80d450104000240e50040e1510051410014006000c0d06401c3d003000ca0301a0003c00e1020f40d9003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 401393992 1250 401392742 401392769
    0x20711060310080c270a15090609060515180f13020c01110703081513060602030a0f0905030a0803060d06021201080f070f0308030a3809011d071101090c 67
    0x10400f15402d00c800138003050911050b5039000c40750008105d980301600d50300000700c2e02d400c4101c04100401941c0240c0308240c40305020300035660749000c0c41c0010b02d402d483c040910385004404410702d02502201074414000c140882c080359a5545110040036000b401c500c511660f80c2c010030b406035003c0d0001480e19030a000c5034041c0c0c001400c0807510000d425980f403610315110101140e441e1019011031a5028200d100920000c051a220740310007803113540c0003075075106803218000d0040c4059040e034205014082034104940d0324042400041680d100306440d540383c0c0d03031b2030001d101c404901d10080d04061000c00e100c003075200140c0303c1a040e144171790100d828a0742122902c540d1040140103e00c4054003890041000500c818040d50304980320080104e11610402c50326104401d003400000e48075020700105035000c1800031030382820582c041c0c0d42c4031119810400c040c011808940700c0d54a081d81440c0016502600ca85200400302040c84020b1004d00e1090901080d00e01060240300c2010160 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 401395242 1250 401393992 401394013
    0x30703090b010b041d0a110d060e10050a0501050a0210050a06030201092903061804030306050a05060c070b07080d0c09030b09010c0f0f0212042312060a02071106031008 74
    0x201e0041d40c4c01c86180d01e01a10031084010012040d5010146c03000000c00c5c0c80ea44099030030310307090340a0300c1e10007415280040e00c545443c0382101d45860203446c82060540c0c00500b841142c507220181d50644000b8240075545405251049140085c82c0b462481c803a4941018400300f0b8449820800459000b45d90300540c0d56224002c070290070807000d16003140d040118040d90b0f0b0501c000030185a000000600d10f020703002d4030f44202c9503100c0d03045404800113640d501e82406140381c0300d00c581c405050705880712402e081324200e0060f40c0d003080b80540c004012002c2550002c009109045800b000900741c0305020080141c00060040e440c64001102c103080442c0000d11040b005115141058000d40d5480808a02d1241c0540c0c28681e0f5015010440c00f684131244c25070324050005200a10265110708400862081c040200458400c44107204041c0014a52084040002c03203541006440d20f0060751030b10940b0708038a11030800340d82e072501b20001004020407007007103820000481d28641d0548421098 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 401396492 1250 401395242 401395259
    0x1b0307110907020d08040c090203250314040f060e03040806090105060d021c0813240e0612150405010305030a09060207181104330305070e12010908030703090b01 71
    0x1044030a0b0006038040c1410002443c403443c0610f41150150007a1112140c5803150313a41640d104440c3c1031a8400c0100407041191800c1d04441040d104038034041189803144950301c0d100c680d02070801342c00ca81d9901000d03020f00010340c2c000080441c0040480e0381c2d89949691442d2600d004865a503995443c2000098103400d05081e011002a0300810004401c2013040c0340c0040010a50410354241c40240300b14010345940c0d01c5110b000d0600b11700c0c04c51034080f10050380c5107843c0c01c1d0881d40301048000140044144c840c2d905030390640081044608842c1c0c1c0e1020500e0038280301a4100d0340c054140ba00005c00e00c20048002d00611109a50700c4c9005a1075400aaa41d640c2d9803007444503110150b52020413070349035640145040741070070300145c1c50f280d034500070083c8800c190804910100071000b030074134100014811451030203005040c1404140341c12000540141c01c4504d080b4007484040405402c004400c0d4000d22500d039124400940701d040442e0010001d01a42a080f00d0311140c1c1c0001084006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 401397742 1250 401396492 401396509
    0x5030a0b04032d081b0315190e010b0307020f0109030f081b0f1303060e060106020f0609100b0d0c06030509010e01060305030d0b01110307030c1e03231b030711 70
    0x220001604031000a00c0c3e00071201848002d00c49040035441c1c2a119002c000048001d60003515808142d40c009000d080030403d401190b180c03100c100440540041000000e2460b400c0e04445803401000c2d22030303440d018241c0c03c00c120304101038081d500c5d10b41d164041507003100e120f0340c0045155a07102c0b1607507603c1c502d1900200c0c03c54030145810500740040a002112040109005081021b00c440c11a549a441c2c074107540c141c00b04002c954120f031006100b1980d04000d00148440c02c1c0000b030541c0d04000c242030f034855210000b081807183d100c05220301241c80d404044810703d40c1c80007500c0e040d81c1c2c0d2032030010020142525a14000c0d42404441030010a05000d0101a0f9410401552030071400081a100034408465028188085504420141402440076001d014040d481d804030150083ca80703001011980c61103040d0741c84080310b8000220350700070020030130604940e0551b03203000c01c06510b00d80c02e8080c02d1062094124020f200182058021024218083c8904c3c00144041c64000c00c102548 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 401398992 1250 401397742 401397797
    0x110f071a09090604150315092f091312020c01030b0d08121f1205060a050c0706051b070311060c0f030a050a020d0c030c0906050405010207090f0605030a0b0403 70
    0x41040d82c04100c16141560002607440c101c00f0000007016581e96034040050b205919002145a545254000740024858606010903010550042c07448409000c0090310030f090175501d00440c514000985031440c0c01840705006a040440001c4203c2c54883c0256288046104240001d081c01614826070800806103402c581c0e00c040b0f80750a29202d40810703003c0101c010441c48032840080240010700b070340390f0403503405843d1030300790710000301c0781818100c3c5040070180020111918142c10003201c00500700540b00e0740741c6e1009002c5901e4403410321051111908e064890040c4d14001100300070127401214000b10021001d0642e2003c0d0364100d401072aa0003152400ca4208008000103130310000b06500481d40a6500c0d0401030800c2408400340084500607038001c03002c83e5039030a181c3c072031640060384100100043e1610502e09402c10700000c0d15840e17a031103505180c51f200d01000c4200030f42c070b80040001d00f80190455440c0318080c09d00042c2d102d4213407001d40110f40030b80c1c00b0600014035042c2d5010300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 401400242 1250 401398992 401398999
    0x7060e045f040203070e040c0911070309050108060f1f12020a08040201110f01051e060a030510021633050601020327090c091206040f060903110f071a09 67
    0x114120103007510350310403008000b00d903d0b004519020521040f001c0925020b0703409280e440b1883c0d418850414112120180c602e080302c6030138024800083d0740024103d0940f9030a181c040070030b44a45d80824000c4850844550740131358030300802141811003a00c4455400411f90790f07000504078a42002040344501041000000c03030b440000307000340d4020396010901e03501907802c031035540181c9880182186c00a1b02c2041c420003603800c0102d50425815951034101d002116485c1c0010b185a44503599080d06c091038503115500440c07071000a4840050b42c1c200503070040c03054070148400884a0030307a00c0c0448010a484802c004194550103110b12441e44507440603002545071211151107544829107903602d07c030b01070311504410b40c055182d011602e801601103502c801d4a580081c2c0811880d405640c00541c0e07590700481c1004045000001c1c40030180303400c08000540c094590400312000b02806c40320628a01c01d0302d03100f06800e00c0004008040395011142d00704a03c03041c00100b074541c841e40340c0080c0d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 401401492 1250 401400242 401400401
    0x1e050c030a0b0402250302030f04060507140303270a0203011b0816090501050708042303010f02120a0e070509040308010603110a05031801020d0e15010504090507060e04 74
    0x104840840210300785d806401104d08040c00100050300c1540301c0c0d00668002100850080308024501070144080d0503828043e504601e048464031445c82d00000c49860691616560151074900511058883c103030090001d00402c1c007003030420100580d41201c108000303601c2c02c1c00502d02d0075000c1c2c00320079042d100d540c600000900d4807004403500d03002a4400c0c0c900032420400080da00440d44102a013242030036032404c00b0200d04500701401c441a03884c04014035070040150704044100c150900342d0246412070001b4100c8001c4140030702d0710020f038025a0b0800e015005000034960804142d504035046550240b00400f9816400b0140c0e0060b003807060040392003070001ca001d00c6c0400994414041d0040300050a05515a5440d41aa0751007000c18950760481400140013940b14030358913000d03100580e0f0502c0625041d43d1440c0c2d40f03150030322a200800c5004a03d05130941d0b100e810a070303c058154241141800c407880300c403070b0648807440040003e001d920b44a0340b410042d8071076603600c40424884c5c00359 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 401402742 1250 401401492 401401537
    0xa08010c0f0e041d0a03090611030a110708030f030a0e2a010c0b070f1205060d03110307021f030c0e090703090203150f07021209060a031e050c030a0b0402 68
    0x44074260203155071a4040c2d04c0e20000025651031001e00640b40d501c3c1002045640401c1c1000b61911840d5080344042021b02d00381c0004d40da40c000f08440f1025000c2ca17103030984441b5502101c3c1008120b400140b00c6001c0040c40c0121248113201860068103201010000000701c0003100b5070307890018070070b0040c205500700500a140e1200d00c0d280d4000f0010b04101d480e002c0c46a803800f600d900704a0300d68011401d40090f10800c998451036915000000540400240c00c2c00c000049242d0707081d0400604102d0342c0315025004040600945001daa4040c00310400701c070281d001c541c480d1982c16071100010b031030300840c007040610552201445001c0a031410503582c903080c01c200e010b008200400da03054880c030305602803a0301c10130007068400c0500d0f0b00d03441c03051304003500e00a0519581040e08043e2080901940c207503650391034200c55004900c1c2c1030000d103940e140c0c3c42459101002000e0040014900070401100092541c011442500e01d988108840103a40d000c00080780110010305142e80c0d5a80001c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 401403992 1250 401402742 401402747
    0x1c020c0d09060f030b040912050c0d0c0b040f15110910080621070e09160b2107140d0917340b0114030d03050412030504060204230a08010c0f 62
    0x1021700d1200035001003051045d036110f500c01100040799200c00500c0000d84014844010300030900e402c8024640700000c000252580591a00c001e000134101900c00130b01700c002c0111681070090b44000d2410305008410000b0000511074028001460184090005906002c0e10848060f48190001071101000c0e91020945c200e10820081c4688000d00c903440b0040744100048000038410140c0030f0003031558003108402240307481c209601500810b0014802c51070305468520740c0050755001100c4003803403561601011529899031005202c5a1400005c0d1180c1c00390b07480d0000a402c0d4050443d1203840b859409000010388500302030014030039091079800708180e40105003006003000440c02c9182c01121522002c8002d139007a440200c010039401039a02c08e0f8141030005020280540c10108020315054446207046e80f40783c6410f81c105030351100000c0801482c2c0d410703034003d040c3e0078480a040c10b0440c0c2c80350343c001c07155807400741c40364224641c0068403c0701409200301c2d070006175656451051190105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 401405242 1250 401403992 401404001
    0x220303020c0106030606090e07060f110c18041109060a030605091212010824042a0801020405040f020f040501050a0e130c08090105061c06021c020c0d09060f03 70
    0x1101055020001540007040074040c1501031030090900080185c0303040c0d203d03011100caa41b030100c50790f0400c29042010301c0e00a0480410709817241840104507103145005420048441d4111781c0c05603003030490403203292803501000e02c642d01c5440c42207202c0c0844010844400001c41ea007950000320310800b440090826044160881c2c920021034041138400e10000b991504240c2036146140441c42c01000140d00c02c01060b40c00c011102e00c071803080c81d640f40b01c541142000034400703400d01040c58806004100300030000e000791b000c44122640301035110b0744c007540070350300521404c4e108604040902054450750b01c00c0f6041080d0f4481003610b0189000019226078000811040601c035290b1101301d8143c480b0300390041c0d144c1c4802000a08003a1220018154100181240c40e41d0f80c501420031000740c540c151003409941c05040c0c40d8000104510f4000702034031944240031944c05008000b015070041d00c2d0060003040f100141034030310b200c7c18180201d804945a11606002800900c82c0d4840103000390320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 401406492 1250 401405242 401405311
    0x216050d030e10020f06010e040215090d060509070521030301060f050d02040e0103060c0513090b03030705030d0b030c0102030f0a0509041b09030303270b060a120507050a0e 76
    0x2031003000c041c0c680b000070340d10302c80381d58210303002d6040800210039141c0d050140d5030140610007440070715420113402090440c19005611000a400046c10105690350140780d0491140d021405100c2d031b107455008142c5910f8107201d40303030040307001019803611030b9110b80240d0f040701d00e518019415a86048411a21310f84215100c400307010042190b55081c0900380020006091781081412484d45146414011600340070001400c001c01030005004409003620300d03200719231440b80007140c2c0400450001e41180b15418009000384400a01080710740f009402c40006070b00100c0a8034130009681005a0b22272080103078400c01c8103820024034000c603019201411084030003401c0000e2074899083c003a201e41d070010085501050030f5003020410194540640c81800b080c0b0841c00c902016842c90f074000305204250b00a01280b05070000504076100c10181c0da004000010b0303204160300310780c1801c1d901e8103c03500465015812102c8081035005c1010080c2e8041c01c054800e2900203400d00b071407045980c50b80a0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 401407742 1250 401406492 401406497
    0x2010b0d110f0d0302030307090b0403030e040f180606030b0601020604020916050f03040317061e0103050a0b060f3112020a0902040602030a020c04050f0c03040c0b07110f010216050d03 81
    0x10002d2015100e0004811400c0c2c4240c0003141c1d2403c04000c003410311540c1e584401d6581d182000140f001075800050781106440586012403460240d0070120040c100240340d40c0862405403c0741c005020306500b0130030450b4003805490b2038946801c8012a03c03048111800b0390000c0c408001f09442c03580c0711a25031038143d840d103010340c00c0c185031801080f8594010741e07041c3c000400856031416003201902c0d5054200f201141c00003404070706440008240c60210915505055440c4c0000d0a12807443d00b18904000000740419030320740542803094003582103141100e10340301260415000400c18096032101910b000d40310000d50b01e1915409207020030300c00c44120713001040c0c00c40c0040c01ca240d0b80003400180c289a00036545900c2001c000071b151a0b1046d4001d845181441d083c42100c1b001d5140c081d0300420040013030b640e0780c0d69900700a40c0c001071950000900c40d00008444050181c3ca207219000c02070f0031520f4502d80e1401034012a5203081d02802400c00c00e8520380100014540042104010362003030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 401408992 1250 401407742 401407759
    0xe15040b04030314040b010e070810140a03290114060409091506060807020c030604110103090206070804090f05090d0f05030a0608010e03030f0115091a0913091202010b0d11 76
    0x20130159101a0b01601c080380c184001c1d1006020100019071110381c060034619003060380345000580285140050302c40c12031075802480c20500141c0300d00c001407001c0c54000d95030301400240da201520a42c0001c82d10440c208482c02d00210319015624103804110500600e110b0030700d41819820b81c01040d0440d800c0384da01c1901c0703e068079200545d024481c01401541c9030229680b43c0401c001c0d040c4081c0301125442030f0004401c01c800154404009042440c081c038000400003024800f242c1b1034410144003510000740800e001540d9112500001801d4154203400d10031500c406030341c140d855190a0445000c0780f803170301150162a00ca200556841240d544022664603500ca03007260860b2100d15800742150400420058650803403040a8014650780508140c41c8088900c02000e01d246800f4640c0440c6480780c05511003500308042e11240e04c00100500c00c515a0903032503600814000200301c0e03e0700c4030202c4401d8140d00600c00c0600018001d049285100e406075030f058140c03004981000c3d4040d514 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 401410242 1250 401408992 401409011
    0xb010c0209151507020307090515060316020c12060f07092310020705090114040914010f14060303160507030519030e09040206040902030405070512030a030e15040b040303 75
    0xd88003003502489812840c40103661074507007400300500c1505503d03a0102c60401141d001030b02d0014101d0300311854a600010303181c0740d030703441507110011004207a0350007100841030064021007545412030b4200c081d001c84054180c2041408071010600594030070304d4000c400000e00741039a84c9080c0d50700034450b240c81c1c40c00984950f205142000c139000c3d5001c0d150740d140005c1c0f0090a00708920340354840540018850300b807034040040c039521070501030a003c10a16002c803c0307451b10340740c0228138101d81c0001d00c43c480030042c402890082030300000c000300c1a400d220550600e130001780c4880d40a810090060351034248400b0145aa00241d000e0884051040d50400030118005100d01ca800741c1140c8041130008002c5e0800402c0b001c65104100d21980341c2e4003c2c040103903502c0e411035080714800400580c81ea680e0b41455420b00d05035501c8150483d811812086580c48088014000c9440039102000303900c0200e92056907900c2c15249100070321700001c0210340030807441c04800d42e000f482840c011400000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 401411492 1250 401410242 401410249
    0x6010b121504150617040f201f0f030e031e04150302031008060c0a03110d0510090f1a12030f070305090a120b040201052505031305030d0905040b010c02 67
    0x3d070406103500c84005001e00c62164086502c1091591301d0340030a0281c1040d45400d0035500c582c0c08001c0445140b0500701c202490704401d15018618010211061303e15007000d0010a65480c0320703a034000820300c000b11031403180a88140010702400000a50420030b0341c0c1414400b80e03040b15100190003006000015114010102c40c3c0b518103010781e0056100e041c00ca44071450442d260b0800400d90700301d2010000160800303025108510001d1802107066504110391145a00ca6960000c4600307003054100b0101800d6142280100c401c042c07010441400e1010400d0200c615410f1201c8503504001c0104c903592800340601d01880040380d081d00e04e44500600e5800c1aa801020704801280303022900c414286000c41001c40101041a10548414101d03a81c06003494801000203050100c007044580380044180340202c80c40c1c511190a0007444a2410055900d0304440c2c80c00c1914500c462010810741408101900310407125100c6030040390034901044082c107044003d0904005401000c800036a4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 401412742 1250 401411492 401411501
    0x50109060605041d0a080a0338030307050a110105040e0a06151d010309080d021602040b0f15030a0209090c070302060108010b0a0b16050a050706090806010b121504 72
    0x14810000000c010340340a00b0711054803940c200c085138141c0168000d10a01002013090343c0d00c2c1c2e5114407080c3d40c840c0545800d40007411642e03c0d41c0d0032000c100100c0c0000c440d01442d9041819009403900d10110825020903aa030f21031703a0742c02000b0b07400c400304503000100c212030340c44c01c200014182230781000e44407051640c00d02e07402ca804809d4141c1f2080b04001d1114010600040301c0340d01c4c50003d500d014800034148101040101c41410150380b10000800d001080f0140ca01001c45460195610f10b06920000c0b0103c01d00d04080e84a035145c07402011503071814070140264018090301c01e60304440d01a01c2081320b6000140410702441e000c01583c1c001e03607581680913229007006544103444011505009151200c160440c141c568540002c4403443d985c1c4585170b5049070100c9100c290b40345e031628403a00b01180c40181c0101680b044810305c50401001154507030a4514030354a02e44010f50781d040e1300d50348003002e1081c014080010000c3c030001c1c01414401c10f52180f9444501341c03000c20140040380032103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 401413992 1250 401412742 401412761
    0x1080a230604200108010311130605060301090b040e1c121b050c01050708010b160204060b030408120f0402060708090f1207090612021305072d080703090b0103030305060a030501 78
    0x400055000340000c222000c01e220f800d02d420300e45070140e90b0641d039800b180c6500c01400303e8850810032440e20074030f031581c1d007012016143c0a06140c0d129607440c1c2c00a0080c19983c1c444078400e40c28a04020070201000a10080c00201c080c4d031008040c510040550341e5005100407151240d17100e510064034440814848000c03590aa41c40542d03800384684200e0840e907010300942d0411600a0040020803828429100c0354154280340000040e8a40b00050060401d5405115603610102c1000103208183c8041d1070b80403100c48010021340e0300e481050030805c2040324002d610407024404a00403e00c0c48004d40440c1070080e05140d1072a0350880003030341d440c1c10700c140f03038103241e0000001780032030055800b030440100401190300b52203100c654001610005008920176084d60b071070300003400183c0306401c400d58411415214071810a2580c0e200c015a2208642d0003001c03c101402141c0e0a03071092140368201508055034540d9642035070340441c00303040042c0005900c0140b80c0305c0400031400a01c20608503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 401415242 1250 401413992 401414003
    0x4050d0f14060411100801060813051507030e210918090f0706030e060604020d0227010206060d0f020d0204020d020d1a090717060a1212120501080a230604 68
    0xb40d10700741c80d002c2c0181c48620242401202ea011401d000c0642220455042d900c0509014505c0d07074400c4290700440b0405880030f4164030a0201e5401074040d0f03188500d002e00c540363b07414000071100d803490359500c900e2494041088050b0501500c400000c04d0090615000000c2040f40c004181c40c1c69482501010b03290088150004440701391102803c0150200400341c500302800a4002040500d4071088010304980c0a2900000c2640200d010f030390407a51015955400880d1060161040d0450b003d100e0880502610904010a5051905040c000b02c4294001d2810401c11100d17404e006210154000882c0c01540911140021114a0004d0034003500c1500c0009000d484c080c092094400114901342e000c3c402c914284000140e06c00b0f10318900e1041900100c0e4a40c4407900800d983c44a664442420400e0706560401001482c032010045d41c0780e1951120758180384643c0caa4201d038402c6c490843c090b40080f0312800050600c05029486c03049120a40390041e19034080b031820f005007200d00b20760 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 401416492 1250 401415242 401415253
    0xc06030a021c0b030703020402090a050d0807030f14030a09030c1e02040f090201020606122107051501180f060b030f0402011403060307090509031b0c03010f02070804050d0f14 77
    0xc00003202e41d104100c810b00c04818010103040f0000b2a40315100d03404081d004680000c0d51210f80c0d207681100078014040a80010000401814651900e400400c01240001c0a42c0301c400a00c51041810183c0c043c4181942c030720f503403107203c0c00c4401005c03924070450600c480d00701d00001040f554034428075112a840700c00310303040c10544108400c5480c005143c2044500e00361780240582d1b40020440d502803c00d950030032110018101c06450b00b451b0444481d060703c4500b036100440001d210107001c401c3d100c1e004450f80032081c044880c4601e4024000e000c0da4100011480e006005560050075000505060015403e074594007107114541c81116440d034a10340325400e20046592007805200c04501c040d141740d0660510200080d1038114a12803c0d00c81b50303c8901040c4403140500458480d001d0302069400c0006042c070816844030070300000ca5200c4e51078a264000400094001c86030360681c00304006242c075040001b003013001400000c080c2d0f108041c4010140015507104020102900208000d04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 401417742 1250 401416492 401416507
    0xe011a01020f061501230708090901050f33030103050d1403010303170c041211011803051213030203070e19020c06071d041d0601050d05030d09050c06030a02 69
    0x2490092000040c2c89160300480400c50340461025443c4003511007441c0803039907040c030700102d4054540354003405002c5d00000107000e800c008100300200091078080d144110b180c1e0b80e41c010014031107800a90560083d0900e40420048420b0441d1011030100003c2e003108082445141c01360160030036001268a980140302c00400c0a0300401e003442004da014003030524642c110365004240d107a650106903920508000071400c00300a2409072409444c581c40c51040044850a0480302010540c0b00240072031100a003000d03040c88262040000c4e240c02000410920052016441c2c995000c8910340c0c0541d448100044010390b0203000703940003000048038400060401c0b05012000c69822004040c82e2407041007030288049003c940198031451500702030035480710819442d03803010b1500d0415584107240264a03070300b04000d0348004000d00c0d000c2e81280c0003030380c03a002030107030301242c002d8040c056038424026a10349a0445c0c22010b01140700d00140c80115000c100410b256420035036034084869000304e4500c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 401418992 1250 401417742 401417747
    0x203090a0801110403030c03030b04020f030f0a0c0516050a020d03050408010e03160803090a0b2a0a17070c1b05120c09060f040b1207080607090302030c010804060e011a01 75
    0x1814502000300b100c1e0f51128260b403030700d100b2880002c1c2404070700d01c602d0081c580651700290072070f01e0180c02075698030b00080c040fa5041d40b044811399207204103140403071402841072041800000c2c141d240c542ca00180c0d00205c4800310002b0004880754450700c00c9100050312980020f501c0307144242c69542e101e43c00c18116909680030654100401d42c03041c401c0259580044285007070107904060039a0303032515041c000170304021000c80042d080300c1d5200b041c40025280a034102c409004040c40700c0100070340d00c1d0000b00d44d40c410307241000b0005541c042d5443c1240c0e01020011742001140c00d100091000559135040700311486034041d184001d95210407c00d5040481c956042c13002000080c00e140d008020004a0220001d06098010803403114502c02907206c03980680084400145080340b10203010024642e581d249004074404d41c015200860030302809080f0342c0c0d099943c014094010091000c0045400520082060f120580ca800303e00c980280c0030f205555031781c1e040f107842c10ba1003a60400007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 401420242 1250 401418992 401419009
    0x506120712150608041416060e0132070609031706010f17150a0f05030c01080c07030c0204020909040c0f0f03150504060e1203010918020d030f051306020309 69
    0x80a00060404203040d10b101c8507209260140c0e01c203410500c0c899100c0d403c168107108210155a2007901c241c000f000c1190748140d45040c2203d515a8401c10406544c4004480b61056001a110040c0310004900070804a03c00e504804025090401b8140031550b200d560544041c103100b81d020603070b80343c49016a060380700400f82d4460000e0a1203261401d04030001003500e2103034114249503000c0359000c2003502c104140064180d500081600c4000d0313840f10030141c2e14607803520406109220b10210b80d54154001c01000e44110f2202d0840c90800c1065102604c02075803400b01241d21643c2008044899030759003407141d0041c0e015078400c1821030f0a05081462505041d0004489840c92100400001d100104012a2625456000f14040d182c51408501070314402101c18950b00074012026082005000598126146000144084c6103070b400020400444840042e401013030407a022400310780680041444043c0c0c51810790701c0d0040c03180000d0340000c800d41203030005803c0001d0040f41e03131901100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 401421492 1250 401420242 401420267
    0x30a03091b0605121b040b03010f1a0f0a0e12010506090105120a061104030c230a051309030c0503040602030403050f0f0c0d151e0f0e061f05061207 65
    0x2007001546080c4040501940140001d83c0e01e0410f2400001d107030300c20103c4012407011500c11505440e641c4440c0030091640090080c14208541208001240c00200f003c800030000c8000c0d85500e00315405064421980c401c0d444842403007120692030ba078a4403000e0107480419400c0c00002030908150b01000302c0d0310720690015200d00c5212100001000000c02d0183e8451b9100714002001e1014801d114036070b000710303800a0003064071140001240588449001b40703c00721352101c42030041ca4001040040070b00c07800303800d03001a69107035102003440d81503101c40c4039180281071943c2c0894456031030510307541c81a0042c07401a00041800c1080140411003003601c3c50420000d4800c030300345524010742d102c0344c035541d5901c503500c3d05c0c0e909000c3c03000ca8000d81d490109444018801080c01c09004000280c8030001500800d00e810010f80d02d14455200303150190401801130310482d21000c119401c280035204201d2200404200c0c00281941d561009014820b000d00b5226081d07c1c14803400740540b800444d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 401422742 1250 401421492 401421533
    0x209010807021b220e070501090b0430020409081c020c030a08070c06050f011502030307140f090d152301031212150f08010c050301030f03020f030a0309 67
    0x103c0d880c6285032000034490040181c0b08002603007079500c54103034000308980b20246540d18003084550341e150042214804d4500070307281c980380259a00300e8104103203d684501e201800c110080d08603480038134095242001c05540c2e40700401500c54002604454a4040494101800145035100098981c0b4134800144111908500304a802d05045841e4800d40c0008010060f0100004550500070405544100c4d0424020030252510001e03881280c07a01303024a6248040c04000d95560901c000101c911076029030707440d480f03412490396034480e05800c00d50b111045103e003442403003000c0d101e1070503407407820740140403a0054602c4d00d003490b0115038003403210003504a071917808040b68007580340301141100e40c0500c400b40c504102c000221035031003a201008a0703040c208070004070082580c00b040002d5620313098588941c0c6564458040c202e5194140c0b20000c20340900c01000403804100c5c846281c2e5000b401964070350180c0110260965112180c12030101ea600d03000c2c4000c0c44141c10840e1498203400c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 401423992 1250 401422742 401422753
    0x221100b1207050d0812090a050606041e0c05040527011e120609020603150102060c0c0706080402030a080a0c030e010201020304030e120f060a09060e060c040e150a09020901080702 79
    0x84a14a440c1c0c41d2501480d40140300f00440113003002152000c440c8000305c41407120080c0d0400c48056929041440300c2995544502004200c052400384120f14011004202c40fa80c02c003a0441200094106614810306100080c000041d464807000c03c030003401107164503440300c512030004c0d6000d002d41041e00202401c0e0030100040507401c800d240305106442742581d188000384958908800a4141080300a40008022041c800410042455607103202030980079a1026503a0b0340490b00240901600f003d00d56029200400c03407039009806c03154009001409858141c4850340305c2e01000d42c031541d95100010310410402050580c0842c0e01c0404c07480902c003c1d07141d818961001050307080c03404107240c4950f544000c54011040c0410259109141c03010a0b10014600000040014a000319050b40c5c0c0c9414081560344c0d06901090944c450004400b5140c1001d04100f40030b030360420014070070003001d001c44185002a50750a04503030300a0041e102d0150740d804080000500450019045c0419580030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 401425242 1250 401423992 401424019
    0x160e011707181e050114040b03072102040c080f100e0c03070c02130b0f030a020a0b090a08060405100f05072a021c050f07140603040221100b 62
    0x1040a03400c40d1040c203a000d052602c0240303900c0041148180464810598000b0301e00783c103010740c008038100c41141440740480c82c2c140307090100f070700c0030f00d100a54103411282c41888200d10844490700e03026030810380307100240c9042d40840c017101c1d500d000c0320010071414020008628014500681c0c0840e4180d5214030461400c1d41084134004060400c9540e0140400058400e911591070546100c1d0002c2c410a040d0b50104000c400400d4018412800398ad4103c1c0308200504002070140c42d501c6e8040c0207400344924042a185e110740188130302070751003000103100250302d402c03c000b028013690203480644034841d108a5088100c0e04d0f50984000b2240c108030400c004980c00c502251401c03000129150a180c9840b48070021710990340c01e000354011500c00000d55050300ba4014800910700c00c604070741d10a0f40005a181e0b598049108020702006091151a51820501c000c0e40d0411720107403101100c4039104c1042607164005600e00c0d14207078404000301d050150305008000f40c0c0c400030b03280710200600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 401426492 1250 401425242 401425289
    0x2042601110a020c0d080d150504050705160b0a140907081b010c0b0a0e01060e011a040e040305070812071d0f01020a0b1905041406010b0a08060f030708160e01 70
    0x420401d014170407108042010240440c00040364050510b06001300400c2d554603c060415190368001c0b28019482d00c000601d01500410846584a0610004410000d800d41e212910301a00810454150f51280c1440c030f240e03161801d0076800b411004020340021790a01c03071552718044190381c40441c4c54042d4841600d1a036009480c8070310f4070340c20810401e00e0780d9a0800c0140a444104240510340d071809100041034901642d61606884d00005000c004400f00d01d560909401140620201400340c0340114000034011001442542d114403400390070001d40201051494400322000c0d40800c4551034036090100703860049440036241104c3c0c112110040c140002e6039001404d1004125803001d40c04034488000c11b003000c100c00b001c08c1c01c0034082071030a464540401840701c411001240b190030300109a503454001a00d041300010350f1161481e40c1c403a07040000500c181c0c28500c1e09405014000f0070089800e102d04165480c8407040030040c00c0c80d0100c49a012030050340a0f400610000302100d00108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 401427742 1250 401426492 401426503
    0x120a050f04020103050615040f060e06030702030a11070306020f12060411030a0f1404050d0807030b03060720160f2c041403040e0a06060804050c1302042601110a02 72
    0x250203284c000f80d55514003000c0b841d04040002c000c070b1500e0021400240400e00151500c4c1074450503a901c0107290400310600116020035600300001d078009100f5030b06241e12402400004807117540442d43d100380d032600e410049074481e00c500f1400d0b210009801501600c0140c045410100036202000b039604c000c04c02c100ea900001d41200007450300c2d40780211000820b504108003074081483d02c9001403c0518000e030392985a8544c80d004100403400043c12140a132003007502c0440083d000e41415560312404980308014400100c841c141c40c1c0c1e20644c0040c0c0c0130000b40350880841381510342c003076003407240310b415141041e030180e0220a070038076010700f83c090550304242040c00f908a6850150300c81d860f00041c4c0c903001100340c0b040392102140005011160160b079a0183d41d01c4202000701c1074a0b003070100c45e004011180604281c0c49091080302509040244004c6200c0740d4000500706502c940c040091545a4800d94040341d02070b03c0c85a01c11f08080c4140340607000307101c814500d00208050081d4640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 401428992 1250 401427742 401427751
    0x20c0a0b030705120a050402010f0804052806020a12110f0414030106080d03050f130b072003070302030c060a060f030b0c04030213050702010605151210090e03120a050f 74
    0x186004004a034480d030240041e00c0c6212030f00d11041880380781544034170005180449059000550300e480c41d01d00c00d40501059030282da04400541500e06a40246041c0044c03100510030030f607450048440c0104603d44040c00e440481941e0f41400004e0140591003a206d8001c003000c0d2188080010010480c1040101c41c04c50700301c0c0c0e00c0341d0030034280440068010b00701c3da80444002e000780e580440d083d070341c0742c0d011912901039074044810a4686090801c02040c000d20010704900c60a0f020654203070044031003602810101d05154a10602c0d01c080724215000030703804038050303800803407910040300f424040183d01070154101044000d140100700ca00e050a248406030007002d40401140d030406105c0301300c501550300900302d01c114024980400001307090481c5c044006505c0d0200100f8189442c034400c42d1065040c04101c4c0c10881e8000c94000b041c04045e2a0703c1090516400002d40c1ea030b100c0c010419014014809142c58030314101c6445003c80b0002c0201c1c001514210400c106031003c9042035810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 401430242 1250 401428992 401429009
    0x51509090c040e0c0901030f0b09010b010e0d0501061a122202060a0311042705070f03020a110f16120c0b0a0203070b0f06031b0a1202060d0e011a01020c0a 68
    0x300f284114140b4140b41c40707908040d0308201d40038004000d01903030150404079588241804080d0355109800b6030300701c40032800c0a45c0080c61580f00364050789030100240c594280074200025025036a4090f40030154011000300c450150089141c40f02140f0b40044654412628180460089072941800b402c00020395402440b0300c00100722a8404ea00c01d80c041c40c0031801c990b28140d5103036120702001c0c014200f03a990200ba188071410001860414900841d806404240c444008002c0100f40540294005510030010403040f03203003404984504001840d6400c4404001c0e1840036a0740c8504c00c811031094001210307440000c48140c000400280c4c1602c1240c1c60500291b4580342c0b0300000b00c3c110f00c50240c1c06000d407051101442050300211900c0340c000c050803400c0351001440700c800c0880410030f07400210b900008413102004a520242850072a8608c024400c901c0c0045c003840c03100c1103c410110103840c2e6995890014841e41110100b189451424001400b4442c1040002908002c00d401050385 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 401431492 1250 401430242 401430251
    0x105030c120c09120a0b0415181a1006050306040f1e0e210d0b010c021201020304020405150303071b15030b03070501050c03070b1b030901051509090c04 67
    0x540c88a0310645a0304038140140710814245400785811907000720310050721400045210b843c40d41030000d040308030b0940c0014540c040f944c65455031300d01d60b0120780c2d80c2020103450340203126519104080c0091510312505980d8030000d0050550143c01c03000418440d44c2002049051080c03940000940c0d41c0f2020407113000c62142d4090340c000e80030300008d1100790300101d50f41c0c2001006214603001001c00d26070200444204c1080078016100000c409030f03210503055001c0101120440d002d400080b00d028060614403000c040c0395000c030740402201d5200400a95001c814042186018000c4a400c41041410800d0004444000070b85a22074060010480040b03101400c0f030300c041c981050303401084100502409060b003e080039014000511909101e03000300c8201282d42e601407819030380780d40043c400a500700505655052048000903108030b0345804d94401c010300a01e070341001544209150f20010072982084a80d21182c040b42441541c8503465107801c100302c8103000541c0500c6401c0807100444c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 401432742 1250 401431492 401431501
    0x103110a0e0405031b032706130f14040b0603070f1106070201060306200406080a06030209010f15030b0102191115030601120603111e0301140106021b0a05010503 71
    0xa42158155005031a101ca201e400c000038014040060300d20301c0c0c2510303079412686115888068503881740d0440420340030107040c406e84282007018020064000d0180c10300780b07401c180b0990821511071940c0400c5400e001400b050000d14110b0140d008403401c02c0e20b05008021842001400c0390200504500401014400c8100d4140c4200d5200481780c0800080d03030030904000d24000c6c0a032200f404159045820140035540e040c6201580c0144020000000d905050a210302201e190b1405460302050a444400100c0540d965645807030007400c400300c3c1c2005080c9000e64145000007180c0742070013031601d081800c80c22640c010509511030079518000001404091a02912200d0300d04800c5030042c0c0200d008110340c01030b0318000d40c042c0a00f600d82c400140700c0c075514541540e2443c0002040510900011346881c00c14400e4410f000001d0003000181c4407000c00070a003150011036200159001d102d00400c03001d9014800c54003c0700c00d041410031030710001340105003640c0341d0748034880c10041c0000019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 401433992 1250 401432742 401432749
    0x5130c0c080702180708090f1203040f030207240e09240a0801021c181a07030216030c0c1d0105060306031e010608120403110d0201260a23010311 64
    0x1040d490341d03130006006190501c40b800070201c038411100c0130040c1c407800c20400b00300744000810540d080720311458a8034540c0d4941c6c42c1c4000c83c20f004411000e521030301341c0104400301c0d0f001907003045d10301c50641041c03140940e2200500da06028100107025851900074049800c0702c0e003041c1444044041a941821424100801c8072400c007940400841e51011030040b503181182d6409a4980344081d00c01e10207001140d510020030988540b00421b15a44200019100744111110582c00300304d604006041041545440b11030f03081005007100000c11412500781086082ca10b00000303003140320307101207840f07880c141402003e07031060084074030400c0c020001500a5074108410743c001d403101564145c0300d1032100c0459010b80445d01400c040c03030058400441c014440d010565003105e410001111081c11132409012107807400c0d1806034108004d9081d45107000c201c8000116004100740711f201d903985044500081240e40c4510207a1010614000d030102d02c90304400114103483d0000007006e02daa1008000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 401435242 1250 401433992 401434009
    0x903030d091104060e04060c09060f0c050a0206040803070302070e190515120703140a08070210090302100f021002070305220e070509030c0102010b03071a0c010204090605130c0c080702 81
    0x3150f5010342864000304000d100c0c50000e602443c46800240b041e03a4000c0d0055070301001c6030080310000b074405a1224030151003107100d04042030140c822741c0c22158083e000300f401c640c020b8000e50401d60001a211081560420406000b00074801440031a802c000000a11880107809503d00d034544400201e40d50214041070b0a03900c1034018090201c0c503001c0d00049403a80800d10099691081c1e88003240d010740c1001c83c0c1d0614840c2e0040c10300e4a8070810340e00304038420000300b00c80e4003008504500800181c0703801813014203105064a07410034000003004000e14200c010300b40c809000380144035140000742c20405841c00c0005007005c2010404480060351800760035079000851061041051207282c81e042070041003d004190b00343c580d10712110b801a803d0b0740c2c400c0d41058055002100030400e1503e00ca4055003c0c150111410f881c100124041c1402d90300309410550010340e440c1070821a51030003100c0018044400300f414001c070082144090700354a0441c0c005804588001102c10840d42d84455 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 401436492 1250 401435242 401435273
    0x1605090306010609150e0114070602160501061703040503030d0203220804060905040e0c0f010c0605041a0624030621150c070206040b0c0a1709040606050903030d09 72
    0x11501c180d03a581500400b2800588200c0090000000100d0a105d00c0b072014081080c0040e110388a0195480c12a507600b40d000d10010342e103180c0e0034000440da1405100311200294040c1d00041041030500611410710784038010005c240351b000708810002034401109407000e00d546e13140c0040c0c5941e114001c0c6425801c0640c1d00640d43c44103411820304004283d0040c009940d001d5070740014054032001400304440080c040c40c0007035446403441c00f5080c40c14103c160141c120614008000094595500050750780695003141ca12aa080d00000600d009088942d400742e4100c0714101d8440c5031840f0710244101030000c14105190001c00550140c0f55a9080220820344030400036818003484502e58031804c0811081074082c0c800401314460021100c240d41c10345070001c011a1800d031078040400003070ba0141e0340c542002d006000029000c078403222030038103108824004007070342c1e400400c04120444840e03402c04424003d05100d182003a8500109460000d01030040001c2c10034041d082620303500110b02c9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 401437742 1250 401436492 401436499
    0xf190f030303060303180518040c051305010302130506010801062d17090f120304020a05031e0105100608040b04051615020705090105150304080c190b061206160509 72
    0x900081019070550040c000c582c0603968a0780e00f04044841180d100f03006109803940659214043c00002d05900707901504a4030520440d442e0b01d590388041849208030010301d40da996075840041040d03080456042000f0015000200900e24003440060800700c018003407101045816a18030503525040030022400402666160743c0ba0b00c840c01303004020b00680600030300c2005000e00403980303881e0b0016450b455a1452406008880ea803503a0a154907000100187c1e448481b02c180000c2c1500e00348030300784011025003102074034050320301c400d9400d44030080d190039200b9811f03000c1008081d2384419002d410550000300302000d51030f9410f05919241c0035103212460f10403061000606103c00383e4502078a00d0981c0c00740d40c0d0340c41e8ac0e4000c100d5405003d00c6126000341c1d000a01c9040b42490300021948544191822801d0034071043d200c070b00e80f408106940c5a11300b000607562041c00201c2e440c0c540d2101044400000c140e060540c655281c040113021003400e501001b0704031120324020317020340d5031014001c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 401438848 1106 401437742 401437769
    0x40303180503251b1509031203020f0909091c1d0108180f01050a06050409020a0311011106090d030c0203040e0402010f05040503010207060603200f19 66
    0x10311403c0036000c0c031034030703002800c50300824541441040c1d80c50b0f03040e82040510124190842045018050009400c000281041c4051500c0c1c5605280c0940c9680c107500008155000d19a0019401844a410808070250014000100000700303042412014144001994060701c50384c0e60710310030035100501c81520b500424034642c2000300c3e41440515201070006d960b04010a0801045050351948240004509180a441e000d000116010419616264000b44229580740300060242000031545c4075160302030809041d107041c2500070b5860501d0550300b51915003400310b002401103440c0032a052141d62000042c5c07815211002c1c500041c0d6141e603001540c0c2016030701c9501081103010403001c02c40740c500b800a0000c1c60301c1b4000c04651941149084800c000c03039041001e0382c400c516410883c4980d1041c0c544521000300b81d1308114941000b80f40300722a01180e80000030f002010 = true := by decide +kernel

theorem cover : BRFrame.Cov 401258992 401438848 := by
  have h0 := BRFrame.cov_init 401258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 401258992 ≤ n) (h2 : n < 401438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
