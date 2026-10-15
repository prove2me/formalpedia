-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4924
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:10:41.18562+00:00
-- url     : https://prove2.me/submissions/b17c887a-c641-4c82-806e-1975f160c83d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 885431654 ≤ n < 885611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 885432904 1250 885431654 885431663
    0x10b0907050a18060906031a040e0d1d0108060d150908210103030f050901090f060203091005040305060a0e100e0f1014010b0702060d0510051e030a030f05070b04 71
    0x2207410705030341c1d402215600f826000c40110741e0310745152a4000317240850b00c0c0b00384e0040c0f66175007160b40300d004d1560107103504884020b03205004540c0005100350380c3e02150110000052110700c0034184000b40603180e0507228605030341e080e031140c86010400142140844045829524601c01c5411040e028080d800034180a240030710b8440f00c481c1c0c811041d40d201440e0f0f410046e00300034014800290440d1200b00c400ca5030f842c0c04d5440700480c2005948908013030300310200c0c40502102c0002c0050380040140003c0c2e00c1614000711400c6c10b05406c1d2400e01943c00014001d070800b02c002022842d8590003289284440d000319109210042c40840c00c0b02c43e42c113504000e58200741c007802c03459901044601b10841103400100001103525a2144440740c042c01f54980000d400107400c0150b40d41c51050701d1500c03190000401c20790620300d00074000022540326481c042e5401b885518803a0021692600c540400900a080b882e103460303504481903104940140c003400720900911011a403205085481284103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 885434154 1250 885432904 885432907
    0x3210516110f0105010f030b0109021207050d1e0f0e06010308071707061d0118021f0c02060d05090c06041211011806020109060f020c071404021c0507030b030d0212030405010b090705 80
    0x11800c0c808c1ea0401c05030070025040e4010005865421109400300703600c411540f900d40c0c1c5810301650044054020030104000307040083c0b003103d1144100394820f8100802c00d0804200c110b00e0450601d072110000d1101605281d010b01005d00810011020000c5a0501802041c90301e04580d8910040315140803c0e450300d18103c108052001b80c091252075500c00c8040c031300841c01c04803030380000c0e04800d10102281e170044135251a020311502400410740074980c001d200680350003000040c0c5e4001c0c0350840342c800061056030003041450801340225404d4659840c400c8508400caa01c480040b42240300743d160400c1856160004c00000c1c800d035920103080103900120300800b20b070030144144c540c455100c80c2c0b01c07031041114843c010b40028480c2e04a4401c80f00c8661406200c0c4006002806a00a03040d0001002c0c2d500150151090340098442e01c2c0948081080000000505030340b205200b0f400c00143c1e01003540c00c1c40000a600246a000d4401c0002050b801001c1010841000051315698081380c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 885435404 1250 885434154 885434159
    0x203060c0f16051c021f020d0e01050702160e0c030f0601181806051e01080a0f060321020615010513080a060b0a0e07020303220f03210516110f0105010f 67
    0x1200c0d010130010342e64510051401d403101d0845d90650300a00103140c0b8680ea4001345414540001d5005981082e180780020080c074038080790065241c0d2500340581d00c0d0404503203004505240848506d6004100512165080d950dc4400301068010050a010305215000e40100e2480004e40c010300080c11288a8102068101000030b10031b4904070341000e072040700b11505041c0181000c0468282d00344091030481c005840d8404104002c182e00300302c00310402d082c0f1802106210000014a010201c6d00140750760b10f0006030003c0303845034002da44090071074004058001d020761107080a80000e20312404041605540d490740703d80342003040b0307800711000d03070b1920480c075010302c0c15200740300c02000c6040c0c90b402c052034001002522407000502880691269048101003182606040400144c0c0140c2c010081e450030f0801030104500e0513a4906600c000c0b03000e0300e8580741070340215401140140c403800c0280d014a00143c1e103c0a10055a10192040c02c0a4001200e801d000c0d030350080000f020311212450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 885436654 1250 885435404 885435433
    0x5070b04060c06050402030a211106130204091a040606050112020c10050903040b1c050919060f0b03030c100f0603230109200406050105030f0a0509030c07081e06040203060c0f1605 79
    0x2c0034903449400c1d40c1240c0d0401070cc83c4220b280000c0c00d01c0d03044500081d0102c0c00d190542250108950108040c00000c2c108010010198010002d0f035800f40c8804144c40034054054040c0c1c404c09207110340940110442010300d8030150446a000054007041d01c0c18151121003600081d0020305990755240c00c2007804006c028000e1040a4000030b48001920f900748920701c8100d6509003500c4024800c5581d0b18540e640d4a280340d0080d42010f0004045e240e95030320824a03256255040c5d41c42c240f00624206c0640b1041d000c9110b07290032258056021040907001403517460000750b4082c591801d43d500da0221200241d0365054038104441c0c4080c0d42500c0340d0b01401804100d51507900107034144001001402000e0707010181240e4404100c88000c41c3c1c0d980e803003500606601404144440922031024041350302c1e030000c121001d8034035000c110001940c9200d200c066541c60282c41c069015040315011491019898000300070851380c0b00c07403441c9030181d580c0d50100440c440c4074003940c05801c59030b680014803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 885437904 1250 885436654 885436667
    0x10270314030306030303010e0a0207170d060608011206050c09040501082422050705041112220b070c02270a050115050a0207050406030c0305070b04060c06050402030a21 74
    0x4080e980000d41c11840e00c10042503591106004500b10f0000c4d04000459400b02e68040ba80e5041d80003100d00460b5a003801c040c915a0804600c0d04400750030718501241e071f640700b414101c0c100d91403809401c0019401d44c4070b10b402800c0c0075012030543c4200f00501e007425143d60103694020100c0c50024441d102106090342104240081c429030045024000e00c660120b0445044031043e91540c00a647d403003403840c106203012000d41c802c1d5001810303e003041200792804400b8100042d0b041003d0740f61507890199800301050030452805901c580c0d450407034042641008815800901170412400f407101a0300010b160b00c0104d0210070341d8000d2200c200d141c803201005100e030000d060304020b204035414282404084a030000070b0b030040190204044c40c1e040d00c20400d0340001c1c04050010440c0c59100e0514070041001c81c00240c400344200d45001860380042c074112821240c4c0340d40c0740c01500146070394031405414054003e03030341807151003441004a000000c003207900f002000c0940420740044c81e0058540d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 885439154 1250 885437904 885437933
    0x10e0a2c0f060f0612040501021b16060f2a1a04030c0213020418020c0c120307081c1a0406080a020901170111160201120c050702102703 60
    0x2105a036018005009900380e07605420a804640140000d203010001c14101d0240d4400c900c04100000c2c140300c188007040d4004d00c5440440f141d0245c0901c00c04005660f01c420306105c141d00c82c1e1010400b0086140302d003201000007907003071034409000380b0020401c11803e100c3d48020310646108403030b164100409494000814400c540496a00c0d20b001c1e100603141700040300c00a8000d00c1600344400010481c0d9040314040e00d0103030040300600c02c0942c8048020b400c050b01000c80351117405a00b40303c40c900104803100f000304000046140600c280d03140c100e42d41010350320940152203030505045449241c042d101c400005007900c4010006880e007044142c0700942d003c500107800c1400c5180150b115a05054103540c1c05800b0701d00900301254100f8010310a4a03c0d490311503030049401000e101c112001c0340c0c0458000da0300d04802c40043c2003e1002c03120481e0910001c00c2c0100580401400e00d03120300c07005610207082503200c5030030b19a46202c2e800050914002d40a9014109004210440000698 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 885440404 1250 885439154 885439229
    0x120602091017040335010302032401150302191d060a120207050c150703170105010801150210151707060f05071121060f040507060c02010e0a 62
    0x14008080c015406102001402c05070810005605001e1140d4000b20100d403a481c04000c0c03081d0400303100b070030841080e500f1f0100300d1090060040441300c50303002c0c0d1581e80b0302c80d00f100404511a403a0491202c00ba08005c10380301c043c10340030b01404c10100030118034210304002e41d8850b0340002c4c442711a619030902c01c041d4414450513080c001210103560180da014003112040c000141d80701d84c1400e18619021800011990040d861104a540401e0410260902620a0b00c5145802801031808030b000c00d824001c85000441e45001004903006007a40e0004256950042d00d0408402104800980305551906111140244010420349075100e4851943c800180c6c0a0003d03907003005002000c803480d14840208001003c540760041c030181c198140b0035514000e0002001d026034200102034541680c3c280c030901d0084a000904040803c40024490b66000340a0451141041010384034070480580c144c0c1004442c2c0d41480840c2c81d03030f00050024081440b01450451940b8440c1036108443d0300d070511 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 885441654 1250 885440404 885440417
    0x9050a0b010f050d11070c030f0519050c0d14011401150c020d0813180515040e0715020f030301240203040e0a18080a120b0303040b0715061206020910 66
    0x41c4034a5011003640c0301d5004c121404500e80d58003000c005014090300300f0241c03845030003080010403c04070050140c4001d00c14400c2e14130140035408041c42c40040200090500d030844445007896207028a013240c030b994402d052213991501010045800c54801c810007000c942080ba0050202c0240c0b0042c2d00305510b51880c02d826806030b154007062480c14000f00041110343c0116804904516103007115000d4202c441c1c10280d486c0702c2c90b6a50740500401c0d02c003000081424203142016040a020f00200a81041e0003054414075280c112025280303a2001801140200c2032124001a0244011030081000c02c61005254915444140c1c0312000310030710200b5980104410803560f101c00008a0380a0104034000500f042460940041440903500081120030005100b0f11081d410401c85140d141e02c5250030010010034070300341a40e9106601a03603500307410900018002a01040e070701c40c1c25640800001c52141e550341c0b484d0340307008548a400c40710503801083e881200d0a2503100c41320707000040d2a021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 885442904 1250 885441654 885441677
    0xe010b030c3a0e03160c150f14030601050307080a06120503030f101206180602040306090b0603071809061506050d0b0904150e0a1506091a0609011d0301050109050a0b01 74
    0x86941e44141084108103070017807849074042c00b08655904006150310303260755166001100005002168085c100c1010440d20300140e40e8154103402070380e00c80c1c078044c0c407404c2c61904c0d03041c816104040b008004100340c0d9140ca07004104c0400140d80c44480601c40c90040d80c881c1010600c1200d8075a0040c284411420503050070802030b0b80c0000d40707080894100000040595641c0e03070b8104030440b500340c0030f8821400010000104074281d84100f21440c000c2e0801c55582d100d000401d91510316911076404114400b040070703a00310070150301041740c5501c1080b0006002d003255103480040c082c20f600c940d003c02d00110300d004620046000381c220882c012110880c0f2071920359941026141c91070102a0780e20f80c2c036003440c440034070100002d480c0503821280320411500904044409804130b40103c81c8444c3c2032401e04c2a1141c002c0034040b0640d28001c122504014152004654140c607214000a0509040d00035030f407603880a00c40c45c4d0182101e503002298070b00d0305800100a0350a958002810010011f004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 885444154 1250 885442904 885442931
    0x5010e130e011d010f0e0a12030f02040f0503010e010b01270509250c150e160b0c010605030601030206070602130e070e090705070f061a031209190e010b030c3a 70
    0x1c003c2d802c2c1d12262300322031552000380890042c019444c0c0700300020b100186c0800c80c8001c2c040c0d00c108a070801c5000340303c0b0323061a070703081403d035803440c0c02070f5001c00e03910545e044908221090400d1031801e0b8070200400039945000050701c2d4002525450588042e00c15800ca0516140b4110424600a400c0110968403180e83d1501d80d61480c250f1104046c2d40c4910201e050701c414480e10311201c00c103662000040741c60f420300060590105484810302e41c40c08000007400c0c02c01140180c122034004101c00e0500c03401d40c60315006540020780c00c1044040091001c41c00c0c003014003240d07024a003a5668000172340391036800c0c044e20303000c040d0142003800400e0203000c000882c86807458021551020307001c101c0700805080703d022036600000a6905000c0c1002c003914400401c405032108080480d85400301d41100c41c1610403010290040203070a00c0c81e8401400b490000500a60300034000c1c80400303203001482840b003c20340e20044800f0010005450641c030401840a4000390110b104a0040201401c41c801 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 885445404 1250 885444154 885444163
    0xf0203101a070f0f020a050915040e3009060406032301030803161806020f060f04020d080901120218040b0402030c0d1a031f110405010e130e011d010f0e 67
    0x802412880c0c2d00310800c0854603a8800c0c2001030402030200300050a040c1c0d41c102a0b0300107440c3c05070041d460184d0b41c0096403800908a03072801e10141c41111100c252005030814cc003182d10003800300c0c039801c1003a0700346034648000900040440350340009030401c1c01120682d0030440e038003055401070007220040c03010804450450ba0030044082080e240c4140300f4809540d18002d4810440b00c001d003803500003a6135a004921582100140c4042d0f449654903140115141d4000751000f80d000f410840c50400000c403140001d140040c5c05041c18050403140340d09030016070b8824510400464042e44004640e0300301409600081a000c440560071071074821000c01d140d000301100e13850450349031b46080c5d405100490003130051354409070070b54001072035240080d40b444200c16008a2614a0115400c44103e1818140c0701940c005a403400c1c42c01e0070302001c1050109001414a584941d118014114100244210034030904016606041018458155030843d00030188868140d410590420507551011a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 885446654 1250 885445404 885445433
    0x806180f091c0f030b0301150b07020f041b08100801060308091906080a09111009030b09030408070b0a0522060216050f0913080a03060e011d0601030e010f0203101a07 73
    0x540003171910980c400081c0900051031000106507035a480104480707108500824101c0d000351032240e0080107010910080312003c403502c440c5082c40e80704020110303110f11419504111040c0c4400202c0e52203c0d800e030300711a0164400c55035680005017200341d5007007065084011010312507050121030b103440307030107440c0e407030010040d900e140e69841e03400081040490022500030005041c6410704010319138080c000e401140015540c00f17140000084c01c0b0301e0000101c03001d803400ea0000d46407951414200c6186904220040020b014062220703130360322070f80000481010700c00403080c05081480c220300681407041d400044c19542003c070303400740f055840d480b0703c3c1b0340049415218480103a541c924006180a00c200000700710403800143d24420076899000601a00c6411070f118000d666510601040c44005070009200e40d4030701c0000130b0066019501c10341d000100040041039990440540d030040340c0c4100e0b08042d004220340d5040c8031285108001065031801c180c0341c185001c0c0d440d141c2010640c40007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 885447904 1250 885446654 885446657
    0x130e03120c030642030105030705031920090901090615210503040b0304110f04140a1d24160c080a030f020301030602030711030405100806180f091c0f 66
    0x40c0414413050089481204898820f00362090f80c60680c941401c0d8150b00078440e0034401d105800022070b9918020418140b01c01d410320140d20070342c0151707440f18403c40030050685238070b00c512000c41c070700d0f078076071405d80c0c0d200d18000310000030089001c2ca01002100c0708420107000e2145104014071510b189201148141003540c4502200d6558901d0801e15500c51a00141078150020050004001031031020070042c0000711084040031003820140400c50740103800742d030344490364080424507000855000180007200d440c207100c0404a0b0081480c501582ca200d40000444290308a4440a03a410440350304042007062680c1645809580140078500544015114010010f06001507500a5002000c0e140f0201d10554a0b507940e4201403009400031500f034004649401c04418240c1004400c54040d600004d041d000514130040f811100d4440c004d040c182c02142c14408200185920080641b0500d0701e1440300c5001c0c0350203040181803a000d071202d4900c115941c540c1200d0250007800c2c05034101c259 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 885449154 1250 885447904 885447949
    0x60c031b031d1c080c03040b01050603101a0c06100821220503010f06051302070f080310050a06030608063603180d0203070b09130e03120c0306 63
    0x5100c4640d40b04210204000d1584240e450710030101e101e52049045851580c0c9588607550382d65080301e01e8500c0120707402002c45190800602c86440c004018540040030b2070a0782c2a016243c12400240300980440c11140c1300000c80c10b14a0010700300f10944d801410100d240c034210b45490007071969103100d449030200f000803000b209244001160241c0380c1d4508000c40d8440099544c02031142d414015000d154007039424580010001c08241c020700c400c8440103031091000e44120140740c0003d40180300e0440ba40003e5a4294001c903007080d0245002d4002310b14005074403440d150401c6104180c03580440249400c08000b08180c1d5804207003176070301c150041c8410700813510320703012294a03075404403031643e03140700d10048100012070000203031500c1040700d001c9981102c41c035010048008402e820081d8143c0c0096000d100740301c001c602030031005070003a1102c20071041c81e00044040d50720003030640c40564008100c6108490000c04d034550006041400e152560a0400214859400d6004038000b04046c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 885450404 1250 885449154 885449171
    0x121a0c031044100603060b03160905154b102d030507020a150f02040506031e0a14074d19030804170a0c060c031b03 51
    0x81040c20710150b2000d40701914018140301c3ea0440040c109404140c4842d4a0041c50300c0d201e05000880781d1815408e4076100500d10b1900600c6c070054a80102501801c110401407d00d86440344440c0c07010040032503221900200003c0c40403085003c1c2d6403100b50010b6864061240303500240d00302e420491006880072840603034091400e50b6180404100b43d82c40c41041e41d200c1c03558103001021401d9400c0c9a98042c006503c0e105c20481e61500347e0380c000b034541070401c2022008d1a0141d400406501d6456602600345952080000c000350000c403010911000e01d91001c5032134101942d44158003114039942002514058503004401140c01000b07041801034801a018100a0b4980f584e400da4a04020000c0c850110003401c201450707046240035140e02d403007040398509110210360714491900ca1682a00e202d102900c086441560140c4107691481314007416407180d1021000070108101c007034851601c0c5550600d0042c04035644003a40030101850100039500b500520758041c0c0f4034011034079002c0350510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 885451654 1250 885450404 885450509
    0x6150313021f11070b03070504170106090c020a03090e100504050403030902330f03070c110d0609020f0d0b06010c0804090c200d09121a0c0310 63
    0x1100310701d00400e201c2c00c2e03030b000040a80d030283c0c1c0002c9440e607440644d44d403a60344082c10301c21408107440711008644240000d111000c407420b440004d50441c02c0003c154a81d482229404540400004400582000450740d05264001c0e000c0b0f401040c0014021113285400c152140c50610743d0700402c0d02c00c5071650089814144650000c0041c540c00030058001c9005000b20a00c05001e410021020a13294042000e250259a0295070b8955904c18425145980301142110881039042c03044401d945900603a00490f111280148a2107200e10b00c00501011540100086104416003a07480b40303d0912000c0002944540c0541c1c0045c0300b801c2220355821240790205140c021600105880d501d400389507140301c0c3d80020380701d0b0f41c0105490f82882e00354040140c41d446005e488005004202c0c0c1c640d00700901c0030407994081815000d10f03000c038521210ba640542446406459120106901105005030452210f50303a00040601d0300d9505c0c403c3c811110342807016410030526400500541c9071448005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 885452904 1250 885451654 885451669
    0x2d0b06030115180c05030c030402090612010608030306011101230a060b0c24040b0103020f01090803030f06040c03020414060f070221010501050d030c060504030221120615031302 78
    0x42111040341a1401c3d12603401c0070b001c0c91408284200c0c1400d122800c0e00f22070041d02128010500702c6141c6203595515020301060720b80103403e40da0040c1103d01c018032a034000780f140c500900748100103140d40b410303e000010000824200c2050341c691401c81751036043c0b041445040c0c0e000300410030112041d0b86a030320180040c001c130f9000c0310002100240726140c2040101d2a81c2c550a90540c3c140b0311545240340c0c2065104c01294001c00145410005001600c0d05901400e170240c014035103c035050392034540c20f9040d0b40013030710b01c050306410704c07402d210191401d80141c01a00302a03150443c28145020000c0d01011003160319280205800941a1085000c01c411503881740d401138030442e41146055139000e40300c544d1721190380301ca51074800003281a00e0001082e400c1c103509540c40020083d00380c0c0f81c40c1e0082c00083c00032801d5103d01c500309030020b0600c01034010103c0c00c0500329034846e0060080e8020542005000078494200120458900d10340002941d82011070300d4507a105500d4148040b9040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 885454154 1250 885452904 885452921
    0x3030b060405031f202101150c0519051e1612050c040c0206010608010e0f070e034207230403060501030c03120914060c01090c03050a2d0b060301 64
    0x644141172400c04041d40b0320001030503035042500701c0c3d603031450030242d80e5502c0703610038015400f074000e00c6540300700c009200703441464609010b4030554498120810503002e061866000880d0640c04c0b5965407107446180e03081244c113039820b10020304004003040030b10240e940c04600440036880180702044013405800c00000c854040007401c00c205a140400010f96141c02c02d00c9041d0000b07003100d00200380220b40c5442d183c011200c0715000c82071512036400640d000c0100300040ca07010300c1440980b015a0300c090400c3c00141c2e0002039921040d0480e241c80320350030b41107a401c1c0c000488200e414009940d80c0001c000c1207040354820021052948080080010301c82c0354409010703039041c0b400100c103200c6202001c0341141d00c246104800d0301c0c0305d03050555001c038080c03040000c0e00408905a01c01810500020281c00b600c140c000104541c041c1d50b4140004850b4006860541c08a140700003044076101325103500d80c503048000a00910174046004845107000801460141590042851354400350403802c1c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 885455404 1250 885454154 885454181
    0x150e0c280902030903040f140a090b011107180f02030103020d0212030408010f051005010e150c0f0601090218012a060b060c0a0b010504092006090d06060303030b060405031f 76
    0x10f490400c1040c4603641e400174000c99542900c80400080c4000d14048101c07141280641180d80007803034078400d50010301003030407080d06210032407144e05c0381d20a0030720864000e001416001112500400e188038222214405c0d41c0c21118810001030000d41d90b04001c155120354102d40413001025200c0c0018150f002d80c0d0300102e8103600700031018500b0404d03500400d1240388030200d40000181d0340d00044806406200e580c5800841148003641d140c684c8000818815003000c003124070348103202c1020b5281c40000d030300c464146607010856121039404441001040c0e0001d1034560152254031034981400c001c2c801001c10f20032a594101c108000664006680e1248020302d031549940300b581150781c852a220f10304445010340c0000200d203d1803d031058812181d0808031000c0c514500903070825001c56001d14496000c0028409010241d44d000c84010b18103121398004030300e0910b985000f4090344d4600740c1e02842601c0922090010b0303200006c1d003403086000161000c9181c242c00d80c4c900c00a05d11a046100c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 885456654 1250 885455404 885455407
    0xa05070e07020c040c2c030a080322080409020d0906050717010e10050f0333010b072406081e0f0609120c0316150e0c280902 55
    0x3550038001a03124421841e41d0266200c405100b0100301c22100c178102240081415112180c29481c4601070900b01141d40344c0c003c0d06c80d0148100043d281c9072502c08201c40354a00003003081540340550170038103015001c00096030300c01034283c2d5a06a41c2e020b1401049651a070110301060240c103d50000035901381c100008002e02d0400d40b4008202d8049034941d42030b95000071000080080300025810710500b5030480c2c001ca218280010007030540300d224181c590601c42d1303510141c041c0030800181103003500d0081c191841a800302c0030101904005034450200900e05200d20804100080c0c02440c80c5025180900d0305000c26802d40001000e0680010f111886030150604044a21081c0103003151b10001c2110100000a400c055466000b00d40c0740105411001e840c14501020301c029000e000d16a0003541c0c2414000e031114508640c0400342511180a521051101045140725600640f0441006000d40c541e2010105034405580b0310004401c01013603c851100101410001000c0c01c04441d056 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 885457904 1250 885456654 885456659
    0x80a090e01090204091401030c15051210050a060206090c04020708070b090c030106240507031101020d020711011b0b060109031b140105120106031a130f1a1807020a0507 74
    0x5030000c4d0014061584168038080301100a90400402c003412203030702951031083c0a042c180e519247c0400c0c50401da0522000380807088043c2107031030b80c0c2c600c01c2c00c014150548581c0751030204070403024240d100b10251b410a0b400d0003011500070a80c21024881030b28096a1a5814079202020744070300341d00a055007045030b0501c54061401300b44591604002c80007406019124444a106007500012501e0b15481e1800c10720082401200946074841c024101a2030a06c0c000a03c207003a640801900c010142c1d0006051040040e101e408031301411082c41c1c0541441400c29030a4101401c510001e858010240005412a803041168a015550003001100c01000141c0300f440c50410b0f50160600010b55044021203079413050040c3c98444214241ea60426441cac1070003500100805903134540000e000500003127003500c1c0e41c60010050002c0c0d000000c0c3c150721780031101045400080580395000203401c1c00260556035000f030001c00c0c0c071841c0c2e03030742c001c0ea01e03000303000da2906480364001407103070148a100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 885459154 1250 885457904 885457919
    0x6010e1801140106260a0f20070c0b04061215090c0809100203040f030c050a2310020906040603020c01021e04060806090f0a09230c010914030a080a090e01 68
    0x140f41290300a4644045a10f1010060320864000300b1004134851540c03400109541d00d19000b02c07080e040400b60000d555150201c030300c202c21414500001d6000d07000190b50040100f0351a8000088c4214410542810306242008150100405115408070786030110700c2c0308a03d070001100c004203071203101007011054960340541119000c95420342d15006410380c03d041c600c5140200c031702c05ca42c000d241c1c030800003065900b80e80d9003175008402d54903841000090800120f01c5d6080c3c80d403000c0c8100c1c1103048007032215619031130249000942200240144154034860311031009807401d0b111181409030b00c0e13502802405009002d81c2d050780c1a01d1441030000e10030150800028407e0320310641c0c03000e5484e40d030350007440201c040950307400c03070500440000992440039943c4084403803445099041c08880c0e030300308180d0132034118001600803a0400044119030b5a0480c1e204402400340d01011000303107801c40c00190321580040e41c0982126800a0214880e51207940404040c0607806440d100a52f101e081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 885460404 1250 885459154 885459191
    0x170405070b0a0c0204061502060c0c0f1b0f010201090305160519140d0f080105060714060f0105030d021603031803050109030f0e240a110105090109051e06010e1801 72
    0xf42640a81c1c6400c2003c00d0340441c0c1070745518100780c43c1e0020f0200351500c02a820303840e07000c400c10401d00c0c06000d183c20720410341402410b0801040305000d5000390541400c119181a02c5440035056a1402090500207a00842a1040c0f00c5a0080c0701480e0a458145942884144402c80c00b1003420708052008000202c21000d103520600c40481c0c010545051082d03070b44e041a5102800498480700041003d441c1c041c0041280f00d115541c40444c0c01c1907544030500e00601a200400402540700040c0300074282004007210705112413008222514001d5441ca100c2915800003804000028005019021020607907200840d0b02c0301c0200180c0c0c030700c2d0030b0051103c40c02c80d25210010300c400e0000c118900e07002c9a109109008101c072080c007000c014140c007aa9500c411200e105100c0c014114890003c03081c031415214103101400850348010078948141403415a03400310119640c04c0d03032080c0d25100e00007a19810b403035141500040c41c0d2030301d1114410980f440d000c805c1d41c0758209031038060f10740035005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 885461654 1250 885460404 885460427
    0x110703051c0816080402040c0302091c052a0f010212031015050304151e090c09050604020f0a030c05041208220b0d051302030f1e0d170405070b0a 64
    0xb5a100e505485489603c001521000e019500040c0381134081009032030664045030242180303090040c50078045001040e80f0340c810401c50610307044036018100604c0800d01c40342d0481d01c3d601d0714000c00c0caa1140c006942c5d03040840111806104484030312074035030f402003200c0d0f83e1208000c004281c40703140c400b200e2000d1601c01c1c0503400c5001407031240000c1c2140a9016a401254010303a001300c11100e01c462040141410030303074107999104032107001441d19614030500181c02c0c0118485061241846500c20650700042c007040d028601c100540303903444c60030209803200700801d440c010845e440500000c03181402280c1044c002e050300c82d80c0107010020400c0091100e248044c41210b40520420064211040c0c24403c2d020501020864901303180d0b11a402158859001030002c4103c54072500401d00e01490340402d007145da480b121800790020401c444041100d51510000c3c0403607003c0040007800302214076891029513261201041c100542805450041d00c100340c000b030340703039070202c03100400c13010441d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 885462904 1250 885461654 885461657
    0x603020607151b05040e09010f1a1903080f0c010f0515011b051b0604030c0f0e1012200d053909070c14070303110c0907110703051c 58
    0x202c1d1070040c150503000a00903c09031a100e2900b0f00789040200d0b001414000c2082982c0c0d507031940c030450800142d102d040c170b0400c003d09448201500305820300c03045c40c0c810980c1c3c40701d4128400c0700b000065040c00496420004079640241c8807950075915602500000300280d00e024102402c0226043d1700320001903044c0d500340d80361201c0c0c80110343d21801c0942442ca01400035044401c16940c031380d0364500f04404d42c800141c0107501d4581d0303940700c400d1820f419402c52000e010035004204a00c00c190a103440c0c00c954080500030480780340040d0b100b01c080c00a00000d203a201d040d0900c03401c10304c110040802102001d080c0e51150800c519107152207001305d4a21040c0c0d241c089a040004941c0840e001e211035100c1c3c42c8402400722103404101e40014010150700401803a04080ca00051002c04030a41041143c030003090200c4c01c525000e0030240d209040000b960303001c240300c0401642c1e101441741d045146070905000008040d0805401c201d0300e40c00140c81c901c60600380c42820444900c14030709000e00da = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 885464154 1250 885462904 885462911
    0xd0c2f030c1f0c0c02031209030a0c0e011e121e06050a090b0a0e340803030f1803091011031c0c0203030402010c030e010c0b0c0712020c01050418060302060715 70
    0xe016003550f003841d0071140039406500051f010b24903403401130f00605140b01c0c000d0840360225650b036140c503042421034004560300b1110000400c415500748422094100105848102070b60801420032102180014041c10003100349503500380410841d1856252160801d4051005141040c44000507146040c01224080da00c20b00083c201e15007071295070301041d0100064981c0f24014021f5015440401138103030307450807400042d24441307401584001c0003041c8070000395403280341c661044417040341c00130504000e81d043d00400d40c4040001008542e10007108960761091003e01401c226002d2001c0614006244800540c0d4101c0c104180c05441454030362400900480185460403030b2280400e0710000c6c08210303200d0744800028007582c2503240428040c507105655030b10325103414a41c0d65003580c040d0100e14000904a090101e240c50105005001d40000e11000e200340340001d1146c0b09a00c54000c424407070112850349004160420001150028913854541c0c80f00e0500b007185c61101c00c0c0702c600d558078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 885465404 1250 885464154 885464171
    0x5070507110321091f1d010203070f1e02060a110c0a08031c0b031507022e02160c030602092b1410110d0c2f030c1f 51
    0x140098980040c42031000010140021121183c00640000341100d9110b0f41003054005980c0049080c8020001c255035624074061245a200c03903c0c0c00c2003820301e411500204254404030b030409101042c400c0d0300000480244c003040040740c2000c0c0308560001d5008100140c2e0120755984460f840907206945000da81c01c0b00d9041c41000b03102d820174440d20f08a80c105020081344078502201c500100c02180c03001041c002c000c0700c00241082e02c042040c1100f030151000380801c1c036904000d84612840400c4001004c1a55900d5001007840e41a0f10302072003a800148410403e14403024a061540c0d00000c4054602e0722031401c50f019401c952417260080c01246040c80001501504e038064070f0841c1600403503403000544400340000c01158040085100b40300301e0b14540032040c412400071410840b14692200c107482442010360300302c0c4540004002103c003402440418142c0032881c0c1c011000c80c541c14058070701c0003c238154041c1000000c0c590064074140208089140703400504243c0d0701d40e0030481040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 885466654 1250 885465404 885465409
    0x203060c030a0e063d1e05010302030403080615040801090503040e06010c110409030311073806060c0106080d0c0c0b04080604150b0303180f0a080d03020d020d0507050711 75
    0x2802103403d91802d121403407101000030003040c070070b41d030400602d41c51603545c40c0d040ca8a038055000d2079100d0310341180641c0700000401500c11034507014010903c2e0542c5142421b4900030000840603000034030130500d040070400c00d00d03451320840e4010204034009101010b940c0c1030a0743c036034000c5c0c4205004055207900040c020341c459001080c0641c0e0140c81c0400074a0340c481480b004100c0b104048040c183d0b61581c00100e24030361000f4000b0b036441481c05804404040e0f503009448920f401200c0751004070090741c0960740c6059800107510070300640e84140c580800360714003400b5180650001285000d070880c440100da41c040040c0342c80502800c190071081d982c8028010b01132040784103401041e0095004600044e08030400d04918820226001c54601d1900c00080d0942d0311a40300030001c40d140c07980300036460400403040d00703141604941c0201c409240a4005864440701c500220405a0000702410a020b181e41902c1d80c15031480d004000700d1a0010000e0110b5024560680d070341c5201e21503169007032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 885467904 1250 885466654 885466663
    0x405031e061602070e150a0905090c01030b060d020f0906070c0623041512050112140604020603131a0721060f14030a080f03061e010e0108090a0203060c030a0e 70
    0x50078030f90041c000b6a01d010112105408050704003500141250301c1164555190600340d00508080500010581071150100d441d044540400b141458101400c4c2c207650f50300c4009542d140800d0b0740700969549000b4041c82d003140314041100d5800980400d00d007060041030307c0c8640640f03d907522013401e580d100c6a01d250141c4994001c2000300c0f4003c200030310810840071080c544100740f5060080640c00c00b50544403c2d130303000341c11500c00681022070120522488103070032000b480344c41c030182c44035042c01d80100e0580d200041c1030b140d0400c0741d07140c69001c10070034440203004025044681301240c00e0a600050041c1d4008020780c18110580000340d104100620400084440201c0c00407200da00e4400e920b1410300049001c184e00d8012a5480e101040c84180102203929080300e28075680d1400c04204080340152110075045a102404c0c1000c0d541d03003080d69612504024240b00c0c0080d5690302c0c0d860310304800102d000713425020342001d0089c00640034014500900288100340041c403003040215588 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 885469154 1250 885467904 885467941
    0x30614060a0b1602010f0c02030a03030b0411040e0a020901090b042309070c0221062508070e0607110325060f090b030c0f0f0c010b2709030405031e06 66
    0xc3d05801c0c1e504400541c000c10401e130040e41281040c603075840d070070740001c1e08000c4041801c1c0e020a80780d5080420710316040c402c00300300740b030b88d41c118a04142c1070102d032400c04080140000026070340014100110380c0100040740041005020b00d030390f11070b140c003040d10400c5402948041c1c0e01c0c859603240da00500e0b1203801d5911455a82c2d4555050500c0c0d9000c01400710b14509003800901e8070044959071034241400b13081c2c8903210b6000a050300c1103030b59280070345002c040c10506041004c007505004a4642c002e800204d070400848060380c0700c016504280042d201503910050b41841010709032002c00c8820118421000707400c15010804961340c2c1401d42e6043e880c030406c40c2c0007894024041c4001c031100070145802c076400d100e065083c0180401350202e55071103502030141e2410301181000034000b0034060b844c20620207881948140980c560036401ca8020001c641074580b2016001600c01d10741041620014100103048454160b1658504620001405422000c1e8000c00c400070b80041c02030842c8060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 885470404 1250 885469154 885469177
    0x10080105090f06041805011506031529070f170a050a2a1406100b07080c0a0602180906030d0807050d110d0e01050f091b0604030614060a0b 61
    0x91950780d144038004400b00007859154000c3c2d40301d03041d1459031003121140c40d54901c00d500008e95103400c03030412490305509500140c00c0500b4980e042c82800c0420204800301c5818402d1980245d48480544104074819014440341c809c0120312603080c031140c3d6910310316070f50040521400c6040e06d4030592681e0f01c200c48100002c15010001c03808001c2c4101100d080f003000705510320071800d202c2000d00100c4261200c041d240e07965000d8280945a0307042c00216000fa08a10181503002d141000f00c150fa40131306140a42040c001040c111540c580c02d20042c04c8490b0300030b10841d681c4c0210340c0f098102035650340d01c6c47e004868503400541281000035800d00c3c0c03807007036848600c42c590361028107d44640c00550403550a84c0c84101600c1d42c030711010090811070080410104420302c0c41071405085481c010080031000c0700350014486000000714001c00381722a91400c615902411001041d2680f14903400181010320707100c010350011050450b00d5002d010221a82e51600380e4582c0c07000320a0160802440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 885471654 1250 885470404 885470419
    0x17130b0718030f060c080c03010e011418070504091d030f071e05030702041a0a06080a0204080604050705090907061d211501060c0f060203070302130303050910080105 73
    0x940c040d009003038041e168444281c0708000c035922035a800044000c03012040300e40c1503c1c0c201600402c2c6d00401e2440d800130785000745d18110340c544141100349003010b1003030701c070000c04010490f000d546884c64842149142e9003007046003810840e070300905d264003d11506d01c0a52401d898400860716068950050840c5980210308007610100051203a0340034003000c480f900201844e0899224103082d9101500380503901542e1540c94034010703c8250780da458a840340001c0c001c1c01c0058507030341c2c46020109076101864000d01031340d1840d000200a2295410410052140d03004000c10044001680340c01c1e0303202640d05071100e40700c0502c030541c0e41c86a4040d60300400c0c500c24991020000600c95444803500c001d100b82c1d842c1c0109182e4652045500400d4030707050f00403881815000401c0040c09004008034078001050b4141901d85801e40c01c908003004016036000401b08819910980550384c00c1060a0505061a5581e140251056000700c00070350244000e111f00301c034000c2c040c17644541200c0c00503200c81d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 885472904 1250 885471654 885471661
    0x7200307150c0c02090403050403060b0a030203060f07181e08010b0603070e0f10030e0607230706060825050d03050d090501061a04080c0d0201020a020d2117130b 71
    0xc0c010b0102c88042c60100400039050001603903843c0680b6000b10b029440303050b0350300d0560400c070302642c0408101038042d501c648010001600c00149641c4d00032110303230318038009403500d0300111410420032104249083e003e11010420350310380c1d01910200318071000d018842e10b0303880081900b619881c5c211194490790a20010701c00a01402000746656402040c01031401652800107000000401c403000001c2d603030f078201402038642000f0f9240c02190b60700380802200c42c090781792030085900ca6404080c011011440100f00030064203d680980000303010342c0e90000e00e8210808090304544517030030542c0d61030400001ea900f0500009002c090301a580c040c0340001d111304100c05000c48040842d40d96582d03c20015103144814940c52511850b40e1080303649620b020b0085140c000200302c2c00e0301c2254034410400041c2e800182c0f000700c80b5816180804100100e08100349603410460b040089500314407000405164401d07140d8503000012041c140136522840c1d030502030030759412002450000c0700c4020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 885474154 1250 885472904 885472943
    0xb0d0507060804030210050c041d010806190e030f0306010807091a0a05090312091806090a11041a070b181e0f010f05060901051207060e010309050607200307 69
    0x3907a030240c0207004071070f44606d80c400301800311201259807081d02c20010809110101d100c100041c041c1c0305640301042a941061100e070344641000c4e203800c0007400d0503801c00a081310103422038441d039940c4005907515500f035000d0308100d99004882d0140054080700028020301e000300c41400c2550003504502d1310700c400750341c4805840d600a4040b07000f80041480300940c256401c200050f584d400c1910000d813210500000e002396840220103500101d8028010000307580c8440d141d45030700107660300d000b050302c0c8980c2c010458a480346812021140d070320607450041240c001e1008002881c030403c501d01243d030340d21181c02c0039409103d1210070150400409c1020001c0c0781c900f001d00c48034212051344c0301c01703c03a15402403c50f485000028007403a1034108015481c94040d003500e0050070103540070314601000070446912407000303004d5502440040c00000010364420313441035a01e543d108084131410b00700020090702c414000503807194003907400c10001e0392160b004010b50f000f66a00510403016a0005d054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 885475404 1250 885474154 885474167
    0x171603050c0a050d0c1a0d0c020a05010e1b0f060c070905100e040503070f1e05060906060406030503120a0204180209030c0102010218010806060c0604120f02010b0603060613090e0309040b0d050706 86
    0x70000380406c0140442c0030003042600c08c15000d0082d680046c54114054504a829140c607007420b01c040d600310415498024510844420043c107084569800741c0603a200021054010504c244885108007500802c0006040e8841401540500c0c0880441c60755000d00c0c4400d000101d600401c0c5800c184101d0300007881e6251040407042c402c60918094045005039641d020655101c2910194004414800303a224244130300364200d4029076051200604507143c842d924410124401d46481d00e28001071601d01d0945c0c1034401408000c41c4d120018100901404041e4200011151003801911603094440d0300520803290303500b180510500c01c0c42e5090740150384422000b08005e801141c00c11440c40b1300a401e0045078880e030704c11080c4120080088400900c03002d00401d140741503a150411100d01030760f62030107482c1d0103002240e0069135880c010003a04401440c41d403281e01c240b420440001486080440a800305100070b036810083c101c44a01000043c140080d4040c005d6081010b0901510b4420b00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 885476654 1250 885475404 885475439
    0x210103060e030a0c08090f060c0d030f05010501020a0212010b030d0507060c08010515090d06020c070f060e060403150213030623040f0602031308030703060f0608040c171603050c0a050d0c 82
    0x421f0780300114000800f0903c158880390070283e854001c442010212038240c0700e5150244040d000030800f542c10400040e50760340e200c0300c01911809100703000e2011400d00350040310740a80d0203030a03500d02e2401c6600181c01500202e1080758550300b0100d110f0701440c81194801d048400043c0b8080804201616400c3d0590014041982180c111524030010440b02d000400468401000030100710b4035000d400101e0071104c1d0000c05c1002500004590290b46840030380c0d06490700304041e61002841d61601c2c3c2d009105078a1407110000e10450004140060b550180406040280c840d4081d030110740010000510203d40050046640b400d802e00800c504d40c0c0034542c02504035850000d01c2d121503d4000440e04111503450004c0d4442c0fa0611600e071040a644008181505114403241850780c1d521322580480d0258100b0904802184c00c101d400800c01c2003040840200008009034503403c003e070f2240000342126000350344110002500381018441700303d140360444069041c9a0408142a80004170300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 885477904 1250 885476654 885476659
    0x12307031812030209060f07110d170d060e1602010f2306010905120c0114072015040906080d02030712120204210b090c0f120102210103060e030a0c0809 67
    0x340005c461944a42004100420a610000e6103414032443c02140300b40100101d00d0113094900e01080024001e2040b103504a0001030456407110810504100240040d40c04404803011200502c195603c800d40010200406540280101e42032a0740304001d90341c0ea001d20070941c1380100c0c2d87c0b17840200341c0d40000b904000140b51131400182c1e54070001d07404140c01d09a242c4290800c0354220003a6803c0f9150840380b0362400d1515044c4201c030b8849100c8404a05440c0522410400e000f8aa55130f036007000700d100615600b8050380711900d0383c039608003c080c14042e613401407040b00700d003140060002095501c51030b40402c1151134000250b504641030903e446500d10320980a10002c00e8040300815441581c200780c94501c0d000340e5050030680c4c11900d002e8070804480d0004070210000d0703110703003440450300f000641e000f42011f410a080d2070700a00c03a00030708041c1440704c501c0450090f405a84840e0407a03001c1d03002442101050ba54041d201e10aa40790b20b40480c100c103240703100180c0f090002d8150034200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 885479154 1250 885477904 885477907
    0x150a03021306050907091d060117090c031b040501140619020106080d03091104060b0f1813050103020907080106080a09050c04240b1206041d0123070318120302 70
    0x1101d011030084003064a0b04404544000000c7c0030005c407030440c603c041c2100c5490348440d0309005d400a0100c25842c081c1d9058550404000f400340c6004000c61a0040703005002c40c1e01c0d542801c1807070051042c0040c0410310aa0a0000016802516200f00c40e140d41c3c00401b40c518041c1001c0c06022104081c0c941e20b0155500e80b40009808941403001e400190410b440c04034103072500f07151064094080d90010340c07150380703054010301034000941c0035211076100380a00e0316541c400d4168400c0c0da0101000e401ea900070010b02100106100a80010f81203034030a484c0c000c40c584802409962610303090058000059042c0300045411407260490540540a8420b0311503039400c1c1da02003400c0d00c45510802540c40000d00d64010500e141081601c01855006810360400c0b0503441c0801c0c0d121030142103076206945803d0444d82d1446926090705180c1c9400300200000c01682c1c00c9008000c0420780c8c0307203011423550400a503015010b40100203281e0641e4242c034040809a40d5002206a400c408800400d0360 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 885480404 1250 885479154 885479159
    0xc0f0a0308070807170304051e030d0513110328030509040218010e0105090a0e0606270108160f1107081b03071e17100911030105150a03021306 63
    0x1c045004084860098050b40d98580e0070b41040040340e03000344802a0501c100700100400b26a0115000903400d00e104560303800c2c1c80c04105001d103503005001d280002c80b0702c1c1c141480020f00d562100d5101c42489101c01d481c00310088000c0540381c2102c00d03c44488a148041121064400d400b00801c1c1c0900c20308000382070031000740c081400c0740c0281c0e02e01900000c003e403040c0f10b9981c0258401540780340074601300e460030111601280201c00e00b03124204107800801c010441a590b0442664007220181c1d401002c2040301d02806034020400305800341c04100780c600414504138621100500c05c1400d41c49170301020400b00d10441d03058224114880b05405000b1010a16500c00d0140710340120380070700340d5030fa03000905040604202ca140c0c440010703455041400e030300202550070304404543c01101c0d41c0c03000e20000754000d424119904590306500340340030303900e900308107941c3c10084800b501a4000c01c525030b601c50119407019502032401c1d030301500d848d908000514107501c42e030324110008000410100d6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 885481654 1250 885480404 885480413
    0x507080706020c1f0b09010e090307060203131403030406060504090b13030309020603090f0712120f0903060f0515030a050c04090c030203120a11030909070309211805030f0c0f0a03 79
    0x80c13445540b01051910360031020a40d15184052602510340200810b000e420240380a41c0d40b885508001400c654002c40040c210301d600c0746132105050b4012240060401040010741d40f2680100d6049414030b15000e80807446050030700c9640c0c0c2031507210078605d0603601ca040e0100f00d001d000c4d440c00ca08041d110b01c54080103031101da0107140a074610304024411625041465410000c41d0b400120702e800710107105401203061480c2840d1042c0036820100c4403501d03160000c0302c1e052041e0300044c04403410321021171524955036000c14440c2c2e12014044540b1001c0c0b1040540300d00d51300c4009000e55000440e04051071403e43d101481c039a00c41c0d02d82c4584c10b50b59601080c1010102070b0a440180404960001c1107904018604171807100e50b400ba51800d04074000252072850b01411100070142e41704510402c0004030314260035100c0355103114035540e10740f41170010710382c48506043ea007512050110000352410001820190441d8a402a10707980c200e02051004030250845050362040201a0000108 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 885482904 1250 885481654 885481693
    0x100908040905130c140a0909330507021b0f2b0507090c080906100b130b1602010908030a0e151209150f0c03040212160b0d0c0507080706020c 62
    0x4094160001074090354020420480f2803c80d03003c51015030900c584000020303441380309c0d00141c01030b05800a00044242c0c0c11004900322594882803243e20b080c080c081c2450300041c010301c418224014200d003d8140744103102000111180840d0031125101da0860001e03208413400c0040e4056040078182850180c5515140c0401644183c0a0079950389800d10b50650040380d00340d1000c0c00c03400030880e13418804442c055084607403080820350400803891042c451456000c0d84e00624107803000740d4440032410b81d1080c0c1d811003500d049001c944240713800501070741c0100598510342125144d0214612001c0c09010180c1006480312411180401021f001d0b800031f52070f40c2c1c1c05134142030020310031030404640046615102406c2003120b030a94004000540c4a084103c5e0340c000e0f810760781c0701d060314030917120300349082c0c3e5204545040d04203010000c81e15001000c080c240c0c00440a034284000c0c4088902a241407040c0400036121290400641003c61290b800074503840f4103c0e01242c401d8100450081000b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 885484154 1250 885482904 885482909
    0x220f02130e040203012f0c0c0a03111f0207230301060b1b15150f0405090f010f110708070c08010501060306090c0e062d120108100908040905130c 64
    0xc140d0404180001d6040921400b40c4c202e007500b1b02c41924000860440001070407031a0300c0415030100180c14120110107002c0c410301010017800c00f4944640b40d1806040740502440028040d10500f00050403003c41107044200c00000c6401800f00241000b849108401c04100584170000b0508282082d684092245030018151191241c4d110301d003039445580c2c9219942e1541080f03030700c071541400309000070200d481d41100041613100ca0a0711100045103103514070888032507005181c5001c00c881e01030003049034620744a580000304480020206042e00712904203140d0407a0410071700c100000102d401c001498040e00900d00082602d940e10030301801c1d108260400c000081d2580700c00c00c51111140140b0080100508000c0d0344070030408040349550240c40588103182000d20240745c0c8903281c01d82480700d0741c20700c905803594400704000c140b40700c00002e00c00c4045520441c0e02150592406219012105a000800d50f1400d89400030010203000042c20018040b800d21501800050f100d41d2130400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 885485404 1250 885484154 885484169
    0xa08030408041707060504051315060e0315091b0607080a03092108041b03020d1a010f06141308030711030c0105120c03042301050411220f0213 63
    0x50b190305002c4460782501030030420f03032081d0388401c03828420203401909440c03da55003603c01201044050008002410302203401d5100c4800d124400708401764000d4122051003016011182294642c0251011320724044036035007060b810440280c06801e80343c4070110005038000b0191f42c1004450780322a585640a515008042681c8031501400c02c1100c034400c1076048642c0ca8002c1c4800305111000c0d20303101000b0801810100622050846400c2441d15400a580c0140c0403090281003480c0010302161f05480e1100040305250000501c0410f1213085c5e000d5400f03540e9600140e0000f400e0540701500700702d07154203a91591040c08122140100050660385000b4021900c03504000030a050070f001500707401c05d041000400401d460820081c04140d0000403401541e40d40340c0e218104940717001000e006e60300400380900440c0c1c07c101015040f0070700031801107041084440c40d2104100501d081a0850801124842c2d140b01081c10140d005c1c540e4119012005460514007032010101003806400418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 885486654 1250 885485404 885485407
    0x603050601080703050c1e1e031803090a060c05430f12140a0b04110d1e0f17040f0801150b0309162408061e030a08030408 54
    0x251560b0710800c40c540152140c101001941010800004203114040c0710340b21030014884c109800b40401c400300d84034081054441c4602c98a070398080307c06a40709980314900742105480c9061001d0000c0304640021078010600180303689400425103107103407031703400c03c4e82e03940942c5242c416001a1103500c1c0d503d0841c2c002804403242d100007075a004440d1030500d84803800d207041d102441041500743d200c0c03096612140c1041d03583c0080e46000040e60004500e031003da80124210703c000c22002017101c1c0e02681c4520080c5001c401c8c040709020408514450103440784500e0035448269a0030549544060f07070284450f8050561181c54a1b001c004454400041c0540b000504004141040400c00c004d411440300910461003291001d207030f00381403070240e005503540c0000400c001403001c00c00c0c000c5070352081208a0034255680700001c400c03401c59030528408290501080c81c1c144c0704210b4188100d038010408107442180050b03040c2c444010311106501849101c202074045201000607500c0349100300100c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 885487904 1250 885486654 885486661
    0x1303030902041505041401060206130f120c020a12050613020d0f05030a120e0d031104090608070f0b0a120b060403050303160315030b010902092806022e090318060305 73
    0x105c2210001c100b0321040c1c601840041c41503d6012801541000f2030386600300c104e034050f050071440c94420f80c000610b9002038040c0c1c1c854054102e041040c0c0180200ca1004603a0b070b6603c0000c3c044803d61400900c00c0d00b10f180041e24501c0808005652140050101c803415001562581d84030030a04c9011b8503a5800890703e600c400d540051101c01902c1420001c0c0910341100f907a8954983c9078114101c1072540326501c00c002c50480e0b000342c500800348004103001982e40d4448058917403100d401455240220320b2004200b51300c0d2403084904120190342c0344044140c0a1002900800100c102e203680b0003070420001020480800140d401036100c407030440400300c040e0b2006001c917103942182d05595441100300b00041041d42c21518115903202c400540d644a40000059032568509501004015a441e040b9400e032600041c1c68180c640c29022580b030005030301070079111000030703801c9089140c0d03104021600001e4140c000c4032940e80300341000c020950b40000310500314541900400e00003070707484081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 885489154 1250 885487904 885487909
    0x1505070f06090b0903070201170c0909130b150603041103071508160f0c031d060d2316030f110708031b0a053c0c061b031303030902041505 61
    0x500344c02c488400300039460300c000e0b540041c0c000f006240f1000c90b5642c0c40800116200c0c00441100e020040080c480d540d1032400d00d204c00c0c00062001030030f48103150301400244500030200442140350b0002000c040c1180d65644d81d003e03141e9290143d494041c0600301d000030300c4001810f401c2c1584010307a22400388030710300000601081c07568480e80004020307100c203911101981208820113003a825103031000c0b400ba0100b0300042c20483d2103954a400040009a45107e1949a4050000c50385c4c03903100c401010502c5551034080e02401d54030725686509807804290701d94000d130b00a140102c080700002c01d80c3e81030241070300095004280242c941080010802c041003111480d20300c45036140001079405e0486d2404014841e0160303c40b800e880e07420080e848243c07100c480746222280b031003041011400304002e0600181c503810042c21109148134120100e05808400380044007800c240320031050035983c8180f0300400c132010085064041c5030703070f80320f80c00050b881d1030003080350400110410106080ca03000a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 885490404 1250 885489154 885489173
    0xc09030f010c08040f060204030c060f0324090c0e030304031208070504030c030605071e1d06161205130807050f1819180c03050607050309071505070f0609 68
    0x419403564500040508269004142c598020390000110072041c101c500c0c2540c001d120340e42000d48905038804d07002400760b40c40a890050384002c0e64050080000400d010301d6054088620712400450709102840500402d07030005040c0c007260315200031100d8003100480d0a541c4550401d030785048400503108103060b00030091682061552509031715141c9991904051440107000003061683c46001141c125441410144010050131060100c8401218009000d401180207100300301a82c00c2288447ca2070064203403440480c1c0da0007081c80d005443d507a4840300312704140d02c2800380b00703041c0014201c00e49440b8194014040610040800c2d40c100360800801407000031040e4413a03c0405403c0f00c009031048040350b0040b41181900070780b400c21000c0e0001078044682c200601824000d04102845595081d03001164000c40c1618920344500200716582d1004458190055002031010001c0070a0749101e0342e040703070192a0250408009583c0c0d19045183c4480c10384069484441032001d00c88000c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 885491654 1250 885490404 885490423
    0x7020a0c1403010627151d060f040b060316111207050c0906010e0d0c09020d02030f090607050703302418090c0e18060705040e0f1803030c0903 63
    0x1e58905285c0c0610b004061400d000c1c08030840b401d610750082480030f000c60715000002d0036800b1041c4084480c040e0446894980c12070310b10b8402c1160084000581c1014490160080c07005069649541d6943d1420243d0b000b06440c2c11b0104031091050400c40e41003030050300039114007405000da50b0040c40c10309a180101103240f66100e10f01107000c0c03205036a00440f40000032602542e54644111144c1005074003e0541d40c8239601ca24000610f200c4020000c0d4000c520407610140c2c3d140658580300402580c444007101c40c8408a00c040041c0c0300400d0060400e140960842c901031610381c818403d519110310100558184e60b291592504030900c0d95915a0b1907181215640c000206840d040e1010710440003021000a0282d480d404d60050281c004443c00284c8403c108584581c10aa0140c8680ca440780d5440200740c05458081100507120700102e50817242802c3c6289150b448483c003928100340058078000345a0301c90320001d00b82c0502440551722a51640c2074841d00c2c2e09601040c98200300401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 885492904 1250 885491654 885491669
    0x130e091212090123040f05070503010c030608150c12190f05090d021507030c0c08070507081b10030221072102040e0c07020109030c080304061103030601020a0b07020a0c14030106 78
    0x4c88a40c0b003c003080700c003940e015400c41c0700102e644003207081c05424420f060304026003550814825040a6030182c0101045680e100e04442c00c00c100c10324a601e00500c16108601505020040c03894445481c8018941041c41000241502080c40440b1422039200da0400b0b0b03896a115010804001e401780103c10b50b142881c00a8900312207150460b040d07040f07005080e0010b05a0310360200c111540b03e58a00c403c210f900c0134690303030790340107a05040e983c81d07090344101000c83c4141907a03c424254142d0807800120009803075190320203840401503005e9000489451a0110884401c0b102c1c1e0038207000b2140580043e454101000d56007a42114107128400500c0b50000c0c0100b008100c1da001d0150b036168080c42c00c01205454500a00c0100c1300d000e05580041e0000c1c42d009808960080044002c104860b42512207910400700f130f45e034480e100c2c00100c4905026812503c036103004900300300c55096020713440d4416135031070309000c3d92801010340103900881c03003e0a640d001c41c140da0030300344104006400311 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 885494154 1250 885492904 885492941
    0x30b0a091a1c020a09020d060b1e0f07020d11011b0c210b07050309060121030c0c05130e0c12070b070807060c020f1002130e0912120901 60
    0x6800c01c420705190005000c6000c1c9007600c00c8030100010071044031800581c000d0403400f82983e110700c0f030302c003a41020804600c02c9180ca10001007141e0420100c0790b11420713582d0704c03142c010700412100350300b030300079000b14103103440100300d50360050b0781e16564880c80c103120310301c482031440c0140f000400d07203280500402154486400e070a400f1600c40e003015800c682c045003c2c0c41c0101c05d0f068060200b400710042c001d0000104c07100344400035030444042d62280d03d15004a41d0640c2c2d0b00c0240030307220340c01e580340c0440034248020320001080c814101608503038000c54a480d082545c23500450340032995501c1d07156480755602619000b0403028002c0100042c1c04442500c00d4142010441d0303160f000398031514a202c10000780900030010302c501603402c0e0582010301088422004035000e5140c903d9600c82d00a58010308000840818035882911003020744d8000d1400c1c0f603030401440d03c848100192010183c1d100d10054004180090001440c0310b680742c001c0c00d600c600700700f44010309480030701c80300c044a401c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 885495404 1250 885494154 885494171
    0x909010810060b030132040c05030f07050a12050a110d1e0e0d05070512072109060e0607030912060b09090105060105070f06140115020d02030c030403030c02030f030a030b0a09 77
    0x6448000b026151a5142c10801006c0e004205400300e020280105800905001100360543c4d0403038081c51080c0c0400000a580b40c3d513203042112503121b05070030031000c00c00317820b1039150451107907001d0307588280f1011001440a12148850956800403401c428901f030300c41851005403100d407000f144070500f5004007488400d0604000315100c55940c2d80d52000c02101044007010b1003000c000306106941c1c0000901d03038402c0c03c0d003804400c92003200284d0b40381c0ca410b41d9030085000d02c1814904120384c0c00769141804018140100491a84026801c0d002c00c0b400e081c0c00304410f844250000700e030300d21803d03000410440d01c00501c44041d00c0103004c014980d241800308005c50740c0220031583c038168030000c900c490790141d25108004050044200c0c810031900741c008124907809030310350a22032a481e0200d8064071000f180807070360f034801c0074a2804590814001007002038025034a603010076100505849002001c5640286150450411400065100c2600350454184031880101a003a4041305001d00d20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 885496654 1250 885495404 885495419
    0x14070306021806032413020403080316080f061027090b06040806040308101d010e0a0209420a1209200f0a0902030a0b010806030d11030909010810060b0301 68
    0x16507541c0d800146417100e103a15582941c0380c40c00e917180f160b140207085407540d44a09244c2d19680044481501103548002d0708101039000300680d910400310100a0016a5100310600281c140c0322500340d421301481c2c48460321243c03401c100012000c145590806541894030020038141c9a05032141401010100800d0000300c01c081381450b4000d4041c20104480d440b017800e8803542c078006600102185244800c0350100d0602440f456040350203030817600c2c00c6034844180760000c0780300301d0300807036840075410b903c0c2560f43c01190f074103514101c405041c02e80d840024081c003c081c52050070100036000e00024030b41580d40c2e00305a140e004c0785864602041549101d41c0d440690007114491108401d100c070f80038240e1603407404c10981d00c41102403c1c0e9000f042c0d8818681029410076a07060800b50306100c04410b00354403410807240b15120040041400108418054400000031600000300c0e0100304501005038681340065030080c07a619000344840c0808541030011034009810203421071008100420011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 885497904 1250 885496654 885496681
    0xc040c1d090108030d0e121b06061203041a070602031e07140a030902030c0604090902040b040c050403020d0614071215060e060901030b0306040605010e07020c0d030503041407030602180603 83
    0x1001764800000788010750722a990304d00801039801d243d01c0c10b4000313420045401c24190030b00c560b84500e4115242d0380c407603904010202c0c445251100e002d50052008101c3c1e151150700d02d40d19030306131841c11031400303900b922040240d0340200c0c2c00064815070000d80c800d034012600d007010707448405440c180c0743c10035a0f00600c0300d9610810440b40200340c1c40d40608400e542d024001c09071076810041070560342d60b50300c0074840041d105c0141d050b44110f04e04041c00070380c1c0c10240900d140c040c11729500c143c5058255404c204100076515800d03115196240b001c11030b140090644603004107170313640b2170107000701d80c002640065070b42d215a040b4280084620401c080c980000141280100c105c0d0041c1c1c80e401d007500100c1c01800c86540c0079905105941c14002408090f52106043c0c4031001501c0707450b03a5802100707070b036101ca80310004c0d0740001c8003c2c02c45020034483d202950f0440d02c03481301b5155141b41c02078014a020360340c0e007056402e15400a181201e21800366610b1940b4401520000c4c00d6140c0f001d00403048 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 885499154 1250 885497904 885497917
    0xa1e0e1510080c0c0a0605010f23010f0c0503040914060f0109050f011205190c020303010311150d02120702060a0b030a2a0902130504020f0d0b030c040c1d09010803 72
    0x901c00301002180802d0f26050039607819a1101080b1901c000203400c20002425003882004202d040d145c40c041118003002160f4071020040d008000218022080115911032070b0590800c00c000340140c4d50400201c0600003440180f2140d500400c030102d01e1501c243c0214800303000144a510f40c1044c14000d640c000d8003980c202c40d01150b800c1085414400169001d41014050200c1c80c0e140508000d001a0a02e58401c04643e2241d801c0010750703140c00003641e42c1d100c20300010303200000c2c0403041c525501d89030040b03040d00503000d6501070802240d1254102a81c205a440541d424101004c21440950402280c3c0e80400f18010078040b62032814042902d8280404018092107444050701c04000c1c0714441c40b45a1350040000010410b6803001040c00942111711034011401c01944006417504c0d00d40203695000740103510103407510716080e407100010180943d400d6054021203807003a00039500d520840c40551007544507d5040325200300401102d40105e1100f41c0309280440060014031000400c6c1ca10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 885500404 1250 885499154 885499157
    0x106061e0c05010e030c0a0b010e07050d150911071412092b0c15020c15070606030611251a070c080a0f021b15090a1e0e1510 55
    0x1e88410904006015042c1c12446115511000944074282000002c0302078146010702005034840c0d8a5541280001078161420030016009100804c84070085600c0301c450618421007a070701044d178510701003042d030f01c400408000d00c01022074450b00b403210b0090300e41d49001081018103102c03c1c074840302e50418020101b4a90003202e000100d80d002040450303103204c894850a40c1e64204035503900d0450b2200001e8010080c1c0905071959982d2003900010320301c00c0c0940000c041c61090b052603540e47e080c41d04003510540d100f0751995000030200c0c00510a00410078640042d0a03502c01035064820880d01c140101c0d03060540c1c00e00b5040c00810a0803411504070412000784240070785510b00c08032a5031801c0c00014186001c0014076012194004001c001d14101580a5424800c102c2c3d10f18603030048094152600702003410345800b41d140130140282210340d4024015501c103a21200c05d080031003840b440980141e80407103024801d00030403001060340428003800700d10ba4940ca02c0003055170308207504441e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 885501654 1250 885500404 885500417
    0x91a01020111221e1502010c020604151d06011e030c12020a090e150f060307151403040f0204110a050d0f020f070303060e1317031807030609050106061e 67
    0x43c503000000340b1400051126070070400303004040c05040900c183c4c40e881904445080c1c2c48400f80e030380380180100e40000301e150b00500502e85d26511800302c60f0490101070107070581d071082c00350310450764540d0714201d682e0108000d01ca190b04001070007003142c0440b41401c822030b2000c07400700005120008910f003500c4940700300c4d00f004d035101e102113800d0102c075800c8200120b0034030f54840501c079800244060300b41c0c0d0310000095071b612a80c6581c0d15566080e20420303055080000c041c00421100ba610420803010342c500f10486030f00300d6800c0081c9070804c0c0d404848500c007100514041d813405002c2c80100c0340720f442c9070307914150318490090998440c00e4002103002da02e80450b02858007041d0705842000140b04401030795400241741c01002402c090150030042101d681c003240e49541d10000400640e0b50203d045480b0b9040040180400e81008010358504110794000048107582807251a00651044801040030b0f15585010b41c00d4404a0300044200418504640f0901e2504114510140620700300300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 885502904 1250 885501654 885501697
    0x715020114180325020a0906060e150d110c060703050f01120201031e0219020309030c0418140a061a01050405010f03110f070b13032a0c091a01020111 66
    0x46046006403a2001c1381e130710402021020148201e00078402140c400c503100020b558880c0c11083c12181c2a0050f000014281400c0e01d0345801c00e0507014003c04090480306007094044a05542541c01e00c050408400388007080b0103a01843c200030301600846103060a01c641e20704407050000819052141c46401d40404c2807060035039021fa840b2203c400e5061103080302c0c1c2410101e503000a5407141000e0a110250090541441303032010082d229400002000382030684210002c001c09090358413492103070040c040300a400000d0700d40450b000e4920780b08000d00303440d880a080c40700c04c840704003c010703144003130036200d0b4045685d0201c201c609961003401c2640b50303814540e0040f8000c1071744059840c0c46223000500d49140e98180c070b0107401c10511600c00045e6640e10310340a100010302980c4000e002c2908003120f60268030002d40c1741003209480080140ca040800d031519001d40000d44d1000308400ea603a01c80e003040d8cc445000002005070280024000044203000c000c4884c491811501030f00701210103070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 885504154 1250 885502904 885502951
    0x50604021e0a030219050702190e0a0911040207062717030405010f06140f0103020f03131406071d030319110c1201060501020c0117010e22050715020114 67
    0x141c44036107000c0e180307901d01e0310001d00b17001c0c1c5280e0141906900c121100505110900702801c1c86100350390075106410081e4450804040151000310b40c110b0300c0440078200c401058442e0300c0505106400b030741020580c02c101090503118214025200c015814208014101154030001100041158108065601d5503181004c074010a440700c0030031140b80c2086000207241f0a001d2110b01a240d04131225151f02e480c43d0015000c034810300c0d045144900f018400510401c0cac6440032070344418001d0540d50f80b06910480386038105441107502d80041403070242026920031803c162102c007210150f009519240b80b00d03020500c000c100c5a02041082080d280301c1e0380e400c10038004070560070000303080b1000808581032114064071880c0a5a40140714010b0301c070031158031410851350320300204113000700d03140d00b05005540c0302500103010714030f2290700044031185004042c0e0b00100d07090048000d40b0a4a09200b42c030400e01c0d10f0400d10900b107a04060000309029286450309070000d01404030708640c1201d0f00ca0307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 885505404 1250 885504154 885504157
    0x3030b03060f07080c040e3c1909120305010807090b010c320f0105060405011a03040302011404080703090b3f2a0f0406050a090e0a0f050604021e0a0302 67
    0x220448800e000740900c80100761359144034480040381004c09681c1030f081006807004628030b030034510001280b031010960220710600c001c2d284005119011602c0400c0b0b13250340000c1d12400e441000081c3d4dd840041101000921034007005d004400000d2025072045000204894ac0e81b0f04050701c8410f81c440d44000102d54021400c0000003101c116948031401201501e480c1d0545040c901e007a9420302000400602e02481024141c1b00b102c1010700504800041450403504001d10840640d035071072403940c0c8480c00d1100c90500c00e40c800d600cbe045e941c00261034024204003541c1d1000300c401d0024019001c2248030700d908508a44414654408072406504e008100d4400d410041a80444c5800510515410b51241001c8129242d000c40288a00511a0801d148542c1a805440d42014001445120301c06c41c001c0c44068420724148410325110200009010015258401610354a018001d04c65110307014146e03100e8002c50b403c6007400f2118203c0000e02400c601642080d003000035103c1301da18000c2c2d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 885506654 1250 885505404 885505409
    0x40509060d050d030c020705090103020a15030f020d0603050c22020d09060507030615051216030b12160e090606090423160b0705150a02070501020c070303030b03060f07080c04 77
    0xb000c840141842040c003400404d00900040014002c480c00440d05040c0b000d010b03030480e54094085907525180004034000d2940f0324a48100b01070303c801d041a00580540054004400160400201d207072840c90082d103030041600c806401810030700848402032164501c108400701146e036016070f8818203240706800900244000400d01444c1030240601260f16911502c282c0d0108404598041c1c809001034a0500803030716a222860b410200281d03096032b00e14140440c0c09018200405c1c007030035550010315031400d0301c2507140c0a9071264842d940c0720b403006880715005100c2c2d0381c01010329041c100c15203034846030300404d2607000740c6c05040860208000400003001f6040c42c0801c900042e00f40c41d40e05034070b40325101a0031020340080c0707001141e071000710b004031640e0301ea01030004c0400c400308a8104460400003041c04880d10360920820000c18428002089101030314070250800358250300d0080c0458801c0d8102c107001c1c0c0d2050781040107034440b02e07440a402c010a4104019542d42d6141d0010b5140306a8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 885507904 1250 885506654 885506663
    0x603141b16080f0408060c07050a03050a090e0a14010501091809050c13061a03062d0a08070906061b030c020a05041406040e010c09030b06031e030c01110f040509060d 73
    0x895490302810301004c0d0060345d640030242e841c0c540b22180d015a8901070004060140c0e0400c40314100000e000d0401402511a0f40c1012082d40307644030000d07016140125448103110351a2650591200031300e0a5480c003426003400d01c0c88005081c18041c400400d030035100d040781641c2d210000740c1400420403410014180060515035400c0c41d100e948009400d0f148144510302c0307140210366080c00116000d6031310807100a0400303852080320421005603c0085a561164041c1c4d000100303400da102d8200700c1c0c01800041000300038003071030480c280007140c40d84e5020100b04a00c102c074007052640700300c01a07088140c05140c01c1d20186958000500c0fa00590352007658414a0079042c07002418502580a120341c0c0102c82c1040800003200d000f44c20790750b9141002c070028100d9101400040d40e01b03040e642d040100a01150710245404812141000802c1c42600c4a42d10204003c0c0c00d10030240904803200c0108400c960501901e9200c9546030301030f41c002d16128001460000c1c96544401c41078419060b0030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 885509154 1250 885507904 885507907
    0x1518030406180e0112150603050102130302120601051f05090a09090b0612060601030f0b030a0b09100e0c060d09020306071d040b0a03031b12090603141b1608 69
    0x450034050592501400b40c508032005035040000c5521402240b5812208078608810f0720320100e075110f012046542c0c024040c0c00c0e40e540750200202d1024406007075034200c00d81068055a0070b500412600c012b4480600c041d5034000c0d401440242c07034408a220480b101d81d025146505080001030b0b4042c024000580d802c4403009400048088003900185480d50207100304120365141e1314240043c3c0801550405900e03440000482c2055200350b002c8444200c070b0200000c2c4520b81500068140385907203000b0b868180a00c3c0034400152400e0010250300b20a110003000b013500000c051503200d00401603803620503039021826542035402e940044040c164010141c400034a40400c1c043d00c6032006400c0c180c917100354480300e01080d00749440345034800d6030300810085107145076580880d50142c44401580c0d1840c0340301070100004008140780380103800f42c1d441d04100c59046c840000d040301d40c544031443d140311841060040000b4116150b44149039140c0c4810f0340ca50304040c00c2404031080400050a8020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 885510404 1250 885509154 885509159
    0x80f0721031a120a111809011a100e0d03050705031201150905010e1011060a02090405310309081504120e0102030d360210090815180304 60
    0x103040d0301800a0b401c82d49040c00807030b080881803000d0034494030560040350744140c140101042c0c00c803e40b201203940090402e105008200b0b0f00c940e40f140140c031a40030b0360b91240340d01e001c0c0d112019410f10034410180d503440700035480400c00802920000750800d00801000561000b0b1500c03075001c07141c40c0da40043c2160307540c0202ca4000c400211092103201e40c0881d07607500b06003101d07100d0309512080fa18140e65020000e8814810040f044201180000c00c0c08071031039401d4104002408610f03c94400e1020050311910710307505000564800400c180310060312420341100000ca46001d00c1d007000d40c0c0b845100c0d44054203140564201d18290080220361055401e6091070022001405125520074500c01070003400b80402500d1b0840c2000705140541c00602172044244156070055066484240d891039028a580c01f04550f0200803440b40d1301d450030002d220000f942810082a541c400c0c440c5003042d216407a01403001d8903407900030717503102d21680030001282d0b00c2034130701d6060b6503000b01c140d0a403651680d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 885511654 1250 885510404 885510407
    0x60810030f112d030d050a0e12120c06010e010b0f09011416030e0915010c0602070c030b010501081005100c0c17060f01090635011a0f04050103080f0721 67
    0x194034005400002204221001c1c0504010980c10081010786d280e207410b0811200d420303214000307240788103a0030031000584409800000c0042da41d0400d2903618503035032100342409540c1840300c140c00040100c00003100400400080d50f0840d080c610360060300503207a8050000480340381035031420047e07801c0710100e5410000441c100c3c3d01260f10340300707407030790003411031180c0500644441c103c8007a11060039428070201d66502500c81c8041071480313148010310b0040c960341c800001d00c15a40040d2500281000140010b58101e4003281e041351500c01e510300182c0c50140002c868800350f6141c0020044400c00d4503042208079080348001c0d0950f007180c0e100c0c100102d4856950303082c08039280c10038000c20f480000f81060052140e40c05a40e811816010014404440ca04055050303844801c2c4107095080503000146003803042d4642141c500100381c844280b4401009a49444003034400e1041d442c02e0010400504940b0407180c0020615000301d84492040c1418041005584580d4080142c0400040c1c480d9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 885512904 1250 885511654 885511699
    0x204090b01081504080405041e06030b07030e19030e0a0e090c18090d0e0a0b0c01051005060a02060f040f080f0702180c03271b0406060810030f11 64
    0x1d0303240714203d50f02c1d107031084142050341000341c6010300031500400c018810350802d90443c5095001c40018901d0010746c084112085629650040d60701110034000c0c8041c981d85401007142c002030100080240307400c44085150820088240142444070324a9100003586441070030304000e0030f41008400d0149400110035031a01d111042c480c1c4520895195110a840e070645d510303014110300402410001214107041c1c0307a85400d040c01d00d900643c3c0030340c00108121a0070062042c280101c1c0049001c1c01c110546440400d92034009a00c5002c061260141265000421070352100c0102004c04132920f880c14401c1c0309000302a40603011200000390001006007040081441500c00d035110b00f1f8040404110483c0b02c1d034181e8480b40325200400216a9a511903d0503051100400c001c02511400117200c4a207028010443c3c11141d20251301200788514051080400425482c20829810b1620a140610384a04e900004003c00d02208040c07003880a003d502004000c00a001d20003002c040c0c00c80032548 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 885514154 1250 885512904 885512909
    0xb0f040603140105060105030103230109080409090308091c030203100e01060f09050405130209041506080a210e0118030b0f190603032c090711060702070302030a06020d02070204090b01 81
    0x80c0d800c200c0405d88a500c106c0c11039040360342080e880540c01c8066164072009584603417443c0b40c0d564039100800c0c042140c8070000e200900c46440002070b465007610700644035050041072022150404c4e0300084440004050400810301507203030040c0d90ba651120b443c0306a0403903030090844080d4803400441e1460b0040b5510080c0c0f8400d0700d80b0525542e03503c08110075901c08842200c840f038040780510005041038004d180d041445134400ba9040500d1410704011140c0f02d50003928540e000034020405c3c0043e01080542c070383c4c2c4a440c1402d0380c600d0710601a0040031211090ba04006c10039480c1000f41240b01d4054003d1980810309003240e081c440d4018100000548402480b081034285040c0c002d1028401c800c102c1c2c3d81a01c3d041c21014881c1a5a0b860007109002080004480c251140b02c590f0342e50b405500c03591107074441965062405058924162004003100195440400244056980011203050032a401100566103030b5880c507082000e802404030080d00170341400507250400c13070304140c0d0070305 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 885515404 1250 885514154 885514193
    0x30203090a21080708090306090c12030c0a08130b030709090c0c3309062a0806220e1506040b090f06030c03030c1b0109030305030a0b0f040603 63
    0x6440728000307960702c8410600c40c0c20030440080b41100040c5000040c2c50020f0080b0300341c074200010400801d08250045900241c503400108040003d8a80341005800c1440a4070085040000c980b1040b075469540c280007400c201c4010548568250001180401400034080031a03200d0030501805031201085016011440b41018045007640b803040008042150b00f0030250b09135000422107801d45076014080c902a002c2020013100c04001050003012001c40c0315080c0011407a650b0002c2d00000b5a40d000303a8004900d00d10341c00f0010390780c041c6505400140858403407460210072042051160841c0b220782c12414200200130b00000d5001c24003100440058026000c55500e074420881100c6810200325801100803020801c114495030031581e10a40203812981d203048905e001904c0c5030040240880542d0000a0314000e030300202a80c3c8020340400e09006444a085580103840b070b020081075a03031000d55079025080665540080d030400042c01400402c00544c0300d00f44109220081c0c1034604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 885516654 1250 885515404 885515419
    0x2409080706150506070b16030f060311040b0301060501021c021011091807020a11030a08070807120305070c060b011808210405010903030c0f02041b08070e03330403020309 75
    0x40c3d5081803800c42d685030380c1c00305e00e180e1141c2d03034182580e65030401c00c00c0000030035646141403c4006c92030300c0ba02000e140200b514080320303004002008160707401d00031071901990501d80b040103266000512440085540141e0300c0400710510340883c0b903d0000f505e000102810009074101090b020701c0100f41c1003905a03982d00cc40b40102d4603c0c01c0303468094568900503030080e0380c1013010a010319003200400038018181e0304500c0700d58071500300395003140506031800384001480d2000c00501420514080a250400b4807d03843d0507500a0303e402100c1c840503000b25181c47d80d50711320340e21862228041d66014902044d00e541c441000d81d0703555003500655070400d801c004821082c401000144d8085403030507541c80000900315035003111280303403c1c40201c4030b0401c90424140165124000e00c000101700e00400121f649003034100501401020300700c10180300c0d1840c0a4092501c0200c0c16035480301d1840b408030b038a00400c400c880c549240f4031204128103102d0030705000405d94040010803e02c5c00849894 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 885517904 1250 885516654 885516659
    0x605030601030f05010f0510051207051c05060907141902061006021f0e071a07030f2d0909020d060f05010f090e1012060b130207240908070615 63
    0x3c03007181da081c020f01244c018003040400c000d26200c41e4002090106141035420710301e070f240c2106007240041c2d503100046503020440d0019004803400c0c6c0240181d04c05d10500950402d0004901c0c4000054842d070100920b20f00707034114200040007141d03001c0c90754840031502c101c26981d000b512000c05449007115400c3c100b4002910600c00a841d078034803614908003490080380c9034000700007003c00c201400c03801d0090f01d00003e000000c4100341d00034a64070b0050135591724070620307004044030080d02e440c1c1d0601002c4500000c16502c00301500c0c0880389005041e4444c4c0d0b031482d4003950103029951000f01c2040c0001212504119150042400c80b80035001c1ca4048503110340054031016414516036000614a80c4200401c1844081ba25002811812034030390054030b030b480ea241d00c074000e00c82c280d41690f281e0707211800505054652403080c404100c2c0440c14007600d030741c82204c51854030404d8040c0289452041d10003a180c1d078895840c059010003450340d148028034109020301001e20039200200c5410000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 885519154 1250 885517904 885517931
    0x6090b090f0c06070c170a030801150206041218090e07051014030601180e09101b050702031203090f190c260f030405030f07030f20030106060503060103 67
    0x800510940c40903103201a078541c01c1c4009600035240c141d520b07070b1401c5c40010b590709052108503550980c0c04054403446200b42006402003070184d01c8908010398940c450501e50ba40801d0305d07900160300000400e00d01948030001c40d005060242c1040303c90300c6508000070410380d254032584059459501341e40c480356a41c400c112150321905440030125080084201d0809074050007141e002c001418002034102590002240310b42e00360f00300512072a810820711641380304c200b2100310002c0317001d90240040c03003064141d80d07424540004200240040462002c08555040c410b0704001c090a4510544034038016020f1644d446504044034024003503031031584900c4085a42d0101c50036080705c44c60403000d01e042d10310200301c801c5079900c00100000c00c072140c1000038140424000000942c00079505d4905110416007081c1d0203a008200c25803100004100252004641c4038280760007548051803061858070828500c1d41c8100719603032552901801041841d00f0001841c0144420303601048400d142c21a03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 885520404 1250 885519154 885519163
    0x6070f05011e0f0c020607080928031b050c10090b0a020a0c1d060616020d080307030e0303042006160c230d2003010501090509061e070c020105040e0406090b09 70
    0x13a00c00107070408000034811901590b4100d810602c090211407965055a9030070f1503001c1a00101a0701c0e8001e00544001c2c035501c5461965070004060b02c85c10650010f98540e551200804100c5015141e5220024502401807003140014078200c02d07050390341c10b043d81d070094595002003401c564820300108041040400002c0380c94140404050541c03c989680080201ca42c015400c40a5407001e1044c10701c0068944032060700038988918290364607402d1411014050362800c419030841a0b00600411000c90840f945031000d1515404010341586c08940101c2c0451041e00c0306800d200c22400c42100c108810f06040200703c80110b010541007080003100403405603160030891f5886040c8200c46400b14891180c2103d000501d42c1408480300182d03808603003980d40c2640403445180e5903200300101034038140321465214016480041c02180b40595034100300402602c00700070030030040d082104590207142101e0103010309144001c25031501c0e2900c00b02910240c1003c9070007996102c0401d440f0400000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 885521654 1250 885520404 885520421
    0x7210e0f0f1227060403060c0801080f010c0c110d020a0e010e06040509030a11030d0e070f0b0a120506011803210f02070902182e051806070f05011e0f 66
    0x849009a91007401030000c0f90b0b400b01c02e51681c0035000f08400400241c0501c00c05a44410940720310402e98500742869050880b1501fa116007079050203503914600354060703188803221398004058200b104100b8080fa4a01140640003900070303070862030100d41556800c40c80d070304841521050411039a82c4000744400d4171000c0c1d40c201881d500c24071100302200d0042c443d9900c114200030440b03061204104070740003526010b5007030403019040860f082c803d100c0c007034849001404030760400b6890401d0300480207003204401041d800400344e5a81c049019a8440c0d1980010340c24400c00e031440c2c054590509142d400409100c4c0ea01c80c2401e0410f60100034003842c040b4140c403400c0d0300a04407041c6807260203030195000445802d03603c05c280c030700c0011554610808007414680c0001c0d00140014a104102304036020f03090032030a2240c28400118504180e00052200f6841560016162581440e1820300000d01c000010007550800101d128506500f00082013001c49004081c0f01750301044810508950851 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 885522904 1250 885521654 885521677
    0x50901240323150301051503010e120405060c01020d0c050c0c01020d080703020c070b040608100b07050309010e0d0605070f09050604180b031603050106050405090607210e0f0f12 78
    0x4801c942e50039180b140080303500c200d81088882001c944100020f0031150101c1e2060143c052014a9000600f000d20420007522001c0000f414174126004071031420780114801c007031048600044c640801c41007901510f0700d01d0200c40c428041d040d9004009840764016074080c0440748030301c00248019610024040c803c90340e054070b481007161034001c3d00310065844018810501e114071100000c0700d1213288021f100800d071340c1e0382d58852420100108000307441a98030000511b50140540400f08402000f00da8003107109081c280e141d01c4601c004501d515128003c0602458035100407c048950018180034042149943c1c40c00100d031198200005801103000790510100000c01840d95400190f1044400c4c910040486240011024041c0700141280d002190107035110001045542428054503401c00e01c0040070344220300d04000001d140341c2c3c2e10b030360f001140c1c1072880340b00000d6645c0354080d1f030350030f0000e20590f6265078030242c0f001d96500e006042c001040c4034843c00c80d0103d8110505807408500c0c003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 885524154 1250 885522904 885522941
    0x150a0c0308101a031e040c0e040213140601140c060a1a0d0c050102070501032a09260c09010e040807051608100b010e01051608040509012403 62
    0x103850480300c10500a16180c0c98148280c00400d00102070002d00d11903100b034807445607030f85c40c0220040040d0a0030f144c0c420901441c1c5030600000803080003000b02030740d0741c1c903c0e80c042c40e80c1c46000261074a926444074210302e0707250120207a01c4101002c1d64510516003a01c0b0b20740c02070100482403040c0d10070005c001c85550406008908071b02c1054000c122100d610007c40ca20441401000a00c0d1905120045548150902d4100500d50b0140920b00c02003800342410008031480c040410504c0004040c6040311150b0103c807540424013803d04040030b010301c24405803d0700f41880d05400c0c81e00d55440d194074988220000700d0b400c0e25280c200d1074140ca081e04410403450b103442e41c43c040ea0384c000c5841103170329003d480405000c055020000f07800900d0010003d04d042e1030030202d600304a070199481d4504001e90910070140c941d8000c0c044030802500041200d5041c0f105050603c003e00850b0001d65000c0303150400003400c0302c1c003410880300c6007002c0034000100c0400310b0015800ca030100081c03618400007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 885525404 1250 885524154 885524177
    0xc0204020304060f02030f07020f0a080307120e0f030403020f0603100506030910050406050106110f0309061804050c040f0821090102031b0706021b0a0302220515150a 73
    0x400340c0140d50401e20440c4049803e07500c1111000c1a03030400c8821004160403542080401d40d8100202c941102401c000340c80f04030b1194075007040c00d01c40240680144008a8040010f000c2c0c15440381c0e0170000c0003002e5032819080c040d10503850b6072003413100b80d00c50041a001c43c1c030140b1300344003128000d0800c03540d802d1032203280c0000c0c05003580000b00b0010940c041d100c20b4229002090040e50b201c3c0703101e07283c0020158181a40500034840200e89120702c4d51255044e07422a5500004031401100c040701e5080d1144288040b01d001d2010381050550014180402d00440b203600d103000d44140c0304c52005601c40c00d5141c80300300395104107080c07080348170300c1000607011120202507004000008040c030550349003500e0314044104040e59000d0790300c0954400d0500b000102c0d030511081c0000070342200e6294200c0c041500061090185001c0139109101100f49107441280d5650320004501d4100f60500141c034112080c41c800c840040c02c900c0c0100d44004684070b003200d04070110760002846440b0004c0c08034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 885526654 1250 885525404 885525409
    0x30602180109300b130c120c050411070203030d02040e0c181e03030304050d030b030f06160c12120b0108070f0815032a010306030c1a091f08090c010c02 67
    0x7882c0000c0350b0542d0301082250404281020251480382da01c8110a10101e80c043c1b030004002071556101d190b071408404210400900e450711600304940c1c0460300491800c03c05119252140301d1088003d40c580300008810009100d0303600540b08407480d607041c840056039016064a100c2c0f09a044034601d22648001c41282450501e0080d04242504442040414601b90101c3c0c6540d00580e070035255036008911a100d00d95050007801ca2010054001e4031101145e80401603a6540c09048035500c1074447e5030450240c4d104107070700d003002900401250402d00c1405009840c0b4032002d10120788082c1800886603965014481180c00f410700c03541e500201d14030454007202c988070050421490b2592400c2040219a402c006001022002100c1070004030a000e140944003100460304506041c1070010800200d02d440206400702d5941543d0603104480c4c0540b0101c1c5481034040700c030340c0400480c02c0801c0c007404c0b0300c8025042c14826203c034080c80c4c40d207036007035581c0d510700c00070300303400200445408401030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 885527904 1250 885526654 885526709
    0x4050702070914091b010c1506090603030e040510121112060103030f020d03140c0309122b09050c0d110405010303090603200901030218210d0804120507020d020a030602180109 77
    0x200301e000e500252790fa0b01c80800700c4c1600d02c15403050b80046c9012000701c0081c03030140b18144d0400380c0c800c040d1180628001c0e40300500100000d000c1c1015001c04022001c03521004446031005038030100b81c0794030707684070729001d0704800418481e50f005108071054900c1c20b40c040e03c14504a2107139001250000e6035120402403680e840100400b00f1f50141101e00030741742c0b0140014080f9140548922420b1501c9074106166460721154001c00250800c0c4149011450201d000c8030b0000302611250200e5041c2c2c1888441e403c00121407070381143c83c0100000500d60312244400c161500da030390a000005a03c1662100c040e108079081c0e104200401c0b08180c5513020b50b00030040100c801e908408920f42c14000140c0b4214400550f05007150301060084400e24140007178806810181130100143c1426218445580c1517a01004240100015480c0566940f110f00c94032241e401841c40c6416500e07440c2c420080d40090248450441c400d1a02e0b085941c0241a034074140c0303d90286c4259107114420800401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 885529154 1250 885527904 885527933
    0x31a3102010e040606050c160f030206160c0e060405131101050318120a03060b0a080105010c0212011e0e0c010e040203220c08061308030604050702070914091b010c 72
    0x188507942c0c22100041d12039002d100000d00290720303510b07141c134455441e075130510325022850294000d12000500c00d440072883d8410a881c1c0566015407118400a4880380041900401808038289540b000070720f1071601e4150744c4156003c0d90244100e40710480c5505074401c840c0801040480004141c8500303510441c080c6520604c45004500d00442c04850582043d407030480781c8081c81e4000680c1c041441d098081c6400500707010700114607142c040840101800300601410707040001c80100d020a564504141450090f1039900801925000d041d20152500c1d00c0780207541c000381040b0000c80c01c55004107640c0c80040068546600300782c04502040029800144000b44403005032032a0501ca840d00b540c000304140c840c140d204100c0d41850b4804d03140c4100141000f064040c030307271403c0d80000c00000c01d49402141c151408100b40d141c001c02607003005032603049109458600042c17442e4080440f0581e030b005a0b100c00c140c2c1c0b864141d05588002c21404c80f020540800c0c02401d510f0300044d444c1c0e084188 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 885530404 1250 885529154 885529157
    0x2090403032021010e07050409020903070302040c020d030f0612112106190513031b17041404021905030703060503060f19090302120702030a0c031a310201 68
    0x41405018900650340026186074540300450f004140c41c082d03107024842c09440d18199004007407400030b400512034841d500624184540119200307800fa00c00700400b40c091036000701700381311202490034003c1d514000f10103003400090410000c40c0c0d9088561107a00f054410202102c0381d251025140c00c6028112100d41d15000780c0c5041160b180050084e5542c8480001540500010f05180e0440c0d1800350842020107641407404c3d043c0521480340b03150480040fa4107003005186072035401032181c03c07281511405860a081c0d88050030031015800b00600540e00c4201c00420600443c0e400d000481c095a421000521401c13000082a1030003000995032004445c50003090705621000480d0610b40300382d82c0203001103d00e400f4404001d840015484c070010702c20004100343c031800c0d10000d503112241c8440e0000300300001140c0c41903440a004622400c1d400c01c04180c191980e0780340c07800c17500d44803050701c6102c1003101d030104a0803080c4114440400c40602d4804412608000c201001a1354a180403070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 885531654 1250 885530404 885530441
    0x60f01120c1205010b03180606090114031608010608070f140f06192001090b070f030b0a0b071202061506030c04050319020a0b04180c03022a0d03090209040303 70
    0xa800c0b40c9009040c0a840007a00158613424110384050768403080341801c000a030400c40400006403114161030341140d601c5041e03400d007860560082410407480a60200c0e0842c5180808211000c054202c0000c0701c101d1812526038560302c44d03040399080164013450744108044032004181e40792008070180d030345400420091500c511103581c80202807003c002e81c408119210040c505681c060400d0f0b502c1130407064001c0c441010107995048094800410b1401840400201c9503d40b5219034005910500e0140c2601d0045031510405032407508010400c8404c05001e01c0210304062022030b090307010312207040c0c1c0340200a229404202c11034000a140d15501c250610001540e0b51b03080044031205d801c030b011020031814160041c0b00c1c41101a810030a1501c0c0108030030132480310004886c64000709074980c0000e007200840c2c4210068030902d0003901310340c80380d807807003020b0064290070508810104030700301c0e81039103103d420507025070f54166006540060400d000901181c042e80000f4007411881c281d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 885532904 1250 885531654 885531677
    0x708120d0e070e010f0608060402040303020d0818150103050127140a020402030103060e1b0d02130e0a0b0f130305390a030305060306060a1a04030204020406080708060f01120c 77
    0x1403143d00f800da00444101c42c41c14002c0003960f42008545d500487e0544066103024203586010756600e95100040e0300b01310481001582540141018840c8d12a045c01a1105500c1454024a0400c02808140e840e546000d01c1b5681d56801c003180030110000171618a10710210a895030500440d030039000e04014020482c01000603a0346100440c0650b01c1410700055810f5882c6001e440c00003004200302145203103504c00450303507607412643c8105c194103c0300202c044514000140150040308000015445040e91240410030b40000342c6100cac0c0a000410701d86035445980384084140c0e40301000e8003060081141803200660451301c400c10207241510070000444524540485810003079842225400c0304c0800400c25a150080b90b4012008800a105608007080080c0900e803040c459400f00b00c10580c1e4006c034041140f03090b82c0045800500071500d4030f0743c2c1c0300041e1000c4030454a0314009240c080020741207182114040044031010395500751103910f0360741103900070030048903c0c0c401e100451415 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 885534154 1250 885532904 885532919
    0x602070e1f1503150620011e090311011a01120b0a06030c020c01080402130e1f02040e01051c030e150706020c070e0f0f07200106080708120d0e07 64
    0x780082400d80000c240081e030b4504010200c0d1411903080c40c815031501c20400c4110743c08007001c0c18646e10982c1407a000d1000c800d4072801000842d0000c05581d5038540d640c50701e0001c603400540c10724080e48132980880f400807851802c80300402e07004078942c80074080c0300d01d140d440f41c0c14003061626039000c0040c2c0c840001000a1488401c1e6001c1000241c9520008181d00e905001988410400382050795090816074001003070440c62052488003e5a140c0100c0c01421080100400d4800300100031682c0c004202d24400107507006000d480611180d41d0000107540c10301901c4031041c8980580c0700b14603d02c25550881d03141451a840551156044040018900601c001849194400e40005035a5040e21405506041d0350764000c2c4040074520b0100901d002d0801c050075446401003007529110341d291a0207486a0f2014100b42c0c0c040703404059842d00801055000c00c0c15108a0301c11a500643d8410784c540d981d122400d14103020342c07002d03c0000c4804503550441c0c4405401802a1000e084c0c85030390 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 885535404 1250 885534154 885534211
    0x1205040c032307090e030729010f1d0c03040201121b0816090303021209040908070506060108360a05060f0a0e0d0c110d0b0a0204060e0a0602070e 64
    0x10180002400b40031016415442041040010401d0b481c0a02c1600f0740092055124020440b000c0c00500107221080340001d80300d906004140c04202103506196190f1075180a402e4241c00344100c40c0c0c05241648a0301c0801160b0b5901c01c0006441c030924550b12940112028070f602c5441e28461519520142c161064480101111804075903941c3c0040c0f5007003003640074007494180340500b401400c403001e2010070390115000c011020002d0781caa030784031051000314000b001040b2018003984000320b800300812401103100c80c080c0c03000b40d88103016a00c0b400041c0941050405000b0301d034441a504020101d02c0700c000000525417503600fa0f80550620b40c56480c20700c5c4089072105021000c074010030403a1504d9108030482c841c00c074001040c0c0300300ca4403c040d141c2c0000860107400555012040420350703a61102c050003240e400510203c8500307208034104040c0d040350042c4408110055014002420014110000c5803a00e034000c00d03150385891010501c1c10405012183d0b03400c1040d0509030540403000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 885536654 1250 885535404 885535433
    0xa03050f0f010605090c0403260d020a030b220b0406090c0302040f0b03090a03051b01060308041a281b1209051f03050c04120b071407031205040c03 65
    0x5000e06040700c4403107401401c60b5015041644501c0402c42407107207100c03168003900c056075840f030500380021042c055000f44603179800700040c0700480005042a0f0a44058010b84207032012900c1c20300c1251045010000c045400401602c0c00420003a000100540c10750850081e84001400002d090390b210803c00d0242c542c411001d4000c40d030001707400c001102010821074001c2455144041c10b50038400041e944400d01010058200100402c4000c528080c0c45101034120804c07000801c80c10703a4a15004e801900144141c0c000b00c0300b84200410b03040706d032008a035183d90700e50b5025081c541c144400044034100c84104103040102c01b0041c0c0200e41307030455648007030078050316a61110340707a4850000d2a2440c1350300b1007802920340c24801c9201000003ca070300d0040942c3c1c10b000c10346a40d07020144074a4080c81e0b20034100122044800d6040c4506c00900714083c240f030b951070280c20458400b5400042c85010750003030000b0342d865110340030803007264081608540f01300404e0040ca566034071041200c00450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 885537904 1250 885536654 885536683
    0x1020304080403020a0509070806060a09052e03020f0904020705010b0909010209210a020409050c151309020708041e09020d140f061008130506090a060b150a0e0a0305 73
    0x30b0500543c501400e42c80001c0100321100c0050785030503031000f016048060030441c081c02c4041880c1d0084d5010b0314001004c0d102c090915030524141441221040c681d0082c003412101c034180c10820158030900844603949190641c0c249008900424840250b000040070341f500e543e0340c4590142a65103601c5280a805c0510000d43c031400d142e4100211010316101c40803800540d0086100c1c040d2001c181c5c00c100ca50100e5000802d0040da04010f4140368180200c654000320f04601d90340c69596090140c4000b80051042075003e5845403120b02c124402c000000e0002001803008002c40c885880e9800c20250086007807010560780c5508180a0341c02204011002c1a150b403001c50202c640320f800154400c0015071107001c5418000d021a5207041070000b40000c0080d604009a1902025449015003d5100b03048900c24034002e00140d44448820350b04507200c0341060380320b07045c500d0244c6010038182d16450724145820701c0f000c0203550f8890703456a841d070021491240000891401e100c0d81510540c0c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 885539154 1250 885537904 885537907
    0xc120312130605070e0f0f1302030a0f060b0405010c0b092b1b020f0616050a03021c0305040803060616020909010605010908030c03070b0402120a2102063102030102030408 75
    0x10b140803070a4a4004240c030041103801c0b1146003990742c0710078040641a5066034401e0502d2901400306861040c41c140b6050098000014008190700170f500c5a50302c0310745c0340c1041102c141c5400481c0c2203403046129103400034074000c0684000c42c0081c1502074102a0200458006080343c04044000002e48940856142d008800d4611015004021104040a40c0403441002c9440c1c0c0d0020354a54080c1000c20b010341c00c040303021011014070f6906a1403254100d808c60b00d400b042494025551070030000a0b04180c0c00c81404214040d003e40203c0e07005550140055040d991070341c041c44600e070044111018440320092210000da04c07000c0986010f110700f070340003047c480e00740b10001d414003850f980700c0c000035030080101d18850700012043e11007496211800c01503075115400024004a04820300d0b2106001c0c0183d840700300309121004009070b108140d03502c924804089801e03a00c0300d42c1242c60108400484603083d170342041d80c07440e440604841c582c517540e5401850b00441c0c00c903001298112802d510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 885540404 1250 885539154 885539191
    0x5100203091c030f1407120b15120108070b0f04050904032d021e030d0f0b19080c09012102062b0b040b01120506150a03091103060106020c120312 64
    0x19602800e54212124046610170342841000100040c40740d4400b50364055880240132601d60714103420708495643c3c401c040e40c90300d000710300c400c054072020300c1004807a22880c400010703110850350030f65500c04110b10106040030b1a0906110711035074014012030410112001d190075900012100c01005a00588801030134034050101a02c0c06030504060920141041c3c070000c400c1600008480710f00545500c041103a09095841d6005400c000307414503400703080d4101151030f101c1d8620b000d03021103202d442203580c40100b4034180a4100001c0c003c2c0780c80029400700380d107101c00301c0441080c8131340d02c050009485c04180c4103027854000d01030f520312041078050076000b0a01500b039004000c82540c0494040140b03a181e040080e1520f0004e191401020f074451001034220764500400f490500c454038030302c541d14030107004001e00400109500311420280c5a1109030b0b581000115076050b00c4042d0010b10792844048200b048104000400c001030b480304001c0001d001d080c4240760380c0070301d0341900302c00e00d4840d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 885541654 1250 885540404 885540431
    0xe0a0f211e0b0601180f0311040b04020406081030052802240a08100e0f0414060702031b010b0315070f0302090915010c02092a030405100203091c03 65
    0x1082d40c0c142d01d2003c170016074180301d100d43c0443c0d054110303a0f12507400b041039000c070004640036040026285601c1071011400080b180e0b00705c20750503c138071203e06100754100d8541c0207243c40c010145601c0c504207a00302c0c4c041d001940751181d0118a05000321304946c40c150848a03100e40d40c113600902c11401e464079178118400c504146174205080884003050214100c116401e0f90305c54091450000100486240440e01c00760002103504041c0c100310280302d4030b61178094400d83c000d002c29035003100c0000c0203d00d003202d10302c0082810380c007607689030380914a03121059180e00d01c920880f640320401550f1b21b4180603011f0b901003128080065140300b42800c0391034084009400c0c0b00014600605140c010040285d169071076481142d84000c648556018840e0003000407034003c40070320b000a40100e0050706000c00d031032001d030f041244440b6120558403c000f01c410702100a00060302d000b07159a00030b030503c240f28929074015603403009000003140c4003005c40b40035940544001d4036407107002c03d6868040c0ca4129 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 885542904 1250 885541654 885541667
    0x180c15030e0a06090c0e01290c07050105090f0a1d600307080109030206040f21030b040b090106050307030e010f0c0e0a0f211e0b0601 59
    0x6012030808112204803a03401603156114080b00801240d6600c02030740030004c1202100c400f81c8081c0a003000150703111245c6444480e040c90070042516031034400400c0d000144002c6a1066580380050700342d0030f1508005482d00d4100c04c20181d44900144000201034440f0500c0000030480302030041246405443e0460034040003030601150102800014404075030400e05030030994065411802000651055107100d040200a58264403090341000c60709404c0c68588004000740f04606413490a0b9807141c24034200c4042100003800340c1c02441c0020301003040e40d02c15100d813500810780c000109000c0c03504128521a0300c000c10f00801e42c2d6212400e07450825100e084541346050341c2c2000b255052840207002c43c08003d00c8481010748401200f1002c540c203401001e961092500203100e00c000e80c1c58007030a8100d59035996030103000e000d00006011548100f05074115101070a41040d0461000d168042e83c6110040580c3e01c200d0715400c400d442d64000802c0c4070200d0282c503201600c0c0c2029400141103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 885544154 1250 885542904 885542939
    0x30f0f1e0203130b1f080c031005010620034302090604020a17010611100b0a150e0d0807060b030703020f0d030e03060f01031a100501050a03180c 64
    0x3220310510800c10100c1203d1400948240c015000c4240c690360000d110510040814003811104004040003030001c0000403c400b540404038141c9540e00c0030030b108001221303400d200c0c442c005200c890068a00005202d1008842c00821040d6403030101c241c200c2072031111a14150001507185000111041d030b2200355211400e5001c08010550f0030303943e0300000c64070f8101800c00c034480c90b0300142840f030543c02440010754405c109100c0e50180d40e5140c0028042990307803030254030307103008040d19006015018407404020031001010b60030514140103510150b850322001400c28022680d44e41013a6566040140ea283ca10464603643e5501807480c01c40c0580d1001d401c60b038001c0e40400007d000507a9441c02d01c3d0f02ca6007055604564558890900f200c1d482000003c0759054010b0209004000002c0000c07941038034003130103025421000c84504000e103070200700d6610120503641601400300b5803046000300b541038040e141c040740c2031100d24000c2e00c1084e00751704100d07001c8550382d000300251106003440d0910b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 885545404 1250 885544154 885544211
    0x110f1809070c1a0627090c04051b09011103040909020a050102030310170307020a08100506010f1b15020c011a01051e090105040305061906050f010c030f030f0f 70
    0x107903640c0d076034460f0f410080c0c200d401840c81412100082d01c0d511807501c644541c1000000c0c2c0510601e9030410b400040340162030710815030280ca040c6a100707080c1801041c2c00351301e41101134120303041140c810544581000007054100b0108801e03c1d04a020100082d002410840f100007903140395600c100b124000c490b51016065400034020441450061096681290801c0d00b00000009032048070908500c40d04100039846030740e1400104801d60001000d00500001c10010811511040c006440051200c944040001ca0060550394910204203085142d60b200e5521941c0030440c00444c070042e6048001002c026a54400e00310b050074403082030b4540800d10a08025103081d071003002202801c02c2084000080765000180c480242c1d00c07840c1114011031700304042d184142000407003440d018460102d5805400c0c04c2c404082158070b402c04488000c040c0c141c4800d000e2440c9a90155140780c83c078040b01d07007419601c1d02045101c0b0560700900307212044282c80020000c49040d011107000106490307101c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 885546654 1250 885545404 885545417
    0xf0f010e19030e120c0301062601050408030c0c0703170a1202030105010c06200318010507020106140f011110060f0f061710052d040504080d110f180907 67
    0x4011a0b0404443c01080300c05940c220004040c01004624088101002c650590701c0d140c8000f90800000b005010001d143c1084280c1c9002e0344211207099820070b442c0500024810001314031003d50010041881c00105403d95225558940340c64911019000c491009144001030f10380c2c01591203240300d01d25004c2c040b0b0071400c5505060000b441c41a2980004091990fa00211b508134880c3c1d070700c811010310741c1c40c01032a42c1c0d1800c3c181d4030708050f0203c560b0103410341c2004e003c0b4007414010b00601055824a44100810141020030004240c060700341007418043d45070020101260107000c03044442c0010000414042c0c945009180c441c05194042c0ca02c1081001c01032100e2940b0034038003035032001182e0401690f5182d21098405406081e8082d0303612428410040c19400007488070f5100d18400c0e2200001d5900540e81071000b5514201d400410b801020000321000080f25404400061045418076040c04017401c82c0000d158020170642e4400d4480701d42d140600e1070542105640542d2600d8141d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 885547904 1250 885546654 885546703
    0xc050111040806161b02031e010c11010204030b040204111204210908030f0703050415030b0103050c03060a1e1d101203051215060a03050403030c230a020f0f010e 71
    0x502a40c48459005800700c03203554060251f42d000c11455482c0c1e4202c2c440740441d080d40008903402402800390003008290100d0b80328403907160600c00d07681101d030401500180e40e076440e070812000300001103006012440500c2416040710550a042e44202c2c46000e4000540908041031001e80b03a140020a08000003003009015018000c8141d80c02d490280d004035459107a24a410340b058003590b0802d02154000802c904d00c216850340003500008400c4c3c800704400d0f1205203052080b4801200c0c01604965500820020f041207005100c0c031101c0c0c86400403000980311005000c1d15065010491401c541c28014040304020b0818108010880d0b60b1064100c0b8203941d401a05a000312180c0358458888403001488a021302200c50915043c01460710f6510340180300050010241550b0940009140400c5c20b20640d00400c0d1442c04410151135003c01c4511040109205900c80c40d900d00c1107020b4030890b0415035030200900c00100d0070303010000c01c040c441c1c04402443c024404600c6c42158140015a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 885549154 1250 885547904 885547907
    0x7090302090c04120b070201020c061e0a0e0a1211100e010c0c031d0f062a03040b0d151d01080c04020f072303130905010902040806070f0c05011104080616 68
    0x800c1005503126861501705e41c0c401400368024041d20f0f00c442e40b1805090100310b50b4280c0804411014072043c004119961541c00858003291220401e51640394000e20011000c078030040c141182140e8103103404100a94003002490038203030520840111642c80700350302c4941d031901b03000d078031410595403070502c03808900c079100105021941c40d10704111401c121a0b1084907203460220a01c8400043d10fa540d682c44040400788403ca0201a0716102d580382d581000c0302e8400120446049861640205040440c0003201000a0040d40000d14070003020b80c0c000150343c0032683c48500000040c80301d010b5158540040d45081560240f54203100b24410801e4030b50890035034041c0d400c00f0360030041281074118201036600b0404d4400d0010400c80c803008c2074950005501c0b001c40d10981f00c0385107051000da41d85001070010307402580210092030300000009140d817841100000400e40305403502c901c0381d03101912854211006c25481c07402c4800002014004003104110182c1c00c0254051002c8221082c00030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 885550404 1250 885549154 885549179
    0x112200c0c10140705150103030807080a050c030703150906060201090b0106020a38042109050d0305280201050601090512060403080a0f0609141e0a0504061407090302090c04 76
    0x984000c2c40f202042940c14440d00300700048041680c00100441542c69040150100a003200c010700042c004400107000b140d801d01601c0d000d0a100ca0b1501d0460300c07035a2041e00507000508141529142104000800100c1400340c50004c00454000182503c0242490080c0d010144c00240540d4032040000b000079851742c0f506d122018480c1c070014a01c1101001e1004517406900100000484035002e0205001c3d01034044400000d00884024580c1d601400c2618084a00c4c0700b00c540c400c1d10b0303240f985e0200340203c00a2669200c907541c52007904500f20a40c00d002c0c1c02d04406900141e41d9102040b0840d43c000c1d42e4840905002c0384d5400400022031001d650711030004000604001c1c074140070903440143c5070440614aa000b080a003d00c40d20344041d240102021464101c0810315400841c9a2455180121404502851191101d940c40a0800e000b5010240c030850b8100c3d03448003071500030800c3c6c4150300e0007244203669203107405156004001d1403150203440c0c401482010031007086000b80103030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 885551654 1250 885550404 885550427
    0x72409060f0e04020705100e0106090902012c03060a050108010501090b0d11060d1107050705100c03030506010c080301030308070207061b020f0409080f040602010f1a0112200c0c10 79
    0x39103090b50007240004607011340202000101315100c1c00300081001c1440390030071007000143c98002c0210076035541030380d402c0d281d40e4440a0301003009d440310303644d842000004002003200c4003000c0da1140015840480d1420800712042c00760a60340d58010310081000380034035401050440d078181b115030342500c0000d4625240c4503008014039410100303160039031255400d40c0c02d013400c42d0201f0082c1e200c03807041e030000031b6109032411078090080003c0400c03a403520083c090702d9120103958036a01c0c60300300e40e000d80040001030449070502c100c50302e10b200010501030007580a58070030b6440883e46c0c00d280801a25140f8140c00000034005142c001104030a081101806803540458024400d00b1404022038014490f000c0c01801000c0300190f40c410b001800001407007160002d50003000b402c04602c050a0803a0a85003004921500b4000b41c00755540c45a46811151a207032000051b5031602e811108000741c4050902c016140008100742c00554020b02c0702501e16802910101210010564014100b05904 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 885552904 1250 885551654 885551657
    0x1213060f09090c031b171e0417040801090332031519060c17040b0d0b0f040510140a0308040e0414030403031d0f18090f072409060f 58
    0x4464040f941c0f80b0a81114401d90700c130240c1084400181c000040c036a0f00d0980c10400c040c510000880e0720319030100c0c410030102c4c1c01f1501019050329942d507601c0c1026000200041d07102c80c148008611010284500c1c0c40080c441d4071200c104809103c1101c441d85541040501c3c0c014001520b42c0e030326442c0c10b00302c99114075010301d1400741310140350020388d401c2c049089404000b00b04000c04a4040d8009003d4200c0f02d00450000111600c541040d10300d92280e40602c00c2000821b0103288002181c46c0c200b030361840e50040c410010040c0c4071010408686044448003010303082d01200b040400b500c410b22245d1440151a01d2030700c40e04640b5120f03440d20513803042a00600d1084005004d120300c5902d20540c4001c0c00040d25600c030743c0c0c0e0070010210180c6a80038075000c031502d5000340151409449485641c14041d0445403c040090000800400000e240049078090b0701c05160608005101030000350581801002804c003024400040304070001403103000340100c14801303021031764100040c1582c0c840c0c01e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 885554154 1250 885552904 885552911
    0x50301180c20121b0f16051507020415091a010801170c03030d0b09060a12020f01090f08061f120b0c0403080301060f0e0102030f040303050d09051213060f0909 70
    0x304120b00d18140788100c40394410000481c1c401c07100700d81c240f140508001c00c40b0460705142e010800d05515001650301c240c1119102040410103403c00345071300200d00c1400c081c49414100e2580200c0c00741d41c8820380e1181c0713400c5030031414808541c00d446152024035568000d070106096100020304024418040c407041101c801020903549402080410b41c8881c000d01685d844191610038040a0b104048140d803149806000107509420b100751810202c0b400070150032001c520342d800f031007002040f4860041c104103044001007030300c1c1080d68944004244140040c42c0501d840012801501442ca5010301003410075841002000c0d600c12249420b15040700100c242074661031440c0c1841d200c1c96000420000011000080480c2c0101c0581c0200080341c550404544100c00120703103074811404c0300d2503080740c00e11007400420700c45e41c050007070f004c060721000400e05819150140b030041d0380303540c0c1000c0c40c2e4001054056048480107107402880e442c100403449186015029100510034003410011603038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 885555404 1250 885554154 885554207
    0x106050a06050a14041818060e030406030509150403030c02010608191a0c0306010f03020d2c06040c09020906090603151201021c09020301090b25021906020a12020406050301180c 78
    0x9400d109007802d07948c081010448078802c4118692280c12500c00e80780420301d8540040c007030603000b0401500703034070300601241c40542d103541d0203500600240b50508219075032000c000c543d8600400183c0d48000450002c04844555403500c1001450041c031180c002029005c20300c1419025641520f1b040741c02400c00030b82003001c60300100d0090040103e03d40800d81010100b90001c0c0380020802512907140000400c1001d403072481c20340e10074050341c0051109041c103204200003a80c51f4040c1644040042411389041105c400040c582e410682c0c8040d940c0c1c04850340280c41e40384ca10a14101007100748000e606141d401c1b85400004c0700010503074241a600c0c1c801d140110b507020740c012030703145501c101011040e04004c1c07012240790780540181c584d8020000c2260a415000296040304803201e52042d803403602030303a629580a508812189014801a0740da40d071284103050020300003600e0b1558a451b12503150201c0f1203410820100c1541503207180c601c10541d0b560f44001c04440d000002c042c180c12030311 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 885556654 1250 885555404 885555431
    0x3020a05010f0c1505100e090a0b07020a06090602030604061a030610030e03180310090c0506071a0f07030c0302041d10090c0e1003060f170106050a06050a140418 71
    0x204070220013840d842030070005184041c000e9000b240121503005081158a803100c0119502c1c1c8410303141441c1d60b50142c04020000780700c00503815401003540c410b803041c8280300e60b140380c1600c4004004490954001c42003000b142014400c41c2c00800c0404002d401c03400c4c42d01c01c1d0320b159100260020380100c003402814001075009130406c50700d0002a03000c5940d40c6482e4081000a810384061040c842d00840f0345400400f002c502580b80d03219084924104072030324000c1008a10b51180a040f0303645001090200140510342c591544184040303003040c2c4681c6007881d401011a54500a60000d1605c140814820705200818119911120303000c4c800d181c1c0c82e448045003028103c0c0c1c2c004e00340181001c00043d0002c1c1c0c040e010008507442521101c1101d15440001d0b002e5460501a40207030801050040001d0208041400c80c00f2505600000e40c15850340041106e8241580151000c9100010711114440c2d014040101da11071002149041600305024002000490340034054080e03207030f203407120022 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 885557904 1250 885556654 885556667
    0x30a050c0f12060405010b0306150705010e071d060612270102040f050a1a030714041e18061415090405010e09060c0a021f0b0d150b030703020a05010f 66
    0x46507000c034036074072400400603003000c01400b11540d502607414200001140035011040e24002c1200078403078100c0035101c2c504100325400210060320107648070b0074a400248000c0c080003000e44042c4e02407a4655030740084041101202528040c081c0c00300304141c1c004541440d0940303400078245038464624610700c5800184d0341c4d03166401c0c101a940300090008080251140c414210b0750b090f01c020702c0680e56428490288802040260412041000014a241d206094000c80c480b96604541d0130203407140f610085c00121a25910f00c1c40c42c034800240a12500000309542d03860141d44248071060400300c0002c610101035070780c0c0c3e0003054914184604911020287c8020003000742c0f0810041da503405041c840c152040d074400c200b5000751400315003000d42c20b40031030750840010780003015444e824864040b034851807400300c3e0081c59500c202d60640c0390ba50070b2980e082036014000707955041d10109940000c032481130012900c6a40100030400041e29846034517003c40310b003400d100e40d00345403e00c0140c0c0c00c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 885559154 1250 885557904 885557917
    0x10906030c12110a0f020318091801060905070815030c12030c01050a02042c010509041a13050105010f0509010b030703020c0f010c02122109010204080d030e0d0e0105030a050c 77
    0x10703a080c01042d10200c3e02030f1028180701c03400c50f40c540e0181e90340204141e8482c45408640070401070030129080450409904183e0020f0540300c242c01c0741000c0141403400c5507142e41104a105843d0342c203014801361f0006160341c0040e1451000f0f28106040c070b0000350b4074684d21203524040c0501002d02484044284241c55504030200000d01403483c3c0400d000c80254840d0198020620480c940020500b54003640080d90290038104000b0a90910040000d1480001c00c12a0300d0111104500603002905100d0703801010f101c0f0500d1009034062416500b0740d8016004003085600c150f0040080d41d4882808904490120340c807075540380c40c1e021382100a4810050390151501c11884803c55142055008130580c02c030b41e03070030740701304500300820b07204544030b00090444c0781850b02146081d810002040c031500000c103000014a46540c4075156428004204480e1010070358440203407059480034007417480b03141c55600d030641c0c07190240c2d00042c100c1c0c000502a04011540c0307400041c600540f45045818 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 885560404 1250 885559154 885559187
    0xd030522120b0c0f0c01200a0203030a0e0703060e0607200709021605010e03220b0d15032301050901051b030a06050a030b0a0c0207050604150c0f0602030420010906030c 74
    0x15111740e02c0c015207010306191240c09200601c03205169400310000010b80b11308a4080d03000d1880c42d1600d4002c04060400d1500324a49402041300000002c3d800d44038540a0380c11102c041d10481c940244090141c42505411103194540d90440d0b00844a0100b00041079865099006844554040401041c00c5010350010328540c42d000c491032400c400040078118400b40440c0142c02400804082c04440180d4810214281c506024245441065402a0201c00300103e0b85080180e034070b0300c5080f03072428206007030040500303a00c2482070310321030030300960f580700b040f181c001c0c000c605050f00c2c0310800c090b842c4d54403000c8030b101101041041c4103d802c034000920b03000b030001104544030f0908260078641605c0003000c075483d00c50500a0f485c0046a03e4003140c0d0001e02e442d0400303150900062038a082c0003107240410901e6442100011074251841c1245805150b00507200d00d000e1414001448502004040c0205614620041030380d10500d81c0e070070b40d002c5190200c0c050507203030026242c418180e86140c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 885561654 1250 885560404 885560407
    0xb0a0e03030703170a090b010302010e010c0c0612060e2e09020a0e040e0d020601290d0e06010f030f021003020705010905010f1b1d010e0d030522120b0c0f 68
    0x200f81a4004804a4810454840c429241d01c40e010410f04440d040c401c02848404013a0040000d503016402c0812842018117211103d01d0340d0755111300c000200d0390020000305150f120082c0002c50b181c442c5001525010002c00060b040c211000040b4a1503140e141c40c0d200c594054000080f070390701c00030500504819009540f07031035952001818960140ae00c9900640c07a0504da404040400a8611030100c3d0903006450143d0030208911505183c0c095442d009907010f0440611041c00340f00101a815108400080c074107100540e1035080040681c4440100c420040c0148049001540690070480d41207a0701c04104020000590207409000030141065180642c002c05006042d08242014401c1c00300c01c01281030200d40d0780800d02d442800110010b2502d8400c0c142c103609040394a07044000505026000d0408500024810300b000602100010804a00404c17031981070894403480c0325400903020402418442c81064910041001403d26503246020548140702f00c411603419100010815 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 885562904 1250 885561654 885561667
    0x905120703120203010312110c031605040f02280e09040b04020406060302031512010e0d020d08070831080d150803091c1401020301092f040b0a0e0303 66
    0x61604116401c0e40424484241c1c801100028421241660b038804900100000411b070100d0351400440c00703051080c8244014040659402c010501c807001004000c04607403410007080c4070685114041ca00e440d0360052001c01614001c035858040d048180d2040b401c0d504005070380444043c010304190a81005100d0140420b011024404601c0349000395003d20903203941c0c003030445c1244000c4958034000031444c46844d40c0340c80c01c80c034410500c0301180e0022540014942101d42085544205500568851854859030079081402c240c1d1205a50512546902d00301c00d00200581131600348588008051022011015002d0381c1c0b0402c1c0c50704501226201c9132500e0034070000f441307180340750300ba00d41c615580060701d40e40000c00c90f003000001410035a030914040010030174032001400704607071100d01152103444201003403000e54003e000c05000400e441180c0005821400d602c00d414104440f80000c40400c00080d400c2210b00325a414407505503182c4121341c0440d0075401540c032031075041c0000101c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 885564154 1250 885562904 885562933
    0xf0e120c0a0b0c090102010b01080712110f0315010f0c15021c0c020f15041a13061103100605030f0408090307030206040f1e03050a020f0103141608071419030905 71
    0x44c0207109020780081001c8600e0100541e9401e404070303045000524000c03940c0d81c2c1c000403a00b000070b45000300342116003048202c500088107a0000c039640c40000d055524044855a0b00004041c0c5024440c1072070320280350f00c1e84502d00100e84006040000c250002121031800c0399881081c1c1e043c0c0c0b400c00042004032034840000352501c0c1034000300003903440f81001004045105020a81c0035540c0101c020340031880007480341c041001d00030300310001c5440383c26101022801a010b9a800b4840c2c240c400c51780c0b40761030501c9041c1d5640c560031600820030148104072156485c0150a074000d60080c09058940400000080c98400b0581009411241c0442d000079140d1583e52070009548503840412110342c144041008404503034440684180e0203610703102c025041010462900640601d804140c22851503030030900790406844076142403003420402a003556000c0d00b030380c1e0003c02c03500e04000c440e45060b901c981c003801868000d01080d00c2d12105e44070710a000780c2c8814000e80e8450161000d00721140305 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 885565404 1250 885564154 885564157
    0x180306070c0b0106030c02101a0901120b1e0f060a05130501030507080a0812152d01050903100b03150705130506040501050f0d061a040503010f0e120c0a0b0c 69
    0x400300c5400340e040c800804c14038007a00a240300e079002540140502480340440c0303000b41c00d1780036000802d26000c4105101d02e80300c035900030f4040c0407070741240400d00e40e1510f41749903206c1c0300901004000c0c4406446000000179840c80c25080040e2640f98000c545440300044c44521080d400554000f94106a241c00d400054014604890161099551300c2d561402125100c4520312001801d22004100801c0b2240c030a410554100f80c4005100c031406041c28082482c02c090700307215009003d03490028040380c4030800310104500c4030a103405800c2c0180782012030b0b076600346440e62030111a11404140d019450800c039000600c001003654501a04102001030260391200006401c0d40000d25404112803c0c24000c40d022900180d650900c0c0052010155500d90442c581159089864a038002514503440e001000300444040100d43c0c0c1c4c6103018205402c40b42c2403403440c1511401c05114000600000c6408442803c0c101241c9a45a580b00b0225042448182000301716420031411302615245100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 885566654 1250 885565404 885565427
    0x7050405011401031b02060f04060f0c030f2d09030302090405041101110a080d050a0e0f0d0e04060b0405010c0305070c0f0e010b19180506030a141803040b18030607 72
    0x88042000000f485c10007034280b82a0f0744003001590110003c00d051512401986034054021980080d031072818404000a490000c00e1302c0c40000d03160300810002184a2240145450030303a0000400d01d09401030751840c04c1821814082e0b059507800342d0005140c003a4044880c3d00380c0090041260307181a203050841e6520041c00540000c240e48032080709035000280301c03045141c1003050182084111118100a800001c0506030740949542050b210410100070f00c88809000714058200050b480000030040c2200c0498107100320304024041124510010840301950710a1800c921751b2103c0341025a003d2040140007884403004581c00100b14100c0b050300000c0d14100e0540c105a40d80e640040e030440c2c000c001e50b0b42020344001d864890700c0c9000e900040203010342042401910340e0b90300e000512a400c11210415001d8072025184008004160f41980c01004610854141000740c05880e80ea4003a0303004101240f130700041c010b00390a030130415050b0940c000408941140c5003030f0a00824951120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 885567904 1250 885566654 885566657
    0x20f1b0d0906020604020d0227010e060f180a09020a0b0c06280507210605030609212a2103090a0803060d060e030a1404210507050405011401 62
    0x21188004000e2094110008581c2d5603070060281e40c44a80030009604000c820403a0300001801300004580c00d0200151004440229208a9980f502854041c003080c001e05661107040c1038038000036169540b01070605036500c00340c2a1032607039842980e010010400c54030040c2d840410b03140c00160209d0b4a0000300303100320301e200c00d0360119201e03410501c0d81a0407214482d5542503050242401c408255404254056030324902003100c060206510081d042e02e0b8100c3c518650f882d84d13820710035820108000f542004000000300040070020024101c4a0b803511000342d00ca0340b00184d003820042c00a5441e150282c0e260f4600c14040110010641e5200900c001c5084d42096090f0ad004e04500542c0690340726a030b207034019204000155880851035400104210382c0a1031600010010075400c0c1309007030001541c00c00a5545200140d0060300c80880e8102252032103100b04406e0080030032200400d48050741019401c81a843c032444d084d8109042e44e000250854a0100001100392116002c10b440072400e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 885569154 1250 885567904 885567913
    0x4091104031505040f14010b040509030417030f0717040b0a0804020103050a0524030102130603050916030c090c03140c04050f061201060c031b050607031406091801020f1b 75
    0x1d5019034002d840040724040c1510045042c52001b040481e103024001d06c13000c900000d0302c0c0c503c03c0c00041c01c40c3e40c165880801c0e80d0020800303014000142c0001079070b40502c080118180ba203901043c041610807000000d0500d0511500300c0704038a0060700f554054170f40f0701c000f90b460300d83c400001031412004580590000e81400085004010140310382c5028045001c0d403103401c0c1d85d000b2040e40008112800441c0c156500f08201412140031070501400780c00d01d0380e00803803e41040d082132850500b0071005810465060b010420000d044cc0c4000c07001c850398a003000c1360b402000c400c140d00501003c56420305001d4170904000916280b03500601c01e4500840d503801070603a051040c0300c078074014084a141c2d8441e141005010540c011091224518404d03d0100b0b5154a400301d01d0031402102407007190182d105a060085081c0c2600410485150ad801c0c134480601d8082d00040107060043d01d0003191318421410a800e04a00b074040b5059142600c4d0200d9903a00800d03480801001c0b0300304a92443c0c0103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 885570404 1250 885569154 885569183
    0x70305070e0a060e0307091d071508060d0c0305030307020c100201020901020c1e030703050304090b06090f0d030329100314180106030c0b03040b010e0106021905030409110403 77
    0x401801826a00241c01040b02e141001801d03500000d821040c1c1d5890b1013001000108644503020741000501002d401c107613030314444440e86240007800e8002821481414002c5011150b02c070503130a134009000c40300f910388000c030390a04140b0200c481c3c2000e070142c00008104001503030000741148401c4001d84500140c1a16031200f01d00300d0007500350050060b0410148403086161101d0029000400c403411000d03070159200010745040e0141e40200c441d40c00218041007020505d1041e0601e804066856034601492030700041c440803106045ca500c02c018800a02c824148280c0c41400440c1070441c0d40d1070400180c42c580038280485c01881132188000b480400c24052090003440306070031043c4140005a12035221200c402c07006001c6000b100d40d41e9080000200d0340542d003881c0207140004103190f4030304003814910f91a58050300102540940d8100405c00c0702c1d40062040354001a11300d000032081c01d40d1400714218880c503480028268144800a0180c1d21001c0081003101e01c5078071924031010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 885571654 1250 885570404 885570407
    0xc02064014070b091003020c12040f1e0b040b0715231e070c0503130b090108090d02030301051512010609170d05030109090f050a060203060312040b0d09051603030807030507 76
    0x81203d582d580c2043c0e941c4184103611b4001c0d00500f0283c105142a160082e00002c201029a041507201e59021170000d0010024010904195510410485c01d41c001e500d05050242000b03110b80e2003182c0101e5400100c070710a004149170900c54001c040307031003488050821440b02000e000040d046200c0c0d40190000b190017500d901850700a2425908080405039407102e0066035800d04038101076a55010402101401004090180c0050300041040e140c4407481e41d400101010001040c0d907601c0c0d40310036038000502d0340000c00e030390441d14100caa08111811050b0407506502905019a020b0314083c3c0c00400d417241c0014010043d10385984240c82100790640c0d8440e60b40c24140501000700e90b0030001401040819042401c91034003607900f0080b2010a640c6042c44c0826407a0195421640401840200e28003400880701c0c0f150744d141500d05060801d0303078a01c018400d5481488649a4600900007005014070030494050a48800000059034a0034082c026410480e0805c00191401c4001034446 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 885572904 1250 885571654 885571657
    0x7061d010c031b03050903040e0907090b0118180204030605012303061b03041a0a0f0606020102090f0906310f09050c040e030f0a120c02064014070b 65
    0xf10700d100480141040c2070100790000c10020b0b020006074041004042450b510800415014922900003080a103140c084000116440010100d0401014982a0107419014840070b41503864820307900808107207802070400207120f141d20042c00b043c00e2400006841c049222170304810301d080c01c00000102c01200c10140c480c1d00440b41001c0c212a0707201c903600000b00e010003035a03000c0d00c203030402090855001012031004030200c070b40d09a0203031110f401c150081e9150041c00000c1945000941c100070015000958a2000e045028040d6010b4000181d4664034040c0594105030b10000c0340c400c0c3c0410070541c0c003003031540c4248540c03850700700429030300250380d90720401c602c00c0c2d00a8060541182e01004100203050404103623040342c8418040704d501002c603070000340b02c10701d03081c0c49002400502d0000d0000740d61400300c118082d5080706c030400c11700350903241c940b01610750844882420520007d5400c1d0561030120090614001804103c00412000000e00c80100c80d07950221218280d83c2e11008449 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 885574154 1250 885572904 885572921
    0x305060a050408041802090a14010f03110901270b0307030b100804060c0c0203071202040e030c1e01270b0a06151206032109060c1e02010507061d010c03 67
    0x304242044104200c1c20714580d2141461608172002d0300d494020000100d031500e0b103421030220105050f404201c15a0401c0107005003408c18242427052548005000301c160060810140c10b00020b04080540c4030340a0503204807102d602c260008a6a4070b40c105400260012500070b00400c0c508901d81c036591521402c814646003440c0d544498540c0c0359503c1a028180c1401c0050911140911031030041e50103201c3c40303000d0424070340e0f60340c10512a4010441a1150118603218580040048000002d00400e00011254000c0d04e4008150340c1c070120a8010403a1303124078072035240201c1c1801d200360400d20781e115a50b4095800070641c2c1e11a644c003802186d0700d03442002e400c07031910b984003040f990241c401c0303800440c4801c03400120182d80e1380f03681c00340d158003003840080495001c40442d4020382208030710014003070601d0045107880d8243c1d10b10141040a00c10500e04020040c2e500045a215100311051030f41e000d00c090026880b449a00000c9101c410007410342542040103103212244a8410080c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 885575404 1250 885574154 885574163
    0x90e0705070b0103031b02030d0f1701050d020609060d020a021b0102010e0a03031503150c020f0d0206070c0c170106030c05061218010204030b040f0b0610080703050703060f030c0305060a0504 84
    0x6591079a036056542805184d90520f0555095a1206c0540e40070310400d00f0f1460b41e030b103c4e0711400d18441401008035032020fa503a40c403591901c0060105071220380c46000795681c16100a0368809640002410718000c8584882c00c1c81c0c00098034044071603022800e40c0110301c11028a07060109844016805d940041c610080650b000340300c40000b0a01ca600920100b458154082541617244c0c1c40320301c94080d15814200820340c40751215140c550381081029501840700007d0401c42e600c21170000d485040190800f0100411107880301c06100c00f0060000043c54844826528410310195041c084e05d61031105803030302e4a01500005103802c01500300d80740d00c140100310019607907420b20f44084081c09081c10016966080c4008000115000c0000340910300600c0e0031401c0d01c4862401c5854030368000c4c0302500518050400c20b81003504400020b070003d2481c02c0109990f910804102c00400d40c2e0350010348107688043c00001488110b010103002d0720b000e02c040d0b07000342c1d4815040201362181a1002003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 885576654 1250 885575404 885575423
    0x603170408030a0c1b0602210906040e09010b09040b0403020709110f1806031e1b030408030604151d0105030a03051e09220b010c030f0309031205010303090e070507 72
    0x48591344100c08074000c50344207042201c04280003680b0505a030304184c1052000d6480008113641e40f4802c000001059070742865100c0c40d00400c4008140180924461401450040c501080030000d080d0010b40700d19001501c0781c1c00300c0c0b811f810400c0d00000142d600380d015001d9210046150312060240309081502d2540491a1071111500003086601140c901c4481c424a1411281d507540e86200642c003441c03c1010f00b00b65220148118003020501601400f44c101c13400140c511407a08000641358403e4104914540342e9880740c000c134002e001403034030b444040d44020802180140c000100022140840e41000246a80b2001415030360f107803503a800350103b034061228444480d40c3e0350320342c03046a68010301217003400c0130b00d00412905074403540e5401d040c04500c0b200c01d04074040303440b8900e0703003180900c2c240c4034200c426103000e81082544541042050344030406c80c0181070080c1c00200994804860800c1551707580d0600030100b03c10341c012142c100071b41102045126100d4025604030542111920 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 885577904 1250 885576654 885576667
    0x6080708160c050102071a0613050105090a05090307150c0306080106051c1a0c09130b0114310602011407051914070f02040b0d0818010c0c09060317040803 68
    0xb9108112001800c0325299000c1049800040e020346d00c018112000c45141c0d18181880b03004c120301d034280200b840030150300c1c0c100104080d50b1503206068101c40a0303200000c007030301e44004207421840342c440003424001c010b0791040c000c0b81d0180e1006200803420b5a080110640380c1d800c2600340c0b041d61081c1c5902c8001e04c07441122031610500d642c0f910501c100040c442c000101912207200190407105041e005101150851090524014140060f07103440e03810080c1010904c00070b00080e0f13403655a440c1e901c00100b0b1000740510002d11002d40c144110260503074443d082d0003c10b0342c2c8007036030040340c0055081c00420340441c000049601d000c3c54007520b4041c240146007442144810070418030004004884440d00d6420075620002c005842c040c04901c02c001800d0f00501041e02d80203581140180011410840400c4204060b500d001c074415062a62140c1c440c40121510b42d46a1f2011780307903251080c070010741d4106c4c90344a40101c0348911039440c10b0529400300d52038540030358821200103400400c4907 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 885579154 1250 885577904 885577907
    0x60501020c280305071a160609020105130b0918040209150a0506160b0c0c1b0303090a08030a020f15070c0203150c0c0708030403020f13110a090608070816 68
    0x9a6800ba481e58600ca600c144050b0030070b002c100850344159015000988140051140b003120300d84104d1202c9842840c002800600914100440401030b0945a1300d04140085a03c948200c0e15602040d002c02000140c855a64002a0380b0000c40540705103181820b00740e104103100d000c2403286030002c00207610f90380c2d1546081080d0000305603280e400710125601085d10740d0303443e02a1940384c04045410314002041d10303003a0480c40002c2d1025500708000d0103284180741001811000c3c0c0504052401c1001d8001000700f4950f00901c1082a48108650000b151000d4000083c1000c00c18036404c0b500360303011601c1c03415124065030422980c100c0710180014030180c000c84800d0820352001d012107408035892151142d180c0c50070345100c1a4000700059010707c152042020340c010304100000307103142600e9940010a0390913010b022501030942c84000c0c03c011841903000040c4135480c80301441ea1041201c00060400c8a24000c81002c50850408075a07264802c5040d60700c108024032400310603a100020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 885580404 1250 885579154 885579169
    0x163002060706020c0625020f07060f02011e091203020313060506030a050a0c061701082805030a0e09010611060a0b03010b03240f090304120305270901050301060501020c 74
    0x41550303402d07020416000c07200c03005c0200f2482a40c084072000d10302e1068003d0480005032680e0034508540c080301c01590141800714000301120054100002c4401c0c52046c05c0e40580b0021404204505010203041d01088407030700900c1b4641d218075000c1580e03240105c0140c040f40410340d40803034a00c10b00c4110390000b030029840300b500200014100d0f9004456613907150700d45004070108603182008140c08009503030700302d804801c50002d4000058081d43c1024800b0350750702c503401081700003150899000c40c81d884d104045008066005416255240500c1c10003800381c0c0d40d100c803103600807500c4100000e102c3d4450f0821b100c41001d100064140c0c0d40703650741603e02400322002215499560760b02d07022480d40e000c01000d58100340001c07104510091541426180c0035008040340d130058680000c110001c80d01104450568540ea180726200d0701250a080342c46002d000b050420380a0720000b107008010300c160303080c04a4035044400c2c0c10f6681c2c85130140360907201c0700d108507405603001c846101d10a03d00400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 885581654 1250 885580404 885580417
    0x191803080f040b16140f0a02040c0c0206030903040e06040b0f0111070b040906090f110304240204080c030607090602120f0c032d040608010e040c030516300206 70
    0x7801504041e100c51100100b9031010510f8400400d844408408024031350700a61100d000c8140905544a2484030711621030500e82e100034440d5545440c3c65482034003800101e9000e80d0040d0509071280340c840e413219981e60185c0138122490480c800000c0c1e492800e03015119440c440541540d000b0829000191a10b0300d0f61250075074603000349240480e2013030004014000415060502064440c604160403048580e0365540308040750800103042003561a00382100d412950112603003002d000d2070a11004100e04600700d140b0444d000141c002240e101c0090700a0490808a064070200e490b81c40081da00c8016900c9410094ac205100440d810200c030409403c0312031010450500c0c08161504841c11507000c00c0e00084600039401181d0f80030702c184410316042d0340369190342c0c030715241c02d090010344a05014810031114006400008081010501c2c41c01e005580c440c080310040710741c5615007034000c402406070b0002543d03c2041c448140d2401810001c0041000f904040c03005100c0c0c0a01125a2085 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 885582904 1250 885581654 885581677
    0x30c2909102304060f0203070306051807140c1218030d020a02031b01120608010203073b0d120305011a03010308090909031204060c080f0f01051c06060b19180308 71
    0x10f078400c40d85c0c0d003914001184200c03000e0354001070340e6041204005a190220b4082c2102410303190411000c1c5800541d01d4240281c1c80c009692160000706000b807400000c6015820180e02c089244550b408044208052030718003103064030801c45c03a804080341d40741000100658140c0c4000c0380070b0501005528404c1204c2c00624214955440e000300303d40a030f950707560005000381c1d07000042101265000320f080c1c0d000c0300b0b14801211a2000344601c0f071246050400c00c288102c0302c1c403200c40200e07600d69802441c4540e2105242c0b040c0356105c00301800400b0300344140101c01343ca07903900380b040d83c81250417241a660700900d050b007010700c45010f0102c036100007001032441d440100403900e07140c9030042d0810702c17562041002040d09007110b900140304050140c9900c0b414040d51080c01068249405030906441080d146807050b8025900000b021459087c2d004e0029468a1008034800c4400d5000b400c1c81c2051144000c0c903580166000c40e004d203c16044542c82080014082c03001039000b038010186034011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 885584154 1250 885582904 885582911
    0x7150f06053d0e060304050f071a0f03190515010801090b0303030412210e070609060e010807050409020a0e12150f0601050d0606020309030106140d030c290910230406 73
    0x20000810744d15070040c4e80c180d030550b001d920740420608042251170f003c0c0c14031003911014100c154418080601400307001c0f0401c1d01f00440050607982c07140a02c002000b0071490113004a0074250400100401181c135003500140d20200007069000c001e010700c064114018000754903603071301c540b110080c08000302a0101042804000740100c91184050030091240a410010390180351401007490120290f01c01028400081e004001050300032210b01504402800c00190558a00b03004032204c2c85181c10440700d82e480031401c0111035500030703101d00071a44180c070030745401e00684204541d202c550b441121a102001740024280314000d01c60140c20000604005060146515000003039501b00e41014005a0000c1082a030310b203424042c840041a002040313000d10041c5501240b5900004440a8103210104681c001001041402c0c02d043c0d00c1b0504000c088030a000c50314404a00050700d80344018030607010151503600d00303440b0768030207841123504903050290401101ca440010040054a00659 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 885585404 1250 885584154 885584177
    0xb180a0518010e060f100503060d1205071509050309060d09020301060e060310060807051005070501021207200304170c09160315120807150f06053d 65
    0xc8034504900c1d126540708190710258100400c00485450007490b030351050071004a080001d4850b84040343c241940751400696079607c1602080002d0b00e0300303c005100490141903800c00315400780c0507007075051040c208a4181601814844d040e1490018050010342041003001520724100d00201944032004801048102090300000e00316155548080d5440c1c0c2e03054200115850103010001900da0b068070200041420403190360380c2e51089005840c0225554965002035602a6040c1c07040c007980700e40259500d40074140c8040c002c410541e4842c2c081001c0e44030140518600380c10000c2c405052000540c1410702c0c201e143d4100c03070404c0c0074150b40b9002d5000d200c4a03503228807520a1040c50607009009084d4003408009044841320031305800000300540e8284000501440c4050b1040d800c1a041500d600c0c86007080d0000494080408103150302d80741e1704241c191740a800523030031610100c0702103d40e12400907485942c400e542100805801200c040d4207414a01c91340003d04c80d040519020301d010700c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 885586654 1250 885585404 885585409
    0x3190c0816031101140f0606091f1407111306080f070509090a03020601180228020c040c050a03240e0f07090b0a030c0e09130510060b180a05 62
    0x40c8401d04502418091248003401c0c150884103007000e40e9503910081104101500c4c0340700c040040500307042e80c011584404603d40740d8910303068402d08000204402e420300e2201c0b581218408a003400b035000310b01060711080740d504401c4156201d0981200c0b02d18400c1c103c0c94100700701050a820010800e903650480880e4030281005070a00c44d00c240710080070309034100b404118514100601d00e0403141c0c003400c0c0400019501145280c11980e00456800d20505000504030113805401440f42090340b4070404115600c01c400808641c00e0203d800341c40e502d507502018070044c0d88000131080003251041080c900018440e41c0300c00a541e9007101016170680d0006c8542c004070006a0080d04150200c2c014002810304111155420206d107041034500c0301e1070a2503240250088607030190a040d51900c0c0c001e42c3c035004803140101910020314407122480d048c2c2c0981c0c0b0f840b980d18000e5496109024511200e1101403140c0015165a00e444605110800b002c00c510002d048200c55044045904002070700e4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 885587904 1250 885586654 885586657
    0x2031c03020409060b07230705060c030702030d021b0d03210f05100302150306010801031211060f091005360604030305090d0804080a0c030c0209040311010c020f03190c08 75
    0x50000d003d4040c0da4110906004a01c00c51030800511801f40a500400390000c00085010494906460302a02e5a42c039a00302400c5000d103810294060140000382c002d0f503a070229201c0d650f03518901207503400c2c04200342840741d01c04d141d08001307000c40e10144210b201d071a0925002c20b20156020000b00d200d4004141c004290b070820b440700581c40602c21020b000314541001480c448042e040002410340c078283e00005e0230b091041c40094590307a0f81401d807150b40e521030f22260540301e40341000c440b09800c1c0420101d002810455401e8070781d0040410261001e6114042c080c000d4100303041d03020441c0040f070300007031070441d5942080d083d5014140c0752103440da60a1180c2c91140f0301079280040e040c90900301203402c01107c03c20a0301013010401c1040000b503440e01c10740d80b10105074030b0001c405a02a01d8241c41e010741011000c0d41c001c072400704000806030b020860076039240300f507802800f80f00002c2100b640d403010743c0705030904c1982082c014555440c6001440ca20001c141d803070006c4e00400c0c192116501d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 885589154 1250 885587904 885587909
    0x20a0306020c19080909101e05120d020c121f1a0108010f0905040204020d0f05090c0d03020606040905010b0a08030406030606300f020a0201090b010f0302031c0302040906 75
    0x186038000c261402c4040e42884440400010300c2800c40c01d126695036107200501c5084440ca1003404403002050600d81600b00d00070107010aa0039080912040301c50690950216101d013030b02c01c01c910001c0560038003020032015402c1d10710f50000c000c0d00303c00d00200700350318841140d1542e80313101c0d900035000c800122000c59844804080c17000141b16020103410b540c07080039198074030706100906004014401d04606030404039034040300001500c2d00c491000801911078040000e44031800c040c81c001c80c2100780e611081c003c003480c00440740a0480e090900014089040d8060f001d42c01050001d56981015003212514511034000052502d4090001480020080e007000700303681d1012400784106070701403103210054521810700c80420300b42d045002004204089058944070380310502070b0310070405908030045042c1281819505c40350700b218000c0c02000c1c955402d48841c1669000061010643d00c007241c20f80742c01602405401142d0400c4d10306030703032540002c0780400d0b43c00c0000080d0b80c40ca9100f01c001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 885590404 1250 885589154 885589163
    0x1c03020f0d0c050708030423030c0915091b07080f04090912080114210f0601090f0b0d03021216020603010b070302010506040b220207080c0d080901050906040609020d020a03 76
    0x3841d0302c03103080140c039114480d08400e116900401003070044402c01d0360282011411301d80008075000141c2c0c003207400c1c90a00580160015009000d02c40e2000740e0700c0324204000700a032661201d503a42d40d4502d0185100383c000141d07501c0c1c4100140d40c0407580da036004201362116400c243e0300d000d5503000018202c5088800a4401501c482428550a903110394003e00508001004542181c140c1c400140c89900391128072818500000c40c2d0300100340300340080403d042490007070710195a900c80c5464050011110610308061500c0000b28040c80d0000f6494500f1780c140e0300901654604251002c134981c800c414603080014024007000050759030308025806080f6858a8030348032065458013074255070014010b00d200c0c40c01c00d030b1540e225456110038132407051500c0301c0b005103550b50440036800034491100d018000c508001641d80c070203800000d041e90b1041070380d81c0c0c007034155842c0c0d1142402c0f039900740c520741500e07044100414041511600004245800200f006201524540c00a103a02c0c5182c0d10448 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 885591654 1250 885590404 885590417
    0xd02010e033a021b1906050903070906030b07031e180b0105040515040213080111090f090c0f282703030816020f1b09060f1c03020f0d 59
    0x3140740075408100d80324500e2010015410544141c4041e4a4004001070511841040503444940c1e40e200c6500c18108100c40000c945d4540d00c6400c014000d5210307100c981d009120b00300d0b002881038900e205540403250400382c0c4400075143c00c04101c014041c65000c1503030403106800c40380c580607201d1090b02d81c0c0030440040b64114507814036011380e00c0481680010311451a20040250500c03600101665400c4c007210b0069451145820401110445422074a182e610305000440004003200040035004411a003403406c00000c07001300101c48400310b901c5190300c4018000580346c0d440b483c01070300844480c1c1290010204d42d503c078603e100d441040c0f0040c00500540300d0745000c400703000801f00e10404200b00304181c1a0641d00c015140d5900500360b80910840410030001b014403d02c04e021000c8050b9060b5144002803610369046200784c3c501702071180038141d000c00c0e081e103040e40310700b10702400c058410740314010210343c0c2c0880d25119580036000e5014114085022003000c0c800d032185d0140c0ca48801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 885592904 1250 885591654 885591703
    0x30e030d090606050a081b012c150301260a021309060c1b0b060418030915020c0d08030417210a05070c022701180c0e010e0d02010e03 59
    0xb500b80c6210380e00003805401006001d100101d00491804070f8280c58800c00d0680318280d0f00103c0315140c0e030610741e06148140003044010104400301e2600310a00813a0466402081445000920b101c2071003007491445100c881c13120703a070350081031040c081a450401d88101c001c05401182650185041400c10a681c561078601080454460340d0000c84680c41e020059680e01c16044480c484440400740c10b070705038800084c0042d501c9400c001c1542d40e052442a040003640d00c0c000c4d1004220740548108561800252600303144006580400c15400a120380444842525410290b500180080c0c5100d0f008110045031051403400601011014007440a05c498200c031a1855070b64000d07048590a50822060019481e4042d80308072402c0d1b0116101d5148100100d00141c581c403c41c040231710924201c000014174021036010814503010403d40502030014240d008071000d043d2010481e000c00c90304000600c450408225001c46144181000540c4085001c0083d03c1d03c900104d02d49140d90b03034101003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 885594154 1250 885592904 885592913
    0x30804051203070822080306010c050102161a0a05220303020c0f0714040506090a050705160308010603061e0312121d1e12031b0d0b01080c18060a030e030d09 69
    0x800030070021020361920460f05503440100f90b1101904042c10020f1404ac1079003030007003e60440d0f250150011080c26800b07000d01d4026005074555422203a140031031800a0810001c0e80651445024000030401400e6410520f044080f0201042541056402d000720403080c00c003003140c0111050140020403006282554031180f01c070319000000c0c006c0b802d22007800015222407503169000000b03024049a240e0752500708840a024010716659480c1030f41c0c110b0420305810410381ca06844076a50203003c52900c911062030800c24600114880740c084200410104000320001403135170204e40b519001710070410480d40b0956a440d0950040f035080c09142d0380f4491400c00000e900a4003191244009050701c00381d40f07441c0c001030b0820034a4100d00100085c1c01040186140c50034900a0410320340b030312203c9050070005c0c031030b40e841c080c0410240404200d40c005910300740c81460380840c1480001c10804418811141c11040c000010305865018031180540107002a088990290000003808601c5040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 885595404 1250 885594154 885594181
    0x610080105011e03140f0d080a06050402070818012003180306071b0609021f03110903190f0b0408030f070e090105010309030c05060c1b03090a030308040512030708 72
    0x10640c1c1400c1050103010b103800001c1001200e4211580242c408403116170242000d1640780c01201c1800b42888003684036400001d850701411050302d08002c080e8503101840200e00c00c107000600980300c18044450001101c05013000c0d112010b14003076605c08050b09407501c151070500034811658001041868016919094441a107142100103041e2400d04040140c84008510b00440203503175000070880c00e1002940040c96100d601a101d403068041040b82c01400040c442c4003140040d08001028000e1141802910340f8608018040c0c001c4625881c601d0a00350120ba104503401c042030396418001c20b420700b4015205034064007106560789485100d9480c42a07000b4800000d0001e80144200e4503160104018159402800c002803456040d040503902c507902d018004208c6c1c4a000100012141d40348094590030341e401015809503846403214541382d02600c0800b50700031040c00005c0001c2071140c10500e41180c05141a02c000c0b00c442520050207503c1200c0303210200d07410906101c401c0c1200311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 885596654 1250 885595404 885595409
    0xf05090f0610050109050603041113020406180b032d07030c021608121810030b03240a051806010e0403080609070815130f050628030f14061008010501 66
    0x24114002d0038106000030717082803410f00546000e8580400083c08000307e0440c6003841c040b00503c0f940006005d4020388011b544a4000c040001d04014245088200c0c2ca0b05003d0645105100880c00c2d0b9903100020325a00759080026004c0c04000c100f48403210803228101c1e0f005040982d0301140301180b802010303107042020032117104c030380311401744c20040c500000c125803031107040403990b00b6078032101030320a0768144016908003070b0302041840031088565050b9204182400050b0b09a55409100c08802030302c0740301c50002c0400400b20f481c001840c0181e15400242c4c094116100f500e9070000f0b14200034980030007600018003609444091009164009048691145080310b258169141c909070003002e0304130107449a030203407d510160007840c0e0340380d46005c1c1040300881c1c020004c41c22019041c0f0050442613905034081c402441c492031040034144031540700440c070a065010505c0c95030742c0f0640c1d208600341d0203840040c9080c1000d0244a03050020074020b440300d44044441c1345c20402c40608540040e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 885597904 1250 885596654 885596671
    0x151805010e070203030f041703070207140307030c050909160f080717100b010527120a1a0403091d041a090705010e12030a051b03040501140306040f05090f06 69
    0x60401000d5070f400000c99a200d200c0c5d0f00044120340b16480c004207160007030703640021310240120800c40c280b80d00040030000c6035610244590301014010a05494061900002c1c2c441c07500104240000d04005a8258000808408403220107581951060224405811a070010190034000f00100c070001c000c128060500e01d49918014440c0ba00344c01e42d61020038001002107922004200c1c0705a0291040d12081001c11a803120081d20031240d00d0121000384420b244507801e250300d08201d03c0c2000a01032215a406180300d40307c0344401e8800260140010300880801444540100b0b484244004003210320700f003003201032070906003441c00c032010444040d2005100c50410082004940d000143d510880e1000c0c20552005c0122602140700108284826501d031f1000151180e11194080024505403044840028840e09030480c0f017520382c42140b003424000755500000400c030380b04400003150044c000501c0058000401d48a1205131101100c20842c0d90304458110190303030105019055109100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 885599154 1250 885597904 885597929
    0x50406140f0319060e060603041529090906040c0e0a110a08071b0b010b0a050708031303021204030803010b03181b040e210901020712080403120f02071815180501 71
    0xc21b001c5062400000c0010b0441038003082c600300e01c45083d81c820050180f007494800346ca00303080b4140c4001ca43d42e00520501030303900440080d12105022403150300643d4042d0a0400301450035450032941240a0240d4402d940d413107070040c2e8141d240f00300602c1550304c2c0351035126480c40e100a0150401910140710301400002c856480001200c0c40802819215140c007440e07114601802e044890b0300803079000030a82d2000009000008840c2c040102c086c5100e80e00721086240044440b0700c05028900c00101000020310050200f4200113015644c80382c24072141e20718003440d1a007030502c2c000c100b076100b201e01070703840700941ca807814a4041c4090500d4881c0c010090034403828208a00d0700e03a144a2403000800c04250044568400d04c0300e2001400104200c044020003428084843c0c0e00603c0304a50480d016014090018081c250f0100c18402640291020f2460001002c201c1555044454000740d60b8609203000340b210500c64401030030302c001740c818002c112224068201c0300f06810080240c3c40b07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 885600404 1250 885599154 885599161
    0xb04170309210c0d0815041a0445060f0509060115050d0c200607020c0a050d1502130f08070603021e13090513031707050406140f0319060e 61
    0xb0004400f0428800c61822172991b03620401e08040303c016a072001a441403d140300d0725031241071070900f450012000c071410003903106410300403002c0555004040320159080080c3d031020f2a0b8940343c807400180d150340e00d01c4280c0525136a5600321204100300c072009a54402c10302034001420050036014215100440c01c820030f80c1c4a0240050254400500304551121012090f003880340880c6001943c03c000392140180780c41c43c4003074070f400c0111000d00042c4100381c514103240c0b4210315100100c80c80038140d44070410301e40c2c490140655099030701c00c850980810400300c40c1860103041e10300810a055030b11008904000200b0f04005056020b081018018005000d81d102ea5a01d46066810110001c6580c0e030100c03440c2c9070a10074241e000b051030038501820012010f80e2010503a404034483e03518001d4940d00f2410280e050841918820001181440140b081d18024000300c11120b1324034900f14104000014604a5540100c401c051042044115510600d545008502c098804051201072900c1d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 885601654 1250 885600404 885600427
    0x507142a010903140c031603052a010c020f03060709050f150306240307030207030806030105010e070c08040f030c030b09010b01050702040b01120603061b0206130b0417030921 77
    0x2d050b01014202c40c42c0c02100b0b80c2900f0041080a56130140902903644155112460269500a03440140c42c94010b0403080c1c40d034840c51915810b0645407a85844860500c00f00c01141c01000200089802c44050400c0c14401e55081010500c0b4032141d968a184150803e4140851070031101d038018004d64034003c0d12503002025006895110ba8107640c00307004214101d540740c05402441209100c0c0c1c04000060161059040c0c000b003804038081c2e100c6203010b84542c0141401c0b01c2003485446410b089020210740d03071900c100462402a030044c552035040c80e4444801315a0000315a1041700c82c0c4141c100104100b02e14450020350000b204402004595100400a80703544034100b0003d1045956070000c51903a80540e070b4107501000e100a00b000100d440c0e2030540001c00803507c051036140c41700440103106500c009055841103848413004c403c180866a100d0014079800f41045072219a804182c0024420843c0998800e54410006140041081004120318240c0c40c42c60104450308019000511 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 885602904 1250 885601654 885601667
    0x20c030a050a060c0c06020706201602010807170f06030f070f05271f081209061e03070503060f0405040203031605010b0d0311060c03190902010507142a01 68
    0xc0e5006600811301c56105003080360300d0165004010481c6101250310418002643c3c031650345551a20f42c4030070810391200726203805000d40e403444002100d184501c0001940b16000c1c0540203d514180341000800a00490952550885802d00304861070000c000c141d281c10085d001c1f00d0f00b140c9014094050500800054540035801800e0041d0350b1000d0b240d41008140e00b0940350784032072009000050a2201030400441c40c0061000501d1032600008615910040303001d441c141a10f122071440e00005605210294004201c41c00c964030364140300d000d4490048000754440d002596807140d681c079040c1c040214000c3c000501c903008620f08000c100040c0c070000101d9101c00070078400c1d0300e61507082d85885405803031046202c40c0c1000c00315500000b0190801c82c6414000185000d40d03ca582d65aa540c0039503000071150341543c004441c481d50507103049130b07000b801118010300d0301a00d8281d00ea01d40d410703601007442560b840396200c052148108c01440c05055030541e407040c5580d03036807240480000e118 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 885604154 1250 885602904 885602923
    0x504080d2105040b04030e0109080c01080c30010b0a090506031005040c02030a080a0212010b0c16060504031b030201021e0a02090f0f09010903050d111b01020307020c030a05 76
    0x920403588184041038501407403582007048001414840c07454285400d050310441139030201c012980490141c0f15a40c090705240d000c0e6507100c4002c240d4005d00c030004403050003000d89440c6c10709908104804035400054110307000590669103450101b94940b10303070703007514034141d200b030140400902c0002001039000b28544100da004981964617911003440101040190340d206a40c0300b8600000502c20036001701c0544110704071a01c3d0300101e80d0f00e540d03003c3c00340e01c9004d002030142d81902c0014020411800090145240c10700c1c215200c4419501107185106842d42142c808900041001c004122045406040003490369684c3c1c41028910f5001075505c1c440c400300d4070041c04503038560501440c4200800002030390001c00080c03980c2440780c8402d00200045d160514200300c014005030100005000701d40915501d0768401d8584a140e2085400500111001d4180c000f010003061a1800b8409003c503024001c1100040c4d49041000b0042d191403202071140d8040c0d00421020000301300301061710510b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 885605404 1250 885604154 885604157
    0x150705121627090f0b0306040807030c1725050d0e06070b180d081015030f0203090c01030c090f0b030709170109052b120b0418120504080d 61
    0xc1454110100396000341d00000d008a150080e40c201246a0016044107003c03208000b404010791154a1142c0080e2041c00380040d0300342d8032074000b00300003420580c014601a03009150401c91507c142e17441a03a0b4045000440444010200300454060703000110092944041007140303101c0415950381a440c0c234001415075003071006115202017a80c442c03204460b40b00d503125200440510700030504040e2080514004c4003144154401446054003540c20140501d0300a004403040903c0c0ca41c0c00c401361000b403401101010b45a00c04441e81024034001b07580501c1051001d440c10308901e40005040320a102c440e0030420230035200402004e20f8030300c054000d4030036402c0380694030307510088181e408084d940e00c4094404020301080c5002c0d1019404001454800c4042d40c10015096020f2104403a0501e5a891444442440d01c60703120300411070042048210f010202c0c00c1010341c0c000604803603009032240e0040c0399042c1190100301e10682203819030003050428501782424009903682e60f601580c1e0860 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 885606654 1250 885605404 885605431
    0x13030e09061c0c0e01142409040c0e090c0a120b12060c040e01320a0305030406020312060402031e0a020d0510090c0e06090103090c031415070512 64
    0x1e510342c4925200103400110428200301e8484140382c5160070004070303c2030a002540000000c2090074140c01039140280001740308040300400018919203003180900e011038038200c1000400300c00c4e142c600039075401c0c034401e4882100b80c5845401780000a130b801060850301000c03c00400c1c25141c1c110980c242c1d0205400c10004040c101c860200b0703480025200428141d01c10300040120380209080100141c6403400c0104201d80d1385c2c1d40c40c01c54404815a064901100c01902c1d402540c62030100049005d080101440622a40d0f034445a0455019401c82d50060b040000c060724410020460184c100c03105560071031071450240700020014154011032600c100d106000306075101902d405884e0051f1001e20100041e0403e0301e00c2490360022031041401d241d05001440110a0007406540f502c100058801450b100f500b200440040c003013424100c0d0720800303400f0b000c400700300c02650440600d40701800500c01121200a4406241802040c010030030008100250490520000c0550092100740001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 885607904 1250 885606654 885606661
    0x10309030807050d0212130203071205070b2d03070e0f0a0b0f0f03281817160503070204050603032805210a051506091c08040f03020913030e09 63
    0x1301e019100b0042032500003c13203081400105054201040051842102240c0c2ca8075508c0200409075024080060f0242c0c010b148100f0030000342500500e14a00c03500c007a02420729000041400401faa41e501c0f00d204e107808000c2007000c0f904901d10f2007a200c4207c4200f58514080300025404090030301800888420115030f242c01d622880c8141c504200329903c00303540341c3c079084800302c0d541c0c040300c5200d240440c100c11004035440307404c0c0b1035103405104284402809610300d445110500d600034001c1000320004100311302c0064029003400481a00c0b0710041d40c2d80749101c8c01000142e85018003502d210350001c0207100f29240c10381c844120030b1001d0580319401c0900e0103005490034014800d00120300003410350345201082c512485207106135405401045591a80b042440c441c00d001d044c49078110108100030360381483c1c0002c90300e010180e080c020703040004150795000010f401541c00031020143c05030b0f062045280400440343d00c00b5168048040100381528014aa604400c511501450003400032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 885609154 1250 885607904 885607927
    0xb03060a0c0e0d0203190305090a030b040c0f320d0c0905060a15110123190209030312040c0b16030e010c020901050f010c0b151905030a081803060a0905010b01030903080705 76
    0x342c842e024001019420800c2d98cd082c80d107000c00c811a801c03182e110000d4004101c8140d402110b1007540c51200880c50680e04030000b0401c40c07101407400d0408021a10303100506a501c4140e8000040d105840c0f1070002c41c50900c0710016074101400385172041c5d4407904244800d504950030120180094582502c529005203078140c0100101c5006c2c03c18210a10288042c0e240c2c038071090340c00782d81c00c3c0400310100515050480100d0003100c07a0f0603419081001402005e0f4990700c20550094000c0e440105500e6441001d980ca960014010414554900c16a04207258020600c0b242804080c240140701001c02e90000300e400c601402460f2064031841e480601c180d01c42e8412003c07143d032100300c00381c4c3d506068046100800c00748211b40c0c820b0800c142840a900e80c244100b1080300c40280060500d4540c40e91882402d4202ca101c103180040a60a0200c05039000c0100c3c60084c041d003080002c50020504050303081d64416442907051504141c2c818002960201805a2003045403516030384a80035403d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 885610404 1250 885609154 885609157
    0xd0c0804031e02092512060803040311091003080f18040c03020405100504030503030a1e1b0f0518100e060403060b010e03060411060d0b03060a0c0e0d0203190305 71
    0x140c48262001040004640a000c1c0c140c0018001c45070344c8610b9071000365036892400d441e448405000031004207601c00300e0003150300161a00510602150180d102c03440b403071950304503902c10748900d204080304800d80d0510301c44180d0021061040c4405160550712001d145205841041d03001120004101c02d0031240c0c0b0f0311105a17000c00900c140050340ba200802400b941217400b50610450001981d545001c2c050713000c403012254004095404c41d520646224020100c44102c8448504403041d44501c212561064005080e0541020500310303800c03550040c50f0744020b40c01041408020840ca446d00a50340c0c10144140f40121812025690502c40c11981c455000d940b141c0c001c4030105001c000c0002c2074026200300e22007a40e0b0030319603404100c1010b039105000c1d90040c25150008603034100c1c4d03040070801000a03213000200407a0410034440480d180c030004603002003019694140e40b9085941c0b101031070840082c00c0705e0700b0001060719000691103400100c007245818013410003a0040500800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 885611510 1106 885610404 885610409
    0xa06080318061605060412021006060c0b060a0506040314063402151602061f05010e120102120f0c030f0408070203100f0228020d0c0804 60
    0x3014410683d00c02441035540b004501c02c248080740d01001450700491064140403090901384400905202804a82902c07035414084104a255407014000c0d86080d007158081941e5100d0078001041d0f007050b0b9000319005100401c0000a01c9102c9096000c6802100140e0b142075580060400c5500d6042c081507003d0403610041102c0c02c050300350b0340340c5e802007140102c503038944081c03a03110022031085510b5010b40e19010b58134503000f40d0600204ea000b070761250410019068607160803c0c002018000e00341045402660540c2c01e684004200b40c038086480001c65440c15420299011031031700311940c0340303850480c030003060417180314400b00d17403241001c02d10300040d40c0c075907598038111580402400d0741d040c03140d00d5800400f44401e2140303134550b40c0f2420005985000821003100c440030710031001c05070042500b88064a16402146504007a04185040198251b0034a401c00c2c00b4003840c3c = true := by decide +kernel

theorem cover : BRFrame.Cov 885431654 885611510 := by
  have h0 := BRFrame.cov_init 885431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 885431654 ≤ n) (h2 : n < 885611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
