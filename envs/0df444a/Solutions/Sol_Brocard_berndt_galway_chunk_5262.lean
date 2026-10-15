-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5262
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:16:52.557302+00:00
-- url     : https://prove2.me/submissions/a3d049f7-5a72-4f7a-8634-a1cbca9e4962

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 946223021 ≤ n < 946402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 946224271 1250 946223021 946223023
    0x30703060f1409030d0c0206010f090e0703080c07050901061112130f0b0307031422020121060f15021504020a0513022104080304030f0221070b01080708070306241e08 73
    0x40c1291f55044154654500c1c200c40140500201d241c1c242c1503003703aa0011001404071005008200700740c0c0001c05042d4203200c240311100301c068110005000449009402400001403180072500d040560141c4650034140c00349104401c54008021083e482a4041006c2c440c1201842c810b0260396000c2c40b07058660baa10b800c1e5004180d8a1144039100b29840100c8904002407150002d1700c185001110080a42101c000103405654503402060b12528204440d00100c099180a848400040c0044001b0300e24003a5680100d5201040c020510400103800e5680c0c14003200001c000140460000d01c0e120b082c7c00d802540500a85010140c0c18154080c8010555a4039071003a54803020261454451741c038140c803440d005954040861240c9081c80c907030082007201780c610714524000e140d80c40f14014646001c0c07a0034143c2000c2c400d0f03031104800b00001c1d00002004411207421502c005210440d001c0e00c1001009c181ca22640384140c502d0000905603000402c0c11f82e000c1100c4c0702d1403640c03a01c0c0c010003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 946225521 1250 946224271 946224283
    0x302030706050604020405030d0806030304030b010803180102011a090c13030b0f1012150e30190f1106010e090d0c03140d060801050906041a010302030703060f1409030d0c02 76
    0xc8e01980032095030a0b00f24020001c00d50051402411641415a01c0d0740d1229010001d07080148290408110a04407040c9500700685052003400240000884820906000c82001c0b0a0034419241400401c1104002c0d4007140c031010b0820030089015038490502403030220098419820705440035001403c0c00c8181001d00f407c0d24503808081c1c4501071142c4440d958040007a040058403503455070700d200303032201c100400340f10f002812125040414030190f01d00910010b541310ba500c1818104400c01c101450501c010b91140c1e182d0401022000c0c1084044842102141000030a8407030540049401409080b40d44e210b242044101d070303a20034542c501111500741c45080100440d08449007a100100c034880640811449008001340d00b82d40d5008680c20345070142da8401d00c47c1c204000340005c1c02504007841c0c0304415401e48a20080d455640400e40ea40682e21010f403061f6503416500351b40444913000940c480c420036901c8805801c20508e1107442e540f01d0004811558607111904559500120316 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 946226771 1250 946225521 946225529
    0x150905030607081314030c070314100b03030a08090f071d06040c12230408030618070f030209040e1c0305090d0e15070c03061a04021204021905030a03020307060506040204 75
    0x62001c2e030030300316510f0480702072070404e502d15280400c1c4040c912091040040e1001107014108100c0d2b1402040c80403402c0c4201c992a000b03075a4100182100240c41c008101c0d0035504081c40c10250720366810700d196050000c140c542c001c550159900029650001540d01911a101c44540002c1c035151081080101c07809046000c012500c0c0480392442c0b08910ba2120a41c11112a101d00d200800c00d82e140c00d003503408031411590140080244209410a0011940701c2e04c840124507545040108025100031080a8560101a000221819242c80b00e4001d000c201200d501151139103141400a04040f56080708480002813a00c0d001070700c0d490307000800000301d030b41944400243c2d4102a0600c611160041490700707214800300005000101d14198103001513010742c100050145180c1c49140810401c8144c01e0b106600600c200303c0b04501c01600a41c00c1a0304507050200011212170515410b02c180d8001c0d076141c020226072109140c3c02000411640e489682d040150f1354828040004900071805 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 946228021 1250 946226771 946226791
    0x405060402090c0d1d010b0d0b01150c020a03050f010b1c030c02030f07260601060f03022d0d0f063503030c070201032306060a03020415090503060708 66
    0xca005800c094540300d4220030031110092611109000820a5a200004044400d444401c9490340d8010030303c120902248200e130004c0d41120103403501d12480e1010300600c58905202c901c3c0300c18041c003071800300642641c0a0413041a4030350380d06040307488444040b10b4220a50034103000040c645006140744140501c0503100f14041c03903058400b00c80807124441c080ba00b41c4603400c03440812b9542081250003d1450384500158042a01034100d003a0f1581002e0050941c4000010b0003150b400804d0801d079004103150050307c404050302d0010309212602c0300c2d84245501c5841a00b00c0d003000e4001840000801901808601030711a4010700f00c60a52007a802405a0041246510320300700c5011072100040c0d00385143c80c01881d41100303085907c1501c1e40b8001140020b503210855815004a2020011030704595584028802e00301c015550700910785446060002108840580254141c1c0c0c086d04040c0c0000c0c1c1b185800801c0036002c51804d018240c8a880340720001010710780301d00c00e104e228000b04c035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 946229271 1250 946228021 946228033
    0x3100603080f0a1b0609021306030b06060319090c0504111608030c0403050d021507030c0f12020f03341704060b0910090e07060e1003060e090a020301050106080405 72
    0x300d107542e01034114000b94420040b840d01e541590a5a540211110300e01401e80024900e000b80f0401401e100716102c0c0300c100c142401e00400200d25800314080c0d000209803006692603480055106415580b0701c240300c10503291004a00600c0744504a110a417141a03070100312481030700d4074034903603801030907800d5078582460044240060f10a0313020315045241070360407506043d10303555080d0030040c0451440005a01c01d101303240705400400780013500700300103050030054a62902001010580ca40300e80300b00380051000c1ca2008015182d0480300c40703c0e068a0406d40740c1c10952811501c0c291542500c84c02c03141c00c1542f200350f04010540ca086040358980707403052000c03024610344615120080c0190b8000f40d80b900040e072140c69072030b0410b105400200b444540142010580411245001081d64840d0b00000091080303e401c00d45007049010200d41c0700422000b07400003100a0f10b480e030000c04250000301c0601084a40004408685c544203c009022a030b03244d2030100c40031002100c01400a5100c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 946230521 1250 946229271 946229287
    0x405150a150e030a080705010b04051312021c020106150503060d0f0c05130b0a080607090306050910091b0e19050702010e0d09081603080a210f0b0310060308 69
    0x51006122404200c2c00c203284241801c030300280c1045244401900c09200000d00d0908002c000c0c407920452900c00c40d01084241000301603400070f070160400040081698028030880d10380200040c412048a00700f520b0300381490090028007801744c900c074600c0240c900046000ba12070140d001c1e00d2103904043d06e0343d40b0440b055240c00724201201841510100520b4034041205d81321442440340e4020910000300d40001030b1011b22074081c929500416082e08034400b03002a061303004260300101c2e5000320010410b6100c1489036404c10b12812203185400d4906180e5004009412498907011b10106030801001983d8000aa422100403200b01c2c0b15003944a0034078102101c944d0100d80c00510510000503408071200c40c0514004440302100301003031024804111145040151301482880b0801a8515030b1451792091842c2c002d82c4015400c2c0604d40160030743c01161100080210b039101b82c0144954030100c00280000c0c00c844050074082d02800302008001c1c03009010300000c070382e40803000901d4483d00b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 946231771 1250 946230521 946230539
    0x909091a150409110f10120c03020c010603140f031c0c0e040908030924040f031107090218060720040906060b13150503070c0212010207050601050405150a 68
    0x2009006241e40c14006440856644503841441c80d8540304044041d0849144000c020890003010b411501c00e411001c1c036619040d13404090301603585584000070800200074902035029029182e00d45942c0e42c6080400010702c0112011040f05002c214159000032200b58401c58492250001c81e07240d20b621001e134086419016440030040034904d1030854100542c1c0070004003600c10014040d00c42107004030a011a400d800e10000798103480e00c4850710400740f0002068940702c04010307c040c0c52404011420f1040c50700a0001205481c0c41c40c098607030003500d60f11518001d400811490705c41d5403810b1040e0f44a400d01108039405150084400d28040b41110180c041c11030000c030b042908075403503580c00d00004140f4000d0401400c142d9501c29160200c60120a640020355445401034110f603090440c5015000022603400152915005200c40c5aa001003200c0e505021440d1120b503100180a00a0040114016050350f600b01c50602280e100d0a44c600401c01400c0003c56010450302001c02c40790003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 946233021 1250 946231771 946231823
    0x50f0a0f12170a09090b0109140603090f06040f05100c020604060e070b0d1d03040e0f06060708070b04020109140303040b0904060512030705101509090302010f0e0706090909 76
    0x486072050a00800400c0140c1e400c0b6005100203c0214101c1001840008101d00400421704001c0ca08000b5040c94106c03d1280b07000280101d0340a203600001249170948180500444c518501c0c0440340e0f1070030310349486981d01d182d03031030282c6590041c1c2540c1051074220b405410550b01881c0d00a02c10394645488050041c0840c2c1111803041c0301c2e0603800600d000100001c0e240c607024110000030701d901c0d8110941c1141d480c844110700a50010007050000c0d4207030f1100582c02840591106a0390703551040895814815614090560000030a0354020482541c3c640752041e4400c0e80c6413180c0702c0d41c0c1c441c0309400320001c81c0740340d9160b001880140b14290040d40a002c540d0b178028000700b00c0e95a2a0f02160300c0380c83d00c1e101811245c00004041040c00003c2246007400c40c3c0025040096a070700301d601000c941881d005600740c1030780351018041814800d4002e0b07540c084980104000d010741240300655520b24500c640400b00340943c10006d01e105c0613204176005a0b41201d44109141d141c03140d0002104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 946234271 1250 946233021 946233023
    0x9060509150a090c1e09050705070b0a0b241317010e150a20070f1403070203070b0d091a011406031603050417040906050f030d140f07140601050f0a0f12 67
    0x41005c2c10300007011215030080c00e000c1c0c006030700d6a59940c525030038081100040280030741307042c6080644072081915040c1c10f200601041c6602009c0c12625500d0711a0315108488104030706884101d00801c2d0082c042601d004001000d0740208940344401200a8a4a0038501e480c044d410040c3c00207102690141c0050041294548441100d08940c13000750150390002c95080d41c1d0a0025500c8508024083d071001c2005480200258140f07603845c0c1c002569030145020745030800801080e006400c1a1607089034152a510581050f07030101003a0001800880c24803440741969202c0c00c0241840c00d08004a9000f04441454400301d8114414180c01400300584121041c401007140d89244c180040085c10181044203000300d030305443d01003002108816520802e110750486a00b41c421542c002a481100204640400380c80720800000c641c132500400c54040e100e19040b40d4401810310022807032505036802110502959540c100500003070550b46d004101950800440c1885003203d0115080685 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 946235521 1250 946234271 946234319
    0x70608090a0605010b09190806010303200d03091e11040218030a0c0603060e0c0a0807030f090812010e0f04030302070f08071b0801021c0f09060509150a090c 69
    0x8805a545600440f1070036800408200d5010904400303503d0005100e6540c0a954524044941c0c1001415504c40106100c01014800000d403400111513080044000000034002680d641402d0008080c1c040c0210110032520060300e121a40c1c100b100f00040e181d02c3c81c1d00065921021441c02080c440203610000d25481111404420141c05a80801c0700046451041448038001c1d0b24100c00a0180da40540200e00f80c10049800c02c000f078000d0005442c02603030325241980298941d92401c3d001000c900c0703070001141d03040012290501c81f041c00241a80d01024003100210703a60743d031545401c03030703410b4400100d80e00b40c010220340030070f2194000d8440c03e4011905094540301c0c990350701ca8141c0c0305510407100980c0b5240d50110102c0f542c01000010301006009524080c0d0505212040002d10100b0031a510303660f201a0154104503072140d110b007607000104000a080c4079180030760b6100c10259a203000c4140d08005000170340d040c0034004800760f106449030b400a04041d894142c1180102300d5484c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 946236771 1250 946235521 946235533
    0x408070c081b131116140105011406030417040609030b060909070303050c03041806180b0603130c05060f09090c0702030a030e04020d090b01080d03050417130f090f06120507060809 79
    0x3003221080103140319144e00c034400701d00b07000c51306c1e01c400d2580c1c2c0c007112944107902d40001007010250120000e400c01c00b0407911700e41c0d40d03922842d0040c0e501d80d5025103a031100001190218049801050a0301920701a43d0b1085455942030704001e40ea00c1c01712410003240d0018481000002d026401401100e00658107480c1030a480b8003422070072600c003007034080500c1d0311000c04118055001380000f28803410075405110705201400418140d00c002350601d0b8800195600355030a10151030140c80103008010701d1590307502000e0212480b030b900481201403080c0001c01c082808d18403184100c5501d20381c05405042c1c03000003a10300340d6032020b4641d00030343c015030200300700a14015a0710a2055041c82021003040b00c0d4106101145480d240400c1c4800745030ae090148000708001b80c51800e01c1005212049907140d007520803180b020601644680442141c0303030070104007824103410400843c01ca00c0b42c00c0014941d102da403600e500601510191460300200b6080c01100d00c910131640d8001104803c9440d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 946238021 1250 946236771 946236791
    0x3040302370303140a1d0f060309030d060e0424020903030c01060303030606050f032d070206010305100504120e0a0b070303020304150c17060112050408070c081b13 72
    0x224400841500c10016103150418000c060f00700e038a059601084e2042207040101c03401c0c000d004040c404240c00089100780e1062201c95655001c220104800034203025180d0a00803005076403a04002d50b00c60500c0d003410400703e8110360b41c0c14210b1041e030700041d50940c0000c0118418405c0d8446910714401103400f00140f51103070720708200070300c9400202c800000d049031943c20b0040c00c44940707802c00010090100b10a0104c0301c1e044040d20740148241c981c0c20450002100c0d0a00401c4016000d04207103a240790030090081d07004030b0018103c90040064036007104411803034000302d40302120300034400c2000300c01d1070116a2003400c81d081031503009059608202d844a01c20030641e0000801100026000001c00013001040341c03120014084044051080759216880601040010f0a07100400c01080d000500542e1181c080d04076413a440480400c918106130a0502c803640c4141000c0d01c0b003183e00301c000a0056800181010000c000c040002010030050013000041700482002144664590495403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 946239271 1250 946238021 946238089
    0xc061302030a140a08031e1f05120304050a03050616020a031d0a0b18032109130b0904060911010c02210109060e0a0c0e0c0307030203130512090a0e0903040302 70
    0xb40c0180841c0d01c02047e0400c0c1e003640e03904040e200034444003074030700c1c01c88090b42074041c00b41000c070079502c0407290303510a005403080032403450099920680c0d002d62200b07000014040041b0781d490140c540d091201170481104641030341e85003011840140040c2c80201d0319070001e00202824450100001c0c130703422a01ea0348804041c8190070106604111340341940040b051071404000342c034014200e030100360b00c80c55102c20450b00c80f8000c08609a0180603c0d058040c481240c42e4441c01100c0e00c02080304115007014101078004103009a41250424a08007134807020f0b6009007109042d0301c4c1e0082a141c00d051485480a5181d000900016015034031000807200140c11800b50005408400d8020020400903081402c1098902d0344001c0410100b41e091101c03101c06003013180e6000c182410003503a251940d03960005075403007000c00030b03100303001d9001103c0d03c1522000081c05d2150f030842c0c11141890322481140865441614050703865801000104014184403e031006480c41d0b000320410308404900440d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 946240521 1250 946239271 946239277
    0x1020c011e0c0206010f1502160801052415160515151f050708040801290a0b030406050405070f06080708071707030b0a0b0d020c061302030a140a08 65
    0x14804401d040040540418420b110701e04180540303100900982d4074005460030044898000c503128140004c1c0c0e5030000600030414181c45001c4150b00420700b031356030002c207402031000360317181c1c0e00f569810748010362240141c80100c40300410040c0000200341c92000740c1942c5600061625114200006908010034420b00641e011403c01040b0742c5114508141c1d8150104d440d03d018501c17507264008074030081c110010008011201d903041199440c8a1810954043d001e01da00000c40356007400542c10300103041ca022400381c91020300c1c0c041460b030480c4040250700d09840c080c0c5014114280001001b1030265001070750000d0185042d500c0213a00ca2403800c411010907005600403642c54818080360a501c006516406a5a031519015107980a00600d00058015081004041c1c440070051b0300740d235036808204010a185e8920b281d0340d017421006000a5008603907402c245010b10b000065095403032200308c1c40180d50040140c681d000d010340d04ca208006c0924602c118034441c0f101078400041d000002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 946241771 1250 946240521 946240541
    0x1b030c1305010e0105040e0d0c0515010b1201060e180c04053c0f010507031413030203100c0c030c06020f07030e04200a030c0e2e050405010e06090301020c01 69
    0x1c5015818150f0b400303000d0380c0c1030340107900491070205261034100e400702d40d22030a80d041c0d10340080c038080c580c00c1452400a402403210040e907480e00000541d11f0241008048060394401e01020580e41e403070040c8c82d00b1145500503600a112000c01303020030390050007034541c802d600c21907480c00c2649800c08900500961031034641a8100320051003000c1c4050950b0000c541200050001d03185114400310b80220050b2138400e045c4600883e502c5e04160090408594000ca001003141d2503038a0315403103503c844400e1005a00134011001843c510b100c09020304420b0342001c2d00d56598a201d15138084681450016060351256420300072880e88d080040000c00c1c24601a81d95081c10441c0344c41088116078221003800034410381c00d004801c48007048030070b40301500014100050003600e281000d0340d07c0003808102650011828418a00700020b201c0d003144d29031120dd01c04202040311180544042c895401068080f840420320960700d0320300354005107a6032401500242c28001000c0c4d0f4682500c2c10791076 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 946243021 1250 946241771 946241809
    0x1806190203030106081b040e040602310b0c19140304080c0a120b0601201903110d050304020d030e06070309030215041d09281e051b030c 60
    0x420034107a10203185da030801115145109501030201d00070303030948128403484e1312469080d00050207212040d81554603403900e681c9080f825400c0b00090510f0704a0004505d0b00142d045c0d10041040e0b02442c094030715040c10603000317043c0c0750744400c0b001307000e103d2030700f41103468503900049000d8135032050020b40f0080c4070009c001c14030048100104002d04840d83c001c419203810603820240894003554009410100a003004921400095003c0c4940b18481600d188944202c81200710a181403620b50441c241c025134480c40c8900c1d014224035203801070788a109000410a1000c100540360410462490b140b2034101481c4080707140e0003240d101d802c203140660100340d02d00410001d606080141100300e01281094a1500303041643c2c5110990403036a100c4110701040c030010700c664504000c00c501d40703034801c0052080829509041506072100304011180303144c0d02140c4410500341107040303140455106000e80070201c0135403c01c10030008040032442d411b11070f2100a07403194480100303001c0c9540d0580f03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 946244271 1250 946243021 946243027
    0xd02150a0906051c0f0617030316090302090103030f0c060608062509030f020303040b040305030d0e010618020307170a0b040b030c0117100b0d020306030618031806190203 75
    0x2038000e4032145107030380040c007031040400a40d16003003800e40c920300950518050010350200703001c900348001c0c103030343d0002d8401802400c2c003e02c0d080d10000295104100c1d0300400601c4a42d00c443c100d4501344e451100940012800e001400020702450341d21b0303c0a041442c000c44800c00503154a03058400320b6001d00102e8100c0300034054884401010340031190f9842d01400506148480d00034000d003040d2201401c28440d005810f0110741c0c050080390010903107400040d84480d01ea080250b1a68080703620600420301d4503540d82d100c550180524000c4908101da40b410404400300b80703001944c030081c02c420801c119403010308042030350f80c82c10b20f02600b0000000100004e0041c2400100c0b04680c030943c1c801da00120303a42129a03803220814030420500c802c02441511000c00f00c0c400600560069203010760b000ca040c21840340340da40078510030b00c021400c648283c0c41e18154401d0460032205014039503042040304c2d1b0700944038008011000d16001e080d16182c54003003665085102014000100160800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 946245521 1250 946244271 946244287
    0x106020f070e13080f030a0b0a0906050d030c030e040c08010602010c03050108250e0403261e100e16111c0305060f0d0b01030501060602030c0705040b0d0215 69
    0x42001550800c440c90061081508000301000b2404000304806043c1e02e90320705440800c203100040e0f90518518441440e1a41841000803002e0400e82071003500503a0305040c0061845094040e0100b110300c00b42c42c2c01c05403215500c0031900300d4044103094090001e190f01043c4d030303078a551007282071508180d90f130345c044c650501e04003e080d034403241c6a00c41054148801807100600c0440c000d000315695184400040d00c3e80e60756000305480a500105ea040704803010041490b40000040c1111208050045002c0d9022141c0d90b10f41d050503255501198814910050b02c00d2039841c080390803680032502d450b0229990300011190003400c40d0000c45400d140340b081d01c2400d0300400350010342040303c4080c20105007000c0c00320515540c41c0700740c4002c050b1a400455500e80707860b6034003480c0c000060301c2041ca803403017401c01a50740b28080c48112034541c60f16000040c1d640c03001c010784e0072170001003018020b45883c00041101900d1a01c0c41035511401c038070510f00040e41e580c030b460881c00c507100f11601d40310048 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 946246771 1250 946245521 946245523
    0x18050405120403110f2101240311130b130e01050708040f080d02090402042d1a070501060e04050f120a09090f0e1603020a090e0309100e09040308010602 67
    0x4207840e03207240014188814400140501c00703070b201d440c0301581c00100201c21000051030340b0b00c00c01d140b00e0481c40e0000d846900101c06411024010200419055041501e0951518001c20a11001c1c000e074a1340040b00b14189001c4500701c07003500d107464000c04c5540102c3e001481c2881d1408218001d0b03a035400b03900340d0b442400e0044a0b4480b100e4142081c2c1d41c0f41940354143c0c0103003140c6006240c800e0014000c3c034000c4450f41078078030703100000d0421911036131a00600b48902c4d010300021240c204000347c2d5050080c416980103030645210f1998030024013000050707020217400c41c050884603552640c10200700c0c24800c46c0f240344218081c2c00184680856464182d091400c004081010008100140e44880b90801614002c5410482c000194800503141040c000c00160007454154000c0d8520740c1c0d8070868460400c3c060f00d000700c40d4000b00703540c1d0b00265022104038584080003604180141c01c020300d0300266202c4250401c0c01c2010000d603881000a0740001e003102d0490115042000604c4984c0d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 946248021 1250 946246771 946246783
    0x60302090604140f250e0111010507020c061b1213080d0f2d0f020f06060a031113290301050702330f09060c0708040513020418050405 59
    0x80e20104210124040d00c8a040000104503282d804010300200b810540032a80340c84240e517160303401e02d0540300aa0310007030820224141c0c1c40d0008004040000c0500010b10846005201a40040211071800c0080c40348a42200d841a48003c100b9640b0003103240c0148041c0c00d41c8821100383e1503a8070b03c00300c1e5050307294469400240b101c0e4000704500303140c0b42c1c202e100c12011000b9420000f2a4030741d80704006d520b101401d001400c003440302c0f6018400250700402114505012502928421301b4800c544076561001291940d074850030b146c60400c04500798103582c0020a402604940407404c07101615403d030365036000c1540a01031603080381c8150f1050060480a2040c040f0000c2c0085c7c140f45600a5075403598420004199a40300c03401c01c1111801064060141c1c030244018140786822554158200c1c0200c5400c0c40c1e5000d100000b8030110003041c02c545409610181040c1071034201014400346220f1201c1c1010360540c2000049000c11411403a034030b0307a181d03c2d03001042c1885c161425a003850 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 946249271 1250 946248021 946248031
    0x14010e010302011b121d041407091a09100302040b0c03130b0720040204050414041202060106020304031104060306021903060b03091207020f0a1716061403070c05030d06030209 77
    0x28000d43d0100c00103284000b108800c0c5410b00e8551625001086c5803040c1d401c0444240d517000b031404103a0044c050b042c100d103d1140619464024400d6501c1e00c3d0840c00b40305c8040c90003600c0100b00400c5c4414038041050300100744441c070b030040c10301c0d880d01d400e4802980308200074032080d0701c0400d0031505041c00c402000e000c3c005882c5070508003191665095041c0703800c40028250b1b08480e8400148079141d0341d051741c004000041c41440b056a03002c041c1642a4030a0b10207035400354010035040e900600002c0c429040300c60b00da0046140c680b03103480310fa40c1c1040c03000743c442d07010f51500800404078403036001900789100d104481601d034030304102010f012208282d1020071040c1d014001c21444039008107400d500c0c115000c103882da44401c03520015140300080b024042d803010414101194507002e84240e240c41d61240f4003140d95806a10a414410314030030b00c9054001000000200c04074003484020310b400c024603091981240c0042d90b41e460550f0030641244030802d980e02c0c810001e610301901016044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 946250521 1250 946249271 946249307
    0x6052e0506040902090f040501120b0105030318060c120304080414090402010e011101061a070528020d0312050405030327030909130506040b0f0c091806010314010e01030201 76
    0x1454540418428000d03803140d42590f0740d0119104809494042d620713940f49100400c20440c542e160808120242606081a10303001403050002c105401c0000440d10070500c91207030351050802082c2040300c03a6004061030225030003100401203502c8c80100c003440c001c91142c0c080645031b50900000c58400040f414070746208095102c20300005d80d8000090340403500b4280f9050500384000b0200c10302602d1950701108030074071400105140071040703601600c140e51150f0b01340d4506403920040c0008003038003000c4040a0020030304503040107281406082c014144a810250141e5483d084050101d403000ca030b05403247d41001041107800915848142101c2d60703014101890310007965222580d138010400d500d40a07102c1d007070210700624044c07804080346560110440d00e06141510705168464400d440d00c0c06180e1400020030050008002500c00070100a00195250184031520781d000c0c0344081c2c04103060540c1e9008c0440607404c461000e0703010f8810345401c100b007949903100050400114071250984 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 946251771 1250 946250521 946250611
    0x509040c031503060c0522080601150912031106160905030304080a06020f040f090c020615030c0f060903010f0b0f1f0806061c2004060905010309050a0605 68
    0x10304001c0c5800b0950f6040800010355a44c007000564892040c0c2000c07169160340d114044081140c104040d10680da0000260780c0e50344da1310411036014100798110311010035078803c001e21403503514454080c030440c040e281c82c0f111380b5600a84c0354144841030394403109a505035052003140c940c1104041e801000d080d4025460030b490548060b80b21091510011b00b02900001c0c0310140c05004402d40d0050403440040030364243e41ca140c0c0a00510501120f2030242c0540300000307403503409402c0128441800a07001c1d2004207070300810400c05038071051229511400c18441a150b40d2001d1003580c80702810400b0002c3c41c401c003403040240c070032001021a0720030b00c0c0400d040852140605855280c2402604000c0e11688030000011810b00801052030074250104081c441d02c40300c96000012603040c030312089070710705003516001c0101d4400d500508000c51510751007003005501c00d502002c0014010801d071201408250b480e0784c2541d009641d034414151004540500c4540804c407489070b925442507402e05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 946253021 1250 946251771 946251791
    0x30f07080108030906182d0a05060901030203090a0c12050f0f0d0c0317040605014523010611010c0e09060123031006111009140a030509040c03 63
    0x143d00d1050380d001c2030040001003180c0041d40c2900184c0281421b00604146404585207030b950620700c14a103030541c14a4000715918020b060891290003625070240a003841e2501e01e00054001c0d5001074426041482201c0030344000c101c0110000c0041c1140010408c0109800c2c10040d15044602e46480c0c126042100c0310106043c00040404110300d03541484080220076041c00c0d070700c0302580f10036800007520310010041000000e03030000d030503500345027075600d0304860001492620300048038003e1140c0070160061070314140041a0351440000084e00465500c4041202448181d141004840303000c8604005200d000d410551200d410700b5605c0c004c1007540e00c0000c006109c0782082c4885405880300c900811103c4c0d2190880e90030300f294400016044500c029607000003a48116202d442a20016802007685c034814030094442d000c20a0062111070230071455400100000601202c00c3c449038009500032841c140000a01030740280c03110f51700c8180302e100b0310041d6000d8800e41c008051610307071408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 946254271 1250 946253021 946253023
    0x405091905030a39081c1b1106150406031407030303230601030b010c08031f08070812180d060b04060e0408030f0a0f1409012f0a1403010b030f07080108 67
    0x11404c150045030016000f40c00b0f00300b0524a2241d01c40c110360964060b034244c0a000c07000d03008461041e400b051100303240b07600324004548241269000003103a401c8440465190160310b501660814001400001d040d517607a40c405601100601840003d80c10000d0b00308149a0103100d10360920508002ca0340c42d403200d401c411050403a000700294181035584038000301c5070344074030300d80030190380e0105a0b50380e641801340c1c540e40b020070a207006141840008501282c00503001ca0740004a4100c85d00400545450315408a50394011443d80901002c1c080004001c542d1448107600a40b0b0140e02d001034602404000d10041e50001d0b0045240c0360b400300c1c1070000084091040ba030b0b22000d80302d02c021803030f02c40c054044060702c10242c48804103410311981100b4401441c1c4268007171904980208404c44c115100401d02c0568416012052110210142101c0f80014000c102c00e058034030781012594000c0c4c03e111016002a004189411008002c1200c0804c1c0801540c0d0861902d0610103601e41c03401a0503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 946255521 1250 946254271 946254347
    0x50103051b07050c0409060f06061829040e1902120402040209180114032a01050f0c1506030f1f0b0409061107051908090405091905030a 60
    0xe100641c400003210801c0c00010b00c55105180c20042c014030100d40f0ba8200140075006040d01d0b101001d2902e900061058010103085a581907500c1130a02511f140040300c15408900780701c41400c0003034400000c03011100c000000d0020b4407078000c8103e00d600b01038000941003030f10403014801c02e920421400c80000261110541d00540c1214056612058070f800704c2c0707400101c81340e481120217a440012071422481c180107046400f083c3d0848040c0c91403100c003400a208080c42800315101100310318620743d4402c400416007600904034151500c402100d4003480c100d0503400d080303072405101003840054038051000c1210307098804c00410362507401c121368411318a040d80e01900100e540e1065940141c807150852a41e82c0d030410006c0000c0f80ba1202200400d82c030500c01114140600c1007102d007441044003000130801c0d001000307541016008014000109800b8090404034400c030000c900a107400a00d040c40154400c1001d9900c0d2002074401800d081500e1500400690340001c01c0d03c2e007400c0032100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 946256771 1250 946255521 946255561
    0x24100f030b09100905011b09030213020f070507120c1502060c1308060c03250c080306040b0405090d12021204110109031a1905070c1101090b07031805010305 69
    0x1d180d01c9403940100b092030301c0340c6010b102402c20f00f08102d1806015044d0300020314000e8041d454001c0c5281c08008903400461408000c3d400245009940e4142d005540030300b002e121009201071501c0c000341c0f11140742c004075a10850290107440300210400401c0c1031150700801d041e00b000c030300104020074041d440398402442d03106004804141c400300020201014070007490850300380c034a9400c02d01c55003811680100e0f0780d80c40550300d00388421211001000791a003500c0280d940e01c103004e04a0399810305541c0c4040c20300c030350041d214081218160f41d9841480d0107a600e10000f03000c1503035949000b600710002d1182c1681c507a0700c1800980203031740100c0d6200b40e0041c0c0c0703d00707900390f0b030b00b03800d00140c4440f81d6582000e0042412400743e003000320380b4131585500800c120701011500260824181003580e80440b8000c00013007042e0201c6001481100c5030040f480c405040182046840f00d4085000d030b04228400d4000a66480d00c100c1c0f01c0c0a6600f100c2d01a100a01c2e040c0018903040c880004044882c0e50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 946258021 1250 946256771 946256783
    0x604050c0607020108072a060e010c020a05030a0e06131d060102071a220e01360518030309030901180303023003010f080d080106140a0504050324100f03 67
    0x7061910303603941e40e0501f05003424800c40c440848020b402c08800030311600c07803400d409600c0c0c840c0c60301216000003007888007564084000d500c1c241d0016011240c417605918440d401c06000e1040002010350344100601514030f64055940410f42d100e140152158094005130540d08645000c0c0615940749058040b2151001075a903031361884484443c044425584888000402005010071896040c28105041310046aa0200d0440c0d440c05068051110b00710104c10410303401114044082c81c0d0b410550f030007495079800c034074011b054664250a5600c1110303101026000010514050742e003015a1070702d80b000502408141506542e0042e5031113401203581020074000c200881241c0100800051113004611a80f68030b0707503076400c60f82051204c2402000d0300750041c0400241c030a489505100c0c100c030340c10759a2818040b00b036070552056600001c110030411000300000b040b41e413020022a0000641c00080c4601805500760380c0c00c441c10040c080f0050340800e900300700809000d4580c02e2082d40c0d0860 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 946259271 1250 946258021 946258037
    0x61814061c02060c3c030d0c0512092a1003020714150a05010b090f12032104050105010501020a170307031805011b091214011d0604050c060702010807 66
    0x10002607078034010761003c03040a00c80c0101103050003150180d00d0007107038845545d2026128940d101955810f220200c2c2c2100c41d40f00f400365042082c03a40e0802c0051131080d0030500d150040c802c01c84406d0040848402c000d56100d40e4a40c501c921214100307007000c1c1280c42d00c62405825640c001004141111200c20826801041d40c1c002d002c005105040f100440d402100d0502c000b820350010309441c11a0103800c182d1801c000065428002c1c0115500103d0060441c81e55010600130444c0b6403640304150f03d500d200510002104182e00c041e14040000044c0c104515481c0603c1c3c141d0a441c4140c00c9a4115000b49000e8000034200210102d01c0f00788100541d0b0b1640d0325082c0840042c2003000840000150a901001c02c2c01819400140200c00f00c1c040d5004100d40903205a408180f64440d85c20070240d107011410210b849246402c640c4007048001159101d1100340c8051013140d11044c01066803c820b051204000c0f0401a28a0800c403d80701a0b0030702e10036400280040c08010000c0c02802620 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 946260521 1250 946259271 946259273
    0xf0204020a17010f0608070906020d111e03030a150609090228050a0e04060f09021b0102190201050f0708040b0702071806050a050a030b01031509020301061814061c 72
    0x10a0207820b00035807410342a9403503940f05041202d0344094407903480451940703004a904640720340e03000d40079114035400606500d14100b200322046114031201044a001e1119010101e5201180c0720500d0303512a0010b60712410282e1f2040100c444015185404401c407a004100c805c0c4c000000c4400c442c4c045400586448048600840e0240c0c0d000c040c0089031000d0020240007034016015050310b496650380c440920400b80306000031540b00b401040009441390300200901c0b945078000b007405141d222515002410035a008a0a84c2c1018008010441c46850881d000030350910075143c0c00711212901000508040720045d1610a02900141c00a0031540020300098020071001008040c40811090383d0300b0b82e0300001004040d1402814411040010b0004051034866030180039a90481c159401c0780c0d10f103584000c0403500405288181c1921421f070440569002c8c0303e01c000800d5000386401007030b40d4401d911402c55031000c012100416010080c800184c9403000800e00c101c0c0441501d202c0200d107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 946261771 1250 946260521 946260527
    0x3070806011d0301021201090510060819020912060610084305031503070b1b12030c07031e0215070207170307021807020a060b13020d0e0c04090f0204020a 68
    0x8601202d982640c00040c08221089503800614100e980b446420031181c0c841d4070094200103800c1c4101d4000451a902043c0c0b030741213640c0f010b0389291840304018a0201b02da404640c44030b40e0080d0a00140d040f2030108100742c03c00113a0005440d05d5031074894420b203400e150001203948901901002c80710340903082207610b003004104003083c0c00c540d000c4a02d004000314005040d40c0c01200d21907003400300b5507115441400d0006010b01030790142e248803403e14503541e001c0d00a40d00825450805886600f000b040c03482c00080080d40100e071550b06260ba152024107014000102a0100140e0f0074020b1144095640c0d001c2400c01c01540400014401616591301c1240f400f1a41d410829000440036488246c0d03000000091200910a86202c500c1c016204032440304e242c402c4500b034000d070700700824080018200d42d00414190000074030001283c410400c1c8a1b0890704042900307140079984e44005415072400b0804411402c02c116800e00005040d555502550b0181e0300c40207019035001b144a42c10940 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 946263021 1250 946261771 946261817
    0x50906070c0f032006010311030d050304061512080d0c1d130209060c0a0c05030c09011403391009090f06080a0b01180501050a03020d170d0e0708030307080601 70
    0x5456004504c14509000c0300a865502c02e1004030b0340c090303100903da54182004250300186008545481d41950b03583e0307c984001d03002071810590b09542c54000400d6405441036202c8013140200320447c0c07202d646040c2c1d0801c4418140000046c8000001c0c0e01842102c2c1000c1d80410310700070b40b84040b6455034400e1082c040e000b030081556000c0ea003c90441e14100300040c5060030240200c44440e0215500c070249612660f0040070300b5001903000c00184000b60496140c0110148050201c0320b900085070014003c0d03040c0d04100c0e02400494112240d15035a00c4141c0d1001c4200440b00c0c01c025000320340000e40002440c1c4a82240f586c0c50f032440c1c06018209a1116004002c3c007404c1d02e4000300d091030007102c8500c09000c0d0070500780040f00403580032080c600c6401e06036040a808070b05107509580801100051001013200c0b802038499860503009030302e10140100100d0b034000802d08000e1407001604085868008102541c424010000c555034000b15198009000b030038503008420503c0500c02a5070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 946264271 1250 946263021 946263047
    0xc0a05061c051503012901050a1b030e040516200f06160908010509030904050406150905060a0608090601090504031412190b01122409020904050906070c0f03 69
    0x20346400c04000415603e56210343c24624100d0007084140070455210b118102d81844c0c001910300260000d5031503502603402032000d5030903400c000c065445890024200f007048032104900007140c43d40c0c1c4910301e00f458094980c20802d2942c03100510f04010307034002d02000000c0d603481c0d4909d100039140340c1000424402c1301440d91161003a0742c510718040000080e00480c81034040c000400c00c5900192070041840340c02c0c018000d04024529000c0524100703c00380c00050419605c05a03500d1401e441003001c0f4804d04e008021070340b80400c5a151510400c0048480c0390300440621540d0350822030300c03074000301d00e681c107460018a0000c0c2c03079129800c040700e01e021444105054450700040007110442072848203842492070000b240c442d0040c0c803050006841140c1d00045c0451074617192842040346c2c1c0e42007158030802c3c00308100e52049202d01c40b10300c07500301d81d4002d1031a558001034080c041e0504e0f000d210782c408204c80040400341400700c0024032150140c02c0140c020944024854200752041542035110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 946265521 1250 946264271 946264327
    0xa020411041211010905090f0103030f0e0303130f120b1f0b0f090a0632190e04050723030a021c0e06061906032004060804140c0a0506 59
    0x6060f440d0a50030b030022001c199010901c0e40000140e00d15020000b50302c5042003a02c0e0300320716443d641e8203803680381c28074004400307010140e2462020b030749082001d820401802c1d0500100c440c580b100294603140d40d030300080c0b0b82d01010f5491501090f103000c1c45903044000b40441642429206060b04159405900b05c046281d9000030742c0b0521501c0341000d040b40a00856618810f565214001ea80c503012082e0252410001c515111800440c40c1c10303c1030041d07003150016884d05012151000c800150303072403886c0c0402d52014041600d800c4c18030234554040e0b120f0600010f2200d4044041c21f42c580400c101c00d081d060004002200317900650182c03a09a1011010b0364a03940210345448080c180c4815000c07200c0c072030b0700005403992416611a515100404062419650424904601503c00c80007440c00ca00300a401d00845034149a00070001000380d9500c0c9030b000e0601d850030f007a03201c04e40080e4000c0c692100c40412450343e241040c0c507007280c900321680390369030110000980018080ca8005099 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 946266771 1250 946265521 946265549
    0xb0607150f180611071509020111100608010b0a050105120c16060902030f011416020a0c0f0e010f0e0a05060f0904030908150f04021c0501110405040f0903020a02041104 74
    0x119404220118860700c1160144030f00c055222051003540100e003406440ea911041c0b090417a260251f0100c280640180f40070008040010a910301e409000810000d000344c2da074208200c2c010084c41050b0310720070110f40201c0800d160100080c414040c240041401d0018040491011f451003030850720501d140100d810900c5c026420700034014164090168082e001c0c1c0005441039103018407a44406100d04011080303030b9110b81d01c00c0c403004030914181c1c00a52140c01c0003e0041910f01782014004d00c0000349545009040c076000120304041039001e039592031030500d0140815580e44030792581c40b10750004001640d0b5941800030b40c014030516050f40d0000580d406100038554030013046016990b81c04101c810160301100c0c032a1410804030f0710b220848401001081c010300c0c14901d0800300000a440310764a43e007868950305d00711407001e040346052101c0050b0400c40f0341002e0203030300a03003100650100701d102c0c4c113a100a9100c840c0008020310071940e5103244502c0030302041c1607401500c0c0104d04006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 946268021 1250 946266771 946266791
    0x1e03020423040606061d0a0b0a1101050f272a102a020a0e04140715080127050c040f09050103170309030a0c03031404050d030507030b0607150f 63
    0x742805e024540c00100840c80ea10000d06104d55151003100010b0f24010000b4030b800314408098004604440400089144070b4501100c2402054041c802c0003844281314240412a814020711126810b00079080385101408048004601c2080d03c00c1d44100140e81c2c0c40c50f490312840040d02d171301451503000c3d0050040008459020fa040003250000070307005495100210000e0b0044a044400254844100b01050202032101c0b4590b50704184516600400c0300503800019040c901a07400c91042c3c00b94603005072140070f030f00211090040002040b0f2546140204a98540f425a840403070031500340ca84011a00403c000340031a8024103425040081d0307140c480d003a40d000380100384001d6915200980707c04249604503011680200490b40086103040203410080c1d030500030444003030f41816660600b12020022030b8901600c80c91054000d00750540302c4102c09011104080c285004041c0b511072405103580ba42ca040710005604500780c546000c503610303003120141000c5441100ca4505240342c01c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 946269271 1250 946268021 946268033
    0x30207060605090c0703030f0b15031005061809040203120a030608070503030405011e030e03070303061503090b0c070c080d091d15090604290a1e0302042304 69
    0x51152040c60140106030b41ca100b004409001525440c6090380304008050029000c3e40c803155030f11100c07071004503c500d1880e00042c01c944081e003c14617000360000802c280d02c004142110040c08041300c0141c10680000956000c0728001d0001071300a0039164041400e641d01000002200c00110070b8031681d070480140700070003600d82071048403030034450800045068500441a101070714010307035407241c10351440f4410003c1340440605d140241582c810000214400500003001558080e44002c60134a01d040000d10240301019410b004251418440000252090707112a402000c03900480d5100c604904100b4451501a441000d440c0b007640c001e1400290081c0b40c40040300c11001e2080d880ca180c2828211070381508644501942030b03804170f4100d10b80f51098550340c0040340a03000089520440c06030f034190380d8038100d5841e03004211100340066450403086a00c007070013120308501d0440100d4109503c00503c43e0000034405da4840040101402c174a80300030f0340003008054001a5418181020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 946270521 1250 946269271 946269277
    0xc0318080904060501050405090c0a050c0709020910030911010e040f06121202070b1e040b0a09030c090603080301050904030512010308120a0e03160309080313170105090a0b13120302 80
    0x10358040d030f041400000b05580590295821a4001340040e0340300e5075004070001d01c50f03120200304018000103000380003061908000b0301014005206005903100706103c00c010700c001341650190209424403549800061001551b0508038034203091114410080c140003d004d04403000b5104030340c0380741040020f0912064903046250500520311003400f0040e80340126150162f9010f211940c1104008803110140c6250301140d8581c00d14001c00c0c1040c0c1c42c4c40c0c0000d00d5900c00030b0110300080d40d0301d8041c400c0c0039000100c4002000115000c0154919560f40e64410317020510a41b4400d00d5044001070516000c1e0003240c1e4188140d00044025603101d00d4101044d070445508190315100d17034800601c200d0101e100340806c000100c0c0003582007070700c00941c402150000ba075007101000307000038001500c03a84c10000b61800c09448186003c0480c100850312090350b500d00e038109a2a030400b414040c2808000c205802d006800c40000b0364181d0360020182c04411070750000074006981141c0c865241070345a405 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 946271771 1250 946270521 946270537
    0x11041a04030209072c060f07080309100b100c02060702030a0305030108060604061d060307080607030e1006030b061e0d06050702060a05060a0b1c090303060807060903150c031808 78
    0x183c00075500c0c0c540c0203c84055030000c0007000302c4105c0031108015039000403031515242009241d02e15024401001c0c1e003590f005841c0c100c420f2440031040c0000c0320000d00c084150360005001c00c002400700c0703600250508681549901c24080841c0e42e02d400e544070300c0110707080349401a044480709005441c000b40154030134400c140351802040041510b42c43c0034040c44044806d80b20003500500506405000e0102c805040e040d03051041107000600c104040c840c0e140300324200d80700003070600c3c59207001504110303c0c4072214125030300d00780e001d0000403a0300c0100c581000c4241c890b8520441802c6141c035a10342c0e100c401e1540304080c0701542c0104507407500100d1007280070b0b50968a0781d03261580007406442c41900e0740c1d9405a90140248207800e9024007500c000409042150040c0d815448074000315180340c1d0b001c1d00001c1e203600051107030140070005c910081c074441c40c22201483c40c42e1205031100a0712115215a1030325203044c21603103072003a08030034291040d0201d8201220340a14280c0507940c05044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 946273021 1250 946271771 946271779
    0x403030f080a1107151503060b15041802031801061520060606030903072901150f050a11030d200c060a1d0f071a160611041a040302 58
    0x81444030140500100d000d620080f0b070b410b0200e5680c44075000c180c00d641580140756502c0c003016000b80d01c82d40080003103020b40c00c002800c0c490325007409141d8894026025203002c0801c0b0410a81400315601c1d00c1a15640000603160745440850000d0b06a80e0400c00c03590750308001c0c010030050b04800710040c9541d074a4032a1010442190b8809143c0d008035000341000b50014000960941130003002540c2c0808201d0541c5c0c0707800356603034501b0044d121740c0030942d101280303142c450020f4101c101c0100d130243c0385666860040c1481c05070300500d56200862050200030b404600e11416a0090070808250b91141c003c1e40e4880000400082c000c203451048408040050a103040340c0036090021540307981c20580241075103070303558a0b048000c1e0101004000d4420b0600c41e2504058000740f01d00e402c3d001c0c1100180440c01e240964550b4900c0441020030f0120030104901e0300d82c0c13030707004000d03041c030903446240425401400c2c91421003c1c061540701d00c04610001c0c2c1010000c0c841c03400200b081e640300325 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 946274271 1250 946273021 946273037
    0xb09060901150b030a0518010e0f060604020c0d0509060d05090d0909061211030a0b010e0a0608070b0403020108040c0b0f0c060f130213020405040f020403060c0e10050a140403030f 79
    0x16541140b040b038a03c5450b04920041010942111594010740c0d4000c0d02110700350340e80f0012150550031180950444c80040c1c0241c034940400c05001d003c603d82050b4101d50a40c01c01440395400c945a000c0800b03240c00340301001409040b242c5452094801803004298100300c0ca00d028500345031528204038203a030004d0054100030540c820103215803010345046441048079000c0a94550204100407000e45034180300308000c94002600320a0000d02038456401038030340302d003015000c400613034113607400c5201243c001c0748041c1f0103802c0800c2900c08694091902d100035480302d080190310082c0b1900140440580015001c0581852100030044400e010742150300307030303600c18000c103000200541da0049941d0401a00d04050318000c07201e0030b81c148c041c00c00107180650301d00c0010102da50204d0207141580c1c001c5020424410540b02e020458119824800c0c908480c400002703603000c0d907081ca21818800b02042c0070320000d228040c0403003010601811155a69140d08002d0110403513420300d030000410070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 946275521 1250 946274271 946274291
    0x13030c3804030906050d090605040c0303230a032a0f231b070b12040605010909350c06180a03050733050403021b0a12030c0b09060901 59
    0x58028074462074042e42e94505480c03c058080311145e2140b40c000342015120106080401d00c5803061300d00561003010070a16440c80c0d883e02506c035809800e92071405c04858000c1d103400016003000c4807a240d04038070340015071465040c0c10342c101c41040c580c1981c0140341c90403425042c64000700760030288040c0c0d4440c180700d29180a090b603940c028103404074007210028403280d03000c1c102c0300030540c071201c00c0c1509541a054992501d245550042e264014010304103a042c0002e1254501c00c1d035003d03080c00a03007480040d02584581207000058600460424400026072540320400304001800344150098035030f41d001f081c1181641d0303200941d210120303400c400980fa5404400001d001d07016030703815200d4509001003900e4014505d090103203824102e0090140f0644820305007000243c0710143d5140001d03d500342402c0c001e2405426a640362007100c1c2c0510b150b212992030031189011607541d505480040b4025180403202585514001400600040e05002658038045581e80c851031403170008001a81e80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 946276771 1250 946275521 946275623
    0xc06020a1d1c15020f030a0507030f020a051605010b150c160501170c040b0406050c010e0c01090e06030c062d0a1403100b0406050c0c1813030c 63
    0x2c0452850480a5101600000d075000c000015103c072442401403c000100c404003403103a200711400150303e5501e40404c816244c042c801e40d060900d0100086080a40350880a040c0b8420003024104017902c507410641040401d41205808500152980010009035460880541c00082010545000d28030440348013400950400c000c4482c140e48181e00030041850244069030042c1807004180010480032030303a4058600180000c00441c1e40302ca64a12100300b20074219011824007888036004500d9038160350381d1240c0c015013681c03014a4185c40e66142e42c00060319011a1200d020381000002c1150180b07400d0800e4480c0b4046c50f0380b480c1524441070130f02050f03024414034070300388045801ca14160001c030ba25032000e10341c4071070b03c0c8883c1c519160300c0d260543c182d0342140d4010400510001540351a50f80e0900120342c8000e8252500d20110a985481038051540140342d0380c00d010102c005041814812543c2601d9150000e0010781544400407565a003043c41e61544ca245802e840603000e43d20382 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 946278021 1250 946276771 946276789
    0x209130506010206130c091b1d01081611070b0306130209150a0c0203060108030a110102030115030b0127030c061e0806010909050a05090601060c1a04030c06020a1d 72
    0x18050b40901410f42d01e071241701c500d500c00400165a4120500c0c00840c05034444e12801d150b0014041c980b50348080c111600902c014810003081e116042c00744c82d40b8045980107801c1c10f400803214101401000003c0c00111002c4110200340d00301481051400191001301600440c0204402d840c3c8251480307018159078248e105001740c20750003120030500005800318150190500c1c26845c90700503030042c03071500000d103025070a0308200b815400000300746607d5600030304a4a0002e44482c001d600310b601d0543c800c0e01803007241c3c0c1400245900c0340401c100903840380924400181000d074000b40a00920740c43e0750120303650780c0802c503240c905034400411074034090741b10b0f6044120710030984c601640812500321843c19010b00f00c0d50500030b03030800c0030421198a0040034810781d1030010008451610303403652403030141d06922440c00d0214914001c404200c0d0600030409a00142c41c540d485925a8038040356030b5017074500d024200c1440455944005940030b401b191325a100c0b40c08000a101c0301d030040020b41d003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 946279271 1250 946278021 946278031
    0xb0304030815060913050601030e0a0c0315111303030207050402090607020f1201090f0b150307031410060305160504021312050f060f16090e010506030603010e1002091305 75
    0x15068400100314031190752040d44844400303000103081904c410045030311000404c00016a183d1108100030711075034544101100e40d00c1c01402040402c140b9192143c280b003075070101130050343d60700c1101c0f0100910303600304036540000c1c01e203c0c5a030f0b2035800c0d04c180c410006a000803030041c000c25100243c0c526280c001e603103600c0380c0204458a002100d03400c0108000c0c00c400d02c0c40d040001107021400c900c00a1003000c0f800c602450280c907440e8491b00e454030744c1c070400420040da0340c1110280704039280c80c0003540c1d00940b6880700100c0d040000a410140c5848001c0000c020004d00b0310401004101d4007007041c0800c02981d070811f8600c01d03200e80402c8242d0007110707000c541c032100d40c040c200201d81181600fa0800c60144066800f42016401c003e070420b80c04450300102c41314100144100343c5442c00034141d03130585a10b01203000c0d5040070990b8518082c180b080500c03400c00032021030b9450350b0a503c0b0182a100c240200c1d100e02d6580c840c03100294021915440c07150300d03d1046030010b9803450003000e2146c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 946280521 1250 946279271 946279277
    0x7170708060a1202040603022101110a02060412020a080301030f060b0411090112090602070c0819030507170c150108010b031b220609060e1e040809041e0203040201090b030403 77
    0x189041140103c142441d07010280d0b07219888401c00000f613103e1040b510108654103450f0840a03003a010002d00790f440340c0700c0400003524100401041c060380800c0d5640c200c0d034000c02c41c4151130140601240791209101d0041d1420900100000410000301450304040e03204020a015811102080008070f0305403244040e0321803810040c6500030740c442e1b4071300500c1403054000060b09003440d45500d402c03030300401d40885081205220070b0000320000c01c40b0f50101581d00302c8064042080c1d80e001403030f5015a041c009c01c81d44403060041d00c1142440b003969141c100c0541150150701c0841c1440c04030305802c1c13140b01129407030441c2041042c05e020452800304102c21202c07111840a600910000440510102414400e13110802003481e0301c500604c1c1c000c121500c0f0100d01d6608180102400c1c0c4405004034000807419004550b41c01c8240f0141ca074450b4000301c1064403124044040340103005810003155855607000340a2125146640c00713140600d000307a80351081292105c251214074030007a20040d000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 946281771 1250 946280521 946280539
    0x204060e090f060306181603050a022b061a0d03091e030203030f0a02070812091809060f1506041d07050721020c100507060f0b0a0513140717070806 65
    0x91145c06c0e000c800046084004490502e840c3c40850b41800031660400c940302c0c1c01040c0c180041d403070040000b5101c0c2000c280412002032600210b0045998501c1c0001e2460f078403074101a07485409240c01e5102c101e006012811f00408601d0010401421402041c50440000304c0030080c0d014010004030540740e0140c010740c54400c0f0301c418249143c108510f00c600b14850741c500421941028400c08102c588002c59a13521130b012201082610000951b81e66441c069800030810075010000702c840d0420315412031070025440714540700b0100155603d1301780c1c03c40400200001c000e12030000200580c1040c08841d00725440725a4229203902c0b440f030020b480d90421a80c0b50f140c0c00350303000c2e1501201c4110700480c1d4000d800340d00416400e1030012054000b04c0d101140034400d1040a002c1c155040c0000b080c204a1180d403a400600510601d01825014030100c0034a4841c034a8641e00031070807072100d40d416260620785114001e02d80d04803501e01404004075040892805401038140502a0100800e40c4c44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 946283021 1250 946281771 946281781
    0x30c06051f1406070f17070b070201050601020a1e1b0b070209091b1905040603080a0e0111030f0904020c1b12010c14031f0f0807210615090204060e090f060306 70
    0xc0482c425200503100075a090b01c0030301b00a0b403400001c2000600c18441b4000c540740000000c0d084890003060141075400c03103818540020850b14100916688080b42d0f296416010304041c441040c13001302004084400c0c00c00451010315200117460715a108036130041c26565262807072078480610240d000c0c06240a122141e40700d20300020806138110105025010680d0b40d100000c007a19140c0d4001e40384501c0005145100c96841019204025401e0a20000d1384100c0220241d60344548000440300103808602100c0c3c503601c1f501180e501da4400c50440365011408000301c003903a0241d5280788d100301440200c1d18a2000b040c01041500d101e00d8442c14180981d0284080540d4001031960100c114601495500390244101e544040e2102c12600440ca43c2090035003031520185801c03130304044095001200a0400140680c0030f01ca038485804980c0c0c0c11211a15410034416411071403620b8004140440e910750300200481600c00c0c01c40d4200301c20b441d40940e0300c10003541582c1321ba805821944c0028 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 946284271 1250 946283021 946283033
    0x41a12040204050603030f16031710170c040905011506140301030834020f06250f050a06141014010e0112090b18070501020d0c030c06051f140607 64
    0x50b403000c8041c0581f45050820a403d01451303218031520300c291620141d581c414154003865910080b8407204180001d8140310041360b00e80307940b41c072400740c2c20f10985880d1200300a080c400500e060102810520086d660344c64118080c02d295464400716035410400003d1803845817142901501615540c5807542c0d0850b220008264058204402d8008004841c00c0441c0c48030b801c0b83e0390f416150b80307941007030360750a10400000a400d541841e218500500c020700d10321040003c4e4640c10721210891320703403c64035072400c50171400c0c8080024006018070f080080611106070000803207151035600340748066440741a0040132f480180141d401e0f502d541d0141c0e50341035000f564a06802e00e01418a28503a140440d00c0d0720607250310a5045448000240600041641903005048051031074000b400c0c00e681000c0c0001c6d501c14030703c0804020001804514801d1601421440000b541c1001d814040b0f460550440d1080e910400014590862132080c0015a080c11031455644090010710003454081c0d00d031102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 946285521 1250 946284271 946284281
    0x1051e01060f1202270a08030315090405101b030506030a03080a0b130606020d020c0301141909060203010e0414070b0a03020d060506070f1a090c011d0411041a12040204 74
    0x102d00f42031350800c036144005203020a51030700149420301c000202c489038000c0c072001d10001d5100d8007a81e4418424020700c50103400c0c03400f100d0402650002d506a9a9040c02da1608410300c0651495078a000c0801d01440c0100e815001c0100c1992814826900d03204141562005a040060000b030401c10215054030704075008a014800300625440314411044406400c841c184c0e88842c026034824624034540c550140035107929414210020081030f0401c8103141ea041400070003a00c1c00c540307001d941e01c04280459000100e40c1d40c000b00e04544035038441400103500700b0147c4003900d079080c843c84000041360780000c440b03098032020850181000307500302c416000794000048001d54540c50f440f011a19071a2040070303242e194004c0000000c4564103040481c1e0001a958500300d0803140c030340c104542064001490302c0c4024080ca0f002140c1c0280c44c507051280d82c1b8084030158040e0829407c400292030b07980c040c006990303203200006244401811642c6180c0710b0b103507002810304030180004015240c55840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 946286771 1250 946285521 946285547
    0x20a080a20071d0f010303050703111c0e10020d030c02070302040e0d0e03070b0f03130b041101020f010b09041104090b0103030306030b01060305040b191b0201051e01060f 75
    0x1003088900c107050701220101c001c48000345900d0740114420000c00850b00c9211a090228400751aa0307802c0c62903001c509001c1c14040982030081c00100c02c42058415007003c3e0b0500525001c1e01c0101c03201c0c10b034107121100403080c2c08001480740051030099280403000c070100c04079560001c02c0740d014030007002d070090b01c60340d4100710650149440c0000961914012a0081450343d000303850250041140909544040d00f11240250702c00a0240a0030107048126500001003c050a849941c0d051840540424840004003001019030501c401c100c0d05034407840c2940800d8090705c0c01e114584010f40c0c04c03280441da10540c44810000440c010846031400c0f006566000342c008a0400210b80f118859164207a00c210002561040104244885c254100307001d008141b42c04c0c40241802c1e1111b110a24000d48481600b02d4410900020101075602541c00c0d180c00100da031000c01c0402030301a000b01812610400b49500c4000c0c0e8051201860b00c026044e11082c1c1c5a1026110410b041117824002140e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 946288021 1250 946286771 946286777
    0x60c050306030a0222021308100b090a05270c090606130b0912030406110706030c0c1509211b0b010e040804050901092703050906070503090603070206041e03020a080a 73
    0x4007210365905280014141900343e6210711f2000341c0f400c800c01d46044006401c10011034502507107802c580d0f4403c4d800c15089440440042116160706000390b82030000703085021400c00d142c0701d6031000c032100422650351071203003142c04048640c0d030b1000f4410548240b41d41600e212410070380c1440030b091910003a01c852140540803155004c1801c2900d803441c0d200790000c40120306003042800c141c4c0c0040100001520f8249001c1c00491800c5402070302103045c4850040c5200d1280110058410f9143e0040400c40d40045c1c542c10307015034058880b0701001c903140c103480018101a1380c0f00c40b45001030140c0503003542d1281c040d031180d82c41c050b60b018000030090000c90b040c036030400002450360760340307541240030340b2807100000b59803941d000c0134802c02074260013045148d031403080864012036007003030560390b0100c401c0e03c2c01c03540c6030205d00c0d005d03041d4894004001d0b4084800b0084c800b01c0707980010568421441920f111002214024a25081c00d864200c000c0069011400a800040945000d0a8034200c141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 946289271 1250 946288021 946288069
    0x150a05070b0106030501051906140307050d090b010611030c25120503091002160302060f0d050a0504110a030809240304030c0b360a020603040c03060c050306030a02 72
    0x541d45400d01102a030000001a4072180180403d15100c403005d08180c92400c03145034041d20b040d0025011500c034240740301a0441c0400041c0404d400b8030126440e2004542c410024001c1c0c902e000c02c1a2242030145400044901004001d03c40c0008110748494500c40c00805401001300c410500500d111b82d0620004609510300140150b804007a481480c1d102c0d9010b5511290390314203200000c030300340e0410f404541c001c00040c25816038410611003aa90141c403103a40d208072190607411180b00c0c04545001540c40d18003040859815580894002c40c818a041c400c8100c1c5001000200222408054a044810400c0e14418070380303002840104c84c0c4503148110350701c090400d82800d60700101c605501043c50502240e00b001410900950b202d401880da2500c3c00621829440503808960b5222500900f0704e08094aa51002c210f0307290030543c01001c10340e9a151514045d24015014401141c049040550300050a030251041e41d1283c5000342c010701c1d1099484c0c0800007000403200240464680300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 946290521 1250 946289271 946289273
    0x1a09030601090c140423040213060e0f0303090901140a03060e1e0d0f03093210050103020d1e140102180a060c300918050402150a0507 59
    0x24844603000302070345a40000d010101920144c9145020007680c0d200100410062094942400c003158034441464038a072445440c01010600030b00c45c6d41d83c04c52400c42182c5001030003540c0708585190300303074040c0d40c100d28070388000042c5a5640034111107590301c000204010700500d26811820740401d400100001291641c070740703900080381d17a11400d030300450300510011290801c003801350300710f224007540003040003c24118000b000c40d50400c01c04800c04d078032148098107020b84000035244510884800d00c10104501c3e69980c64000d0224440d80d50340940341160010807a6032103014100c030740252004240302540e9843e51074030520418500c001c20802d160800110f41e051004c0409101814001640c50340d0302c0c4101d070901c0c000c08000718890700180400b03028550303100d4980446580e0064028506080ca540c01c0d142820802c00c10f1a4a007284180c061700042e031020b4050f0855000502d5543c0400d0501d2003041520302c1220040c4d00010800c40048850320100300501c034080d11450002c6c100721807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 946291771 1250 946290521 946290523
    0x5030313060609060b030105011b150b0a08070e0117060603060a0c050c161d0415270515090309030d1805060304050c040507171f2c010f06091a0903 65
    0x1241c5c00050b02c90700e02100500071540c01c00a441c021130800140b400d003981e02e07a036901850031040400e4640607038981c1050401502d034442200003918007601980c0310320b42c48500d251101c1900348144030004240700014911940301240c80f80c020b00d4080e01070619540c680100d07402522904444800308082002172442e0b44078107202c1803203002100c03c0d802c80504c2c50230540319080c2001d82c9005e10b4005448043c00009052a4508102a003210101181507501017144240800c141d03c3c0e444842c2c0c101007003807001c20001203812540c0c14204134071070000761111101203540c0d000b0300d032080b42c040e8800c8070400726160190741e20304d96011208100404a03500e500c003084c540c2d081070314200c0d0603500100c00485c0f02d00d0f107401426441206c51805103240190803140c04003030700d009001c4004491015020031304900c0030240040c0a011031728003498183c070b2800c03003003100807000101c0100740100050010880303c06032040c6004491039079681c00803640c241486d8801c40703840707000208600402000710785041d480c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 946293021 1250 946291771 946291781
    0x3130b1003140d0c1104150305101505010c14011503030e090a0c080c0a030b0d08031e06130b130e0a06140f1603141317040305030313060609 62
    0x20151500c000e080c1c40c41ca420340410103045402c2045400c44540c80070b0700d0b9481900018400d80000c0c0d0305241d0341003200850000c11031150f81c000c0784040c0312800700500c100081c40c903003d1406520200003101030303590720302c8104280340111800181e0610050340800e034815480d5580c00101d00000655440c001d10040b045141c83d4012400300308280c020008900c1c10000d4141d00c0040380d8001c0c80080d0b450729000b8406e5000810200d1081808680741d413896229520007060503401a1142500a10604041696410440351056407a1f1440d006a56442e1103640c00c074003541010f0001c0c140c0a00c1610404050b03c0000c80c000e40040d007181242c20010300c0d50003400203007402000600003501880c20101c0c00d40b00c815220503d11001c040a005000384005281c6a100410105681c202185400d089010f000c91810148610507402c2c04e201e1a1120103014808561290211403600d01c00f008680c22140514400502190010b10004610604000ea0054420f12901000604a48842003001294 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 946294271 1250 946293021 946293031
    0x5030d090b2212050f01020307140c0f0102040f0311011d0f0f06040b120c040605040612090c1e09110702091e0403030b090c0702150d020403060e060a0b10020d0503130b 74
    0x24005044090130700506001c0c5003d1404c4000c000d500d54036011001922081800450601040780000c40102212007440004034013804080295519580c1d8642c4202421041c081907500070600c1d0480340956008485c15a030300350b20076003903c84064542c4200f0600d0805202d04030b03007114200e43d1060465540c0801040a0480c050b80c1c642c4400000d40000041580148845900c0d20108010700c60103400009690445010303203004903000281c0c400c0840901490301c0006c03c025041c0e80d0228912911076200704003171402120044000e9904c0324103005231004072000c14100c1d0001c01c102805418035a1519038855440848006c0e4021898600243d5040445054000235640c802c205101d180c489075854109410082f101d040c0340868000542e00715200c0040c8682010025072058612844d8050b24015908070301d04101090b9000c1d21961145811510501c03001c0c03070914aa549498525a80902c00c00d403580200003890307201e9030589583c0e02c040d10203013141c2c814212004c005030b0f6a5540f24864 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 946295521 1250 946294271 946294289
    0x3050d091805091f021e03070e01021b150c2a0301141b071401141e16030f0f140f0405070909020f060a030b0a0f0b0a051303020d0b0403080105030d090b22 68
    0x182c50702002c020500c0c00f905072750310304640088080405210b030380000f03003034001011074840c0a0750342103401100361441440310070040c0b1300400c1c10308954500410942c0c00b02d1085a165440d290090104140c00c80f80e448481c08456805070300131030000760000918404103016032081034a40340b020b0f150074038012407188241322181c0d1120042c5981023548100380750490750340701c4019008081e036850107681050007400d18a80480126051154922a4100d000307004aa084204031041460b4072400c050203544014441c00010303400422169a10324851078452034028000d40055410304030000003516590005070b910850001d0300e41250303999035000380180c1700c00b030701c0010340c2c0000e90040c40014911039004051007460180d04000001c480c001312200d0840c2407414598811400340b8030f419103821034002a401c051404008000c001041ca4003a00541c081e0f25120656aa910301305995240c1e0f400d070490004080307600c00c0002c0b0740c00304090403042c9095a1902410307110380d000300d0f8044050354008548 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 946296771 1250 946295521 946295527
    0x90303160f110607170d06031407060215010f2c010b071101110601171e01020901090b0a0504210515060114090a030809010903050d091805091f021e 65
    0x4100490840c440c0d42c810558000341040d04070340b104203110b950300030154455440001d20100d0307008542e1048003d1030303006250013042c2c1d08030900d141d6181031034011800944100c5200704000da1100801c03a040312080b550300007090303081030220418801419003c90580c4480360b90b10403441c91514100e40030301202c5100302c0d1205850704101480c618980c0c80241842100140c0c0a24440f01003010740c192030602004407403041c00c10500f1498490b00050000c042501000740c682040410740003014001001d0341c0b0341c19001d84031501c420040c800c0080e08804104100710801018403122801c0110030350041059181d40207940b0340d181010071003941d940d023118a0004001c1d0540c1c01600702400d03004d22000d07490030082c815000c1903403017003940000382403030401188010203a882124890003442d80102541c103015114003002c1d1041c10307240550884204502d4454407034400c103100317203071103240804018022050000701c0c0e40400c09090f0f41241c0c00c0343d020030850355980129554410781c4440b00c02416a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 946298021 1250 946296771 946296773
    0x20f0303090d26042004020d0e0c0303040b070b06220b09131e08130e010503070b0f0901110c03070b0d05010909150b0a09050108060f0c0309070605090303160f 70
    0x80e8a006800b072010f003000400d40e60b1500c20494050030b6019621911389060983c0d10b40034500507072414210641d03ca4000500400101e0036500074902c404088800c442d0b999000d602015205e010340c0c0156483d1080138480100800c0c03e0000064002c40e025051720070181e480302101142c621110200c040c030030f8070b0b001b0503496030070401000c0740d00020090142c08241400d075108850007050408084181e283d4140740400e1000e400c00312280da480c40c2d020200841d070740d801401a00802482a81d100340160680040e040005208644900c44c0280705e00307252000100040d18a00c000b00e0740e0444503c10550380a009450030007103200038101ca40d007610340311090780c07040301c00b9158140c124a021504204031b8600052154001d149100390300600460400070400c0420044401a071081e881c41d41004000070b80803002103080c3e4000d400b40718550a00e55035040744d0004038401502c9401c0145d014100c2000352a200f6005056502c500405580c85d250010780058405481c4030001d079660b1040c40c0040b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 946299271 1250 946298021 946298027
    0x1a0604141f0b03070f0f08160c05030909040f0308060303070f12170a0f0f09020a0b0703030902061303030f030603030f0f020304180c020d021f0f021e0a020d03110316020f0303090d 79
    0x1420707403001c80c640443c007440d1081150745443c088d0f09461050201d0b000c4004104503050054520080c0e0241c15258103223041d0a081951900018003a4081070031900401e850303080100c12034030540e03000001d207402038049030395248911149c03040b0301c0100154070503c804e41c0c2c00803502a82c011580c1c0300000c10b070b1819443d424000c0f506c42801c1c284507540b401310441e00589030408a041141e4071003400c2c3d40c540c0c0582c01c1c264090418808000d41c41100052a0041c10b100c032402c03a030982c1c2c000e5840507511490a14140c04a80705404042c005c80e46006201c0c01c0c4030721030b28011011305002d106036401e103955046020961040110340040450700d503000c44800d90740c100a2000110001e1000f005e41c9800c01c0c002030000b10043c505000016222101e0304140f0040340c0407207030386080000b00c2182d42421964442d503a90400c5078000014050034002c207010074480d0103081c3e1824502c0058600e503440f001c0813613280b001074030f441c1e50541c021807030b0b2a0b030b400ca024030107503200e11a980090038004803c1c400c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 946300521 1250 946299271 946299287
    0x1b0f10050108120301080d051c0903050a0806060c060f061908010902011115060409020f0919110702060904050703090c031a0f010e130201090807031a0604141f0b03070f 74
    0x10140f14401070004108501c400505c01e441c4513024204542d0f00ca204042106038a0034000000404904103d9907030201a0f01c24024800d5506a0355050403944841040141e984603142171041c00e94007510200c1c002c1c4503104841a00660020411020060041030400548002d503001c0c0c0d81c2d0780d55511041c419540c21400d40c600040c08040584201c10009480140c0c509000d4605402141e58002d000110745843e00301d000c009500034440e200c1d5203482c0b12044a4144001d003a64012820300103c41d075200d00704001d480c1000d500820583c01c0000f00000c1c003004050061034401055290180c120126243d402e848010358043e414440000000e0b03030503070200071009010070f10601c002600400010010440c07142c0c0080300701441454101c0c90b800100c401d0030762070b0044581405254400010010001d00c960101d55480b00003c10640e548030410040700d6040811141d81980400016650050100014900696461138000703d684900d0b50404940ac200e43e8200490154000c04400d503400c0024 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 946301771 1250 946300521 946300543
    0xd0603080d05070f0f0c170304060c0e0f0114030a091a0f0f010f05131b020a021206060d030c080d0c0503060102100903050a0f0504080a0f0c06141b0f10050108 70
    0x811000343c2c45088004003020b0384401741c81c08004d142d8100e80708101101c8141e480f02d030000500540c0300d090905000d8020440079007490086007540e694207965023424881007221030016108c0d12803a10304641d014000d540000d0070700c0046640c9448030360000d6040c00c00702103155034404bc450741d0391904840301c1101000150800041b48410300c01000300000d031703481c3e103020383d41d05448003a242049001410050f045502d0b084c442c107148044801045a4001440c140c0039000b01c0d9141d40d03620314100342c6c43e141c000c01e42d1b40c41d4012200c1500100400e00504c40c3c441c810344240c0401d0f2800084000940032500303028008400214000103006440d0790410102d021b0b03941c1c00108008050392660003a00034407a10b50f0f60028006000388001c1c215000d201a1001084042d041d030f406540b051410440340144040300300c81210044030049039181c8110411041c0c0d8100b000301e145015a4420001e0030169004c0b400140e501c45e890840c08041401c1c400313201141c00079a0041181c0d41440005400c00f004948 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 946303021 1250 946301771 946301777
    0x305030906010b1201030809040f0c0e1528090e151201020307021b03010b0916080705040b03060105130503010c030516030b0603042612012102030a03140d0603080d0507 74
    0x3c216800d002108007904580d88441c1c0c1c2c3e0756400e912000300703020b01140c1c80c5d13821030306203070288011040da033000e544c030020301040f659100b05003c20741c0203c0e041c1c0682c0b00c1000e03e02000c64140b45003024501817004201d2000c0c00c224200f943e8a90070088145000c035600c00344039000171030744e1106041100047e40400c0642c0002e50652130704020080d59582d1100c0902c0c00104200c018040c180c9082d8402524130170042d056241d103207885105000381d00901480000002c44030704c00540000e1055080e1415a01080ca02c5850b540b13070200111401c2e04491062550752011140004a035a003d2045000000403520045a146403103030700b24021680000100040c1401d0081302850740d5104011241d0081e40084071002514484a1200742112706034492000303c800003031011001d035007227070800341240c0b40e68107825512131107071864501911142a0094050b0b01036181000000d00851b244081c140000c00401c0c1481401c11405068451503841507030390407800116051021a0381c001c041e40181181 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 946304271 1250 946303021 946303027
    0x150a080d0219050a020904020604150207031110091e0b0d0506150906040506030c040e09030c06010f14060721050d06121a040809150309011a31090305030906010b 71
    0x40c0303d00e612112500780081c070a0300070000140466840f941610042c3c0941c1c9080f5440325007a02d4003a40c1c840c01c5000039134904010800420013881d181003000d02086060380c4070b424241c508464468003a0380c28040d00f04c001d00306172011516001c3c45000d001101035408000c0744d02d041203801c0c000110003254581e03252040402070981f041d241c0c801103400321034041e5400390b1b40c1d50704c101d0750604038025604960442c1034208140140309800202620121800c04240d60860340d031868010050300752480b6003018449001c00c2c21540d0300d000f50140892a02401c580000704a51107210552204900b03060004258007003006d5090001a1158078090223111581101101035500c43c141303c0d172400441c4c0d00c80b40c2583d200041c100603200013070700c80c0c103072000c1c0281f445403029404c0140a5001103038500c0448d03203010101c40611002580741004508054503000d40110001101090801044d003400d111a002000100c1d40e201103210358550b0740c2c007903661907441b414a406113a007440810703448000c00020038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 946305521 1250 946304271 946304273
    0xf020a05060123060301030501021c0509070902030406020c0625081302120307060504030e040b0607120513050a0e01030b0c03070e061c020d1406190e150a080d0219 72
    0x154280c10341e20101c5143c001460700541455240541071803803500800048000000c03c001500074000f411800812040980548094001207500455890704c150b4001c0108200c0061541d0003150480c0c0211005032914441d4490785217000025603448420246400c00394151800c800001e885016413440e086a090901c07040074510b040740c030103019100d130f140800150200d40f0100112000c00341c0c03001d000d000905c0c0a0401402e190001c2069a01580c00c2c4800d00410345002c00c02c4800c003540c0300000846100900e1012242908150108a448640d00a0125543e0798850024004128030b10a00640f581580340032080060080d000d58101007081c001e01039807a4100002103541c003001e03a08c0030340f169010380da000b034829601000001e4041c4001f8000d61054215003060354202d40a441d12000364540b6030500510300108440e281c250400d92a0a00030703c05900709075500204c1d02e0003840494a00840050104015544948100d40c016040130303441079014851840c044170b010b6070407441e501c0c2c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 946306771 1250 946305521 946305523
    0xa0f020f031b03060c0a0e060d0e0609010207030306060f052a0703060f0e01110d02030403020312090c040c05041d040804091104060e0910140406081903020613020616030c0818010f020a05 82
    0x75001140f02d0640814a030842c20001e500400030600c5210460b0320394203033600900c0c001d40c450070098001a083c4400410498000e0b0310403803090805568441c600a4021b480039a400420741d40390601c07006a01091070000320401151000e103005000c0003512043c0850f40b042141c041e88100f407001d07410041101000402e180945844d00d080000141e500da4941c9400ca0031031180818200c0301110a00500c1103404001401008a81c01520100500910503c041e1003d010f144115001c940b450210462200080d500890300144a00205400d1548034103120064030201210341c1460040403a040040b0b6500414480385010140c62034850741c200001841214402402640340c0700c003007440c14110903212540550004d21141060740c03442064442e0b0551041d92850041e001446814042443c0c04503403500c101c1e04980c001c00d801d15184102e00c04000300d0750248400d40900200701c4503800401c01d6040184091811f0f44c00110300c072040701d80003510218030b000c0e2110465000c01c508e40f0020710 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 946308021 1250 946306771 946306787
    0x20f040923010b07060902181608010b0d0b0a030b041110050306030a140a12030501090e1b2b0b040210020f0d0305090a240605120a0f020f031b03060c0a 67
    0x241c0c1d1500140d4030049420000050146d28000a422138851030400c3c81021015580c00e00404065030f0500e82500307100300032a0984000c0c0204100c4c100100502e0004a62aa000a0b2b503548042c11141c006580c0c0d03101d524200400700c805a40e40c07010700c0507040340740c5021042003106941c00d04020307095007805000329581d40c2844900425200c1c164200740e41c020420414140030702c0d07204084042c903030b00114004005d00b400b885011001c07420f00320081e5032401c02090541140380c03c000345040400b0001304020880104902a005d224000f040d050806102022080741444c09928011400d0500344140b080d000e01000d054800c54000341c91004019001040d651003480113480c0200312a21840c090320f00381400728070010103c0a0601440c04039040303aa400321410102403008000455450341800a4030318004038245890700f02c00441d00008940304585580c2500203055a82160b0318940428034140f500600c0119a10280d401a08545400c2040e260b01501d030401107400c04424000c0070304620 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 946309271 1250 946308021 946308029
    0x80c060702240a0f0b040f0b09100315020a0302090a08070302100504232b0b1b12090c100c050d0908120f0d0c0f020609161503090204020f04092301 65
    0x15413a0752955039400340396000034516001c000c20402c012540020071038020402040428010358007400081c100c1c24854003800c0c100e90700007002200600c104404c280081d03000c1c2d0114401e0560034040c0e00b00c9626a4100000642900d4001303200c041d0039401004200c030540119103040041c104803d00c0708011070005110301413080c1c40003e0403854890f00080b4000305d50b03002445050580d0303c20099548081e1160b40c4558040c18180c001038403200c4081140c0c0c0202d0002600903070007040f401010b00007076500d003a884040714040d5854524904009116100741144050000f103402482d102841000c0c041a00051581e0800c2c0c42c0351071804080b1915001c3d00c10341d05248030f0300412091494100407003103404c104144035040081c140c000b00c010b00b83c0c0d5108000ca000510480000826010b00042e40e41c2941d0071150110700d1803454220301c80c0c01c00c0e040c40540b00416880d0148080140c507a8000ba00784d01111581c119100d42c106505442240ca0b9403c880503000d245c05442c401c000c030b03000c1019042d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 946310521 1250 946309271 946309291
    0x6120f050106140f01030b24041a070b0f040c030c09090302010b0d020f0d17030a020703090602152205010501140301150e06090c120907031e022b080c06070224 70
    0x440d01f000d000481000081c07000150007102c52802d01c5082000000400c00e854400c8452603110344c1c0c1c400700b02190b01030380c10b00412141480e00440c90714400110502e81c024864100b042555880b43e8400030207441c01e900550300117032030701d250004042e02030084000340703c0180c40018000500e40c0001300070b104030203492805928030400b201c09012551101c0d403641a52000316a40d64140300500e0030096002440c1a4000749a09501103507980c804034001088040c00ea080b1801511200e005d20070b150f2141070b0140543c8108105030000401c06e010f46c900030410310054110400e030903014942902d0407800848007036562040244400c0703000d800c10316002071041d00d06c0d5001c0e07900e04110a0f400c1c07140f000c00d031540c940750104021003100c0005040e41503d200d03084040b1024540030280c0d00d401c2006900a44c4424400e6403030041055000320501c02000c3c040c0d118025a00946810380150701140e002e94007130300b021040184158041100d200c070b108190400910910340c040c001c101090f40030708441c0c1a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 946311771 1250 946310521 946310531
    0x7020c04051e09030711190e0c16031101050603070602062707090603030f030e19020f060c0c190312050d151d010911160606120f050106140f0103 64
    0x102d06019002002c060744409030780050390625816540c3e0729000300b0800c4800740f11841008100b820b099101e8500d0121549050070740700c0c20100340c0c020074035005010011103903082c0320603440c1c1c2d000040403200b118060388564111039000005075007912402085123001ea40803480c2005560784c0002c1581e4051680001d000758076503400e5183c0741131221a180905244241c0d04081030a1219502c48412240300b03480f0782400341c054000507803d562015040800640010340e079803047d43c0e00d000f1140c2c16548000c103a807903190081ca00244240d0004816102c5a80c880c004500c03035800c6c038032804800c819100d40600540d0340746a0300c0e081410a045032a600b00312012aa80c1009421600014140390100c42510407140c2c40d071210b1984000035094030004a40c198000280705807540c8902001100303e411140c0c500010041d0361880c100000400301e591981e038078000a401b00120020341410341c410013501e80072004d80d060450a54210340c00901d11400002240c80344d83d03462041a401060082c200031403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 946313021 1250 946311771 946311781
    0x1b0302070c030803070f0906020109031d01020109200a05030a0c0317090d031e18210f0b04120f0e090a240929060c0f0a08031e07020c0405 61
    0x41000352940000d081801c04130a2000c0590001c40d401000b002903170361500d010766186422070a07505410009008070b15a0b080840340384040e5404081b00c181c06000100b081115a0313228190000b0020b141ca040c4a0448045500c03481d1a01e5000003d1904800801451079642c4800c50b6912007440b000381001181a40010f0280203107040e102d403c840100207180d44626818040e21090150401a0b00d001005c41e909803402e0145600b0b007404100588041002400d007805243c480000c0d201c0d406401c00e801e5402d00010b8420b040b82c200703062051f01c0503503540c2010329144050154040c00d46007400442420281181c0e84804801d451000c201c0d07054a0503107407900c0c1000282a88543c1800124020a1102d12101c8064070700e4220b44009008000101000104200b10400c000c41f41003403c81c2030410340c04614001014101064000c010382d0040e0801c02c0f4164a404450101210003004c08010010304070100c00c9144400c0000020504891801550080d2202107611030103104981d03610101d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 946314271 1250 946313021 946313033
    0x4060b04260a0312050f040327091b02120f0a08181b0a0b04060504290301030b10050a0501020616030209150306150909190b04180b0601031b030207 65
    0x1049a0410500740c0d5942d8650382001000e6020a03603043d0b505505100216480e0144400740d24401c0b42c041e034400c403c4402c0d9a0107120b107048942c1c14400070702c0e03a8180c041000c070094810a819280447c42c100c86814100f400642040040034521204030014081210036041180807a02030281914082e41c01d980c5058840b000603241041450340340c4585d6541d20030640c501c2d0000104000c2c2203d056126a603601d00e614050312950103200005a0180002c00445044141142c007041d103162103400c00280d14444058107402c240d00c159140d001c5901484100da00c042e151030003921080e65507540607414440040d58662001d0141b042d00401c12004600c40342c42507068522890000780702815000a2290354032040d0400d0f20a94443c1c0c0d040d81c40c15400034200022280c0164001d030180e4540d80d101500e16940d4684508038109903921111501d0309940d661003141e0000301904d5180540001c01c1c18200b4040e8002014181270605d41429424003c10068182c4000019403401580c1c5000500d066 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 946315521 1250 946314271 946314329
    0x20604170f130e0a1103060a21021005130f050105030412090503030a021027120519050712020f03040909020d020a0303020d020f0706080a0f02220501090504060b04 72
    0x6801d10281101003012400b24092900500c200c3c1020f000c0028108017880591209480d542d03801240104200514440c0041c444600301d080b800c1ea201036152500851a86011010044000742d00094418268000b12003008090140c01d200305450341e0030140068002d10001e44081d04513084200c0990385c4500c40e1140c01d02800703018080c0c0782c5070340d403102000e50389080200c0f401d14201e0422804000641c103880b00d00781d101d45007071086803030601c43c4c3d101e140103805a4134205080002c01c01c048681a00210101c0c0c03e040d2a80d80d489540d82c4a0381040410395074410001021034102c0000010380c07020010a0710143c50700c038400015501d09901c000791581842075030082d001070002100006050300410150080703c05a02075840d5280c10000b200e03140d0045000d100003285c4110b010402088082c0c3c8038803080800103d00510f0311503d005000c01840349041c0d45014592072480174002942d11a600c1e0300145020348043c00450300b4000000c0c00342c080ea008040b0394811080000c1114904103400b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 946316771 1250 946315521 946315537
    0x8190512090316081c0804080a050a1214040314181003270309051f0c030306030209150a080c01140d0b0d1109070804020609040f230115020604170f 65
    0x414083c9a603204016115400c41e240a8000d202d0700d40d41140030790040b00c84a1082c2c1d803090784185014444c6074140c0320354010b9074803030381000760b070700242c07103190042d8483d621000203081c2c298101e43c501494002d001294280401086804c03e001d10141c0d101242c0b078102e10b44404540312117100f41c000a00f10002c0c8078820b0ba60030018204a851800c03400c0b000401410240241e82d040030941d159014440c07d500c40c0680d00c1c0c030042e00035860a00c2684114030101803a4030078600820340a90303903000142d0900081d116440d441c4c41d82c0140b1042443c021420800070301c03c65000e8031107901050006010380c1460305100c1035800c5d000440090319000c0d076002c011120340090219103c8002401c10b4031803140c0c80300510707006600368404500050b005100e968840c81d40102503626001d004030a002c0030303115410070410401d80f07610022910701a5101c1203010b1000c019500d010641c9049502c0000c0700d460200b21055401c480c050002003140700c02c864640c41040c2802582c0d90030034255902e17030f5116081d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 946318021 1250 946316771 946316803
    0x50718030b01050910061b06061203031406040501060c0f020d350717070c051302090f040e0a1209080d030b0102010e0601060e120a080a09081905120903 67
    0x40120401901c102068140c5034151402e02265844a9a002e043c19150040c3e802007030069441d29440545040c00b0710f14184a01c002050281d40e80c4c1340700300d40011f840801c0700420703110303182581d48090000701c841d80080c0c100c40030f2242c1e51401c1d01c06426103841d0840a0f200c0303000d1580090030340d2101e5100400e52a44404540c070040c181e80382640901010201c4804422410b440c07104040e0072030b0094804040c0c00c13803040481700310b80c4044c61259520042040b640070502000001d482c0d130340c845c01240d1960006002590b5040c00d40100401480550945480389142141d000d00001001450582c0c5907804107501540d4816000261280c0655500c5500303184104812103c82c25415000014054401e030024010540003090321a1110801d01030701c40041d00d01601642c442c50300044440d19400c0441c15142106ca690310f45404c903610591890340803e0143c00d040050318401c1003041c0e80d92010141704200c000305543d8036902c50a0b020112001134001041194145c0c0c2c05003c100c40d0303800044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 946319271 1250 946318021 946318067
    0x2070b04030306050a06020a030203040608040212060f1b16030f050c0d230a0e0f06090a0f170f1c110f01090303050702030a020705090408040f030503091c0f03030507 73
    0x4030307005010304a2809080d0181c82c0c1c94000146c2caa000140c03000107142c0c10b801549c20a0305100003240d03805001001680c0c4030621041c20354400300c0178041c8900515240400d01c0740d0b85800003c0050402c412880c880f1209003c1010340c1c2100c00215030302c6903a55252901401c64500500d0840c1c8500841b2031a500707502541400f9041950440ca281c1484160490704044d220100d9813003c00a020f90100c001c040b81441500200030318181a0300e80c24a40000c019a061000405c0481d842e500e03c0c0c0c000d03c00a5503485014080c034060034005070451540c0380010003286d00d0302c80c4220b480c2c40807034070f07100e14480b0b519511044107805000e2000a19002504660f280c1101c1801180641070903a03058000c40d1402c03001c40d008034404800c8540902c82d640080625a1502c000d021440c0e100600950b21004103020120341c0800042805d0700540c002c40c020b54039032201000300314114408000080055040400003000101401f10550509400d4180016255181c1d02d055812142041241070b03000488 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 946320521 1250 946319271 946319273
    0xa1802040e15011803031b02010302040b0c010f06051005070303020f0424090e0717191107030207091e02070311030a110106050609061207030222140d020a1802070b04 73
    0x50b940d40080550240d941301c40900700741e50368040c40400c900010300018500400c4c000c6000b0360901c52100548103140062400e641c501c0c001c501034001d00d503a444d642e510f07854401034494a03400b41c40050030b0121400e059454803214098400d21480d0801818549c0210b2000c100715603200075900140554003e24000b10104a1004a42003d00903c00046499058081004440084000d114000340c1c2ca8000300b42840156110490800924144014170101c01d078a142480501490340f440c1d0340203c3c0541c684165142c080c1c1402c069806c90543e1914100c0345100810701a501c44070050441000140e070f5400341d05007115441c0d40c51906101c148000202c01601941c01400d0520646044000700701013906c1e14200801841076050107030b8446400e10400c0d9011043d44070258120001d0f040c0149001c0e1182c51110301104181203071824600c89083c10400d060304014030b8028200101c0300c5041c0080e6507400115074084a00902c461410950507004806200340d048410007900700d031003544c161500b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 946321771 1250 946320521 946320541
    0x123060301030f0b180c1201091a0103020a06020c10050d1b0810050f030c0405060d05121309090f030815040e24100e040f0615050f010207050a1802040e 67
    0x416400c40d442c00d4482c0004500c40c2000400380b00744c0c0b170120090120103865008214503000b81c4071003e03040795a02c3d085040002c4911858001580074000c81d140250b24500402200700d400d0780c88a400d5400c070320015120b0356205000b1506100f664108a51512032074101603002780355102c507a2000320701d00b0392241080303034010503050302c41c203812801000c00d5503c030403d00c036072540642510394240e4801e41011001f0b140c560042d50f4400300c058400c0c90184041e40340d2914000500c0d010340c2c1c91910004402c00c0340040d0000b82c5000d40b11415007800b501e0f401e82d0351004500300c85200a803c2041060110340140c4808031409039540008200b0f21903140388a410796240c003159024095022000030b02000c084e003004500300e110b00104a20301c03000528010f0390080c0700314020812980b005030700c0e82d0b600000310140f103030603000009500341c4185141000300340590507582d60300c81410340d4000003080146540740f40a1a0540d01811401514200d034605910b02a0169400c00070408a55404111022131 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 946323021 1250 946321771 946321793
    0xe040f12080912070203033c0c0c011407032d030204170718020702011209080a090b3915371a04050a24060503012306030103 55
    0x10b00c4000d840b1031030140c484003500c84c40b4103000250140c100b84440102c030181c84141d00140c0350410031281805a944090140000003044291103440340480e509941c4201007140c0d03401c070380085c00e01002d050342c498681010303406110001000c10160303c0b1000c00f030420207802c035101120004c0710660004181080038001c0d421500401c0b410405061001d6a07451000900404540c810a10b062151500002d1900694000b40301a0306012141d4000c1e00030400754461900701c02d016942c910303141c480c0c89400808043e1589c0c0b01040d00d4000313000751090320304410030140a00708400509400d6820401c62415041c0e07481ca8000038600071811055000321201803064840d1035a182c800c1004201680c0c860070320300721803020ba2500002000a1400200ca640c08003400700d424807402c0341c010a46030700242c00d680d0700304d405030303081a01c030410081c0c00608401c54540c1d906500c40c21415250030601e00803d01d00052080844031b000e0111410300003580084254500c28018260307170b80c6d960b10f900306003035804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 946324271 1250 946323021 946323031
    0x30d0203071703010f050d05010b0904150e011a06160812010f061103040306020c0114010807060207050d020f22090303020315010302160201120b06030406090201020c190e040f1208 79
    0x2000d001d420310301d081054022a13040e40c4903604008851800c25043c45586d0324140c80850f115942c5126800056541d500d1461245e44600c5e0f5410136100400540340640320003030314108007603041c86120070240040800ac80900507003500d080b51602c1203010a2002d0b071183d250060460307580001e118408003141611941660307200300180c01070542d54442164141d103880c0c01d40d045908188414400130f000d0760000c05580417064004154002111440503905100303a025401c543c1c802c503000c000880d0180720802c010001150847e89042d296000304880010400c4007074896064840d20503078900c2c103200303200102d000504003001000000e16003d0300a50003540c07540c100c2c1c4540b2a02003d01c2d8400d00850f00204140c0c800d0b02c0c40e0000c56401500d82c5040184801e451726110468010b40d912684051840395001703560200d540740c0140006800d020b8011045400750fa0820840150b90b100d552030502117507007001e0103001c1c83d0358605004041201c9840000d043c1e940d0006049410b951040802d8052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 946325521 1250 946324271 946324283
    0x61b030714060108060615040e190c02010216060e0a05120a08060a120605060a09020c150106080f040b0912041e06020f150a090c0e04140d121a030d020307 68
    0x541c00c0712441580c0751024131903650707507a016100080650412040140d017118110460314100750b1584141d60340383c401260a41144055006114a4180d141c050030850f48102d000171450950405c260080c9000b212a01614981d01d0391080d451a070010440d000d9019041010740e480b5100c0700040903904d0f44180f00d4240000c2040c2c1c0403511030714155040804584500b218090b42c50301e10303600c07030014220050a45610107680b510004240c001d50006100101c4441e000d070400860904800c61078502c1038005004120a03681009000c1101106480d0002d07040141502c240e03a551603200c0c07829800c1f403503070903080d2004180020580e5010506250f100e90000d20041995280d40003269502d404682d41200766002027130415000000e50710041e00244030072008100211540c480b8840140e0990000d400d4112031006c100900130fa1000e85407a103001c0340040c0c0b1964052201c01441c01c080c100350400790a43e41c2e00007801403c02090486540301029040d29002c19034050061344039005205c040d600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 946326771 1250 946325521 946325543
    0xc06040f0510050f0708060a0503071707090c050703080a0b04020d060501081b04060f110109230c2d03011a0f04140403080c042d060f0903020f061b0307 67
    0x640c8150701030b0030310484e980d042c00c02d40d599139a0400c450000e0040c04003034101c80030744800316160320280b20450181108100c22100100c0e14071540380b8019a46c1e20055183e032800c403400e0300340342d4004c089428054161618102d1900c4400c01d203401007084012a03a4010f00c0000da44500f01d080d038005802300c40c4241c813810032070380e104000c801c0200f0440daa00b1807580400c010034230030070b4021001011034a0551408440b425040e100003402c4913070003001501c40484d114003481055104040c07c1c005048450044c00c0d00c0003204000c00c80701f1410480302a11014101421a0009421940f12861716001030080c0940344054480c1d0b881089401d070a503006000b225403003203043c103003070090310542043c1e2444e1140a60703a94808843c3d044010b800315440150030080091400030a11140b85d01650902c0c1004400340040e4200d00b100f040b503030042041c00002060441d040c2d03005070100080b00c1d01524007243c180107080010703400703120b9044640c500d40c00041c1042116031002010f40600742c0300e032595200d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 946328021 1250 946326771 946326793
    0x50709020c0c15090f060307030609020f09030d0f0503011a0c03210c1e070320070e0f0f06010309060b04020409020d0f0207080316050409140402012a020d080c06040f05 74
    0x1040c0e1144c1d00485801151110f494001d03030800700c0085500001c0d92900060054640080d0400d0b6031003d914010060804100c0e1089407900380300c1d4410008550404106600a03c500a00705003c1441180e01c1810714050303005813003000000321500400000152540c810786a40640030b840e88000805819200c14800655083c207104100c0302240144501c0f0b0200c01d05d0121000550707800040c00704c0412540c000700811070203603601c0b0350381540548809020403908014000140810090080c21042e00004c02c0c4080f0004407540c0300e07042032003031030301042c103081604010700074051000303016130441c2c400180016282c034581d000d0101890f1000040c400c981e110001001a0302400201511111040004c50b5400d8542440446074406c0c03401c01508003591290f851040f0303404649038108401d034000c02c100c00c540c0c7c030060400740d8454841e03904a506e9807211700e8035a60000401c00901800102114405100401d0165000d4441000481c0c584d46000e19000403c02c103014011a0325201e1750400328 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 946329271 1250 946328021 946328059
    0x10602031606051515030405011404080d05280c180308090613080303070503150909330a0b100f05071709030f0d0f020a0b060904050709020c0c 63
    0x14a81c1000d100040d001d2010030b880d04070003010050038071400c0400c40d0300900c10a80395031540d501d60007141100725413a45407a04186094425584d06c0142482d07042c010000001ea8040c107441c03120141700d8000030240e0b15126038050b5003034000350480b460381910300c900c41100f003240c00508411210399a142c4100c5011005c440c2142900d000041490009001512642c00c0c50006403036802e15410350300d458907545800301c0b81154015507039040080c20000c00c000c0702d070300704441c50154840c4c02e9648a11030700d0107990340740d1a1408884010800700c6040c4110307070b040c44000114184240d07403000c43c2c000c50420440620003003210001090141a86c0c02906803103902807900045002c9082d1241454030156549101140d440d9010506011006010107a0076440800540220f0344142e0300420038407610a901404d0411251b001404641c01022050005182c03031401c0754110318207030b807282c480741c0b114a4180d0030121190031000480e4070100f4030401d00c04002400e80368191052300c8c0c140c0342c094104038007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 946330521 1250 946329271 946329277
    0x20c06040804081e07151209060606031109100e01051b1b1801060e040e030a030c090f050105040e0c040503160306060608090d0c0201110111030f13120309030201090819020601060203 80
    0x8000c2504494000c110102072086e80004014840c03034841004243c860b1044200e8118800c190f90041d52958140041794051007aa00000d21b001c0d94242009a000c0002d030311024580300c3c42e420000d800120034000e90240c1c05460700c481c030b45a80e03600c031071003100149542c6a0b807071526078203043c0088291a0013420081000d070800d403114403103244241e0034441d09903000c24040010980040d030712070304145c0c40d540900151450464070b682c0855005400c2e803000f480c102d050b030815000012450001c011582e04541202c0403290200c80799045a6944c0540c00031030301442e40000d402d409002c224010420155000d00107036403280a040214a4403003808890304001205c40070b40070f500840e801100c65002d219248000c910502d4003c076615244150113003501c4150400ea01c410b2000301c18070481c00d1010100503070040f00c0c12481c65155016440302641162a094801d090541c0c454804091620039084079510b00e82041e040c6565452040340c2d40d1148904500c0f00c001405034400200d40180b0110803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 946331771 1250 946330521 946330573
    0xf0c03060a030b19020705060601080a0608032205040213090c0c02010e240a050d0b100f08040804030c030b070e0f090105120309031e10090c090b0103020c0604080408 73
    0x445503481d411640c42903103a45000e0031644c2c012107280c8100e10100c609000a2018a00c9200030f0500c80c181b050003d816140c007d0540d40308141441014030025000206450031064203802c0b80002e03813011400c602c4e600c00e094120640183c000110341d01e0101102030741c0b50494004003010040f10090b04401c5503c1440010020300180c10010b80119a10704a20800000c0d1074400205c0b40c161010b0003c0022507110b1200c0c000850300100703010700c00b50124400d402a11a0a54100301e086090980c000c2030403550200e82000d000064000c182404244000c1ea0b0181d5400f040c02011640c907400c01e1002c2400c1258010001440d040d041c6440e4205603903183c81015015002080c507908103400c0021286aa0082800b544414420050640e41c20000a0b201800c03011721411400d40100c003407400c103064003040141071810702d0800c50000307852602c0e5404840200704001010a02c0000480181c800d0148110241c0315000c02c0c0400c1c4071000c0000d000310360221088070440c482e5050100700340790245207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 946333021 1250 946331771 946331779
    0x10204120209010e0c1903150f14090f0f04050a0f0302151302100302031e010f050321030403031107080d060e2802030703090f03051c0203010503101a0d05060f0c0306 73
    0x446c0310a03180348500d0f10180840ea6043c0420340c00691103060512108950003505480454041007028401801c140e000d03c0302c2c11340c0d107800145442d031076181507590081c3c85d0089003455240040c05000f028070200c002c140e8071107040c7d071420340d031410000e6641070007104d80d800c160303a400003091038452110744052607203601404140e244881400c00f03074000d41005102c0841c1c40f4445075141c40c01908900194060804508000ca4050501c020306190030940c0f45041c60f4000725022415a2040641c10740340e00c180d161601042d1a18840015400e2340510030f0000c201c030201198902c4005003035004601a103c106090a500da541c02c1601d44035000701940e00c807d642d100307600030380380800b00e0b4004540c02900c90801041402c01c50782e80401340001a40180c00280d80422480340000c50400e56070060101341c1d070107500350b5040c00c0000e61034203424405442071381c0d41e0b821a0103488101842ca0403540500900c840100d5100c2e08096441e400b0445005010082c1d4800207803400d91010b041c1d0f40a800094 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 946334271 1250 946333021 946333027
    0x60604060e061e15301504110d0e0d0810060305090c030307050a1505070e04090314030c09011701030804030209071112250b0720010204120209010e0c 66
    0x41c0a2000c103c0f41a00081d0480a0705001407041e40c40d4100e0405160b4a44e441440c2c0e03403c88001007410150701d00d24614061705480b441d507000340708007104664001c04450720044040c0d00c0e00c0c0001d0010840300301c5000c80c9010124034564509410307485042d40712551340540d9440d00b000c10084500000442c1d40c080c0c03072150082c0a1218600c030764040c6078041c0f40340089980340b40b40c95000a01d50b411042c02141c465002d41442c0041002070b402d25001d00d02c11240034403490600b040c000e010402d00c0303100c0324003403680ca0b0007000c10301d03101d0310607140080401545251390707040411908200e9404512400d02180c0422111000c1c01c00031821070341243c0d0002a101d05260541d0300f00b0032004001341c8880c0c100010601c0040750900c007032020310048070507081401c2e034440300901e4035840c186071211042040d103a1250b1300c03000300d0f0102c0c00a0750310200c24a8520740007010800c10701d4000d07c121400680c0b03584041000300e0700c0001065102c20307e41c02141c81c09078903a621400d24a440b0340c121010f080f000c40038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 946335521 1250 946334271 946334281
    0x90607030525110f0c01140403020a0501051c2f040810020f190c150209090c0c070e0108030c0114041a0a0902060c0a02011b020d1101110f0609060604060e 68
    0x240c1c800010b2620350725114450305501d0002d10b25112030310b120301c0015003042c91008401c1d07801c403c02071a00074821410030304043c5145c00189061041e8401e40d030522000044842600f40700742100c400b2407088020420540f05004450080c1c0c0c03204030745000c0040d150789840c000034001c1d0800d41d000c8403698801480c000701c130703402c82101a421030070003205408014443c9400d20584420b1480360123005039644202034884d42014290043c2040202d03086a01c100804290381e00c5010041e03a1004081c103080390340e5055054624544945035001d011594651000441c004034003200500a80d2680c00003444041e04101c0c400044160545004000da960f04e4580b0081c40c04000806520a80002c07000403078480c0fa0300451170380c0c4d110841001c926006400908115030700300d441c00c00140d03d40705140c1d5180d0f82d90340c01714910a0041c90060814054103091100c50b030720484d4158035441e00041518a0800000c1016a50310805d49984203d0f0003400002030040c01c25125a000304ca0150b81302403031a03119 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 946336771 1250 946335521 946335571
    0x5070203070c1514030c0d0f06140f0609040c020604050f011503060903180303022410090906232a03040b0604060b130608060a030503040e0c0c060f0906070305 70
    0x42c0c11040c40c1400102c24441e80b83c1942200558410290411b01d6550303030001c807064000f01c07400c445010055600d0300100740800400394090203044072064414100e640d00d4840041c2d2a4020f10009503031060600035080c41d4690b02180050040d13200d102261512003c0907483d034242d90b404110401c18015040c402c00214401e40c1180482600038113003201350362036030800d410102441340c00030b03005603000640440b40344003040743c000c1c8058000f4501c900c46051130b583c0b02c52140560301c030302c58909031a14603038024404143d001c1c41801600c02c44451400c40800307141062400c00300c0c2c0138018444106290f000714442908010540910003440e1460342d60f03a0f940d01244841c02801e0310350482ea89200201c0d40300450720041a8040412031046078003450f10300024503250001300b0090065004010410000b240003083d28240c942900da5000290350301d10003046180100802008144211828072402c070704484102402008030209841c0147d55000059060750340658401c407850400c0076100e030522903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 946338021 1250 946336771 946336799
    0x70e0c0a05042c0907050109231018080304030503121e0103052d07060507030c1a040204050604021303060c020a15061e142b110405070203070c 63
    0x40c8604180c0e061a0b1900b410b5000070010400b0141081c1c0a0609885501103280040307a014403924001e0000a0030000000c20b44052071040f43e51508002c41400b08043c614498003802e400f0107041c4041d030703a01201005000301880705c00d0800c0c0c51000e10000c54181c00220449042c0c0350420015850003100040307a5007421802048140c400c12041e0303191107140d006800c43c0e8000c500a100804803a04d42c110950014001038454030f4400380c286180940142c80407420324102c60b001d05180d61914010304042d03401110103400144214452032904030380546110140340203500942d030410042d6181e800340000c034400c800d140741c0505540c400030400039a40d50807040420010788180e0781c0c2425590307941035192050300941807002c0d4440714140036555140110100002c4c210000c03502c56490028080e850243d0030711400c6c050700701201240552840c41c0c11504041c1d500303200204580105007041003051052200c80351007981070030040342800c0d1001064681c3c2d56001031a0101e01864200540c00e462 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 946339271 1250 946338021 946338037
    0xd080106180801230a0b1c080c030a0201060f0f05090402130f0e030d0b01080408071101230715022109010f0920240a03090501051314070e0c 62
    0x75000c00d1407030081c0104821100c0440e40715101c10f900002d4203103002001445405428a8240d041505070b50b0084480f03601040584510903032411400c01a40920524480114074400014a03030b5039540c2c15480b00088485034401c86030625100c00c54541241c810784103855120078601c01240141c6000204600ca0401d509800550070111020a0003130b194100d00540301a0404581086600c2c158010069031074000d00c3c1c40401d40c40c003640c56502d1030082010241050000c000c0313800c2030380d00030f81103400c2010380c1c184c81c08080440301c04135074030a030301125088072403841e0744500d0b0201410600944040301002e200034181e424441c07000d1010b1450003800704c900d940d01c1312111929011140b084407200b6009081445825144c00e005181c084000e500660041a4065100d141c1e4441071a0707902450202088180d03451609040071000340009c85000b0b00030354030301418494100001c40c4a43c4c9058418034070b107110342d0450504241c44070041c0c411481c0662440300004c001000301c0000340942 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 946340521 1250 946339271 946339307
    0x4050111160624060e190e040b091213080f0c010e04090503090402070b010305121303060504030e03010c03020a02010f0614040b19080604021c031409040e012a020d080106 75
    0x201c031600c80d000d9100c40181c0c044c00100b003070f6545c2000303603003403043c0740340c04542444c45a000c04a1901d0160501c2c3c1d540200054841000b81002c40c9100605104c24a0f0300f52903000c0c0c5503119841000c2540c40caa50074811400340d449590100c000b420800700c0e00c1801e03000140c6600000f2100a001d01001d0700f505d48046070b041c00108000c01c200e81c7c841c405011994001d03d10743d25a9030440c0703881480c156101c241141070980911038100c0716101c0b24883e2041e6948240b001c1401e840d28503050b9040ea0400300019890b5080c084040c003620b0b80b507800350280e1401e5600030b04c8074409400c540f200311b50b1503006940d040b50407142c4400c09400c164111191030f00c0040e02c110951460006040c0f008602500941d04c0358004405000551511f102003103075a00d0f00d1042803203042200e41e800390014a5480445030365440200340c0d150290345c5c6a20011060b0b21711002408040a0144140d110305e84090001c1d1109420380c51031281c03e44006000c0d0b10b01c0c40306442e90119642000320a580c5210510007085038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 946341771 1250 946340521 946340561
    0x30e060319050c0405010806010c0c120303020d0c1701050118090513050a080c0105060a05030a0f050309100201060312171906030c15230715061a03040501111606 71
    0xe44801c6210312072044000035500764446040400040c884800500f6060400103c1042280815121907030f806c1190220740601c8200b20661600b80c000c0e00400361103d16071807402d0400071016030003c1c0c050035454255442c0008581c0c07104010748990640701080c80b103a10150f182030001407519885540c0160159100f00b0810030580d0300c3e680b5114102c201100c9948011490f10510035090042d02e4100740c0894844440703e0900c40420b079912203030f03000901000c0f81402000305202d41802210442d00e40600184140b40010320064041e08052004907611005030400307946040c4030b20090301e144041d001144c0074503250186482ca1003054051210000c69582d503001000449402c0c0c81c60003020310807211072010b0700c00384020b459845890547d9100c400d441c2e031460b860f10302c10002c8555280d80402c0761800c0c3d14412640c003004109640042c4c58440da801c440e400c1d10098400694821403085000703120ac031030703007103403400c0303d40100c0b50030b004611003103030b6064006080d43e009481d42c885652a180c034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 946343021 1250 946341771 946341811
    0x1060f0815090f120a2c040209010306360b090f070e04060312030c0e2d06030411100c03090e040807120503070f03060f0e0907090203070807110a030e0603 68
    0x1c18050031580844084c4c00c0010064580ca07040011000c0014100d288400900781031001020400a0810020310440d40054080d80c07031381c06684514003509140031090324115101081c55101181e90041000b0700c08400403481c5690614081c101c1e46030005044042281c03070300e18a0007600c0c0c8000d0300450500c182500301c107885403682d2040000640c0600b6480440b04074082c0c010b0300b203d41e030218510400ca09841c0d204007580b50501c4050641d052888111487d501ca840329146455078001703040d81c0501c001041c8002e0200038400c805c5044001c43e00c14400c80c0407440c095541c4443c1120080215000420401001006140b50350b401806202c1c0e0303500c0c1030b00744d0b41c40000b01075900341d0f0600441e030080184000964081080e44002243e4201003000c1ca041000054584005102e038a4031702c0e8210740000c18480b403e0010300003c0104500954490401460142c80c0b46003c6400d00c0006090030942c0c0300014002405491141e01071701c0c3c0d0840e44070414140710042e03000810450000c40d40da20685 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 946344271 1250 946343021 946343023
    0x20d030c0506040b0411010c02010f1206120f030e010503010812032d221a0705072001081006170c13030b090607020c0328020904030e0301060f0815090f 67
    0x143c46903118022504140c5032074908070041c3c44200c3c00d01d9041140c0d54905500603608400450f038550b0040c2011034880c4c2c80b0400d044040c012a8006450303415034012031074100201a0044480240309072200c102c0b0003041001160540000d05c2604a0346d0b2001a49244000c005001503810004007045900504007001440c04030b01c1c0d1340ea140d00804079882040000c01184c04031002c5c1c401d5031840070060a9a95910340d60302604890b42464540c0311081c0200789518000c0007121540c9911540070180148448900c941d920b404081c007501060203003000400a601003040682580d20540f80c0581050501426140344280202160007080301080100307404c000c0005084000d501c200d5a004440c9840341b80a410498041c150405550001080c030701c83d680d0108001400b0103010401e00c6642d4035018104540140008029400413080c0c0c003072009140d8049441991102d0940003448080d0f602c080c94a0f070f09156210b01c40d8a50450031110700c04c00c855000054215410904940403078103510106 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 946345521 1250 946344271 946344283
    0x1a120108100506150703030509241503010612111201110d0b091510030207120306080d02060103050c011d120a0b01090b03150c12180f010b0d020d030c05 67
    0x890950361121004503664109402025400f0b04191582d8040f11030840c04559a40600034004040c10b80350800510280070400100002105041c020102c62810300074032010068203071000844142c800d4800b090f00d040c1400f45600320303039945000306003011841d183c4030a409081440d550348081100440c01780e50300709005134040245054107280e81d5503407808501c421542034460300ea02a800b4242004450708418101141e8040190340480b040c2d000305c50700b20001d100320364004281c0043d415030b500d4801c0d4154848003e5584000403240182840f5005070780c2e07044240b00c010810342c082c100d0039a8951181c9070f0810740d981c400c00c1c005a601241000038048407410003d21616500900f00c91303040c00140c070081401004003c00030005001c1060129443d8440404005803098031000403450940b80b001c00c89a80c6a00a02400b02504190740e035a03010032041c078039040e042c1c0700e411614001c181c018456803103429401002883d800c555036003441040c11140b04c0950500040c0c07001640071410601c00f0f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 946346771 1250 946345521 946345529
    0x20a11040f0f15050d0b04060b0d1506050a0e040c05041d0709050a11070c050f06040504091a071403180a120302071704030503070b1510050d0b0105030606041a1201 72
    0x898000610001d8040b0f01510740e205a00c90009201500d001c2021030503039540158008401003003030102070010800c64580e030a001450b448100c80040d10641c3c4560100701a0748088446104065075003c00e104d000710306a1700a0304036403084208102e146800d0380406441c0010700424000c1c10607580301c0030300303041840c0d10000965445208011490415100e2401d010100d07000d5241044200d885808680341c250084038010000e0b080300c8212550303480251030062100a01c180301254161034001804a2581c10b41410342400501062070300d8040c11004440c4695459100e08554600d98940382c20482c40c0b03201d20380c0c0d00030031503c40c02180f04c01d020703c88035180b0340e100541c0d190704038600811046401030400d08803a606210030700000790088115082a600310200c040c41e500c42c07000a0f031b0080142c0d0a066400a10088813080e40ea81080c050085000b8844040110061010041d40ca92000305c0b0740035031100d4100000c0c420005080700c0304000b000031101e098103244004a00003660102130704 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 946348021 1250 946346771 946346801
    0x1120b03070f170d0314070e0a03020d0f051e2d03040803071b050d2a060e0405060f010c03080709080a0c0e090718020c030d0c0c0308090607020a11040f 67
    0x6008143c240410500b40101c00d5842c041007140e5070b460700359031100409408a01000f2981101102d5941c607075103028007450300100601800343c82c0e85810480318860110803549409050301c0d4641c44002102c04450ae6070250b00900342194000300d641503032102c90302d141c002c0c3c00110071842800010070030150003d4803461006595a519a04025038031400c5040b1280da1350b103c15200b8410340d00e0b13820210280d207609c50b43c03e4200b05510b0f0506101500c4000c619404c40150721b100040c00e56100640ca61510b409071030030090307510745c030050111032401d106825003c100f07403099110000c0d1252640e03aa100c5002c1c03a01c0c248082c3c6a035200b40c10582c1740f1905a9458482d80c1060000009081c03140e40c000c0341c11401094001d20b4101c00c005a51404d4141d1076095034081540c203040f150610485002d041d24001c208040c0e04850741c068a442040c1c901500040e040c2d40c0014020400061800e004107101d4004120711144c80d641d0000e079554a420468100d42c82d0506196002c05600030510301c0c5840035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 946349271 1250 946348021 946348049
    0x11040c0512100612050c12091519060801050c0906030402030a0f1a01061b1113050c1207020a03121505100305040b07030618092a0603110901120b03070f 67
    0x1400c01450002c5261148513000d1030300c0c0c01d214121040c501221515110300b9102101603a500e90201d041c5050441a40c074800c800404010070440814280c101c2202070711005c00c00c4a4451988908132202180d0780c20340d249042110412a140c15009907500510040403500f0103009543d5880c090450306100300e400c6542a0740c002d400c04007945d0001d0140c42280b8003400a0301401c0c0dd5201a2411a10060300220f0881031104560710740d00c1c020031a50803402e00a1242e800c0c685040b41c82d13070b884141c0d605506c07102c02010422152001c6141e6501c590580d84003102541400321301d0780102040c112141d4104807000b0000307003a844801111000e1189038030700040a1416003042404110024030b09030416203800c1040c4240b0400e80d641c007807503400d136240005545071240750142c28088542043d5451030810040c0314400200c8807000806e403545980e09000d100800c1c042005036004a02c081ea005c504d0000d04035040d01c81e103a02c0b500780850000d0403115983c1d61401411075242c199088030112101c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 946350521 1250 946349271 946349279
    0xc090a06210902030d0804170c030315030a0218060301021b060f06040b010c0321090f050d05070206040314070302060316080c0301060c140a02040218190311040c051210 74
    0x24494120705000d0580c003440b1400040d400030352070f584400c901200780055400031405100503100f8440885e20314078200f564070b216400c101d036529041110030809090849905071800c1c00d01140c0c0a900550140050742d404004410280c40f04500902a0b42c0543d403c0c0401d00c55103480e607804c100001c00360300c041d1a031410400359501441c500140101e0040e07041c50314501460364404001902990145000b41c081c4510020080d541c9001c14103122600e070511405009125565a5045071180700704126491f5000491041d2130501a51002a500c5082400f007000891281c090744012806401e050b2003007a600ca600007203040c0c0069504a0941205288550803560000700e5560040540c1110908641c0f420b00000e00c250301c0e0720002002d40e1001c01103600e00c61403c02c104109072b03a00a00079500c2e00403183c1c02c50518150b540115104500304090b0440c070541541d001e0741940c3d04100325802c050b9207842444003400c00301e19180204501001b8000850a501c2642406403030444100708016142c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 946351771 1250 946350521 946350557
    0x6020a0c0614070219031e0908070e15040c0201091506080c030601033203070f0b0f04021302090d1b03020a0806101e05030109052b05040b030c090a06 66
    0x16240403800c0200c003043c028040d4000600c40c80d5012000b8013840444040c1c0b50071141407200f140e40d01041100c0d50f080140d0b00d6000008002920429401c5071142c03a59540c94560810007a034a851103080d060454900500301600000048403543c000411542d0b1240d43d18010121700031940d4250640d9940144008103041c00322400031744049000b4041c81d41161180e03211030f0404040d0300a0604000042c04ac408415105209410102420b0342c0c2c82d400d01d0b007012108140c43e004100c644a5105d4006850229040c0c5140e004980151100d031015400039007501c025803101c12083c4d07014400f00d0007400080c102500158008030307000760103c90145184140b190380313281a00300110507040300e020851085081c2c003544048604c101039401e421034800402d1030800b0703050740090b9099400d0601250a208001034000281815005141e00c40075220500c4011101c9035100000010303c2008100010032800001d9500710f40d00550851078018554001007180394164000004108001c02c40c00e0f807603074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 946353021 1250 946351771 946351781
    0x150c1e11040e150a11030103050606010e011e0c08041502030c0c04090f0b10030b0405060402011404050d080d0e0732060301150e03010c110705031606081306020a0c06 73
    0x103080c0c505124001440c07100503150744140d405003c1600343c2500156030720311590001c82d440307440c09000e00d60365616410020f8135001c0444680f8041400e0401c100700a510421648000c0c0e000003451a1303003103204000c12501c460701071506030340f120700034000030072030b0f4600c008503040c20f49140c0c006641c0c4052020805081954400a0a00c600d243c05580004a52014484a0a1940011050404d03522019540710702d244607003001d01000d1620080104003c40000c00c107001718004d0300d4401d40201c1222080c5030310f1040f80241c517000415200c03844000380301c40740508030b0444540400308518036100d400781e1901416a10035030300701d407560854046041d1400d2000c6140103458804800b032a20080219060b4403040c85010141140c3c400c0d03d800a80c030030440003059501c0100284208444000000c00648005001b01800e001c1c00c040040c652400003040c443c0c0311500c0540b028082c5c03a00754190366684008000401c000f03540001b020014140384000e0500a0040d1201750712001c45041c104101c071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 946354271 1250 946353021 946353053
    0x411150405240306061c05010314011401180e01091a04030807030b3f0f0c0f0a0e07050f0f03101e0506030703090c0902030108060c070c150c1e 63
    0x59080d0700038000010b042e6088aa1001c8181d49441c1e07184002410f0200850718800101142c9203801c001004004c106429070350724a200000911012165418095804d0401c1c41074040d01031008201c80c594020580010450540c4000005032075251602c8458801600041070b1146003550b004000402d90014080d0350415407514007080070707020501c040f840788030301200f0003103080c4002001060808400b500c0001126068009401c00000c0d0440c420ba58880038100d100a50059001241c41d03410408800404003c005055068003031030305e880c4010083c0c01a115804010b41001211070200c3d401c8014034400240c10380f0aaa05d1503c244091000d002c16004502048c903420903101d044110220580e094450403200c2c6039807901c403e0025401003002ca440180402a200360003e1718540d1540518102ca004000383c40740d907030320300c0001d6580303100f0306a00501880704482c0a114225810160b42d07030410742d03428a00090b00240d2103403402c1b14403140c086005180800080f004104020f41540d80038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 946355521 1250 946354271 946354309
    0xf0a150b070525030c0302130e0109060c032f0310030b0f0f06060a050711010927240b0901020c060301090903020f060919021908060703050108071a030411150405 71
    0x410708556880d25821410301c8080d208460000c012010f48c1907176488011700018607c000c100d407950307a1410300c0250909821000100f0701d000f094680c50303995010345800403103000070700440c40785040c1301e0000940c1002c5c00f40341c0b040318080808400510f00b942c620303001d500101c000f01641c0c44c080c4008921400c0086c103281c090a800d05c03e0300341c45074021003603c90b1030381e02600c0b1a0303440b408400102d91502499000d0180140d207848800703001040f1200d82820000b0a036400e100103802402640500208018441c480070700b42ca00401035540018090241944144140c0d48006107000026099800a805c118820740d030320b11402c02095010031440680c44120800f42442d807819031410368031f5610510f00c00c04000003050a85086541d0482ca07003001c2d0002044444170b0070f84030042941d45403011220400880d10300760012840d108002040400c48400c00291503606410708408001c80e040038204807140780c2070540c0c180e0f10b07a13541c80e11044038000a903001602c0d58604001c000f0000700d079081701004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 946356771 1250 946355521 946355593
    0x906220e012108030c0d0e1f05091605150d09060b130509030a1407050d0801080706052701030902040501030b2e06051e0d020403030e0105030f0a150b0705 68
    0x103590401582d6005d003100c0082904c0f402d4801c40c40300a800303500c41c0c20f64240243e0004100c248409000010b4030200400100a0f50b5114811035645d0000c0d500041c20b0b113130308003000700101d1070440d90700080040c00a003000d0074044591024020385025110481d0069102d080c44040c078180555007801c2960903400500660504081c0903483c1d110348201c03001040305040d001950718039000d0495000350340c0f000450321000c003030200040c8404020301070340100340140d032000030f281c520450a460940c00b0307514408080080c042c013183c2c07002c060034885505241d102d650a80245c0c0c2c60784540c1b8002c1d4021203454000e4900401803005c0d1f241080c00c0003036003030070b000200070721004110f407001c2c1a901036050940d03440b121050000c0018601c031108000d000b00010310001100020b030007510490703101e900d41552402d5801d006480c580002c41d4140441c10142c0001020f211503900107514a100d0110000070b51903c0d1014568280e011b468141c1c0c0c0e9611403221020206100016100350340071800003940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 946358021 1250 946356771 946356773
    0x9081806031312020f150603061f140d0f14010b01140306150f030702070614040321030e03040303020a020f0301060f06030504080d0e100501060e060906220e0121 71
    0x1418140800e000fa01115403103551561841c003c001510005d104403040765005422400007a4001c20100c9003a03009004910104043e10b080b850414070080c00404a4410241029691403004460b04060b0f54882086c29002c1e01041c50381002c08545030042010503046200081040c5c00d550078015000d04005460642103503019601d0306032600107070211411840c413441e84003000c04a00442281d070904d9800081840005500090020112203040d04c03045c804050828110b603042c0290b100191406584130140350303080c00303c10010900402c2e00d0070b001500c2c0c9100d0300b1240c0755400903001200942c0c00f100301c000c00e40c500440701d02906c140403002800002d0800c4960050040c440c400e030b005040d11240800d042007841800da0301e001c4030000041149501d611002035407403850300c006800c074920380400407418520031400c8002e001000b511962801c40342e0307014420146e102da8000c000100661030700281c0300c014140004002d16102c01001c0d042d50400d00a402d4601c04480408192149078036054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 946359271 1250 946358021 946358041
    0xa02060105030f0c0f030106030b0c030703111213030215071106060301020a09120314070609110f0a1e0e270105090d0305041406010924051f050d0908180603 69
    0x52052130b0195140c11011450707501080c050580c0782c100614803a841800c03c0000f42442e009036100318071596090000ca1684005a0070a200b41e4810025105803200000c0d140310074881c41d0046c052091048804458038018400e4a40b8000e070b80ea8000101c1141c2038902c0301008201c0aa000502140210300e419032a40c005000005540b0594140d0f03400100482c0c1494060003d040c1080e00b40103200c0c4c2e64403045d02e0888002c1c42c01c80001c40ba0b0161030503404009042c07403540380c0e042502c040c10716504141082e84145c0902d5800c901c040000c0024800840c180044000c018020031404629003140024501405450401a6a1040c0c3d0743c1c0340800b005031910300003400c0d03034248545050014140d241d40c240b00050b00402026558640301c1c0c480001214442e03941308848840001d035000c0154404984010b1002240c4e10400d540484421040d00404c6425800102c1e03141041c10075502d050b14811781e41d41900e203020001d640203140490a591661400e440150340164115117441c035504d8400074003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 946360521 1250 946359271 946359283
    0x150501112122050103050f0609060f21160b0c0309040b130207050d09082b0c0b04030e09010605030105030a0f0305040909110a0501030504051e0c1002030a02060105030f 74
    0x240030301c0344610758880c03035003062000c8560104201100140c2e80d00440c4060502c44100d03c1124002851b00c0001509129041c08450180308014011003a680b130390010011015182090703d075010b50341d4111245202081c0144880680703079100585960941c181e815200d004540c0d000782d664007000c1106c2c032440e0b6000f10882e084d2090850307002030000a6100400d0011011100d01c00405100207a00024802e00040c4030b41090f01e1951002810350304d1310802a101c4030907650562154641450660f0b100d9107141540341194010f250885142e1403603110204421401d460039030229100d255600414184001d1700c038050000c0d400c05520715450680865510480303850090314082c01c515402007094880d0040314028220f8031802c0c070a4401c642005654042c5800d1024840d83c900c5c10300190650080c05640d1240c0d4004014080c059500400d00d04021320404403035141e0f0240140007000b0b5540e0348613000ca4040d20754000c3d5207500f95070328041d1134180107030807003442035000c5014440a9240000c80b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 946361771 1250 946360521 946360543
    0x92012010306050405160602010f0506040b180c07020a060c110303030f040807050f0d09090b09010b071e0618021918150e0702010207021f05190c020301090615050111 73
    0x40d0f5a6560510074104582c003c112210301307102c0503001a0a03541500507005260001c907082002c3c2e01e9900402c01143c40301c81e40607400c4180c65a140014a10200708154000d055104081c902070407540080c078803050581194000c203655804c0717002844581a501701b8825000d60041d451810014170746e074218603009000030090580007950300c0420074140301d80095484d40c3c00407642c000c243c0d2a4064800651400341510381c62804101c0886c0d8038004001074100c5e900321a086180801c0c0341c441d01e407100b44029403210500d140035094400150948a45164070750b108032221461510352040008041400c50110308200b181c090510120712114050340c4100d03000d840c0000e00540e0f1032104640100c4035031040e21180c0640e81000400c0b40c06400901000b442160800c5100c01860701d03424510b03a8074070501000441c184070020202c0c0d9421400c403041030107401e00382003041c03083e03001a080d1148014119102c545810480c13054a4400080d00040d11090810300718284074100155a030b4003407204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 946363021 1250 946361771 946361783
    0x100f1e0203060d17130e07020c0901030c0614280801080c0307060e040e01110702041d060a230a061406071a13020907080403090506040b1b010f060920120103 69
    0x28516406082080485985e500f1410452841598408110f800141e0071200c400c054020304405a400b460405983c0f03041c0c0f5030044400401c1c0e401c0c041c2c2111441c0c0c0c420044003141004008a41c0f0b0046a88108003c2c0062210450000140c11800030809001a8010140381d0303c00c0441410703070707074002c00e102c02034584034900000202140000100680f4880c01310422951904818901e4001890024000c035402030f5030a0010b950208070b02d00724a049000f8001558004030003144410001d0b4016015951201460f07110190140b4070180c44e10b0b1040c0c45040045940d860704200340c1c6945107002e040248200d5510b1301308012070b00d552a000000d80342095040d0780d4400040c01c428a9825080740c501d8020300851810714000740068100314054805a0114030541c00001c4e0500d404ca04440035100080155414810300940d040045805d98940c00c216540710598a4141455131003074034014004045c02250004045000d0044602020300840c0d9901d410441c1040c0911000c6116044030341c045 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 946364271 1250 946363021 946363043
    0x3090f0201031e0e03030f22080a02100c02010b030d0216120501061508100f03031407061d07050109090b060f0d3b07080d11100f1e0203060d 62
    0x9a0420f00001c6000c10300380003403404075920b0000d54000301561061030b001c03a03c0b46003600d48680c0045041d8648060185d0000451030900010300058040c0c5456000707801100c0594a45d400000b066400c22240f086c0141c0d5291146c041c685810007d0b603244401c10300242014030400514856052501e009420714074082844d8a02003017400d40c01007006111581456a0442c000b0340300601c603050960340c0400140120700c01041c6100b1000301103040381d80c16140c880d0707800072002d2402800d030010501503448030703510f0b852a001400d00003030138038800d0300d2580a4031926091070b00240c603400c81504400112440d0010768000c03070b01d451080300c00500782d24045a80743c414111104001d800b29810030040d03620712000310280e02d1300619280340700b8042d1400d00995061450460780c0d0b00d8446226200103039010048130900140501100e958a04a01c410781d100c2c164214001e00c02c1c0c80300000c50300b50855407045010313080c41c1d0020a49004a049080039407450a2803c00103580035a480c201502c08c4000d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 946365521 1250 946364271 946364291
    0x20c040501150f170f24010f12090f14012a030e120f04030c05040507020c27090307120c08220302120f01061401051801140c07140103090f020103 64
    0xc04036031110402d0100703413420914240007901640c520554400080364a42d4a40c034500107903004803a5507507507040c2d441251448154408850b5000d0028031a141d60740c0c0c0c0c03c45440032800c3c1c0340e6192002c90080c14064501c842c180d012500711a005a202c4c01500203071002250300c403680115042500303040b031401050518210501504140001d0241c05408900040e40004440c001000c0c10449010f000d600d03490598610510094038022180c1c03000503044424000b1713a5203808408041005540c110700c0341010071146200d800280251803004213540041355032010480900c0c040d10f440009407920410462003543c514026000308100180085400004082d014162208480055400501140c00c81704152489d540704c2e004450b81050075402c1c44004240900d801c030090035804d038184e4483d803030540d0034100079082000041140b41008040c00c850070211441d040034107484805a405842d10f107141400c600c801000c03011081e4103040c2040d0b020400325411070140b0141ca602803e010800c9228 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 946366771 1250 946365521 946365527
    0x120c091602251e030303180209070c0c0b0c0109330e010f1b0f050405060904020f0921070602060709090b010e060d0603031403040c05010507050a020607030f020c040501150f 76
    0x40d0f500005414481c40c400301c00c0795241c0d10b0b000b100b02ca010707480402c03004a0b5191181401d01c1c140501a40001c0c00344081988148590704041e01da9008030800f154090302c83c846802550310261420142c4d80d19024050203200035910146c040c88600781c000b0721103400104c108000c2021140c0d146034065607500d0742240103d4203402c010207044000c4810130801901040d030300030044031165504000341a100009a00078040c030200e409540e0010100340c00d0004103000c0201a40c4413042c00d15aa050503c514520340d245d10b80504c61840b140b03c00100b4008209039042c0c6400c4603a03202008642c804414000d44035044803004017560106007000c210a4000801a240343d400242d04680180b400200c1803003488081d4086010f40340700381e5900c0790201d81c01e1601201c1d4001500c0290690041002c100620760084000f844245d2081d0199441075500c2c0d00041c0054200708429404035042c2000e80358040e6042c070010880660072a8100555410400c0180c01d5800d03000f075080900200342414038000d40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 946368021 1250 946366771 946366843
    0xb0a030905012c0f100c110d0305391b0d0908070e011a03041e06050601090815011a0c0703060606030b01091d1005120c091602 56
    0x50400000d1008204500c0032800c80e00003c44006000b11892000da00c00075030100b8804040050a00140134044070791110100a10000708000c0038000c0b0344940c60841181031007203d030a484d2985000505150451487d200d00c0e094a58000710180c0c90101c019a54555402c58110210043c00d03198681b84680c80c020f01c000400785070f0503001e01c5460300100840d40c0c800022815904080d0903150b205640d030b20008100402030080701404152000312060300018030380a194440c4c00754184106481e4004401c01030350255040c1035805e41d4648041041e01c0d40c00602c0d0304020b0107808020404c0d803001c03410410b080041030203400c0c200c0ca0078540c1c051a04000038160381026400009965841e5983d1034040000c144a1084a01190400c600c0100540c001c48010f4100c50541c0803044203222440408910b00030002c0107030145019444e0045040d0b2120032205100001c020010715048580c4000c02c000d002000308400c4500c44210300c12407000764003003049042d094040750243d40d10354014041a03c248 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 946369271 1250 946368021 946368023
    0xc1c0912050d0315081c03060602010b0a0306150b1303050106120b0a092a05090c04030c060806010302040b0705031c050c040b46140909090c19030c05030a0c0b0a0309 73
    0x22090706d4030104c0401440010350200c2001391001c0001d16600c0c40181d090320441d0000720b5110440c0601000801c100d60015044074080300001001c6607202c40c484059500503804145600c40d448000b4810054244588800340c4804080352224a860303649100c45110000c028115150301c0340020400c0054a508038280728003200350f02c4021498440d18505401118410140304a01c80c03008504102044030468095079005803200c5203090615405503024500900f40a040550030030000900911078400b1303045252080000e1a694200c6046055101e00601542c1d00403038036040600c040c01c00314208403821604456072007034a84000c41440040345032442d0102800e081c0401c41c454000328403c0315400305c0e03848a0100c868103921103000f160140c500c5881c043c0700342410400c061031031402d8448640e00100034000c4580141050001c01e210f82c0b0b0705d900041d52190700407802c0c401c000c043d0201501904042d4018550402c20740c48813541d4105603c24070040c040e0026189240030b1094000c00c44a07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 946370521 1250 946369271 946369273
    0x70e070f0833030d170109020a02030702121f0c121505010c050a0213090308070804030509090402210319020a080304020f0a0801052503020a0c0312020c1c0912050d031508 75
    0x2d0034260101520030041c4480c20700da034100160000c2047c030014401d84134014120784c000c42c2087c240e5828890f5044400308074642038440c9500000f808080800c122014050076000881d00c00342881000d041c9028100b110300b003a9003408018a141c00352900548104c0e44c003441d2242d200040c40c00c2650034010440c0011350080c42e500d07001900c400e0b07150040c0c0c20080c0b003541e80c0b006954401c602101d100c034003036400500090b010840e5000c286020990280c00500060248050354041503900d03c048440d00c2f1900000d0b04081294039410b00c2d07181c0d202d882c043c568000340200700c40590b1307803c0305880f004000910070010195441b81c107407220080c85000d402e20f00700801079824040791501c80002c500080f1600b003141959400d07002c600c24000e0300c10707041094951440721006590246d441441644160030069400d00c040e040789041042180d80300703403500070440104200300d0340c001c100c1030b2141c108481c0e0a01e000300c0300c400120700080101407a54540340001e0300340250720f80000040707242e03030100640b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 946371771 1250 946370521 946370533
    0x31b0f1823030607140414010909050709140f060f0313120302130b190806150a0801050310061d040302100606020102031005030613170903070e070f083303 68
    0x1440d50a1064a5001c1c542141100d1256840c903008070b0f140c041070684905130b00c80c10310082204101f118070700c1106000504180482507100c0c0224021583c00300c0d1074800050180104024800e000c000d0008494401d548000010060b41c2c04140140314030031501d00c480c140000003518440d0b24540c500d40d602c0e401180d00102c40100d00c03001b00a500107542082e81c00c02041d500040070020141103980240207140603075440030b1101340c02e481c0120001c00058000e40d0300721712220071404a030003e2a400c001500d442c6040e504000905140c821031160b0034040c6881c0100c144a680444507440f02443c40c564110182e540d280d14089080c10483d9041c0b2a40d0b60a1410120310140c040d005507106002c1c0003800c2c82029951360800d69101401c4e6501450b10407070000b20300104801038501204010b9201c070591600101e20082440c00110740c0c4070441104000d414004030650203109091741040c940743c00551810010914420070500350f01e4154102e10030400c500070000c0030301c40303940ca4600003019192 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 946373021 1250 946371771 946371809
    0xe0301060b191e0f030509160b0d0b09150d050c03100506120d0e0105180901031101140310050f0409060e060921090609031603050d031b0f18 62
    0x800302208102c42c00309818180351284802052500c4a0880113503a604140c00880c44058000308006841c0e104240240a444c05002055000802c01810050303962950ba002c0030038804105d424403d6000e12410303071a003d000d1400403842a1508000e012266001031072080e1030014a00307140d0304070054250180d41e40fa05156603e980c00503110340c400b51910250070400001550b00c98410030a42e00c040342281ca89481503501c030714080c0c8814070712010b50ba14042d01042c00a00c40724005d07131080300c546100074860900795910aa0545500c98220201415801d003040008a04003440c01010f000c2c1d1114204901c695039546c000c00c05080d04000c041080b0251960000d445403405ca581c40d98921803c0496014064807806010326048195074150170306124400b000a558030040220368148104640c0d2200f4491380d144010086100f80005e04602e560010081d041d00c00c01000302d1007161034500081e802d2608046810048422840c2c1b0241c00140740359072500c002c0581c1c018a18414054000c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 946374271 1250 946373021 946373047
    0x6130e07060906020c032d0a050303070311190e0d29010f03050705150403050d09030c0b070209040f0203030d090b010906090b0a09020d02040e0a0b130b0d030e0301060b 74
    0x2040e6031040d911008101e480f90740c280c2e61849242219038043d840341721000003420740302d010103a800103202002d05450441148951030034820032800e4405400000900c11510703054403c80c0c111072131410341a0306040900c00300f000001030514410050150040d042e0100750340d0b0f41c1340e100c0030f1640480c002410310f03400c003054000402c2035401d42c04074983c5140007003040100030005208580d400001420311504000901c000f001502c20f10100c0a1000c1c0004000100306000c4070004101c207907950510305140d0704002030110b0680c0d00001907440c08210300009a258000482d90094201e0002a0318410903c0400d246101d0785a52800b450b00c0c0900c100200400d0381280c40c104d80c0403000a10000741c4a000340c0c41140e03540350340700b5441262504100030079007203900a84104003849800504099680b0941e440c0040c0840d03460b4410390b80e618400b425484d000e0402070003081d28840c2002601c90b204c1c003040e652194100080c00303208007103915000b9950700350440c00103462920030a9031101c868600072 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 946375521 1250 946374271 946374283
    0x70b0304021819050702030c0712050a02042d0b100f11031318230702070e01330210020d0216030f1e02072c0412020106061706060306130e 61
    0xc0241d8a013082d0214401c0782c8004140c0d9014103810000c2c1140c80d103006112080240e0344070007107840d07001d4000c00d9800f6a4481c81159035a41c3c03a00350380201c00408200c0c4e05007080300d12000d0000e007860401540d03103a8480c500b558803c85600e0920040b0310850710400d5a0311400603030340c2040c500c00091140e0780160b031045800200c50040b45ca003400744a000320340c01c1c1506c0040c1c541c5040307003945d40707520600f10240c900f04503000901401039442e002d071079821b01913803420260449806205240c0941500c0364040d50002000340f20000342680d41109188002d40b580310f8100c011540d59004aa00d1030790120b02c0d411144001e000306e400302c50045007840c000d0904442518008081401d8004402d182680d000030f0442c0e05082d613002e00141402c100001c2004169450004295110200030b585060040c0102500890150403008650b038a075100082c2954895004803081104007001d04c11413145147c00c05411010841c1c00c1e548039900e0300301040544005030010403010f0b040100c20751b0740410100300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 946376771 1250 946375521 946375561
    0x240c0609050d0f09150f05120403020105060a0b030907050f010513180e060c04150306080109031e020c01200c03030409020304060b0405160806040b03150a1b02070b03040218 76
    0x10164401e1180c9000d50b0000001d100e01c41800300d50310305540c0520306c1280c61034541e4000d414250309203040108803a803403082c22a01100541e41d1003082c4561031a201080320000e040009515140d40f030246401034588016101c0e11b406403405100100e110380c000c005440000c552141c183e0207403503840e01a00c5a005102003240351840c17509841220031030011a0b030324442c16070740c1c0301285014640092541229008400303038007007558900c8081581c840a02034441442c1c000d60f141800005003000c44840745201c14030003815988407441c40040c80c1d0300621416030b07000b08a41351b407100449a2041c20b043c10090350600d680b5020000380491664526805140903500400040040c0040300003800115032060303c0c000489440030201c11981c030b119100e650ba100390f0142012078001c0340000800e00d0231801d03411002c2050308003400c00003028014411001c0204240c0c111240d01038003410042d460746aa40150101020000000780c255101d00300c162020b800d9108103540245000b59801601d5030400c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 946378021 1250 946376771 946376777
    0xa03030209150a08010b091c030e13021806030a02040905010b04060e010c0305070618060501080109031b030509151903060806070206010b0318010603060c080108060f01240c0609050d 80
    0x46800c000c03098410030b83d0030003080c80e01c0e818096428000055001c1e046050070a6001074440030302481c11210214113540b56109484140156004500300911607046411518000388140030445c2c44a0102000d404004c10541c1e2046c3c2d42d4442c488140068802c9070098411107003002c000180c290001001402154400d640b01000040d4030801110070b4034540a0140010b80b0902101d00880c20903132107000714401c0c0000c091740a0200d90755020954109038001101c503590343d941c070f8062503086800100d9048000503000d14094850b60050081d0090b82c59650054049041d0110342e4141d9000716440d540f0007a9071100c92014018004010302210b0042d81040d00400c404286200c0c0001203440c10703110b1480303400303046d0b5030340205140904c014800111281e64a840c0c0000100d602449402c0c002545561000c0c080c3d0f040c003000b40c0c40c00801410f1002d11a0340c0400401841041510507403004078002001c065503c60983c088a040078003e80240c92686418890400c01200184504004440381c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 946379271 1250 946378021 946378039
    0x50a060503150111192006030903070f05150405070501110d08010b0c010618140105100203090618090a1b03060f050d030c080301080d1d0102031603110a03030209 71
    0x10100c0386400280d466511081071000040c115601541140c030841c1c03c4802299400e405419107840c0d50109920259940300d0342c6800248040a0102111001784003079816030328606008800ea0f03624801d130600500405206084c50080141c14003031065821081940c84d0b0003420942002519010207104880c04104c0340d22131441403160210701d107085040c454403000c596a2038200707610728560221041c00055540e03840d001c40c1d2007500b1503414a600c90010800079003280d43c6c5413003d40c001f0041e0800e6200c2c644040100d442c0301c0d40082107a091171001d071091602c41d0b04041b0701180503c0d03a84202c40d800000e880400001903140d070702a007050300c3c0c0100c403c680b80c0d003c450240c040329140e0290aa07805101d60701403100341000840b00005610130314001c01040b010380c4402086410a0300400316035088901c403a411a40d00c0000131143c5080c08102740d50410b02103002039641c0c071a4441800080d608512240103060080300040d041840c02815a213a28040e07140080081d4002c0f03503840d200d10465 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 946380521 1250 946379271 946379279
    0x3080d060503152e17101a09070c061104030308160813020d0828090816090f0e01050a020409050112020102210708040611060a140115030e07060207050a 67
    0x50315150340500181c10300b24800c08801807807142c12129603107980b61041030882c00054640039036003810706480440b031701601c136152035200854180e50400079150000c0c540b24484291940e1844c201d03640010385420300040c4400e403450013501811a20200c24052000442c0000030705400c901528440d00003505018900c0c007100c1025101ca9405664401c4641100d0300740200509140c3d40c2e0002c010301654000b820907620741c3c1c0780141d805000342140312500001d0b02c1b00b2042c0c1d4101c0030580103848114007400b80c84c80344d02250a480700381d40c072aa0902ca41c5802c60083c000c801035020200b25181d0340020700c003516104241402a61081c03250910040c03500000003245e20382501201c2546905a014100391000280e1170a4106c203402c02120a1200801c030350340c0002c11020007040180f4a03600c0d0240304501c80301800f400c26030001c0c01c0041407410180001c076050f914007d900d042d14000040a00320a1124100b10001e2a00e424400100c0c031589101044a60b000109401161030031601c1a05003911 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 946381771 1250 946380521 946380553
    0xf031303023c070602030405060c0a0203010504140d0801050618040f0606031508030f03070503071e090608060d02150d020d0f021305010219060b420c0714040603080d060503 76
    0x8030300c141360068000b4041481149000401024071040180484007400c0558000030b0840f00c080c3c604a0f0021080040d40900b10418445982210520b0902c45080d61400004c5220342c49106210507034980340007000c0c55181c2d1075070b00a01e064220300204000d015101c81b000303002822210010b031a9a52074402c0041c130190008100e50b010104a05024190b450b5600b099400c2d402c0544000d086c00300c5580174840302c50507d01c0b9004080310030b9480d62452842c250b80500b034a20b0150845024440380e443c0600942c40b19039a91110181c000901d5585005100055000b030003031011070540207043c82c4401070824419000b0b0f007006420340e039941c81c085640d5030040e681c9648481c5540150318070303001031502180c40340d480100000c5001d0700311141c1c5000700303038800c884495003403460031851070b200114000c03100c40110f00c84100580210151406079024902030799105c59104903c40c100041d007500980351150b810200045a05c0503610381ca50180343e02160140882c0e00405010340700d10400e8001081e2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 946383021 1250 946381771 946381783
    0x614060a08011e0504020d08120703050a06080c0d03112a010503040213020706090812070201050c09150c0106260c240c16120506010b0f031303023c 65
    0x2a6820303041000510a00f0741d00900340060050784c2c44139401d030354100450a078100814045007d20640c280c01d140a0101504566001e810b00d00f4141c54040c0a01955000144194000d4021600c10f800c1c05010300e01290031100440d0301d10081e00644403264210101e2070030b40c18103006c00501c2d1042d20030000004540702d00085401940c84107040031650b001612a07401000014020240032031640b1482e15205031740c2d402031124161490303c20703007003040032903081c41810382044008001d00c6c500b0400c3d000017040c041c03480c042603006880c0003074040c501c07a5003540302c100100100c048195040c41c00b090056060f01e96604408840d00a46003c1652480c0070b00002220741c0888030381e50b07130701400b2245401032034101845580080c4100305440030081d0f03020b011035008040c0508490040c0c4480e1600c00e0400344103910217403070b000c02070100360701d079542d960700362544035a890010090320b410500f012464018144524200b1100d02c1d07071a5540a100c1640452800d510b00e04a6480d1031401e4a200760707206 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 946384271 1250 946383021 946383041
    0x30a24110c030a141e04031217151206011514090a030308041112010621120311070c0e0709150e1003020c07240203280c0614060a0801 59
    0x508104058003070301d4020010400d113003001303d07442800e014442c036240c1200301c0d01c00e43c5003000403400314080003080301801c0d101f261090103251901d0014000c174201e204a00e07001d80108000400c80c0c48440060300d4415000d0015608034040741c3c120b5039120050103608410f03010702c07000200c02c03200540d142d0800b0811a0340084004c1c2c0315000c0c0b1450345e10101c9100002030011240ca080803400031150f50349400305038040341c000340000100c1d1403034024098140c14000d82da54040c901d21040782000b0910002202c5800702103410041210700c0d80219080d4280309414004242420054001c41c444c0e5940c911309104040300d0b20380c0d110160312076a0a0034418007220341c2c4800100d100440380c0c2d050a10761355606940906090243c2402510240b01e41401c1c0c09030415180c09008001e0102440d10310001000c0c440700d207001461a19034010512000b80f0404c03150031703209681c4104802c2002d4400c10020300500d400c44d90802880c514144079032450711701a00d07007510a05003103901046803c0d0600c82c0344003031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 946385521 1250 946384271 946384273
    0x11d061e0d0902190e0a051915151b0f06090b0a090218040f170c010f020c10140a05090c10020a020a171902031e07090513110f030a24110c 61
    0x196039540121005040024410800e1600103244d4441740015402740034078001c0b04c0055a2012401c155581040e218080d10383c1e003c0041c003100515404a400001c031450300e400052902d60f100740d03030903c2806024a400000c095200200c1000b9082c1c0d5650f100c620068421580303201c02c0094a42410f00003042520050200e4034101142030004400c2c6103452403005203142c50605011080600a084840030100c00b150903800184000c3c8050040c0050b01c11082c0020741040100c034141f010260308807000b0a13008882c0e5a0b100841c5907010b04110304100e100000300340c0d07010303041c000200035220748888200301c1c0201c400b208003081c006c28200e01c403649c0740001001000d5007040031200e5126001480710582e09400f800c000c4c0004440d000c0811890036098400805040385000921170850f94000c100c0c43c4105035603400c0d0300c0001c50b8020003404002c401c45c0c1d104070842d0403500083c10b000ca0408c005143c5402081c036030080c141845010250160401410040060319902d46081c600c1004951000b07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 946386771 1250 946385521 946385549
    0x71e0c0f0e0f13210f140708070b04060204050a120302060a3b01050a0209091602030306041a0409051f0b150c0a051911011d061e0d090219 61
    0x4404028141c8a421a0103000c0810350442404e111307031425090001040c00280d10307400e603086043d4100d4407419542180b1800b1a280c4250303600c40500d140906a0020a440c541d000031600740b15941c1c040c0c03009040010000c55003942c0c0c1d00c240841003018402c0c00c40140c0200700c000f40340d04d0321500c10819885080203015420304860000368907030070b401d0004400d83d2000260848914002445624400c2c0110700c1b00694660818080051120b0028415411106100c210841d0581c1c04401e4940101c015180812041c0d02e11160b200783c404c4031144981c00c14507016a50080c80030005000d0b07000403820704285028154101b840c4150b0351748410541d00a080d2428100051201000411500c64085c080d034000e050603070740717150510242000782c43d020071004541106029242528155481302400d0403e290030240c102100e000184041861043c0310206203804218403902c1d03840c0c00c5000820741c1d50758488101c10801c0003440d59000680c001c542580c11411150040c16900c415501c0340c5000240c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 946388021 1250 946386771 946386781
    0x609051e06060d09080f0403140f150a0e0d030902011d09060f04270c05060406023a02240405060f0a0f09080d0e0c010c08071e0c0f0e0f 60
    0x1c0140e000043c0c0030101c030741d102c2d4400301280b4a0f40150200307080445005c1d0303440d840c0d82072028212400380400780594205442107400a0070001d000006090940794440d103950303e0b6201880200945004240c950148540c8101c10302d903d44d00049003607100740ca901d4401d1102840403601d1601c440381040c0c001d594100130a10a20300300000b529641002000420803103002c0c0c0300051484088100c000f90101840d400c00c040084210010000e07100682d0254101450700000948c0c0c0e1441841100341a05840d840c0340c882d504c1255104015102604280008020505d00070f40e246404102c000c020401c000e4100243c65400301c0940c012a001030007004280c40fa40e000a503400c1010f41a10465540c074814180b10280317074001c2000380750090100c10f460303d01d0104000300755002d030004480180c1205100080c0b680c2c008046600041c1c0140b860794481d481894511200aa06031901900020075400c00d0308100c040d014150942d000b40c00380c111000e0b56609008080c05094600740701d01c0c04030b000090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 946389271 1250 946388021 946388029
    0x9030d0906060506040b130b0702090402011b06050c0904150e160e090703020703030b03070602340b13080106180218300a1203020a020709020d0609051e06 68
    0x103540e4081d0600082081c0c0c0e50000454903405603000241c107050200301d0008103030000745a940144680d081c041d28040382640017640000f00140028140040c0800c8401d00c2e02c41000740400d0554031070010400303070404860261040d0072100041d4071aa0070021481c0048a0224168049810014100c2c40340e442c0c0100c40042078460000301e42c00c000c0300780310b82ea0059681480305801501d070760b280180c0d1a03c1905004003620500d0001a0182d0300c00d81c410400f4550004158000300009140c44114070320881c001110306410b0001e41e2000c811240003c00e4941400e0014071200d50000c00144006603100081400d0b81c03181d10401c40348444203448401010143d800401000790f00c00d0031050004140c030f0002d240c0c000d00c42981900007031445d4a100d64004540b2184a2260543d401401c010306a80d131964110182065444100340c0c0120348100322074000c00070340c1e001c6e0010840c29526107444100103030040480d0303c82c0719001030515011a040119180e000d803c040c21070207004e440c540d50301f0180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 946390521 1250 946389271 946389281
    0x211b03070803070515280203040314070c050609030f010603110901051e0603070306080d0e012c0d050a02090429010e150a0b1b01061502100e01150803070b09010509030d 74
    0xd681b0401144840703c0081c1c44400c810807444100d080b0042e02d904080c1801440105881911520004204850300c049080b0014120480e43d0445900e074ad251001008282000301c0010042c10350342c01c0800105c10050907032420728000b2426507142c02541c2e40c4208000075085480e010b0b1000000c0c42d00400c20501b0316000a540c040414140440c1030b598400403145440c0072401c203940010031000b20a59250780c00740c902c000007862000c4000410400c0c481140d0485c010000c268483c8071070b010349804006050000540321500107050a000e440c1c81e00304100703100e03034100030300b201c0360400c03c0c021500d91441031b12241601c885400d680410307074910b408040c050441c030090550001c03400318000b07079480e41c601c01010071500c64001032034410501303881d841c00e40350681c01507802c24018541550350183e002840740000d508031040411401c2ca0b00803400d0051001a000380200c0c229003a0102d40c4040020007810064480e01c541d007100c0c0d540c0c034a06422a20141c030961041d03003040145220140d070369040307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 946391771 1250 946390521 946390531
    0x120b060f0102035e06030b0604051c05060c040602010f0c08130606090e030c280206070c0504050a020702090f0106020d031d060915010909080702211b03070803070515 73
    0x5000075041d01c1302d40001c810028a21504001c0d03903000c101851a0203185007640080c1128141407091500300400100e0a000d2401180e000c0c04c85c856910a607100d40c13001c1b444c4165000011780c0d07001d060204070408560312a01460307000d9803c184011440a0281c0b150400000300d03076a52601300e03192894040b00301e451000050b00d880d40c440c1400301c0c1c1001030f4400da10010f0706c400c0040d551010300d19022400d10201009001d100f0403659040024403011340e2810600c2541103690a0303035900c0603c2d2682e24098150402a0480d03c0d107000c0010f40186030b4000c003056030007260202200d5468041c9107050344024001c510040e04520602c000d45806034110110607030381c2c60110b071943c5084041c980d03e00340c4215081500b990103450541c0c481d200061a56014000310340d41400781200d0b0303455001d002e101d4180000d024078001e03030301d5814102c2e0120701840c5c0405200103032081024089500b10794106101e40d410302c24004e90800252242e400070440d030790f00d90311034040e046209400f421854401c1000b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 946393021 1250 946391771 946391857
    0x80f0f0c010f05010609080601140609281809050c0f1305040b0610180b0a0e03060a050402030d0f1d01030b031e011104050f09070306120b060f010203 66
    0x11441010340280245a0782c1000d4500003c1e02c0c0d0324120004003070400a901581d00c41e000726005014214200003201510704003524070a40e14011a0045440005118400108281c220090000c1c1c903840840c0343d011103610000709211821240d01410072522000001403150b0300000584002d0b0419440400c40307020010034961911340c10040603015031342d0403507041742e894040d00100f10701440e1020310f1000c040610301c0d048140c0e0803004800000d6240f98000c1140000c000f107051b42c4800d00c940d015a26181c000b13016074000d8207040844070041c010640742284640981500d00c040940704002055200c1959551600340f070889070300b00084490315114050400d61500d4282500d03840030030004204400001c0700d0b0100f02c3e280d1201a00312400074420a003c1c03a8100420007050f56500c800c86c01e0510704854503041c948400701d05400424442e07100d000a0309224031190b041c0103480058520410090700c42c803000301070b10001289c403407140b1248103001e28402040b000b1460245030104444501e018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 946394271 1250 946393021 946393027
    0x3060c0f07020f2b05010f0e190204060f1e050915010305040218011706010503121c0e0706020307170f03012c240d05030f0f1e0c1207080f0f 62
    0x104c0d0119810714215010a25030455009602004424410620008500030041025222110fa00c940310b0486621302c201c0d420442c016181559030b00d5001c040141422003007440f241d9998800480c0e2041c1d410241c3e181c0340707044a0001018108022002c0c070030201300101c040408410001940101005001a6001003480c51500000000c45400324060301c807281a841c001644100080e140c000140c2000703009420118112001e1035000050716a461083d400007204240001d010341c008041280522095201e50040020042d07000310003000d420f03000d144000410560b01c03080703228a02c90402000300184c41000108881d05c198031042c00580d04800000c40d444413001040190504142c6d550100020782808000450006445c00c0c02d140000742c5079004c11840c2c0381c456a841c0e00a43d0392100092800040c41d00001c8040c00486201800c1e0900d6554890040b0555034056002490824814070400220740802001b0f6000e854015503c4603095140854215403c400c1d45c11005d801e025100d014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 946395521 1250 946394271 946394299
    0x160807060203040804050a141e0d170a090e0f0a1e02041e080c09041209170105070314150f0f12010c091418100506030a0b03060c0f07020f 61
    0x740011070065001c0c2e9242e030b84071420078007008424a401d901c200c00800240780081000e46035000b080c8041e03690f0b401c070814440340201c00f013003800b0b003846801003c0a420521080318102401d010303109400382981c49544980e1a41342d1041240d1054901c2901e1104c9000084c0c03400c403094000d14444041d91420b000040b00b40c0c41c415081e038000c6d4125050070ba020403010464101c0c410350080040200781c0c003d04038500390300f000c69070301c220292026040c82d10300403c12031014055400c02000f403480481c0e209075403041203040d40c0240420395070880000e04120313115074004c580200301e60040d00c0080a101d130801e0301804202c20404208403e42c0c200001800514071940c51042e51090740580705d00100b107204103401d004180d9802130304061099205c25151240940304c1c2c2d034146159000310b0454508a8480d101d003000080059840503520910005c100070003440e00f90030940925800790300316003440c0c80c0e00f241c0c2d074010300407640c1c0b40f42e02a50512810780949082d804c81081c1c0f020161003050004c5003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 946396771 1250 946395521 946395533
    0x3110723031203090c10090b181f0c020306090a0203330403020a060f020a09030b060a0b03070216060806090408131701090510060e010308031b190e010c0305160807 72
    0x108a0381d5136038903001141281440e00b0704000039071040410346000340d511800c0c0f0176540194044c0c09210305259070f504009014a071185090503815420304603007480076022101c6c0041880790740401c00c90013030080708082a200080002d002c0405035004010b04000300210f140507169500229000300c01c52103944540101100003d1144e008030b002e54081c0440603900c1c107000058078600700b906080c4903c10130030809029440000c520035a0392080c0c90b010300da111030700041c000501a41042c03840035000410300c03042d9500040d4042c5001c0741c0240d602d031059903500c0140c03509107040712a1604004075200150008580e50001c05801e03441a0a03541d8241d16883c01140800640c5910920b50790350f4600c078403c0c0300c3c3c100071614001d0482c10040c4840c5040003035180c0c0d000c406201c024503c05000c0041165103130191a070401a47c0840f0030319891b04401c1d81c1d10842080b0400c0c030030022490341915030074154402c840407200300b43c050f11418500b030305448680d008003009440c19550342c00203104600c00148 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 946398021 1250 946396771 946396777
    0x1090c0608040b1b09040b01050403060c051207020c010c080702041b03020d06050307050f090424021c1803080c0f0f0301080118051009080912060103031107230312 72
    0x210307550168549454540002040400b0300328245403030341d51303d03860b51000302e0f0f000b110075082c010303140410b1142004005071510301032500000d0405040040c0c0314001a8000094208100b4603030a64a0740e07140c100c000e03a16540b0f207000150025064120072000701c1c18200003401414809000001c107589602810500c40b503c000c1c45400081d00016a03003040b40072805a60007400b81200600035003480c040014070035540b465035150180300b80070006400d005413400200e21405c0c04081225819403a0b80054009500218074200d440341c00018169400c45240f08021040148011507070a1102d1901c0075240842c006102040b00c41c0104092500e04010308007a140203c0040b41141c2c4a505184144c1d00f0b44610403100c0d02810800144440030910014880c52400343c001000a2444024244040c50340700f0700c420f42c0d820084001180d0791070300303000400e14103da0003541c0b2506042c6141c100940ca41182d40b040c09100c001107000c60042c43c03190a051001c001000f4121490700c0c083c0b82d100d12440e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 946399271 1250 946398021 946398029
    0x1e040b0d0902060c1b01110f061603060b030412090f0608043e180606031501020c1005070b010b0306130f020c06040b0103120201110313060605031b010e04060b04061101090c 76
    0x5420038146020950f00108610562074001d406008d0501894070000d170f0f610b8005003080c25071540b1040091881340281e01040160030b0a5101035600d10b030908040c0d07584044100d1742000511001000a0004409554082a54080d64a4107119152074446e510030300445080700012441d2400652280c60540700780fa00d00800560081143c0c030304075010011441d4a14240c050b030828581c1c00c20260381c1e00c5408407948000c0000c14903402c4a000030040703250130340440740c5640018650864403012908031000c0c002031881925448026a2685c0030041ca60005880f800e0300b01b40c0e001030202c50703c105500b003078002400d680c0f00141000c1c50010a589804402e8405071490024070005005004c0c49002c1c000840f94240000d02420b65035482c0c202e054440103041c09510b9140d40188820007020f508284003c010041c01c80e400d608801c0000003110301c0045400d808945d001800e400e4909217805a141106d01012002c0d042520f0400141d50000c2000385040c56035503510b0806000070b41c100311060240c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 946400521 1250 946399271 946399303
    0x2160b09013515030a080d090804090603140d051e0f0d02070b0115090e060f09010906090606181401090314030316030513031b0b09031e040b0d0902060c 67
    0x401d0a00200315040401510a06003a1003500284043c1e40340060782c030f6003460340541c81503a03684a102803000105107002004101340030029000034200c04503002401620f0144c01b9003a12852010f160594882e140c04100c00892002d010702c4442006414440b580100c103a01d0b46840c01a0264481e40d25178030600385211116408118403090010540c0c039203001d4032110a80700030344c000050002d015400c043c0302e403c0314241c1c440c002410f42d4554104590480d00050b00b070529a503110080700c80988014003a401846151210001d5064490b03501081480c10380403082a80310701781030041d03803100050790007a814049444400400920401c0c05500e0342046140a10b48a042c0300300985600780c104a46481098100410b00611001b0401c00c0c101c89a40350403c42060a405200344a0166040d0400313002541d13907004100600c0e101100900b002140058010083d90001e060a0003d0103180500245440240104003162040d43e110503c9540020001420a80c0314900341d807600498510750700740 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 946401771 1250 946400521 946400597
    0x90102091306060e2407020d1401060501020d020c0d110d051203162d110304080a0b0c0319020c01150b0a0e09060f13021308030c0d02160b0901 63
    0x180e40c0b00c0124246003104031528040c0000c2d8400410700d44003040d40d40500b45e500000e440c011036684811000100340d100340d18088903040c05003864000c1055100361809030081ca4078141a940c4046040703220407100604d0b4040c80b5525450795a000c544100da030307680001c4000c04500c0450b1041042d0044160610703940b540d64500030800300380001e0703170900b41d07424003d4040e0001c00054007139400708401002541c201c0c00050b203890084450300011070300c50030a4000090003280c5002c3c00708041704140c0c040d1749000c5480e00c400e600d5070714038802180e0003c294a46400202c0303001e01190010a0300b00845400407c0e10f40c0000440001c03900ba42d03021901002c8001130b41d40301c50790400d90200c1800c0c070403a821800d41c500803020070b900260900c0603522400729121043da4051407a415925000000e40f0304000b00e9444060b59592540810b0010206215080d901c0b1842840010b0909139900c0085d45e5003a5240342c0b800f018120742026400c18140101b1181c0860440807401080e450b402c03001d803032550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 946402877 1106 946401771 946401779
    0x302010c0b1017010c09080c030303130309081f1805121303050a081b0102070f080c0a2f06121810110307030e06061503090102091306 59
    0x2d030509040c81e01c0f640c4a805501c6403070415420f40b11030b8140f41d2518041c2d641d0f01c0c50140c02c664160300070000140140b003460700198149103c0c0c00c12041c03407910b0305000ba04051000c0c0264541e602400281d01520b1441c0c015100d180114001d8480c2070092500d5072a00c8680381118003034140c0f00003900b2902e4003d00c40e45003009540000c1510031400c1c26141030342403544040d00a0301d01c1d110514011130000d0040c400c551070198441404084a406a074440e23045820000441d100c60061a0103400464140019400141c1c111010040e50404500c00b0441c11040e0420f01802a04280310003168406038001c030b0390b00f0508000810f1003480e1080e82d070501c0d1480500041ca00141807183e071001c0340302c480004d0b5002e0850303604c09104003489011025034510040300e04c01d900c401c61340c03a100030f1000000029604043c060001500c1d14510070049070716080544003003810a603a841d0100 = true := by decide +kernel

theorem cover : BRFrame.Cov 946223021 946402877 := by
  have h0 := BRFrame.cov_init 946223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 946223021 ≤ n) (h2 : n < 946402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
