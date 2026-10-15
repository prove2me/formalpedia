-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5254
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:15:16.428926+00:00
-- url     : https://prove2.me/submissions/44a321a5-8b7d-406d-a132-e18effba1642

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 944784172 ≤ n < 944964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 944785422 1250 944784172 944784193
    0x1020c0d08180a17091206150a0e04080c030c15010f1d07080a0204090509010207110a080c090c04090c090e0c0a0207031101110601092c0a020f0a08 65
    0x1540c0d030800510100001d01c0410004000781410108503816140120060070300c0d02d801c2c0c0ea01da420301c0550400120310311091002c641a0f030740d0280020101c003c500701a10ba2400e020032107000801c2c44280190003481013040810003002190141c50388260000e401a03200e0003903400d00746c110b02c11401255100e100b915008100f4141e030b002120b0483d101022b441102c0c1e070340d03100d91a08880c119102c0340d5a406540c40001c1890740241c00d0713a58001000700c0d0041c40c050b21018400c04407502512503140c01da40c08550700c010400803580c02070100100701c0350050158030300b02540c1e564040c80448980036400740000700c0c90a030000c0090320041c0401c0c2c0002c1c030507c50807035001003030007000d4400c1c0e683ca200e42c18040394507081c0c00002c80d800c0c003150340d02400700a030442c0c803480e10700c042080c0740c20304201c094980000b81200c10312080c0d01800f802c05d0007107041180d09624041d100003c4144010112080708001e0030840b0008400034800d50556610320808041c1d07000170b01d0140c480d8880000740c0542e04406 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 944786672 1250 944785422 944785447
    0x4021e0408010f1a090402040b0a150503010503070f1503020a0504030b180d0905010e0d0213110a030e010b060304150603060e0f060a050705030118062610111b0f0102 73
    0x2000c3e260441c903400c2110300144104101d0400d144a030894200c078402001c11302505040d0000c00501d0006409202d60640d6000321194071014229480006070020005100e0351a050ac0312074000c00c0324003450b40441d8140005070300641c0d1161040800e059000401807051406181034070004d58000881072035031300ced041c56080300007022211070701c07001d001d40300429200e503000c1c20141c015200180c0d00c511801c0c03002d80c14000603003164041039070300c4424480311f03c07140b07c05400744054015010f0400740d10390b800c1c514003406851903030a0f0100c07680d0400802680b1501c5000075079a01c81d8000022900c401c500700c1a01300140450b40000e081c017418130320320707003130341310300016040c0155684c1800c4440940e2540006030884006581c40c8001130000c1004000c07100e8080d40200d40075441400018201303030754a1a01308504274032000f4949240c0444a0160441410f00040891100c110f00a20685010807000304a901c164030342480b000b51582e080001644041206914030590540219619101030302d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 944787922 1250 944786672 944786681
    0x51b010605060d09051e10021b16060f0503070f1412010803091806130207030528140a0e040f020c1605030601050105070305271c030e04060f0504021e040801 69
    0x50724203200381d5591b000d140a18082c00e429516000300504850b2002901e54000307580b00782018048440d007400300e40c0d20004d09001c2544141d142c81d04030050b10785003c80c05800320303a034003040358107000d001e00030030000540020303c910743c00c241c1d86860343d100c0b019414a40e01c24004d4010b50491030b146100045500ca20010042000c4441200c01c40c000300500c511600d16a032048640a800001a4260003c12600c80d009004aa40300381021420042669030701198051840e0100181c01c100303d6007080b80c10b0b00110420048407190080c1803821610341c80c00781180009011a50003280c0d500035a0041c03400e0703941a6244d069500301994507104c603003d03611f5070480c0d4034014940300e4000d280c00000c080d800703601112102941601c545042c110000000d041c0d40203040700680210751343d8000464503540d00c0000002c42030b60030078403c4052419050040c2158500000c0c24080e600d4060244264903034a00020121001182c0240e40c0340425040f13103107a00020000401d04034408200810480e006410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 944789172 1250 944787922 944787941
    0x411120403120b22050a06030b0702030301180c021509011509060f08010507081b090a08160801060f033c060507180905090705030f0106060905030d051b010605060d 72
    0xa0003204900c40c10080d941d2484020301208500d400382c2e543d00418136800442d80410001c42c0090704036625210b104029000303c0700040144c200000510000d55002804807444000d0003040100d40e04082001c0c1d61428071280c4090345030341c40c03030004041e241b00b50000310381c0c44801e00c20b4000c0e907a582d040d5000a0005e9025244800b0100040401c28400500ca240d100b10388030340d0b944000d81c9036501c424001d0a5410210f00d02d1150420002c10aa1982d01d040340052034150002d007450110f0b208030440c2e50392550480038069041020402000944940740401e40c1e400c403500d5982c0c0c05030092020700b0720aa034014850811540440000c00c075001c001c0300449c00e40500c5050080d6980c2c040100d40010481c621402d8840500d42c0500c1031307004035130003140c1c0310b058142110020f03a160704c0020f00d44442d003c98600f50340e4480f00c0610420358010207130401004150001d205814035100c006e011405149440c03010000c40140c01e214142003500000010940035104a5580c103402e151035024280300507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 944790422 1250 944789172 944789207
    0x2040911030f152a0304050304051c110a03020105040b1606051f1e030f140a26031506091f02010219080402010c021c1e0210020f0a020411120403 64
    0xc002104d100c0001e88120701480e0b41420071299415040d142c1e0540c1d000504182d800e88001c1c8804641a155010100c2051a900e03441d9141c034a12450000c0503400030005107401141d5481003000181d8000c0d050b45e055a501c034401c5520351401d08100d14407400001d502030046400d04040c400041828207a9414042040448a40c59900e5003000380b40e007100c604c20010040703109081080411041180f0450780752042c000f80a00400081e002c1d4900600c1010543e401c045800d0700200c25048101d600c42c00400d01c908131415441c044400507189030340300900501034600019000d076682c0e81e49044200c8540c021460007001c1040e040024000c0d00099007200c007107a101060b1a400500403910b00e032003160b059442e1316054000ea070a105401405141120094541000400c005200d9007480c1c459580b0390304004962031258010000c01a0310050340c2000e6420106020b826032202107900385c0d19580685c0e01007075100c59034200412601c11420382051800c0403034103000401d5400404004080c0426 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 944791672 1250 944790422 944790463
    0x1504110d1401121e080a08071e020307080306060712030c0306170a1401020d0603210801050108040f2904110f0a091a030102070f171602040911030f 65
    0x320904050500c28090221440f108664400c0000d50108841c0f00308481320030140388000340c03075039085159000845d1400c0864403560810a449034041b0190101030964120303108044920200039403207105001c0b01409a1400100145c116100c0c003080f10103143d40641406a410807646004004101d6440c13080c0c002401c0c140c0019443340da09500f039860b602c0f840060210790f48141d48000101d9146052281c4a5400f80000300304401140301c3c1d0703401140100704401100c0c0768500703001c1140b0100e1882c04188860309005000030303644901d45552140d1300102800b20754000741061400624031600c0701200200c0c07481200e8903440c000459a010b10320401c1211440300094040108131800c041026402c00d2001e1406c0011070620381080d07402c8080e4103003041c0000f042c0340100e82a64450181500d407013035050549000c1040c550600e610000010143c58100441c5402290b00003001540203842070741c4035503009060290300026020b08a80041c12a005c1c112040b002da42c86002c1c0805000d10700300780 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 944792922 1250 944791672 944791691
    0x1c0c1112040e06030141040228030c06050a031b08061e06041410020a0302030f09120303130320100906020d050108102301030b1801090b06040b030f060606031504110d 73
    0x14410f0b403409170b6401000340e41c07142d070070f004109c280103a02a80948040000c2c2000004210034807201d10262056607100750381c800120401a0988010050b0051840b8102e40300d1425154480201c3d0b0b04a00222440081e58100890103c80d11018041490b48280c0000340054541a4903064218501c01543c904000360703c0702c00180d031107201b245006000342e04108040011640c0040c000c0c4004100108016a03d0f20013060452039600b04030741040550074903800e42c50900d5080030040510032076481440042c0718803800090f895144251003862140d40341d4845404124003030b0107a074000c112a4100300b240b503a60702d03041c1750781d0101c5030812030040f450803c45040c0d1112509812060400040034044a03918550b02c9600e4900e006000c075141452502000550602c00cac000c11008602840d80007045042c84401c11088034000c02d00c032031281d40034442190041038040b42c503c1d40542c1c12039140b601d0b541c80b1806071801c0c0304a6008658401c0c40c0010327020040f0604400b50201e80c0403600c0c00c002d960391 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 944794172 1250 944792922 944793041
    0xf0b0102011b18090e0a050f1b010302030a1404030207050f030102070c030b09070b0708070201080124080703110403050319030b150705031c0c1112040e060301 70
    0x4040c2c01008030070070041c8050840600500c2c2c180300082d25504106143c541d60031000d422510841c0c05036529030400a2000c09120081100c0e00805488e075003d018035400b09030050810344081481181855004800107566581c1c036800764002e0038490807110030314502481d000751906c0890081034850030650078030341c005090500c01c0d08c801075801100340030034034210b444040e031800c80107080d80782c00e20a0138004500c8881c1324001d00f4065109419250700c07000e0f2072001400a0905800005c0c540b404001c0588c403150316a0050445c40c1d071641014149500c802c0d400310301030840300142404e0160000b600108020001004040301c02102c100100b04003030900c000c85c10344082e11b2403282e208150300818000c04420784020700f82d441c8114201c03450056a090004030a003d001503461110b0345d1401440749064000078070070310814001c1d0242c4010580c1c2d05041066018a002e00300c4070040740e10005005840950002c2e480002c2c0300001071070380030300c0e10861541c00341000701a41c6480010520491420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 944795422 1250 944794172 944794181
    0x906040c061b080c03090d0812010603021207030f060806100603110702150a02030418020403020909010c050d0e030d0504110307080c0f0d29010501031112010605031b0d0f0b010201 79
    0x40201140c010046000c0d100c0900c513400042c203040d076034042040701c00120f94070340c0441d2030864440c1c84901d48481400e090781034410301c140d225109250040042611f485010f6000300d612104038140010250b0130b041d5400c00800c82e5800042c0140b140009020200d02c1e940b03c8002113507025582403000b0104200071100c58001c1c031000030b41048048803030300746d46110346004d890030000300e2040f030303003801e6079103908098803d402c200307040960313900160500c154100504929403060181000b07100c0b20894400060007407144218080b0083d5070b6001c03001d070308071044c01110360b4582440d105000074103081c10310400040a404050348640300709032000541510119910327105c1c3e8001400d40b0802103a210500980030302104086592441c00004c011003401c02102c002004454400087c0c1c03d0b40c1030100140031200352150f241003901e0180031014484140d210410705462035450502c0d1203441c1c00c1e4a40401d00951808225007850100d081032460b152540300d400003040020049c03160181748801079080740c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 944796672 1250 944795422 944795447
    0x1906030804060c03140a170924100306020712030e0d05040b16050102160605010506162307030b150a060f031a1c1109070c0609020103140906040c06 65
    0x400c0501040065500940014014500074181704210b010508100161580004916004900000c1c028843c003500200802d911880160003003c3d000820303961403005a0703080300603001498a410000b08060345800201c002550301c8101991590514500040c8015501351072500103850547c03070001d4000c000540304c400a4647d200e90745031030b040c015144e81c5544a009582407100e17442d0561000900c00744010003100c80d007094228009407131450810b09503041030b07100c5441a042440031141700c2400d4860015103650190b45031100044c05503902d100003020180e0362820b409111400414089011b8100784101e00d03017140b400155001c14208240e100c4103000e84400601000c05000940e0300030350007a15400c2c0d000b6016150100414000307a042c00320303000b0b0006050f45291111080112500d04903001520444843c00390f032038085401800b045c06008007031310040c0c4801d00f050035a4020b5001d076a44200758a4421340d94179103202101d59480c01620100d5240001b40e03000a1424405c800c0319809 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 944797922 1250 944796672 944796683
    0xe0402030f010212070c02010318030f020c09160e0a09090503120a09030c0b131704050a0f03080307120212041a06030105061f140307020f190b0601050c0109120206190603 75
    0x200d48590000702c03104402d00341b00705d0505550300d00003001e0302c8000c05000240e44c4a5602c125030641030000081c14000c0340b0482d24050a20f0405200c410b07232810a400b55058003074902004022240c130001481d071141d40d071180389a02e1074901c0c542c0c00e002001c40140b0261030304001e82001ca48591030a0300c01c9921100002e0002140c0b0341300c03540010001c4202e01d0700852a16900d401c1805c240e10352080c2c4108101c20341000401c001410880c1d030070b014034450014005500624640b5281d41c07034500c035511000302200100034101100041202695041d220a00c001550942c514501483c2c0070144101c106442c00502d101c0b00c002400301d140500405120ba01e02424004e6502e0388040c0822048c4100b00c203010500074150361880a80003448083c42c0b0a0b94694000c040021550100038286500803d184042e01c032905240004544018040e5400a400380780c000d544120000c013403401044402401800740140552152601e5030000d20b49018180740048116841014103100c800c4076441d2100400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 944799172 1250 944797922 944797957
    0x20a11190b070c150221090601030b100801020408030403200307030620031e0c0a09120c050414060108010f06120f0b09010315110a0e120c03070e0402030f0102 70
    0x40c80c07a10105402c10224106005460016500c0c0351a0001e5010102d2525502080700d1101d40d900e0041501c0d410004008900c550502040540d1100d0050002421803086807000c51010b0011074005001896483c00843d112500c0d05180d60f201e5120707200681d50109603a0020010300016032034120f0b50000280100340c5039142d2b40d90301d0f01401c80721b400c01c1c61407803200035030b442c80c1c10039040250b00c0303000d01e80c0940d02148580d1400c1c461000e0040c100c04c0c0301c1c0e0410320400b00f80c507030040241d0050b103082e440102c6001545107800d070f52081c115002150098104407101038000003086a0310301510b0240c85001d030503070301c9d030162500040c264131484000801e55078010140702c00c0c0d648018103000351141e000c0743c0340c1c3d0043e0120f50b807410280c0c403c8421003d03500141c0c040c3c0b00c492181507090b031242c680581c81c0c00081c1344001c110f8003011a100b88038806482c1d450b8038001082058000000e005030170b075004250303107800380302846134105c805038004e000c3d485003c40800e01c1031080b2003888102c1c1030b80340c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 944800422 1250 944799172 944799223
    0x210807051b0c120708010c0806030604111c05010e06071b0204050a0b06032502010b0901151731083f1807031509060b1201020a11 57
    0x918680c1d80038072001c98016240c0602c1141c907065424150400e400c0f0007044c3c107030320f04020700d8212140030313100c0400c00040d0700c24452141d401150003500705400240010f0868503441c0014100a10046008031040a40101e4420403006400ae031060072460400d1300c038031740e641036400c0d1399114202010510504a4401c000011b00c1e1070351107150400e40c4020300203800d040c0040451141d81c01503910510000800c0301d103030b0481c1c00130030032003080d008644000d01204442401140d411401030107451a0f001c030030b450303006203c0d02c01c81c04032040588020301804242058000b03c0d0f100f01004441d0402c84200343d5601d0007446206a1000c040740c0d00c0b4039030311310300301054140003204868510340b0305080c0010b031860042d1400003610520440a44035146c50746003040d51141c1559000b94030006a01d411501c001c10101b001da22402e0304252062401140e80c900d6485c01400401d2161010b43d4001600c0c02d014402000541c0a018405450340b20906d2480d00320488507660040c030418480390007071003403014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 944801672 1250 944800422 944800447
    0x1030201110703050d03021e34210c0f06150905040503030c0f301e0601120204051e030d110c060d06090f0b0901060c1110020f0a21080705 61
    0xa050046400031000000c11f014148c00d40d143e40700151208104c1c080b0300e07070b950185030241003144030340300042c40404001e90701d45e9640e14844071410036099414600c0d00f40a0341d16010701d044d024515031021010070340e140d20386044001840c000c0252522504507100200b60f2901600c40d59008030b030441e001310300356a9105010b0056500200c0131044050003070200b25100c50701079550f4007403504590020340807005040d0107d140900001c1c4800f00c404c10601d68001c50508024925070171440c2868454113200d03e40610743c010740b15540c04190031559000c001c001310022018441d65030b0004805507190080c5007803040b02d1529801d03207840b9090b0060600ca0005240880042030b05146458000ca80c641da6900e4032000c03203100140302d5030010749070b02180170380d0701d0301d608a50702414040c2085210706000d0346401c03034510504032466000e08400c03c2400142402040042c20001446040700c01c090030301d2a050340701843c440c03050b2420900402d50a0300d6503000304142481a003003540c40381d00b00044030544 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 944802922 1250 944801672 944801677
    0x106020f0618070e01090608011109060a0309080c100209120a02280b0d0b0a060305011d0c07020303030112050c010f080f0403031e0e070b0301051c080c1501030201110703050d0302 79
    0x16030b40c5900c10007500140c40e0328000030060003462034040000b600740c03601e420b890075144803071482d040e039600410a0407182d03a50314095030710b120024680003d0064662600a00b01e1007061850f489510800c3c1d689949070307000b43c0040c80c0c40541981d1020244070101100c0c3e42c1c1e40501c81000303601140304940403c2c07441401604000381c080710701e84451025a204c059004582c00003007061030701900c40548182504000d000f46000b0034540c41c0801c8150701d888440c080e0a03021110750611302d0582d9011a80d004520700c10f544450350000c0070f582c0c1c1c075651034030003403004160704000329198000c4203a400c01540c007541600c42d0104040c0c46151095403620300c0c41c000c10500600840a1590724080c1102d1804065511000c0002c564000200010340d55440c52406289600000a42c031003000140110b4403010002e290240b00c030044004d440300a45020f0210b40608601610715110b920030f4200d407031043c41c039400d040b13034003c0e01c404041041d0008013030b45a01160201810540c0050102c04806109500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 944804172 1250 944802922 944802961
    0x30e09040803011a220e100b0906090f040509072607060509030f011407501303061409120d23090d050412080703030f050406090303050106020f06 64
    0x82c6186480c5d02180603019800c0d450210001d62285000248406440c4444440e0420781d6009068501490140c00c0a014440c890040b4046e0f240030500c0012500e80c800440c01400c03006000f8041e138502541c0445d5510030074407410010a0b40c1c1c100f012186800c072610f032645000c814019101580c10060f090320366500054207103400d0303c612295112045401e120300700c54055001d41003841400d108500500c2210400800960040b1000320000001d884070740d140903030044140c0304404203e4140d230280104210ba2000e1145803400203164011030268440942541d1244401b00503007690761819122103181140c0c0b03540f07254004400080c03240c40440141c9000c4125501c0401c1d1001c999004030340745c51544043d000c01030300d41740620084020500030400510007a217081c0b42041c1c41e00c42c14401010030448007400095000403c2e40505100360404503155210101c140900e043c14079101e8001d041c2420142d0000e49040d00108480784003140600c40000841d000b0b042c2500c07044181440d0565140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 944805422 1250 944804172 944804219
    0xf0510140f1f02010605041d1518150714040b0a031d070e0405060603150c0703090905040503070213020f18030c090705130f0b1206030a0c080109030e0904080301 71
    0x1c450741002c01c0030510300781ea1021540045566854402070200340d0720112080c1e040401c16502e1042c1c1000b0010f00e400da040c0c050004440300b52600350141400c482490390120060060042d028850904001e12a000722502d42d01e04141522402802d40345000e10b000d08104503d0410029220038030030713004410180380d01c80d0400c0804400103860b51070100da60380412052200d081c100400c0c01024003210754070040580c09404c0e205840440b50888100081000789805000b180c07020500d41314900004c0074200c9030004000504090410715504d400411080744078842118400314144803038001da0344422107601001c1e05080c0c0302d4444040b4800e110580381d4142c401c02c00b003101103984410b40760303000700880c0d1035850350348822408450740d91700d090304105a07038010581c0400c00041000115030305014800c4c243c4041e502c1c0d0303100080c00c05107062800744c500e500520010512060641c400c1800e82e1207900d4801500740500c0c14441c200b1000c0314080c1039417400348010060b5103850030071050920040b5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 944806672 1250 944805422 944805439
    0x6062502030c060301080706202109040c0c0b070908060106120e150919110607030c020d08192d090f0f150e0f2b060f0510140f 56
    0x42c40031038199082680081d03019803280320200311450300715465a100c0e8a0000030f000e400c1d0a4100c160f9039038a0940510307242c0d03140100d0350408109480083c0d4965500081080c025040902802030001c0500e14094484504080210701030358043c07103000e4100c640c541c02034442c980c607203101610284039840c50444503544956441241e410140882d17880000b15141241007420040002031401641350741c4560580b81c3c803604080412034500001c440001c0880f0901e58500481c5421600e60300d98000080d040b4884103121000c02904d01c014042480720101900b590b410202c4044a14507155144800c01401e4500c40320643e40c0d0800103001c04e410541000b07055a9620040c032410381003203602005140c00c50700307014003a07442c0d5004a804103400302d2409020b9a003103000010908900c19440501c034940c40144014510032122085008545600040400c0891810650058407001076406225460000000d5400c0c48001c1c1c118151144000d18001000881041c800d01c0c0240d400c1056020500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 944807922 1250 944806672 944806693
    0x806120f0102042414040b1608070303240608060603271c0302040608060904020310090506090606060301030b0a1806021803120c3417060606250203 65
    0xb40028801003145002a03442044844044200040850100000c004640c010a282da520301c1e0199011b550304115102d641c0c02c5a410900c410800d94040142400d80100c0c0200501da0107030300818410b20080c9804855028181600c2555103980c0180f6022406240205a55092180c06554482400c041283d44038048041c4800a00104c0c0f03151581940221802c111403015011501800d080c0784c10103500f01401c02d5030140a1200050045000c5c04100c03000800b55a0100200a1400c0c3d40c981c08120f40c0804d400c285454020403503000310070b417041201081103400e0140440781280c0c0c21042c8102d00381c4640103110040c01e0450712842e0071200b009a6040840da03103100510003c04903060b642508415402414184034000c65124042d074010b100c0d4080e030707a1010a02c1602102d02c110000543d042c0c040c051220851848809500035042000219404a06601040030344100f982103c10f141d840c01c003080024441c10240c405904000c10104050411204000402502c000c084d41c600505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 944809172 1250 944807922 944807953
    0x150c0106120c060201060807050a0533120603070509240603010611010510060e0d0206070c0e180318040b030307020d061d01060302310606030617030a080612 69
    0x5801d81c10b0b01e0480806504120b42602480f0340b000401da018003404869290000140003000140300300e50041100c10b142d113203502400030210001c40c0815071404208001540c080340d0346d42100c000b102020080d03034085080c600d0300041100072544014002100b541d58104001011006804542c2007d00300304803141d0b060303a0307207800346020300000e590707030711070101c40c25506425500d000d04442608031400394148000341d0b22001e60412450150750400d400521440403803010720070008044c0442503c0c42000c00d0b403104007508503000300441901c042c01103560700000d03170310792003200d0001d00c2d1420950304c50851401c0035000729000d214014144e900300250340d00416603061680c0d000f01c9140d6624014071040d03210011407228105800402004420b0641e0701050f441100d0f0b03040b218a2440000c2d015100030100c1548000503d0b200c00184415555000041d01030001030003108120620046010807040000082e55125800c0e5a15180c0b10b8858009009c40c800380010052418040c1007154020005e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 944810422 1250 944809172 944809199
    0x7082b050403020a03120903020a06020a1209050102040303080c0a080115050d0c03050a150e040b090a120206060307170a020d05100e07080705010201060806180309130911040506150c0106 82
    0x42c002d4024000f01a020b10f401048102070614400080d4603008100d00440c0c0c3c0060550421a0300c1400160358040d00382c020340f001140c0104110a450408001d03808001d019001303041101c0c4039441e0320034103403a07035502c50185010301d008090020b4030440040004640c080100e002000c2582031151404070030000440555442103080b4012946132000d00c5040140c0780300348a0a02104000c1c10645410030b50707031105010b03000d0070260400440d1004030305150000d002c1581c1340d076030144400c02c140500300406510346104454a5101e4021918000341440701e0b45441171000451401900c07154006500300300c04c08840100035240f0b480744070103140e2419180d00c6040c40811007030300204403903031604201600c0d207003407504418116414010708115460001500d00e4001d80345454180070a15a4802680784d070007881070b1240e009884015003180350016034003106a035400342288444c003004420902c0306031101070311400c0d040450500202c4e0b003d0b41c1d0401911030340030082d002103040e5503150550314402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 944811672 1250 944810422 944810431
    0x80105061c0f14091605060d05220c1701110912010f020d02040503010b0d030c0224040b04081605010206070c03090e090c03160303021b01170f1005030307082b05 71
    0x3c160140b00012500300060030b03455049850284040c1d0800c03001c100300b03000b4000c0404d0050b864101140141400c101d400100c2c00841d1108041859241440140000f09205001c0040001d807529009039a040c05024090361607220700a19201d00c040c184101541300704a84030595588240001e02e107a0705000a1082c1040c01d1000358840742868205421560042d2880c0e00c9001c030186004000790300000401741e80c1d601100c85020340e00c2640700040c954840481c0441d104e01001402082c0b410122003c0c0c42039503440400c0303ca454407481c8664106003098041e86025034022400076481904c102c40400116204c0c0c54151110303560703a403d520310b011080e1005003107504907911000345400c0410810800005c400c080b44070261460320003a485180030a61305500d800030741210360569004070008480d840111038407d20f28a0700c05080e00700140160340c0e82c81c0d0300c0843d0b50001402e24000096840c0a034000d01800e00d4000100c4600c0920a41881c100686003900100c4d0304000d8194401c05219 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 944812922 1250 944811672 944811701
    0x70602010606030b010c110f013b010c0f08130f180b0604030c030803130f0c0e06030a080d021e120403090e09030901110304090c02030c0d080105061c0f 67
    0x750038000d014040e074100600c40343c1040b9003182444042040d40c0c81d1a0180503060710aa200800c9900040391104403492120300c000040e40b80301c0510003607460b000c4550f00c800040f0655440c240200460781007248407005441601300f8540a0045040e100c020054040385032048401e4503a10711f80072000040300d0f40480f070551240103201c072018100340941c54540c10201ca649281a0560359482c1c0e03c1d420720700014107600c40100000303060307115000c55030300d505400401d00e0800c0d0005182c14070100302140034030811620950041761080c10009081441d4a03030021500741170000f0340d92407000941046800c04d0156100c011800200d00c1d00c13200074260300c54204400c0c2c2c042e07e811706000d000701c040f590200411036000010840d44440100035120503610034030740602401c07502c1542c18554010303074000700e00c0d240c07030b001e60101e40c15000802059001100401d0340c502c803403008402e17209103009100e06604a007041142e40d402c4030f0403881e03804800b164481c0000f043d60141c400702c0d080300d003a6800300c0071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 944814172 1250 944812922 944812931
    0x503010b070b10331e11010b151803010b100e0a03020402071b1a0304082d0417060f01050d08071703011404060f060c050c1e0a080111040b0c0f07060201 67
    0x88003460003d60a45940319050907a940e8040d5000d151003500c07105e001004115001c050705400703210a41004010b40f400810007000c3e40b0706040e414049501c034038000031600c008818046400d08042c000c52200e40380041c0b21462402e950a003e548201e2514000e9501c080407103800f2006030746074400b81072103d00030103445e885038a82002220800c034054000c804401c03405012810001c0880080341c3e4060340c4005880e80701c20906c651074100a0b0700411078149080102d910050b40700c03800010700111107210700740c807610303422182d1402e4580e202520300006240c9110018015401c1505042a00c607100300f034142e2901219440d1014070411591801800720340000040040901509002d440140119410440b1a03d0b181106041129522580003481103224070502032000512010300768103001741061403180c1407465400306405808084610a42d40954082000c2c04140304502c9100114814140740c5405c3c5021296130360802c0c840162103118121004d082d4420502203c002401c10b0b0b0008107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 944815422 1250 944814172 944814239
    0xc0c0307201806030a080d0917030709140907031d0d09061205160813020a1e0b070c0b13150f03060603020901020601120311070605030a0c0503010b070b10 68
    0x50000b0b0710040d211111822106112842e0f0300405c00c10080303a480743d02c0a90f80c18041840b040078150800010340b210b5100c81c0502c6040754450020340c802d01c195030301d54420f280c5552510703101002060203103070480302c91800a842e49000f5400040740c000500701e00b100541ca01c0c01c03040d04d0030407072048030310000781807000401c190341d008496181e0301c010070303401480031745000100d16488003861007a4400300205403011030301d0566141c5404103440c2d0060004441d554032038020150003030349842543e0049807850320000d021315448043d07400d50760780921040f400500d010349803075094100003403013064000941400100e6401100003282080c072607803106040c4008001c0081c007201d40590114007410300405c00e03604c990307034089405415904640c01400e80b184650400329000d401c0d103140380c0d0440c8104500490b6658100c0301861184192031001d12001005010865040c0400c1c07240056041c424041d4100080040c0ba401f540003203108402c41046550b482c0e0f44d442043c0501707040e410f108031106600e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 944816672 1250 944815422 944815429
    0x10605151821011b260c09030d230c03040603020306040209090103060b01031b020c0d140609031e0a3f0c170709050d06110d02042c0c0c030720 63
    0x64049105509100c0c400381c0b03024a0550200d446940317040740c901d03400c100044003200c8140940b065010b010301120101003411002034400c2a40d22912240030aa200710350150700a2002200c100500c3c22004d181001c0c0b074a2002c0d0081d42029002e03aa01540900410101d41c0300c0036440b6008500880001c40d07021582e0001404561925022610803140c030070710100c805030005000880180c00b03541041904055041c5840071003c00001203d4602425051240003a0004007a1998542002d150040c24030202e0119070a4418117800d8008500c82c01e03094039019802c03446001134184c1d444542641c40c1410b00740c0f2140404580d0404424a9071a1200e035003050744968094200c200d591001c14a07410000800f030001d60303183c410ba03841107541c0f51403a400c00000d50003418540c0c3c40c00c4090703030b110075004060402a401c28000d40c0d200c980c040340641280401141c507041561540300c0c0b0007945844200c43c28044d07034841444400d45110030000040054902c20070003120344a00d0124800d80c0e84c1082c00c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 944817922 1250 944816672 944816711
    0x200a05150f0f040b010b070311030c060103021f200f07060f1205011d06120f15090105070c02040e01060b04381603030915060801060515182101 63
    0x400382c401d00d000d400c0000040740d10000c541500c4542c48016100c031036a140466030b03e4581352000b4103d0002042d411140d503400103889059a101304d4404001440f94600d800c10740c044507544000113503050400714000c6443d20400c410303805069040d5850080000300d41490001603034424400036101c01075211358583c0c054011920414406030030300c0294940303042d506050546640301c101e5400f900307004c0b0324583c0d98882c00e000005070080540b005455205040d9403035181050985500e40700c0d100010740300744818862144201f44d59120245448c0349502448020008103052240319940d50744081010244240034100900302c28103800904800303540c403034640c1d41c0c4801e41d10050080008444024101d250140d8600e640d00c031401e40b100004030700f405c0300640000b91010f0b002001d000020b14808810350055002d48025800030700500ba0380f84280894424136031103841d20050240404105142084100802c0c020001d00c0480380c0c0841c006003007060780f080340508040d81c0d9590b40e01122508032002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 944819172 1250 944817922 944817931
    0x5060f1008071b05060c0f04030b0703060905070807080f19060b0c1b011409031603030c0506010e130821130c0e010308030f070c06020d06060908070501200a05150f 72
    0xa44490424544e510390f6074903034001e400c0c00b211202c08503016641c07080e82c200f40c400071500720b806c0304000d081c022400b40c001c000601400c010300341000002541d242c05800314600500302680c803810b096580d290410b50311803010b814500c0450007140c0c54102c96040380500d0018101003114166900084864a468a80c150010740c15581400d209001c2a82e0401301e10401d00104a81c625603490070500040e0400b01c004100d035400b681d4a00e0003105040c3d2207108610b0042c86001150042c0c5d0b211080042c002c10304941544824503a451000c000a42e14006800000030400350310400c3d81e1074092500300c1c504200c8055180030003c69004045c04420340d0300e04018a1400c5080c0039650568039080004d100061207058103040100c00305510510480b40070510b550400780454440f05003040c1c0c0d070301600b100d215040004518610110b180000070a00e002116016140c0096002c6891621046030b04c10410610081c040e845011003c1441400700c0d00018031034180d1409249041c0380032000e0060043c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 944820422 1250 944819172 944819207
    0x11e060f27080618070e0a09080304030f030b0301110d02070c050d0f0317090a17120a0b041d0d080402150304030201140c19050f1605030904060e1905060f100807 71
    0x4d100381c0d60300801080c15010365400902030302a958699000902905070080010a1910000308000625500c00004449580306c0d030b03024040c1c81024403c06081c1d50b03007010551a0305000b000015807070000f0b40d0003040100c2c8102102c1e5181c0c2d075035800040d1414103140064410181c02c20104c420143e221034405401094070184817000c0c108650f80d070759030381c00842c40100300070b0b408052030000313180c05c000f5510300410b41304114900741707400c00c0390401030031071024954002c900b042003e0680001c400c02d181907044486008000040b5020011035021202030002ea8100360b075005d40030540c8945000a41c0708038040d800101e4140d05071642c280311848010103010400d1001d000c0140140200180d01c21885000c1c509070b500e608002d1544100c0c2d224820400c019406410180801c00c0008006400030343d070110740401c145555114030359001e8400b164101800441408040418100c650100b5000080a054012148040000316103170306c030088408800f0420728010800c0251348801c1d14080d084860 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 944821672 1250 944820422 944820451
    0x9010f090e0402090612030a120b0402070f0209060d0b0a090c05150306090901020c0d0e09010603020906070803090304090e0c04052503020c1002130905011e060f270806 74
    0x1010140c0141d018000a1240741070402042c016034035803d0000c0341c682500292562910114800f801c11101d090042c10f0f454100036a00405151034400c0c0c2e103d054101c1503114002c28641d00f001594080201019801500c030012240803c42070034210b44a003203814400500c1d0750b464180400d042e10103500580c03103a042441c4038035076402c00e8800e07603070021070550b948440e03a203e88102070701901962441520511842c5c140c80700c00c3e0360068800c10144000d0f20202e41c245d886942c1101030344202c0c1740c0c07c0c0e0451002c000302000900d0f01401980d1161101d01941d0619448503507003010f032028400c04101c0ad500c070318144100c83c5441d00c1150340000a03c00d0b07446007501d1050542a9840f550340080c07040c5980030494280004003030020f4040701e1640b0100b1541c0c0ca14601854111842c0f602409042610700303000410402c100070308180c80800400c4da1030030b0107854000125082da8614500e54100b1480d4441d86401c001c11001c0032408050301149809118101074040e45000402088224001e00c0b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 944822922 1250 944821672 944821679
    0xe0403050406110f010e030904060e010e040f03020c090414010b030a11010c1e30140a0c0b10061d091305070807060e100e0a05040c0e0d0809010f09 65
    0x200003114102d8a80f410414038208031100024140b01d1980c0d0022040c1d400c044040912580110050980344c004803801c02c40c82d500e961814001080034000c54000740d01030008100441c3c554000d503e00a0321070701c1103410103102c003804950035041c2520100d50882807100208402c0b58203000710b19000106400401c20001161625245144292601814810130b0900e41c8103100e0f04081c48030b020a09903440c824414290700d0081840f40c8070840e45e02119140a0304a020607a00900d1485200c0081e9918000002d003105450480c3d40000817081c24081404083e5002075081000320344908604d80c01d50b03030103c2c5441000350180d040d080c3c3c0120313a1240c40600131700c00e0f603810194030340140810000420032201d5242c01840c1540c107070401c02182c030420200145543d84549440a8404d041d00c003c0c0c03019014840c01e45120108603142d540c0f246880b4018041405e0a500007290700000b4034110b0025240e14001c1007616038000f01c240d03181b0500141415036941c10008240e860fa0240c504014070300c0c60f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 944824172 1250 944822922 944822927
    0xb060307023712081e04121b0606030201110304180f060506070c061d0d060510090c0507050118020d0807021302120708010608100e1b030408130e0403 66
    0xd2900506603541c202498099407520090358520003a80c0001502181d10307803d0500d450511491080200002d0003503002405680c0041d90102c0d5a40142400035003945582d41ca01c001591044011030401210390054031180c507000600008a9010342000200542580001000380e103035011149a1a0300400080003d400300180c2d8600c0508042c0b40000c7c1c0c40b4503c0c04c2140036001c6c56115503031040380480c042c024071100c0c500940480b061502d8110070714250b2054400341c040490710310b80c5c0c00303019520040003040441d04001c0d441101e070398000f992562120b80c400c048400e0f82c08424005000410301204111091180c0d400c103103000d070a805681005a0b002030206203000303a009010031070200e059401c42d02e84541c02403840364240401e54842d40140c2259003842d004030352400002d9038040000030818090080c07913000f030310b01e40310280302181400692404818060096040601d0f4030300f072100004441c002440c0681d01ca070450b2640da0208009140035074505070400708005030078206210020f80c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 944825422 1250 944824172 944824183
    0x15031605010e01030b0f0315011805070c02010c03090503031b06090c0f060a050f040b03041101030c02100903090f0f2c040201140d2d1802011803080a09090b06030702 73
    0x40d42440c0c081171098608000c01d1a500450300c025405205c1d0a0341812100051800c0c02c3c183e90a003904017034444503420401040d00c2c803e803204004118114280005035110b01900d07802c079070183c180450030310b40d5180407034550787c030a05560308807107103201c28078032440018462650007901c0400142036040c0500c000030065241c00038124851000041c000142c0c602035401e81d0300c0f81d000100e0040d129640d030f814241d10b076441100c08451011031561080300c99802481107465001c0c4a034000e10020460401000007000182016012301158010005841102d05290360107060b900340314152681c68000459200ca07442c84105885102c09060042540344050358568816024070300190a0030b405400c01e0454811400104609824000d40803080390240c6004c042028588048030040700d2509440021558400b03e942d00300411101000050f601c680e8056003914183c0d48002e040683d259140f881c20b0f4011f024980114085100400004115101e4004020b50583d051891403502404c02500c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 944826672 1250 944825422 944825447
    0x1804050c012a0c0f050d0b04110a17150f010e070807090302120706140c03090f3006011505031807080f0115091824051503160501 57
    0x11004400300d11466502a446110031160b0b003003034007204803403e0105039201039008508406810200c00500c074100303104c0009942d41c00c24142e00c0c032600c0325642e9502039100065a076500c90f11911011403000c4411f25002c2d442103c850040410340c0030f4464a0782c0e945401494034140c0003e420040100e510002e000c0da40c03040d280d04d00b10782140d40b240401d48500c1c504d82c00103074000ea15084103c01d109070000c0d6850642d42d1a8903541c2e400f9492001c0d00c44640b05058440c0041d0304107100740b072441e00f420810709100c402c000740310070106c40c100811024280c8845200a00620304601520040304060010901500da01da1001d0801c000780c0902411520014003400c1142c030350703050390810900e801d200c424040d042800944080c0c0b0700154850f4040d0001c2221103110302c00d921400509405c030352256080c9601c40001c036141198071a111115014000d01c80c2c050200e100c40e07003041d5004120b01c00c9600c910380c038201d8601c04c100340209041c5004031014000f006842c20f0042409185e03040355200c002c0303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 944827922 1250 944826672 944826677
    0x61d090a022b120507060b040506030a02041a09090a03080703020708041e031b060306140a0e15030a060501080c090402090c0913020a0e030f120403080714100b1804050c01 75
    0x14601e02c00040c0300e07400d079142c0d0150010510306910919282d20400801c1264003600050001c040e03010200421680702340ea816030301d9489681d00e031005040540003005901c06404035030070703101d50b18400f2401d000d000301c1e5410f403580c0085070030340d080680210742590440540d160841c1070441603540c90070380344290b00944290b00740e24140000043d00c0408600055503120a041c104075a107800d800d800c0010901509011905004001c900074900e00d02407504042c1c000c01e005003080c41d0995500d14008080e000c42c80d540080758044080d92020441415090712454000629614000c6860f04222000315942d1145400c0410b10001d40e90710201282c202041c03603244c1d41d49941c890000f80c0c2c18903010340400f044900100e0080311440d001545a41040429010707140d01d09544460b56440c4c103c0c03945240f5480105000038408504601d014041c41407090f03000d0364082903803008080c6440c0410040c1d54100c0e480e6100c04071142840341c80c50310b880303800d0b422200031814140d031025206d038007080d8150304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 944829172 1250 944827922 944827969
    0xf0e070308130e060105040515190503150d0b070e03121909060c050a0b06040f0e0f0c03031e1b0105090c1203041a030a02070c12020114090904030e0301020904061d090a02 75
    0x72251050700403181d05d1083c4903c0310342080c0f12b41201506c03070f410413039900c00b1240310080310040c1d90600300301c007994595001c07103010010750751000166820800340c80c0050b018401d100340034a00c6c0c1d6400340209001620910030816901038058002c0201c02c039500325404101962825000082001a5026034298003048181d040e569074408a4000c1001006001d1224144819200d1007034002c902e50f6040241502514881003850050543d46c1c410f03070380141210300c1048a11848812050060204450400e0112401000001c0c03400d003524020b6400c001c0d40e0304051844d4020f031030540252000c544601015600b030500c4c0030186540183c4681c01203000c820000000f80d8080d04d15411580d8244e07021010100c0a50cd4139031608a04c0c0b1010340490100340394001c51b0740c1d002c03400803e8070a051802403004c0e800d5034a90b80d0445015880302c240130341541d0244503416041c0e4a81c01040003405101c0c20002c51071a41c002403094200018118001303541214282d4409030b15007000240701c1d042003000044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 944830422 1250 944829172 944829199
    0x30c0c1101180f051f020a060506031608031309060612021602030106080a150204030f0f0201200309180c04051e0a060507060b220f0e070308130e0601050405 69
    0xb106140c20030101086954950004a4940e040c01c600005840040d10200c0c00441c0314100700154010080c104c0300507a01ca01d2403400095801d8201a074080320190644074a642564020b03c22003242d40c000300c007207400115415507121401c0d00703110018510810107004032803504202400d66508502c4480d00c040d0000381021401c0304200424440c50381c054000c1141607950b00c4e8075900ca00341a6011030b00000d1501141c1e00104060003a281502d401460364144a4055510b44e0b07100152071904078180032401501242d51240301d40c0c00f03461802102c1c0a1940d41014004120780f0355221b80390032074507070508c6051286040e40e000640d411389100b0754001d80c40d050614000d40992112080039a0700c1034060030080b90785507025000d000c0d0702d8800e410501c02e00e2511800c025642c0c20f0715030070341d101a03281c40b9003113801800d6030040c2a441ea0b508900144801c0c640e880c2034201103407a0025184410000344118900111010210040280440108032810000c0000300a40700b0352040d148141c0d407800121 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 944831672 1250 944830422 944830427
    0x150b0108160318050a08190e1c022701080d080420030a1205090405090102071a0613051e01150c11060f16051b010509100216060302030f07030c0c1101 66
    0x400d080c4c1103800c491001c1d44030301e411003e6074404400c5600c2071a00704011030070603004840c44c1c80c108000a000040e0301c440c1e4001c0c107041002055050ba80031450f90f1510410f10810060750a541141d647e400c1001d44c14a21014903141d400e06d9010104090881084046000c401000311482503850070020304000401c002450018558000780514200c441c0d102807194008009080c802008d43d0b05008646d6410b40440c200d004010016140d2909117080340110000109580d80c00000240007808034034600600760100e810442c2c3d8602c11026040704002800ca14075141401082d2240328090403960303943e4001c08210217000010602201c004400065a803003038240e4000600c11015183c4a00034668003c44525000c041500d16016108a0000c03640d43c07820f09111000041c1c607060700e07004190041c17102c04002088400214001c2c0c4a0340342100e0703484c0c01544d00411807583c001d605d1b403c1900e20b20410841c0501060181403408100c01d03d07044c0c00c880e00c81c1c40a070b04200400c081e042800d005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 944832922 1250 944831672 944831711
    0xa0209150a080714030705010c15090c0f0e1915030b060a1502030306120106060207180f0606080702010b030606220f1517070e0112050106030b04150b01081603 70
    0x50321540074021000c04c41c0c20424816460940c01241151400707650b4100644001c8500c51002e00090240c010120203070069411101c0c45510907110141303240d540d5003041100035a20381104440000318010b002c5a442d00aa08801300d0460301410071106000140d611640c0360b10b4800189802c544000080301c541d04c05114000a1441050340740c0203244624009440e6801260030a114200d081c014691f0350310705102c0c500c10341e84203400070004503040007014a0020000c0b64001c10058441d0411540480d980c01040014134007a25624614240f41c400a42034581100c0c529010382e000c9000c0000d169038900c40c0c2c14000307280b06404c134810409054140082c0c8581446480318178101040d0302c4c1c604000101807000c9882044020040c400d011140b5030300d451562240048554a03c401807082003c001440071a0510407800042c200d030341ca50300e003c4400c408032001e803007061022811410b44110740c00b422403242c50918010740b40e450700440a441c181c00001c0a48101a07540403950130440c2503801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 944834172 1250 944832922 944832929
    0x2070b09031e0c090f0702060a1104141c0f031b0b04060507020f01090c1701020306060a21110d23180a0b09010f0e06070905010320070b0f090a0209150a 67
    0xb25820710b241030070200c69684006d40d12080140f15200028800d0a014820782d12101400c0e00801c0c5811f00d000310144108008007000c1d0b9000c400040c0c25142c04540740111a6100d1040480148164040c00d001d4110b144079880302c07244500c01c0c10040700288881e640140e006900003400141341c5c4890700203d14008222a8200e015864005408280005000a0002c03142407072012514168015200c500340e0109481c03264200106010104405020f40c0c0d00341c990340f0307401340f5600090303030b20881d40b4094421020901600b041d0018010070062181c0c01980c0f0546580c0000d5070485040241103640702d04020700880090300768580303c4880d2581480003c3c0b01580001000c09103081c2900241e0007806405c0040c3c1c1503520b4210303000a1540c01040003441626540c4401003a00d00c0c20340150702403c4488184040c0c000b01300511051810800050040c4a001c3c88902009160100d00c1c05644013015100e10311550185201c080180d4a000030103a0000f51112600320003803540c004102c1064080d00f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 944835422 1250 944834172 944834179
    0xc0601151403100e07020a030e1507151b1b02010c06060b0a05030a06090504030203030a110f0705031305040b130b040e1e061f031e0203100c02070b09031e0c 69
    0x1040c405420303424250001600c1840b130b1021000d0703c03402401c0e80c2d01c5030062002000b003482c1506504241c80c1000c3c0481126941d09030051401c401035803014072003507020210283c0d00b9500c81000b8590700b624145a20046003504000e003181906115403862504401c500a042000ca560030408018442e00a07500030300c41202d000d91076241c40000900240c00031290b001c003403890550001001020f50040030301454054003d145180c035180c804101410001080e0103c80d50204a045811a5004024240c05000340c000c6c6489040c0c0c20607030340c4004019070205114904004400030706599004806103004c0b00030303000103460000d01021802400e0a0310706a059801101c00044450310220601e41050b480071065500503940c02d40104440f00783c0b1303905a14041c0b191f450510004250302180000b020b0702d449371440060403940064503100250700c01c90305403030701e501150180316010800440035094000c80642010a5030002c20b6860808201c401001e0319410300c16000c40c40d0034030414800342d01c040e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 944836672 1250 944835422 944835427
    0x17010c2a06020d0605090c040b07351207110c040b03010608060a1b0f17090f06010b13080303150603190906020712030203060d0b0613090c1401050c06011514 69
    0x40120400030070003449014002c0c1c031b4001c00104003480250440301038500d1040d009061440684582e50311104e60007000010304001884084070400070001e021181c3d5001041d01c3d40c403039007126042000d0380080c0000d001e122480810418205000c500c1a14168013a00c00049400c10000083d0250003540e100078841d000e04014800c1c915040e8120140b2980c0164842e000c0500740d1504070b85e1981c070b89480c100080c2001c00042c400080d20801140c10000c0300c0b044032078600c0040d1030107050001c281c1c0010b01c01c10380001c040714503030b2014001c2002040890040c0d8198500b64801c0c2044162800340648643c00000005071601d4414910105501505000b0000403509140000003076005d120241c0d1103180c0207400000c110b01c80e000b101e03c02e69001c1d010010081503a6a40d6040030720140c204c1c0e602c00982100388010b60302512071581070900a0700d05602041c80e0201a46000c00d00205242c1040790400800702011780003c1c61504480000504030f406043da07400481d9034038034109010754001c400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 944837922 1250 944836672 944836687
    0x6080a060e0108061008030f12060f1309020108070309111915030f1a1c050321011406030402012c1c020411030114010c0503070203010608060117010c2a0602 69
    0x8000f486608444a0040e5241d182e001b503942d2401030780c507000c07002d5008215060030701c224803a82540110000e400c0740c01c0d2a0b001e1000822100884070011080381d80d40c0050419582d200905070780203038043c1810800302a040e100d10303e0950a41801e0350041e048440042038444005c803001c00109800c401164030800001d4000740580070500c0420701d254101f1003c008124a40d20060103d044001d00d070755143c4070b529110421000c4450026a6580420f20020b48801c1240d500e03a00c5404035000e0680e01e645c1000c2c5880c4503d200d00b0030344d1380220018000c1100503608461822030101d420440011024400d40c005103a130b000350f00b829504412000401c000c0c0f0803482e00d0050500e44200c0e8180316200c450006e08903140000d120f0300064042100b00100075500410080840c030340604146c0e49440d003181c01213429202540d2100059501001c0100001c94410070b0300340c18188020000d11442e0f40000e17005244541d07008221032440350040a0700c2e4846565010a0310050b0b12440641d1a602c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 944839172 1250 944837922 944837939
    0xc02150417062e051002070504240902070201170916090507030e0105040c0b0a032c0d020f0a060b060904050c0d1802061617070818031606080a060e01 66
    0x1c0c2aa28a1980c034524905020f14141241c000e02180c03030352281140749540343c802040034410803a412001035000d0010007085685441c00340d02440001104035034401c00d6000c0f945081a03510b684210720030b501c14402d0743c0050381c0c000304d1000c20b01a01c40c0038000945502040c9401c207504081d800400c0da4034000001008407407174004511502440c0c8040040103040300e00c0e40e083e01e4040300e000341600504401070104d250306d200500210b411506d400954090800d02841a02074442414420682040c01c444544401000708000707030007451016001540030f0484d003958555900400900f881d4841c05019a00d8441e10160b5001480041c010312a5050602d090010395020f195004c480c039040a84008090740c61103d0045800d50250650b803400050490301c1e044e04406810845884900009600303070111000040c1a03100d000e6001d19564058140014111100151099010b40c20101182010500041464040710032504181c0303000c1da14148014000d10054008081050900001064590 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 944840422 1250 944839172 944839183
    0x40f2d060c061a10050c0709020c0c09160806040b0112020a0804030e010c170a0201020f120603010b040e031219151d090601150306030b01031104050a06060c02150417 73
    0x74080c035001c014082800340d03240e140030b0307100309001d40002d160124403904d188908000c041422422082d24100c03a00c4076100f6083e40e020070580d01566100c490164860f2401d43c1d45a500705103614013a0841240710300015143c46c00081015200707640c1c0380318070040c0340d020705070a045030515214119a181c02c140d0018101600c10745040d0009105896015420750040550300022900301003200002c0d842c610305031106a10422400c0e00719502131003000010912a000f80402030000310b8001001d1804c2c0040c503086440d0031051522a900308031024a0300c3d440401100d036880407a01003810036699210b11011070640501c01c001601d03240200c4801ca2291490403c015141141564400d00403590280340c60304238103680310500ea402550042080c09111003000d074101c5550b080c00f05090b40d90ba2641302c000c100907070040d6981d40147c7c0100703210f850f01d4410300b940000c01c1c04c02003010a0400100404052235094028056075038125003000c003600300c3c0c0c107172001820181700c140383c1c07480c2d868010780c0c440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 944841672 1250 944840422 944840447
    0x200403031707050c03071401240317030c0a030b010c020603151305220c180203010503190507140d0204020316110105040209040b130c08030c12040f2d06 67
    0x300e8030400b15100380c0c8100120380c85000700400071420708a85031101141118000e19a4407159600d000c403020580101c10038046800080c600c582c5020315604020001d440d03003001b0019400803c00c1000701c03401c80a42581d48800b00e502c0e001901c403114100685102155640180d400207001c4104914950030034441070003403c1c01c0d5010100750a000d44c100043d00c4c0252a2400300c0249040c0500185d0850038000b10300d58080c80c018207020380c0d200007108040c0c0403ca00c8030003542c1c000005002c0c40c1803c0001102c01210400c040124000d591145911003901e402581070300031280d1a41d80d4039544071588040359070740080c41117582c0d06181a04190591101411501084410110400251041c86128404d0f500500081e03c0ca035100e80c0c4181031000024075019a40c10660b03100c002241750300754414050030103d0011660349a003003020900d07144560700c100c02a05030802090100074540304030101201c580055040748159800c42020280088940251040240080014141754443d0120300030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 944842922 1250 944841672 944841707
    0x1030b07050c1f0f0606020102130312051b010f0b0612280608030304050d0507050a030c0f0b0a0605190609140a0503030d05071407021e010e040903050c070e0f010920040303 76
    0x161076071b5a800b40d00340d0107240c010382583c1f08204030400c0071440b241006400100c20f40b80c1300340307010794040005842c1741c0c04944100860390b5409031840442d60b05c2c403501c82c0d040c0741150070310f092540140c8442d1a0340001004070034001079a900c92070181450358601400e00000394003d00c600740c1c54449007aa20703002110305031b9483c0b245030a043c04083c060021114455003000c0039120071541030b00d00761000d07007880300100e80c220600380d45000407030b00d1070702d2050043c18410310100f0514900b200700840030840380c0340c000c051203002d101004107540100b0400201d8180603656512403800c80002035040030203501154050100240800c007015266008911580c0030351980210566861101f1003c0d000b1184020342103464041550405241c4200d0503041540514110711603410003004502030b00c54865080307020070004a00b03aa805103040c0240740c042d026001c0c400c80c0b80d103001d0100c1d4900030010b2007070507001d03903880854001001d101c500c608019801d03101260b13a03030f40d038030302d401020420320b400712400c0e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 944844172 1250 944842922 944842931
    0x32102010605121b2d01200a062007030806131b030c140f0d0e010e0a021809070614071a090c040e07091509060803091801030b07050c1f0f 61
    0x1075034039107000c0c46441707681610058602070b200c3c1044c080b0b00d14440313010325052000d00540d441080c1d0f1541e010401c500d203d580601041e0469191502c20b440b42007000304600411592961942c0128030240d42e2019014600407425031148404944c1d00f0003244107100ca1681800d080d15641d401a94030081f0311100355800708081400f65400701c440c0d40f40782489140303202c410003140c075008092401400c03d0328070210002403402000b1414071308440e009401055a5089030010b0000e5207003e582140e04002950340741412480d0106d10390380c441840d801410244042d959240e001c054541054413100c552140c034928107100589180c0c6140301c0125404280c40c420070307041c064181083e0041c0c030381d6150088000c10580b424080000041c00c0c004401240400d049000041da03c0d80e00d004110040c44070342c0c0074542c1c1e000d00f0024403140900b28141c00d07180000b00001000000d054140c00c0794405000c1c5041a21016a02d0351a07042c0180400c0c1c0181075132001d0591020048560b03c5481d20b012804030410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 944845422 1250 944844172 944844223
    0x703330f0b0306070e0a06030b0301020903010e0d0f031103010b0f121509060d111e090a0203180703050a02041104090e0f0f07080c10030e03030f01031b03210201060512 74
    0x7100c544007501091b80000b05060b003004141d010360003030400742500400150412115001080c00c603044038400d85040d17400300d4200d0041c26004903208030030110304d00c1d00f4065121407810040c5913100610039840c1000b00020189100000344040d21090010f00b034070700d10a81011000b1460024204401e20f02c00e9000c200890000d142244803c10365503401070340354078255010801c1210030a00b000c00034a40c03000281145542c0d5540146080c81501d2481c8016220f04150520303203240305c80345c0b0071800d455021240901c04680700240781c440c044e41c101d130b01054001403400f5a03100e078011507000c1520282040d4032140400404116000d940007844103c0340003600c802145942ca0b202c62084060a8003c001440d01034200b80188601102c0f0600b00414134046040340c5501d154402c440541e03984003150018000c0010000c010000b11003c030042c00780c0c050554a0340340c00410b00c8400c00011001000d101e01d0194001e4004500501005000240c41e4050010b065100d0044d20f01d00a44054048c0b542c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 944846672 1250 944845422 944845427
    0x90709110306010c200a0602010e0c0d0305040b0a030207080a02010b03011a1005030c04030b100f08010606050d0b210c010e03070303091e09061203020c030703330f0b030607 76
    0x7203100d444140c1d50300901801d03a448110350b00c210440c00c05c1501d1191145490300382c4a1409020090030241d0000503103c4004008d030303080007980c00b0f515215110441c44070f0b003c0380e4004d05907016901d505600c40d64808801400364001d22070340d0002424410041540a01c10f6010740c401c00c02c14200340c0007400400e102098a680f048550640320340e2250004101d00c4546109038050340e13000300750140380c51800340c49450306601d40108a0b1030305826065403005000c180d160300030100050080700002d001042c14880007401e140220300071590745e6980ca495081250fa50004030a08040000981000e811900b00f401501c0359070040d59103011420b903406041c02801c0c00145c200459402d9500c603d0b42a00341020403280e104000480c6045016810b404981c20b0018071231032000306600901c00e040516103140203818100b602e1b1040c2c1c4290005601000456010010f07a40d03001c02c1203507009032140613030000e5444c2303035404078510324024075200b5a103103101c8503680310b5503a0510403400c0b1070b8141d50302c0b1401c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 944847922 1250 944846672 944846677
    0x1f0f030516030c0603020723060601200304090c120f0501050f0906030307080708070b011e090c020c150c03040e010e1303020a0f06090503030421030213120309050909070911 76
    0xa10f00003698408011032446640074140c100d1052070064000020b030111b03850180442a04c4091640220082c004136613003100d01150412140c5400300002c1c17a100e034072180c89000381d109070784000751030b400c0ca00304003446800c6140101c0c5480c2c0040200f00c140d101c03000010b001c2401203a000700c80031400301ea8103180001c80c2c00d1141a008000b0b51038515143d440107020f030080342046441c804c0070310590000500c44003201d0f018200d845c24a4a40c0310b40050701d240241c01c50f900882c4413501c1c100b00040119404503e8102c01002510b1014101c140340280c400c0502c40c100000701d05001c08113001c201f141d094100e0718102c6000d140043d5540d11101042440c03d083e10320300a000d60310440390340f03000504101100003901c0c01600005a45200fa440302c7e0300f990f01c1103d0450381e1401c6401c49820110a1f00d030803e42c6201185421401c203081055401031900c1207004c0e0b0000c2c510030344146810984030f084000007512010785603c0c400d0820108290b62100d15000b1a50458208140700c1403500c1d09005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 944849172 1250 944847922 944847929
    0x5010b070807020d14120703020105060108011d090f1204050a15020d080901060b030405061614040302010804170a17070206040f060e0705041a03061501090308031f0f030516 76
    0x10980340c8602c9500308880000c2150341200d10403000711401c4181d11060003001d11400454205c2139035007040785002400c58034010200c60600840e0001800000100350003100501342407034901d4643d450700303ca5a40340001c4e0504640d941d00c5901c010310120030960025008940b000e58011f40240e45484820300f850341c0e42140d00005a2003100c0b903a5000780306d04141034001c4060300c000211241c58038a4a0480c0d441200d0545041d40302d401805896091300f040360840411a2614004442c404914685584511710019041000300004a810f10152019003010050309044940e41d41c40e00c401c019240440b814003441c8184080800a100c0c0703400807804500c511b901c034610741d100000d66a9010700800b901f00c4001c18a00c0380410204080d02c3da07105a01c0e481406100d0b07004007814500805140c19130043c4004071541341502c03515a1640c00400c0c841c1500d034400b84590b140ea440c000800c11060b20800d2141001101010015120051880403001c2c2c0740107030161403001444101c450f10b642004d10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 944850422 1250 944849172 944849183
    0x216090e2b0503040309080109030f26061201060512060609100e062b08091306050906101b0b10170a060e160f06091d01090911041b0305010b07 63
    0x41079800082d109500440d40706100e81402900a0b440b111403908443c0020005c0380490f032080c4103910401c0d001019440c0075136a0351250300340c90b4002c5450020744c020107800107015a2000704615007031b12082d004140a480090120064400b901040701e80d00c03042075a040e802107070ba180204040c006124003d03004c2da00c6049d0440b050351290402d20100d002607451006000ca80c01004501c01594104155034890150546a4031201c0b000104041c41000d86001d00d0705a01d000070030005525030350359241d484001110b000a101c07100040959159841d80e05184005030111900000c0102e0b55404034050001c0d018014405a2900070030300701000d40c0d04207008a84e0012103070f13000062090300000080d24441d400d87e10100900b10340340c00c0c02e41c2c5a0700040d0400c8c8940c0818401c41d540503003950010b041c84520b411200201c1404d400c0e4000e030600518a400e82c03180704130780901130182842103140030058810450b02c006a10041d0030100402d802c1b40010741040000a640308101e020380b0310460300708 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 944851672 1250 944850422 944850493
    0x70c14011b0807031e090503071e03060509031b03070c1d040605071101110d0b0306010302011b0203150c09150a050d150306060b0406020601051801050d030216090e 72
    0x20b8441c58142d401405080702084402800c0079040c4480e00b8401c100b140c0b09032104002503080c14201403c1400d1900001107440c02000500980c01d61850040120b85d0010000101600c41030002c0c0e082d440b48420041e0780600c4038500d20540c1c0c034008010001c079405070346000074050f1608070081001d001c0447d040e1807001201b000c240401d21503400789400040038101441c0000101f080c250940d80c5415941074040c20200d01c520703041410f07001e42d202050044000d81039560540d4000780c50b003400c100c0c410109003600e008102c11900d040101c070007102a00d00042000d071410108407819584030f412018068200e01240c004c941032034500742c608096458858509000860b02110f008108200040089038a0a0300000c003042240c03007a90084c04503000c4a90341d542c00c008002e403510301c0c103a10081c043e500c601600012800388540090642d201110a82403107803090034120b14003d441548204564690303000022001801e40c0164441c1c5601030a84810a140c0109548200303c81c821001139404203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 944852922 1250 944851672 944851727
    0x60415090b0d02030f16080106121b0302060d02091915050a0311030a1407022e24050102010f0e0c040b032e0615020c1e06070c1401 58
    0x11500400e5900034080e00400210790180c000915005c0420b208014a4100380d00c030800350b1a003032102c2e8010309140c00080c081d01e880e0213036008a140e0f01d05da0240c82c103280c91001110340350030020130100944d00202200d4641107416103c500943c403c40010303226145c540300c20400a80c07003010b0007040301c020043c2d130000301d018003100340d40c41c1e030180f1118000c250782c0b10266803400707070740801550044ac0c080c0c0e0006110340c3c0d00300d000e02c1504000340602081d9440480741c40324400b40c5401d4665001d031628142112240c0c110031220152030b401100d0610700891184205141c803080d0107480440364264003e01a010068024200301c0c0d880311440030090700700c0305002d055030070140c122049504d0080c040781e0080a82a200103920120784180c05d0100c081420320741304c0c2c174030980a640040c1145c80c3d482d00b0081d00581c0043d50301e13001048154082d03003002039070b480c076841707503800b40303c0200c2000c0d03c0d4558805192801280c6482d1501503058680188004074400d54841c58102514040d824000c050303a110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 944854172 1250 944852922 944852939
    0x60f03090309091e110909010611120a050910030c0305010f3002030303041b060813150b03070807091503080409050c070821010905090c041107140a0308060415 70
    0x226000140103084c0c1014003040d030300741903114080341c40480030b14460b11030071135000f0401c4200041c0d1052041000050601012800c0170400c50003d0740b10620480c3d69071403840041c1c03124042c0440865100041444080c880c58150b04140b9802000b0b503410446070f80c0301c440000d68844103010f17090310001d900c0d04d900700315803e8440d0102d003415014040130400581350700007032071035100b29400c80fa01c1c0c0340d440a072100841c1d40900307000540b0030390418100c18600040f10075100e00364410080c0511520000e004201c0d10700d41d1000c10012805000e9035a01034813040300542d80c5020b4840d1002d1545080442d41381000459030410036030354849050f0746018034100e1610040c0a01404007030521030704000c01da00050000000b0311001584c08403220400c61800c13446000325805a2041092504150410081c03880104083c44901012200052107034100c2010004c14001c518000745061010714002c4840c80780010100d207842e210f80e0f1001d42595a040501042d00c0c0721209c22a00244c10f000144030740d06 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 944855422 1250 944854172 944854181
    0x20c060d020d051e0c0a080c0a0e060f0a090803030412080910060f0501110d0813050304180e1603020303030a111908011802090a06140708040f060f0309030909 70
    0x3040c0800981052801c0c0c0021040f6007059464815030040d070a10902103860950101313500668141c10b0504141086501034400480103050120300030300000d00040e814020114059a08400707440135440f5140740c0308031a42ea81c00a489040850300d4054002014800081200d01c200d90104003e414070002c1c0b4000d90345640094409207090142070384081081189100b044000c1c50400c3e16601420f1800c0001742882030b05415100b01034103d0441c100c88980c00820081e080540b030002c803071403107205041c124114051600319440c40c2030201e02100c143c900ca600060680c41450003510b903611072000f1507244845e103601c0020741640090000800000304ca5010802e480b9000d0f101d43c0c94880e54140c11801d03024442c12031000b0800f00001030050b100400c000c20300e6012842d1045151220110008860400603c10b410030070401481030248140c5c95000d41d00c005070f20261083d151910b80c02d01e45007510303035401004000703061b200b1000700440c480d0082c2c00200d50151180618542000c80d4040600b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 944856672 1250 944855422 944855437
    0x1141009090f0218031605060a0903060e16080a030f140f071a060105090d261b0c090c030a0b03030c030a09030606080d14090102070909030c051c020c06 67
    0x99030034030006444481d4000d0100d0250007410060796408111320680f000360342c01103801c0c0070b507000507075a0fa00a8030b0458900d059400440303090f81c449280c2c800c00c80e070380c20031600020005070a103c0e1000140800080140c1c00211441e1820320b981d8807000c1082d03541d0728180001c1d0010b04003143c1c481c2c4141c082c1441a039448131584510385800502258020554840101101c0d407141c4070041c40c0050107114034041c0c101c0024a481d519000c2504000303040032999003405440086541481588000c2048844010314a90542e890311804044030700340030a81030300d807003141c0703030040401040d41c900d4001071701403090400300c440078195280c602e000801003007100c000982512003000071005908040004c4d105c9282580d42c0e4806180c01c0d458807400f03550741c9030700c18401540300754003108419800c198036414070701050105c192940007a0300102d02d080b100e9441814254a00610242890f0b0311a42c00003600340180c04440c6c40320074507504684071680f44c1c0051001600044064409403a00d0300040604 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 944857922 1250 944856672 944856677
    0x903060c092403090c010201060f0e0a0906050c0c1002070201080a051008100b0109090b030a0b072a03080f072a05250f0503190f14030a020c030105011410 68
    0x20b04400038590388155400308484481c03000c01104100c0c0d42c1c64100200404220284000d00807585000203d4100b01694004c10070403500d4100082d0450166601012120360400307801d004a0400c4070b400760f041d5208112401d014001c46140c000001c0b443e0085840c1590b040c1c1d82d42e0406c3e903406410b070000b007801501c0c50240503000d04000510040400400c00c80c0ca900d42400a12000c01070000b4042001641c80b9090071400c00c1480d5090f65804505151445d8100f043c60103640e591980c1121081c0d0b0791181310000c0303800a21606036401e1200d0714400300600c00d450f00d01d00c1d9101c0350343d1400d404a044400c0c3c000a440c1410f0600c083c5010000b0142035a0210010040700d0f030680d550345d08104002c0303102282c0f100d002c201851030005103010032004003c00700c8221101814900820344915514860b40c107404601000482081001030000d001c05800035a13400507010355600c00782d02c1364800341814005214094100300700b40703410701c9030034102d45221601001e80300c00c48050120500c0500319010a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 944859172 1250 944857922 944857939
    0x90406020702041a0103060e04120302091c080a030b011806030c0513090c020c06041505090a0b070515160207050d1a0705030702010f0b0607030c0204061e03060c050903060c09 77
    0x140c94a0090303000c021613190181d0807008440b0001012600542e00c16620b0f010103c003807001060181c00c0380768800d0030741c1c036001d640c0c0c1440074042001d08042c07a10104d41c0b0001d80c090304042c01010702c042c00d6012403643d81400164001c10046640e803010324141c0a40503100b00f801c00c0b330140a80d20407907094005041882c1032642c403030b08049180d00c1c598404d0701a5a190342c80035060b580d040c4080c0c1002107084a503e0304043c00d1100710f03914200040c600c103080c0000069440c80355034800403210024032040007420b644a00740d1402036110a440136001c411440040d020800541201101819259150307005003182c620300401c00040c200e0100f81035900c40e8000410501518008000510408554580a54a0508501c02400c407000103113001030030b5203411075200840d5a00d03401c941900d82c152826441c00c0c6000d00026000301aa54003036190303007104034103584601c001405001c6c1141c0c080d00c0100b01415151070251041d100d90058164141c111000140c07215844101503d01750001070308150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 944860422 1250 944859172 944859187
    0x80c120a0b06040b03040c060203070f2603041a0a0204050d2a0b0301060806010f090303111c02070302120c060702011101060803070809030c011e0302070302160611100c05030609040602 81
    0x10b800c0c0e03120350003041041d00c0000420007480b000c05100001800140700840c50202180c442800460410200407c088169001c0100024840039070070116080503070032581c0d13400c1c503103010660b141c04c0301c80180c10502c140700003c0000d000fa20070744d001c4600160028070444001d690f0700800f100c1d9040e03005c0c052120041255003039292200c940002d05454121a641c03035042002c01313000d101008040c2410010158041a00594014211012240e06080c8000b11a09200782c0c4d40c10910704400288629a85400c64450079a001503800200d0313000b9514401c4008184d4541904c0300344107400503400450400002c030055110310840c00c2807040c00000050300c181c41d582c0481c2036500092040d64490404101d4500929090110010410f03090030220403110790310200c441e00c0202d1540c00e00c1410390228004060500a200c4840c80d403503048480b591050719901b019110f44410300a41500344150104518140700920524070303078510a884450035a41d03078004000750600001e000300c0d100c81c0c00f4001d84 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 944861672 1250 944860422 944860429
    0x1815030313140307121a0903070f050706090603050c04060c030c0c060903060b04020909010306050901090b10080f0f19020406090216110a0e060d030905150316080c120a0b 75
    0x100098a00c2d00e10b80e8550800040c10949002441c1e0018154130a0b02d441c1c03100042c0f80503803c2081642e8000b040051303580d40b0301c042c50860284210107040c803154082240204000852224284e500946514021541301c81044045803400c035858004804100410b11042d4000e004141d41070f131080c0740080e00780d291a5603041c0c0505e0036501880100d510401d060040000314007490b4880e0b50103039421424030000b04006a8101018800602465030301d03004102202d2080d0040070b0442d42005100340b0300d0400421000c900203661044a1030303400707000c0311004800e0000c00c1c064000c402c0134008160041c071100c481c0c0945492064200d0f84556038180c00038400a048c00900b104d202ea031488060805040c0c104912130ba407262503038a03c9000070032070500c901312071108450f8022000740c4e51520040c003207103000c0c0c580e2803c6070000359010103c15030341c8100200e114015440b60120982c10b400355584146c09882c40801541d1000e9090303010b02510004032800d1500742e601c820030b0700012a5a88002021 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 944862922 1250 944861672 944861707
    0x30b0405030f070b01050f0f0102060703271109060f030d11210d0b0108060d061a03120a030e0106031104050405010f0f02040609050a03170c070806160e18150303 71
    0x100d504c2c4400000411a0f464a103403612040c13101907841e120901c04110000b901c940327004200c9824181c0d904144103400305030742815a01d80c070800d002074140038064200100c00000c9004010300c21030b40c00c000a0221304084010104241014009200500740c01d0780695100200001ea0800e40c45102402c500032140e80c1c03000d1451180c00341a241c0d84403520000d01050724000310b4810b050101c40c405210041d140d01c0c1c12070000c9500711000041440304015107484080d0015903041d0b01d0701c12105c06c024146c1c040b0004000c90304554804000105440341e076a82030700d0f0a03100151484c03850800d040f075241060b0700210742c803d01c10400000c0200b0451100c0003101c024110100180d41e01082c00c2c004503030864090401703007400701c0300c1217038003407860392a0050305101c5c61520651440210300d42124841c10030221010300032150940e4503a140900c070302e00324441008401000281c005a0f45c01d40350900c1d840450300c5858001501c0425505c0407124500c1e680e1600f00c5941501c82041540301c25081c5000c1e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 944864172 1250 944862922 944862937
    0x207050c0a1a2226150c0f0d23090a050303041416150311040b0403030c05100f020d06210b0714120109060b03150d020a05041d0124030b0405030f 64
    0x1006000300c84c09a95840341d11403c003498080c282d12a1000c668540100000c0340e030722100c2842c000c1c1d076841c8480c600503140c0c00380c5801180150f041c0502260105101c00a00d064000381001c58000d039903480101fa45d4aa146103c0909190402c201040220b000b444c50404203102400407102e08520340300d0b01c0012072402d139001d080842203414460383c082c0d9242c010038000404a4405605050030f21800804ca031040340b0006052042e24540f1404015081c040042c1c00d0910003410002c0c0e19a1b04c40c0310740a5806a2600d01585250400100b02c02c10846000111808168502d4503d11515039444000100107803400c0c050001040c41c0b05c1d403540c01180140701424039040110900c0d4036161100c0d0039070710542c11a400c909424001c1000110316486110b000c05c3c0210390b51032400c881c0e4004038094003803603045107070401e044c040440ba04901a04140b00b5903038101008010168030140d07024040140c10b8004025403048038400c00114245d102055082400740c81038034a0229015201e0800da44102c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 944865422 1250 944864172 944864189
    0x10810050306101404020c073302070302040b011719021b010b090108011b0c080d02031305070f051e03151e1f33030207050c0a1a22 58
    0x10f20501c50020030000940b207655003135406500348000c0401c11a00d0b90500e005d0745800d0402103d07215139a044081319906e0003e20741e07455403e6a030320010004c2d2590801d00040e0700550a05010340c00715403107100d042e088501d510307100d00585d4580c1303880d1400700740741d034210204055000d0011000c4000c9440a900048155000010f4144902000d01c6a070a50590000c04c1c1c0364504005a00711140d00c02079104503003018a80a004370f02d0504c1c280a06004040240c900a84084200450340e4001c10020b05100d000e041216032066440c3c00943c808038881c00b540341c005286490207802214a189916806503004080d250050302c840703904070030035504031070008036440399150400c4442e0620007400d800402d0441e0302d0317814174600c001001240d04a403050091803030382500d941220300342020803c0d03000d4802340c90350100c01c03044590080103504140d6040d2181d002d0081d1540c501c1c5006103001c001c96600ca0f2603150f02c441c013031340a504a0b400030342412441c1c8100c0d440020203900742d0095000580b2014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 944866672 1250 944865422 944865451
    0x1150207050405100317040e0412050c150103020909010b0a1802090306151002030f0708031512030d2901080403020a060f05071e0801031e05010908030f0c0f09010810050306 76
    0x1420240450200241b07111910365081000380403034954039121550091b040060940c00c02d201500880345d510902000035070a01408490b80d401031001d0150700c0c12240212601d49a54645060060880d4005110541e201c944480104101c00407680b0744400c00c07200010050800c00c0d0b000209050080c101c5190300d90503000140c00409103080d02c1000000c0c1003a100130340c00c2190102201d02d1030301c29020b026142407000310010304084044081020300780d101074a400d0685004141c1c040d81d0740c0091102c80c256908141e15114105140160100c43c0c6142020604400184c10019a05100084d1040d02180aa05403003008a003c0e40141c4d1130096042da40003995103000d190060000600c050400c6406850103007c2c4135459000018505403a08050b220700f4120700000c3c145c0018a540400625950910100c0c1062051200c00385100d100303001407074850350b80c0c2c80000d00c515101d0040548480e00b0288609001544942601c6601042100150540316220000289840800c59100c241600b10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 944867922 1250 944866672 944866679
    0x618020d06060206040c21050a0f03030e0d020c060a20070f120809100302210103120c02060d0c03111b010c0e030c01140d05130b0c03010b030115020705040510 70
    0x51007400300070007091001d01650b0420307990b80080d180d501e00c188031661641071408100704158107200d40049034010200e82c00022030346012032003031694442c15000300349041040e40d000040401c2d40848001c03d075010f00442c215100c108101d40d044151180104191401c4e0118600903c01615110311071820080c0005031800301d100301d40301c40036009100e1000c0500c00607400118400c1c152050044211041c0050f002c006204034001e020b6000b80790b102c1040300010387e0f8880340546410707058034081c50081d124000f030340d0350540701540c107044001c0d0421010403446914002030f0340b040703224103c603240101e43d11078a0081042c0c99044042109154049201004800d00d800d1040016075034580c10040d4585460700300094545488401660500c811014416000104401181c2c40d920502e0010401800c1c1140c0768076a008540754112940105a0081092545500182c074100d540756003d580c0f0703603030a06004004144103001c0420a600c11042c021a8903030f100c0c050503114800980c01059050315 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 944869172 1250 944867922 944867947
    0x804050a021c1b120f1a01120b18120c0705190e0a0b01021011040b04090606110111030103110d02100e040b0409021018080d0f081501080613061802 65
    0x700b00342c80458098021904120b15202d020b2010303480e1740c0000a40503280d0700d500704036200d04080031403000600d60690011807100d5802d01e240f904540500b40504181e075032011541c03d03034010280c41c0700c1c4070350200a038141c01c08070070302c0101066010041a25034003980c0e240403a0070291041451182d1b05000d0206000c0e03100061802540641012420300000710340d0700010303481d443c1441030138803100c2c1c4441c0c1002d00c14101e0b6049070001d2052008056480382c0d114030720f07030003080c0324001c140001e98043c050700c400070014001d24080350480c5440e98656440d542d00c900d88445104c2c48542c21500450003103000d603507140d1007240060201e4403449113102a48040204951001c02c801d489240b0384107062025894400c030100c040d9a2509101e1810b66100c2d940b441a902250701c9803203144a800c1208000c2075001c405005891103c1d100c0142c66100d4140d0480c0f0140f83c025601d0003d4010b000046851401a10203000c01604520010b0b80d1511942800c60102c2c0c01c2190040068000580301d45041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 944870422 1250 944869172 944869193
    0x1a0c0d0f0f03090b0403081b040f060207064103040c050306070224130c12020f0901140f010e0a1202090115020d052a010906060e06100804050a021c 65
    0x2403482c04001100302d50f9549000c1240c081c0025042007014000181c50080550645602d11520618107490b542c0d105400e0000d01030a005080040c01000f00000c2d00c0d40c000c12a1020800080a0400d00c6510148048000c07868403101c81400f00c1450a40314605642a00114004c0303000308840d248050510050500c0c183c1c000d401401150b0010542006861050b460f0b0392020fa040d012050181d1102000321640325440d005c040c041c03038810b100000b214850802c00700005807090325001d00102d0380400b00f142a080901c282800101020102784039850240780c540f2030000c0506207e45e40940520100700c52000c917400c40b8486981401100c0c09620b002403006004015440d94a40103000076800252590345858205050110200b0300c3d8403070b4001d07030b040b080700e03445a0305020079640075080e030040c040d010000302079031440e19000c00400c00d0026060b031700307100d00c42c0074007240764403840f5910882d0860001442920907000d012090070060740d41012001485041880180e001011410700c4140038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 944871672 1250 944870422 944870447
    0xe06090a0321050a0225030812070206060109300c08030406090e0402280306090b180c150703030e100506090f0f1503030d0e030d060803090306011a0c0d0f 68
    0x403d0078000c1e80c00040e40020507081d00420f407041c108408440c159001c80010b504d400042802c00c0203d4004950b4005090051140b60300340e086a181c3d850307030b00054504079421300440b0825003840c1070356001e0030352500301c000c00048178410f5401c081c00d40d600c442036100440d800402c1c040c4c000140800110798020003490150a6803035103000181000c2c0e00050040c00c8840039a100c030508101d901002003141c0031842c005582000c1e003442504070900e48880410011244409040080001c40c4131071040010f80750180c0c24040c100d1045003060b5910108d40e0f800141e0100d08054803064078040c400c4040c400c0c88005d920710300001c42d81d03080141c00c000c4a0740d401000b00c0e40d0160350303404202d00c52a40702149a0450318800c807410203118140042030640c41005403540d40c590a040b5106220b4000100070507203c00c1c1d82d030701082600e80300c0d21040e489108100300365915500040c018000b9182c51140f0303010000e1b0a101a03443c002c60702e0440350900540140d041c010402c40b18004c8100c0e90030500d02c0411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 944872922 1250 944871672 944871677
    0x1501060e0f0f0d020409032601030b07020a0f0303020c1e1507080f06150f0c0606090108010603080d02031f0311091b1b0c0a080f0706050301080a030e06090a0321 71
    0x10400b000800c042d10b1200b580079214645810b000e405047c0500c03000180800740e113201d800d5810a000b1f02ea402402e080c03004903a0840b034000000c0c5140d10101d01400156408a0700720312022080d00c04802032f40141441040074061030054064501103401c403c044400c920015100d0107228609030506504002d044800740042002000700c2c0d003008541d0141d02240c00c940d9004502c9090f0500d8440b4000c2d01e90320442c0701d10005100040c0300c00011040e00c030360b10484007004d003070f83c035a0445400c0e2441031100030301e05d540602035000e4111254015540c804451110030942e0007a40c8600721005034694000e4510b1103140d80014200c0c00c1501c01c240d40215000c0348c0400c060803110111002e071055100041c0c5100fa811411410b20006116503509400d0040c01501260380390480e80c1d85800502c06140c44a100e600c1c0001031460054056a0480b494500900301448150700c00380c40c1500150415503120801300400105542c441044101950182d030450402070083c0950790500b5101120301b0b1305 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 944874172 1250 944872922 944872939
    0x105090a02060a1101090f080702040b19270c050a03271104110a0228030e0111010f1811040603050c130b040207060209100e1c03021501060e0f 63
    0x758803400220740d800300c0301c0e2a000200d03040318500180104080d5200410740d10216045405018100d03028040c0c2a000301c030204030341100e940400182068542c010415a8514203041180c0c0b010900c41e000b407050b04280300300b0520003505038003044800411170400072a1000c504a9104e44d8584100051213202d2000a4068a107000450224580424009180e6001d580f2141c2103078980b90003400740240d071002455200c180307903c0007a44814086002940040f0360362520079035044003070548802c0c542c240d105c0c00b042c00c5409004480c0e9000d41e40b00c40307241c2e6403034200405440409100d610740d10700b03101100c0440000146030880d4222810f03d10305220305d051003014008a10013190440240b4000c4900d00040113900302c0000180c1200998170798024404600f0006101c0340b0b8000703203500802115030040005452000f6500c8030100c2074119003044003500c0d0001251602c502c0d14044a001e0700455a155403101080d8410304800d07000f0a000a840e4080c2141c913080000c0580b05441007240c0b07107c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 944875422 1250 944874172 944874193
    0x1703010806010b0a020f160501020d0801030b060f120f060601090501021b06031302090c040306110a1b0c03050d020c1207050d0f030e2701050f01050901180b0417010509 74
    0x7641d4480601442e41e000000003110350081d8020455078410500d0700b070903154000180387d440c200d0244148a030318094003800803502c1c1501e2107134840e0343c142ca074007032400d500f103880709802d00c00c034240c1d1a0344440c0c0000441d50040c0000b00c0410880504c0a00800180114a4080001412280c040c3d110606543c0280344000103030304d001601c0e0500500c02c0d540c49440b5541c00c07050310042445010042c1d000102041071000d080c0d910f2000b03000740d030b000c1c0300103201114200c19840c0d0a807041481d00000503140070700410755551400c40107407030907025540710702c82c1640301e444840c200300c500c0c0102d402503401441c0b0242203050140701101541494406420f682c0d1400700803a40d060036460b4010800e5005d032905d03100f05801401c091882c4400a80b40e1080c00000c2408410400d070401110b4690703c40c100300000e0f0b20318200e03020141d80c1606950b541d06282d4140d006490002070052005e20070918800081749038262680908000c0903181189201d9600034031141c4d08450000e040d650301500100842e2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 944876672 1250 944875422 944875439
    0x905010e10030b01141c0e0a08030f070c0c08060402030f030a020d050319051008010b091326160c0f03030c03050c010f0f0b030c040627060306020d0603170301 70
    0x5000c0298503003004550319038200012600640d030840000c001185c04600380c0b0900441700c01200d0710840e4014108250303000c0400c0585ea4000010740200702890030000a1000c00300d01c61020341140d81400c0c80e0701209059039502c4180703130b51500f107030080c2d510010412007940703000c014805011898802652522211010081d00d80c485031541d0820320000001160b151041c10b0145104403500342c1c0c1c108150301305032030500e842020500c9100d805600300340344d2680c640340040c9070300c1c018200701c41c401d40841c401d580c42d0b03102d150034888490740d50924014840d4404034850300074034400e07943c0e18200c90038090614000350a6901600a0000b840c81000d062000a402588415055400d03041054131141c0316007441e0f01411003107840b40b0189060480d10070702c521803500b08a41126044003910312503140309060004035103941c0f14594401d00d01d40300c0880c1030212460804481c0b5040000070880715142d8944c00300307030380c00001c0503020b0b641c0d03400c0c04000b0300c802445854403028012002c1451075142183d039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 944877922 1250 944876672 944876689
    0x82208060c090f0a080105160302041805090f062706060907110f070305030d05070e01090312020a052a0904030f0503130210030c180f030b040203070f08010605010905010e 75
    0x24a180740d8000400c04503a079901d42540da890329000b403180c0002501d801c0303124080c100c161641040c195946655452190090003a141502d80c0140d0280c0c0016210051a010303100152034040113001c3c410140c200481c0030b0045e14401c1d58000592179442480d00d0005030f80c0100c9102545454000c00284507166a900c101d40c2c0e08a5003138a008921203045041040c14400680320045061103000000410418040040d0200c4a0b4030201080710ba038403c40306880c4401c8100344180007401c0300c00140001402032102003901c1c00180b040743d07017941d6195149440c102d4022800407176489491030104140984c3d501c61841c145064540500d242003d40e805018042e201c03164005001c0d010000071101c0c640803100480858004040388a6045416000360040540002c800f0001e5040c503203103213448080d43c820030101d4000c00c0404207840e103542c890480025000e0000c030307410f0090341c400090607104104901c01620300040002026441e1a00141c05889182e1080b41880100c061110195441040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 944879172 1250 944877922 944877931
    0x70f140904020c0f0f100203070804030c0c08010f02090a0b0a09030f0f020406030b0916140d1106040b04060906021b06031008030c0d09082d01090f08220806 69
    0x400544031020000020040d01a00701d607021240302d007482c1c0d601981400a80842050030703020a540ca5554011102c8050348030446074080807441c50708c0807800085c80780e5000444940509481528244c44001c2c0c6070a6440e002c452250b882d401040040d01494000c0c075200c0101300ca11206840d100071500040c041c02c10b24840030305005410107100c81031025980c034028946500401c104116500ca1622080303141b03043d83c020155100c0e0840d403915039218845400c054525005105181c0149a400c0204001540ba81110102c50443c040c51017070f10b070360000d88003502d001c8000c00d45540c1030180040c03400455602c40401c45d0f201146544180c04e1555612000d040c0075140039135030303a492281181c1d40750307840c0d40301c40c0c0d5a102c0050102800c1d100421203d0350841c103942e9a8a03482d0f070311290507544020302d600b5180c0090f40c91142c1110310b40a2629a2202e0300c034000041490380c2d85460740c90300540820703001d0b22050000101c4403c5410f0341001e0f070400d190100901403520703041100131640e4180040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 944880422 1250 944879172 944879207
    0x5030d0f05030a020903030a121a01091505090d050601051503060d020409051606030213080703150209180103051f021305090a110c010614060a020a0b131217070f 71
    0x103d010341949404079002e00d000034003200d9480225000007400d5100c0b082e020384986150110b01e400740343c0130507002000d44c00160741e040701040c10604004d5956528402c40b10a12401300724000740360300e03070704400100c45000e0405005650714050611484c0724460f05005000d0f01c0403c00c020565580384d92650750103070103030740004e1056020b1401c4e07450160144940310382c0804102d400035600d90303d42c00800c0d090603000c0d5014100c82d910b01c0362035a941d420f800010308800095034005204240ba0b806090720300001040c2144100e550035091041200a8000b9174041d0002070300c500e00080000e0200030950440a011460b106801070440e000507450b0141d640b140406034003066680745c0582200300030300d103113500482d51000c1c01e4030410300901039031040700007509041d48810850316180041d00c2c0b081401c1e4000d41011101b0303658101c449000101072020040d40501c111010929801c40701039001d540d500e8038080c0503a07403183c03000300c940024800c02c100101101c54a0031150300c110003103001003a00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 944881672 1250 944880422 944880427
    0x19050306040f0515012a080708040b0301090e06010f0302010215091f0218090f01030b07090e04060e062d0a020f0c150a0b0f060306010c0c140a05030d0f05 68
    0x3100010040c00020302806031a0b42441c0c2031007449241039204031103824017600c0e4190000c200c9820401d400e40418451801e072a9850076200208400348000c0201903c10300a05203065190300114160750001e8006502542d80c810400300d90307003000c00c0b00501501442d02c0201d42c3c5451580000d540d650b410451000c103005100100700c0810007040001e030800c640300c2c92645050312038640000250082850035030701002c4400076480900706a9869400340c1245100b003000c40c3e007152561031050002a00c3c1c0c800300b00c1107590000c1d541755560000c501a41c071030f1001061200c80045540c0c54820050045841101e24900340c680000c0030300208071100154030b241131202d41d64020914001c0c019510506500c540008203c5e10500c0c01040324503004d00606242100c030b85810b841c0d48100c6101281d0360782c10003c0031041c3e480518241c0007540c0d000205140050a4150903070b6114040c8420380e106100140d102e5554030300c20700c4d10074042000f400f0254001d000b008910300004100a031307002040010302100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 944882922 1250 944881672 944881681
    0x150504090f1514010908070b0a090f080a1e05060c07061b02030a0e010207052718070308090d0c03050f07121515030f080912300702040e0a0201030c05190503 69
    0x100c000400401820058030b01e100d82d1542e0794070555024270104800a1092000860021603c8103072030103941380040108444142e0303503034101207580000c260b901c0010700141e4004c0090010010039200d2280f8480f95516481c441c504481516046040681c94400c031540003a12903034000207503004003840e8070f0224210252600103078140410380e002160001000101400c040c20f9041020302c10fa42103d0600f403481d9070b9010144d01000820318182d01035044814200040b500130006005002001000d040318000e441d600d14000302e201d030b0307c11941c0c1c0c1c102e40b90b0810840014800c07100100203058179000c414406541c1e00d00943d0651000c00001031742d800c01c02c0710b0003114029810182d68081c4003110300d4822400c1041c0c4035003001c0041c81c13081c00d0a0085501d2a400410f94814401003607103103608401410144041c2c04a0510f030540c1c0700c10302803014001680e0359000700e002e0b035580500038180481c1203000044c10740710100001c01c02c0c803d0802040128140c1d454100310062002d142c103640325200c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 944884172 1250 944882922 944882927
    0x7270c03051302130608070e04030e0d05030403030309030905040e100c021506040c050c0d1101060b0a0c14010f020f090a06030203091203040206071406071101062d150504090f151401 80
    0x716801c0030840d803180347c20110b0079100100f1a540118040e484100c20a65844100070407001180e00003007441c1c005110400000c3c1c0a0f0300000c884078400d00301502c42586035000b00b011a1803e400c480c5203130b0f10484407404105d101d803051038091100b91019140084848003881107444016101d24003843d60f505210070b00501c201c084c0c40707401c2044d01c10384e03a808050400042207018082c1c03070f5200c90752038080e0014403d1145000c0752002107854460041400391900d508150410210582c140c03035485142003000b840d80c500c000c2186200c0c280e4070304d07141c417484000d000624800740c110000b070501c10014409140d4001424102802c01e50030415030b00d90300d80c400b04460f07008030710006104e00a4409014404000415824070650792551034480d41004142c0603400c1e039a25120700d4504000b038900b415494034843c654440c1076516004c441d8074441da9030b0960031850216203c5140094030105085c00845c01ca03005030300b20b200750920184451002c4120780e01308006603110f00400f600f0b038603290b0400c82c3d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 944885422 1250 944884172 944884181
    0x170a05042304020403150b010e09060907030e1204091103010308041a2a0c0306060f36070807090510050706150303030f0c0809061302010207270c0305130213 69
    0x40d0042c00c190b48641d5249050440001031241c4c04294606003640142194402c4c411003c2c08440100110001e840e41028402140ba0203400f40b070400d92190280030565400300829001e1482c0008042d039240d140c41d035000202e130041400404e0100041004001241080056030140d4101001c0b807079404440300c000ca01c49109030b00c501c1e9070450800017014081581e02c9040344a4000210076140c1043c04101055100d00381101e95650000b4440700d0340c0760070f0074030f1383c5244840d2000401c0741141c2820607084d9001e1510f00f0500c0400019103800b00503a955010000c907802c4060713420450301507400d2500040c0301d2090703240d21404001000c10b0403003d011740b0f42c01c007940794410046580d05540e104d00700140649451407514440605101c8004e5031203104003d0184142c9083c009451a03850354414241c900340e0101d0f007641140b00c0d0400100d0901e008030b01e51803a4801c0d220059444600480c954400c0e1520340718441c05052a000400109000c4410b80e002510703412902c0d1481c1d038082c1a00c410042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 944886672 1250 944885422 944885489
    0x42090609072d0e0f030c01140c030c0a14210a1b1e0b2a0706290907030e190219061812030504030f02040605040c0804170a0504 56
    0x1249908407082a458011075403100c1860103851302c0d00c407410404c1c207055840345090009400181d10320103405d07181e1041405040180c4080044d00e20f0400d04460503440d0444451041d6084801c1203641e00881070200401502000ba0703104c51007602c068111540402c1c06010645018040001e800803520b060040d11a007001d0f90100313504400301903d82201050440386001181d101310004c0c04646c2a41c2d07a08411204048a81c403810030b9120755641c50103c40c2c000850031604180c03a0940c0f0300d011030004d0b2448803029000b10b820007404c24400c040200401000c1c00610030700d450300750004001100815a4402003540d4201d10080341c00610128040356000c2e01844078401581901050746641701e090b02044980d03812007400c0d4140c861800e45203a00c0039000040101303a08000400c00147c9048500443c280000c10000e44281d80d5404281074078500180500000c10354800c200411021101d9800c2101704515400d003084101d0342c02030942d00c0346014900780261801c0102d0180034900d40f503074490 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 944887922 1250 944886672 944886737
    0xd0201140727030f0302010515210a020402041e05040b010c02040506031203180606060a080f0a0212040b0f100627030c0801050910180206034209060907 67
    0x500380c0e64140900d000360004d404500550030040450041050740740c08203013482c03009010320315032112842c0c80c0e1040c100d111a1051107006103403000303015903205d101400040400d40e116121150540c00c100d1810075058010500c298500790400001d42d80c0326401c0041680e060303400080035241c030000246072440101b00410340c080300000f0000e01d80045030f090001c5002c154203c0d19140c4403a002c1140d030340150628880000e00001c002040301100041a5030071403580c200040c94030f803400c0c40c040000784048070180d0300c031128107040c058840c0380b40d0a865407018226220310003207414018020041c210241d40f9211290f441e00c0341c100c038000e803400f2000c000c0d5031110032042015a94040c4c50b0180004440c0c000d683d000354000c1807523840c018040d050703100311684403000c003804503907080016a8002a16040150001d002402d043c10540c0300449544261007400c0a40b580840160440d0701407074a403818000c1f04858184005501ccd00a4490740100032420512500c42e0003000e0222a9144007500920 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 944889172 1250 944887922 944887997
    0x90405040f151a03120a270f06090b27011215030c050907020c220c03051008030f191e0903020a09020c0a0201030c0504150e030d02011407 61
    0x60900325035000410754003911034080350043c0704104154445041c000c1c0202062410401d00315054441c00902c500000070f100c1c100c108a080080e0603551030182e82246080d020303403010510001d5080702540c0001c02c501030503070746040c1a0001c2004481100d440e4150b0300d40440c04024446e80c0502c510b4103403d151604200007400c6171404d0080780d038280e48402d8440c80000a00803800d0300300704480038800c01c410340081c1708001280c818003150780000c24030111560020b01c00b91501c1c01c001d003d21218401c0a69000c50107081081d51a41d041140d584190780507130040012222850b00142aa0388160032501315040b03641c0e1091b070944000e050b290719411520180d400075075005d50000340304000d4900a555907180591201100c0d000c0780304040840b0819070240055000561180e00444000c250600d0038500f0950745000380b0100c6000d00080201103100e4060803a03990608001481030328a0510080c0039409444e80d01c180c82482c0504950200401001a00d05400a100040c101192911440c05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 944890422 1250 944889172 944889203
    0x50103060b4f09060507020c010507240516031104050a0302010e06070c120b090d140702030115171603021c0f02090a0b010f03050903040512010609050403050c15010b090405040f 78
    0x20b0003040e419074200d41c56490040030410880c4001145401264182c40d868030301403c035152030100f182016081124a40ca00c9910165600c8034081c031405000c840d011110208841040034050320103402052074024814041041250358085101d4201d940a09204031108510b0300456014421480d010380300718441040001c0300355490401c951840e001d980c90751060385074031603615103c00784a103441d00000d0207000c900c980000e0300350041040c0c6100400005492003601907032a1120388a40c0107507a000f05800c0d10b00705000b001d00541c1d11007400800d20310402402c0da8001520801580c660002491490040b40104001d0780801501150006c1c9403129500d82010340380c014043d1030301081e0000d4600030010403600e0180c001c05008506082c090741c00c01c0e0a100078031441d8044180040f14564844034000f45283e10340c4541400359010380d440f581e94070313003500d41c81b0b14008212480c0f4001c860000700400000609400766542c1204c1210082241d444906103000d42e412200300142440b007503502200c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 944891672 1250 944890422 944890579
    0x6150a03020d091407150306080d030f1404060b13051b13090204230d020d1113060f0608010f210206220305120f030a020a02120d050103060b 62
    0x103c11206c000703401841070007450700100d041c1c0e031452094090a43c030544042075214065082038009100208001801c03800d4405c015aa002041e50240e880903550f000c03001860600403240307110307160101c03000e0185040c5603680601e06007501681e550901c90110b0903555241030300043e40000d128010b0203546468a50304210000310008018070351190348410b4480303d03800d0024940040b40e4006001e0703480540540c0f030300d088165411000030b80c0400010020040d00c8181e104200c0038021200300c00c20003078200350340030740b9440301038101e1400115908800c0112450a071030210345c11181e00107031080568a0301c0455002d014180240381054501030060406020942100048070f008000b00e4440786042841c004043c0700f10b00a04821400803c00a41000e105400620701c0c1380346032040b6408580c000403590700700e4001e031a00000468440d401001070280d1406000311081040720742c0d24151102280b045211200044a231a1522501019144038225042d02c40100d244800103900d07a000554000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 944892922 1250 944891672 944891683
    0x7020c090a050f010f2913090b181b0708070b07050304020f01050c0c010c110301020c150603010507090303110715020d020f010203070e0d050f03120106030506150a03020d0914 77
    0x2da400f20b011080000b131441c1080c0c035910b04a9003600b626644001c008140c4411000002d8030449011500300310800d44140091310210080010190008491071010200115001203e031441208000d130b106200b491003400c200c034078020308100d80c1d450b9a8450382c034009407203024111020702600c42c2d40080002e40e40e040310007944114807c81c0c3c0710784800140d0005640b18088c2c0107154a1070342c40665800059402450501d150a01803000006c07024a0040001c0c2a640a4070000301d541d00491400011900810303402604080202c000348200c2c9840b00c00100407234000d101c064200010407000f4140d0000600c0200e02038510416110340046c1d4050001e542c8190300e180c080c005100711000d00340801018401da9000f00242d0342c400014400c21810040c0488801c80180c44070700400d08902401e601c10070060440c0501144004455890481c0290031580c008022078001c0d4010010071420408070021a84201e00741d040c010f807140c444503640302c0102840d160042c00b541d10380032200102c0900191 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 944894172 1250 944892922 944892931
    0x60801080d020105010e18030706050a1d030c03030a0504110d0803181b040c020304090f0b0f0405040f020402130f0b12070906050702040b040b0904120f03091a07020c090a05 76
    0x840300e1010695000b00d00700c5009101e984800c90340c010100b0f103940d1402000c0400b1004445c01c81e82030491a46a840032540140c80708522583c0d20b6000a04140d1010401c00e1000003032000381d418955199040c58503880018000c9560540e984002802c02143c4110a4980d600c05402d04180c8403440c80e1200295009a0f0304100441581c003105028100000745945245a8000e00030054a0341c1024030014142c160001030030b50006110226420b01c180c440c94141003410407001c078030300040206025468003050f1119000724105400c010120700340010681040d41d047c0c80040c6c4c1c8014001c0440508a0f81e5000904640c4e100000000d048a06034017034680c0d607124040a880a4640d0403040d103640c9058031030000420001d00c01d420242c07400c3e9100d0b0f003510201410120b112440f00c0300086641d08201c404842000d03980038803a002644c460401840942241420062030340d6544481c90301d0f442e00ca0820210f0240e03900020100342c0b00380820000300d003002c1c08003d02c0d030401140e40409400110fa = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 944895422 1250 944894172 944894189
    0xb09010c08060628140a020304050f090105090f0a0e030a030b0907020a0201020d1d130c0e0906060d02090a2601050f010e070e040b060d0e070515042904060801 70
    0x10007203521494204211801404411030366040c00d40d072455000140503c0c0281c803000e1005d0b0a0020300c11071410300040000440f15406507540e00d0501d0100102904804003582c01203000700010712090700e880903465000117150481032a1039690200c000c02601c8852220f10a5000100c0c402d002c075501900074010480089500b01310b513690380d60003265101d41248001e40168041c0d4104440c13a0f01441115143c540004154407820703000402240d1214403c01010140303968940c49410556404025104110400c44602003d03080c0440082c2980c001d608080e48402da0000e206400b03036407940241e00042601e0b01441c07080561040400304000381c4e81c5010302c025420440021290f070b2244042c60f042e07407141c041d03000c1d07185c0714803104079000c0d096420680e8101d0b0342c81c6040d074134039034904024254052080310045009000c91040ca4103021556018030b00862284074906042006030f803d54003034403da80c080398400101c0c8100031200c08262610094803810014021032610781c1b09060754141c40130315 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 944896672 1250 944895422 944895437
    0x3020a09091a090a0b1e03010e060702071401030b030a03030209030d0806060d0c110a0506011e1a070c0905090d0e090f070e0102150a0606110f0a020108130b09010c 72
    0x580c00c07041a5103100c00e211460a9141c00e00d03100c80d1400301d111a070002001c02e00001c01101d680c01080800c1c2c04280341c0c150314110184440030b1441d090080055000f100750240c18a8140100060b5450001c1c2c0030f902641040340d20000c2035a4400c0c0d01c000c0c3c04200013000c6644201c0d0504002d4001c0d23100c0c1111340d0081c05080240008580038a007414082c6501808461407e080c02002800a0034400c2c010300030000912814050b4950401845d141d590050024100710b51501030740e801c001d000f4034020048110100800c10542d40d07900c400b03050068000c041c042e550381040c030713260b04032950076000000ea13245001c1c180302101070001807546503219a07403115450030030703400700300410180100c4044000107030540003c5e580e5803080c10001d54200c41030040f55081c4000354000e1842e034504543c0b01c0c4003035503550740401c080c961001c40e84007c60741d4140a810f03146055001c440d01d40101c0040039040c0042c6601141d0248082d48415010329041556900389043c0941c8260182007160b101c00000b4204 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 944897922 1250 944896672 944896679
    0x6010f1404152613081b060f060315010e1503060c0a020c01030203010e18011116060c0905030a24060306050411011e03050405031b1f0207080412060e030a03020a09 72
    0xb0b2080504120380854aa2400e40e5101ea00351300c40f00410074400c13141c2640c103116403034a182041c034102c0c03c0304401c54060042c0d40b411032065036031110000d018038803035840001c0741a01e2280c8450350034103481f2405008892603030351603107220800341c9070461941c141c420f0508228229000a010388545c1c40c40380e0070b8540003039600004405a003c280603d8100318100400700b10900410444e000d40764404000120301d04e0885151480e19812000548901b92130512201c0d0402c07141e07104940c01d203c3d0609144141505103000305c2d5540c1402c1030300070100d50b441c022401c0650240034141c0f1001c0b4594005100040e00d03450800c01500302524212010142100004825030040d4801c4041000e001042800c0080e850003c50146c140540b09980c680010090080303d901c40300742c3e041709030098000410000001c2202031031100660010180014414841072700040c040714103d400f101c040000c5000720498078140280103140180502d982407100040c600c031a01d42507009056282100c0d1110340440c3da8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 944899172 1250 944897922 944897957
    0xa2d060807120b1c050c041a09060904050c090709031509030e010e011b0206040512010914010507120905030d05010e01091a0a09150906260d020606010f140415 70
    0x2a510900d41d00030b50a4050b030342c5040c284c0034080d019038000c6040b200c0110081d0003107000c842c030300c81d02007490700799001089001d401c09540451b0032480030303500d0081d0f900c0c00ea15065100c006240301740e07119404d214045040d0901c101a030401030341e0445542044809031800c20300080c80114012030100b0201c001a0b8442d41c000c0040c004800301c185c490464910521411708160801802d00301d038030040600010984e51140c00c52801003040f000300004142c1101c1c14689d05201d09481d22110b681c1c148020820059402111803440c00003811f03010441c80290300d003550070750140d1002850418a001300016100000040040c125020300380100421201c104c8007101c0c20504004081d04900e414500300088001f0f0ba000d9034041140d014944191034445030220300751039982d80544441c1c10280741c164510004d8085000300c00120350000d0010555640019407a80b03030040100c0d040c08007a42076001c5560040404c2e040c40001583d08603620b90f1100001803000480c0d0303254a001074005802c9035104603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 944900422 1250 944899172 944899181
    0x601080c120c1c09112106100e09060103081812030705151501140a0e0d080408010b0a080d110f032a06011a0705010908031519050a2d06080712 63
    0xc2c0c010380312414002050050000210010740000c44800715243c58000c442000d01403e8001d40760307071280348d150501d4500e403110301d07040207000f00380c403034004100402c00035501a0441e9140359650052030f2104c0035810019425000940d17500b10309000000c2c0c0700b0708100300418804050301d401e240008150b00c40c40d81901034940005e0b102808200c11042d0f0b15030360109600503150400c0140b822100d4803004034080f074040a4083c078102d4080102050901040d042070240b60742d108020364880b2843c0b4070b0030b003040d9070340e10300c200703500303080c89080703075204061080511014001d03c0c81c0400701ca6a0701481100b00e1020000d585010035100d00e01d140140c0450340104c0c4403412140f500c1e00101003d101c444006085a00141007105c4a43d614116400003403a918041e612401071404100504401c01090040402c0c2402c010a4490300380b0034207000b40c0d968030004c0000d0b6581035800d2040701c0301d0303000ca03104c1c04949600040031640700700100080c043e82c80310410b0b1056019550380b00b0b000c0087d158840682c1c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 944901672 1250 944900422 944900441
    0x3091a010510030b030c12160503031c1e1506120e03040320040c0509040c031512061d010c0f03150312122405010206010305060601080c120c1c 63
    0x501100000b81d02d24802c1d00880c050000040980b900700b851302d03000509a060010034001d0ba5040380300e010009088886101d00200416405180b40c440141180e0f0990484d030b81c0748001440c2d480780402c2c0705804540d480d6031508503415081007185000c40100d10307501024400c0e800010001ca000e00400300c0180241031000d1252401142458156501c01540d221a0341c0082c4503940008102d403045d540b03901408043d0748498503116a00c1d0130b48400d0000744e80d5245007040c24103003040f00e1340300c881030b020004900710362280e0548040c448803490218003404201c034000d044500001c01103008c43c64103500c000c040000e41c0c1c85084820902079019020384041604a07008800c01035010000f003070040e08554607016080c038042403804041c2200400b103a50440c500d0003c1c14001e210360344103801c0c001281020742401d0004154540c5142c0c0c50650310700b401400c1d941001316a90201e84402014004d0320200b0381c1181052001b490040d41403045500b0014080c412210301c1c50820380c120600c1e10038030204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 944902922 1250 944901672 944901679
    0x7080d0b0a0f152a26031806070f0e0a050d0c08160b030a021c0e16080f030f090a0506030403020c090c0307020c040b01052a010f020405011b081903091a0105 69
    0x10252018200c00c012901c0c0809541d401c495504100e115050000c0c5c2d45500492482d04070307100e06050035105c03468640410000602c0e845103040c00b417160781090000c40c1d0040f403840c040a800000704046105205164070a07900140711958010070002107804210644800340100e030808010000c17150303244591031041000780704040001c40e46085084d001010308414a40512114901e00e00d20a0111501c1d03207034000040e040000c060348254640c0c204c030801001700c1c200a10660854600c07581c0c41c1e10410b03491001d026400105600c0c05d44904007020010300b00241015202c0c54181006900c07482e4002e07003107100d0442140003850314491a0240c0b0f01075580360703005114000c41c600500004000040300d050510405000c5400c0d50a40491420402c03100c20070714126140c111030350f99080d50716003c01d18524030b0040c8800d000341d0764000d00c003d14924901c0e90f040302c40d43c01130601c0091480b82c0300d044c1c00001c1040c0e5885403010740580084030518410380c01000320354146200d903c4041028052181d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 944904172 1250 944902922 944902967
    0x1d041401200a020c0a080606090606030c0a11071203051e1e09010e1518030304050f060d090b0f0403020c0111060a1d03070b040203100902010507080d0b0a0f15 70
    0x40a008840251040402c1401142d48040811001500480c0d296006408a41c0100104102c90601070707451600000150b48050641c244800c0d40029401000030782810230484500d980001c0c1c1e8100807040007828020300b070400001d9541401007260b480030b640c402045400310034005071a00440b08403100c1c40e0b1101c2d480300b280d040040440750305910841483e410801f1140d0f840c5c886070f503003d0b00c07030400380b1407608030782d41e1007140a08014034165400d000341e01c2504240010000c0b0780303030000198819201210390039030324511002d144008103c0c00c070000c0c114840100802200c4002d03101894040c5d07001b5001c4450405202004640249005041c1c041ca600a600841c030380014030740020062216501c040f0111040203100700c2d10f9904108001d6421103e2030007804258202400001000e1004850600204801c2c0c0c001030410311540c20000c01c4d010000808211254143d408001d0700e4400603c070119059603106890003595160040505060000c030070008003c0c012110311a45c4e0707100c4c420000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 944905422 1250 944904172 944904221
    0x30307090e0c0c16050f01110c0d03020f10050609160f110c0607060f140c04030b1518010503010f0e250b070c14040207110f04061d041401 61
    0x4280c51019120200c0104244640c0704046814405084c40318100c08015540616120401081030702c0d030a1505d051100c0d0a84a03052200042024050b80c0d0098643c9610b800e1740740fa040780f034003d11002d852114041c000681c0d40c94500d41e0030603800b450381210f140300b05484a41501d0301d980941c40c042000708154200601925018a100f20f20000081c03043c1c84400e42183c01141e43d80d40b12040460b002d41c0c0e00e01e9031603c80091881506651105080c980c55035140c100703030340301c17451045000c0076101c0c10000001450ba5031501c3c69800d10709502518903205049006005144a00280180c0e0300c29424009504841642c0d0b00c1600080105200104841c141c0c502c0d0808012400e003171010050240a000400e803000c40e0740090ac3e01a06c40e41c4000341c900d10b45100e40003454142007005206030300400c40500481c80e1805242e100080403108010040c1a800000340282801d500c0252503100550514440e1454100154881c1d8021a543d5561003d500651401c89580b4141008a11038180340c03103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 944906672 1250 944905422 944905439
    0x907050a0f051c02040e130c1a04150f030e011b0c02040e0d020f0d0e06090103020912010f02070302010b03240717040f02100c0b1515030c040e070203030709 69
    0x1c0e005401500300340d49020828511a51255142014480340c3e03900080d040214121130b41905030311141d00400c42090801556441f000d03a15584144015000d9032980810030b045c1303110444006000711f4003240c034140d641040151054441440000119103070900d40880c0709030601a01c42c070950b10560900309802c6100003030341c1810001c982644c215a450f001010071800401116100c0061600246840107032410301e98604100c0c0786004040007a10310b40b1681540310360069408142003407e01580303907041000407640070201500100c21070f42c01d1201c0c600c01c41109a0050070000e000ea402440711078482d070241070381c648412000e00c4420400050320b003c2032014a03c0309800c4070240c03400403090154040741c20482c2e6016542550000c103520b140d40210302c2d161455a51248090420b555010f03281e486000018000034601a235222011480ca13403143d4451000d032054201d0164225140e080c1018a503240f90071038011103170403c00d40c9021919060000042d039100c0d00345903684025550400030301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 944907922 1250 944906672 944906687
    0x6090501090f090c060f02010207050d2007081b01030b09010303030203061908060103240c0203090a15080c090406080304031a1008100b0109080f1b0d020102071208090616050c0907050a 81
    0x6c0008555090100c040020024071000030f00da141a83c942a120b44a590320414250030381d000348401c0c0c0c2c0640700801c90554049410300f010b401c20600071040150600050307000e89102201541d001250070000300406416a025502401d001c0c2d4540031003904400c547c980e404841c0c01109295445440100f000a0010152840100030fa01020701009038085040301520070750001ca1000d0381000c11808164100a00a28000d010410f180038039801d1518014200e4a07016103030304540080000d52003a2030703c60342c0088008000d4481140d5a0b10b07624108160310300c0c0210032041009410300c0100c0c0782800306101903001d03036440b54041c1a038007401d00e00a80017030070082041814072811140000300c0b40401d004908030b0203d548040d00b0b1002c0c0386031114036000e5441c19a207100766685902000940d030700040c45020740340020212880c0e00c0c07544c00c100781c5078000d003500107030300520010f50700b110716000f4000300039454481c000303c2c0c601007401c100300004071008840c0075000900134042c1c1c1c0c5106200e01c48 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 944909172 1250 944907922 944907947
    0x3080c0702130c0e0402072f060d0605180105010c0215040803120103140f06070c020f0a0801020a0207150512090c040c05040e010e0417070c210b103606090501090f090c06 75
    0x45555010750f023000704030f042c0c02454100040c16500c000070041410310b22001c1c801c1101c12000e100e4550b0601c0006017007001c1351600030340190700424200780780307a4100c4102d4015221400842c2e464020b0301c0200c84202c1404d000483d803821344860551900c090014410300003040c0328018040700c0d51004000c49030004c000e0002d030781c0211014000c41464599030182c00c0900380c0c1500145e40c0c1c02101c0000ba2409850b640a60408004000b1b02d080d12944101540d03086450000300a41940320b004420307140c4000c41540561241c600204444000d8102c2e005104540100d40545000d80c1da44d00031201d510340486014203040c141021007680d60b011a001449100d1282c00380c01800ea44540244068001980307400700031181201c048024040764420895000c3d0300708500b45601820300031100031062410310080c2c181040c0408082c114154074a0201076103211000c100441341d07603110302c40e000e03000030b02c41d240509140c900c540b85600c08500483c40c1c84c0e5000f08056088074a8a403044a08440000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 944910422 1250 944909172 944909243
    0x3410a0206190b04020a0f17061c020f18040c0e0f0402150d1401180b06180324100e130b1009020d090b011706010303080c0702130c0e040207 62
    0x20b0710300c0c0f4140d903188060f00b40c0c1066541c41d40035001180c1009408510b42c540519010350740b1000304212030703640400012807000c4105141080b50301307d101081c420090810310380d5101080401c407540d400c54000c07190b44164003900c03220140643d07404241c10030000595043d1132042e074600010300541410442181d90020100b4242e180480b0701809100300d07030300941c00303007402d0803013200406c40440c080d0f8085d40900031a640c00c01100c4a120300040251140c51101c461140062402008942c1c0c00d10003440c04020400c0d12210308880e020303005031002c101f11000d00000c42007a0003c00c0e0f030508e0442140c400c83d00f5041111a4100e07607203500e40c02400c01804001d44019100c40424584c1c0c2c0d500184c001d201e4221008250103140380f0709120b00d0407058000d000011000b00014500703d400241007811640c05080804a94669100b07a0b4940d1044940107500b2403085410440480c0030760703101d191400d1040d9104403103911200100010fa210340500903002031010310720390122841841e444402d0210b0326 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 944911672 1250 944910422 944910431
    0xc170f010b1612021c0215010918080307030209031501050d03030e01110f0403050c10140706060b22060206012709060603030503150402040302090f0403410a020619 72
    0x507621046100792806421006811084200305100c5c1d407491440320182081c0050306021070f0300800700991440510850f004181c40790f4401d450241c0382d83e4000e403001c2e0841c0304145c1d41c3c68410400742c060741c84003622a020344160700d12043c0c0c030078210151505036071001307011300640a803580701100a8069619822055540c2d10844a070b42c07050070780140b9001c480420b04c26129895402d2040c2400c500d002030500400750103c0d01141c199004ca4a0742d14020041e04c2d0a031101c1107810a04001c00c05600450744988000947c1804d501e42c2c0c00d01c0000d103030700b94040d000100b0f440c2d410480c0c0b100428404d01c00c21030031680c60ba24a40c49071649440200303242d102c00050b000b90035183d22096070010303032040d00443c6c000000d0007901080c11314001c042035070959040d0315182c03456020a02c080002451680c0b14040f80700400e0802d80300e0030282407180c60401181c0d181e25049604428005100810108403c035503140800303581d08680155040079613070740c000e42083c1d079402100a598400d0700390740000403983c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 944912922 1250 944911672 944911717
    0x902060c06390f3a2007120309020406090204080c1e06071e03030903110313050105090d0c09050612011109150705070905060108070201090f170c0601090c170f010b 72
    0x40800484800c0da15a0750481a407030841e40b080c01c40e0034003481d170740d010b003a00d25600a100d1046800c80314102d03071101030515442c0c0d014400310021319510303a00951242c1006000903e008050300500252015241a183c415042601308440844c044200f03002c0f14880c402c42043d82e2800034003801c1c00501413083c3d000781c4186030710101e03000c2a128004501003552440114241507112027201c0642d080c1c0c00055240ca003200c0b02180003010184501410080000b4090074551a00d115104446a0060b401c0d4140c60320740480303002810080319441d020301d00c25800d1008140050180300032030a0461001854980803030144031001c0341111109513a80e40421842c0d0000c0d8042101400904c0000710000ea01d0a21000040c807203180500400216030500c2e2951000c19621200c1c04501903002003007118060f802440d00001e406488062801409076500000d141c480a40186807045001d40d030744a0035101d000d07240d1410800030380c0e03013204007051080140200b80313844000340145036110f0154140c0400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 944914172 1250 944912922 944912977
    0x8010e180f0328050405090c0f030411030d05040e06091e040b0a0c050a0f0e040e01060b3001060c0f080a1e020f100902060c06390f 58
    0x40d4245030245580001090203040a45030b0003401c20000c3c2000c907014054269200a10900481c01803a214a0315000400c2d54140440101d503001c18005002c140c0f2031a06042031520b8039001d9810b07602138020000c9030321740984102d04490580780c2814030090790341c841c1c03414407000403801005075001070724031480c401c035030301c160a02c16101d0b0307210b40c200d01110316241d64224141c442100603201407101c18007003584640d411039039040503164146011342c0060b5100000601a001841c0e80010369481c011001c1134500d0807000400b2008000e4521a18002d401d1880d8070314000c2c4030500c152115001c0d001802280d12440300b00c40140d0081d48c0484c010020341c1c580540c550700c80e103103c1d000300e0080d42d0380a600380d58006900b1b0f24460713240041c05007000400340c003a40740d0088000c400c81c40c41d500c000084c21962000152444185a202121102d2800c0c541805c1641c2209041012449a0865515503030b40c4514480c1c1c4440c0d01c0210b454140f40301003a0034030017a041401d030380d01d500f1003c082110704000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 944915422 1250 944914172 944914183
    0x314071e0311040203060112090c0b04082b02031c0f02132301020d031e020d0203100b0406020a030305060d0b0a02030a1103040b06331306020d08010e18 67
    0x3010580c481112803841c901079034080e21950036a4010b60051040000c0c0780e8021030000d4841301841c40104c0c480e00c4038541000c48040d90782000300f0100b4003003808074a82000151114050103107840c51a080044000e004007060f80d228a40300060740200310101d0082a12110700070003003c0100049108002c2081c0401170b6003001403110003404c0b450301e0422400c120440000307500a18041c200f50700e40f0f40e80300000c2d1525444070300c001c10326031691508404944c0f50903499060414004045444602c1c0b8000940039620a50340405000c49591010910302441d004a4080306c00940080c11540341c01c4e42d064019000044c4220703400803201d0100720104166031a071922401d040d11b40161790385800d0b403000c421640c0710122204200014010000001c0d80c020180c6d030070100441c2d100040e00b0802421911071649850400b46209503d49140f10548000010705449440041c20f0402d50b07841d0041240d660005146000005000c0310040141031a4004c0c1690001440141c0c44d000e2a040c40e02c0c0392805 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 944916672 1250 944915422 944915459
    0x604021e03070c06050121082115010e030d0c030f0323060316081203090c1207210321020d09030c06050105060708180d06090302060a06061107031407 66
    0x1951050f07818200481e03071203118050080141900280d084c43c032504106184009001000c999000955501d80b40c1d8000c4c094a880b002241016060b19105446200b1011841e070641d010550319000f0882e907180104840610100301d5640d602d0400117501e04403a0a8a503400450a15076100c265040c600905c04a07401c48100b04000081c440c00c00809042c9010302c5000f84c42c0c00786555140901064001040c03003000d55901c2d840740382d101d440b590031b0b081c1020381d003107038036039200740d0200174036824400105d0290200c4103038041c000c48a0501405400720b012508000600040928100c4000b80c002001c04040a40d6120070050812025422001c00c0350106070040e000710fa6518001e03c2000b55034007030035002d09026180c145c1001540d17070340d100c00c40c010703408801051101c40342112074545400b82640400b0343c1040c010b21914845040280d210340064990905c141e042540108a03503003d1040740606804c4c80d4001c248441c51502e86140180190445a846009079000080c4003650440c000300c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 944917922 1250 944916672 944916677
    0x130c0b070602220602070e0406060f0e15010315051c080a020c0f03010605030c1c020604031a062b05120307200606010203030a0e011b02060a06050d02090604021e0307 73
    0x11071000c0c01c0c81d5480c68611600c0f41d8800365590f0010700149a020481d03204550341c185c8428580c0e00c0f1880c20801501003a0428280d41030b44290000b0100d84014030a4012007054501d1038000c0031403030044041d1000c01403280c540c00c01c445000c220701d0401c101080c3d042d0b08850110202c00303030325507610b0a060f40045c0060b401a4401c8802200d2803a0064402017094000c5000300840f034076040c0400c1c1c98452024841344134100f1101d4000d2590746183d0342140096000f03040651f1503403640f408105c892900c005008041003013100084003824451ba000d41c13881011140801d0803101140c0c0c0389944010407204031503038020032118491149012003c0e6005010320344552a1800b00c106400310000d00910b4042c05e01e03480700d4188041c1e83d030044100c0760010002030010030001039904215000d000613205900d10303400d0781140100d16640c0420030034000c1e40400c03010b0003290307030f640104202d0004c183c0c4013951180180c0003090b01894a42e008001c191241c24441c05204d0304d800c0340c0c010710781084562801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 944919172 1250 944917922 944917927
    0x110a030810080304080a12050d06031203110304050604150f05040f0215070b0c03070c0b0403080601081005010504090f0605090f04023a02040b0409060e01051806130c0b070602 77
    0x1880010020450182c598100298102072620000c0d03070f035800b007145020f000007849101c03a001081c03049048440f082e0b0812400c0c0201c41e03991801d01001c15001c541c15000078540581031141c0c45508044a0160380c00074010500b54580b6165003010025074001c1c80007056440f920340242180344d0245500c1240141940525851140103200076504d880600144c801800c00c80e610000c0e501140c240d80108084038001d071250344800060f1035603c04003001601c5422a03500300000c045d0701400a034440d0100381d81c2e4418640307845220100d04220380c080c0b80d001c00d1051205020071034031a440170304260180c0d280402c034142d644010401055041c0c5004481e00109001c00041d4185140080091170000c60038120303030b0b02c50542201801c10000002c103800c3d40701e4102c04040d599144c00070601d04000a00810280203146002001800d1018a9050319428a40052242003040d5020a030454022000d0b0080d0740e651006890203c81d10481160105c3e110302001c00d664180d000a040000e1240c240140d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 944920422 1250 944919172 944919181
    0xd053c06100603150e06010c08030a0b10050a090902030a0b0a080a050c0105130302010c030c0c090207060608190b04080c0111030a1422030e0d030e01080f040b16110a0308 75
    0x361424801e82044050504003040380251010284603c030880700105d11240d4951540341c0107d465010a8102030601a070200c02d0000302e145030341c4848c0101001325103003620841c40c01c4059a91703000320080c01d008650001020050032401d038006560000d400500010318240010005e070582d54a5080426240e002090800400200b0408007040c0340c824200700c0e081640181034001800800d01009041046a07900801014040c40e03400200d660300444440c600d94640f25440d009410800040c1c554a06000d000079080401040b981c180302c4401015001c044000d8840c2d00d5951805403044900d038008104c241d135088401c0c822001e22001030720f62213030780341480c06040050b80c10032144218000344540034010032000c4410822000d1000b9064150a40584e00b000c0d50b2a05c0715207401034128a90020150070503610146000d04280d09803a600700d01e89904141d68000ba500701ea0040036500703003002003076143e0b00700280130b10003410616000042c8041e0031210f508180c5042c400700d010034800720601 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 944921672 1250 944920422 944920441
    0x3091206070906140a30270b011a0f030c130e0907060809010b04050f070908030307020606040216020d0b0609130803130c0509010f030507050d053c06 66
    0x5030020400392130300a241044810214803e48a41c049981c02c0c0003210080c1c4c8904240d008003441c0340304031095444041d41c070100070840500520308420750500b0816a20807001800d1100102c00d02c0e80015a168442e03007808050b040c05601c0072040394402400380231410304410820003c52007002c0c250801030300e804000c1c14554814103213400c029040d1818000f00031034000000741c00c4049840700d1400c5d50b415142c00c1c000b5801000e10000c0c181d0440d007060200031210744c400400500511b40c694619071041e45d151041500c0b40026912440140c10240204030a0b25040d006000c0c038540c0503410700b454400f03e6002402560703402604940521001080004600d04094115840300c0d0558890307104240b80d507111000c03440000c29140c9500d10701090340003400500742602d0050324001d86940d2595858545901e80305106210407603040c0304803100441c0a0a004284070030b002d0340440244210f4041062415420307035111710313902801e011941c00080030b00100b51a0002d001202014050504125850 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 944922922 1250 944921672 944921687
    0xd050406020c0f1c17041410020a030c121707020615090106120f0f1103040b0703200307110105280603171803160503010c110d0509030309120607 64
    0x485100f0b14402c0807904103615480da8000c0c1c4081807041d4007420341c1c3d503071070120808160701d00c5548040c140403401040c2120a94080014031400301d450700404110404101d03914600d04000400144510240d500001c0c400b001d82e034510451414500076140c481d03286503035600e80c1100c15000682c0702d41d09100800b4804100d180c1c1080040d51240c03c00d40c10b201000e449404288210308146582c1d01e12568051242d5220200c0034860311424002c011409000c0d400a810a41e401c0e0742403481500802c0603680203104070161511040c82001c101d207901c0c0c1030101590401810f01040c01180c1d0000300d010b242c280300380352080005514520044600034041394510300420341c5003009600e000c100b400810741c443c80c1610402e42124800d6501c2084041c2c9074030050705004400c3c2c143c0300c0ca1981c3c5a584d00c81900c40303010742d0360680c000c0120040f0303110308841d00c854200c01140c00d500203040c411102841400140540e200107400c40c0d24100036100403c049a00c00d003403c0085411100600c00402e901004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 944924172 1250 944922922 944922943
    0x60f0c191b030c051203160c180605030703060203040f0b040c060f091802090316090906110901170603070806040b0412230703170f070e0d0b01030b06030307050d05040602 75
    0x394081060660381c0d111100f0a2501031140310345000700344000c0503503007007046499403a4404e2606c61070250a19105400d014140940f41c0c5101428400c6200617426100d5641280c1d40180201601d80c0743d6110100250b1020b80159a00129142c425000c200c813500d42500407445524400041403810000501140000020030b0030014011010480c3c4034000850030580c5002510060340d50a24000103450111984141096450303805000a0f400c03140340d10030520140510428030603000700c10006006031142d140d40c41e01054040390260400c034a07050303001d940010042c0c21541e4440c1c49501007864800300726402c4541903561820002000104140c0070800c0e011410324941da04080c09840313480298030314449884040c00314206051506c11010390300c4900b901207114402e4200f030000c59440703141c100d030b9610204403003002c0b0750181d00700721243c00a211b0f0411980c000036400c0d03a4503c1e000d1280074000c0769142c40305000610103c2c406104000760240c154940f29690703490040082d0400b8030384030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 944925422 1250 944924172 944924213
    0x9240a051e0c0708160f0308030c0c100c1218140c03011a040b0108011208070813090b0a08031809040f020301020a02030c010b0a0b030f07023423060f0c19 68
    0x40200000d94008401c0c80507623030701c6403110381ca0b0341d15181ca0000a01030110b11750f4040c80f03500707180743e8000d0301644903620403080da554001c2c6200000b18408181c569422108445820414001020812a98081580c4940e18040d15010f5001c2000039007510300704071442810848601c400b6078103181c00c0c030415051910a00f081480c0307614002003030b281550f541502a0405d0310000e4160208880d0340b044031441c0614000d219030154981c0701d18030007404c0200585010308c0380c206000c901110000145c4140c1641000c2d0300000444400a00880c000058000c0342d040e4204004c16006907000e001610500010381c3c0111340715821a1886420354400440380c1c0e028030f00880c4144620030a410803264841e914801c2c00550f5210414100d181c840090080d0101c0e20682c100ca919204a61700350101c40b21485000e00740c03903903e8400301050041140c00740c08840d0129840b03031145041c480d01802d4a10b041c0403889040c400c41a600070306251145c0703001800440d803089440c00704100592035490790031086 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 944926672 1250 944925422 944925463
    0x120507030225090605101704050a05010c120e1f0f06080102040902031914070822061e0b0a030f08041d01182f07050f0309240a051e0c0708 61
    0xc240107010041c1f140703410005200c01000080500c50f0800440d81101e038000020010307040620001800001e0006021404a007090706c100503580c00000c0606400d0110945038802541036840388000b484003220a1016984400c80010b42ca8401e202030401440000405a6245090029144140d55401040c8c00ca18a082c24011113581c02c00d0581d940103030b090074080160703207449002100d50f1084402428000e1440310741c8104000187e0001450482d94148501c0790000d4100d12070290b441e4080340030381085002400f00040b9583c4032812000034018031180346065140c04400c502d103481181e03580b054511110040060a044100d40c80c05055a40302c10400f07403041c130024128140042c00964070f400021107072025801025402c0383d05140d8410f0460b5200c0840c0640c0944941101c0d118520562802000d4040c150340c41050b5544509501c0c0c4551a080c203020040d140340d00481c280f0754104c0f00b5041149400164140200000c0c4a404006e00c80075240090139840c0101d508a034800c1d02400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 944927922 1250 944926672 944926699
    0xe1003110303042102150c0f06061509040f0b060703030207031812060c0306210501050c03060102151f0816051249080105040207120507030225090605 66
    0x2480c1c00304004002c01000150002e104e800000c111421091b405c1d05240340015116254110010300d0300090340c0064280d80701da58074102000710f04440d4060130345400034208180803035440d180d031021100100036030001494401403804a8580d40188000300d01080d400039168090540000c04082c06501181040030300d503040c80e040c0482841a0700c4014980c076226046400390501a400120191540070204508640d911030b446040c03140038002030710194a0030001c00d60288405084911449040c0c00070700124108610422489100401e00d14400f200401181d20760020101400000c020340802010310926400813a0004042980058411400c0b0050010390071300200d10030440e1004031503401c84030751303540a92650500036120326441050b94850700c805007011b40c02c4080400f10003561010703440da0301c3e202404124800d203500a03181581e2440e03100d032883c2c8101c0040411034031901c180e5000e40d400500d180c1d409406103404180d0340140c118107101041c0c5a21aa800074000cc44014511040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 944929172 1250 944927922 944927939
    0x80a110403140c1009050a0e0f1303090302090f091b15090312030108031b010c0206060919092105040e0c0304030521040b0705180f04060e100311030304 67
    0x19074440109206100b03098902100c1d8140940c9108103c0501140c801c03504040700280650300c5405000c0c462500941c0c0810740c9010f90100c144034950b90082c156094032000080d1910400c000802c07010440c40503008001030b215080d4860080070b00c1034a0790180d04110300010b041004180c6142200003d8104034506691140c0caa5a00206001d0030240d413800f000c004242810240361212462400000001440420000c0248003085d550500701d00300c01c20303c01c00d0600360752191038642c00581c001004121140344c02c510703441d0440a0300c4a418040c40d4005280002c3ea001d01c20160f50203104040c0c00c040c41586060814441c000603d40b69140c5414403071050b00fa250041d2501141c03050200006d0101030240085034240b40d10605417584042c030034030f204456240212350480e01c90080f24040b0344024003440c2500c0c001c10302c4001843c5030307111a40620083c003642c402c0f216481038445000141c01035180804038015882000c0a080039801c50514565080440c060075020303510400081050301c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 944930422 1250 944929172 944929177
    0xf060e0109020d03050a0e0306010b070203010e16030b13020301050a0603050f07050a0b090607050f010603050123070807021009030c12050703050a03020705100e06071d06040504022101060f080a11 86
    0x1c1c4d25050560303c0380340c019000c66000e039030b5500e01c40d018807842c0c00100e18207030144042e00003184210000d1000e24490003c160700c0d0b0b0540d03032086050420b41030082c8001580c8030344003640420302070281c0411840c0c44d0006401c0d91030696110458541c0c1d840705006102081c40390348000320100001f0200145080082181c600b4030b4805ca216000d00411981d60603540c00f0211035045d0340009c00c4a010002d1002058000c1002d80700c1210250700c1d15800300140c240c101411034007800351500070000741d03503101d00903180700400400d5281103000341710045150b50103910076940c0c1280030382d403240a5005140750003100d01c2c1042407500207105042c0608800240d010084901c0e161181c0740144e10750b0700c10300c0d01c41d1410907144a2014610300b0500c811450010029440303120f94401d030b0f10070900c0380100506c000508941018607400140400c400d0041c2d092640007000e0b180d200440c0300d01040c0c13a03d40c1044030781c01c00b81c000707200042c50305201d035039803550103180740e030b0000398000b0104076050f81050116400e2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 944931672 1250 944930422 944930449
    0x1061a071b080a05032205010c031209080d09050c0d050703020d0f06230618150a03060f021e090a060f270602070b0c19020a080a0f060e010902 63
    0x4a0294000050400199101c40000d0071076004480c01d0982526020303489400c4000c40c018010100c825010390262400340400031140180c50359103d003da00c0c1c40407240d000c100d2a41070b204a84400300c0d100040c01000c0108122401754030300007410042483c010b030805400340d0381903206940454070744020800104000080f6503041b0790030030068080d8a400d860000318084041c262610b0000d1003240c2903406000d0294482000c2a100c005646020070048492402c003036007403407203c007000020100d0f0342c1c0c500c504c1c00d03010b8003d2128085036070301e50b40c0700c094a1200011018070380d000328100324108008000340700d80325000204541420b401c007020030004a214810711003000425000303001418058850084081840390708027081c0b074280400c801601001e440341c2c00c018401c440c000207a0781441010384120220040281118088100300c1c2c102c80407032403038245d0b488000c0800c0050300c04010032101c00b58610800720a17558180034200b90f411122140207000540e41450581c0005a0381c8403503800c00c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 944932922 1250 944931672 944931683
    0xf06031104090507020f0a0506070e010809100e1015140d080304020d020609060307111603050304051311030703151401020c04050711010606210e060127140901061a07 73
    0x1950340c1c004c01240340080d442034080c811300130300c4440e205004012810b0b0344504034507224400340100c134200444491600b01d89521164006040c40c03641d100013900041e00001152080300e80e01c455a0523030313104032944448001d001020f0307150100b0944001010041100c60300311032400440e40207445441c841d200040c0020b12920800d14860110341d138060a0b0b81520034090582a103d107040c201c040d03c4054803844802e005d21410620501404001c4010802d59034081c02442c2043e141ca024049107580380c8e10410445a2140172039900c5a60800c00f45224034403035034000c200c1058940c4040c0802c0e072581c111901d02114110f500c226646c00040101001034107407800200c0f5034810310115050488212040586c0d401e016001a030a0384c41100603131012541240c22804441c2101100100c41000c58030601940080c00100a40e0180c0b680c080385600317040302c034031a081c90400e55090440d0544104460070080c1c407000e1160b00c0009110700703005804031900003810300c80862000f1100d4040c82400406 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 944934172 1250 944932922 944932931
    0x90708010e151012080a120c0c020d051e070608130201210b040c0c02090a05040f02130921021020070203071a091c0308010513180303060f0603110409 66
    0x710140c40300b0381d0400504c20941c1040d43c64201d89051043c3e90f20020040002552004017007403a48902e1242c030988403007613125a003242401d542030180244040c0360a40700c501514507002d00880c05000c0a16020b80b00724040c19110b82409009060040042c000881d410700035022a001130b604030003c95242004482d04149a803101340019000d030541000769600103050440f040e40792504401e803507440354421520a0710710340e00d10b040c0c1d504403241100e0180400c0104518140982070a090f1103d1541e0403c8000c19260300c65103074440c90311070345698032004013655100050226410b0145280840ba01d050521000305c0d017a03942d8188040099807884003d5000400d48115a07082207202c0061880101c030101604400604040c80d420903400c0c903001c0c8810a2040e200e03641610210311207030f540758a07100c0150b404c0070180000d01281c01c03480313404103a507071280c070750505011885042503510a9801040c11401c1c04103401e1281a1580080705060400d400380c0d14174440c01307040d00d041e21a00c181c0003a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 944935422 1250 944934172 944934181
    0x302071a03071b0f2d0b0402150c160303300b01020106050a090c030b060705061302040623190807170c060f0c2e15050a0e090708010e15 60
    0x403a030401d008002058000c1c4100424104050003400e008107003914804028400300045c002d200030f48181074020089840300c1c1c0090014a06610344130b07035400080c407040c0e007466a080b00052400a82c0912962503406880003001019844006803001d940d68a0b40030401c4409440c1c500308400105101c550780c3c54550f0b411040e06d910075444080140310041607114035682d0b40c0074401c000c08401140d400042c0c24500c00000717078240f05003119882c6512000615061740c0b0080c42ca4500340715048200d9129450f02000238805441e00000400380c006840169806a120020005013070018a01c070750403105072238000c0090703d4000c41d103041100c1c60381000f0710620310090802c82c200109060090b0348500007042c8007a4074400742000d800076920385800c951481408845000d07031b0103819030314280c042d0324000b042c03141000103401c10091080e03d0700d540c0d508036440341e001568525043d0400c000b000340309420005440d400704030082c01001040002c006030b1500c03841c003980351404080100444c195000104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 944936672 1250 944935422 944935457
    0xf03040215310504060612020f130305010c120501081e071a03041208131118013b0106050c0f0d0f0e01090b1c0e0102030f040302071a0307 61
    0x4802c080540c11401908815607a00c00303001c000032400405408818a40c08542428035108035025140291a5250b07224940c0307039140080e501c000500c188154062207070a0303c0000501100c0007075445170001043c01c0c152050300804a0700750740e10302c01c01e850509c07004120510002c200b8008c03000c0c034005464211125241503d01c0c0070082d0380301d8030340d000c0800080b0040300e100c0c4000c0c1d8015485469009801c100040d002c842220041c3c030100e540c100b403c10800006030340f11801d41c624541c0034204000e20414009038880700c0009a01c9102100220400c56640d903070310701d030000710208950702c4158050403643c03090b8440700700500940701880400a014030018208000c0e9107a40e0501c501155025209540002d01c00702080f019640481c411851380e004030b6005107680f41c2a5108688564249404003181307142e028850403061000c203940380883e144d9101c00703000640c4940454031402010742420314009151054641c042c41c03180e43c41030504060705212030304407a001301c8240f5000452003c075000c3d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 944937922 1250 944936672 944936677
    0x3150b090f03032a01020703050a0c050f100c120911010804140609071d06010c02060d02070b040c03170307050913110a0f080c0c1c05161103010b04020f03040215 71
    0x450b9418400420558804500e6158080000e261000c3c6031003041c103d129000d09134003410078000e020900034000907400d640b007860302c000c503140100300700c0e40c0030702d8520003280c24160342c906060401901c4103402c2c1e40043c2c1058000300c1c544040d460030095441e203a00d0b0001e50000030704050381000b0041d004101030200c88080040b0211041003607646604246c0d001641e00da1052003450444104810052804003400051038072070304043e1a41e01800a5907400c1045d0f0764030814900e0f002da542071100780c0118005d01c2030207100f58400c42011004a045041080b00e07a05c034100c1084440408104120000d940f01040e00c1411000795080e81c1c03a41420708400c1d01810700010703c5019540049200c111075030380081e801e443d1140c2070b16616041c0c4c4601030000c51500ca00310ba00385a96118000c10b44504900c981c1002140b80c8500e400d50a181e10109441b000017003049051320b840d40c03401440e80b95880d0a00c2109007105040350118542621001c0c2d40c002e07800020701c043c0c0301d2101c40100c0440c120400c0c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 944939172 1250 944937922 944937949
    0x20c1008060f01140c030c0d030b330f03011e080d031a06070f0209010918171201060c0312020a082a0a02030c06010b0c07151803030f0f03150b09 64
    0x2011a11881c0e48445c884d0b50b03030064140242e50740301d1081008103442c000d116030850600040c01401c20112403107594a500f02c4071048000c0d58041440100100b041d16a0141011610205d580382e680d5261441012203484402c140102003040500100700030740d000038551101c25024100450086140d003050030302c2480f5165001d420440002d10003081000c49101c28000314404c03503001c1c0e400d0343c941d04151700b21900062a4a5504017084060b030114590101c4840c00800c101d495a25100301d02500c0720b01182c0a070300880109401200035401c043e044407644000c1d050514045040040090000b804214064100790450701110800e50340c0004c500040d14000c0c8460480f030341c1c0d0302c4030400025600c1d403080030b00040764000c003030001c1001c1e610302045441c103500040003004410f042c00c03000c030b204204580c949814071207000e01003400502541d046900450003521085132100348084094241c1c0100101d95040501e8070811000040740c15941c14103079400080440d171502031440101c6c00002602c0c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 944940422 1250 944939172 944939207
    0x23092a0702041806050f0f0705280804020a090c050708090301090606030c23030c0120100203040b070806012307060614030d02190321020c010c020c1008060f01 70
    0x208804507643c1880001103209100f4a420006a0750312841c10325190010703103c00080c4169040400c0426120f0405040c0903401164001d0a0210840c1909282d03e1b441c8008070100e0349103002c11065140902d4011b0050103180f100b84410959124010550721a8440c001c0088034081003000c81502c096010001284e446403080000315100d05080031102118421210702e40440150765005d41c3c0d6030130100b00b0880028000740922a001001990480020101ea00100d1022044020180f104000000b9800e220507070042c1c0e03074181414585080e03500100340005100ca45070511400c4d0342d000c4c3c01001200040c40c0410307018200c103015078966204100020744100d041540204081d800b81e102405026001c030100e80d994290b495060761a458200000c40040d0401d00c1d03080c000c00e0103a1100c00710300d11401e04030018240402000c004076000120780000580d5140c82600c1c80030b404008524200e803044039200d0701e202090b04010144c11006180b14054400c2004040c0c0a03401030700c0c03600d81002e400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 944941672 1250 944940422 944940431
    0xc03321810090210090501081305030906161e0519110d030504180501051e03010f0c020606040b09060a290406021b04020306090a020c1623092a070204 66
    0x11000440984040302c0700380d10494054080c0c0030040d000b00c0911048500607107a2503100e540d1025481d840d084a21400e07a900d0104000b15031003640c03034000030b100407828552000d8810f400c80c10b210b131070070340400b46181d5416003100d040c03008070701f001030403d5003e22841d562454448851408861081100c5041134000203100300e92420540c005000e04103a0b03050182e10360701c0c00c00140c5805d0030341e2428495540c100d0140d0306c0304032000072140c20500f940c11020b0000b0503020583c03041102100c00740c03102280142c1041003800811304e05402001040c20049840030001e09100001852030107030761003080030301000c250440d14440d09000e014104070070300035030b459117403035807458042d44824035034034950b0b41d00d44550030a8000c0d1074a442034034007410020340940344580c1d4590f07508000354400c030f1411010f4815030000126520140004c43d010b4400000200a500d100c446903120405101c0c603564410780c400e000700704500c52585c1c1700c0c40511801c03d00c2d01d8171502c03d120b00740241c0e2142e544041d40080c1003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 944942922 1250 944941672 944941693
    0x3040221010b030f0d0201050c16020607060207050604030509040b0f060a03151508010614040303021009151a0406060201050c070f0f0503030a060f06050c07060810080102030a0c033218 81
    0x843c130410b0350a151b170000c0c030280d541c54409520502c00c2e841602071410080100d17070090304106000c3c000841c81880010318008064650a141c078601301c6048000a100042d0046241041e01802e05c0c0c01805807080b9050000380400241c86025404081081551b5a0303082210049114010700042a00050b006200514044e0041060009010701c20103d200c041040c441c115000d412901142c0e010f0340507094070040081405c01501c0026001e550702d00340781c002c0c00140b10301c505c0344020400c0d010030858202040c3c0e40a0100352401c03913000c00d080da4584400c0003402c3c1d580d4422109030940c0f0400c4c0c00c90f40002403034001c00d40075041401400b50321000c01000801c007a01d81c01302c01980c07201005000c03504d80da01c20407201072040740100c20031604401000c026441c090040e43e40c0004c000c601c0d402e019625103044908a8000712424030549840350207113010150035115001c80c4c29901d039100c99180340600300d03200c40703d03101c0900000b0303e40c400790001d00c0c101484000300c05034650700e20944050104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 944944172 1250 944942922 944942953
    0x207021c02030f0703080406050a20070e06180c250605011e031203111b0c132d0b121b0118060c0203030f0309060a0e010203040221010b03 61
    0x45180040b4001e10424854140c030083c00107080044075800503032945000d042a100301c4060300032035489014000e161940821120310000010200001b4a0051841f00d180500b00c0a203400d014050a000381032280d2080b1602c801486915480f40c2103620031607440d0504510405884807440d5802050424a4010350400425070032a60498044d05000428a1034210115400d41034030312009000200c000300081c4024040d0308144154a0450403107414582c00004950900d0f2071100c0365075458100c0f01ca621910b00d0500c0302d0700c0c0401c403122810000c68018044414121b40d0201403001180506d280e510703502d0ba15a00801c1d09810003a0104140d50803605100e82d8910300d140c6158040b80384030401c0000c07540b14407030842d800d038413070303002c81040314540901900d4041e04014140d806004c10002d24840300844c4004500600c0360000400451412890301002c55480300b223a542c0b183d0040042c81b0240c0ea620700c10404001450f500c0d01a41c00c03400083c0d0f401401c1d580015a058043e4500c070b07850020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 944945422 1250 944944172 944944219
    0x1f0911090409022b140c181003020a060201150f1d1302060d06170a030818070b030705030136020306010e090106030219020703020315040302100501091d010218011101020702 76
    0x288905044400088112000c5444600c48090350341c00c82c2c1847c8021081a9280d800c4940100880b0b034070022642c2c80b5000304400913156000200543e444000b034022400760041403400400100300814813403800c00d2058407013070303201844000c00d1001110216450b000709400d07803c5410785c01011550b541c1c44404400001d061030340b1800c0036256103110301082c2d405007ca0040070b09135169407030700c9007541c0d2103484003a4081c60a40d0b009007403041a402041e0480c031381d0011406080700352a059200e40c984050712001c41d00c020384948200c81c481803040003003080c96008024081644001580303039501c2d1001215110b03941140141d1241009000203160380d01b40d802441c0060071040350b000e801c0940b0034280d9403040c4500c4000c1d0994031078045405c1d501c45d07260b040c5030450701c64030585d4800104807060b4015100c00f82c00403540c1d2640d03407078840c6901c4920544040d092070120300940c1810503214010048600300c0c65114140701808841c848054020b42c1103031a2598010f08000c40022a10246030102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 944946672 1250 944945422 944945509
    0x40b04030c0f09052e0801090b0406061508370504020a1715071b03110d0c0803060d020402040f030f17040e01060f090e1f091109040902 60
    0xa40c0c20b000c1c00320300b00c5844d00031544209a003024000b0344d8402c41d003c45090b07502404a00b00381030350340e58000c10300540a0255250035801002090001d0610341000401c031516270b404900403820303546c07591003955000302c0c0c034030b03031080d88520415a06030000c14080c050070041c5c0e5076a09030001d41c0c1c01090040300c0951241340190300070b9801420f001e8403070104500c858030030645403000c0c0c4c0c003248035007800308800800c10794001c50760300d81807003020025420303030a59030f10740c080450100e01c00514a8124007800c100d83e040c1c201880c03038602050310650322074040030702c0040e010a00800d00c000041040d512240c04403001000c5201400d4291030f50707818101861801c1c140308076903000060300c4002000c2a20801e0f40d095030180c0024150b50f918244c0b085d21028801080f00003400040a030000340c0300c4031103041074403c01062208e451107801d42009101140e0075070b04030001c841d24044c0304001c80901042904d408207070550700002d00030f07902e00004002c0b40403400400112000500119101442c00300608a01d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 944947922 1250 944946672 944946689
    0x120c010903030f020f09040207150204030c1d0f01060e030f0f0706031d070b0d060b0304061e1a0105090a0801060b071e0201050d09060f0c0e03070504062405040b04030c 74
    0x142030f850964a003030748650404607800c000306005030280c52809074001d00e91030b842a85d40380c018030300c00d420002c26604107510907104100203200412041c11418480f4101101000040c100f9141203d0441c3c98900103015802c10402d00c4070030381013691010810079207504c1c1600201e4600c01046004181d450f42107008fe00006801c054121141c203140e41d4840386600400d4016044003424030901c12003c1c0c209040750030034140c0719580010280d411000450003140500c80c0440c100d4055100040000c0070071780f103502402c2c174140c030b40c0001e001050445841c45109103005a6200860000a50040c1d00e0b904102100d529016001892a0001c40101007481c49058070b05451940e000184a0265038000c029000c600108a002c0d501e03941c650000044521a090002d03540c40c5030441c090456071000b00e400041800d00e01400e006142c1000070a0041c2004c4a050040601309122101140f461156003070310120841039400609010300140c070302a200c8104c0710f81c0c44503603d00306240e0105983c0f069000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 944949172 1250 944947922 944947931
    0x2030c1b0102280f020c09011a160b010e0112020307030212030714010c090b0424050403050f0105071e17060105040302100f2a020f01020f1212150102150702120c01090303 75
    0x126800070821090200707001f80b03021600da190444002d1a9044c82000c402807160420030b041c608411010f4640e0040d01681c4954030a60401d44001240441038202802190342c4180c240010b13500011100b050340e505444900081500440c1a841c43c056144010320620345c14161185140301503220000f07000b246d540b07429440355605040314161040d03000d00a1590300c02445403070980d000c161020310ba01071602c1c059290035902c0d200c5500300444c8101309010350351524180030040e64000610110f0064001c102c03849041003407005880140e014070b501301007561036000501e883c7e0190017568000d58000e0503400e490b00c51400c0050400c1101441c00c00420441c0e003040345030740324052100c58030610101c01404845807a800304410032903506a081d0440c410b1011046103500d0521201e014082c85039025500c0e50004008440100d100400103418401590401e0003903aa000520540c0c000191a001800762208541203060031000d02041c3c109180024501d1425201503110010180c060b580800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 944950422 1250 944949172 944949197
    0x210d0c2003090a141c0c1701020310081209010c0606050a030807140c1c060f021b010e010b030606010c3f081612060e090106061202030c1b010228 64
    0x2401140701000480d04860025462440e0440d82180d1700c4039035003c1d61401901c0ca996404501408420715100800e0765000310502138070903ca040000090101c12004c1c010381140801c0d0001c06005000d02c2c14100480c1905110500c0900d1340040d01034500500810501a12801c245103250312602c801c4036805106e01e00301550050100304450410300040000b41c108a83c400746640403848120b095031265616403441c45412000e1000b450b0030048081280c10510405080c50b084503c60041c07014540d0501c0c142c02e41070b680115040d54004802d080070414000c00d418041c4000780c0d1038101403107441e000625100c069484201d4403000061807030070b0005c1d41c1c00581d011900300300213840d0741e240401ea101d441c410081c0511098080300c0e0744a140084c080b581d0f61044016400203603810304075130b51351f0402070201a0f441030700d140034652440340c194910705001158180a00ca4084031b000c2c51004100c80d000750360001c2d01110150046441610f000c2102c0700075042c2c4210391207140750046609540c10300d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 944951672 1250 944950422 944950439
    0x120e0a05030307021605030a20030f0c0a050a15050c10091505130f081b0a0f26040b090604090c0305010503070f080a0206030901110a050705210d0c2003090a 69
    0x85086e640042c0c00303040c4080e042e50345d46001c0300c814040e04091301c040550040e0a6101003146021441140f8010180c680440017440b91504c0150012801408640000d0002090261240e191081c0d10314180d41c1d551005034500d42400c8581d6210300e0414140101141031040044558807001d44030002089580c54034a032148000c1c6c0b0345030300100f2070400d650a00d008680703884d01508032903000e8130207a91101e00c0c110420342400c06802c021180d010111003503c080c0404801c210451109090040e912a5a1902031080c81c0c0240c0c40b40e400c00040008603a40d107a02e0b45801d8600900281030103000501c2c0055000d03000d403900b4001c190091042040025079284400260030032140e001001d003030180466000d11445610090007a81c0940d258076001c10700790303183d10040043d40e00e00d0351120740710320561801a080114810403854802c00c8110015440b0384040c080b44e007100c00c40070000408080280003501d1130701c455400308a50045075040d070400303420040010101080308942800b0840c2d12460326 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 944952922 1250 944951672 944951713
    0x1140f01020d0c06110c0a1a0f1305070b0a110d1e0503060f060a0507030809060f0c13080d03091a13170f03040f05150601050a120e0a0503030702 64
    0x6860059100030203005219000d41e4901c1812030144001080b80c1e0400c1128141c2980500c0c40c280312648460004420300c00e100b8004106404400c40380400c1d41488500071240c01030191021100d40390384041001001401c200c80c034000c1000e01503858841400c4000540420100c3d007144000b40180840010214802e402d00310b500b000700008440407551001e000c44141d000107100301c2d0440668a42621103a465002904c4805110f030b489503500c0c2890300c2d00038441c5001902a0030150720500c20700c060b030380b9112800c2e5400421410000d03203403480c0101a414442c050380c000361242c061102030707401c41603040c1c02440da500c0c0150340b000307290045140d10000000c411607080000300300d401c00141c0090b00c806407200301094688040c078200654010b491596510a0360110b4001c0c1c04807100c102048400d021415510158a0042845151680001c4c20350722507056580e081210246808003d0840c0e64084a00314601e4012a5a581e140e40703400740d40d95200341d440401610441d80040c4201c0c43c1d1061 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 944954172 1250 944952922 944952949
    0xc120c020303010603110f032e0b0403060b031005090f0f070b030112021f030f0b0603060f040f06080a08030121050c060f0d02033103021e0a0b010e0114 67
    0x210302c0c40c3e18064049000b48000f20580410b1401003110340007240342140514019644c00364104a001c4110301c07071040041d03014821500a041c10321080100d50307504400c0e201141d0300010b02250b401091030001e03050078010b400c82d8000510b80010702654060004448119500c04005c0742c3c2ca0300c4121005555401c0207200300c88400b401000140038010200b07a500490510282041d00b032401c51014085020440808a000007036513208850507640d10f9009801052800355a042d01d5810428045105020b014900c1c50149469401302c004106055118100a03c1e0510a84e03ca410442c54000010342c420303c21034440007100d11041590742d0000701e1500d680303a4848024a411030005090040300e030843d40881c184802d09019100001c2418001548039040c0c5149114800702801d0a03800c061941400681e4200003003000d050001c0d800146000114001c400ba5200c511a1560840c0c901300740c2e500c0080c801c00c1e200c40000b4106801c000701034181e070302111052510f41852824413a1800241c01d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 944955422 1250 944954172 944954177
    0x409060f0f06230406170d18181127040608070609090e03041a09031c0905120c1503040506160512130602040b0403031d030616030f09060c120c 63
    0x700d600f44a01003c400710508101602c04120701e55542c00024058401407a0b459964001640d0709418950103010308850101d840d0300c8104041c01d08200240526078000d0030440a0f650f60307095007400c0140790940760b844104800e0780b201d150402d92070b04030140d0200c0409010f1414041d01081115020a58009aa810f5650307007156910349030700c440103009011003031003c80c04100008141c00c000c0c4004503c02545040c58a540c5001180c04c4c0351810004a814001c510703101c4d502d019506601000c03910884d10121045010170926000e85400c04c10400e510592000b0f01a45035208481d902000e0f520560003501555402e03903540c0b08090015450400110002c1e01c10840039030000d858103241c5402c02400d00318000100e00c1c3d035844500302d0388183c01c040c41541003c01c08000301036011010050740c41300c000781c2030081125170780420307944c8c0b078064014103009605444042c00d4511a81c8014055105908240301500342400c2c074100420542e007a4000007460484141448c10084c0101000c41c3d541d42d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 944956672 1250 944955422 944955449
    0xa020405010515030c220f0519141012062d06020d08070c0203060c0d111c110f0715050604050915060a08030d050a0e0a111e0409060f0f06 61
    0x40c2c68066155002d1000b000c3c5900719a5a02c1c022086c5980051000d070000a0b0443c5049040804200c4040a809100120700c4a504000c0c40226030440c20300c4103d010035246013015501c94102034511030300394124203898500c0d0080c0060200c1c0c3c40b400078044408004400c41142904008031241c3d41614041e1102581c0003a07c04400603101b244000c1d03000000d86000406000e407540081d0501c0b4040e07031114428000413481c94485202440b402c000c0b20582c8108524007403d02016401304c02c9018248800c1640d52590b00311440f0504003100c4c40305031500070880d941c404d14504450070710100000c1c1d0040903e0300307000035181e0426200c0c61380500000d800030911071460215103458490700519144d000303105803500250400082015050383c045810700802c9520307104107560b08540080120080136070100b82030801165154024070703051401a100321404a6843c0c80e00d400c3c0800e0b80c008a0381061808a904007841050340c0074162080c10214188141c0070009240002d5504a0003a0481440d03803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 944957922 1250 944956672 944956681
    0x7210c03021302041205010504120c050c12010e1014010b0403030e10090504020703080108282616030f08061804152f07110616140a02040501051503 65
    0x4200342400190401a003d46030540700c04211412441c10a03080f01c0d143e4440c02031000708602071508000c604c2141c0703814942c1d00f08075124190398403120020b1074002c141d005942c5c80343ca80d00390400c88884042c3c40032500d140c24607000500007842009505140040c0440010501c80114030454080769055920740b80444010020082000c020000d58000e2100c1910006155150b40c0003800129000c1e480391543e9600d0214510304140c064201e021001400009260900ca21901c03050503450f04a1090040c007169015030000107858105041c55118020804006041001c40c910f0311080c41380d92030700604ac582d01c6054400000948440d5440301500211007a0422110755281d8801c0c0103031205450400f07524080b0302240d490110103000c054002d1000e51200c80000312420202c401040c2007403601b5003e80702c110b000b80740700b10420312514002904040c1c180101c8030040030550441e0101c0b4600b100156007503595407504008034000c6041800016092820755940f14003414460202c0345107584 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 944959172 1250 944957922 944957929
    0x1709010f110109050706050c0f0f150405010e030f280e010c0213060905010f0e040f120e03010e0607030f02040b030403030c090e0106030903030e0105072a0b0907210c0302 75
    0x100c0303000d04a4a0340d41d401e24400424010080350b4020006501c40580c3c4a102242042c2028680c820403c54ac0c2d03c0504d0410030000d00180800d030715141e1a0000303145403245d02e007450151008100742452444042400d0f200085150001c000307182e0700a00900b100c00c081102c100ca142d182c100caa00c0800d01c01c920b0740c00954059403d800340d09100900100301240880c250f402160220b4010894040e66200140007c4011a41c0362010b002c03080c8056645240039514540401e030b42840040c10800c880d403103038002c18090f5211100e40c0d10020000d00a0703190003648a69940012588800000d06103107403220022500c0c400c035070a55203a4241d0034510313a2251800d501400d102c0d0341c040d0410403e9040010b8603030b01c4261107406803d180c1d80c040b0301c9540c5401c000301a030301d0031803107185036925001c01d1001e5590007450b030f21544e40d1403481d90b03010704020a03501000c512440c540a00008105020001c240704c1c00b25411003030f50ba030000740071407080d035102c43c10400c1e25881c40c0041500c4022141030000d0320b0f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 944960422 1250 944959172 944959187
    0x306150e09070203130b130605030c07081804020c0a02090c0405030a060b060417011b0905060702040e01020f0a09150203040b0313050102040911070c0b09030712050124031709010f 79
    0x10b007030044a1501c04002d0381500e60500300c0e07015145094000c03480082a585411800c401000c540c81c04500f10b040c190710b03100701445980c400a0801c00001488010110200d24207170b4149401041191074002c3c18141c25190240d18408034400c901c140b00084098103a001610181c9501800420310450540e0f2a500148800c00d440d550040c024030001071030484034043c48004902e808004140320000c0680340b00d6200c00c0f19940030034494200c2e4140002d0311900705690352940c04a1300420706500c102201402071040e409085d2403140000380d0540804e4015020b03400300da942d4209200380d82d030040301c201c1c3c40c0e010f980142c0d00341740310420210340000500307124141c00500900005103031994403030680040b6120754641e0500400046403207001d00c01c200a0030350042c9054034280e40750541850001e91641c1840c0110075018402c1000203090003001d5000d00d4054451020070003200100311602a0000190310044650381c00411101d5511031128059485a180c181c40741480e0203902603040d140312 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 944961672 1250 944960422 944960431
    0x918020c011b0f020601090209010f1b0c080a02010215040b0609040519031d0114160311060a0b1003060e0705070f0c0e0a0605030c031b0a0305011109010306150e09 72
    0x25900c402c1c41c4160a190b6200b02d00761411181c440b03007418900008040d05210f4164400c134201071042c0900400d40e608100f442403060002c0c034000b01c1c0c10100c2481001079090110014040401000d80455040030000e910840c0074000d07000c80c0c881008043e001e02804100700c03001006d10880c10080340e444d0412800a80e000351040060381c0780550070002080d030004030390200303034002035001045d841040301101d0300d00310001007845c0803082c107c0c1601c60807002c0c0c806e85080044103400c80c0762250a00d4800c1400b40d2803200c018081e606217081040e100b50140480b0002c0c10322030380c3c0000c045c4403014083c0c80f51300101d415074041c0d814281c1d640001542c40d90001c44c002e0300d02c6203d101c2c000001401480642d00502920b21040c070103400e101d407600c0122045c40c0c0203d80039501a0000c0c0026079000102c0ca10200200d002c050ba02040d41c0000c40c07010b034000d500080c003d600702541036220f01032a6010300501502070b03904000090b52050200c030fa18414580301c01c04908407003072045540c00c00603001c5511 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 944962922 1250 944961672 944961697
    0xf030b1003080c15010b120103030e060904110405040b0108040c0e220b0f0105030a110402091f0302040320090a05100f03080904050f0709090c090320030d091802 71
    0xd85559864500742ca0b40001001102d50300104401e0b52440d20b00504180900401c450040c1400c0e0100509200c107071041c003024041c07002d01480c13a9403ea44000855100c128050401d120035080050f0701001a00140525485582841044100da51282c1d0045124a42042015034160315049070447c2440b40601000f84000c1c840d5400c2014410291140c031000e1700c2003032105038074a0140805860fa15060b0400b503c01e420483c080f00102ea04040c40d01982a030403100103a46e104e000740001c010034401c150b011484020001e4400f005601a4081d100300c034010880201c0700241191020004000c0381c140940c4020ba250100d00c0c80c403542c0c6d010039401076100100c011b106807650a02c0495078100e910440362500001100c1d0018141400f40641101e41c5809401c80d0b800c100d0300251512409018440c05a55242801c004040c41840120000c41c0c10900040c100a05e06d458100343c0708880366414007a01c10404001d105900c140443c02c220343c0d52a480145104041c54104040d52040c0001404d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 944964028 1106 944962922 944962951
    0x130203040b10081605210f06010602010c03061503020d0f0e030a1b1e03140406050301080f0601050f0d1118060a12020907141204050f0c0a0f030b 64
    0x94903422120044455450311019400b5040f07042c04086c0391240441002e04040301095813030507113900394004d0110a03801003003901502d455100d2401002500403200210340c0c800c1c1d000d0217603541202c501144007018044040280d604058131541a80c200080c1d210301c194210664034001148080222041e00154840c4800200011005000500701c41001001c06115200b03e400000200b04e01a440c0c0341c544d4801800d0f60001d00407040c0c28895002e05460707000c00082c800381202c100804030480440341005019054481c0b0740111034034240ca07051780106507070f2054840142e403c1100d00001500d042c00801c4603150685d0b21003860610002c60b0301d00580c5407004015401403460925442c0c500700030200e040e882c4500b00804441104480901040000108002803050b202608941c6403003034003410060321500e40d200e4445064401c6d8400c01c0002c8840542a40c007040d8a40c0440 = true := by decide +kernel

theorem cover : BRFrame.Cov 944784172 944964028 := by
  have h0 := BRFrame.cov_init 944784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 944784172 ≤ n) (h2 : n < 944964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
