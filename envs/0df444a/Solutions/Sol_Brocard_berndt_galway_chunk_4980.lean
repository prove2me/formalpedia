-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4980
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:21:09.847276+00:00
-- url     : https://prove2.me/submissions/2e6eb5c6-9b24-4002-841c-43f12f9f8f16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 895503597 ≤ n < 895683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 895504847 1250 895503597 895503613
    0x130312081306020c0705180403030e0c18090a020910060f0e150304060929060913080a030204180b040b0301090c090b060d061215060305030f0304150c050417 69
    0x41c0340d28075640440e480800940c903014911040c0b4a001003a600150f80410380f200c1101c1c3e09a044281217000340c2c026038090000450220406544102c41070356660030189150322121280b2051000541000d545803d42e42c001c9507070b8000600f100e606540c4001d480d60740c000100101c60300420b684500ca145c41c241303409084500800185480e2040c003580068110002c00901040000d92165031f40a078000d400e0951903202c18a0449031000043d4403001c0618480040707a680d180107851707070348544601d82e00700c90400c405c0c0e03942e540c1c1e9030848240401850307003d20000c5120540032641510089c0500342c0091401c0c40d1004210544103900d0303403603009074075040341c181c007080018443c0790654035001400700b242e88c0000c022901c54800c407050500c2080c90810049954040944507219443c040e14420148503140107402040301c0701440003c0081e80204084926805901c01844e80a4043d40071411818000080a010f4621410708500000d1000905100c140d00300915003c102400200400082e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 895506097 1250 895504847 895504861
    0x110703030213150f0e12010f1e0e060411130218150a0206010b0a020f0f03030a050903040b0d0b01030603140d110111030c07060e1609061409070c061113031208 70
    0x107807102c1a0100e0801c00c120300c80301c5c06500d5804080c1640c10341007000b003015180003002c56004114096050050647e54980c00c1804801c9000e905076030b0084202410007174a40c0c0d6200c542c3c4031741d200c0000d0b4000200002c9a40550039510107031800d42100e00042148a5503502041324041d0540e12031081d03110140b1420881139400200350341501d2114661581c0c0707000d049002c0c0d14160000c8908030041c40340021004807120040045e5010b441500d000307024a440340002c1c2c6403030340a207001d8003500c4602400342003403400d90394200b00381642040c1800a48503459440f4100000c06007900c4503000d03030181f0f120039403c65101c01000160040c5200801c2440c65803402017a01c0d00c00501007007400070012440328140180c1d03904c072100d81c2400c2e500b11101071750041031600880001e8411803456130b103885400510300000c100c111001d0403001f08014540c0d5260401a100c0d4104800107448040c0d9520340c80207182c2da1800240b103009841110101400d141d46400640300c0c1c980c005000c2000316900a1040c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 895507347 1250 895506097 895506107
    0x2100203070215010f18111209190507051e090f0406020d05152d211e0c01030c080a0e1f090212010b0a030803190501150e031b0f0411070303021315 65
    0x80c200d80d803234550340c0035218100380c40d24010000c0d207070030b540540100146003004000600c04007201e400b5600b444e03105030058080c150107074844504a400c2220344c400200307001100341a00b680244070f0b400c01410300540412100485004a40d6074032206104135031604a45804444440145403040c00600400d01d01408052020074121505016003900c018030314003064100c41400b1480c40003821600300454461018119078603c0d00140070601420507042c0e2994404d00846240d180b135a10740010949400c6c45840c010203441e0456600d43c050510322406031282c9030a03d80341c50b41c0c8580081400c507068010003080850345881d024050307140c50840003581d1102c599100071680c222141d552290354048034951754082c603641034125189450000704031360361207030445c0100e40d915540d80c254140545082c15900c4081d141c40482c41140003001c0d0403e45081031040d8801c1740301074008151200c50044100b515085004200e020035001302d02440704e08408440d10000740000125a0142d2401c0341c0b010b02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 895508597 1250 895507347 895507357
    0x60b0a11011a1e0409081303140109051e0109020907020102042607060e01050c0a0b16110703020402091201050406060e09060106050304060f0b0303030406060905130302100203070215010f1811 84
    0xc0725143c2d095070701c1d060f40d40e0b54001070f0229044031005a548080c0d084c281410119070000700c1d2a400c03078620180c030ba840c05101e60002c00f940240200780101410787c0e100100700811012940540d250700c078110043c2c941102007070142904d500090303100ca080200c0005031501004151741d40441c0c6820329003401400203604011515181020071a100c00c1d2401294144140a148001c42c4101c40e0900c0401442c0004944201170280e030a1000c00e41c01e400032181500e4a5541961035441030a0600c007601d00f035402800003e200600d100c1c40c41555958442c25100c00712015031302c8694494003002803100c0009400d50009484015014942c10014041c04902010304068129541c41541d0850000366070b2100010581c0101280e0700d0745020728151020317080c2d90203404425820200882c100c82c0c90404401001540758000e000e1107141d000c900c800035000284118110300c00c046070024110500c041481c003030a03c2852049800e41404144603030b80e14007800c4000f0301403800c41c51124020100b01a66 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 895509847 1250 895508597 895508629
    0x60115080a0c090e0c04140a030b060f0a08100203041203060b03180c09090f0d03110a080a060e0403020d0e09040206071101031410050a08070f06080901060b0a11011a 73
    0x8215082110860b1400141d40042c0003807001413050005080d81c0401400445007118803044c1c2000a210070700c68a042c007172200505000c00800403c40a1512010400d6102400743c40c4844040da50441e10b0f181c8040d6686160901ea400030070b20040c0b100510f0084100c0081b42014002180740880b600c81505c40240812142c0c4141100088079040a00020a408100800309000c505110a115844945048811006205814519101a0003802220b10640742a00c813281840350000050301c511380b0003405441c4c007a644150114550450f04046c900850080c1d0060038640300d200d4010300039581035000e085c4142c088030304000050352038000311500c891780410880c000000041c010b8000d058252851120f07400c016040014100400310390200311038044518698103540d503401039031114800d00403040b80f02140a000e109950103010869045203003100000f95060b075840d544001500101c0d80c00c0000390000d00804101c2c8024090314008625042e8403400729405100090040110310346e5074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 895511097 1250 895509847 895509851
    0xc02100e0a1a03012c0f061e1c020105130e160504080a022707050d06050d080f03220f1a07090303031a04090506040210021203071407140c0102060115080a 68
    0x1981107a01c074181d4550156102c0e172241101420030b0300d5074020401c1d00303c1d89180600d9080da2401c40400b14403080000f0a01d000d441048410b502e040c114611074400300c0c0c05e078107214041020a1b1340c1c0124145103401420440e45144107801c200c1d544500c504494078404042000610080c07048460109841030000c1d030403030b01000b812422080c41c0c8292812460700c0a8418084020031114680040040130f00c48403c000c200b081d41d80311030030030070092141c0b14083c25022040c070100c2c42c1015040010b641100b40c10b0003034a41107541d07502000b010801a4821a0600076200b036140c100221410481184d1109881c103030100c3c940300c4d01c01403d0300c000d0f210240406232034400301c040a811884090f4541038000e402030000341c540d41000741d5109001da408078081d004a00c20001c11500c00b042d040c00f4203408080d66440e40e110401c00b2961045101502c0b8403100007044a035000035050b4000400d1501c002d800340401e0961740c80007a0408605900032003441c0b24030707000078500d268844100d41d4801214400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 895512347 1250 895511097 895511129
    0x108030a0318051f0f1406040b01020703080702150717120a05060d03120e010c1e0201062405042705010b040b0f1308070303020a06061413020a0c02100e0a1a0301 71
    0x22000113007001075002c0440529011b0071042c1c0c45410000203100c0c05040d60180040c00100c001240c3e1045c503484003806560080c0400401460070148103458070300d82080c44c40c204290f40c3c0700c04050304062070091207088030001d007030006c0c114190b04140d880300c580801040740349410400700f5050f4001c04c00042c1006104d11821003451031650108a2000c1c0810007044103100092007e44040c1d940341c0d09120110151000e03140b000e105001d10000d40781c0000610742103038a050300c00803010103004a0102404820b104c0802c0140b05c044032582c41b5a00d03814403c1c1d681200d009004121007042c3c00820148804001c00c3c804010000100c48200045041d01d65513080400603e990100c1d00b0340040f1440e010f094000001d0503800210f6421490240c07000300202e55076a45100c05100c1c07003000450300032009140c01e181c0c107009079000c0c000004450030000c01c480791070350014039840f91004610b004100a1107458045042843c00003018161000304c0300b581c43c80f11940440980014498960b140c500004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 895513597 1250 895512347 895512403
    0xb0309030f1b0f030d1505010f27060e09100501050702190305061015080c0f0904060b0d2004050f090403031401090f0612020303070b040f05030a03050a0506040b0f04020904090b0108030a031805 85
    0x80790540c2c001449144410bd1319030350300800f845554802d062044000c5404180c03100141000c0714102c940c140c6803580340035142d509118003070460140d004090100c408000010490500903141b0030b81148403610390b4941000b903010252840c00c810780041011510400030360407802011111007141d0000a40d440e0b0251000040c0601616040312081000104810380c80705050303080040e04a0904441d03d1621f0040003807035519014500c102039020105a0301044281071503600140c0040c0a8500440c0b002c002202d0040100c400ba444510040d0381e401100700c0050091041c9405858440100c1c1d1202c080307600080d80d079000d81500601350a031041c01090400c40e004107030501365581708041d25150501004003a0082104071181c21748035090400040d55403400d8031a071031410710010315068100050405010094000c004120b402035500d4040d000807682e940c19441c020b01400004560340c5820310002130aa4080b04500c1c0601244500d042000681c00318101c0719020314075014260090444c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 895514847 1250 895513597 895513637
    0x313060f0f09140d02030307060c030c0c0c060305070e031f0f09020d08180d050106060212040302091902090303040f03021810060525030201090302070b0309030f1b0f030d1505010f 79
    0x150029411f10000a01e4020070005401049821006803000c20100707541c40c009440c0400e91600081031240740041c1446200d0180d44010b8110109190605c54140c840010030320300440580d0010031030500c501425000e25960180c580e842100e07040500640419a0200e5aa4003840d400240001c0022071a0440c4042404499280c03d00052001d01c0d10a181c2c28250700a20042c003a10005014a4054044140c24201203a003225805045a0320700e0365041591105007001c0381240e13202c4c5d17400300003583c3c0580d4104041c00141412400d035009240c518810050880301780740482c14040e41c21002c1142403508102124119030090600c265242440c0504480e0101c114191844032014034260000b81541507100f9100d40d03200c1e4082703540603900c1d04902e0040c1e0000720751400301640304001d9000544440000303000c482e00e0140e03030a003801704620f81c61414814040901c20090f44086141c082c0c10000740210340155480394100c06035241002c1c002800305090080c00707010b1206295482e00e010020f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 895516097 1250 895514847 895514869
    0x111071104141f0902032502070b03100905060a081905032b0c08190c021002040b1c0e0312041410020301050427020907050403050313060f0f0914 64
    0x60300d12010510700000710743d0403c05a209070303801c2401d900c900401c11602030b1080301c2c060381011a0380844406814401002410030031482c0086001d040d2001850f0003512020b50b0048030036031000c0c03102c3c1e81008010340448a00426282c030038802ca1100700100b4002003145014600e903030001c003000315080e06045180d03100c0c803000181e01c0100c40803440e803c0d2045114607100703079030706540c14060601001c03421211a801a40c13503d41d0b1002e64203152005042c507508c100481c03945401034071071120010200f101203802c02e50001c4030f2002c1c00a4141056900710b00245144009104200b01980c210b80040390790b03004180c2d00030b411541440104060084003544500580c0d82481141d01d003218400d02c0001a4200b032007110b0241e0300b40b00c402e582d10710560071015200c280d03001c0c19211140c3c0355001c00c2b80c07005001d0300d01024010104400310101c0d105100030b00e0711960240b1503004503480c20304010480d0b000a8500e204000252a0b8000c916910131114022116071208020410350305c180024801140c2d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 895517347 1250 895516097 895516121
    0x110112060b030c2a2103061302130b1803010e0a0f0b0a09060c0905090709050627120c0306060d050c0103110f0c0601090f0504081623030d0501080111071104 69
    0x103018150a030680000e40b46008144100307172020301300070f1980410840d000a0390b66652240340501d40082003840303940a0101d040c5d5078420f140d00745a07522100009603015004501003405188100b84c20ba003800d005485900c944040180031540040d15015100c62001000820150291004c07401c1da00f202d4010b904071a800001c00c0000301c0c5072041c0941400d006101e20740c0103070001000115000d0003041c4030811104050500d91030301240c840780b029070007100d18100c101180350722041001606c0c0c01e180301d8100301510008150120f00ca2081502d8000014016489829030b06541c0d0b00041000c00c3c0c4034409042801d000c107000341e41c941c601c1618064034000c034544a4002c15072006186000910303d0403030340c03010300800c0141e034210081000d4407001c0305c02a041380340801406040003542410003082034054544001104591740c51803041c1c040c9100200110f038808110104849114400c080c01011468000c00465084144980e0f02c2d0150803000340c481307109041780c1215502e0740c6d0410160030b82 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 895518597 1250 895517347 895517407
    0xd061a0d1a3403060b04080304121a010305100501080a120c0c051e01080903130b030c0d02070f02100e0a150c0b1303020f07050108060616050a110112060b030c 70
    0x80c100314030302ca42d4002051400040c3c01d000e000112809a10b0446094800740d1001c1d510b0309042148030360000c2003200c002c6402d2040346080d190094112107030b50b030181d4880c9005d40074400350080d45005807081138201030420781100e4113020019100d0040058981c0c0d20b400c10307a400761503605001110ba2070366406070b50001f00e15000c50120a004103030b040c010200c240c071001c0d219247c07502c000390f0341e000304c2c402d100408100550a00c5142000700155a10030203190101e03140c080c00d21941011780e082040704a90041d42c412130380d030445c501301030b1408040c940d514240c0c1d04c3c4d202c03030000104002c22502c03918072000281c40c1c55132a154810103182e00e0f140d8001c0400c10b014100088420380c0101703032510a80060207040618480c011010641c0400c0761016500c0c0030054480108100160b800301d0136052108202c040980003341080c42030f04030140c064502908442402c0f0005008200070482680509180c080f0502508035030900b601c1c0c22801c40f0311040d490ba00840c0d88100640c100f000d00c011000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 895519847 1250 895518597 895518661
    0x702100c02090f090d050c06041e08070f03030c051206040e010f02030f04050c0628030605090a09021507020310090201110601080616050301050603180c0d061a0d1a 72
    0x4407460305498003c4da003076401c4512101d2a2441200d490084100c190745a0b040307600840d000c1001a203220901b04d6407a00040e140980c2c0b5918024a680030080c1100d902d80c0c40c14000e001e054161080c070b5010009801e00e949040503038070440f17040001c014240c6125035601d400c0b005041100354000c20107904920303000c544c0d0b800d0183c040d1080c03610407076088815100c0d07d0f00c441d05505000094841082e080c41161482d162001e1500004030200e0000104140e070318a0005041ea540304c440c1d6010b5460600001001c03250790042c8800c03014200000e01020100704010001a18000340c039900090002e031000641c0d008a10040b6040758400060042c0e500c512000480d000302d02154041c01012400804228528044000e0701c4602091068660000040c80003a14128881c0c42d051030b824508400e849202c50448005400350400d0a015601e8170f03034441321042c0350940c3c05840b1440315000c980040c642031030356481c00a80c12402192404041c0c010011529241e11601031090011072407001035481 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 895521097 1250 895519847 895519861
    0x1d0c130f0f0602010903020a1e06050406021218070e040f020604030506160c021e04060e07020a0312060e04031419050702130606090b1b071e0f0501050702100c0209 72
    0x303480350701416400401d100320010b803890052152000d01c50385500600600f4099840e003215a80401c150507003424024103004d00003c035a442218442d0340b180c50010f03100c0310074414030310288100511010000e240c2d9429003100807000208074044500c10201c0c0c0100c7e688603e0200102c000b02030000750440c90110300402002400b04030603205c0e141c0d240ca041c2c88104007103c115010500c50790f001e904000540c140803d2582c0310360440d6038900c4007a00100744150703951480a0b010382d080b40d03441d0050f08400581820940d114030409030481d08114148211802c0084038881c8200242c80107003400803a401614100100c0750944140d1031000c8010703c42a2003040019046034040c0500300d103d03545080002019100e1440b50000f078910f41c2d503502e6100c40c14030740703908207030740c0200441d640a461445081410003820000c050141140b81f1210100340c0b0200349001d485480b5070004030000d20896014426a41d108083c0d404280c0c04440940c880d14109105035241d4605450284d0030000000400803d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 895522347 1250 895521097 895521119
    0x1f0e2a0a02060f0a1107141e330112030c0803100e130f0215070c030c150203040b0f09040b030a030e123c06010602070807050405011d0c13 61
    0x441c12a00c0510561556650134940c2210354500402c908004244034030804618405180d40403590030b2001ca41d0b00b00c11101c02c2c4583e800001d41c0140e4141d00c0382110030756200e0b4030500c030b00780201c0340d007003598504050807804003500c5014004d01e000c1d211040d61000c241849aa007903901c043c1c1003005560359040011811a45411038000c51003400705100101d82c103801d8401c085030009070005040c60b00e1a00315800c00007425070f140410304008101707010540205141e41901030007540304080401e1443d01d050500550940e00810080541d002480b00308500d58442003110104801c0c542c0155403104c1c1c4500103001031552400d03c9070148514452501010323000040e407001d2490465840396240044c00b2955602e01141c107108030704e220f418451441c03d201e000449030702429051040f1424200300e091440ca03100c0c00344d000000607031114600301304001c81840344802030708094806000c00c0d818440a0060264031000d44445610100c0015412103002c000b170701d8600c00401c0f034400c1503994aa000040d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 895523597 1250 895522347 895522351
    0x80c10020a1e020907030f06170303130606090e010b10080622140c2205031e07120b0703060602010614190b0f04060305310c150302031f0e2a0a0206 65
    0x10541e8a0b041c0c01086400c14200d01211100656000b1442c42e0b3314100300190f5041c9441d404c07101e480d2107a10104410740d90340181e1100211074400014000440e10401c15800c0b5402c5008041c8501007045c0006500c40d5815072050300c84a40b42d035000602409581d10003000c42d40950629504580c0a10880c048050018500240220ac070104148905003102c515200c03a0b103d840d0f80b591000940310610324020301606154440941669103d942d01e007040310283c076040d101212610406010010215003500c1040054503040c0f00030042c03141400441140407050588840c07140c41c25000700120307290342c050008040d15254107465110400001d190881e41c1180c068400400d00f42400502c01342c072500c004644000700d501c9455a550005036880c48081c030b0030078080da5a5880440d0100ba40d401605400c0c065102c0c55800590724a04941d40e1000113111440c21408800340f51801c01804500702c00c0690044070344203144010354500900c40101102015034450074000c040b40301c2c1c0328140c021030107034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 895524847 1250 895523597 895523621
    0x1303180311090a1401050d03200721120302070f1403210c07060e071a07060c020d020a2a0b07110901231305040606080c10020a1e02090703 61
    0xd2152144291030302504c414400c0b510520010000410452915a0024401038003a007460411034410010152100105030700407040c507801090100101c078103c0c0c8401c2c0381c4580c9030700700c120400401d03a20046880c5001e002e110825802140d05020300203031016840344543c1c00180d1f45111402d0004554481d0003a8080025120b032300748450b403045814034401449040c0000629140c119580d4403071004004008001c2514450342c0130201700b103030350080303c4044480c8003600c3c6601d4034003d0ae8184143d0701840d1900e801c541040380c64202443d00024410301084d840a600481f40710a01c0c200d0b0101e0b0341d0540401d280c2505c00c40c00140495802d802440d02a00030102c101044440342d0078088000b03800e120b1041803155040c0310307101c0d40d181da40300c900c000b51000b09042550070100003c0c2050355001d88007510480d035036a4081002480422440e0b0410b401500d0281c0901080900a511500c4050740609032400400f42d0f0840740482d08002c2d00c6c420b40c010150001d90400110050080884003890 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 895526097 1250 895524847 895524859
    0xb030319030b0d030e131e0609060902091c060b03030d0207020907020115091a090702010c09081b04050612031201150c020a0b09040b03010e0d0311030405061303180311 74
    0xa03060b02c0c2003551240d61090382549921400380c1807282886106d507a440340c0c280080e942d0b0080002503000c0c1d000c40308580d413120000030401c40d00300082201201c030743e0b51010760700e1032040240c0f902e90380700c0d1010180807101600ea640c0c80d80480742800300c0640801100582d00d0b0000051070404420b544c0d021b0080c003030003983c800c04d41d5502c5030420b078200c9144200d148502044d1a804010319441c6400806030000c10305c04580c030f0000b052020443c121000da501e040540d4440418501895024002d100100f1540004140081c0c085070450700325144486864040c0351a080040c00c2c949500c1520400580144100c95540b004428946040b440030f01403610b0240700f2080c5441144e128494180380b00b50001c242454085c50503012106541c40020540e42003a1141071500081c4c0c0c00f071189409003044003001e07040010703502500508846408841201111040c810720010903c0003a0181d445050520b946480c0c180c182070a40310459034001030260404a000c02000300300c80341c0b1401d0340c42042503c00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 895527347 1250 895526097 895526111
    0x201060810061e1d090703050607050409051005010e0120060f060a060509011e0c0f050d030b01051e0a0527010801050d0b0403031a0612061f020606040f0b03031903 72
    0x8000c02d0120744280c0350304d9084d41800284e190400440c05800103003020464072015640d5949074103007003048070b180000ca6808681080424418000c0c241e00040c1424000a510706290010748000e040c0801ca504014101a00c844000c000c03010f0030281202c10401c0321840d05e0020344041644178101c0b4001d006003045500020190300a90564588600c16110407030f006903040802c0c10500c5e003900e80403041002c001d41d00340c04206c1000820546030301135409000c0c40c0f440d40030050305030348503126410304104040248146c00c0c0e582e40501c1e9a44408280b03601d42c1e030f1300c1400b0100c03030f28010588c80a280c1450881c1c5c203600c94000805140e0000303400e880e203103040c1ea83c030420027401c40010381d00601103c4030b00c0005000644a40e10025550428192404052031200003084464005202c14600da241000901903d0715211000d20017044082d81e1036580e1502e94500203482d40006803c0c0b60260b601c404170f5196051113a000304400160280440740c6800320903006003450842260038101003403030142 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 895528597 1250 895527347 895527389
    0x80309010f17010501080a091a040209011d04080307140c03070c050d0803043e03010b030d050414040204090c020c19050d0b062b050c0d150b01020106081006 69
    0xb0720030515140c01012220b0f60329060054401803401000c1c00d0150b903460710140e0000742c0c10103541d100000b43e2040329186103400c3c4107000480c00103800c42c0312800312100740300500030303001d1110541c4594840141c58580d00d03a400c0684001012207910700200b0700208500803407020000150600602035000800c074155508280314a040006d00041c0c42642e0800006000c0b90212152100140d1802c0700302e442c507020300410409050000310010404019180070802502c0d00340200919030300e08034003801d140005080d01405621591081107602041c01a45004540d580d07410745005100103031040c0319120010600940712031303100c00c20600c0707540d8000d83c07210f000396030040c3e420070345001505003c103454154580d00740c03404004101c9507201c000b241c003001e84400c004107030501e00d0708001d541400f084420310f005400c2580b07000703429004a060800c5000402c1d210108400c2c80354000200041d01d00140c40102e001d006607411249080c0301c0c1004c030700c59004003a80304108503580389039140d0350526000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 895529847 1250 895528597 895528607
    0x3080c12010302040209010c23070b092d030a0b1603060510050c010227010224040b090f0d110d030e0303010e1e190c0516080f04080304080309010f 65
    0x340e100901034800d0001071005081c242d0081c400301c40141130485001c0799030f55880c00d10085908002c078245d0310300d50011005120402c182d40103810403c540d50b091852200c08030f00c1f0404020305d0303041030000558080c10340007020420440c003940c0c0603003915030122090804d03048600b000c0d91a03809580108001d440118444d21601e000d9900051004011000345071049601e44c10205a245003035500b00410f984d5403006400964000f2190900743c2070740300c0118000b90401c40b0755081d400c2081c0030250001400482200007560190340400d88100a40307071800c91920b44000c4e200c5000c0c0da44a5a40090750541c1c02040352260411900110340c1d503900d240c0350860544005048894082d40244014820344a15410f404e5214000442400c84009090340e00f5941c101d0a6450a01c2142481140340c1014003d0040055080b281e0604030b2501c16444900f104001407107102070492040807481d44850311b00b010454000341505000c41e516a92120a8503403294050700c4020f02151040d50014442e500074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 895531097 1250 895529847 895529857
    0x200c01150501080601091a0c25120f08031504021c0c09050306011401020c031207020316080303270313180501080706121506051305030303090a0f15110703080c 70
    0x46c0d403240e504500e00b1a10100c1c1349030b9420f01001441082c00b801d19070b001c0400ca1954500a64206400301c0f01c4840140c0003508481d400a8032145407001c18007021610341b07a5208991580100b14a580e942c50009241c02800c40381c0c0840d50050000642003041c0c244128018a0300c500c0484c200105003000c0e50590f0111210310032107030107402c5900100314086144410407602c18060058413043c2440c0c400013800c00c0c507180821035141c00042400010740c28200034048091032060f0b08032200905000a0725564040184a0b1240d00002c08210300e00d4110501c040540f46985022641c940250310000f480c2515a4002d1031604e1080700800350303138170b00503008081c122403079203000d81685400c000007214100000103e0506984d210b825103c02151300103080b00c0104501ea0b600c039118114a16804684501588010300c2035205100b40000c503800481d195031042d60140181e001c5246074a82003100403403801e54806007a1034264030801c02e403c0c6100038a0001d20a40d100601a51002e002ca00c5601503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 895532347 1250 895531097 895531099
    0x7020a0e0f1f120b0615071209050d0c0e07030b130905060604050c090907050712030507020105060a060206060415150c1a01030308040231150f0810200c011505010806 73
    0x84500200800c0448144640205e4040c18586128014001109440c0d0040780c04813540c0f19100307492110540d2040700c070340191900319441746103d00c40c0e81303c04000c014680a44038246103040041185240a82d1004449020203801c1c0d0b1540e80000201c00010084040103407a00e01880001075228a014410745108544400c245070800c0100070038000d03a45801001081400410031083e0040340c00d000c685800c0003126500460141b40c200c0c0700a0a40c5d0300608020300410200001740440d54022807410303403040041e2070014084140c0302d80c1014103a042d40c0002c40d08003544c0034ac165046c1e4040c5295400302d01440c2d48055410096100b40c140e18800d20016000030130b0880483c0041c41c0c4542402c5051103401501c080e4151707094060384034041c80b0060110440d545481008202850070103000042c1883c0558209941c80d106a490b1222442045481d02913600c5a00e02c40000b51311040b01c540310510308100ba03c982d042c114850080c80c2506590b500340088a50001c0c1c190711900d42d00c1d200341d030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 895533597 1250 895532347 895532369
    0xf01050715020a1704060506010306081603060b030c0616033908090910050108070c08090423010311090a0c20012301030b0a0b1507020a0e0f1f 63
    0x100d407020078000b5041540c2c40410000c100c02800100f03568603d44034000d6025a400145904040001504440315a40903100941008101c12511580791800000300d0b50804030108075200003c0001e414900d01c20a400e038054408038260400d0300c45810314900c100d04c02d4840a1074400000042681c010604140013030208012031402c1d02d00107002c80300003a05100d51100b0742400c13814400a401d60301c1c115480503049045400801c442e45c1d00006854100c4c6103424100d48003c1a901c426101d8441d400a41e4015910b0324240342191905d400f81c003007140b500c0705914640f542c40e80b40c108501480c2520380340c401c20307d42c004111070311500d100d4505030b5009901c0380712510700041120340c8049200d0710001032956894030a000e201e003075220b00e00514075041142404660640c075040c040c120000c0d0051308114078100006156840b56218124120329110203140c40c2e000302c0c030004019180c0d507003103910034550020074003d1800b280084030b40100d90036080401c0b000000c818280c0080d6523849101c121b24 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 895534847 1250 895533597 895533623
    0x4020906040b0f070804140307060315050108101a0d05070e011b11060c0709110a0e01052b0203090f0f0714040e0304030b040201200606130e0a0c050f010507 69
    0x8048401070040c900f80b558000c2c02c1c0f401d1a10707030000c0c0750001c0c0e12208a084481200400c680703020f101150181603142002c0190f0751030440765421000c980c1c000c903814060524040780750300b061282240000d00c003c0d000030040c05d098154111b0036401032101c0c1da900509040114580d1030040000d55025801a50365801e039420b6100c1d00e00100700043c40a40c0c40618481c80201d643c1c4490000b0003005222100428059207003202e05412100f01d50346402c803602c0c00b44569010306520120340300100d00c0929002c1d854036904181e0740c06c510300e00c60311340b8042d811050408c00130186a030065880b50910505480c0c000e4004400c581d2035000c0800e260381c00e40c0201c0410301c4103180003080303103202080242c00000c541c01e01c40b500c240341d64001d42003a901082010100030441d07034002c22141c0886c0c00c50070b001c4a89c0000e41e9030140d440c5c2021b0059441201c210b640c0750000c109581c400f042004400003290b408400a00f0705031003605d03040c000e8a01903622005042481c0d4003507001c4554443d0b0008a0356502 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 895536097 1250 895534847 895534859
    0x7050a112205100b0403020303043c1d091f1d060a110a0507030f0c05011508210316020a021905131109090901060f08060907050402090604 61
    0x14114100c02540c021288000030398440322521030030001c07101e50040041d00e4148000022009101548503003440c0078100310030300044e14040251021a0700d40e5003c61900070035003549080200700c0c1d910041c0074080340319010180e0a82005000c040301d40400107200c1c03019101c401c000c01c1c1c00085520b07644a40c002c000c1f80d4026284564468511000c010b4001015080281100c81980d940610b085960707001c9000d0040d003200901c555031841d0769800c546460561440c0c0050f125025890018080c022455000c004c0b8074040e41c91041910b52090003000040c40d040f541d00300f42030060180201f540304800c809541e0040307040e070700f000c01030140003618119070314030140c41040780c41011601c085014141071400141ca441e2104d040200f072020038003291505003420302c03075007243d00005d2003581800d01d9840d400305000c410842d03502c68810b8401d18210380d102e1081602502c1d80307a10403108455921000611080080388081c09030101030290b44c551030350340702044141d014404915a10400c100801c02032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 895537347 1250 895536097 895536113
    0x50316140405040204060203040e01050d0203060c0d0605061c1505010c15090605070815060306011704110627030106080d05030411130b010f0306061209030c020603040501061a07050a 80
    0x3401030030310000d107000c0c0c640001ca0142c3c0c00c2940302102507400408d0038403e00d202400e007140900001d0307420f80d40780386031034001a5450300040c0240654440c0001c9a602d0811550801c1d0b0290501410f851380c0e80310301b040b80700d6201d40706007010a075440c6010342491401c080040c1780c2e000c68030f050307560550301a0940c0795030483c1035608134280d400c10717910000e03500000c0890007003d1280078a5280c004440c64090f44028000f054002144e2044070200100034141e03030400ca9280000807142c4200c070140c0c0c2c0e58504850298001401143c0c003a501040355580703510031580b88040c0000e4054000150740b880c00078117003600c0c0781e8003415401c1c0c0c04c401c00d00744000d031180f4051640580a10711030030024003004041605100c00145042440340c45040b8000c1d41d5070011000b01c0038038400e260800c5400d1400c1c0c801403140c1090003169101c9501c86000d41d003494842d46021030980e8008000c0c566034201890118000d200510408581c1120003070a00c2404034004152126203400101070044d1000c42e5a034403074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 895538597 1250 895537347 895537367
    0x109050f16050d0f05131502040b030a0b010c06090804170703020d0201030b01090f060503060a0e0910020a05070c0b0d110f030f07091d1008160905061c06050a0c050316 74
    0x303901c2c0e584070b4454003d1180c3c0d0141d035004030002c0e42c0711b480842a40c00d14011481132607404030030744c600400c0700b0001160000d00f00c80d4844103825001800c010034400481e80c81420b183c6c0500000d0420008000b4404148004c008031480d520741941c08000240a06851700400d00c00698020114000303a00594001d802055070050149481030f00035407121400030b901f021940001d000240040100107042c02e0054480700a8007486144061901c1c080d042c5036544c809550420400f10b801043d410074250081c010740d20307101e51040c001c1021584070325001c20303150050030f10038444504024640600d200c41008607201c841440b0600d503e143d68100c20304206880107040030040100b01d0f6000a0031089003141d40c617946211900c51001410031500740440007545030042c06041d00030540114407080d9114840f02181d42c1400041420f54503100004e2142e4100c040d500c0038506011a00f10410200394003041c0b1403280b07264200110f400d000340071103e501048030310f40c50700528070010601c0c142c09020205 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 895539847 1250 895538597 895538617
    0x90b030318060418060503010c03020306031e01110d051e220512031f0609060c0311012c011b14090307170706020715020a1205090301140109050f1605 66
    0x10b01e031684c3c4100c01c0c0e444c0804e5202e80300748250344042c18403184c0f9080c00750950b401628a020340c1581400f00009840380707100c24840c01c0c1c1083c0e514084502103030030b4029110312150401c00345c2e2180c0c4201342c11006010101c4646c4d6001c001e100d113450b51040b80104040c010903490359928586883e410b918841c4a0380c0070b00079111807190350072321002e08200d007004602c034200800741d03030080035a002050900440b290300140e0502ca1700c003609101255000c6080345510790076141070300c1001110346415004202c0d10445800d2a409147c035403642d00301001d903c1c2141c1341c0c0d04000b004490f288418400c0d410710040400400503003031504440b01400c03c04050409401d0003801d68024030356802d50006170680c0b203d500c420ba03400800b010410603070144081401005541f007810401c1d503000d400291101c00004004001c1000600205c40c41440303201070b5003800781d0223402042902c00c508283ea0120509105021040381000001401c010340740c0c00c07060040050011002c40e4103a0102c0994590700809609 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 895541097 1250 895539847 895539859
    0xe070503030331021f11070e16120c0206040c09020a0f0c110a03150605011d060a170702100621120e04090b1509090a0f020604180b0901090b030318 65
    0x3c8030140e0f86114144030460685078030a050452003d4006d881c1d0310484d4101c5e00f0a0b00208010458000b0031800603500091000b1003608104035100d00f41c6001d055a610b4005ca2031034100507240203038000600d98022401456211801f50b511522700d000ea00c9904042800100c11140c005000350142280d140418030408148003203140f00b1003c100794003890340c016a6601e0040100003500c0c1c005114030000b40030300f0711340101c01400d0108000b04a010051080340100c400043d500e0f91540300c3c0c410200074803a04851300982d4105401c00035681c0c074a840041c3c40c11403801800107490418010710140c562650000543f2881c3d4a48490791780c800c41e0b040c1d43d401d100300006840d02b50340d214450784502c1449a184101541043c860f0a01d1110704032680364040e500c22802c2c0042c00c40b000075800c0c20290f0080c010f285200692000c10614020350b44503d1103c0308030401c9e0f10000c079061704030030341c40001580c004c04c00e43c2ea2203c0c17040c29220080d0866400d0780081210070b41c4001c03400d00d12a80b1210107816 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 895542347 1250 895541097 895541191
    0x50306061b010917040b07080c1f020d061410140c010207050322180b0a05090a020c01050601050a05041703071403031f14010c21030e0705030303 64
    0x10101c0034500240c94040c15954505400003013000e800c07680a5009103c510340c5003081c0c10720103041c80741c1c89145400b80101c00b0100350b9240e01d480400612150009003000807505403149403030200a9007008217481c0f40c4a0400c2c0001c6403c8107020404200b100e401444034000908980c2c0540b43d0501e00000349041c1c6000b08031410044809000902c10548510002c0d56a44810003e50303d01c0083c4100381000020084d00800c1210091011495600000c440c00161185944000703610343c0b529501190704013444c1020001400c1c03099000e40742002c0c1c4940207000f42d649130b100440b1240308084419021600500c0103100a42403840c6400700300142c00116441c1440d01d850300e00e4203000e205482d2519a000104000300700c0011060400800c414014500495007002240004c0031000e800160400c4940511242440200d00e000448481c1015005010784c0410f0002005001400c050418a00c00d00500062a04002045a1140624885108041d8803400f524020f444404104400c282d0070410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 895543597 1250 895542347 895542367
    0x3030b0306010f030303063305040510080405010b011106150301060b07080a17130204050921090a05030303190914010e0114011e06140706020d14100602070605030606 73
    0x20405010301420341103002c802e0b142d03140080641e80950001100340300388c141d0000010000c10030802400205040007c1c8240e080c0d8002c603258080c40d4416907101c403800c84401c1ca06074214071200d0040c3d01940003031040901180c010f4482c45500d81c2d00d0300c595402200040c025035030703090b400742e020350b001000490002d580d08001440c1d03402c800000ea5244000003242550340ba00f00d402d0a8412107c803104181c1c038642004600600d801c00715010340196110000034030b40321400c0c003980f0707051107403149001d4508040c17410480c039030703080301014500404401d403011450f490b00001f600c3c450481140c0300d00040d01007001c000040c1c45540401c80300c100d025107401800400038003c40e00048000000092098080e001044e018401a444242c41c1c071040200343c0c01d04420001410161150b60503c00c1070032074400002500d5104100000d05154804500c0307801c0062950000068906100c1a5186070b0301c03040310303030209040148504c0000d0781c032480c820032400d8050805980e101f0802410070f42041c007185 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 895544847 1250 895543597 895543603
    0x40f060c0b0720070b0a080601020609060f0709080613030e240c07030b070f020706210c0509060d02090a05010801081b030c0907020f0d0203040b04052229030606090c0703030b03 78
    0x504201c0d4a45e80200342010b400d13900408250b8003902c01d10040215061900c076007610b4030030140c0825500d8410500184009020348002c2c00108007a4049032083d10b4140903151042c05c0c052411070000300c0c412010b10442c6482180d202001450f50070150102d02c00148254480d0b0141281070a00c0c080d0340d100002140e402c802003441140903494241c2d248210b55402410258070b038215100340119482040840c01c0010f408a140d009241c00000300b4494030030702980c16002c1c14000a500190018500ca02e0046a03000380c058181c094880c084403071303104c0c00150fa640500b4081e5403004d522000301000510b541064403444c10b84080c0685030b03055080340210b9406041105c00d0005640020604039a07a503040144400b142001d00c0034608041c24042400b0080c810743c0f040d180b1400038038915100840042c44010200c0c00604403c21820081044401c0b00d10309021041005004000e00030502d8200429a503108030300040c00040240e4803003a01c40303065002880c0036001c041d940d82c41107295840030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 895546097 1250 895544847 895544849
    0x60b040303050d06080102031b0a2106031a07020a03081315090b06010c0203071403160801050711070608010315020d060e0610110d051b01020f040f060c0b072007 71
    0x6640d034290340f0341e07152140900b520043d600040e001d0780304204121502d403100d8250303804c1803441c2c0102c0340d440c100540100c0301c0c0280804465281040d03220300340e541e031241d64440402c90744100c0000080101003001018444022030b00d03040581c00c005203034030010340b1070710880c1d81c0030b81c6000c2c8100f01c85260b62100185a06041341e400086a40d800c4143e09000c650601c40341d00910901e05250761460950100362030700b02c248290800e08450040e90180740e81d040c09452200c582c2c00200320161961020702e98041c04051341c840010a09000d00c0c0c207038003070010540e41d058030450385500340d0903443d5541e807034003042da8440b404001c0c03503080c450098031884601480c0001c2110b5504140e15090140402c00d100c0340280883d004e001404034466080c040126200a00108500345262204211804c840d040010105684180d51000034500f003500d200710007800980c1e00c00b1026000807915601d0580e881c490300080505080303030f40701c0007550181c4113034007410001c46480400714034610603c4059180100c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 895547347 1250 895546097 895546103
    0x909040314070f02040b030102160b070c14011b110a03080c0705031308070b1305040203250305070915170601020c04060f090e03070b040308040f02300705150d060b0403 74
    0x44041d80905618041c003c0c1c001b00319007200210316000e0510043c081241a03200c004020b034400c6000604114000c660b014003207900250095103200800181038004c003421964420541c94400403110158460080d0b142c10817425402411520450785054440c840001c16a0000300000c00580000400c10700c0640041c03880750310010031260404045034144041d58006040c0100144070650b950303008800c51004452080d0b900580d20307100c581c071082260b403500a00304000c1140b1280100e40c240e0542c403083c46048a40c0e2200c840580b18015000315618414a1000080ca5260a007c00b0311540710f429800080500484241c0010400490700f0382d00543d000000588021100f0002490503000741405445000040c5180c44803999440350380510161024040145800c00a020172003483d05402c1303000e8000301244c40000c005c4d198444040300300d400071080400309060903030050000260550a5400042946000c4c00e0180c11100d0b1541006051516003900c505000421010302002040a140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 895548597 1250 895547347 895547363
    0x61802060d0e122b09020402040803070c120201050306102106051201020f030106081e10090e0706140f04030602031015090302060d090807230c1203090904031407 71
    0x16195540d40c00c0c0064181c9030b0208003000c01031320921982c0300c20b9481c2d081c0c0710b00f04071400c03880801c034031180240400c2c00001c5d0898800100815000e5000002d0016140b02c0c401d85c0c0c1c00c040e161029884040d100b00f100a0104409201103212131030111031000484201e858070541591096070000c440307074210030003c51900c0d0384080034015401c00d000e50410700d41402000b907103098100c2c1c1c1c40702c4d21444144916000c1281c24030108070050112030580650f84001c031010105802e040b100d078205000c451060714612450092080074101010030701c00f084807003503200c07128914000d1014844a901088d515442c1c1e000801c80400041c48910195004040d1a454000c420342022034452134420b0640c024010320880500400041e6100001c856a04003424000b290442c91032421030704a01840c0e000905200140003d922015441358041003600d00b0b03402200c40091600e8207021801115661b4851150000c0080341c009040940c8a41e03009031003803400440e607c4d0007950785540d40d0002d07101118815 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 895549847 1250 895548597 895548611
    0x1c1e0602040f0e060d1205160506072006180c041d060f190b0d0204020c0109111012020c0f0a03180e01080604170c070303030204031506060c061802060d 67
    0x240c0030710b48202c060b00c050035010b511824841c0029007220101c010003440c0703012040000d0b48251040301a0348103250400700681d944451454081e0711364104540c00000140e004042e04044071500c41800761001072800074101070341f41c3c2021001d09040070510b5440d1403041d5011a015511070f03200700380303a409848850059000f80f10718840e041c1080075081c0da0200003a2000d0142c045003600c2090b581c24841200092002c1454020031400140518082d520a06c0030460300c1492006401040c6003078440c03a4030401c13264440341080440e4420407000c100046280e40c1217002031843d5801000c40481d20012142c80740f170200021440c041c04040c0860000b000007806904c030041245030b40b400380c411b0805000d050340c10283d00955030b01000f170015050000d00400040c5508007201280c069604480c00c0c0c5180c0d94483c200034019520030f10088070791350394840011040581c04d11518080e20115600c030310040d02c1c075403110405001429240710803880d04a03001e10051b80c5140083c8041c04a4800201e41d80d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 895551097 1250 895549847 895549859
    0xd0905011e0203160e2107032301050105030120031302100203270904110409081b0c030a020d0b090708030406030905060603060105100c1406070513141c1e060204 71
    0x90307809504d40301c06000381c0c0290750b110341c6d855031a2903000b036601c1701b040100118084041850000746a0024221241c03a64006041445404c082d000250300030009000700e9981d401810300f20341281d07c0a607004a1007207120503054944900030b541118103102000c071142815000149442101241d00e8090303800058000c9990f8810840040401840c443d09002100361782c1c0800c9034094000d100829429441d002005d103a6156441203030400d800c803150940310300c2a201c038020402184000d0202511854400c0a070500d0001000a0003590240c5260740104281d502c0d092540f0010b043d841180c001d105000c0303170700f0781c04202400c0149403551300400c007404c0d103050407400c00368040c110b54040d422610060145840b1088a503420741c10910703005800f1003150421621419084d80381c0740042c0161f03028440e219501001501c445801e030040c40101503a03500969002d0000c2c94005034100c03402c0d50a80c0200088186441c10850091425114502d034540d0040300b1a00c1014080b122140d0108083c001e1b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 895552347 1250 895551097 895551121
    0x306020d0207200303161b1e08010e070e0709080a08030a0f020c0705061b0a0b041406010e070507030306030b1e090307080304150b0d060c230d0905011e0203 69
    0x40982114035841d00c42960030042511392103254000c00c0c00d001b024020404204c802c5035103100b441040d640084c042600c80701c01c0d04040010324040069135030328400211b02002c061080701c4031032640d03000030306503076140210200c49210020040c0090042e001c20000e552a0700f80040081d09101f01c0f140c50b602d141912041080302c00c0c00141108562040c041c040f001180010400144e56003290113945079800005c0d04480020042c240001900521380c060f070130000008243c40c0a5803040b98141c0d5069507001da8196100024490b00c0081da103600b01081c0c1290007178008100346030103480c0114019440c2c0c2c40c3e11a0f080301c10754059010100301140390003202208401075801c451001e020318500031540d01d40305100d0001900c040d000760b5070b141a01c01040000c4c1e00c2070312a00405085d0200510007070900c000104103211086c4003003548443c19035a410740514503218403c030f4080b034030303414540c040c04e40e02d0051003c080c04403020343d694900901c181800e11a50050500c54100159491805000690b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 895553597 1250 895552347 895552373
    0xf06040b061905030606090c0c0a0b0a1103060a1a0f0c06060a06090f0603021605060910140402100c11042f0403030c080d09290f2a040306020d0207 65
    0x100350040d0308060103c3c0d50302080264000c0401c42c2d811400c1e440e001c20150891203072103840030030392056056650401c00c103c806070b0f1041c10075000030407001c06a0701200340300c2e200c211107542d8450145a018012014122003500440c06100421801c040c0c814840c00001e03402000300e003040d42c3c40b8404024162400c0f9045801806007840c2c01c4c1001072070700300030100700a290702a803424560045400c0303480a82805500c2c4040f82c000c011504103040c1500c1c003075140c0000d8148210b20608106c1340c0d048985803040d00c40d01407680a080800052315a6000720740961040c081210782188070f0105c808150781c0c5010705c1d540600e0740c95145001340640c0315000000254000d40080c44c0b402440204003080d0484403c00d00c907904500840e554640344040d2100a050321840140840e4010741c3c503903408600d1400d40030f080801081c8180321910b45503100c44d2440000c4a016403540c004c0310300d1003003080f503868110b000402150303182420035450f581c7d0301040c0d8001880840f421607001c6014424881542100d01c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 895554847 1250 895553597 895553629
    0x10e040b06030d050f09043309020a020c0d020111060c09030f070f061404030b0c040905010509160e04180506040302070b030702072106021306020607030c0903060b030f06040b06 78
    0x103c2822080e40010303219001e40b064400c0301c3c220100700440da6842d690040414103403900e204440c05c0e101d100b6441140c00e034200d02a40d00b54101c52011600b80202c1c82100d082e03a4413600140a8030003000c040004102d01560100c2c1001655080074907100700030028030f4040d0039424105512035003141c044c189880907105e540722165110040070019190381c001c030030b4103032840c0b8074052151110400c03031418907214640c002003551761003808105203403250030003400551311002c0f41400240d82c1c3d50100503440c0010b40345070708001e0b51021700b6510b1501640d14007448481c054000310f02030340d082150016514202405407650f802807010481016414004900501110b9100301e00b1346c01d104a00940d15a0903000d0703800388040c10b0212656a4201c0004914107680c4028155940e841e02c004d80101040540704900240c802c22000c18131141c042d00400803080400da8030400e4251840e101e00000c0e1001d0481e050305800365400c601c220a0050010500ca44e004101d0070b80c441c18802c090003c1c0b020380c0780c01c035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 895556097 1250 895554847 895554853
    0xa0506090a1503020d03051c020702030c0405070f03200705100f0c080106050c100507050a0e0603150607021f110f030406080106232d030603120309010f05010e040b0603 74
    0x300c2d00031000c407000181d81d01900c1e00c0180711281e203829107a9100d801514840c955079003d0302200400070790014000940b00703509454901c0203240500040c1d402c10b0351444085000301d0011031440341f10b5401103005007104e80c64822042040754000c04103901500e030980d41d0390041100100170030603234010000340b400341000c100021425440f000f00b190206001e800d04101e80050b903002c62007400c104a003442c1070400710800c944c1c00d1665025200c0d0780540984000710384000000042031500c901603912480e54000e108007455410001c01a407a0b002c4081261b11201c1070540f1030341800040344046c4440019200c1055015201c06214a00390000301200040e0303100f0042403089030380c0102010704544075810155945880102d084215001c2c841140040c0040414811108441c500802004d1500d4190810600580100440351440200d49941c2c03d60301c9070a0070f05404c8070102c001e542c0155040000a90902c2880040f426900203034001117000d4402018030042c4880c43c0515032300041d0460003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 895557347 1250 895556097 895556111
    0x170105040f06410114130f1d071e0309080f03010906081216022b0b0a060f080316050a0c090519090b150a0e100602010c1106150a0e0a0506090a 63
    0xc140d5079002403291201440170a58024213225220380d00e020b8044034000d5000148c94001d0101c51110b022580c01ca031011460107d6106402086140b25058400b00b800c11481d4103001c06074050301100700e0882d0704450400070314030342c2e887c1f0300c1c00345004e485158408108185010b035440d02d4240402c001e00c1103d03108100c0b03407039030551085240c01903580c10340714503001101d40445d100400d24007041c001c00a81503c420402013012143c0060b2107000c104800b0421503465400d1142410364078000c40059900c00c024807110110508030868410b81b29408482100125036500c1020028903070001c24078540310000e01c18008099441c0f00030b0820a440104a2000e503501c84450a23100a02102010031f11644014241d485481d607450292440d91304070f030300c242005402e14654088078440e032001546002d06c03548141d8441c418003c07a032050100101015200d0700380150030072030b015060603030019000c1030000d007940456841c103105030340c000c10018042c0340c0b4200744550a040102690407091509a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 895558597 1250 895557347 895557349
    0x5151e0927040314091e090106091206110c0d020102040806010506091e0127090b12031206010c170a031505150c160e16170105040f0641 60
    0x107075540c1c06909842c0c00d0a4603014480c1c944450b00c40c100385143c020600b01c0225107100300894000c40d29003000d8074100c640c2d03a61041c040f240385100780500126402d951002c400400c41c1ca411040f441d80800304c1862030a420b05044518092001a144c030150b5004981082048014080c1c0d900402c4250b5030207180c003100c4e1001070307405159582c0e1a000800c0030648041240d20819403000b10520000d015101164900815000c10190b0b105a144080c00c20440c00344c1400c182c128a401100380034011800c2400c2c41c840c80c1001c40e801481c2c00d04001d944403101000c28401a0200c051400c00810140c0e22181030340024181c1c0d12500f800791000121807030402c019100d0b200311400c15005a03400340d072030b801204070705e5083c08844001e52840c800162004a482c1c140a242d250180c1e12950b0001090f100c0b01c54160380030804080309460050103e80100400e040a401c40d4011000890002600c65116800f4582c0b4200341000620b1104246482c1000c0b00c00035501d8520380110f442c0310428000c40c000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 895559847 1250 895558597 895558669
    0x914030712052a150a03090501022a0a080304021318060504050615100c02030a0f0602030105010f0305130209041104050a02031b12130c0308070503030a0c11060105151e09 75
    0x90301010b05480010718414420f102c0da07c8028075641c044020341d41c80752045a0f113905003e001d0a5400342d021400241840c080700090603d07100c075446520141141d882d80c08000e802c0c940f0f0880000c0f001d80340e00c00c50b02aa42d40c011880111445884001803e080c41d003000d6140000040040000c08915140c001c56a40c070350414200d8115640b401000c1442c0520200c0d01380591244e008254045180b0114204011a00a9030680b6020b03a90b020000141c04011403c1c0c2d203050743c4071907403001e580c034494015040821007071b0740c001e001d80103d000104140020400325242162540341c00e41e4044180082d03154403000c0c080180e1000d52403d41028072440034214900301c00381500070150101d50386242089800100c2000940d008000c0780e071101c105040a6849a2049501803c6645090502c0354000d01034020080c40c0351011000b004a40e081c5010300500144110014114100030f0041d1480f0780c01414000d030303032102c1c588202c0d521854401c0610001007000c00707408006140300458054504850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 895561097 1250 895559847 895559869
    0x1609051c02150903030f04050f090c040909020402120703060306060f050a0e1f0b0c10110a030e0f1b03100501030510110702041103060906030d0914030712052a 70
    0x1100c1508030041c008a540d5a0b92045080c0c554150002041c8030b003101c44950b01030400c5580581e80101828843c00c1041101c8208407100d542011081c07006200c0011254098015903101400040ca4030000b607140c400c0d00b55044815500003a19190180100080d5005da4801049250a01071162303003001d00043d4408a44c0c020021400344c0c0c140040c0030801a548000e100c8500b142408800c43e848409880581c0d0160221769114401c10150b02c103400c03c1c0703210f2401001000b043c807504103050844110058040304c920308103180701e40409041340090134080038140642e1a85103011404220040c10f0603c110581c030b0034a010701d00001007000c21408903800071b502c403040200050401c4d03010000b802c03900400c20069045468880441c110b012113600440c02903a04070780d440c205d95038400c105a5107a284600a100007454140108960741184080300c007003600c01001e444029440d1582c1e14007590008509603095404554403070400291540d02100c00e40400c48040113102d40300300841c19034a14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 895562347 1250 895561097 895561099
    0x6040e160f05121f0b0d27020d051005090a0311010b06070f031106310302031606020c03030901050403350601051e0904060501080105090708060a0e1609051c02 70
    0x71003c001100ca600e501180c0d605505950710510b1a140c891400070354941007812084c0c4801e180100a012103060f4440c403220076000603031aa01c407030003da07007840084800e1610407511440381d2080355082c071402c2d00650340b0480844006010b4141c1c40d05000b0020b016130711f01041c1c1645003010194060301d07104211500303190444180c041310000b501e002c5800308201c084002680c0604400c0c0081c4094011001640c00c82c2c2158a116070b524006101070302a6844c1c10007000b581c02046414029010102c1c803012203409404010b082c03815010b4101e095900417100e40f2aa03075954410001010b03080a080140300d0320341070f0291400c1d05c145c481440e0050b0038000b20240c9010070000280300340c1c407501c1220005980f0384180c00301c00c05100840100c68001a07411445503040284c0803c8551081c0e1466048400040400707101b80c031400000c0c4d540ca0405040503802c40c010140100355105410700b1940656865180e00000c469021801000081643c20951045a01100b21181180303004414007080e50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 895563597 1250 895562347 895562377
    0x4021305040c03120f0f170a0e0709090c0f0e100b0706231b07051509010e030415080f010b03161b03080a05090102041208090402070206040e160f05 65
    0x945040c0011a01c049074030003001c1d1a5416020191345502c002c9403400e40c1415202c075200c60b00d4060044e90714000c02c21038a00e4009040c0005603012160781c11441107048a034054441d0183c0f1a0b110009550a600080e510b540000e40c04203c1c0e10708103c151002030149040030412402c00c0c4004c2c803c0f84800d8405c1d2800c03e0404541d00b414014150306c0114200524103040e03025040032041441d90260485940c02ca101482c3e0000551014040c1114280c0b5171020240c0070580409002d161082e0024040b02050740d42e800d00003560380b000b0402000075104c0f000c0314080043c10708a0040074994000e000c1110050810010880545030b40c05881d00400001c124000b00203134150100c0d0131001144508404080b0300441d44103058210290601a40c60074809000340c2d915034000350300741d128610402215131520444903002c6001040a0703c1411402003025103400800c0e00090b1703a5070015088210128140002e21030389a100400c211f040d0300542c1400d02017540b181c0c102904c01d0240c080500710b451 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 895564847 1250 895563597 895563601
    0x20f0c0a0b0d0c1803050c0a15020c0d050c060301060513080309060405040203310302151e1e0a020c0c090705040501050d0603200907020604050706030c170a0c031404021305 76
    0x24002c020b03d245242c0c88141c008030746940d901b0302a0365031541540507801090a220080b50308859142d98005015003030f002400280d420784280310101400070b06c00e8030703640184640c2c0c485903039400300118000c10b00380d0380d03460302c9161600761105641602d502c504080d0340700300640050381e29483c0030f8604440c0d04882c01a166501c0343d190050100b2200540100145240f0b088a400004410405074060203036080320780031847c51043e2002048107881c46110900400d140e0700300a00c202140903400401501444505840020302e00000b680a8550200143d0086041c8088100030844600c440404982403142402c200c4000340c150721541c019241081000103501c091800180c102c00002c5a00042d8284229900f04c104400d081904044900c60840300f030100301c4980c40040d07028060ba4022001c2c0408030b18000007940101060103003402400403080e0040e0b01000c400e02c0d094481e40102c04041032818070920010304903035075001c4034044094580140000b5841e440900d4609000103480041c1329 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 895566097 1250 895564847 895564871
    0x114030a062703020d0306050114030109110d1a130911011b02060301030b0a05090d050901180905090a0501051b0316020703080d02070b0703020403050c010c02040b03030703020f0c0a0b0d 82
    0x9410b40401c0801d80180c14440c031400c0540c00124081c01c5403680c1d4003040410b840340b00440300000240e1600004040a00041c00314075410f92010b001c28051041c140d1915103d80305035000d41d41c04a03907801c0d5600151500002505042c0648402100b00050030001c0680c503560f840c00920243c14514100030030004051a2640303e60009031409030002c0c65152a9a5280740030700300713400c0031181003c0541c10140032680308400059140c2d41114503841d5107050600c0c0e2001100c8003942c01c001002c0038540345100113001c610302e10459000e05081d2024009003075840c24401e007510f1000e0a692203070844100e900070616402c00c2565001014140340d0112002150822840c0c10300031780020380504000030b4094800e0a055001300707080b5106a4207404075543c0cdc0a41581280514400988035400000848541d98864950034203d1032005200280490001001c2851600208400c03005640017010402c04420200001564031303800319040c2007000d042c5400d4040501a011203940910340380c240c2c08000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 895567347 1250 895566097 895566131
    0x90c0d09020a081e0f030408030313020d080a0e091008150a0212070206070914061b0a050d11060112020102071a12071e170c0a1403090c01080114030a06 67
    0x10b0840360200d800200b0003158401d8013010008265130f0034443c0ca0001c2c00c044101100307490460742d490000d18115a914000c001000206442c103d91003609600c81c40d0004d180800602241e4805a40e0030b10b1104640707084c055600e0b806008050808041003040003014400500510380c80c94403d4030084030b840700c106990183c080e10030180d0920381c0d02c004100041d0f900003440c030302c640d10607942d902000d59600610001c1c0e84080c000d075900900300b000070620100b990000d400008525904803103501a03162901c40c1803403052100c0000207800005100b988080410201d405032062004914001c1110707800030750344d80c0c46441803400c040b024a2902d4480d90010054907a80130019013401800c1c500050010905006c10003145080e4010030407040b0458410b48000b40b40c100560825030498076070300240c0a0541101c420801005036407250070414907240006103006130004001407080c1403e0344005030034840140c024000044c0341600d07800c80c41d5800114002c119800040010b10f071162a41d035055 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 895568597 1250 895567347 895567349
    0x302040617061327050a02031203091002092d010306050306090d0309050307060603030c020901091514030705030312041a3606040c060809010b24160b07030b090c0d09020a 75
    0x130b52464213146282c00c0c0840800d0494000340b007207007a240320315051001c09100d800180d445a0351a170040030340c1801c0716043d0740205500500240035485d80d80d12060407001825400c1c00384151205800c41407040b5503014000c24018203c1140038001c0b41ca000480150b4800791100e80c00201611062074505000040c01100c4071240c01500038010385840382005850075000c2c000490042e907404000241a01c0c0d64842e60448604207140102d2051810700c2e0f0002d400c441c807400300e40c18081c130080020540e50800c01861044c211860540d01b03840c00d828172440c107202804000440c1d000000420a070710680c00011660b0850100210100c004c0f48040906503816401505406224040501c801c0c0a11034482c90110780d84c42e55a00e983e0380d244083d450a03104204c10140e000b074503883d204050040320050000e5201c0e4440c41c4a818443c040844540300910400c040d182c00c0e1003d024490503e51500034402c103004207461000f42406d0104074039025210313407459108440da41e20720900840d56840b082c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 895569847 1250 895568597 895568651
    0xe0a080109080f2206020105040b1528090e070504060b040602060a0e0304090e0606042703050f1201030807140114150a0b0309070815010b03070f0c02060a03020406170613 75
    0x700c004c03920381c8800390003040243d07800c1d2090b92120001452446c20490500700140003c5d0521000706290038000702c0d0b085110b81c810189041100e07020825101a1049880344080c1c040203088561408040c041259129000703041c40c00703810802484040e80003c1c840303030003500d00e070800956030b40400c443d1030131805140c1000314094140740400740503000014046010750700460301002140755a5504854a644111100c05000c000b124041c020034001c001030300d11042c40c3c400b0382d4076000b4404c480c0811b43c60242c104a0307101c14003007210304c04c0c000b20208200340314004174000c01c4071a0664014401c980130081803600c2c400458002001103440e40142d51000703045001c0400d48905012503844e443d00b055004025541c03181220050303000920b62100c504960303140800d10314588a1310802c468a0314503078925010701881212520040c1c1303505004040200442c0d43c01070b1228200034000300010341d080058111010400280072841e03490100c450703103a82400500003140c1c2492441c101d250720710f802081c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 895571097 1250 895569847 895569907
    0xb1204030c0203420601050708041a1b03040608240a030b0a0e0102070f0210022803120b01020d050309240a05160504090b0a12030e0a080109080f 64
    0x15400c040c80380c032001340500210704084098103448995824004014140e0410b664402e0404149103500079401007940c0790259444500d004c2c1c54569140280762800322070311222100081040014101820448503010741c10003035803901745010f6004104540141600d500340c40b00780194161302c2e058280c5403010400182910340c019550f4101002604011030728010700c82d04101d01c840c0010010702c2200d85166100030b9800015100d0f80074400400c1c0000000001d42c0f062100b510980c03130108040c0390100d0743c1900c3c40d51012040d0701c0c0c0109541000e601141440382030140b900e6442c1e8000c80c0c0da104495462500c0e80e107a90b03c04040c1c3c0d01c0c110b003076245c49643d145c01c03c07050740c2d0340400724055622400034100305000545592040c00d003840110106100000c0050100b0b2010b0050754020410289008200700311441d12260340b10351110340329074100d0100700047e80910050816101d10402450f503207000b00200350141e1150150391040e5980e449038000d0000320011000c814000c6e28940e101c6202070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 895572347 1250 895571097 895571113
    0xc010827010b040e011e0e03040f1401030605011103120411060c0a120804081803070b030a1a01080603210f12040615030f0b072007140a0b1204030c0203 67
    0x103000b8000342c684030340680c1c00e00011102091050180c8040648648080d00c890890340510400804d80d0080f5130711103010401c400174240e40d94440070b4004c0c2280b104910580e103031960015003164016401703d4148910248440700d0b001000c026074039020800281c05070705907a40d00c0e03c8001980304c81c00032a4400404a60214505800030341800624401c03a01c070071400c00242c0083e40c540e4000c1b50000c2641c0e00403c592298910f4016400c3e1445002a003110100da843e00200103070768204940c00c0040d5585d40d050642c20345000540b090400707500b804d0064041c00c0007000b0980311800e00320ba9940c8034110311804100d13024031000300c4a019080001c80c1d5180c6203800707461040144c055909555580c285041c100403d1610001502266444105882c48512982c2e80e00e02101000f00640d0900900c901106400b56043c2104050030740c1e140301610031f450418608a5400c05102200760168491210900020300c4484c21500c09d4991292608078681d180d241c12074502180c850020342500950304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 895573597 1250 895572347 895572421
    0x90f070e041e0608010b06040611070305010507052517090f060403030c051c0203090103050a0b0901150201060b071a0621011e140c0a0302040305070f090b0d050c0108 73
    0x610b520403034440e041d080c010b450b0b0b5290201c2c2643c46003203400794011300820007040303071034058652031088541640c16500143d60b03e464450840344104c07403800110324005844400b515184003130420300a6102c84010801310544c035196000382d000320135003001341c4000644140ea6510011004903048000700010b640e9030310707460020b0070707103025200849082c464880e190b000d07140d842080408002540c0d00071400d00317000c440110090000500340888003591349000095030b843e00e004540c0681101140d1205900c0942030003802c4600c15406400003d40c00e100310380000d024151448400d100e800840041611031400142c15800138414819a02132980082c220311035043d001589641d80c2402c3c1b54000b2000b9200000c2680c859400c40c5050000c08000182d82e410900050240ba285601c0c0c01802d060b166520185003040e590400740015005000402c4180301c2c1d40900c0d9001c100542d10582c8050155450350341e60709902d10700d5418070414800282006000c01c501034803e1320341406000a65200304 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 895574847 1250 895573597 895573631
    0xf070308070303051003170d1b02010606121404020609060c0d0305010501080709081015120c03020f06070c0b0901171810050903040b030c04090e060a060e06090f070e04 74
    0x11002ca02180c00c2ca0002100c114560400380b0440303802500340d58454600c0c418491040d0b016005503503200d40e41d501c42c568070032010381c2100b100368541e0700000790017420f183c4060320134000d04031200307429418a954541504c000c1c603000340d00998151103040c0c5030950400040c2684c005e1340c000071094400c000124a0f901e5158001904a075020f88544549031501d18085427622a0360203a85040c0c0d01c0700c410340028055544c840140b41c100004012003c0ea207031400144a08100d05050b00c1c0b500034050140154585031134240d00a20044900900e000c445541e4100c03170405900c2041203243c00400c0c2410541d008070000b030b841000d80150300383d851900305001c20043ca43d000900c0315601c1461411900700c40144202405101542d00a43c1041d00d0030340c800049a00c0200f0082c500c160900000a00c00200e008a0210400242c00340c807951615905050880e0f44541c8018182c0c0b06813001d128880d100c0303002094026150701403040b9299200c50095901c030040340203183c0c020b443c1c4504060421185 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 895576097 1250 895574847 895574857
    0xa0804060c03090f12090e07030f1401080d110c040510080114070206010909030905060c06010602060903130506160c170111130b070201020f03030c0d060b0307090501050c0f070308 79
    0x14080401c10024901c0c41241101c01a40000f072001100c0600e04000c80d000e48032140741c0030103500c0c03d010019290029029005d1055030602c0200f074031451889214080e500411030030000c260f141b020207603d0801e400303036605d413042d401d5414000d50010300d050102080c4098525200090000d010508240010800c802c00600c5019425440c00a01072110035038a0a003034010103880d402802c0a900b80007400000b070405000071000c2c42030b0f01d040011182c0790000544811001280541200c0d0300d040c10190a292000700803031a2608100b0a00e41c039042da000200040d100c090381c01039100d03000f0310007021000107907420160120b5081c0c500014408100c0c140400403900902c020300c4a02035581c201c2c60070f0300882c9128a2424010501806140b0b001e00140403040d005104a854540f0003080503401c6500c10b0b24030003504000010035240c004020b0150600801301d9115072403030b51a08640c004c0c5185500d000380d5040090000342c96190b00c600f01302c035060a01516065031040d50340c07890000c400f03030700c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 895577347 1250 895576097 895576103
    0x12010b1801050304021f09050d0803070801080d140d09150b0a0501030b0a0302040513080d0c0905060403031b03020f0f0303060a1a0703030c121107061a010c1401060504020a0804 78
    0x811000c0254462016a400303942c2c05407010003406034071180e11600b1446120b042c4104400c0010005169a40c00c00b50b844541c0611400396032400e140030b00803c0c4da04c0503001940303680d001c01c60340c011040d800761200100e404003a108035126030f907103140ba00c050881308001402d100709903000a203100b50706a100d049440c101b1108820480e6480340150b0a036010049040e5200710061820005803c1c10342000394820884804d0441d54216a5034548003600030035900b0607060359070100c00d891250000d010b00017a2100b141d40c030340cc00340b40d175800034000315030325081c0e103000c008840e40310040500800804070102d102038155004007017184020342c0d680e00100e550903c100010840051380c410070203c00450010706840080c075141c40b0b5241a03001d45141d44503a400c0204c0c01d4038a4640503e00e11401c006142e4142540c1d5468446007441e42c1a504c1c0b4603031812968034002901c1140b680c01102c0313141450b40c0403420000f0314030610540c90041c013070b643c4203542140c00000c9c02c08515510000d11131040f84 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 895578597 1250 895577347 895577377
    0x1b08090105090c0d0f110411040e010b030f15030a0c06030e19050a02060a11060f0405010b03010b011d040906020c0f0f030a020c0909160e10060e030d03090812010b 72
    0x103201642c1d241d84642070300c03038503030468042e201300340c082140c1802d5070412134042e195403901c2e00310080124044402c4070744010003910020405200009500490500500d040640e541c1103040000302002240000b0f44407480c0601d80c490441b800c0d0310305008c08a80ca03508a96840c20300c075642c1030094080c210600c1c040d0382d03d003c1c070401704a10301e036281c0d41c14034015000340040422044580c240012070307004808940c14006100b26880600c903040000340d01c01c505080542c807542c10a844d1003401e5400100056100780d06007180499070742d0348402c00d002821035900c18903e40342c0128020400804180b000a04a1800000d102c13003120000551322a0f40d242c85030440354501c20b64078040c0d849002d2006280c00503003011110100034500451082d4002501d0b0007a1800c4103440038100181000c1c0d94018461702d10100e0401860041c0c0c9034605009284a08140c0c10524404000035281d6691003050b078245940c9500f0113040c02045015210340c0d49205c190300f201c0d941c60b0342d40440c068001d00e40e00d46d0b000c0307 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 895579847 1250 895578597 895578601
    0x301170303090a08091f0c150b03060703200c070f0e0108031204110603040c050a150203040b030a0605030609062703190201021303030e090a0905030d050402041b08090105 75
    0x80010840348a007503503030094104802c0359502c0b00e143d503010004240d0302400b10b424400241c04085c904400700d81c41a00d071164680024940140202907501300031585502d4880141007984010810503846541440c0004488404d021107003003504280850503800c06e00410310001030000090b041c0d0039901da640300b10114a980e402440d07000a801d0013a0382c21a001031003000b12840c045004e03d90828400d50280c190b190017840801c8003500100c5081c2c0382540000c0c0200194180701a40070050903099580e05c100060381c10303002c0e507244180e11032500c3d40d100000000d0b41e00c0d401580b000300607040c018203960840c2070440768560f45800c1a11204681c18200d8010004038407116100d04c40441d1010285081070703207500240803404488403400e030641d5000c12141c03424000c00e060700c0c0043c0d03110741c03101ea01c02d520902c01d01c20701c02070003010301010514100000c808a580001a42c480c6080c041c0042110350300d501c042000392401a1b005c40c01400c00c00d485084007a04948001e1007200424002c00043d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 895581097 1250 895579847 895579889
    0x24080f01113a0612260a0c021302030403210605010512060d02061315050a08180a1205070c0915031b03051203150d1e17040b130803040605160221030301 67
    0x1030a0720003880c4210542002103c50403030041f851780d21694001070041071050340c0d0007195405e1fa403080b2030443c002268011b050b10003074154280b0980d00811140200a40340c00e00001030541e01c140f6010800b0300000b003000420030fa403a0140a40c0955002d030071517445000e0381107440c450019501560040f03942100030b0000d00b5120344161500e081081d520410aa102c21500700a0701c0003001e040300080c02a218110f002c076024040341c20290316144d6816548080609140e982d0f01e107103401c500080d9041c58000e100580d940c44080080c0c1c3d4014480e0f544102444641c0390598040c2d5000504034003075064510a82000900554424500c02ca80305009980c1d00007001b9804103581e500400b02c00188803125926018150700300c06203881241c900d6403940700b280032002142c025912148400c4000200032400c0c0c0e0052708403100601c03600300218142801d01002525a0140c01902d07141d20f00401500c005640c1c1d500c10300d007810400c24014075080441a00415102d61003401100d60319640a130401c070305 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 895582347 1250 895581097 895581143
    0x90b010e0a05190c050d0e1b030f060c0918010605121303090b18121e1c0309330c020c0105030a24080f01113a0612 51
    0x842d85003005410000d6060000f00001084030310260303003c000301444050100349192244a6000301208000e1034620003114010091420888a680c0079400c030102003102c4040004c1d032190040e0f04160b0182e180c886000129030401914011069041d0740b01c0000203201d80c1190003000c901d00c001203510304954800440728658454020010009840304030108000c950500107845d03c1c800c9811900ea60b46145000200c48074110f22104040343c1025021140c0f204401c1c00740d00405c070340032018060900c4140d00b6000300e00403a100c15011b0685590303900003048000c0b290ba040f0300321143c6a6405410300c120550f11340785004900703e80d000e4a4022005510750002441e02c1a5240580d240e91540e526010400c01400400351111101c085180b89911148100402e010107080031500811315003030f8680c4d2490948481a0000c00348040c10004246190000e801640b003456086841d02c1384401080c40740400d102c5686040071655140480104003040e020014503076441c001d00085003044490640151 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 895583597 1250 895582347 895582351
    0x106080a0b0906040c0504090f051602070302360c03100f08100b0a03050319020709050c09220204120203210714012301090c0f08150d0204090b010e0a05 67
    0x350200302c04000400c2440c0c19040500d0b0b1040310700d002030070b0555a082050680e41211a820001500c03502009408450780740007a01d4900544004d0503076501d51b0f0041000202d40c881900f654094501c028682d4402c1e4040c0c101110030b40340c044070550300e0002410542900141d950804003240e951002800900340014001a03650140c041d00c150901d0311044801405044079081d0854251040000421010b001600440ea01000b07a070111700d4034048021700b0400c103038004041c04c030328103018052103c1c0f00744203035100d070841607400c2000c07103810b00d064851440031f448030044400e00003d00410f20b00300c01800801c0080c42901110843c200041c0390707006407400c090664135a070701300740402c0e80882c81d41602c658010f000c400000417204407205c81c03080c000c6880c0c445403559040e11001040b16401e02c2c032410702e0018a03442c003071005240c082c10050a540c0054623442c90740d00048044087c07940d4814100550381e500820030829500a031520845001091207038490440150703002454121041c02070358 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 895584847 1250 895583597 895583599
    0x170f0f1911011b030c030e0703050a03110a0507030303050711070f0f09020418021b03030a1b080403212d0e060c04030b070504091508213001030b0106080a0b 69
    0xc1c3c210044180110010f1403181d141c1c00405445040c44800f8903003d200304400340d8065030142400a056080c09800075030414015600c5038490351000e000700c0d20229141098990500e00458182c0712100d044848081083c00010300d07000300b1100040d6011401c0484c811100b005c906208600c2d52035000504900035489071450303801c082c90324000c10021a9000b40744460b150b42d00fa2070100000c07100e041c950b8200b103800c40c400d265603880861510741400d003440303500302c05803411244074501a5401061010844441c0781c43c0c0003408003850411001d6089071f40d50203240c3c0d01d80c80c02c40b19001c045424520030054100b64003450107131505001c2c040420054424507645030134500e02490b56641b4048558010484001c0003010b00000c28003101c20702810a5560514880b032094505000040b070900d100e081a81d0341101035414443e2404050030b041c0c5840e494940d44c0e1100802452010f10241840b04008034400c140d020008000c018041300d829050303a00c243e5408025903681c51400040314401a482 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 895586097 1250 895584847 895584881
    0x1801080613230304081006051e030a0b06041803020c18010501210f06090b0f030705010e0904060e0f060f0c04120b060307030c0602030a1209170f0f191101 68
    0x94030310b40499035080b4101484604882c6803640d43c1e0070f00790801c203d51852801d403d489400400180c07a05440c03a0501212a4922038680c688020000f42c2e0751100180003088440c1c20000034206a5903588a500c00c001d12030b45d15402c114151030025118181c00d207642d80304180c00c550320380c00300000f41c0d00307641641e00684440d5600c440c2c44144010710350094a0301d00250707450b401c1c5488250030500030300e0000e1030280000300b1100103110811121741c0d401000f03180a0392004c0c02c1044030740c3e4805d03060703103e140b020360304079040d52283e09000d03024019403030800d4060321400b405458903803c0040c50b1841034421009000300f603120340401c40031030300c56031040c481e07400ea86030600004034409070134880c0c02c890010126505a0707941c0e40d40703000e50401940100003503000480e20240c200d4022410b50500e00c03000100704204d4035141e0701c210210343c0906003001114004926440c46400c1b120032107000f950001503840d02d840b41c006080c420f0f0340c2083c01c884000351591200c002031310414000c0f81218044140c034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 895587347 1250 895586097 895586123
    0x30e06160606080c01141c110405010f140d0c020a02030109210302040810180506100810020408210d24050d020a03030e03030702150c3313021801080613 67
    0x192625420900d22050740c14207c01e60144180240e02c600305081611010040e03d603480c00c400503002102c0940c0f048103000032440321f50012940700003103031444000c24800048020484d03c0403460507036100b000035090761920b45140180000b1140f0f200380c501d8001817034032000b40315410460603801584191042035200100300c84d8540e940c3d8200303500160b071000201200092036220300c1e18101d002d8410174400185900e0501c103103281072044800071400c140040d031900e840d200e0350070f6641d03402c1c04405448072188000b190381420030500711480c600b0100424840783d00103001c1c007140325211400342040c20100c5440007906080c102907a4421a800900c84021180346d9202640c41e08072600b181c0c0d0340341c0410003141006a9a001d2010b40700d10002c41041c0c1c60f9580000120304e419001a071071709209001607009075030703403a480941039540065900c100c1c0c0e05850b4012103141602c482d0070029404058402c0b0594149420081541215400030441e013094035001e04c43e4580d0004894050001e601d0b000e2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 895588597 1250 895587347 895587377
    0x513210f0507111003090506060a050a03260d0605100305010605182b02151303030e031e010b031005011a0c0a080304030f39030e06160606080c01 64
    0xc003401c0014040c120b01d0148119550000300801c1c07104130100c012075038075524a42071141c10000c4903405201554201031a50030b18000440c115500d10000b424050400c1c0c001c02c1c91644105403003440d4006800391925046030881f00c074007416241c042d050007024040180f51005100f4056035040350344a48603940b4280280140602c0101c20300703203250f00030814501d0009205801c2a841c000c4c10300d60700000d40c070071010b48100514920034000c5048019021311141d40114a00b030550b130200d80d0300d402d10750034412074400880d0a1400c1c820f4002d81e0150202001c8154034030640210b14a4841101903e600b00e020941c20400ca6200b80141c10040501041c1c0b94250070a41d00141109504c050450328424506c0d903132032500d0780c0101d50440000b960804203000c42500400702004500f082111449184d06c10207900c000803102c10f0340c0000c1410283d080743e007494010844015078440c041d02e081c0d03442040450009160700b9a4a00b290000d1401000003014600421040200d48059541421021136a070b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 895589847 1250 895588597 895588607
    0x3010b0702040b06130f1a161106030c0a020f0a1119170d08090a020f090402060904050103080c070914061909020403030c020918060f0c0d0513210f 65
    0x110480e0450707034498034222299113040180482e82c0b079070030105504174240b4460b50f10840321031344982c540b00003c108001502c038070705040e2030303074003003200495403040540382030050103089000c0700d490300401e001082c0b20030040010000c0450303407140e40840341c00e43c0d1012407160340d41c1202440604650004052051b0520b0501d0200c039100d990001f140c00e5858540410b0f00ca04c46000c0c40259250f44802d4642c00c00070b4000a94507404180400942940b03425600804c2d0380415034074145100e00603680002d800c650341e241c02d4620035100034004200755a1a0301c1c09500540c05249801c40511a06400140d6a01e160007070303100180308207c000a00c1d17203614041c4101e64842400c904104000c48002041444e001c3c0b01800c019030003a0703034084048000c1c0c010300020a0303005d0155a8035000417a41a450300303c0005401e50084519140d582080c1d40d8514004601e019040d2007151140c140001d00400d074419045081301c039230064101200302c54550030007643d01045140828003041d1102c10001810f8082d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 895591097 1250 895589847 895589857
    0x20f18040210120e070306230a02070f120f0207080c01050d1505120312010902090d150f060e0f010b1207080709050d05010507090b040503030711030f010612141203010b 74
    0x505002441802c0c00b100001511134260360121325500c0000e080062001500502040d000c103c0b01c0d0001026041d0344403003030000010407a2841d00d4000810104201e1005a0185140d800c101040581545800020701e0300c818400e001c40140300e0342901080323503a4045401c3c404882e05860301498840c0260800018003030b05181c03d000d22805200009141d100e07031204880300000040515601c1c0000e400102180358180c010803601807060000c400140c40b00c00c1a80a0320f5000038030b010100650b1a515000307000c2140c81e0500d0141480800501c0c280e000072118041c001544143d0306c940e80700d4040000c42d000d44c40c411056540e0000100300902d006482e00d40d00300f0070038984242c840ba101d2001c40c0780f8881500046070903030341d220104500e00798025495005010781c600c081d880c081c0303000002542c4e8081c4080c042c081081c000d90500c082d6078100725000302c030032110001340001030b07480c9a01013607045d480303070140c440020140030f10324907103804290500004040c0900386e0441e424103040d04071715001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 895592347 1250 895591097 895591129
    0x1a13060506030f19030f0912080c07270f0c08160c12050408100c050a3005010510090509010608090109061e060e010b03011403070e01080a020f180402 66
    0x82c605441c0c0080006020030380b04c001c0394080800342e1343e000d4034000f000b403c088900350003080780c8039030184030711134501080a4070a03402c804595282d110220001e810076600e940320701c0c2d03101c100c000155060700400703203840c0001100f4007080103d442200c04180544d110a15454000782600d80091280d50b0b40003500c100701160751806411030b28990b03482c1c41e800151a032040c800f041d004a420031a85c002006030294003500e640060264001c0c0040242c1603001c0c144078141800300c11110106c210b51440d0003030541d000f1078070f105030001c0c1a100d000d100070482030182c18000c1c0401844014420b010351071400131510081d0201d0581c3c4c7c0b0700441211941d602800c01c070043d540310000031010031211701811280c0800001d036040c0d4050b08025410403100a03a000e0007070019a50010440e0003d66419241100c0700c81030100d4a0907c8000002e0070007940750008035002585800200c0e034407100103140e503000c920035034410841d125840c080010100410b03d881d410b60702210f0001e401824050625444445 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 895593597 1250 895592347 895592353
    0x2040c0c05030315101e140c071d06090c07020108070c020301051611010c0e04200406020c0f06070519111026010e0403030e1c08041a1306050603 64
    0x40d9a00c803030441d44140c458140c64071042408401c1c0389000d00708840b1418181c2802403240311080d40400c2190703104904007080c04110b40721583c40804640486504606210030340d601c154440442035032403a075100d600c2c03042e004900e00040c042d040c0400b2550003107145071200360402c40f82d0b60044624900090a903000c020395852540c00585003405040e00850782041c602c6200300b54413000900240071900c00000e66030401880140d0b29400003030340802038100792000f00342900702d0343d00190503800d40b008190b0581e40000340007a400e9800301c0da000ea100021250078050001e501c040040c1c174040c501020301240c00904500d00306040f40400103061522503c40b02c000c141104000030145203403c0b0946002c1501c18844180400030b110800d02c0c0b4080304a40d030b15003075061a840400d030315030041c4010b00303150307603150b000740b1032102003200b1074408000d0200d03d0380d036001d1807034001c107458419101140c054078001c801103000c2d68620b04581c42606d1044d05861320b103070301c0e0301c031403024050160071140c00d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 895594847 1250 895593597 895593617
    0x30803130b15030c030d05071b03050a12110d0f0c1b060f080901050f0c0f1c020a0e12032b0f09050f0a0b01050409140604030f020f1203010302040c 65
    0x40d505a5480d4410202c1c0c42c48041c00d810640145030402100014132442500403801038010300b900700302030340c40c0240c0194410300c241946040c54507444031a50005483e074410f440c2000c0410640700380c0304038107050660380c641d00e081140d0016903949610a6125010808005405182034070440900410900804005c800a48070070205410179410341c111500185001344c109035016081045a50001c010800030840361500341482d040d4410050b040d60048130340000c82c070a203e150003060760302403e191b81103201c040c6e030b0b4543c14100075804252901c0104624121844407031814581031001c0c030700c1901c055803070400c150b0315050102c5c09074560104d40c640ca44601250300300c508e22035a400400300c1a40080c103804142005032809403054a107031003540c062001c403000661a500c01d1411580301f40d802040f4006940703000c130001124856081d03001d200302c80411007815403040c03c0c4000d4008540a960020100c9503169456481c001e609095000c020001040141480d60121800000601d0210844 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 895596097 1250 895594847 895594853
    0x60a031a0406090b0a06080f01030b04231c02010527010204091505040b0d0312050601090321180b25020303030f0916060c02192c070503010f03080313 66
    0xb5201030700544561582c0380b041041030f041c0b102c0700c9000f800c49410185a945003040d000c042c1000d05004c014200d0290314007003800c01800664a1070700110709074070520501250118256034490740c0940561407112040b030905024010321900b40038480303c240440309a101c4c052000034660003100301c05031a40d401c001c00548501c4900c40d071240c01010b2649544024607000401058070441825144030755034203010280080e400414860b0120384020740881c1d291788000040c1c400144c15803000d4000380703100300040c618540440030fa807403d14068443e1041c5910543d401c920300300c00d03402058561042002065580e100242d40d2000382d0020030728410148403c4d5001c42d0450300700b03503502c18001d5a03103001e0288040c010301c110441c2c10711010002d6a2540343c500010440c0403200c0019000340301310741c2d40a071146c24540d0000050241d034030a01c1e2010304156018130403030b4001c1c0340c0806010305140100c0c036110710803006c8078103c4d09101e104c0b0010038115122200c65074005420854003400b800c41081c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 895597347 1250 895596097 895596101
    0xc0114031609082a0301230403050d06080a050f0c0a033f0f02033a060b090f0406030201021c1715040b0a1a09010e061201061b02060a031a04 62
    0x10b204809003200c4c00d4900c8443c401c010030034800400742c80ba9042c2640078083d0a001802c1401507480307502403241c2d0707460b00d08040d40c403403140b001c00d5502e43c2d08080001c00c000100040b580400e45c4a0000c880c066511a0486512002c210311001c1d40000c0814003080412011023280c00700c3c0c10350011407000d20003221002c2401c80700c164007503008400d03418408002183c022000390748100540c00958a007030a420504881d5803a40c480070040703c0106a2400210300b0904041ea080d07428800d030070483d81d07480311304241c8607401c0785000500c5120010451030282c18107001e560120707913068008041c500000c401d40c02c0040d48181c80c06d001c0084655040714001800590540146040c80e64281c45061400910080e2608002101d02809104404005030040d001c107011200001890090f15482c10500494040d03e4170303c4d0690340f2820200d0442c7c0701c0807a003148181250710036150012401e60b1144188041f412184010758040340600400c3c807014041d4000300d080010420342400e0301540c034000681 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 895598597 1250 895597347 895597363
    0x90409061b020c01090602070e070815222f0304140604120306360605190503060112030c02010302070311060a05040618170d060b040b03090c011403160908 68
    0x20043c1e00c0000c6020a07941c0012840006c5c141a1001d03200700c506060a1300300c4610050141c404012040d0300058501c42c84a402803001440108400c01c6402107825419240c8814035840709440d03c0c00741d580c00100620a42021004018644d801c103091601c1c0e40c1c00c803039810084c003c0da400420140b92a01e0f00320240841c4e8440e6102c0d4510b01900185818000d0071200180c1004419282030440008640148030b01020b085d0520032021590810042008000e458164403540e08510b011040c0e609810304143c0c44004d036141501125601c0c0e0741c40080c000d01448028014003c90060081e0b040954860f4000b00302ca24000e06000c0040c002d182080b030300e0550211001074045035110140000c00049009001c205050209100c81d503402640f14003040c0205001c0c80f20782c14000050042e01c1c5074480e04500010604200c2e4035131a5a5218001080da43c070481d20000c141c05400074581d1a58003542880e0013003000d2801085c210f0780e902c8442401c0b01040800f100911905040019035403004010142e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 895599847 1250 895598597 895598651
    0x1a1606050406050609061f1404081b010302130320102706120e011508070807060224091e03070b0f0103031e110a0b04020906040b0609040906 62
    0x190301d2520382003140449402600e80f620452007402030003003e42d0f460803401d00200c251007107140b0403000d036201038581d00c07003114034070340602c2022400040d654400f06440781d40020b0f0310020401e48082c800118100d01c13540320080729410981c0e1041c400f080401c0342c62040d0a9080d002d01d1189011000024021384041c00d54400142450031012400615050700c2c86c209218103443c15007080c2440700c060302100c10000000c52141e85c0d074031081c403068000d4000040c460080d607814010705803078140040d2070b07940501a00301c2d1445112000a2404d10019104080c481d01401c0300e1800862010074a840e01e1000d001280c041c0f08294210039100034003540450407a8640f002159901000d2802d448540700c020040091103078204010804241c002c80480800e000c4400c5620f82042c0c0e110044d035460043c0380300307440c1c0ca10907411a40300304140d100003203001b94021101803903036549000810042c1ea10b04003030140c005106120b200c2650415804c4002107e210b0306010503200705d5110110354081a0103061 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 895601097 1250 895599847 895599851
    0xb0703020a05010f06140405010b0405040f0f0c1e0801151b0b2e1d090a050703230627010b060f09010e1c0326101502161a1606 56
    0x406c808503104084030a411400c0d10700f071006624110300d002c4240980c0c07040358051901c03110030740c4501d420b0f6403105081c05c000c0441000304001007a001044002840b1070b00f0305c04105014810308503402040d50781d040f90700100e400051259100310803518180c858140320440c203205800c640008140055084c410740301d44488124802c0c802080d10204049040c1c0301d0600c00440806000c00e5100c01002c28501100b92005481502c1d54041070b131900a44031030203040f0380103222011080080040c29000300301484210845201c140580d8562034032001d03200440303032603526907038030140c21861815040303008004030000a03076080b0440440c100d0f0340919110109044000380700b008075a0480810100b42c1c4080c0e443c00441905000701030f0810b03015900103020300030304032900d140030743c8080c40f9800340e2140c030a42080f25040c43e84070401c0c01c520500a030340350440104946255a4400125000030303030220718100c00e1f600d2030103038051025401105c00e0380e144402081005404d00030b95050900d02e42c89a000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 895602347 1250 895601097 895601099
    0x2150a120f11072d05010b0316060e22060303030905061f12210507020102010e0f101e1d060105040207080f1602030f1e030a08010b0703020a05010f06 66
    0x20310100ca1075460241e8801d807400154048400445040e18422584421081c0011240100c0007841e5601c0d01c200c14880d1081c0f800071001c1201c10342002081da40142c0845400c604203c00306140985580603050009803110520130741860201451551070110410f030030400710100403900195100341e0001d81c0403944038030342681004020014aa070040320240600f414000700681030000074064842d1400c1402d03c407100c0360610103100744152034081c500ca00303000300c10092540a031051304811001c0e07001d9464070340344220f541c00c00700348541e00040141c05880d1754101d040c10a030051540da40c0912035600115101106088580b01d40341200c10801c29401068000000391481d101058016078043e60041c040240010441c80554248440c400e10540d00c0d54064a9412200c28040002a505d8800c0d41007410034840080b4400e184850440c0300d01c14800104107440780d40384a1203a0180006070b42400404c2069084000b0384603503403191059a00b44501600ca06081d40d210b1001d241240f543c6082c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 895603597 1250 895602347 895602377
    0x60a0314270712080c0f03121503120307050c0f0a031e1b0206070f06050c0a02100e280c1401030b04142e0b04150801030b0103080702150a 61
    0xc6a460354141c180007801d070a400c2807030101449101060003444034101007030080e00103a041c030000c1c40381c5c140401260344075081070380c0b02e2412140c265048582503812000c88800b6040c042088000f00140795035161540d20b03461011603555008440305420350055602603c494034047c0641200c240c000c0c1d441d0f5101c402c5005400f4005041000368900f840380c84184200c8261220010105064040711002e4650071f0500307100030010441e42d0010429458003003080101120740001d05107040e01350b07003126206051220b00508940500c09600d805030f2140006040c0c09401d8403440c0c414004c040160146600181d40e10070018803581c0107014038041d440310824a07542d241c49900600301003201d003484a6015940d0500310350300f01400025640140c002d10b8407410120b00c12070500d60043d0a0f0710007500b645d030000500c83e0317040790144c44068400144100b0350303076102d080000d050701d8000748101c850764a1595003450350791042400703e802c08596441c00003114030755400b41c1a900c919407684141444110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 895604847 1250 895603597 895603651
    0x609060c150f0118092a060e0109140d06020c0615090c0403080315010915020c03061005030607030c0c120c020a06030c0207050108040c030b040c091415060a0314 71
    0x1d0021401202c0c050040140d07102c0011024a00d08500c5030000d2240014200403030303282e8100d40004803924204182806040c006100a8116a0682d90b005c0c41c3e0f840c0303400115940c0c1e8171803150400030300450710a08041e00d080d02c55400c682f0f04c9200d00528004c07411090500b0b000e41120f6455002e1a11a44880a8142403080b6640000e0301c00c00945454115502c4000b980005401e86040c110300c508403603072507401800400c2c058070045500300085a4020402581c981caa070f040300d402401130601180c88040e503803c200303040d294001d02030aa00d0f510b6040890003000d001c940403003000310b60000d42c40801c001c1c0200388510f1115940324002e0030418014891562240d40c0078004244c81e101442610a60205040083d5942460400c2041d2200d081261035207150b81c00145c445100402408108540b50701e4135400c80718405810b020341900c590340011780050880c2d1342e000fa28441c8401030407510702a402041d1303100180c240001c4036400c01c585a01e10a60858000c010f00e20f1001d43e0740ba00b44500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 895606097 1250 895604847 895604851
    0x1c05041406010806010302060a11120f04080c0906060a0f05090901090605011704050601060e01020a06020c061b070308150415061d031c080c0c06101a070b150609060c15 74
    0x8100104132951556002c5900303441082c21780c2040190314070500340031401c14000c3c03040300d01814850726211502e82d0710003440c0e83c4c081d210b1204217200344e1044c81d0a84c20030005052007000000c0c201c504001c0000030503a100f22050391382e0710420070100952041907a4030454580a044188070004040307041400143c03140c284043d550210032090420800060300000e6040e0650300907181c050b210382d02e90b000507458600c0c801d00042000d80080b4a8003500c5c0b200041c080d102e1911401c038100d4000e41042201d80a02c220100500010440000148100b00000d4618042d400140c40010000b02020250100c50b81a4000200244c01304050810314010160712119441c000c0f0701620515820003a019411182000300c8414000d03c0000035001d04442425180c940030140151000751600a20b50707003001c1810b0044244464000441101c1d100588058400c401e42c840140e801c0d0780c407685240700080e11590286a07200707808015885030f43d00c4c3d01002c0d10021030f8110080a90211100c0c4a60f980480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 895607347 1250 895606097 895606109
    0xc0c0604030c060506242b0b01090f0617060112020d050105090c042301030207051c02060f0415050606090a2619080f13140a0603021e1c0504140601 65
    0x12464885402040300b5010310341c1c01005400c1c147d43e201a0110380c1540aa9603295035104034420784850781d000f10315000005510030981c0d0742000d15031102c22035484a1a50300400c400103181d1000c046c011000c90302c2e00d58200c101410003000300d07070b02c030b10007070003aa40710200e108031954507040100200e09004407810742101d01c541c0d0381d03810503042c95500150fa4011030300000c1100f270b5a000d030a81c81d034043d034101c40300a5009001e0710110420030690b00440d005c41a500344c01440f9410001c3d000082c007c401501603940174120b903e4010484424901030140903144950194040100c030032240d8030a0203c1e001000c9076640043c0d16905401254140c00c00da480d20002500140400ea1601e42c0000000b190507500c904c520751900d14115005145005854400141601e4014041030b4195958418085144103c507000d9840b512620704030283c1c000c1d8003030103e85406050b4001c2c025440000070b0720710021070185032100c40d40c04426000c240c6106075415540c1c6141e040400d034040c0f41c1480f00303a016140c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 895608597 1250 895607347 895607359
    0x1805040209030a0f080702060304050601031401050606070f05070b0408010f0e0a050c091005090c0c06360f0d090f060207080d1428020f0a0c05090c0c0604030c060506 73
    0xd00c1d0000b007900d899514038001c105420800c801c400700308000701920501380d0080c15158a030300d02460b020750b45810a000503501c0741c089503184003c010050040500c60744001d842d003410300c0b0040e5a00704945501540444440c010300001151014078040580004c10500001044c0c02440b81c1845040b1101c14908200c5900b2148400000c14000280d110304e01c0c009448107400c503603410100b41c40381202d60300445c2d0302c004031394244103102075000c001c0d1140c101d6200a03600c103030b02d802d0040c0c0f203905a040040d810b0840300581e0007405050285001c001a0044230a440d52407000078030b0103003003035a00c0c60050302080f2690814460306da61401400d010302280d0001304240d90a080030035945904064105081003800d040c1c60100680135400d6070450115035199140c425586202c81c540740401d14100f40042c842d43d5055450a0340000e40001a15001039840e82580e040c08140001c0d03200c020020103030414100f100d4110340404100f150b100703a009949447c0c0c42d900520340203042d600c2c003400702403040c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 895609847 1250 895608597 895608607
    0x6090b0c06010e06010c06060e0118050f06040209010309060e0105040b010b071e020607240e07060c0b06010905100e010f0504060503062e0c1505250e0d0318050402 72
    0x580081e00c941921608001d03101c043c4c1d01c2e0380040381c0d22480140010441403c01d030000500000b18112941a10040c03d0303e010f80c000200003540889c0c1040715030b400b0068080c0041000d80c02c040c0d00801c0c802d8410b24000c00c6004898440c034081e00c10504141000380c0d528003c2200f8400d013071212501501c018041c2520380768154031114020000700000e1a060f00c401c1410b681190744010803100f40e81e9010780440d0103444280d01344441d40103c941001205030a210b02c40c90072030000314005040c0e50551319040c02c82041d64460309040c2200800301d506006000c1d1010407a84e464900c250000034060b80da400788402140c000510118204610380c06000083c13109102450b00042036a600901c251a210b112600c00ca0180c040c0030300c9500c00602003100703d400b195001d60b004e11040e1106000d21080c0e002c211011711103074101c40084501c40300178010300700700818407016242d42107040d11203480c2114102100000154030101c5281c001c4011650400c240c4404141c900d50b01070007000103d0f0118141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 895611097 1250 895609847 895609867
    0xc030f030a020a03080721050912090d03080a180b0916030b040f02041d03040503160f2d090203090d030c05040b07140709021c270510050a050106090b 66
    0x501c030400d00013010b00c091200020310711842414071810b00304080403105080148114000c005001c29245100240151144c001d00d4804a000b03d401c4046c01a04002d0700d0051610110ba10350809010305401c1601d910b214100d504e621000f030388000340214030440280c00d00c048054500390303d007881102011783c0090304101048032400e00592007500010300c011580c405200040040403640c5109410313070303548040000920030000162096070400d8044901c288980301c1218560001885280e880c01030902041c003c0d0050003898401d1076007540e00c02d902c0001520011002c2001941106c01d50507404010070181101c00c210705140e28a081c1400c00c284102480028110310490240c03891048001481d641084074042c034190700007840c01c042d50000381d22500464060350000d2003181e2001e100c1c81d0781c42a220014490b410a0f40850a5148001704440d1000e00c244150160162658028480c0300c5480c01007500403140f040004180018566040c00400391144020303400c20f08070f5441c140284280 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 895612347 1250 895611097 895611103
    0xa0306060f2301031d06090706090801060e0612030f04150912030c02101107080303040605090d0e220c0903060c0c080d0b121002040801110c0d030506060f07050c030f030a02 76
    0x2d40e28007881d012072002800a4092542a000c080c0365440b441090108100220089081820b0b540c1c140c2e01d5515583d500c0400e9800e803451405440d6080d4100f2011450321b1800e02c81c03800c022441402070707906000d0380c580001d1081d0441d52041141d4082801c2d0070100d01c1e0302120751006080703004144207034161a918028042c15412500900944455410002d42401403480c5003002d070189044440b41d980b1284220344a800a42d4201c403098208000f28103900e9010441c04168111940d514a201c55410204a80c925030700003004454030380d5550803a0001c403a03000b00481c0d12104d480344034810b0f2642c5011800c070703201d004255041100f81c40200d000541c10008980c02c9020065001c9140413000b00020710320030005001c1c02d69482140d0003004041c0290f005802164109002000800c010b00051000307403040340c0f28480c1d0342c1c2203000b0f82d02c68180a54440c1c5d410440281805007410306480304002c05510440094078103034455030300b200840c0340c01c100d124140300e1268065401d21003240030180d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 895613597 1250 895612347 895612409
    0xc030c0e0f161b24090b060105041505030c040f0b0a020f0c01050403262209050618090f0d050409050a09020f0907030b09190b150d0f0b0a0306060f 65
    0x9480781103150304001d105050b09400e0101d036541920094501300c03041e04800920022038102e130b400c40c01400050156000c0c40c20b45084403640f54460304600714003c4101d48640c0010b040c080d420f41c05000100729a00750200c0c00b400b40207960340d0240c1e205402e042c042d00c0d1903408000720706648e10082810a550341e01100760380440c0e511844000011815440b240e014a84640e200c40c0000b02c04a90000804503100c801d0882174107103190501c49544584043d001d90780d0032201e480e00303c418041048070b440c9882c0035542c1e102c141c0c4000d076210502020b010720f003043c410140031800540045428800000280b09140d0003e0003003c042004444076804106820406c2d540244521390b0b081c00610b1540c0a50840019884020081d580510b84a07600309601c00c4d1b5000d010940510303000080c0d18506081d00c2518008042c400c10324140200292008d01511f4041a00140305c3d0312075030f1005181d03c0b54000300c0041c0d40308a002044150802c0c1e5843d80e50007250744841c40e0390780e01900351440c060040c00d03029 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 895614847 1250 895613597 895613627
    0x303240a0b0406030c171f0e040804120501090624060305011503090215040f09050f0403140a200d02011401180218061209010c110303130c030c0e0f16 66
    0x80b171071840800c015191020110703540d80e0305c40c5126040060295080c8007000015a8104902170b03107546651a101c3d5180301210001d103000c00422092015a405181a10003203114030008541602996641d001355035200c405001e84608064600380c451541643c80301c044c041a01e001c0082d5898030b541003c0d58100090441d0a2660350034040040d911092140d100d8000d481d541c19544503a21142d00040700818800d1031026450300002c20715001001442c24015605551903900c49095000d03003000f60340c8032038824030620050802e0552000a918a40c6501e282184040c00b00e280f070031003010f42580d054420a00940319800010301c120b012801e81020034180301c180c0140c44840a802403400d1444502e06554402e074040341d40710901c03048401040c81605160000c2c00b01c055440020380d0603101c40500f11499400501c0002c101c002e40020f0300718050b01031a01081515070701c0c4c80300d10b8147c100d500700380701c1d10000604004000071264409500480c1e051004e912420f0b400d4001800201d40001d11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 895616097 1250 895614847 895614851
    0xb0906060a090e01240f0e010810080f030702090a0513031202040b030a1a060f18060f0a0c0c0e04030504090b01030b040e0c030c060415050a110303240a0b040603 71
    0x740045a101c0c004001c00703092400d01050706075844640d5031081c03011103e1078414402c4654034000b0880c0c0b042d160707480c0d00b0030703030392199118070352204019500c1c100010038565801c81c0d0040009000700040150119090351007010310742d16040c03070040c00104035001344203620242c01d02061114040c20803801c44141030309480e1071250b8807582070f1000d020307110b660302c44403001a0100070b200201700960300c0704400400c070602d02600c07440360b2001e100d02e40c0201c9100c11700b0a0b005000400100035100085015944020300003490003956640c000c14580010080784006002040302104200014811002502048810a010340781955000b4807600c240d00601c10f80d241c8030003490000364040e81002e045100010024400700c8075015045070b454490403030741c0344644030b41c0b0180706c003d007012400c850940d56800c2c5215152540b0600544080d44100f4559040204c8011015440c600520296000d01d00055400c1070142070101c19800e101c3e10315036254440d010380c030810442200c14208917400c0f81c941d4100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 895617347 1250 895616097 895616107
    0x6050c04081c020c0d1101260601110106030b04030c05061302030d68040903120906060e071b060e030405090c031006020a0812060a080d1d03010b090606 67
    0x100e090194940d004d40c0c001d50f810842e80b04101c004480c55400140a0383e8034051000c0c0703041d581d10b0342102c03010744c03c203200d40b00c60100d402d5510031030b003607104150030320300100c0c038541c1d01c0c0d80b02d50b1801c80c101e40a4002619440e148010010240800c40c0c000c001e100c0e41d07030681c0c69141c00113900c42c1040030b0b0400500c400c040e0940b0045c180b04146450703003940002c0a443c400c1900c0b201e00541d0018010204504908103491200d007070500080a012140d901803050b184151442840010512454194184100b18090b10340c94038036030260b1844c0d54817030f04001c520b141c9401a8422110b40241991080c07220281d07540780d0000280e030500c06081d41080010500d0300700c161407503040d44190b800c203d070095005801c001c8901c1d0350313000850150030400002501150303140d8007240c0358044642c0080c811503081100b07145400c5240d08481e0040402000c202040d99100d1106161050030b90960f07012400469140d90340346c00042e0218552a409d13002440845c203414009850044000c1103184210b01c0412 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 895618597 1250 895617347 895617403
    0x3010b090f0618010818061f05130f0f0203040317040312241505190306090c0201050f0c0309101a031e070902040303050415230706050c0408 62
    0x1e080c0011000500711a43e0f6600a1085a0802042c092241d020421140114100380781c2c16000701d89070001e40c0c02902d17007910340c840d180e000031144a943c0d1507800c001c010007041c0d96540070181e00303041d00128000107017202030312001401d403144040490b0104c1d1050042002098110500348240f481c00d4052845540d01c8c3e25003541c40211a81005895a01d480350701c41d480d08207000f034010307146c01c0310300c2c000000390b40e400c02038900d109204082800110700b07010100f2404254503060382c4408550a011070401d444800700310843d4403030810400141c0d181d005002040000185003071300958511010352071441c1a441007550b448029810b12502c50340e48140d42140a42c84045800403070004091710340f41c0c0204801e50100b5448201002018040d070400082c940301030307100711400ca0364140c0318942440c5c43d00d2440300032240b9401d001d00c14040c145001103414160303260502400000102e240340c84000d1810030b1002c9030b00050134900b1942c82000180704000b00002e04040710361400e050302d0302c0c0034412070b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 895619847 1250 895618597 895618609
    0x109060b0406090303122d0b04020708090628031d0c100c0c030b01030c03050609030a0c0f020117090714060424141611010f0c030e011418010207061403010b09 70
    0x40118010700300701080611280b147c41018600e611a8650144100d1103c10f04000803481101030082c001d8008009100705410560041c01030040350034003100300d64070f284640622000d040d00c07030480069a1000c400c86000d0500700d803000242c00b604020604100d0351000318100c0542079200f0301c1400020721182042044d0303920f03a071028551056402d0409e50396440c0c90f0142c3c0400f0b0008031100d0145900180580e0b000005440c200800d03a60b0b070141166a81e204c0843c00c00244206070b0401040448000340d010144d07403107a000d421084020204185456099a00303613a040b10220b104a10070002040f2480321240344400051421a4803d4420400c2d40c068415000248601440c0c01011440e40000d001001d01034000c24002c5000340c4040304080700446940c5030341d00c2d011300030a9030824910082441002111510a010704000e9045000c00703415035a69086410031550070310b40b0419051444d641800007000504540c10703d22020304081382402e0306c50105000d451800d00c0b0109020031296905 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 895621097 1250 895619847 895619861
    0x8060f0c130b07080a0215240d06091a071704060e0a021903060b1f030e011d011a011425140114060a080312090a12080109060b040609030312 62
    0x89542540d5504520b483c10710b640003600d007403025000340842103000055040c3e5240c865403230f6150440d0010f000b000301410510507110308030740241100004100050162050902041c02942900e526810041600882200040142040000061880f41030343d8500140c0e50300180d004030702140000240021a02d09405010f0280d801429002c4104070f4513840550303041500c3c018241404641001d00a000590094440c2140b11125621440da040c0c0d202e640850b03000c0c2280d0300042800901850440043c0c404040b9800d4a40d5590100a040a200b004ea016400c6801c0c2413584e0404100c413014500703401080c51000c0400b205803d14035100201440007125075a1000ba40c1c002035144003000c50082c881074044400a4007a0f070701042e1a80b070110951401c54188400540c5801c088550180e48c801c000340046240d03102d810079940010b501000781741d04030140c0b503403901320795850500740e801035552540c00300102502c00c10050004907481020001580c0d018103180340c0c40000401c1a200070565 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 895622347 1250 895621097 895621109
    0x91103030f0403060501060e060d0213050a0f060e031504030f110a060e1e070b0d06080114160509030a0b07050c101a060c0705011407050604030309020a08060f0c13 72
    0x41e41e94203640701c44090400c0c0d90180008100356030701c8060a4800300358803c00d00b603108000f484441500300c44c540080158054414900400640d81c1001c580e20030300d150480b80f40781014460501a050b4020411590348000300c000301005841d0700003881031010003038001340c100007072031446509041c06000c00382d082074004e001300c4200000909202000340703041e006a038000d008002c0c004040031180078080f40f841017004050814907140282e1100e00b03501c080b86110b4803644402000603000c3c2c3c00e1284140ca407042c01281007040c0342c514601d088100a82c9443c20a020f000c3c01000300b40c1d01d00090f400340072370b40000710f205e0036200c0c01019102c6001f05592107090b8031694410380911441600003001d0744560203181860b1103080307003c02c451405074560044a0381d012503010403042d07200d150341507900309114020b00e160640390b41302d84e404d02c00b08480540204e508c3c0e00200c41103081a000100081c803443c809403070300f824048401202c0d01405040303600e003810082110403400000b40065002061 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 895623597 1250 895622347 895622353
    0x908121c0c09031407170a1208090c03150403020601051210020304031b050729030f15060f0301061e0e040902061b0a02121906020d060f0915061b06091103 68
    0x41d89040c49503508064051205600f800d510380c02c65007540050101541a80710507480071000f2300000c122910840205403251920540508001c1501c041c4089140401e818412260301d24007130901034541601a0300c154010058042c1500b040f101c0465940d50700c5000e9131025036240c442c5e05044910282001084074444c455410f1042001400124502287e80040e01d45c0130390300b4880c800403d0040440483c45c503c05013000000d414482c03020905600219048081742c15815080105109400900103c4030400000005200c0f540d045603d42402210680b040044aa8a113600034008440d20240600650b100c40c6d59608654824003521065601c464240c21001c1c03281d41010b90b1030900010a0780034202421550001c25004660745509030265020001061642d6813100001d510400034a00015030719800460041401392801c1c0c02000c1d00175002c101d40b00b411128145000300d540c0180140706078811842c10301601800d880143c3c03034000900042c160f0a5042c03000340400c02210460b13044c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 895624847 1250 895623597 895623623
    0xb040204140f030105070509040b1504030317010506043014031c05100b0d06270b120c0103020c010f09080304120206010e16020c09070908121c0c0903 66
    0x160300c0c211681c544070000c4600908100246060500720b070010703501000001c60800c000c0711507040c00c1e0440c5030001c401400b1100d40e2194405444502d030007680048000482da03c541343d540d600102c5005014010440f0b225250901d002508004680701200c40c010382d210346007003044961036000002c0352054104c500340200000c0799804039125072200700124252002c60f0603480c0901c1141c884d562168408000d000452420091003054541000c003e2040341e5407590f9002c601c40754084102d01c0c600064480702c0c4800b86a40203030700d054458007801103020b10101c45868003030503000140d504080b80c0c203080041ea20f64613010103d0142c40d542c403400ca5498104407050b81009503440c000c62045001e941205241040110104d80b61802032052030141408000440e0b55840041055180e40c0803500444100e404800041038202c002182c00902050000204102104040c018100da482d401c0c000c00b4034085084c00c07c2d244d0700000d140034040300c07683d440f85030b143c1c2c501a0ba944000b5641140400d0703c0d403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 895626097 1250 895624847 895624859
    0x30906240a08101a0901030201111c020a020a0803070b0705030a0e03030c040603060b04120b13050a0c06140a050d11073906120c1404030303020408060f04051209040b040204 76
    0x141480740c0e90210f040c1c5002440084030815181c1201d220400030a1515664038503001142c4410204901c552030307006200c0008100c820741015610800d055401600d814030740c0380108a050354042e070000c4400e41040000c180018200701e00d143c0d018045040c481e40780c6e02e501c00c500c40107100c0704200c99040e00c80042409491741894000c1c0040341d0603583d00780711450b2169407041050040d4410b4a0344135041300746010000d220640e8241c0e02240201c5400c82710565504d84525100f181081540c050307a41c4401071100715030018064042100250001d4a412541d41c001005413064a4410701b42541c0c503100312410307000070003c40b10043d802684002403004500b0601da5003242907100b04800403940303001e0804e0a50f0482c40c0204031441610f504031a401182040405801500c8940f000c01001c400b035110945a04400ba0025600a1340d0060b03d907401c0c51445c0303280000117082c2c0100345268404005c005500001c41083d00302e0111142c50702c0c0d440c840041400780480c100d00c00d90081c008500840c01c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 895627347 1250 895626097 895626103
    0x110a030314010609030506011215050f0a15080a08070203120307050a0e0a06170a3c11030105190b1801020d0c111005120c040e070203030906240a08 65
    0x100d032403078401e00a2182d0b40d8071001d90740e41314a84802065500010300405c0402c421103107802080b401806441084039100c4407003c2142d0317084541c0300c80058a0010b0108000040c442d0608480287d0320940032a410a0005907847c102e50b10028201d0000141c1d540464400348150038807401c00304240350301c81c10039810150a9400005600c1e00060041c090740140d850308400d01c1c401c40703503035458091b2040ca01c0e8442841200c0020564030100791500c60b6031414061003880c0d0b480311226021620741414240d41c3c042400f07080c503138003040200d04010440b990411464101d9044071021550104a842101c030306c0203260a83c0e80c4111126040404c0740c0c102180c40b2081c0a44000c401d9003510025038040109a818540c4044068440074040804c0125414150610b980b80201070030054185480b0103c800c0d90400110b4110070a800080340401140c00301c400107a0300440c1d44e001a6040d8640700c000240d07107031802030007410004043d040b900c10518803031210888540015124a4040e5220241d5942d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 895628597 1250 895627347 895627361
    0x50a150203300702030a090603020714070603060f050901031a10150504060f0807080601110c130b0f15030f130b100e0a06060905090a110d090b0a0b061603110a0303 72
    0x40b00120702000121024400310848040483c0d90300c42e000218148282180250441001201d0943c04028403100036601005282d00815541d90041141402e01740118200402c6500490080550b440144005030800c000c00c003a20105018201442c0d0700c020b2442e41000160303115041105040e5130410307003e0361000045c415a07045440749585404690b10850f905103044450781300085080c804240151310400141020300085022a1300007004000007034040d68146200d45c0100b5035404030000541407140340c115040c003046940211044580e4141009c0b4400288148841c8610314002000007007842215070240342c014940000030300e49225030140c123610f40c0c0200c624402600f00014040e50541c080d0109a8000d42e941c0aa401c0c9000180039040320058010418107444040b40020f1900e050f01414100d030144030701241c04400d6003480008000050541c800c4581081c6040c0340caa11800c080b54071a100c25004041011614102114000e1560400d10307040d009000c020002c1c590305411501c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 895629847 1250 895628597 895628677
    0xb1e09042720100f03020409060b03100b0310210f0b060307170c0402030a0f0c02150a230411100314060603040c170a1b0305011401050a150203 63
    0x680d4242c255000c422660310358030001580403010840c003002413031140c00d03038510803011401d015042ca034980400005807516030300304a82c1440c2c040104142846410102c400400030700100c94a1801d0645114031322860700d0103481c8811301d09520905001c88040b4401070301c2500419030010448852400070340350401a106544207101e036080c04130700690901101041000190020b0201401c160180130280d08028210b6948a544850401da5074406004131088610140d020b010103a84800700c0500e61003024100001d0103103003060000015407110720700711502c0c40100b001c905560360352a01441f10111099601d0f08a8900d0300142140c07900354000c3d9040320180c5502d41d00e5503030b420040c80f6003800211000381110541440030004404d245900617043d5100100307886001e20340c9c1d1240c1081c801da5085520515100040c10400d00c0400c2c401c0200009400d0700661036545845c00059024205000e2004841070180682c191540204200d51283e8a500f086180c0c8072540803201981c1055250741e2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 895631097 1250 895629847 895629863
    0x1060e040b03100902030f1b03100614010522060503190513080304170720030a031e09030f06020a031d060a09030e180106090b1e090427 60
    0x6180525080c0030300a11020050010407000114007405070140404000582c0c041c020b44105007150a803c1c0004840c24290413030600344c80d0030800515180040e0b4503004260b480c42c0c1041800a00704e440a1550741001c2440c2150b00d42c002c2c1645000002410300e81c107407517000703902c40005030260406c02552007614015404d4014151110700c00e0144c41d03044950751108286241c1c640c00040180c1d018580041c0038a4906045010310040f2001542c400001601c0c2c01101d80210728416200355181e0460000a8010341405102d640e00030780b00c4920880499501d0340d0303070841c0300b118500c0390030036200a5412400311440398009080200082d4400c0c5040f82c0000c0c00c01d041040c26a440707079041000c03049980f00804595807641c601d4002040348460407001c0080441c1005560342e200034690700500608009480345501d8584c4c05000041240d006440c50303102801507104826a01c15161039401107500c9281d031392204400002e00a09aa588040c200d0701c0c0a80005c108111041d501034400d44a0131030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 895632347 1250 895631097 895631117
    0xc030c031715042409050408040506030112050c0a030f0312020f0d0b09062403090c0d050102190f0c1709041401030302010f02030c0405040e100204080d080624030915010e0106 77
    0xb140403c00610604200c0307080706800108480d50b40395004580c494040c8e4980c0e070803d615100019801d50003a488447c0003204442da81d4144103090010f000401804c84d51740f80c3e2189155140960321815100240500c20040c007800520032064049a907000c611040e42540e030350070394200100400b080c18540d130103000d0110000d0024107058121904403d9151050144d504e858045c4c403425500080c40c42d00903019030741c04003185865013000890224030500000d603e59400e401044001002120110200508001c85000d03c40d00031a054181c60b421110310207140d103000320310075601c1c0f2074419859042403408800340c1051050700c412030305032031295000340f03c14011040500c0a1340410744d0b1104070240100302c100414505940094100000c110680308070b091400c141c1002c07071b003090f0301c0020650041401c95042e80d5000e240b1590111084441c445801d03c4050b0a500f6094809250103003004008046584040100300c2c8592003041c0500394071082d038480000004a5000303210b0309011543c0d41071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 895633597 1250 895632347 895632371
    0x60702150912162406051309172101060206070206010f0b04170a0f120f02030309060402150403060207030306061e12110c060405060105100f0c030c03171504 69
    0x1406580d0303640452150b500307003d070a0601980414102c4021244405101c812201504d0119881c00b0390244020002030801e15100500c0300d241e8002d150851468900b0325070b02c0000d1603154200303c0d40b5114441351a1a001484149000f0b01d42040541c01d85614660000903030b5940054100e1040321191b080e11007599880e140e9140c1d43d4954014001d01c900d05110600044005a01c0c0c420104495412030700703c3e1805841d80d40792121034203400d90f027501089010310f96070b6400290304c07038504c2000e200030352031817404620840c0c0711580034000a12070b00000c1c000e5801c0303416000649002d503401c00340031540c40e512481d0185c000d042c80d03c180d03800300d26040310a4640e002614100c10121542d903c80303c201c20b40701e2280c00001c01003403601e0569160b0a01085490074020401c8034480c0d80b0420040c040fa50409003000040003400750800104000321a46a02e0b0304d500c86500000d180d071508104d01c207088686410303145060345201c035030082180d035410481d01d4289004c80300420701c029038003040010000c003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 895634847 1250 895633597 895633603
    0x1050916030803013507060908151602010e0f0c09070504051008070311040e09070e040507030308060d060f1401050306071b0204060b0c030703030e0d0f030c110607021509 75
    0x2100150042c0c2d03043c0010441c1c0c5510f20384030041024942100422805950840d881d410014110240140d00810050054680140351400913020b903000070000d51038008440e0079610b00c0140305008144d2000c580c1d4815034001d402000094224006644800000a00c82c41d40c40c0402800c503031003045041c02088082d030003071044038107448000e0031100d18050b10f07403000d850800e8040c00c400704160382e8205070341c04900818043c1c0040d00082c60581d40c03d00f1300401140c0303004020b4001d0200310301904140b20010750001000c40c1101d074142004480343c0d450900140c000401600090091406c1060004010980c0c1d4400d01c00c120000d03e04400d2a62100103250366a0400c581c1c400101d004000849140440d04801e20136503480140b02280e09511100c07481440d8200c4008481c40e40e10114584041503014011820004800d0008241016113074070002e05541046585506055603aa0015a40c5104d001c0c80d503045810b00040f1400e038203010400075034802d4010b600000005a907030101e9007400d004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 895636097 1250 895634847 895634849
    0x12061f0e1302010509030a1b030501060b0c1c090909080301030618020307051c0204020c0105090f0a110105030705091f0315080d1407120309200d0620070501050916 72
    0x241d070044036601254010355095200f6000030360305120314840b2000003041c12038a00360b445902e02448070035a1035454040d01391003454210b4925148140a5041d225000003002e10b03112076420a003941c5401025425a11f01d0825017003003641c00e080a404100b4080c4510046040380e11442c010481190400c103950307504a2100c80080d0725411001c4100201c0c82c00458041d800502e140303840c81d414699900003012a44081d068092130394440d0304200100d013041c0039849051882a000e0300c3c44002c00c0d03032180b01609103140d042d4140100480425001807044064071900480504454000301a044406069254154082c00028240a202402e41c0c00d13001c1d54030225003440c0b0090641030660b1400382c4201c80001501c46a542d01404103001083c4003080c0124528042c3d24001020101030404078800905152036070701e410307009007840c18281c0325110540703002a04400300103440c040484040c041001000001044a03030b0100e601e00c00d0103019844140100400400c4509120888501e0300021a407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 895637347 1250 895636097 895636111
    0x320010f0806130626060601140f0d0608030c0610140a120203010b1009061205010e060d082b0509150a0510030b010314010e0c130b12061f0e 62
    0x14840104810f41014a41c12810401e54000414050307100d942c05508000714443c4408032072541c803502135a9610174032401d030700200e0038a04405028500989007070507101d8061600389150001030090010011a0311078030151004109495680d0b10009920b5a904419240c0c007240c07900c071030b00000320703c440c0e00440300c030b0307258060103c4441514102d1055820310480d41d00340d0f0103540b0f8400c0c442071951003039000100300309203031141003e0b1418204004c0851041002c4618000c2c90074005003c5400380d100c4403a400b60045a4000c4c0915a9180010a41c020131005a55800c898003201c043c2c81c0c1105560301d003001c516a8100466900c094000340e4500c0d0003200302d00503000580102d20121758580207107620202082540908a03902d50301d075100c60000f64019940f07999414090b50f10400203010f181c1012511a0040c83c000c882580050444164020f08003210740c1d80b02d5100c01c4544901d03140707444100500d02a82e041e0700d040313100c60316248240e0b000600c4000f032045004c2020f5040c0740104c0d00500b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 895638597 1250 895637347 895637357
    0x306010f03020f04020d060b0c07090207020a03240c030227101d031b0418030e0d1a0a0203071713030c110301050412030609051302041e060320010f 65
    0xc5540c083c001d01568070351402d50019001c00c800031010015004100081441d14491784da1008907041044c1400c0c01a0032000030180100705200259980600e1001500e03006200d80c410344460240101100c10080c080d00e0344581818582c1107a550154082e280540761080f05030000690400e001b4a01000450116030000c800748a40e005a03104501518500160501c000560000d61000910300350700b074119444d207115030300384021840c140340c040c1006030110301d550f020940040f59400340080615410103809004120541030601451540030b4400100808a40015060a0034401c010f0f500c101d40740d002182c0c02c80d20003010100b588010398480d16a0b401c40c05280e503601d036811505c13014110000c1c2d82440c032000b140b40880d6420f01c03a250089110345890b00c412494100090180c5001e984640071107803600d0100002d8403e0000911040c81e4100c80c00564075401c044a00c0d80000903038010410313649884c0c808000c000f012800f408005000c52001c0d90b280d5491001110844003440c0c607200018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 895639847 1250 895638597 895638599
    0x509130e010b030f060f09120c010b0a050915090604022107020c060c07050d06020c06070201060f0803070b0a02161202070906092a1211070210050408030a0f1e0f020c0306010f 77
    0x40700314040580041c1410300703a230350580d40380441c0c040340e41083d0000811030355101c1810b0607502c1c000410b00e00625050701c211440c1e00d403245d003e103185a0a000c860f4045d042640015815035600d07411603507071001903800000d4440703024051701d1100c00101d42d050054807a0b0480c1035820b00d0501c3c242c42004240354000c28005044c0390a000c81c80700445400c444207502440030820801007808554411f07462540001461490001501000d030015404034106801c200803580101300c12195555209150110159940110200c2c0c40000120400040c0008014200b000811640885e00308115168900184501c0c1d480b40e110204036400d885142c00c5100801a44c01424001590124690082810001c0050a4444c0a8410380d4507085400d28880320010b00380085141c8030074a07410421040c0360282c100340c2400d6540340d070ad11403c8825400d124096010307030441d904c00d20000402c10a82644240881d403021406090880701d0500700016015402d04810f49090000300c0c0e0381240c2e4400c421010311 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 895641097 1250 895639847 895639861
    0x20c0616081201150210110901030203150a0602030706050901020414013617030906071511040608070f0e0a120503040e27010612080a0509130e010b030f06 68
    0xa55241104907000e110a0001580c0c10b18402c0a4900030000c04c52065440c1406038002801c00003a14004140d00780362000c9502201549029101c2c500e000303090050741e0303440751150003441040c000c0076258014444040480e2095010018000e01da10400d414031064442072072043c20307030040d40110030390050400b500452a41c031481c00c03000160216507092200720f09440310741410b584050410310020008100811002c5043c1300c0b080024070080c40910300704401080003c110303124244001c0c14448401c0c1c009c40c00d040003644203075a000c450069490343c41769141c40141c08200f0840d038a01c0802c2d1440c0700d4900a5003d501982d030038200062945840c076042810a248054400c00e0540c3c1c548000c2c04041042e07200c0810f054000e6000da05001e03501548030b0211034101c80540e00030700c0c031641800340420100744c80941e0412141c0c2d114103003179141c40c0b4201e001c4600340240e423015948001000e02940c40b03440c196000703145140c50b060082c0902c100c440107054fa2030b407032481c0d0b400103035114400040744 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 895642347 1250 895641097 895641127
    0x140d080f2113030e010e09160e0108160311120f150d020d0215040e100e161409120312060301051003020f060a21050a06090c020d080405100906021801020c06 69
    0x529905041c140e0342601b8402c0883c1c040d800865240100c80d00801e03a009455030803080740001c403482403070182207500d0211000c04003500c8107580744043c5501e0f41e401b4040c41150b4001e031840d01a18212031025440c003114035402c250b0081d04c080e296440c8080b925040d81c100008010000780c0c024111070101d80141c0c0c01c1c46141081c81c0d101228110043c440890030044402c1c45078016400e519a40c0c04050074001c41e001d0320140500a141a20400300040742280e400c20380b95160041d04902098441440c0f10100304400c9036203410300100c0c003000810118460384a07a0303d84c0105402d078000c0010b6528a000c902e40d9403004c1c04042d42c00800030500c441c45240402c0101014150b510300203250160740b040c0d4084507840359049404060b181c100f0410f00d4032403403042c04002c00210030244194000d0310b102948810400d1030950400218400207020300074100940e91345054481401c00c840b41c02802c2060007034220000b400c220389000203511509620004008034103120082c15140b50010301e800d8824 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 895643597 1250 895642347 895642367
    0xc0f03170709290d0e0705090c04060f121d24100b070f020303040b071b050a0302010c0606080f070911211b0a090e1e01140d080f211303 60
    0x152407420000c01040e004a80501700403840000c0c000c0000e582408100007080744003c01c40491820701740000c105880d806500d5141c070200d1030030281e500c211614818000ba0072062040401003070031550414101c0000981c550203c52240f0200c440f5421440c041c0f41030b030b5803d0b1114907080a131500305000b80080c0d0310090040510615055840b00000d6020904681055010307640007400840c0c0301043c4000e4801d0704100303181920040043c1d60509001580c50700503070001071304001c0246001410000745500140180102408803060402d014140540d02d00581c0222303000036040042c1c1c0c5100c451600c00390f40121244030305546001c10084464a0425001024004140c805403241501040304000906001e0309990364511940e00303282c0654559079001d00304000c245000c5d100081001c0d650141241960812228070869001e040300040045010080141420400249400a50f160040207001c08841c0d035a0311980c801180244a0303081c5021211007030714904400003003000903c0b07000c41d25 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 895644847 1250 895643597 895643669
    0xd0207060e1309030e090108070f230405010305030901030608010e1c0203121311030a020312180303031e06010f0f050a0903080d0903030506061611010c0f03170709 72
    0x11a0a20001c2c2c40d2415650700080c02c0d008030b08130044040450520b10031030750140060380001e020051800303400700701c8000507220f20080d4003216150501d055031b8260007401200303802070052040b540c40c2e0030460784a030f10400a440c007092800a00140d1400c042c000d030359007035814030060461540400c0500c043c0d986005150310031404204550380c81e0203180030046015150302d40301c5001c42050791406680e0089032501851181e0703c0084070b8001650000350080c2d24505403014184c480441039051011240051203081d03050002004120321000304102204c15003058a11042464413000010b5400d4141482100b0001e50300d01c0041c0411070082c002002c5804d080c0c90b04002c9165a9294801e0581003540050b070500c0d11491000b00f030540c50b000c0c880e003000c0c0c11910503142c00358200e143c6003104c40086000f80700c0e064104280085030700a4480c9518150008100d0f007413104503141c0240121010710140760700405000200d18194442d0440ca800d94081d0380c1c80c851191800c1c44440942400d800d120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 895646097 1250 895644847 895644859
    0xe010f15030f03180906030c120503180f04090f02030105060d1221050705090907021f051e042a031a0a0f0614090105061206010f02010e030a0816020d0207060e 70
    0x240b9400c0540c131401050750882c0061101d08501c0c0044008000c0e0b407210340d80c01000850107011610202c105d440c0b060106403646510051100400c4100f5a00b4907220b078010701c5d0a10710741c04d100c5c020400a9925100b1002000076503a13540801414141e40c4030080d008040900701c1d1210f40b402106502c448805091001588070000c9640d01c00340c81c0e08803125070004501003084499820410003d5802c120302d400903101c0e81c01c05008140c1d00400c51020410060b03141c0000c102401c540c58090750740c5c188a005034980c1c502e0706040007150341d00e00308040b040e0140c4070307061001d2495560700362000752680038480c2c2c0d4507400c288000c14446d2802400125603c0c0c1d540041000224891044500030700320381e1424180c0400c68400c0100030081680410300500080044c502c01d0410a030513a540a03500b402d046080404c203140481c01802e2603000c3c03c0c910b1100003880c041058000400c10b1103200310384444034860050907070490311a40b4001d90600982d00000c01800514080c40b07035140740500291074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 895647347 1250 895646097 895646117
    0x403020304030b18210d0b060f07060912140d0b12060907060e010c080d1104120804240207170c040204090606110a030c0b0a090503030a0e010f15030f03 67
    0x50041005410f840c16519600d81c405031681d2880203000b80300c2c44643c3d60704242841085e540d05c52019100d40c0c41c24030303001680e801d0007042c19036910007600d0303c142200c0e29403903e80403140340003c0280014181034404000640d90703c0700c86d620a40b4400044074401c0ca4003403e103a80c060014010f0328228030000da0012070075850006e0803104000b500e01c501d001c800144a11850400060100702a00e031465042140c58040b4601241c07000b01114114a45141c00140c00c468041d20113241d030199400c100c151207020a00441441a000090000e41e2408040b1104d003406d8100c84500c0403540642c8800941c100e01c42c01c200140080174a0850b10141c081580c2856883c0c0700007404903405504941115540e810007400410340c88111201c0860101004201d44051610b02a0010040c50b10040401c0c160708001000316200360495018541e11008890b1a4102018014082c0176862000540c540c6030105181542500c3d0103994080c1c2400102407011606645440b1030000030303104103805020301900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 895648597 1250 895647347 895647353
    0x2181f030b1c050c01110c060306100e030f160b04050d0f030e03370308240d141005010b1b030702060424050307140901030f060f0317040806040b040302030403 70
    0x2520b512854810b10203004042c48841c0090001055815100000e5010b6000000d440d02c540c0708480c1c05c0f10048410101a9a0640040710a000001d000c650503001d0154a030b59480e00004518041141d003403030300b50b00a0340703031103881b040b500075031090b0b0340e01215284500f03000ca07000d41d1810b54141c1c064904440c185980740003003441e20300180d80080900302500545030315010003420300c00c41d0306408104a0104100c54170010614000584400306103081c1d00c0d00078891030100c010762004040d0140448400e1401e6040c1641c540d4230441d4221124040c01c1101c0400e82081c2c403900d410b0f90002e41d56141456200045440480e90b43d114070143d0344800c0090070050303503c01000d08000d00d9140c1181451040402616103681c840741c440c3d505001d41801400100d03030b00010070030039096030543c48076220340c121001240074101d03040f1441800d51400c503010442000d00c0702c50f441628000c3c40515101180c2d821044241c0c861445940b4040c0c00580100d400141c0084902d500300e13019204403410603071031b0340f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 895649847 1250 895648597 895648639
    0x60803091e01020f120d0b0d0b041209080d050415030e0d0509061e0319020901050901031107060e0115080a020d0204021303050303010f0e06010c030206061306090f02181f030b 77
    0x41d0622000a0340480d4400680c46c1340d00070b010305000d058601e0048101584e031001313021500504010540c008002401c1c07144c521400d81900100050021103103094820800a0515401802084440c1d1002020507030700c030b802030013401d907040c0700040100b400000039034045549070468200c507540100104859076001400448000c028054400807580d40e060103205903c02d04030f14400d0440840c01404109900c2c1e030850140c41414100307007800309164881c806020a13601c600c0400034982c501c0d00b0050b6030211815841840c410542942e1500d00c10748900c0c140341d4a07403d1800007540920800e200703a00504041d0080c0500d140441000030070141ca0b0b0782c441d03056800903040390741d00c4400c1c84070400417065403500d00383c0c00c60b0080c2410f229590041d1402034440a000340680d000d402c0384a482400c000d00e80c0c1c04180100701c03410301000310348400d071600e038069404011540102e51204c05280b0300c510306040000ca00811420703000000c8445c4c02c0c8107501511980b50401d5000e901559500b500000368 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 895651097 1250 895649847 895649863
    0x2060c0a02010f05100f08060705030f1b0d0f06120c03080a03020412030c02040b0a051c05030f13080d0201140a0509070e0c0a1d13050415150603060803091e01020f 72
    0x421005041c5d44c1802d04414652102d50700180d59940182c0521018039006400c5940150294080f0ba22558038540d00d08203a1141110b200381000c8001032402102e0100da12854141a0120092140300c2d6204503c02c80d0190740035000d804107c1c8484100700060031040204050005400d0160503c0d0340e90101c08226003003c107007034000c51030000601c0300f185018442c2e0400d01c00b00315000d060540c200703001b044070741282c50b4100c542002081c40d100b042c80820016200710001155203242c0d91150304511110b0b62216211b6269030340300f0f001841100078018040c4000008110214201c140c0e00c0118402c060280980b40c105180034852010030100c4094607603a2180300d0145c021552103101c800001d00980e42206010507c000750428000301e980c4a0b1540080301c28100d402140d292243e0030804a4112041d4003c0007152902082c3d022007400040c1a004032078480d1410094680d81e010403075103030f00c12204000c1d84070210f030b80e1044041c1d0300a00d0400b400d4006104076003194132800c032030360f2600d158 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 895652347 1250 895651097 895651111
    0x171203090a020a060c050c091e04020a0e0c13080a02010c120c0803010321030e060c07020402090306040309150503010503070513020c011401092708071505040b0a0506010f02060c0a02010f05 83
    0x11900c1403080c05000c020340383c7d030b10a050b580c590991512003109200300300002c0c54901c000241c40c000c83c1c02d550310b800ea03140151030a44131200030781c28420791140391540b019201c82603000c5540c000041c6001c001c00e07440700d01ca030180c540880d10780b802c0e513030312200007001729200c400e00119401100c00f096062000d140650720580b407810382c1911440402d4011001e07003002208050400c1c80d0034260b02e5022803103940003c221803e483c3c41d40346910004010f400350140340da8142c03081d01c00304824075074400555804c84103125a80c401c40c02120904441038402402000d1b0164402c4a08101c2d900303000c00041c03044000400c005041c5200821154207403006100c0c9005840c00c4040180451000344c4100748549102010002e001206407560710411220b240d8080c0c0200d001194603001d0141700c20740341140c2e540461301040203182c00d20300381c80301500a80741000e2041c503120014225501076520803800e64400c0c1c0080505507036003450011107920400c907150865407904400070007a242402a1801011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 895653597 1250 895652347 895652357
    0x121e0312020c01020a111c0e0324040209010506250f0f0b0601022a090705090a080607120908070609020a1a040305100b01091701090c060810171203090a020a06 70
    0x48a40081c650039100c6c840d16400c2d0845080e5403100010400300c9488086c00b41812440c00707109000003410700102e55294220303540b54800300c51000c0241c2c9640e51003588201c504403013a0342c075142802041d00540401c040d00000c10350414010400080b1a034960520400092038901c2e960f549030184a0181c560844108a4020a110256805020303500302c0786141104c1032030720112901480759103007000e40500c0c000d00b01d08002c117007034900c90401c440d00100e0143ca00d03a0300380e0b81c450840e59900030403902c2c000043d6a040a0b2100140180600c141c4503400000342d6081c50241e484a40c000c100b00d060403a8882c48154001840081c0311701a41540001d400f4210f0700c40340345091150610040304594800c0c60b20f00307845480d580c1c2e0020400c3c8180c0e030010b19815562542400094010040610041c0117a80a000c000500d00d90200c0aa44100b240142d041e032a180c2d40c008003081c03c0941b940c1400260420b0048205c0032582a015591000d05d5038229403401442d40c0203e64004440e810542c0052 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 895654847 1250 895653597 895653607
    0xc21031e060432010b0f1b07170d030605180a1e0c02281e26071109010e0a021813090b01081605220f06060207121e0312020c0102 57
    0x1600c000350040c11603400d0301340740080b5595a40041d10440007c100400c01c041c000c121505000c121000152900d140d0710612190502d04040d501d00c0007040500c0000d007807a5000c2494100b22030030400184501c410340200e0b48551003088080c0c054044240703c00000039902e01d04000e024020b1071b8a9a2040d0040c0c0241b81ca00d2003644088001000d030f101064004008000000d101c101892600f03140105030382e002d1003020b10b46083c10240300382c840b5400300140d402c0f050034040c0c21030003800362070710076001c54120300140c07024841812400d12480741091039050010f1003403a105e0700184080020000d59800c804011400a1000c3d61754444000c540d03a81c881a42d01004015003080c0d0150082c40000d140b110b1a004d500015500c450242c28012084079800710f03d819626001d8801107401c1e00c0061060410400206000f880b0a2080e4001881003ca00040d0592140724211340e00b9000b851031840a501c003c402c44611214030001c5041140702c5071130301c103825030b20300c06000005440000980d0714 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 895656097 1250 895654847 895654931
    0x60902030f031201090f021918170a060b0d1a0609130b0105060f0c0a051e0313060f03060e0f060306180703020d0c03020a030b010f050108010605030f0711030c21031e0604 75
    0x1449e190001c4050400d2143c44001e0400002100030350301d940990301044510304580440c114000020004001c45605821603165690f00b0301c1d000d12904007685c4121320390340ea1001d0701030f4640e01540c028204011990040c071042c101100101002d20100030440d180c200400c000c00c0c0b030180c0300001a1900c0e002029064420144c01909140700e0130158010b5081644030100740424031202c0c0b140000b8424043c062847c814002c4e0490402800c050342100c04501d050b19403020780c640d045504602c0380c028000003810071840302c0003032540e017035419008181315421f540c28004040004da206071581c840d00000000103960385a8400095403050030001455403501d58580d00c104002d40040d410f2109440050040a40c01020b90b0360002c1c2c2403884503030544031074a0546038040c01e100c151140b8080004e50f041800d0f40003481660b00c10030581c2500f4064061100d60341c4500082e5846007a4410700c1c02c44015400c2e11035506504408000c20000b0000c1c803c141d04860b04000c5840040c101840075210048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 895657347 1250 895656097 895656137
    0xf0f030115030902011d01030b1305150618060f0c0106080d0e030705100c020d080408160503060405070509072703021216090f06030b04060902030f031201090f0219 72
    0x1d801c107642400c1c4031624141d400078107110104618060050241c44c95100709a100380c20403d51284040d000d11859841e4007411000f07000201c03000018160080d001c9541410620200c1e5070b1104110036042c4404500010000c4990040840b0509070750103006d0140a13070b00038400c5200820302000101502c0d010400b000e04008100481c02d4440e07041848100032075240c030022071002241c0c5151282070f0344610301c0043d11440200c1009015007402003008030301c050001480e41c03040c02041480c043c0d215526030170982d070f406c000c440003440350b041070b40108018103001d4002d9030001c04a083c0327040058500607155100e680754011701ca4030165010ba0401c19400c000a9824000b51003401400e0714203640c83c00c4c00c000401030b2044a040325500c40c86100480210b50080010710380c41502e0b4405402c29040540c09060b4014040c2e210b4066440c0a03034694100104a0f04814204070701c2040716032825107044d0040c24800d6425000d542c003001161004400d15080941a40c880c1d190b8041600c00306021300d413 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 895658597 1250 895657347 895657379
    0x503030f0717040519030216090b12030403110402130806100303030507050a0207151106040f0c050303041809061b02010f0614130c05040b0705060106170c0711060f0f0301 75
    0x20003a40002c043c400412804a904120b444540855101c4041c0d1458200d00d883c0502c070010742075080da10780110300309203590026552880110303082d01c44c54418a1401e40c0380d02c40c130320000744000d0010f900c201050505401500c0604420340760f50492560b0f44036540d08080c0704648040c0d400c0a025414804c154052192075001006840c016003401811300c80a07540c0da106000e90351103420f07542d1000c190140f04e9042c40151801034019180b882c102450000389854107100125450101c1890102e214100003060f50212a161410650b14001c0d00c81c20100500391054141c2d0304070340f01e44601141445e19010f80070076450340e82c0005004207460300120110382080c1c008a1158681048500c142e6076070380e44880c02c4418031000040c0598003030009072041c0c4501d60011400301c8001c1544800d000004c00c150b8100e07180c9844c0c003210110742034442c0c0060441207585400c000c60500507900420881c0c6903031030300c14001920291600386c2c83c42c3c100d41180c0104134039541010340080140244030342805800303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 895659847 1250 895658597 895658627
    0x390d0b071806020604110402040801020d0506030d0806030a060e10060303021506011d0108090304080105040c0801060b03010509011211060d09020a080c010206010b0a12090f120e0307120f0503030f07 87
    0x6a161824510b0094807138201500140c00000e8084021a441c2e50702d504940c01000da82000319950000d004040c0007401044525130b00c81c1c081c076181080d007540110080b42c460b0308000c0151041c2145d40c2c0d0f443c401406c1c501caa158140c40303014010490b41a0500c102c4000c0d40c0650001d10811040301d102a00c0c03114000c090604000807190502c01d42205840421040d80c003d0074040803a40d1850441499070103158441070303296003401c0a00080c001c141041c0401d07503d110f0000d003d8035496514105051201b07105003600405244010084d001086805502c22407280c401024406201c50000d031294020104491115540309104c00441c0707400d03401000181a0080a44040e00d03030200040d484910500c1089000000021000c200034480e80504441100c10082040000524109102801410701c0b04a0b0145041080100d00501a11455a0b5404018001c026460600076002039280101c501110f1a001d468070585c0051424000b8500c0360003000c1c54400c540c50400c0c002004050422508 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 895661097 1250 895659847 895659887
    0x218040b1b04121e0b07080a0c020d0c02060903060c0903070e0411010c02030a0c08010915020316050c12040305060406051b0406210e010501080c03390d0b07 69
    0xc40d000301d211029281102c0c86a001143c4201ca40d08140c00b0240100456890240c0403c076148204440d0490790b9015600036902c025007542c2d555078860480d2201541d020150b400160a070a041c0d21a07020510f03c0d0384040c1585040c10401e801103854504169003240d10b55101240040c204d0404021000052241c00c0020140b030034103844401c1000210440c607030402621000303400075520100614003805500c800f0044400b40c0c0d440e0074034000d100000c1c0403140340f0310051101482050a0080c0c030b00032191003e103012030000408081d103140d03110755403072043c90140b035030804803c0c541704005d84021030103000a491140362900d4143c0449000509644694030741c81081f05403908000140ca0076034800c0e0502040a84480384c02e01d808421280b005440d840c00c04030441060141034001074100c400c0d410866020f00344020415440d0460800030f25049081c8016180c0c0003031541250081d4440106d000b0100710301c001e07011072241c0c481014260340048038075052152040e4410b4034885500045024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 895662347 1250 895661097 895661131
    0x60423030c010c02300f0c0a080703080601030b130c021216021f050d020a0302250506010e070c110a09090f03080705040308040b03090c04020d0c120c050a1b0218040b 73
    0x4002c001c000c4000d101700703040e012442c0701c1d880c80b500040314901441c4038115080080203180014907070f840808110002181d68001c2200c41d4000c0c001c02005480c001c0009040340c0d1040c0110005044003151041144610a06079034840d140c18010301c005500802e92940d41c03e0280140180d08178410014404804001400c9c455503902c001951181c0e1300c029005a03461140c42c42c07c070042e00580180031100340e0140102c10030328030101d604500b8103100790113a4a40380c0c2c4c0c80e4101d1860301c0084406001040e000d86035080000c92401401a0301c880040c005155280c40d11299421166030a40c102e1340110801118014141c100003919808161886c0141c036060450755608854012441103c0780b00001001080001c2c000380407c2c400440007400442d2255410703241d0030b024010500080000c2424010a002d4000b054068120129030039211b107071034280a000110342e00900e003c83e0111494003000c1000050751000820710210040740d43e00e60050400c1d08010007000d6010345810190b6448540c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 895663597 1250 895662347 895662403
    0xc0212060115051c1406030f010c050d020d1808040f080a1a0a0f091b0504050c03060108040c0e0906100b12010b03130b010803190c0302060423030c010c02 68
    0x29001a904840c0f4225843e20540d0410581564101141c044007505000c2c51650704184e140740f10780f00c0c1e0011011150810f454039000c5003220810100000022020441d00c07000b9241034000305604142c0800000e09130f440355511280d884403040d411100040000360800c41c120301d100011002c3c0400358042d080148480c0e40d8540504a15054044030380f405400042601e0341d250703c650480d0568040912540d035181c03904002c092440204480d00324400036020031f603410588140c0344203280e01d21100345142c48400c0156103944000704220b500904044001c0741e501d0700c1c0c44816004001040041c11582802010281054075981103443c00e40018020100261803000042d811a0803c000c0d2079580d8a40d006d0454000060309005040504864000140440004000d102c01402821401c082c444081003c4400290302c600190050384a4030201d03021500d8440ca206440510002c127036211702402d20024215001002180f0103a50b40e140800c00064042c0000c0350001c0300c00704480c5412203024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 895664847 1250 895663597 895663619
    0xa143d090e0a1d0307050f06010b090906090604320c0307020d030507030b03030a022109030604080919121a070518031e03041d1608040318060c02120601 67
    0x41400080b162128145880c080b4005035210018450f038098903a2070550b4240207907102421105907130300384641c030b000144801043c82519112030009048881d03c1d1240401c1214204016241d40d03030155a41462200700d890a0303882d61a991840d00c1c0001c8940c0a510003400c60b040020300030a10100300708100176010ba4045003105a0702c0d45030600203031544508030120010080803250302c4c1c25110002c1e40c0758100d84c0008400c6c5034550a2011400c0a5003050b0b8140454050404060f0b0160302a0004c0380c0003400c52400340100c2c01c4e015020142943c0540d14075180300301554002c0828007402401c07881880301c200e20080d0080d441c4181c3c00a2401d0a1fa00101940320b007a10f1402446907944580400790340520105121007044c03c03001520410f0041007684030751049c401c0c40c10100c01001003203400c000030b62016200b125010814415103056510690b8a028000c0c0102c041100701500c0c01202c3e80c0d2030f00c4501c00f41072695202c3e13000002920611a014240c0c140401c4a540408010401300d0f0700c42d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 895666097 1250 895664847 895664851
    0x40b0604063b01090e0705060c1e032205030105070305070206130812090309010908070f060f050c1c2006061017091f020304020a143d090e 61
    0x110401c005034246010582000c010000d0706280b01403003510000504008503008001d4070070314001a594515503070000c0107210f10881e113103d203842d01b00d00350703142540e5000c00b50202c0e019200c0082e00c0c50500104e1600c0d0800c0e9110804000c02102d0050070300840c20300340f081950103003107814100a2410042e01c043c1d92650000d0008a51818070100c4400b002340000c140c5007030002c0500004031905081d08403c0e280e80051683c180041d4030100300060004000800c1c5003112028046261542d042130821500d05505400e600d090040400805e52500810010b000004013040008400d00c0700e81c0800501c5100c4048680101c03000d030203210030b28010085480e0350041030440304110441c1052074207031a0b10400318805060a5461803c00004440c00301c0c10b101140c0f10144001e894020300c500744001c900013924041c1d0849000b1005019070080e4029502211400401d075590b04085000102100042084c400e4100402c089210314000b42d4002824840702d080d00305105990b0070405035001030000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 895667347 1250 895666097 895666139
    0xe030105040308041e1e033f09020607050106030606061106011701110a0e010206011a1b1006140f09060d110a03200a1725050301090b040b060406 64
    0x1800c5403036441400304001d82004554030580e0508003c04e8001d01c207000506c505404d60100f00b6039200c00ca88a0705e18248101c004070554400c9484414084450b08044100e035150351419a441c00780c4000360361135001400441e446a40040b402c02c0c11460024182d640075031040d011310034241802800a600468130906540d140410840700312880c00707072103014240c82144098002c0000885041455001c00d07001d8420600ba001c490301a6030728000c0051150451a004c0d0354071409021a04403a1520094084213607008000c0b141030706447c0c003c0d00115195540940d89240c074001d0303554003e050040b2803404854084031681700d10b01d0613001040044913074200081044c0107003038502e8a55941c038440d20000d9a004564120224121989000090015031029220700484400003958640080010712a45103d00c050283c00344000c01c035a5450000c980505c03007400000001081940b402d124034602203000e8400042c40b4201400c0c040c0e2451805011140074509100042c414520001500c0580c200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 895668597 1250 895667347 895667363
    0x506060d0b040b09130b1e04140c1306140d051c050d06170f0c030c06070302100c0e27040b04050f0a030e03010e0a1a09030d09060c0e03010504030804 66
    0x18100005000300b0b07800b1843e962003000001071000c841c00d81c01c014100e5a214120050360768403420115502d0009000c1d8010800e8055000100040d0041d10359184c2c44812004482d62142d15600190030503130309031070700e941c7c1c1540c4850030000b8030182d42c3d00c42e1140800313580011081e800d82e1140340e05c0c0c220080e42c100000617601520307982c6a12032401c662074840520410001940c80380058803003035074044110302c03851241e00514140c10740c01081d1a86168001001000c04488450601805421005040e021f5010304031009a19841303601030503c07092103d40d10070464581e10320410045d01400307640e50525400c942100d0051000c00d00380380e60060740141c102881703983c9034a0300c01c3c940b45040c00100240c1c080c00031b5078070400d0b42102a0402401044009020f01d06206086558849a2500c0a4114410f0820001050060301c2000b9042041d01c0280c91800c88455265019074200d90700440d840ca946058049420394048441124504210001e200509141d100200500800303000540188 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 895669847 1250 895668597 895668611
    0x20307061d12161b17101410260f060603190510110f1909080d1b03020f0a240204050d2a062006010b2709090a05100506060d 55
    0x104136024180240784008080c410303403401e414040d03220709520010852060820070b8156040003070b181c01c144600c900c40c440d40c0010345407030220308540301c0011512807410095000d640024005200c40710456080000410050400006141c905000030406141940d401641c80c0f0001e40c0104407242c0801d014103000c241c01000084101c858420003601d10b00d80640041c5c050302404c11952000c051040f1078850642c80b41d41c9511443d12100c41003480b00008030080f1050b401082000c0351841501e00a204468059002c83e180d9464550703000b006039400075030308085030102c6035111005410060b144905506041ca800c020407400302081c2e600812564003081d002d00c4003c0c00c0b04c5110819881e4040300301d10160b41e4080a400c13048003080c0ca07852041004032090110b0030020704141210400f2803520715001801500d40d01c40842c0c80074905030200c2e084800481a0b94118070031f80549003400240040080500c1d00d0f40c900b245074600303000d1050400c003c00c015940c0d040290783d01d07004451008201c1c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 895671097 1250 895669847 895669883
    0x1406070c0b07180602010506190b0406081909081909050904020f18010605131a2b1406091003020a0504021c0203010611070608060a031101020307061d1216 68
    0x40c0011140c3c00c8114550002030f1041c0d0541101e40602403e403040d00d61002300350280014250700d4002c0c10024042000f04001003441120b040b0707884101000117000800100550f141070742c40080041ea94072002003100d0101150341c03c40000201c1841c14549201803400021460f0b0300b00003080603206850003011582c0546074035102e142900c44030b0090b5001580c48000140c8150485031200d600702c1c422020108a40c900e0410702000c0e8040a2086428842c1c444030359100380d14038800c600c00c80e07015100c1002c42c008040c0924050b054048218000c1450031005100c0b40b08002040030001d03000d034110030005605c1d0b401000c402d40300103a901680d1404411b1107101807511221001e08091f10000000594941c0b005900440070b1004c403d650790956600411138501605a511a50001964808000061107000603c0c51104180192030902e0203640362001241d003480e408943c000254003a5188c0d8650600000300c001c0340034445607040400380c190b60300b165001c1110040400031001c0d0480c0c58 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 895672347 1250 895671097 895671107
    0x60906030601180e070803030f010609030c090f140a05090c12120a090308040b04060e03010b09150319050708010c020313140a0b0d050907050d03050706021b0604050a1a06030c0d06020918041406070c0b07 89
    0x50a00e0f94741d41c08a181420103440340101011908401c03140114400744103640307840c081d0407c40700003c2004106034082ca07050041c0700d500090b0841c050280b00480040065030b1000030704000d1860070300701a162460039901410b0714900145d424426450071440300c5c1d003030f81c1c1c64141ca034012480b010b146400d000c06401080c904042d8404c0350001e8441c00340841c0801000044000c15038040c18000c0c050141c0d4541c0aa96034080d43c80c440c804607807071000511030440009410504610002e09a50700d4680d034000480312a40042d202c00011600c6c8c00401240080c00c00c00380000b041c09441d18031220080341c4004120303000d000c4000b40307050b80002c2e42c400401729040c0e0480c40403031070390155084c41c00c062601c40c1d1b440105250440b03d100c200e84540500142ea540300c544114009005419040c4d01081048101c9011030700441d4010390a200d02c0d415511041640c1d41c018104d0441030b010b0f81000d007410139070706903501c18503006984247e040140d039a0307000b40d4440c0800e42c401c00d645d070691184002518 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 895673597 1250 895672347 895672361
    0x819080d0c090f09052d1603140a020d290904060603021f090501031a04020a02071703040311030318190305060a0212060906030601180e070803030f010609030c090f 72
    0x1a409000e0f8001042026503a8425406148400c42c030504041a00540501c400d02e143da0903000782c01d000d0000380704003459100c0c1c92942407881c41c0001f0861900c0c1804001000265501110550702058610051809106290304164070407142410075082280b01c0c1616102071182c14050907a07100072804120598201d0009141c0c010048d85000c509440c152281c1c9203030100e00d00004070300301c40c0040da44d40288074600400c8010203482d100e84034030600b0b01001e580300001180451240c0d003030014112441c9807a4441c980c0c0074201840d9214039505001614070f502d41c483c0c41c4a60420420045000c6024420b1401c2c20002e6620791100307400c2501262118200385d0025095024003010410701150550040000c0030550441d04502d4503458248040c1010444c0ca564043d03000800510108030035420b8070a040c10840c6020495003a01c5040608001459001d02c000340c1c03011003445200034001480e140034040a18010100c1850758450307841e5205c1611030503018541d0f40312140c0d41e0843c20b4200718 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 895674847 1250 895673597 895673609
    0x5010212270708280b09150a06031104020702030a1211070605040e01090e0f01150e13021005131a281205061507140c040b091b1b070819080d0c09 64
    0x175a242c64900ba030103844140c881c008000f0300801100003045c0302c0242c072800081d46c1e003003c980c0c1d41815481c424000203600c5a10306030307814426054240e00049107440c4d80c0c92543c80702d9442038492208210210316006141d044042448420300052046440f17102d981411545225008200c3e0f582085106040030440e000c0421310303500381010b80c0307440b150b021140741c1110b20b441902d51807695910400410b0814141c0000d62002c80e4001e4242003d100d0b00181c0f90440c2c0075a5403120466454050500d11030600c9020260000301091170f4860402c00400840001e0900c41c02c0b000c1c0769040714000f40850109a0401005580c9001180150701c0d07441501c282580b0441510b075494099003400300404560011030421442402d19044290400e400342000b18203014007141050345a0007410036842511a21700790142500b480f202404070b41c01e444880304124440301400140d8200b016640c1007044620f810140d00a03061441800200600110fa00b160b540120005103903440102c22103030001d641d8808 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 895676097 1250 895674847 895674863
    0xb041406130e070b18010c12030f020f070b060f040e150403120f020909070203040612050a02220314030f040e07031517010612020f0603040501021227070828 69
    0x200784c491001e4001c080c201039021403580030070180401100c1c100600308005103034442001114034410f0107504142000c0074109405401c0070300a0500e0925908000340a8410050003001c1c401c56040c50500058150008e450904c1a200155629903a4500ca000c6090b40e841d00c240015043c144201c4070980c60120800041c028034003a40000c2020f0b410210016204184140111714001d000008560449856440308040c0d1250126001d008120042c8002810fa8080001030201c10146030814600ea015038112a500c0382941015610b4000c80208140079510802643d04038410400944085a0a4461030582c1d0f603507100c021005418998804003a01c00101c2d800705044c2c0304400d1000d044c05425008021444d510310148c40036940350300c00617400c580501da5100301070801c03500441d806401036001629000c1c1c10004000e2001e003c440080c409440e02100010282d503c500c81d031207407403030780006014a60030409640c2d22200c0f1860780450300c40000280c40041d40c40030381e0b2615410742117090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 895677347 1250 895676097 895676099
    0x1308030910060b03090610080d0e010e13021c06050603040b090c0d050102180102070b090409081c0b0f04020711042f0a0318030c03050304030c020909010c030b041406130e07 76
    0x3c400355a0010343e50a1540c1c05100001220014141008401c86607104000c020104040d041070310a503042c0210107040000c0c01e01310781c5041c6c68001820385441243d40c1e005079143c04500440100c800c116458504c1182420401c0081d030303803400140ea40158101d00b2032441d545441036044c0c541001508180d4112a5820450301480011f6014081c0c9d5082407039280e01c2d0154a900483c0c55911600070a044028180108407650406030b00c01041c4901c1031400030f1400140000a2806164420070030340542d40b81c840c090384908041d0f490b40c0401078141c41c2036052003460366521803d0000008110b000702e039502d041c03a14ae0b01c25403d0601d07120f948050001c030074851140d07000485074000344020022a04103002d00a0300c107200422609076030382554ad842d101c080d040c0c0c1c003142c1c10f51001c1c106404103d400b090b45800350b96181481030081d001c610000a56074456074020701928100031350b49215903d0050000c00305481806241c2d81b0410881d00305000300d00140400c40203124411059034680710300e0038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 895678597 1250 895677347 895677359
    0x180c1a0c010903081f030302060412030e0319090530010605040f0506090c0403170a09170102090325050f04150305070e091b09060a03050f070e010905130803091006 72
    0x12a00c0d010303809480c152000700f1446615211142d170346200003401a800b1100090100340380105e05162201d15240200da03522520300e40300e01e140c22108514000b8800703050700c0080c1a4001303690b01c008010981d000c005400c503800c4c440d01c00340d481b2003201c00300985080f042c1c034030040294002c40240100070810000b42d001c1c034034498000d0508a42040c00b807819500440d000b0080c25040d5411294490f83c4060b01c654610120754141c1c1002c880f0005025078500d002c58030700c5903141d405880e411071100040e2180d0799003041510b0821092440c1700d001650500416203d24107040d040300f503400c2560303003203041a94040858018050000f03007804d2980074540c04400c008000c5010300c110356811a42500c02c0c2c030b4654080d51210a50704002c000a80b44450491003801c2850449a00140c0200307003d940c980d80352600382c10604d0b20281c8603055007015205100c1c40030310103695405420540d80030070071440c1003d013200d0010f1a00c10043c1500d40f01100254040d482004014070a195a26044c0450b550381d103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 895679847 1250 895678597 895678607
    0x17040b04170303011208160b010e0910050105010e120a0f060501061d0306040f0f0b0a06080708030903030a03050402061902010912180b09040e1c03180c1a0c010903 72
    0x2004000c050794503001030720350324500003050724140c420181a030308290b07900d0303075900109900418451403c81c8080303031240c001c68100c40b041d50003410b0307a0411421600d4101e00450a003544003080e0986549030070014010b80e41c0c400842500d401c8141e402136030340000151103d02d0503d454800500340303200f403180700c0100030003600b000d4121640c2e82c50305602c604046942c0781601e60140c1c1c0c0c0b16015071180b00000c001c02e0100c004500098010300310303280c03c401c41f6120700e00c50b100111590014251100ba081090391000c10180c802000c5d040042d5003441c0c400300009880f80b00c1d01502404054540c0e02080a41d615101107600c9070075040c1c0582c101d440c00c00b10190180501400984100000100100280e40600d000f40380e40030000d41040e00c201e0511402c218bc94000c200700d19005030b40d80440503600b07074013086205040786010988140004000c8801010740700740803070039405242c60f00d40500019241c12040000d98602c035100302d841e05040c1400500310300525212a031a903090110541c1416045 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 895681097 1250 895679847 895679849
    0xa0302040e130b1b090402071109090c03060c0f2a0a152a1d040911090106111507210b01032f1c05010608010602010f2717040b04 57
    0x50255402d050f51201c0b5265401183c001d4041c07150721040042442c3c41c982940123083d090320400c4801c50801c0e4600214540c044120340c0d0203032a40c0000070140fa58507003040003591081c03405e03100300c0c50080341d04281d00150103544540900b4140d16280d00d8007001c1505408140201c18500701c41d150b900c5800c111280a1546c0c400b9040d0702c4c0f5000c03840c000704410015840104200200b4519111901a011126a901d050844d40e40c1d0026002107003903a45c5074081c05400394090501e00010b1034040c020003e031004183d001c0000e000c07201c4c081d14082c51000c2510140081104840d40c40c50f581c045007920162032141c186140602d00c4408080340d41c841e58426248080280d070308104411000280424254040b054500c100000031940e40144810f40024901c40ca040352001e0415081c00b440a000e440303007038021001107070240c0c0040c00140c1e424401d0f0385040d000712030b0510a180130103100b140020381c100510911055107508060078001030300132440402d216051482c0c0d40780d079141c050034080c0d085 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 895682347 1250 895681097 895681103
    0x90204180804060f0206010f06050d0b150703030b060903062404050f0106020105060406030b0a09020609040c02062d071b20030d080f07030209180108011b020a03090b0a0302040e13 79
    0xa50041310702520024005040c3c132000144400302c1c40c10410f00b0b43e01d617049001840d4510303071034000d00c8031903450380c1d40c90581e400d42c02c1503c01d0720350400303180181c20384031803041c12406110148039100c40d981d4005541c5802c81405401c0301062600000011401588450003581160030300d400d1048091881c00d50701c2c100ca0007540200708546400040109803641484050148500d950200f1000145031b40003480322480140003c0c545141400441d060364802c06201000d030f040041082040900034010803217807400304075540700301c44000c80c01d124000c40140100c020031699504184458140040034443c554020b410141882104405141110100011240203018200c4240922802041c06500454141c900c4c0685a5241d0404030001c0d0031494800350301406030440c00041e41090705806001c3c020200c0049003142150001626a40c000c000b00343c2194406088100030907808800d0300181d540000a055542c5070b6402c088000e03008039044a1a011204018000070707906030050640301501c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 895683453 1106 895682347 895682357
    0x61b0c10050903041701060303030b060f04063009120f0e0d050a080d2306031b030f1608070f1203110a08030126060702030d09020418080406 62
    0x40800c140e0380311b075900c0c041802495814026625035800c291065403030170744200c002c1c141d2807140b445408104420000d1006061b000d28880c1c01180407008595400c00684905030b00080070381c0070085645454480da0342c90194000c008400000c1d03100e885021015401c0c00611441008000040301c09002e140c0b00c0e8400a1080c101600c50f00e030aaa000103007000000d15002946040070f1551300c0741d44407100401c08159400a281c90175881c403484900ca0040511010030b203880500c01b2044124001c00d0b245e00c0b40d5680400000003200c212030112041c055480800450810700c6020f2414407070f05502d000c5020900400c40902d4420b1484115000c5c08501e4035114002d070000c1c0c01030004241000344000700500c40840c601c1d4225051400340050f410200e801079a24850080b2001d91a1303100c0700408203650f995405840304040403204020b0b015024038080900d640a4020440850 = true := by decide +kernel

theorem cover : BRFrame.Cov 895503597 895683453 := by
  have h0 := BRFrame.cov_init 895503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 895503597 ≤ n) (h2 : n < 895683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
