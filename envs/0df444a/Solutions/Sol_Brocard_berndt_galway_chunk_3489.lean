-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3489
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:48:47.07798+00:00
-- url     : https://prove2.me/submissions/942f26ea-2ff9-47e1-8a6f-44b638b9e01c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 627338129 ≤ n < 627517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 627339379 1250 627338129 627338149
    0x6010309111512010f0302060414131409010f0c1b02120f100e0d080402010305190606050909130503031b0c060103080c060f010506090609010e091f0e0f010b09 70
    0x8120307581252480d1568411a8001e03d0000c600d1001d090010070040c60f0a60380310240c035005448903040c2400d26515083c041e20b0480c0e19940580102000305480855004240d24250800b642d0119414100f619034251001c101c0b02e100c4003810300c00c0c0412401d030300469000741196501540017040300e090010540010000d14200d0b8540181d25054850a20000b08102071b0003081d00104100302d00301a40d04e40303414107450705400250900307002c1400b640c441d80020750048031008114246090000780c040403209268440700c0429008a456041c3d4500700381e1315648010340008643c60703400103035100750702e03840000c0007454035007a083e41e5150710701588003e13560f0300c012000440f000340d40c4034107065500c4c0c1c100c001807107000d100d420300086c03040340100320b001d040b40c402a10b01030900d0701480c1040b100741c2060400c00d040211400c0d0301c51485d07440d44070480c0198925407508c0700e01a50001c460609140301d4026600d040002814010351039004a4007504454000401d15100d0300328030700165518078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 627340629 1250 627339379 627339413
    0x5100e0111060901060807270504030509090f0105040f0203041e0813030309050909160918050a062f070b04140d080114010c0203070b07020303160807030306060e030606010309 77
    0x1040e50b0401003803000550002c015550040103c0d580c1c0d030740c2c036a5100b2400001c01d076410902c142607400084d40d0101c6c1c2e0420750300071303110741056800d0011500100340100000c40d20b800c0202c241500400c124142441650502180c2407029031a52802c0d4031060042c215800100b0070301009104203000340711412068440106c1000896444251f50b400d00500c1c0b000e240c01164480c441a001280100333600140e00d01c840300e0503010840c2c84a281c02c3c407007001412200240e0b401ca80c600c04850000840030300c402c4200034403a00c00014a00034526406508403071510b0304241081c101d0502800d90f0480350266481c190303220280c0082d9a9813894105102070100d40440400e1043c44042541c031a001041c5505075025003000c09010780d801070044586000f040310294068200080a00c10310b0f14540c000c100300c90020b030031280380a000c12803100c0f40c0e900303682d4140c40d8a00046541020180d0601030740b07004010f986400720b80c2d0071203080041c3c3c807040c0203002c80d4141661141d200c4200700104a00d140004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 627341879 1250 627340629 627340633
    0x203030301121209151101020d0c0201050a060603091a0a0603060c0e0102104206051c15050d0609081c14010303080708130c0f0e060a05100e0111 64
    0xd40e5980b407496080a010100312502581950390f2003c480c40f501c40d15048910030141c800f400d9440782c0781560152424100c000f211b54003003000b2040d00500b4090407030540301c0c9074000105468104003505c1102c0e0560480400c2500f0311a4490108440710b031541d4822403402e0030000705031130302c803020780042115500003000f0340c1c04c200500801e190043c0f800c0b007511400781c0980b0000c0311201d2002081320a030403a848071003000c206840703404c000203602c4490340710310100c0549112505510a001d032004160702001c00984002410132482120f03a21001e01918070500c24050b00c2d000366440100c00d0700c01d004080c06202040009000d016075130b0004240180c000c04003569446000700105820300c14412224035990811441050140740c2821844c1260f0b05641d40c1e06c1e894803002402c41e4140c1c03020b42248090340607080903002040703010010310001c00041c14609200c07443d2005100d1419002841c95209600c950801c00c016121841d02c035080c45200d06c2c0c08404d5094a9006076020b4541c7c500060241c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 627343129 1250 627341879 627341881
    0x150103081b1c0e1f0801121103120301050a0f050a0909110a060905040b0114030f04020d120306030308160903020103020906041208040503010509190b10121a0703062306040302030303 80
    0x41c0d40040b82000c098006480c11407401149080d404c10103800944d100002800d00c1004000100c4000c003040031b403c0c40746028a070000702500020340303001c0310385038100d142030f00c0000100900e00d450003000005107080e2545e0308450b0314240000310718441d10f11900410075120500b00303080061644184d81038107002061583c2d51900c80f100184103d6560140500503490803132404059800350040c00403443c090f01da56441e40e9a41442005d031418054412604a41107108800000f0310f200c00540e1078440d5075400240c2a80341d82030051406001520301c0f1207022003030741140c0e81d484d40425000c058980a0902590300d01c080008100584129400311100c400f0711041402008001801007046034400c400074031082e15040e482e2529000880300c4017540541054803180010324800c40541d2080c00061005101c42c0d60b8441d090041d5400802155000461080406562152400503400180c546000c1021500b42034020070b951104182110b140c0b507030301c0301d0041c041d543d017000c483c059980076084d244c030f0f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 627344379 1250 627343129 627343183
    0x40b070f0302250c3c050a080303150f060d05311104050c19090e042108010602070314010228020c011409060a0201240503150103081b 59
    0x558241d9040307070134802c06807000841038007103101c4007171400c0e52413114503141d10040400d03807500340b0300c00c841561404120b90000791b80c0c0d00ca040c1c2c4401040144099a50303031034200001b030654030036440014490340d2003886014440d00c0d64810b4a603141c0180c5e60008498503030024003441e5202d000100101510101002492064100030040382c1b503224000050358446a10100000d0703030001c48101d0012201440040c41c6405441c0200c882043e250410498007511804042d03503c0c4801c407019141400300e113000030340c4007120f030749040b08000c124074041d84e09504002000351100a64440585003a02003825524009400c0d412180e9801c00200e121010301082e111850440c0ca100c8941000b40c000c054194103030707502641e1011840982070501600c2c00039400f0421005801c050700402c2190b5075a8042c000502c00d0f442d11082e4500c002c08102107080c40c0100701480c010309410098840032280c001040082c0581003030362354542c04e00f21b00c172002d0b01201a61600d051050700c5003110004100d024001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 627345629 1250 627344379 627344437
    0x80106060f1205010506030c0a0306030b0403052205060901050d0e0d11250303121d011512020d020d0807081305040e0a1a10090e1b09040b070f0302 65
    0x211005107881d95201c4881082c800301c00c8610910070150001810800103040b6031620300100143c0f00182070000f03042d40c0700d803034183c4050340458080300070980004103602505030880c80190881145404460414140808200300340181018141800404100c540342036425421015601d00302101700e40c2001a4840d00809403d94112000c0c1c50340200e10b40c5460702c0d1b2450544141440d0f042e00d0b5000d540d451a80d04a07a01103400740000c02d89991010100004058608102c3c85c5c9140035001240d03810a41c040e0300c0004038594091150100c102d00c07004016115200000c800340c0d01190454a030807541d081040ca60b128030360005105100004008400503000702c0303401e01341c800503134003000800e8520455075610008000094040700032001008107101242419650081a03141c80941075a564059176041d1000d601c120000c542010000b070400000c2c1a5101b0019581180d00030018140b0741c5814803441030140000c02044042ca00c1103071014000c0e0122a45000c00c1c201c2542c6140f803c1c1c2c0311031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 627346879 1250 627345629 627345647
    0x90c040f0f0c09120803070314040c0302010914010c060c0c020909012009090417300609100905150a0905182107021801030c14030a080301090f0608010606 68
    0x41c4256141c52854003096100c0c0348084280c8114110443c0b4401050315041141c4c0c0004041408250310f55030840e4005041c141a14000d501c120800828036055100160003422580c10000c0400400258440281ea22a04c001a41d40d040030000030142c1c00c101c0300b2241c1d0f080200000e5005a6010306002e80c065056008411007031080c2c421844100701381481050511401324801e9103e0300d03440200e000716080b4100c0910001340024601d1800c800743c24018100300210f100d2050544500d25050358044003001c2c0c0b164080000c40703410380300b850704800004482e0305500486400c0c3d5a00d500103640112812040c500103178004003060092030b52049018064503084030900412401c00740390703043c00c8100042d45004140b0f02e140d01d441882951480112903045906c050781e01402201d803000e040e00d030740070300705028500503034400c12441d040124140b41d41c1483c4625a0007548000400400f00b0305580581e41075071410100410030454265558015003082d4100c1d2009502e0080000b800c95008502a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 627348129 1250 627346879 627346901
    0xd20100504140d030c0f050307021608071a030c04030f0c03020901180b010807080a0e0a02120c010f110606010509041d030901020c0405090a0f0c0e01080c011209020d020405090c040f 80
    0x2103080300e20f160012002c1e14403124441022802c03810b80404582e0260000d150720060510480c4c40b01e07800344402107403401040c0e001e100303540c0000d00b0900c000703400d500b503c4040c81c41c09803d082c51800e15641103449072080d4480a031500300e02015001c1000419501c8500440d00200340400d01e5841c0c0d00e46840306141e0042201c01c051500303982c4200e550081540302d01c2040d083d01c60480c20f07035815001d0340c058401940300d03c07414041e84002c80c0040c0d86840728902a0401c200040410040ca0030001d041e613058080404180721503035042c2c85800000061302a404002840c045440340100d8000c10080c1c0090080c0742680381c1e0042483d680c0c02000006401c008109a0840c0c0c48001001d00b40022581d081d00c962501d600a081c9540100303a40422803009607100d02c02040610ba9a50203a03e04004d083c0c1202d1015001034410303104e00d41e48548060041440c9110410038041682d0000d4412141c0c041c0c0203010b036131200b00081084074284920b0b494032201800a0203041d0302a8074100007003c115000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 627349379 1250 627348129 627348133
    0x1b07050a05030c0906060c0102070807050d09120b041205072901140603010b03130503070303050108060a060b09091812071401050906041707170d0c020d2010050414 72
    0x1d59180018203840f86520103803102400341c0310241808010703400504078540564003008a040000d01e881c0080008500580c05405a0346103100000d08100303196002c0b03206c0090944616000c00c5440c0340694116600030b28030020030700e4014050710315000d0540e010b0100d444004c4560103001e984d43e071844000c10200c0507050b040e0b072900c4c0c1e0302c0301113202410300c250800006c0c0014011a100c0200864010340050f40c4180c04c04e07001c0d610145950320451003140060f032501d00400000400704041c58018505107000d208180c1880e507454102d010741c0e950b00b032182140001140302c000422420340c45403014002691020310103007000c0c103040d0340880d20446031100c100000c0011030304184181c0340250456005806171352900d031100400100a2542e503590f1040c02c000a0000600a43c0020031a14145545540350040a01c8030001c4950b1105142d06540180c6403060350b451b40013281005510849840200e8260311910300e070328010071903800750300c00d034035040a1005005c0d002280a05403026602 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 627350629 1250 627349379 627349399
    0x5180f010503030a0c08030c040b070c0612050c0a030c0e03030a0314150a0501050a030b040207030305010303030e0a210909020d0e1204060207120503090a06050c0c041512081b0705 79
    0x402e1560300d1103507501d03c10010350020500b000065281c0c00458121900882e03550400d5180c01100c12290b000700c00480f091138007602d003040150380140300036280480111080046140000504031a881260f45820400d9500c881900c151801542c68040d86032000d41200c7d258445454060000d0500c0010340791205162000507107500d02c002c61011003035602400d14901c4034a040c006441075000030f0003032030a2545511a034100c0d03850307a02c040c00000e80a40c0c0d0128984d40f45003009001c64000e50001d000f00d820170310049000c84c0c0c0c00c0c222001200641d8422092840344010102d600e401c981e04040c14040c000a20070b10001e00036013001440300800d00580310101d00003219100e052140d84129005030f08482810443e1404040d17121424a02800560f403902d038000000862443c20b81e00000b000c00d0700412043c001e100100031100c2d494a056070304000080c0b006943c510748c580244100a0390f04026081d03401042010003c0d0f49401e01c1c00d030032400514107041c600b035407103103031a02407680642c500032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 627351879 1250 627350629 627350639
    0x9010b1903020a090c02030c030c03070c06050c0a1e080c071410080a20162306040b0406091a0702100b060d0c1125050303270a05180f01 60
    0x38808000c41e580148201110b500d03112401018020340c03d158400c0d80000d200c060100f1105000900820084c1030203155905154500104588a030b6008002009420b0140713a00f107040000c1d442070b54a0300040a8a035006150000b030000044c0c00e040180410004644c003d000d810001c0c608058420b06204c10288069060074800c080c10140e0001c00010350f1407020440911265229110170800c2c80f0145186145012500b61aa4400d60b0345181018000381c0790028413280d041100c0c08280741031081150350625000c110354402d4098005011808610040307400c10085520a14980e035003d2410180d8085034824081c0c1075108485103030260007036501c03030303a0411524420007000d61310091100c4d0514007102d0350000103108000301d0606100c5184000c0c80101c40411130506148e050b03204000c0486800c9803e00d0301c101c0540c1c06280240d005004a80005800d9200c0312900e0b1848900000760b400d0550020b10340d50380c647d00143d00a21080081c42c0000400501984140450440b80a0b00e0341d0f60 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 627353129 1250 627351879 627351919
    0x606010c02100c0503070b0c12060109080304030813030b090703050d03091a0a09060f02070c0515031b0706020711010206070f090519081b150406090b0904021209010b 73
    0x6280250b02101019411400b20701481040900394000d00883e8140401640c2d07681c05880b096914803840040410301c0c030501490880c14942c031480038644054914036280320b50790b40f4011404001c1054101062802815440e40014401180c000c2e44062450402c12079442d152040c0d800b003555240a040d5442c00004d000e4042d601d6256400304003094862105001000c0c2c4090160076211b07850784071082000455468010002c40e10205070005903100c14a1a0090007000c440e44218001c0240d4084214410380f58800c1d02e178050b06002c00c030304018116100d0854680310f0820024503c034408039001c8240003240380c0c1071000103801c0c1c00310350a903140d065065503001b2a6800003000116030340020302c100c0c1001d9046034440d070525142110f05544a042c0c140c00c10210f9018910260703140f04440c81d0500d84a148941d040b004401140e00c0c1506042009003928070b1809150f15102d00041c520300c45441d550704603850001250301040c2c0c80e0500701c2c2c00c40d010301481d6900600c03412421140d444c0c00116 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 627354379 1250 627353129 627353147
    0x30c1202090a030602071a04060c0e0904080414190f030303050903070203121c1107020102010c050a0e010e0607050d0e03060903091309050a0212030703020d0915030b03280203060601 80
    0x1851400b000b4034654452020354080039084501d95104890b1640015084003058012071142c0004100c00d900000021320440c3d0302e400c0b281c400c1026405102c0030a01c5242102c0984215005030318144491002213019004a102181b1440c922180c0c0002c8000305c030782c1c600003034920a0b40c050000d5180d070030203640d8038040d00b1000303540b54111040c01e83e41018040e006050088665288400e00410b2003a03510445403d0883c20280c1100083c4407002c640e420b100b10741000080742801400c0900300383d4014030100f52402040d0601004044841e06076030384105803403071254404110343c010851054018150300e08200c03a1400782c400c21002c1031080c4400300980d252018043c0440c0c151410081514000c1d0042610503207003409400110005a1234103441c3d0b4044140d01e6004594502031031800a1030a2541c3c00c15800b048006001841064100300114150341203501c0e021515094540019003000034680752040c680c0514001b0f442c442c105200084812030084050744c0c602e41e61100107540c2c03090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 627355629 1250 627354379 627354397
    0x20a03061a0d0515030d080a0b010201151e0b0c0f10060803070201050904021b030703080a0c050403021009090f0e07050306101214060f01090b0102070f1403100c030c1202 75
    0x10034040000d03041e8099103d03650225034541001c045494640119052400400080c000071740213800300100e0611500503511094000e10003013103000f60b5606c0700895058103010b04980a200707661001c52010007469903a014008084405a881d504800755983e42c6102580d545464020155404030700304141c4104022200a07001852402c0c0080d0300446050740720070261540710350309100c0031010f10405450004048042c4001b9070740c4032190706010b800008014140b402003130400401c0c01c0c2d4030f03510a040d1421a9415584018001030038082a40d044080340c200060302e525020440f4500a030541041e001017039444140ca012075140c000b8980c035080200c40c04040300d60000000c0110300d60802000c918280500f0114140c0d200b2542c60364280b030b20685900b2a205049030040c4048081c07031080d210424001d00050035101d00e0a003140e1004000d9100329480780d02e40ca00e440049840034841e6006042c26001d04112003503000b00c015008145c00d44003000010382c4002034041c41b000d01d20172200c40c26 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 627356879 1250 627355629 627355679
    0xf060e150f070c0e0f0618010305070504091a190e0c10052104061a2d0d021c05070b0412021e120601090c030b0f0d0f0807030201020a0306 61
    0x5001952000080c1c0d221030b5046840d0211001c0010b049071075000024010400e210300c01c40103003405410072850060113160b0094194201004100080c000100182101e000380d60100700c179001c50070840c400c212810707125034400d50b40200b027128105241c0710b0500722407155074003040051702500e1142e90780c2c1500e000761904004c0c84000c602c445030140e005021040d018881c0740301007407098031f210680c00704181c4045036819101c5541c00e1a19064000301050000300352442210070343c400c00c600c400805c5045406110030204002200183c0743e10326044141e98001d0300403c0d0f90070501040d0010080d62034815200307400781c1c54002c140d0b09948001c50302200d2403461460640e8200d6000c00c4110b22004d403280d0303042d40f0301d6092040c041d2580c25482c2d10b030300210f0340a0200e540c5002c59002c259000c19810008040c0b6003200c1152590303e42100170216a0241e0f510714076902c461414040d100060a405486440d0224130001010380c1500141040761540c1d4060010565490080d014070359039003080240c02d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 627358129 1250 627356879 627356887
    0x2090306010b07060219090504110906030406050603070819060f090b010b03090118140d08070c0f02150310080d05120106110a150b04061a120705130f060e15 69
    0x1e100d002e019014040c09410010b251008a1900c0c26070035000e040031402041c0c4000080009151030300c01d112020301000051850002c4d030310002082071100900003800959a0408900c250314104001c0020305588421200010b840d92808d0719550480ca200700e0300f950070424810005030040c058201003c0d440050180c4503401c00318424081d801c0280100c1d429982d0301c0144019005102d80244032900600c1d00000c00c2100c107080b1414403200145800c280030f83c04041c8018240d12606c20034071103801210b40c1000d410b4620010301515035202d2800c0d440c18000c0f0a010325000d500440104031080d0710200d90010b1035079001914103001d01c0c59501148144003004000e0030780107007105001b003500c0005480d0703682c0c1d1540e66141c146011120707a50340165943c0107003400f81042c1c07107800301401041110305125407101034068014410300b084000c102240202081100e03000b50141c440e548200f5201c685502d0301c03030042c900c100001d8402d24000440c0e03c03c10b18403d0400c0880c0d200d06500500d00c032440c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 627359379 1250 627358129 627358139
    0x4090608161205150f0603010f0b030c040c140301030b18070812030a090f031d060403050a021c0b040605060103060e0601302306030d09050d0204061d07030f0209030601 74
    0x10b488844070190ba4900404006200060005000d58412213481d007500b0514144503040c1800c6440c0348003078507101c51600403284c0c09a0b40006038001003d10458010920901d002401c858415005100d00d407400c402000100c10040d150207160311801c450b0201c01c0c002221040305c03a60311640ca120348401500074031848240120076100460b480181d0540c0410300845543c3c43d00801c2289000075000a0101c00500c0046a01b4191561030407008507038050030705007103460741500e07000d081400900c5611070307107003181414001007109401290060500032140c078050806134003905c82120924000381c9064804900038104000c214003d482c10b94810003101e00455007a4014400214507442c445030880cd4413080290a0181c0b041d0104090045640894076558640e15000b0203030041d8441d070442070784082055409982c01040b0380d000c43d09401640800e001090003061250040c992004c2c800d075481c1003001a514034103010b80b00940c1d00701305015a04280c0000c074091580002d0b8150086401008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 627360629 1250 627359379 627359399
    0xf0301080714060f0906090d0816020f04060b0f180d06090b070306060503042d030306090b0d0525030f050a03020c010e0312030a270b01060810210203060109020409060816 75
    0x40700c01f0141251001074095140c0d118180c0291000c05604c22032442210304504100800154645003942c2c10301c542c03410481200c1040c0034060856055800205039400503007040d011000840002070301084007450701e41000c001501010303400b035411114100100328400d200e032081404480050707989500759121980c892203140400203040c111004941481010a00c01c5000311070f03064803a850001d141880d150201c001d44001d2a040d501c01d40f606842c803004910042003450140301c0d0051803d04080c0410010100c1801d1030700080e0800182c0f610100402000007458030407180a03400300c2c0d100d18440c40045920b100d01240e0303a0b0f003540141485808482c1054043d40c0c00c958110000715980c7c2807004c074488104102c1d50620b01c3c90410394001000d01c039206459501411951810088034a02120380000d14001480307460102d818031020a001c8568000b03818031180d9004080d29480d595404440e03000c0d40050060405142c54032200080b20040000c0340d00c0d60380c240ba002c2100309407800c100c0c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 627361879 1250 627360629 627360637
    0x103020d06090611090a120b0f070c0b07200c061c060302060d140c070807020f13091b050604080d0e130c08040b090c0108061003020f0301080714060f0906 68
    0x6400c582c44000c5840000d03050b018031400703d41040c10468035101340b10304110620700c240c0d000b03028810000040303c0c003255071410100d07404124007140a0040e1220f200407991200d8199015084140c840180034031164001d8120300300001601c800d00100d042d0a05080d25081502000d50340000104806460814001013800d01109804000606075036a500401c01c50b502070407040c146296120000c404c408ac0c0900e0030346d0068804c0311054200001c942d140003183c415540064031403508840c958500340d40d81c9144d000e04041a45c000e0040c5070303c40ca8009084040107800341c46000c143e841c0400e450600000752411030718005d000780615800418140c44211110395800d0300002c0b01004e04038094818007681c800c0c00302580d00d825840c81c007810003134036440c0c02a158000540200c5d101043d44e0b81e000c4000d6421600840c1d0400c20003d1201c82079009208800701c800c1010303c00f00002132103040100d030a40840e0034000541400a5004007080250300c6604001a0154000d01c00002d43d070900303a000d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 627363129 1250 627361879 627361883
    0x608060a181410080111040605070f02040e011e0c0507051b0406210c0f0e0f090327030f01090302100b150d0b0f0301051315021b1e0705090103020d 65
    0x5000b02c207a882c030140214100c540c00c3c11002d990381c042000581c00d01c500c1e03140b4100302610a0809085c044c0003841403240040152615207142e4070b801c191750302c0f1b42c007203060345001100800540c00d1481556612140e00c101c1c07021118500f0050b06a00e42c0104110740d000c81e4440090040340d100048070488034421001c1098210340d50784004a01d115120320000106250a1681710440f2010300d88410340840c240c000400d0f4002c403030410080b03d05140010b903003084148070042c500b95103105600b840e5015a6600d06042140701608138521210481001d03d8000b050303087e01c16648940500c0c90036103001000c000e006906c40003c451100e402e0b40d01c481c0d10114002d06503810000d0904000c0300b1500508506150702c0e41e510a210b6440c90000400240c00c0340c00e400a202502e40214401007035490908003910301d035900c1fa8100484007041d41101d07589231207211103504c05059085403e41d214595140819000046010701020003000140c0200300c0704000c00c80d509507801c1d030b42070001c2e9400103481 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 627364379 1250 627363129 627363131
    0x50a02060c030706062411010f020d3809070507020a0e06010e03070e06010c021801091d03271305070203030603070501031103070507020a0b0a0305100608060a18 71
    0x40006035a440000d116400e00000103540300c400c1c0341044804c481c5264424a800e00c52568000d920a5150140311100c3c01c4604090005000900040c2d0240c42c40d00a40c134109440096a4600b000c1e0075801310421814a0082c4a446084000a101a42c0c6010044180c041c400780b5822158500408411350007680da01d800d909000c4542d021900c6454141c000700c03400c1c6501002c11001d075901c5a08503036003480c100d004200c290f2130048089010b5001420702e50402c420fa252450554440c0c420700450302d83c10b00c4440a40c2c6da540c4050800030041110711280c0743c035240049051f00302d000000d49140b18042c48510100303204070100e00051340050f5032002c2c2c104900c013031880c2004540e4420301d4419a50340d005540d90740b07800d408041c1440d440d500058149490180078024902042e02601e81c81303146400c182d5070300c0b6594000642c800160f40d0040f041010009250990b45506400450045c54480102c14030300340c42d100b0541d880c82007102c00c41e0700081200700030080b0b00c01440c04c0138100142d03284 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 627365629 1250 627364379 627364393
    0x90b1815030a060c02010207031116030b060406080312040b0105010512010b281701090e03180301181b0e1905180d180f21020307050a090e0d0f140705 66
    0xd1940159004c9018240141c0d6001c140d00c814150040c141442101344940030340500f0204081101000445000142501e071003000082c07003e40f030351b5001c0006850900112900c420b011041203440b85003ca60440b400701c240e4000044a50049007503a2582e000c41030080c1842c0c1c00c181c41c0032000d4101d0718a07000f101e0301140d1281f4903520860030700a080b4048d96100c45140f55080c55420302140180d1101e180a45170210709a0702103000f20a403082c108202c4114080340088100003409018500407080d865035080300040100302038401c03c2680406171045003540d07195214441d4800c2a4111050304c641520500c0c118944019644010b034005042440000c0154180c1022480c00309100820b80104114925412a42c070120300280d00505890b0305145055041c00100341265500100000300409148004011550103202e001e010703003c082c1c040101d0a5444042401602c55080405924003a40bc21020703000c0c4100d458240e2105103848840c0c9921580c0c0c2081415401a24142e4440c004c0d89 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 627366879 1250 627365629 627365633
    0xc030304210812060301050f060d03031802030303100e0703020a05070f0c080609030a021e0a1203140708010303110d0806150403080a1106090109030806010f030b04060807090b1815030a 81
    0x2d44103090f0480036654140c507250040c1421100c0152402c0e00c0100d85000b04089556080d031280301040e41442c02048503900302021960f13544c11510001d616000c0402004011141c40500e0b1040724001504444203880b80c041c245d04900c912410200041c40400023800440da2100c86400c1551250a9a94420381d544049a0503c2c8040c0c442c1d18080d0000180b0341d200320b13410040c114001d4035000307800c04c483c140707000c3d0030f0345c1c031254040700410880007210301000c998007d134000ea00d0310000201072050380c0b85c001350090840c0000d0008501052240d083c1c00200b1500040c844140384d840d494803613654580804024070080044c040d9010501e04010100001d000307003000c3d0551030b41c0c50703c0d291101084c004031076040000c0102094003a0380f500c52228007080d444039440d82c2001007030030416403000034140d04601400340b4a01c480e80141c1091400509018000381001c120313440b0032030400c00c00d154441000608406a20703400103000040d80400c002007600a0700c110692001000c40d1010410f40d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 627368129 1250 627366879 627366893
    0x9060c070f090c051611060d0e07050111060411010305090a021203040608090d1e120c020607021e0304141c06050a050106030912182d0501020c03030421 67
    0x150300212207240395103400b00324952443c007420b02c000300f250414600b400e040e1101d060540b80b03840d03005040e410103d10f940340c0b25110401140d4180703401c5181800200000c035a90b0307940b00500c1c481c0c540000c10f920aa00c80042010031a540600c2d88620005007000b81440110083c140141084c03620b070048586100040e0b803500c0798030030700e040303074070003860b103036441c140d0050b02c20100141702215540204030518441a0320400008260000d8840d12070360308200c10044440300b40e224592102d03240352555602e00c441c5c000480d54032170300895080307030311681c60001044290440e022400025a000b400280890103449111800f502c2010309500341d401d10034249046407500c001d4054900300c1d038031030510116080c04d0240070701400c2241070900100703d8a2740c0320200941003c2d1204100108800c8141c01e80d16010400310051081e10712070740162694040665030168505c0c04003038020350440c00081d8550000c00d003224410002005541001d140210300751000c21950f05e020500c22000c0000000100300d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 627369379 1250 627368129 627368143
    0x601020c131a01170417120903120a060f030f260417160303120b060406170615040b180603100501080f0c091c120315120f030509060c 59
    0x6a4a40802c001d000c000311a076100948285260401c10082030034001109400742050f041303548141889400b000c1c22202031501d0040400141c1aa8042420b00088400000191400700c0c180355168407162103200180040ba8a24400c1d03c000d43d80d280e10800215400300494021140030340205c40703040215032450490b1003e141102e9400d02c001140507c034140b20800e840f9040c110240061489030b4045100c0a0103180c641310050070098008400d00c0d240d00d070f079000800444c1014020640b00c0e13480c0c01014000c0078002001041c000600c100040f0350303150000e0070a1454604e44000381c034003402c18804c121181d10182c44005108a611481d41490311030328011880b8117051282c20002c0b40c200000184003000142200940b0b201100510280d1400300d42100e10b868400c6800c10070320070101c0e0a030320b209201035801410300300c1d004004c0d8901a4050b00003482030750000202c131412903122500c5034540d143c40030b00a0083c904440000707001901820003000942001080642400d822020b02d03454004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 627370629 1250 627369379 627369409
    0xa050102040e0403090603091a0414070315140105100509060c0604080d1b020d050a0306091a100504030b0a0923070303020708070612020d090218040506010b03070c0b0601020c 77
    0x9000803c01807540c403100701006030009181c28001e94980361a803240c4038504800c01715054000c140460108104414800300018000040d039680981e02c0c1004034050420a0b020392009040c50a100d0120507608800d0b810394000412210340d44650000403101c1b9080244a80c1d08141c080000203801181004a0391056100e109000c0d52102c0407400c0c1c4080d03038004a2145401d80c0c46005c49102c264010030000350b0402c0e103180ca40d4540d101907a084015003110740c4000e0b486890321030a404a01106002c180700c100054908200f4025004400c035818411740c07101a08212070040030415112194000f20001130040c6000001020703035503100740030b50102c585001460740c80000100100b68040c4802c600901101000d0a0000c1ca00700c0b001d0009040c0262440c40c2540c00681000080b070141d000082ca1f907005402c1400e4091601c110f0300a0203404d50707003583e0308d20518000195410922040f00d104104d00d0b80c840076420b03042c0c1d90383c10241030090080e5040d8050b4903600c09a948507081441e56080d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 627371879 1250 627370629 627370649
    0x605061209010c0f1d01051c15080303010e070c05010f020c0f070f120b090106090c02100605040c050f0a0207030615060e0609010503041e1b05040b0a05030607110a05010204 76
    0x1c280498500d08442c1c00c00c20341000e12541c0401000515045148800300b1380b01c1d41c005101d0182c081004172807503c100c21114481602c540456001060a41c1c0100b1402c400800c144122644545013103a8a0100344614980b50342c1000002c1c2409114405000344036100340c001188105060382c4800590300700a8205407150f102e07400c60340d4400c0081004d10b009019981c40c500e03503641003100415100c8240c803c0644091100d40104200d1700d000d5100000030102c6000030048074482100003900c070880c0f032529500042c20700c0f401181614041c8a0503420011a4541074501900302c400d078000d0f5044000c0500c158011103000102041282c007070107550035440c14000d801e079400d014000d048c45240c0304da0940520b00c14084a217072a41c002c01105e0b0019000884401140c004c444195041c0d00a828018001401c52030140e0b099502100600c0a65030103e4080c4014001c0d2410b1040c410068401c1c030340d160340041d02080849014441040140180c0d07005d40e031010860351078441c00d81e41710341d210024103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 627373129 1250 627371879 627371881
    0x402071101031401060e101106100501092709261c0203091506030f0d0804060c020109050a02090709030b01030c060f050a270302030f07170a051f06050612 68
    0x9603814841c003c100150900801040e5041c2100203044c1c070b000d1400c40c1d00a101c040810504607000c1c800150034100301004a80341403424809848503a035203441414042110307900d000c50070690600c51002490240711001465009505154010b0302071140d059501c00303074200c50180000800078028241091100b4030079501c50320120383c41c0b8800c04640c1c55000d654410300910040f094003241c400540c50850504101766111000000c0c1040c400c1d6603080350921400d00d030410180d4001d0400c0d80f045004400800a038600e001d016030985000c044020840d81003503811400601d03010001507044501c0340741c240d80c4540c4030b5a0780c01c92100c0a8000b6940409210010032401740c3c458840c2100c180d81c1c0c80c0c20390500c0b450b0040944102840408120640e04072405e07280e000d042c0c2d80c4080000c540080442c0c00080302290900c0e1505d100340101084a0100d40c050341016034001207070500c2980c400c00034868201e4210020484140900c036642080b6101d6034001555521100600500032000003e4181 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 627374379 1250 627373129 627373163
    0x1b04170a030e03010b0a09021b06011502060a0b013002070804030b071403010b03074b050f0903011d0d1b08040302040207030c0606080d02100212071d040207 69
    0x410514118018400e030b041101c0a41039841b00700803c0200d1b0010100543c40e000d1904400c0a4051080303c01c01240c498480006184160404508502180d507001c0c1d8505444401804080c0e409503040c103408a00743c03d0007050084451408502245001004002280160041c607800d99001003c01c1e2a0b41402040510902075901c0d079494015509061503d69501c1440342c00781540414403520312040c1012000800c1c00b0b02036502c0c2a48243e600401c0c160180c01801d48440c0c0d405c04501c102d42c019600f1444001c0d0401a06240d10241c440791203032420550a211210f0141c5e1180c1e80c401c2d0075540f950540248550340e0280c45a0000d401c1c03001c0c0c185940c1c080c40007814940706491600302c1104240050010803000001c036810303680c042d1405030741e99109090658620040110003044186030200000c1c0f00030000c680300c100401d985d429582c4010a00600200381e0040c9911112160140008581c500e03010f800c0c001c2105401d96400b04c054150030001804a801c500010b5802940010b40082 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 627375629 1250 627374379 627374387
    0x3050d0e0619050c0307020d1202040b040608011d150409021212071707030906050a1b0c1a0708091903060207030302030105330f0d05040c0801050c030403081b04170a03 74
    0x41c4c44030001d0a01d90135450282d01c02076480402588031024030001e98100380305400c0c640c04543c080e0104034001c0350b44982c2c600c0c008042c41e500748140008000b40c076443d03840e600600d52000b8002d4100d101042c5050100c0c90400004103a4244e040343d104048035400b2032020070070b0020001c0c1d08643c8103060b807582082c3c02c14000d04543c1140504002e40100420741c0007a4008180c2402d560051406079102c1c544400243c40540750304c1c42c034a00130705200800c081046217500040c0140d40710f00c80c01c80070190701404218042e018214005001d40001e00000c1800e082800211505c104528005c00506941c0d403903074000c0341d000c000c09400181c1c0010040c40607003088624003c0300784c21190b141040d600d04070200201c4401000c3d045109680000c6c0c0030717021040c45170a9030b56400700304400700503030f0900c2e15100b6912111449008801d5080c000000c803a02c00220a50b44655011b884000c1c0c140d442d0404c10300342c0254039410240000d0305120100340e5105400308180a03400b150014042120389080c090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 627376879 1250 627375629 627375631
    0x90e10051302032b18062a140c0a0b03040212150a0203160905090a321504020403050717030f0a032315040506040e030c1506061603050d0e061905 64
    0x10305c0b0429003a51006008a4070b40700032a40e01d480e0801000c4080451340c0c0c1110820032401d08405401c0504009200c1d00d549121401a003000407540f000e40007005224040d40315200c0c81d10f0310b00381400000e0160034194080d0941d42180c1301034070840c0b000c0740100c0c0104001980c90035820b036800b0080140a814442200701005214102000c401d13188c00005142654014880e200403610381c4030b000c28502c4110294003449034600341f4030704056009541c0900d03008088481d103000c0385030001458010b05251007290b00703403500217014250796410840034801c90003410400103007510040210380360f20502c5001800b6005c2c055540411000c600c0d00c90344103124060700004070301d4401e000912007442c800400300c00c0004000c0d50003040507940d12000400828124108002d44d0000140c0303590081c10102d940c0801025440c14900191600404d20803036004092000354000500344990010a0045000d041c40900180e0041005100101c0482c18910140c900c4c804030042c0b0901d86c012010035000305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 627378129 1250 627376879 627376963
    0x40b1309031101140408030601030902180901020d110702030703031b0b0a020a020d030b01120903050403020901060e0306100608070302070f060f0615180e1008010501120c090e1005130203 82
    0x60b81c00d03041581b2000043d210140142d8149941c03064080d04648462042440f5805071000c54aa06d00c0c110035064040c0d806504542540c40ca058a80803596410805840900341c001d40100909030445c4d50913a041400c40050fa501c0040340711905000504422805110780d000c01800360704c600c031001020745000232402080d000d242c10a02000f0250740c0c4403610340c003000d8800402046a03599800c00342c445105541001c0d4000801c9000411441d07000092841020819011264190348001c08050f000946002c0c000000344010080744036940f1a4001d04641c1e400791003005900081030340c1e62822900e0702ca010121b01c40d11440104004250b40c00d1075603c1845a082090300a41d07030410504171410035000301011443c01101094044002d0180f49010380300d290000c01865031280340c505a01d10f0038400c201d464074a0700c880498003000c42c2c01031441028100c001801e10f1000d4140c2e11300600310050003c060800150f038254056a403c001c65186206440700b900ca92000c00e0200030400b07400c21140c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 627379379 1250 627378129 627378161
    0x80f030a060512420a050108061609151215080c0a05060403060903020c0303181518100203190c15060b0301140604051005090406150e040b1309031101 66
    0x81c134189002a0310385440a5038507508411806041410000325080500320702c41209103c000800520160550116060700c8052007100c00c05e5940d00e035901c03584d03011031a0100c0080c3d0f21200c1001144140a0450019551803c144641e00383d5440b10904507000c03654010643c00420800708443e0005101f000700305401584c400700003505007404519941710300d00c00140140c0d074070014034061501c00d10140c000800c00405a81c1e0358003268100c0060074038442412481009005e01c8400d01c030100404842c0d81c040314a094601d210764550420848061006214040d40000c00c038050407007000708400c107500c3c41c494942e030819083c1e42c18211032219110110506042c504002480010000b90980c0e04440011161040ca00e038403a020402c24026503000c07980142e01914512821074105014106580003078404002441c0d8581d032074a805507443d0b0005000c6101041c0e40303049820507030030006840c80007601c0081c0b00c4003040c0c0d011040790706004040e40010407554601d142e0781400e028001d8a940000300d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 627380629 1250 627379379 627379393
    0xc02130c0305071103040311040902060c07090f0b01170709030b090d090906060203091003140406050f090c0a06120e0d0305180705060409050a0b041b03180f0b04080f030a060512 78
    0x130b00c20b60307207100303502018142800f2208000040c2c1d45640144011650140c42c950f00d51424154103035495040e80208030034641001e1024003841c1c500d2107050b44200050b5986201802c214600e0401e2003409003615040201c040e5012000c9650401c1d03080c0185070100043c0f045203504807000b032a13120907401001615040001c1001300da5400402d8609080d02100c0101500c0c1e07115100b030b070041140e22400c58420429104010512411782c1c0818410030030208414000da603001103254642c1b042001ca990f0040c45820b0905c90b992059155001400c0800e10014a04c80385404407440c1441c8072415200003034586c810000300c401c2078810000c800000e04000e100003401c00c000030744903029034040e02010b1560741002480030040c0345c00c081201072025100f0803440380014892440a030312100a00086804c01c284240080c06209550a62542201c0305066480f242e580c7c00303071060f50181040e2412034043c014070098481180045005094055000802503c0d0200340103101151510400490700400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 627381879 1250 627380629 627380657
    0x4320114040b0708070908010f0212070302120106030f0b09010909120215060405072a0209090c01020303060910030203121306050906072a0f1a0901020a080a0c02130c030507 76
    0x11081e82c11481130300304a0f4443d659507004071211000c691201c00701c0c2d82000d0001c641580c0d2a070041029590481e41030740c16a951007415010303480b030001508001e1100e00010001103104c2e074802005924928404103401c034010f0001a603466080c1c1251980540d200864400c000310400e410425910354005070654080310740101e414100000c201500464031080000d070300c1ca00c210349503a071a6400c01d0a805450f03903501e00d007081101c09454100c3c0140004008209411170000d05a0b012000503030086165640c1d034810b000c19450064804442c3c03200c0002c0100040e9000e105801da5110410030032030700c880300b26a18a00414503540901c091010420400c0140e03161401100e01c0c09801c0f015124404c041440607003081040c07030010146080a016012804905040042c0c085502c0e40110103001c081c80008442544101a803480c0036a21051000b00000c51040180801c4240b03030a01c10240149500400c103071490448280e00c030b00d907032840c800280d107070584146a041003852900e2501d03d0105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 627383129 1250 627381879 627381893
    0x90911180409021f0924020d050c0a060b0f0a060f0f03020306010e0f031f0914012f120c1b0714060d1d0312010b0304020603010e0432011404 62
    0x881d43ca075600b000042140e1040a0103148150000d040342c0c80320a822100c241d00a402d4a86c0c104000b00060040712000246280305e40240e43c40c4050000c0506000200b994586004052818030b0035000402071a1854103541c4802e0300c0001400f2603214080c18035214030006205070001c8403200305061040c003d004032640c1c0701200c002e2200d002d46400342001d00420000e0301d00740000303001421110050700d00d0800c0238602d07040103600510070004060412405041a4241d8010012800b103e200c0f00c49251290f58018060170f02c01000c0001e06803401150141202c10500c08590400c0046000500a01d095480c000c80d0306d0b05074003c00140412501701801080d10080b0070342c000f441113402045940041c81540d0086d8000b41507035111084184a640e8419203079007201300355a0043c80385400001d2400300720400c69109543c021305a6242d0f0f800d1500322071204401a2066030941e00503c440040c5482d1105c40c49103174043d100004901070801c01c040c40c00c1d102201c48402050005405000c002004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 627384379 1250 627383129 627383149
    0xf030322110105070213060603230108280f03020115080309010e010518040501080706020d080115031121041b0506030606070203010915020c15070f030c09091118040902 74
    0x2460b1950313441041e0700001e00211035007040c80740d42601d0800005901d41d015030184e45031200480e003c181c01991030303180b0000e03040c0922808805801c41c0c4c0d04408516910402c4640c0070340e0800c1c6812300c0c00e01030303100e200110b14080800c50140c1e5403000c00b200d40d091082001001802d545006501e011b50001c0000d00702e61000602c14140030b408104804040700140c0b01194510024100f00895a50340e4a520b60341d24403481000b002d03006e82086504602d02c0f4020450507150301e04000d4840d90041c0c0c800f00c0003003100700c40910500c801445040c0201c45a0740e402c443c1d502c00c060718a0740714280750031701e1800810420990400d10b102407604100e00d88411055a0388048221082c949400c0f5500129024110b540c1000748031504090900ca03000d035641d800f502a0301040400c44e4180c0e1007281c46007101703c905541e410040b4002c01000b10465210790003c0000810030703c0c00c01740190f0f4482052060700c582001c403d421200c0841c0302c10700c4104200142c0240e00c800c540c1803203160356a070082080100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 627385629 1250 627384379 627384413
    0x207030f0c0804090905010209040c17010b280c050f06010f0e040219060c0b092d011401140f270a020909100e070e060301061803050f030322 62
    0x1441c11141c0003403144840c2520010221300400703100c400614940b0794002c1d03025442c0603205070314001c0c001c04454410908849a502e000c8030070300c401e07420700781809500e80003c1c00b400300840000070701c1c540b0000300b10210f07043c08030661142d500d05c4c4640c0c90201c0c140081c03d40c03102516800440100701e11a016000b0f001241e90b1700ca16015591030340e001161b8840d103580c41604840402d5400042c02c03d910083c90200d03035019070501e682a03154950802e84810524000a101d03003802c1d5500b0004500c094104402611070600014690003000481503990000342d000b4000a9018a0f40355038031f0a1a402d010200c520031107403c0c0311804444401311203481d000000301c07000d9488400145120a41d03504580402030005c6c4103602520348051055205044d600401c0d0540040c43c0c00314040c0c0380118a001c0129000038141e500b103030308002048651240c0b0241006142c00c1d40c07200040800e0091100140300051000915581e140c11007420103591305003840030010043c130600c00800b0034540560002d44c52 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 627386879 1250 627385629 627385637
    0x21507091a040b0c0c0a090902030a03080613090c06020706020303010f030f02060c030414120a120e04150e070806031f050a11030f040302060c0a02062a180406090207030f 75
    0x4030190704411200e02440d00301600d0b1142c0000d18800441c0700050070740c15520700300c4500320752903180c0c42c03070300244d60b50040001d4041c0c0c03012004c072002038015240340303500c03075000381c4642c00c1070f0303040d200358015600100d50aa60312044440e0034006140d0610001c00680194002149113501d0032003215007001c0244406825141400341000841d501c502c03c5401d40708000b021030b515580c070b41c0d40544100c640ca07510b00d88214143c080c642000300010848921041d0000c008500d072108008050303d10060620104e68002da0b64101a00c010f000003005002500010130301c1501c0d07280c800000b400b0b020740501f0903031196001d0111a41540c80d9030202c00700c0c0348100080410140c80d9450810050852040c2110014001100308101c0c600c84056061245000360700b10b910a1700d610240300c0e11031180846c1c100040e0800c1002481d0807199201d00c191042c03121159072051360600c03c4400250700f0811061004030ba5140d00e4980910b00f9004110140940d08000c624001060b03401030400790300c2c950400280 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 627388129 1250 627386879 627386909
    0x2130b0f042a03150b030121022215090912020106030507090c20031809060a09110c011508010c09260c130c0305100b030601051c0c080702150709 64
    0x1840c0f003508100c0458004041d4a410b00c2d4403049071041682090040000303031400501d07203105082804001115083c0c001c2c003514894059035080a054800e204c00a170507035503ca11290354007041007a031403401041c584000240e00c40036403504106c0c1c41260b034442d9003168103086d02031000c1a80460300c1000c48003180070008100d00e00034025181c0090002506080380c21007400c3c08d0b281e410100041c00d00f10601405840034041200070400f01c580141d03a4650011403807001402115a0780c0d01031058010038080c07903070038041c00c1c00d20182518401001c000480540d96002c001303003031003405500d000901e1410403198082c20464132180c80c603a443e0081e01c8040c112594030360050703814004011142d00c0a81010014a602d00c44203000c2c2440c400b202000a2070540040c14840844241e5420b40f402044036614584070a001105c0c103800c00f900d110540800d03071018600c203003231a12030492030100e9505c0c3c0d826145032803800682802c0054100802905201c410083c070350340d00003e450141d603151241c40080c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 627389379 1250 627388129 627388211
    0x909190b09070825050d02090604090906060509090106030f031d030607020105014403040b03160f1d1917010e06070903030507030507080702130b0f04 66
    0x34254514040c0d4000501d8414816a59401000c961090b0301204030826083d0303148040384550700c0b41340303562400100c043c0110824030390580c000f466a8900144603c0c102034599000e90101c5c1c00c40c01e4122551036840c4800c000d54108030503210782c031a02e40c50003040407510790b88600e280b00b00c8481001b010008141060205442d42d034002c18103402014040f90760614002e01c019000302401e01840e000451262281e0300c1c035a54140420b0f402e2501c2250040c001000822000e524800c42c2c0040803441c003090101080c0601254050340c0308101409000c2041c007050f035000382c0110a040c21100821095007040d100c00d541c1d44811805030b0b002a41c0c406003100180ac01c06001b18100d8110101548805184504e041c41c1501300844030203000c0c059444544032146c0581e050113607440010701080082c42080086401080034103055805115010f1030002d8640c000303911100640580450700d0740c0c07043d5441c01400c0850300080c038102c0a440c1004101c1861070009003032101c0c0e0640300790450040d90302e03100e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 627390629 1250 627389379 627389381
    0x32307030b0a03150c0e0a03020d060e0309030a030201020a180521010e03070606091a24040b07030309030206071d0603130503070b0106020c06041401050309150703021e090919 77
    0x1590003c082136140310306007550f0f401070800381c1880c40000702d100e40a046a0300e0004031300c404495005084c07403000d034040c0c0e4510000c2c042a0b04010802d000c00c0c8880e1400c0d840500c200400b09109500060740c07000402405070024500d1600c032449002c2c07110082c0301a89960494840341e60282c0d01c0790900003984040140581800843c110850001050300803c011003030308443c041d0389051409006100e002c2d074498000a080521190b8040c0241420741c3e00c0e0b118070003240585905240c000c900d40340d01e0310342c15401503000d502c0480003e03a07113006803c14598140540c41c3c0045603480c0c844114491000d100380300b0050a403006d0b11400c0300001042c60403407100e03041624607a00400351380e160000c0d41402c00040c1c40910803180507005420510300c4601c0c02200f01c42c00d49500e2a610680da0456000455041d000102440740c94801c0c108203000100c83c0c060110320480c40c80d42c000d0380c0c82054411010303041880106207903008205008000f080d5455018450348011f08401d00300c441c8018041e644 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 627391879 1250 627390629 627390649
    0x1030b1f0f0b091302040909051903051903060b0f0c010c140912100906090507140604090522050102130b0f0a03020f0706050106080414030304170309011508030406032307030b 77
    0x11213640300090005c0c129515420100010340076105640300c0b91150b80078400f22107a40741c0000c001031002c21440203055510084000c8031310f80740c03800040389615003071040d115074040f0750708100940d40412921407000c424019074208070058581805d035220058400d26030360162612103442015509c000ca20f048200300a0300407130702e52000c000d101d680070b03600b843d50003040003c00543d15400742030300200c1e4580c2035440404650702c014050501d85440c00520b280149000350541d410305134045144814000d0301507200140a01130000180d540304075031010a042141a44035413014801031184c6080310550030144c0e1024021420051707940c80030030740b81160320322074801d000305100d103004008a00b03d030b805040e0381c3c440c9105d018211741c1240c000b4410f6640380822a4010700701314514111080105024002c0c42c1c2220301040046085580c15081d8005041144c2209900e6400881c003005601d0341805036184161080790030042c07240c080e140c00c43c00ba220062441c0d0a050321808140c0c60340c0c0380d401000e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 627393129 1250 627391879 627391909
    0x2401021f0b0901090c08010503150a091401021908100303051b010204030512030105011407050606151c0902190312270806040c080f2104030b01030b1f0f0b09 69
    0x101d0710540c1c68640010003013940c1040c00000921b488004142c2c1c1c140001c2c45004000c03550804c0842c0e81e500500301c80603100705541110191008191001d260380d090002d84040080d41045030140349243c20000c000710001070040c55469081c078400c0011a8018048448210303030701e0100c0e180603040307542181c068469036000800d135102d070702190381a001c444000765050710003d03a110784946c001100001d24602400c0c5010f04a83c11042c00b00b50726240583d0b00c00a00b072514403205050403043c1c0c5003a105406001c075101d8059442301d164a04524101c00b2503c003145c1141506407509045840304401070084a20304000c0c000030540c2d02c92903404404007031440c02c4524800c169656140d690040d00c4407801c0e5011100720308210004105210301090030919920322000518981502412940c0030b8912101d1300304000208001c088003240d8021403da01a50054540e075410f41000c0e000c803025001c54841092001c042d4010a010240c0e07d8040c0c0d00c1210f0303003480c4603512800fa00c00060300c256184014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 627394379 1250 627393129 627393139
    0x12040c0308070813090501031203090c051c0c330905031219021216150204090917040e01060f05120106020c040c1803061815052401021f0b 61
    0x240404010488005006104c0d10a0400c00c5099942c560032096405c00e000080842e41d0102088007007920a5020079421030080e0030030711646130b50310040b603680d51100d203100c4048050750340c00000784902d4800741c90084c0f070112400001c0401682d580302d2500c00444815501203c0c20b00b01c020110300c00c02c008000b07040010180c84101000d041d03030155544c0401152841d540c1d0000d00c034480c40e400824011403888086c070515140845565200462000080c002c80e408070b00e8104118400340c0da807000d44050001110002500c625604015600c250b9284d03602003070301010041482010403050b1080d0444e5035609001d44030990300706058509004090b0b541e00104411000020041d9000941e00707035502003030781c0401840035010012103081d0200005140140f1001c44100002100b5030320110450424045164036071200c0c0d582c60030314036400c0a8684500348c8460502c01c0c02200307019103605291542080b081d00f42c0c140400030b034542d2020720240600c142050321284107141203810903440c2c0d041c0106 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 627395629 1250 627394379 627394387
    0x20703120503040b0f0f010312030f060915051509010e040b04090606060f090605030105091b0403110a0f140907030b030a05071511120a090b040b0309010e010b0612040c0308 76
    0x100182542c00031201a0f409042d42404100040800341c84503004482044400000d6030854807408005141034101804042eaa61300c1c051401d6420700c1848082d054070b040c0816449407001c1082024110381d08510320985048141c020b80c800380008a4000803000c0c00c044030380010440c0050010300c6100405a0403504003004001081801e500000a641c0e4035115407110745903044040b80c40780c06a0080c030010540400c010b02081c0b5006906aa00c0702040c1c214504000007000c28200b00d40080e072048401d01000c0602030400d140000520003e0103050403521505464042441ca8124070031382d00c54014890007020800c801d00c80d80229181010280465030b40d0000c600c0e02d05e55407a014403c5218000411072404203c0d40f15074003010114003004000c0450a1038016040c225900407540c003410f0103042c0c9000240214142c015000602c64200c40c140c50386000f00025003540c084038000700e881c0e490494001603940e51481a0750b19419550292165a903403407a0060001d0002c0d040580020310200d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 627396879 1250 627395629 627395663
    0xe0a03111c080a08160905040e0c1002060123090a1d010509070e090114060108070207090f0605030c090c0f070507050901030b1608091218040507091505040506040302040c020703 78
    0x1c00286500038490ba19000d0a996018441d20b00260080074100019080c1b07001704000c1c40c1c0341d004200102c10807020380380c07841e25440001c0e01c000c0e4100d41020140e00403c00401020002460103c03400c1c5201200c0c8415616040c005041c0302001405119001e90320740c40c50040014020b86a045580300c18000c01003400c1c011012036071101507104064040e00764400096030558180641c2e0414a004024032031582c40f820015145020002c11200851252100c00620424540100c2ca1030042d44c21002400600302014141880048119030707015079440f8003805094541c5508035011520030b8000c158032000d41c2d00e81541801e41c0c503030096034080b1160b07002106001c0740d1241315004a651001200030664151410368141000b100d102859070003c4021100303c140301c2e07008007250f10342e0f1101d920f800c0c40071100140442d00181d03107540005551060034002400c0010074824030b40d000e0709000b03003420b04d004002082441203010080c0100e0312281010780c45ea008001d1200550f91082d4060000c140351 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 627398129 1250 627396879 627396893
    0x5220c0b0a030b1815010e030604060903050f071a011d0c130915090605030d020706211e0f15031104060e07030219090608040f210903050d0e0a03111c 66
    0x2174a80011048840b024450158084e280c500101c090141c050200385e80c032a1a10070090040c00340c1a000d009041011400c2034101a0080c0195407246c10f50040c15202c146001c15030302816003109220390500d8411035240481c0e1805950700490300e203e11661128400382c8185021010791210702000c0c181802d10040000105140058070380310881000480d603940f04045e9900c0b4803107001400340c1c0000009100e080d1103019400900c0705048002c2e100c0e008030301810702c101c4d4101c842e02e00031040410312840008816004081960703560ba001405101d0300c030080c041c012046444002e03c6c08400c401003d415864030b4101c8001048418010b001b03510b8003841c0580694040c2c05001c014051000c080b0304074a018401c05016102c040d5550401c503612655018850380c01c0304000d483e00c058655020040c090251010795001c0310681e1003c0e007003880c52406034604000041003c0c144010756002580507118202000300716600403034200280d1400b40b010030314000702d0800d40c0e010899800000001c0c4824 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 627399379 1250 627398129 627398131
    0x8062808010f1b080103060b0d290a0e0d0804050a170c0d0c110d02031e010c030f050112030c030e060d0b0111010603020105031b0f03070305220c0b0a030b18 69
    0x2400c2403d01c240c403183c0303069001d1000010300b48004501081c0042c0086403952344220440d05003d09014602e070855240ca4140c0f940c2e400d4211a10b0000e03030184102c501c1104080ca81020400c0c01c18000c10f00c20a082c2ea0300e41d0704200c040e0007040340220000701800400c101c07036514190041303003007140c4100442100c1404d60000e660090148501002d16058510030119400f0194204100c5d0300c1c09400d0a00b00079000f4038990050382d15210706c0c40543e4581030745081c00c11070414400b00004130403060410180903900601c18041185240800402166145a8010784000d0713040c40c1c2100c100c5080d15040c1c40e6107040c1008130b41c0003440407038581141041940082034254090301c4d00c1d0b81c002e039000da40780d082e21a10b00000b0f00041007400898079101c20000345042c241011700c40c60b81040c00c010302d05c5d2240e0300120348990000e42c0319070502c1801032103000e40c51201203008a900652606940310600c0c6032441e4800c200b010240001c001130180d00c6035004c64044980104081113350066a52000c00341c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 627400629 1250 627399379 627399401
    0x70f14130f0b070b0f06060712120b0f0303160302160312031d0715020a0b040602070606080d0509091b0a030603110316050f030a02091009110a0806280801 68
    0x2204420100349151030702c0c00c2e0b034056a84183c0c0b40c0c10b2940c40e1504075904013400f402050300002c041c05000300003182505440750302d04941da200d200e0403444044000540d001e811000d8020b5100c80d0360b103001c0d074030701104507282e5608203c9040545081c42c0b504034509031540d40341180a42c0350110100410101007841c11074442d5942d000d00c0006110310113402005016055446158420802002805400308001d490703600c6a00603034000700d1150f1122204900202c808503070340c503400a8442d0401140f4030625000c0c10300100201642c800e00308002e03101e4440c00100e2480351100c83c0020785002d11804ca4034a825045c02001e03900d076809000c003d805000503000841c0d1030807052050f4007c90400198400740f0803c41c0d2100600e440c03910f404d00c030034070600c0108660103000305004500941c40d5510010701500240070315200081c42d00c08010304683c21003100c1440d00e0b008110222920358018500f540181007141c0c004405854030f00544030360ba5064120016508910400140441042d88080390720a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 627401879 1250 627400629 627400649
    0xb25080f030f16030614090c0c011104090c0c02060f030a06050d05030a08010608070e01050705010e010c11060105010c0308060906031c020f07080c0907080702030c07030c0302042003070f1413 84
    0x3421603c4140d0540f00c4500403a220060380490440c071610b8400c00c0181c0208541e0f0007145440450502e203401e441448505030200040050704101c00c2600d80b19043c900c854500d0420300004403030740050024403c4034044440c0e1000807011034852526580b01d0802010000d168003079006041c90040e40300d4200e51a5140851044400003422502501445100e03081070380d5070039a004901d0005590f03942092802780c2d01e541d42e0f0180310158100074405c020703031142c26032a540750b03890226001500e024816007000d4104140794041c0c000090300099541c0c0c00c04c404a0341810035994200110707251180c1240026904600840c540c2c50b201c0e00031800080080d107800550fa290b50329860500d555031642900f00e44c2000c8480001041c0602c16000380c1d40000651042c0d924050944401c14a4502e8a400540d0b200c050751408008514051107508903092070342c5e20140e1141800c280001341804010020070034848900e21440c0800c0c41400c24100070700520701c060340c0300c404c0350340b00e4110b100c124002c2c51800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 627403129 1250 627401879 627401911
    0xe0c03012c040b06041d030f0f07060606111b0310020c19230105060f0906030a0b2508040c0b1c020409020a09170601031b050402071109010b25080f030f 67
    0x880e055404c1b02240000000114a0510b054101500b19400440410110402840040f000032500c0c00b808000b020b00d0359401e040c126076000e816081a0f20852000c031140312102201889440c013080ca0b02414000c1c0d0f40040c0c80700b0000c0c07641400e001181940036460819110044104a0703014003000e5808421072030980b034007020703000960032220180c400a500800004944020f80343c2030700026807215010b01560404200c40d03450402c01302041d144086511807400101e0810002c0b909640040301c40762505500c20b003042d440d04c1032090014010709100080000e28410b2803078000000c182d40005a01003196a240d840c01e40400070b4000440f4640081c58500c0c1c00984030708900e000e903e400b00c036000501007a07441d55445090010191405105841243c3c20004170b41d5200d1000d004a54050b80c500c8800c0d03840700b401c0000c80c0005802001c000d92050000038801209203000540d146040300d543d40c0b1a03149418110145d0080c03a6841007050030000c204144503100710051030041e5074004441c201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 627404379 1250 627403129 627403151
    0x150c0309050312031902040e0901090501051e06010f02121c0b03010204050112020c15090d2d0818070b0c011503020603040b0712020c0703020102070e0c03012c040b0604 74
    0x4941411000b083c20f08428030210307035a005055900a0200c01452005181c55034811100e502000e00310f0342c0900613503469080c6403e004080c01410351201d40901c1c2c17440d45840d65480c07189070b003c000c2d0103281006541c1502c1d404c510f000b00034403000d03c020054000e4130744e44002c807544440ca00600c9611541d82c1040c618510070304050081e1815140140c40d50030540409401460080d00101e401a0b40c6102d010901100c060b82d4001550050b400f44025098207030b40c0d500003412454114061121040005502c4030340c1003510440d60fa84141585010504c2d5242d020404000307004101e5448554081d0000c001032580d005d000a00300740c40ba25009010504105c6590700e80d40005200194101c0010030015000404e4913000c0d80d84450b550038407480c0d1186802c400701c01c9030004030310709000c1d91140d01d0030f00a560b01001640018610a004580145800e041e00c0d49103000611850840e60003ca0100102042885000c2c0305842003003040c00651920b4288000302240c01c0c0c2d0f0300b034050791800040b000c2d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 627405629 1250 627404379 627404383
    0x61113080f0303011e03240c082503090209010806070828020c0a0605010b040501090b07050307030e060d0c032007020a06080a1805070e0606070f080a0306150c03090503 74
    0x40d28030074014509580c6080030078001000e0b02049126030100b0720710080700142c0701da109107008030000540700245050900d00f00040307440200030501440700d032408000210420042d8508c9800940112400d0324a10b11400c0c1c0c007a040e2800002d5000701008008241e030780000803d948600c09a5817610043c1e102d10241072181070710200b810039120350303403c0c039804115a035800410401c3da0640c2102c4014103140c9031307030381150001c0e0002c01c54641c001504111f07940e40095038401074042001d04503e02100c690311581d49101c0c1035001001d00c80740e0300018000d541c1da80705489044050035014032540032b581c40f009000b800004024180d03600864a21141c003a064411f80711010303805401710750075508106080c0c845600040a4243c0e031034a0f06040644000d03000341022146100b0f00050442e1810000702204505005240758020070060008501081d42150383c401ca45801040b050b0ba205440361046002d0089070f040b116801d40b010112428207a44018441d008a00942c2c2ea54002c60722401059 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 627406879 1250 627405629 627405643
    0x9020f121812032203020c040b06121f0b0f09010305010f0e150312040902030114092217040611070e07020c1306080d0503010614070b0117010906111308 67
    0x7800503030211441d440034604075001950003d6040f44080214484a00c4403888514030b590f003100141c0044c00a15224101402018081e0740300303e808600300701c0b26010340030504000410524000b800d070301c020344811070101082d0010b054a560a5a5580074220900f2103581c000d6240c0c41c00249004000a1900c0050040b2000d0311281c0b04645859211401c0c081180c1d003201091a600d4000d11010120f80c1c8031440c01003008210b184005a125890040552550403103800d013607014146800812400a50680310509020b48040352031690714464107010000100400a4002d54480000c01288994104511503940700c141c104450000391103101d85680e11105880c0c1c240968020305d225240740c071f002001d13a0300d40900d4150004000da47e411005103030128045481000ca480040180189588078198282480c11200d4941c5011280d80e2080c400310310520a03d10304988150b0701c6e00c0e8600b429003001031030340e40000c02880040d60b05c207500e03200c5601c4080c1e100301c104452040011400004a41a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 627408129 1250 627406879 627406921
    0xb040c120b06010518060309070801050a0e070e1308030109090b0604090507140607050106030b010f06020a03140d020c0a2003060915130501021303031214010311060409020f12 77
    0x101e60240ca8040040d2a25040040c1c202c1d90341c1c01c9100103922946401010310b1040c074403c401441024070744030301c81e42140c50140402018a0400e0064910500d0000b265012501d00c190109059a1020798040300020341c0b4400400311a030002c000a44da80d0380d50080318074540200c040080903141d0008020442e19030b210f0040003508101010000b96019000c001c4c2900c03005000140340c511607507161030864040c0c4d0811036405100344014000c5800011860001e401c10340010078006800751405041002d9140002ca014000000c0d0900081595015200c4031140304007215015103243c41c1103003021011050056206000c0300c43d50b001d91074000750b0305008504400161501c401e00c1d0aa000b82008010302108521410300004800500240b000340608170b40098040c09107030030341c98000c2984404201c419035030b0381000c04204064800008107411213611020104407d54150081540b90007650302460b4640e1000c500821041c94410080910215200d00003819a030b540c2110882d107440700c050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 627409379 1250 627408129 627408143
    0x828110102090f060310080105160212070f15020702040c0e03192102150906070e060c190c0819110303070c15030f0617010e0d020a1b120b040c12 64
    0x14000c442e05060000f1500039600444090040707447e010400e09540781a52200d154800c0303d0300c68203240380e05210048182061070702080c600b04482c2c9600190405880380a440c80d00740500b034485081c40b0f541111951503016000f44859801e584d0058440420140f10074040e0203103000c110030840711103940c286801d9200c0c03041c0b003070050356040f200c3c040c0c10640c1174031041d0b2040205281c015207681413440d1040d2044001406145040100240501103032600c0b1402088c09101c11032407110040750303010000d000c0315103250821981c3e0402c03c2c3d01e003d0b20ba02403516070158030207003a99141d032180500c0003a4001c19981020700c01c54002d140c0c3da4410100007600032004140c0510101d8402c00c01ca4407894401c2c58040b41c0851040c05210865030140c1c003100c1409244000c0500e8180f0070b002c0c1210300f05040c0c015219110115034040d4a0703201c2d0000040c00c4451424410560126010003200a0306003405c3c03141d0b0030350141c540b00b100c20303806807019a80c43c0b100b402c0005511107803c0e40e5a200640c0640 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 627410629 1250 627409379 627409399
    0x306010f031410110703020d030510030303051510030e06180304061211160210020c0a14010507050f010207031206030206040909050a05121903061a07082811010209 72
    0x714440891915600c81d80b541c0507180c280c0205068a00440e882828100e018035a1584c9a01e400791800900461440c18542801c04000020760240c8200c011a5018100400c2c19903811301002250921841d01036404070000c0400c983c02c5505500481c050b481c064111030007034940a07c014504400d030b442c00c1c03089600402c42403002510503c034101182e1003010340071920b0903000c2c082e60758541013900820450350280340e030002940740440170386040101c140040c01000103010b0108a100380720b80980300780c0040149025210303912410848203155004420307a80d20102c801c140300c1c0070f940704142c180c00040600074088001c40e1207110b1201141d80c01814640b03000c4c606100f607006841c070f1660a4400e400f65644c510007152081c8000700c0348181160017640d132001d03580340180e503031600e1058010030507160017801d10440400304230324070520664050b00c903101c80b80c1c0d18100c0c40c81d22904840706000540c5040800b091201e0b17207000650a01e091700d520610a0880e44110b00700d028942c022540180141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 627411879 1250 627410629 627410633
    0x30c0706111603030903030f181709040e0a03090503151603021b06070909020f030c1305190e010b0c0a060f1b08010305011401050306222901050306010f03 68
    0x2038000c0203458100c203907460500071840300d900b84410782100180e000c25100c0c0700050805900d4070841c91100550715040010052000040e942c010b5801401800ba40450801400c40344070b00c401c0c0c446d4000000d00a1140398911a03005071240c20403803003100420302400c004503980c58041480403006184100e0311810740c0d5102ca2042b00b20a2070b20780e010504d5070800258030566101c0c0030001080b0303500401808075051840005140024030742c081c0e88030300e2042c1708406508071008200c90f00150f14489080d180c03038a9550300303650000640d1060303a000c200001422200c070a4010708800b151400130f4541c2c0280e81c1c5c0c05140380316100c0c001001d0070740e401080075003000030328903845051801208800025240c1070303030405107804264445400e0210340042d00400800109000b0b8030b00c9400e40d0038009009502d40f4010a40e0b40001404001035000a881d0000700200720001c1c14808a0f00032403901c10801c00c170020f864181c50407030f91240310700d805500042402d0034006440c90480c0c040103401c001c003034615 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 627413129 1250 627411879 627411881
    0xb09011d040b1504020309010b10050405030723060408061b03040c0e040f080a09050310020403110d060b04181e2f0a090219080408090d051e0601080d05030c0706 71
    0x20495400305001d105140f102e0f4503030784013445c814500c440c000500031481d07604008881017a5940701041041c100400c5c05203031404100c02c0708840d00714042c030300403090030400303001100c4205607419082a07011500041c5075200103003d900030b5400d510030b81100105000c0d040c0070352004940c090a00e15070100100140c040d60718215610602a4500005001c4181e80b01d00c582c0e408038200320001550920305004524042c071080180e40005401189814519a104085903081401c42c0f03200b03841c2090204203000003500021001100104108425602c40400882444030014280d83c50600354011002840c1d24500710300c180c1c2e8100b003407920700c462124460400e5090302c41d0082c0d200128140a02c1d40d035100c4945400240101039809603c83c0650200d15448402414402007048421003d200225051104035008918181e4505030081e207903080041c906070b00031301c4c0c1c015054241203502c0c40034080070607041e041c0d99040c01030710003010501d00300b00c0d12400b081e0b0b85103141d0902005000c000a503a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 627414379 1250 627413129 627413131
    0x71205070302160609140301051b0a14040608010e010b030405070902090d0b09030408010e030a05041427040204050901020a02101508150906060423070201020f0408010b09011d040b 79
    0x10030b1040398154115409402c07801080c542c401800b2a03c03400081c8038600d0201e680340c248030741c01e900810403407074440261082500d0586042d0603000c80011501941071041c00595030341d46000100c150749a6803901c00800c5100244030b90504640c0c14000030540080c00801c0301c3c003071508280245601030a2025920096128000700340e80302c1043d06660780090300444107241325111840c09152540d2a00f680b0a00b0b640c1490100c8526070802c000e0b489105401c8419034040d03034071729400c541000c0c00071170205192660000101d51048584540e5010607031403001c94501c12071099a050045464000041e0f00381c1c003440c1d00340340241c0c10591030300c2186a0305500c00f1950064000a0403907803940d84000500f00021003070210f941041d50030410450719400c1000340d8010700c081d5000c000781038480c41400e03102c81e0106c44011840c00c41a0105e50b0b418030035016110140120b018196503169581d12840c02428092aa20f028010700f40c0009642c415140d1b8002030546054408501350b503841d9030741c07180154 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 627415629 1250 627414379 627414383
    0xb060f04020d0e0f0c030303090607080901061d06010f0302030912070510090302030712080709030f0c080d0f12020a05040b031b07060b04051006020d1404081c08070507120507 77
    0xc0e007802201c01c2c00a450003080c01c1c20340f078440980098999003100c0b07420b00d0210724406010b40e00810610850b2840003d00917030010740c502d8200c160340c0b1501141405802c00358800b082a40440030582d4802d251084141c1c0601800d8a40c41c1d04002c030600300b50260302040b80c201c17880f81c02c80d40c0c00f52046103500300281641440750003a61103a00ca560011022140d0040d02540181d05c00300e11207040028802d001940b400d070f14141407c66141601300109181210f00004054480b0801583d04010401d405a00940b80b62010381e22200c09140b401805040c5c0a85440c0000701354102542c484403e502c2222424070709a50b500c0c3c90307e4142035400f40700390300c040c009689000158026002c008416405818150f101d200041001801c2008100c03e8030f4000d0418107510b0103804080209540016952082c4c690038100221961105041c44507540201c0c1d100520b58010000c0010340702040d050040100c4000c2d80b502c0d1419100c21004071079034042c1c43e20042003400844d0003810b545001d1405045014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 627416879 1250 627415629 627415631
    0x414030a020a080106030b0c040b0f07050a0b01030503030a11041518031a06090105040b0102101503171902070312050706061d010f08010b0612060114040f0e0606070b060f04 76
    0x14403aa0100781103903680d42c0242007a954990081c020810081a850740002c881c2e215182401c1c20411055810720038500c06000312000001d1160800800348181b0414542040f1000819039490404a440e58821902100070700d01c0e00283c021000064020f8034281c40310340c201ca1410110703000041e2034156040c41901d9003000e90f044d0000028825114000384070100390011641030501c1c03403d04c00d41c0b40040c2c02c87c07441a418840e5031907459030b000400111004040802040c0c3e40c044e24201c08013042d441d04041c1400500721000d50061500100030515a1401e100c4d903400c9480d00481223031590081e0100078445038545010112040c072400240441078083d07403002402071341d545e0f0301000b8120204014480380c3c102000400046440e0b60705000203103110f400a10811070030a000841d2440389a90146603c00980301140c4079900c07c24804d01c41c1484202c0c8955204c1e100c85080507801c0321072003104030a0f0960f00c00284542010390a492815a010089140a84071074042214290305201c40e65040b03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 627418129 1250 627416879 627416893
    0x31103011401060c050d050901020c0409110d030302071a0c04060309030302090418031116051507020319140c01050406032f1c06030804030b0a1b110d0212041403 71
    0x3040551400c078000c3c80a0307100c1e0108140756141c001d08169002c818142800310502c03500380b440c0d030081401d20700704d1011180004c00c55403078601003402c0c0710340303100d0690801d0042041c00101a0903500610405003d07103105168600c501504465445045401c034484402c1840708101c0315000c0d4000c408182d1090030090b04010041e404070b81142d004118042c1d004240031840c50515400800200c1d0380c40012001c0c0c0a050103014030071080d104c0a10606010343c0f01400e04c28641c2c071440080d510942c2e4020261081024880c6070300f881d1400d0254282c031070340f807030f88071003150031400144001c0c0c242010b0b1281c40c1007074940b0700250028000b10614085402c030405070f1408180704e0640c1031034042405071442d6100c000c108031071103103000c1e503420014000303280503014404240d00e030082d2401c0300d50041c43c1030141d036036859060001d044502183d0b030740d0b080440596031074a5041806915000600300c1203862501c50010220b9850241422031950184100024029817004580d1810080c401400716480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 627419379 1250 627418129 627418151
    0x607020d0801080703030e1012090f1a0f0705090301060518090d0503070e0f0102011b090602010f0504050c0909120414041a01081614040306050702061e07180803030a05180106030c03110301 83
    0x2a22b00d1303d00101c48a8544041d01c50030011080d100e800d0a1800f4400c1c0040b5240c071100d81095540003500c1003003484804140c280c4196002d4001c00c020b000040c00c12011400150560b0380420700a40e6544020700800d40d02055261184060782d21841c074507038462072800403e06c01d220020303500c5600a41103540794102c130308024a12078020145103c2658072088030714907104000742100c1c000300071a50384904000610010078000960052080d80c101c5110366262181c4075814034101c004d00340c0611790302c0d0228001540451412508600e1a415201486100280042009402000c0c01a1400b04500401050400241c0c1300010b0b91451581805099003c0300d40c0c0a045c5500603510407281e1b07540340c604001c05590306104468008108a041d407007074015840708072541007802002401046081c3e4250070f007141c0e07134402075402001c01d6404d995880c14540b040d14050802150080020b640051000d130020805200d0304049030380003220b01e60f04031b0031a41e441081400130500c25506640340d0802e005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 627420629 1250 627419379 627419381
    0x1c020705030703020c0102070501030b03100f1e0b03010b04050106081311040e031e03070c110f0d03050d0b0a0503030405040203150a0f031208160f02010603050607020d0801080703030e1012 83
    0x90b400b806038004160010344080020f20341103040d000141013604240d2202000e4400061800785d0034503603140820b003101c180d64100005c0c1945894a0360000400501000b102c0203580b1181813810244c0090081020310410703c41969800c1c450f02001402000001d2090005080400703800c07031103108030325400c030720300310020302521904010724180b81c100064411710514140f110000c40550b00d40110b00b186000c1d98060800e6480b504003403c01702e5400b000701c1c2a42e07620801d44441a42c014507095902c1c0f07050400501079080081907541c000c1c03a000c1c0800302c81c03a060103940708035071004004518007802c0c041804080d40001d031a0140340c6908201000140daa40c6160b40090700e00b068408180520318281514840034170307031104c0140402c0d80240305808200c1658030346800c200c0e00b04807150580d04503089004060320790024220b801404148100c2d564040b4642c0352440403030b5114400340e41c9884032aa101c42c2d0310b110040204164200641060400960700641d0300c1e40c1c5e040481260f034031030300414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 627421879 1250 627420629 627420637
    0x30207110306010605130f0533070c090507110d030b1c0501021e27060903010e062e121e05070312020303070e12010f1a041805031c02070503 62
    0x1005c90350105400d0910b010384d500300001813aa0f1186030781c1f0145424046455406011240710160806c8021034502200102c1c00a08103080307003a48990b00c86540c02c1c07000c0300750414022580001c0c140300200d03440e24492004050f101003440080d10701c900d0400c1083d402003039075054098000c0381c0c95603921040c41c03038825036080e018000d038000b5070f8a0081254440c0054100075405000b890140445100900700e6904807901584c15036010138040d045e0000507083d809200c01c125419801c1c1b410810104002140850044200045000c140a000c000740303500b25001189840c0800b0b13020408000003007110100b84407103401264400d802c841402c105007290481000c0c182c4541c0d000a13000c00421042a1320500114224400b460450400ca2030060011810504c9240f050043d1420304034000300a5224029038000d5420402482c85030103210f810364280c110703000d44202d2410707009400714151011604610742d1b0001c051880c000515400c02c2a8036101034641d401180d09224110000d50204014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 627423129 1250 627421879 627421889
    0xc02070e040c030c060f080c1606020c070303030c09062102070813080c01110d0309240501030c050a0b0409090f0210020c24040317091009080f010c080703020711030601 74
    0x9200040c1c00d40c14415507103001175200d0420803180c1d94041c0c0c0043d500419103070704101070000c070030b03074130310541c068852601e040c61005864688001511450414009500821a442610140b1803101e180e841602c00c08824441d90307012508018075060100301d174040025071006c40b80401410003600b602e8240c2d031500306007040c2445800741042031188290800112860520900c1c1940000303003454000c0751100400100300040c19100c6042d0710400c41d0010b0715800c1078511a035208840c2055a407a04080d08081c48160340004400308085400d00b000034000b0103070b50300729035140d1429182c5a110001081004006d44030048140c007060f006a03a510042058414294020122001b14104101d8083c1c1e80c0410403051030308540102c0c1c08900c40704117940860b60000351502002c0c00004100ca410f02c18095a41c0c1c5c80320381d0641c503107452900440707050161801c40c000c031000d0f071b075580c21074900303c1e19035011b00808a503020300012a094400c4d0000e0281d10301c201b050800540c3c804010a00d8014203800c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 627424379 1250 627423129 627423143
    0xe07051e041d1b03010603080a2105091b090c030103031b08031e06010f0210021c05041217060108010b0702010314071d03071a0f070b0109050709051807030c02070e04 73
    0x40680f07030811a0b145807081650440c0201312036413855981c00b01920480c1040018841c0100d05030b002404941e07103c5807070b998417500078820340c50070442c051f440328030f0700c0c08260b034100700641000005e060013501c50b8480d4403807540c8545540d0950310103032503000c4400303442a600c0e40b000c40301000003403120740030f1401007500c803885945802c01c0151401c0341c501c00601c5203041028144552003078a0b40040c10741b03c2e010601600507039a03079019541d240005000c031fa00a441608240a000402202c05603444941300c1ea680c43c02100320046481c0030aa200640d407107400521840014444000303608d00030b1403140d205040001701c00301d8889a825046d94111012008030316001e0180d240f03501c806149400b0400220090801e05050108a84100b46502445083c0d98004070b040344001d40c2e5481110241c50700b03e41404000d6030f40300c51640c0503100c100c2e1103070001b42c244030002030036081c031000712540e04080302058041a40c80c000c040b8010515404403108505c90380d000000e810303544110b507900940c0a020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 627425629 1250 627424379 627424393
    0x8130608071110180204140f06011d010806010509032b09030309090504060e0708031806160303240308030609010608190e15010e04060e07051e041d 65
    0x644298801403144080c80b000141c4442916000310f00c07451020700407140040d02001071a001902010703446002500240342000f09000c5880e04400203100f2401408885c5007555200b00442d2003010309110140035408120b8241c54a41c011040540e000206140003424240f101c4002443c0010700303004e0083c0c201092010780b81d24407061b240c0b9a80220b45040c10005589541c2c0c00030912885441039071041a528004142003003019000b20004075445c408403251161034460346d544175401000f00c800f503814400e40c1c051480c1010720a840e00c41e070b140041c150b03811105131019001740c0f82056074603203c04404142e408101c250405007001860043d4409902c0c0c0c9454018401443e0381a001b81d018000b07030000300203c90481d81c030301000502104c400424010180c402c1d40b0316205100e900004803003120340001c103507688007400c541d20460103100d0074016803090805080d02d0b00345c0e900032990042404681c1e020000c010b09064031120344050000100c20900021818917020348814082030758011078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 627426879 1250 627425629 627425639
    0x10050604271a0903041a0c0a080a08130209071b02130c03050603011b0f170c03090c0405070e1e060f0a0225090f0209030a030201061502061e060a030813 67
    0x1140800800a5a80c0908094100210125624085d80c03146004144041049460000440742503e0080c3c9007001140e80400c03252030f1400198100c0c3d4407940002e88030000045481c82c1540070152003540142c11105c29484820084071507000000071001358640d40105c550068940100920000d400c80c040003c8000000780018140c950242420b40b20340c2c1051104801c8c8160301910107410040c604150104515001080d24040a403000e04180001c816007040b0744c41c03100400451141a205044d200245400d404100c00c4801c00d0300c05000240c408103100318a402d103c84000c0f8609119042c104504d0064000100142d1040740c808c2103c1e030021079a50321880d010480044041c1403030005c000c82c400d030700c42c03510310303111441c441c207a0800d4540001405080e034581c111140c80074094151003490419040c0a80640200e00c580b80e811603d409148042c2480403c08500582224030200d03016065030040f01c80040024002e190b0091082e00d00000107081c0c10001d09800c1c41001002400034030340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 627428129 1250 627426879 627426893
    0x2d0f0501020d0f061a0c190c1a13090203090304081006031109010b03041101090503010e07030b0c090604180b03030307120f0b1807200a0b0601050a021005060427 71
    0x10f01c1040703905400c0c54810b00c50b4411240c042c00300d80101c0014151100c800702511440c240f43d2a100c02e804081c40a60703034092103540d41d6034200b40c50a01c11100c04901c0958040c030b03040d22405442400040b000728080c00000f14580080d900151580112030600e41c99503440e50401500410800125584035010002c20540035040300e40c03181c0855050000f58036000b03020000e0701c0001c00040021540300003800840c1c0c040c0a880c0c0241c0b2016000300600e0440480c00c90740c9508900054845820000010303261001d04011101501005004541880d180ca1088400c0c104100030300c02c8155107850440103a80c40030005984070744800e6681d183c2d134500310a640401c86074040714080c00d8a0402002e02c403582c07103500c20b9540e031128000c4001c3d82c0742d44000040f81c801c03c8916070f0440004150400b64030000002400d031040383d001b404203180c2901c984005484d0352254499090258004542410340c044455205035440390380034001040200813401c46004000c8030211510829071f000703911344144000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 627429379 1250 627428129 627428141
    0x9040507020111070b2809030210200c280c0b04060e0d061401090207020901170a0b0403030b13020a0e030a08040b0901020717010b10020a2d0f0501020d 67
    0x80d000810009180010740691480380c250054141010b1502250240c8403100c1b0803c004510120000300c0217200d503894801030007021005a006210b949400303034107807c0c18414025207605144042c1c1d03510300714031840d0a13181c221000c5001240a40d0458154050340351810000d90b40c444048205200005c0c607201002001c0c80d0490004198207000500040e078210944480f00003084030700310800501803901a0180100619141004510100000d090040b5030040c2100313501c2291090403a07030300c0e9080340c00c3c40000c881d45008158030036450f000c040303000340e0861604503009103404103a01c0707030b0030340401d1017504a1090352041030703400900d14417000c8d402181c142410404401230000d844940e16480c100e4040c42c001e00342002000194081c890b03000704014002000b0f01220341d040900e08900e928020591108118007500220b1038900019102251a940c0c140d40101d1b0b44544842c480115500703c415420340c80720741920780341001c011483c0b528000702014400d00c00503940c0e0661240400541d40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 627430629 1250 627429379 627429391
    0x403140d05071e02040f060b030a0605060c0709020304140f06040b01091806020903150a02090406080609121b1501081006061707050405090c03100b0702100c0203031b03090405 77
    0x64148a440b000a4081c42020085070589820014900032400090001e241d21708001003000c1c5402c60006420000c0070146110b122100c00c1081035a1f51603040c407801d4400c0702405c600e203030409001806803101d9503002d140c21034080d01d02c02c00b81c082d1218803103203055104d03000c1c203002c1c0d4024000c0004100309080d52a0152500f0303407003800b50504a403c801c0e55070030b0303001c8000d04d0540c0100e1880340f1910304110741076809035052070040c0301e8200f40802000175403103445058000c0d41018400310f1500000900c69001d02e800000800052000f02d6454142d030700500407039041350045040700503a0200030095400480304008c0001d10315403401d68114a0b101e20004044400e6091941c20040700f038111001101d8050111001e5000e60b0b105201101ea0b4441e603080113038000c403200c00784075400080038040c501c5001c800174551744058444494203210301a00e500254491480248290b445220360040113050340b01030100d030300f0100c0f085000e498240c0c000d18491101d90000c501c00d64186094040d240d0000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 627431879 1250 627430629 627430637
    0x100503190905150c0c010606030e010c080702031b0102040306061d240103151a0403051006120807140d180f08070312022d061032060403140d 62
    0x1440d542c03825103074588081d80750740f80c1c0034080000303030060302d030404403103845904000030000140c45603006001041101481e40c0b40f0362070409030034203c5010341c0115002c0c10480e001142003100e0b5886548650b0b020711040c0c400b95400707000c000005a041c3c060480900100d1195914040c0541e0040d074484200402d0551a44640d40d2049070300000c100041161800078039000c01d660740c0019415100400d1a07101c03203c12403011034081b000d9000300d4040c00641e88198117031100e01294030058819030302540119004600c08580c040001200301d8014184c00703103e03918500481180e101e0341c60074084407a0131000410030710651000c1d240301c01003070751000c1c1240f10440180f041c10444590703910403260000a0654500d00034414219000f0400c12004100541540604200240c00d641d039981070310710101668072030400401d0b420b0100d10f20f00802c0d1f90580003608140e8100284c018102000301d1400740e180d12195080e1032aa4507050010070103940156501c0c0303000d00104844602e0103600c54400c500700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 627433129 1250 627431879 627431891
    0x80f0609010b030711031e0c060702030405010f0c030c0b190b090906040210091526061e131404110d050a030c080d15080f031315030b10050319 63
    0x8509034094a8010b451441d0000f103032030030815640e03e1803045074202c50301d4181e01100030304103444940003401c0308000941502d8840e103c00005078cd0702c1c05280965400b003404000c5007101240700d014400b0b04c00e80a4507110100361034580358041c150100796910030100e1400c2c40c00988500c81b900498004450a5444414601d0510034040d101d92001d04020b2103a4120302c04815801d104079014400341c10710941c1c0d46103141c90f01c0c5020345980300d40782c14914035403020000d800c0c1c00c046414070780b4400d51004e00340060100380d0340400903001c9400c0e280a548402c410781d24081c4803040d07100e075680240078108504000e007000c1c1070030311810110340213403449586901000300000c0c101080d80c0a00950500740300700b1940d8145030070f6185014003200c103e81d6901c0d2001d1002e4484101d43c000c0111802e4805413000100120801c68582c8034102040f640f001048404105503466900710b1780c0b0780e207450300e8002140f1103814005080c0c85903090310b0100152003c41072000c45414100e400401c0c0702480310030850 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 627434379 1250 627433129 627433139
    0x20307031407050703051207051b033013080c2b152a05190806030a0206120708060402090f1c05240604091e0804080d080f060901 57
    0x103003200d2007103100c034003020200d000010400200700f00030140d0b41c80f0301503031820000a1072032407007034108201c00e0b81d0b10710131400165011040000c401440150282c0500020003c0c503c080c0901d080320403111b05a080d5140151030340003503a0b4061b0001021805441c2e0546140c0710350b01d454180d03100751103840bc032140912003148484c5030180700c0c10305050314403d0304402c80c18200030b00941c910a880601040c101031201c400c802c51a0000107040e60a00511142103034618822115405142003110740700c183c840404c09058000c25001d94052402012240c4c0c52009a010030361a40201c0e06401003001840d080c45020b64000d121150303c030405035411420b04000078001000c1c0100300d80b41e06d00407070b100803c56208415822448080c40c1d0031404841c0c1610529000c0b001c0114a681c81c0700950244101086462030a40500e600c4180c01c221900b410000900800d060b00543c98001ca13080c01c000c06c000580c0800a200d680030448941e12024140c3c54200c64940b61041e00424292046050f0001445 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 627435629 1250 627434379 627434387
    0x3150509040f0501091205041706070509010302090d1b180c05041205010f05151017070819050127140a2007050c1813080306061908060103060602030703 67
    0xd4000e0b0402e03841007080d401c5041070b0340102654840501100c00802c0d01a00043e0800c000300b04482c98001c4001c690100c40389840d0f01e0b0783c0c040c2d511400040e0b00300540d0450750303c03c1d0003904070010004c200c680f0a100315900e417030241001e10b95821807524041c00401081b40035400484a12603c1c441c24040a002040005d010b40300700c1c00f92007000c0c0c0c25221f048081c81804d50101d24041c6c105a810003460906c003543d0a03d0a40741c2c42003620481c4044940800e16114840e9a601c21141c095400c3e0309403501c0109840480c80244141c0f41c5a0448002c0f192164031030145074000c2100d81e020150282c080302d08001c003025403c40c0308500340d04000800595007078a40030907a001c60010b44c00107040408a103540c03080310f20403078048100710001c2010824000c02251810804004440703600940c0000d64207096541003c60b410001c08480040348404560150002c1d81d1180004080700c5c038100452440d4045042400351260006030303003504200082d44c15203d130304054040741c0001c6017000740303980d0010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 627436879 1250 627435629 627435631
    0x1e0c031d060420091e0c1e03150d08070b060603090604030f110706030b0418120c02041b0c0309063b0904050a1e1106180a12020103150509 61
    0x101001010780710303c1031003031496907800c8103000000c003030b01424103203d1000b2208041c00b524820f052481c45001c500420200c404032250203245040b0030b014242101884c6245800003840201164990360362008a60350b40c0582c3c171080c41c85041043c1c0c0351055800c003c090b0700002482903000355030400606c0305050000031307207c0e40b00383d05240c0158400d01580040320a9000420b11601d00c1c810aa4041110303034154004440b0104191001c10400c0040f403031002c1020307841c440240c001210360060303803e00c42c400c02e0882c510760b0000e000450054a82601d141340e42d00070502090000d074203032610f6020164480074244c001c0c2454904104640980901031030007081e25150700300005071109441e01c0c212584140640701c807e0040c17140c803407071419051158499505002c2281d141c03010350502501c0310a000c62001040c0c0d0022002c00074110322005000d09580305500081c0c0070b40354074001e82c0a030b80c0ca80c1170ba030f00a01880007410322000c1051001409035102c4640322000400444814000ba4803221860b03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 627438129 1250 627436879 627436883
    0x9020304031e020c06040821090607150603021347120f0d0f030204030c050603180106081e0601031101050306060c060a060f06081006050d1e0c031d0604 67
    0xb40502e66664081c0c2c80d00100513100340c0c01c035502250016019001044400c20148040c0c58101019580d0400c80d02900c500c0d9500f55000b0002c0c0012000b10340510270105100092600004845880b07400103034012404038858208144c445a21802078030821080b0b5014085000d401c480e0301035440f400c8003901d0b07070060108490b40000c40c103241c0386566400407035404406105c2560081000e0808954a8128118034200400c0e1014050385206100c1e00c01c131400c41e504905424141820003013080f00c0c0c0d5101038400c0050410258034a81c0d001c401303110341c1c00109592001041c3c41c1c0c10410201300719020030482110542c020500400c046914050100c0301c00500f40703070540d5695101c400240b101d000e040d004014511510041001130740099112600365408284802501d541d0341c44100c540f480d003110907144610310303860704000441c010800741000c02c0607580c0109244a21005a1103034040b455500d0014548070074014600035010310902044102112481c05158021980b0943e100005000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 627439379 1250 627438129 627438167
    0x30d0b0f0f0405070c081309060815010306051003080a0c06112508070506093d09060222091b08160201090f0317070e01020d0507080d020307180902030403 68
    0x80e484c0d4455050b04201130741c020f4015842d005406004405090b55000700070000d45040404500c00c1000a0840140c0001440c4500c003a03086d6611a030141c5409040034054404500001c400580490054065161560740d40070300c0c4826030809106035901c248903039060f010100140e91015a544884c040f850035500b0000400200c20700d08401c01d407150180c0540580500810f11401103000b0400b540040c483c2d004056107524688414090412080d02440c00100c11090401c1ca1640d6508941c2403240591030040c14105100d007414102c6006c41c3c41202c1d0015a0501170200b0881031260080601740340c04111549015080c001d03008120181c04429035204140b01500214401d403c000412540315010b0100001076160180c480b01c0300204a112003140380e40050203082c4036208803051440140e00821042854800c1503800b0f60143e0416141000304118819007450640019401a0100c6da103404140c51041a80c541c0e41a41d03401c0301012900400034040400d600180d800080001c0000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 627440629 1250 627439379 627439381
    0x30105010504061b08030c0a02010b0303090d0f0c0314030d0e0c030606010804080f0f1c200a03020705030315130e03070222060e070201140603030d05100b0c030d0b0f0f0405 76
    0x10310244c04440d0120010a0400b000040244400700007028043e101150b030001d000d05a003100c05c02d620b0340500300c20150059000341201c004100009a01c00075203001d6151804125200d4886001c01102c040d10320005d6440001e051601c0c1c8801c4c0304149030204c04101a1407a0390031b1000198071180b0240280f410058814081030602224a0840d030720800300408960303455402d550750500c01d070061075400343c214441c4512000c200b4124001c21000405c145120441e65940304041003141e04610708440c101a400e210200c00244100021030241003d503480780b01c0302141c50200700c00b003449008600507217410300c1c2030b1501c802000025a240f070342e41100c0d004403400640e14407580326084408880f48007410036800080c44007000300c3c20b501a01241d402406200411550644909030640d85d09070541d10030002020301c07000d2540095000744030030f2848940290780c1c04d603548840c0c010840580e119080041d016403510954815294841ca040c0c9554402c3c090030400035814042c42e202940c02251a50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 627441879 1250 627440629 627440657
    0x20c010e240d09030c021c0f120210050f06120706080c0306040e1903030e0c0d1e1209061706060a2316022106040f110603090d1403010501050406 64
    0x70040d00d106210680c0100005011403c0050406012078010703401909102c4d02c040c000d01420811001d043d40007040b41c2e4481e80c00c2d035583d603041100e5500682c1180a104030300d00c0310200900845009106452072030495082c05820000350a05000f40c00c0c91541c000c1004000ca250049145644651300b01d500c0d80d200e03503a26011a01800904100c20854011003401d254194104002848164080c1e035042142c4c030410320b00613655a0040c4603d540c00420f10801d00001001c4040b1500c582071342c42524401d9102035030341c41042c0602406c001002ca0840c1d0700a1101661060004540e0b2050340510221802c0a0002c901188901c80c1c6000411586080f1503c80b00d078802d010003c1643c4001429966454101d4206000e400fa88000c038400c80640b404582c0c01c0d00309440c07100d000c02c3c04001500083e162951000800800c0d80011114200c09208036845591100040c0d4840c100160180a012104410046c541009901c840180e0341040c030051010fa42d0150940702911080d0400b00c1810a84e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 627443129 1250 627441879 627441949
    0x709030605221a061c06050402041103071d100804080306150d0f112109070f09051905010806011205100e030912010216060c120f020a020c010e 63
    0x114109410001c075403845041050500300c68050a1400f4240003a5440d440c0800c20800e00c00300503860690b403a1011034010945070303030111381c000348018800148141070100544040d00708484c4c1c140403410724840b11440261410102c0702d00c01c0c048a84070900d51040101422840b80075201418020340400020060b460b03d483d07440700041c600205035107542d01e01c069032000e4484040107038003241c20500000e071018010400d6901c100c4214410500714405c1044072016424018003041e41d80c4503442000500040080340400a82030842010880b45803007030b0301c0b022144498070200d40c01450714004001c00c0d0b00108806041d20402c170941c0d03281240b80c0c2030040c940014000800c0e0b01603d08012008a010004000c02c1180d0003550206c2c2240f01d8480b40c0c908070f02481248285030340d0104c0700100001e00d2540b240700142d880d41412080e512842234050304031f501400174259040e60016466a14640401c01440a24824038250601899540c0440d070070709102511b0414881410044040d00300d10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 627444379 1250 627443129 627443161
    0x504031203020f3601090e280509010c03110a0c110301090b0906061203030114040c09030b040c0e090106051305061203070f06110a050702010804030e0d0f050d080709030605 76
    0x2400b0030602c414140d40d884c2444001400c0c00d0200103443e1504a101d495024404e00401c031600c3c0a8240340d16544c40141e4071601c10711450364060744200d0082c142e807078078092182c2d07409124400300014413201d0500f00a000c0710020048001c2c100b10501162487c0e036030141300d0b405200c1d480304c0c41e42c0c3e071840c54002081c09840000001041001e80d801002460000042c0940c801c0d00c040311080c01d0054542012516444203024050306802c400314000e003541080e8005000c030100b140380801c442c554a0300d40b41081e00c015181142c43c0a0415000c02c95031103142d03103050b0002170800c000c01002d40381c00000362081c6005400580c00d1903c5100003001a07503804e0704100240104401d13241e4641e114941108041600d5404030740d010320f071501488007000d03150159803002032151501d030b151021700d40041da0740440c0100120b0030080011982d4881d030320f41c041030248051044070850840743c01c5242250605040c10001410090101d017088009940601d5803030840303070415230000f1139848520781a090581 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 627445629 1250 627444379 627444397
    0x30f110c01021911060c0a05120c0d0b0103020910140c010501080f060106170123100203070308060303070c12290a0c0216060302130f0b03040c060504031203020f 71
    0x24012880c85201001900104422a07900128403020300f59088180c640d92814002c219007980705400041c0c8240390200108420b140c0c6047ca14141000301184110071a000c50350b9401440010860080c0e00007540070340842990242015400d044841e4003041e28801207864520070003080c89680d45201c0341c42e9044070b014640281c004c1c0070f0756840c0d82100741c1d50040d070150807525115160001680750701c102440b901907510301000c40c84070307480c145004102c0010640c0004a082c50f0600745011a65001c2140b20420840d40155454009508025140700c00007000117009800412000000070030002010007529103400383c24110070420701303082d04240c24103d203401c000010701c6020000e45aa44944500c00d2800710414480243c0d80c903070032030310f03424407007804903c00e0521b08040c080107000f5005415040c9403101807200d4280e994089420014996000381c9290000005010500007029500c40107400c0f103042c080d1400d861941d441c440243d0001201c810035902080901c010041e4500b00d070b000346 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 627446879 1250 627445629 627445661
    0xd060609050408070c0e060618030f011b030c02030c0c0402070302100603030804110d1208061519090e010b191704060b030c10050d0b1903050f060a110901030f 70
    0x3142c240303405441540200d000f550406035a0070300251500004e181a0700c41e20019103406e0410890101c00c2111402c000b1100e6031500a41c40601402c610900c94040d031001c820b03510340c40c00e0011071000780031070750142204001c40d0800c22000032004000a18110320b0030060f50300681c0c0c2c0e46542000c0381041140301080a131642010000001c0c0766200e003840d0300a6002c0c45081000d00320003410080d10f4848404c00425070301058500c41c1409000d90010341d4441c0d40135080880140f81403031010800d90101c0b1800b1844941304003100900c40d441100d01c009410b8002800096504285860b00d6500070010401782da50300d0144210400c130b04c00c17020803030411500c1c034680a043c10300b031429078083d020f81060140288190600d4101c240b401e040a05110030705512a0f51804001d20719400141440c44c030700d1608044400c404200710404454890000e50051020b01401040b04c001c06040c0740f0083c0c03048200e40d092a41c01c8904c000450201ea04501c800d0030005651400749201002030700c01003c803c0104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 627448129 1250 627446879 627446881
    0x11090408130e0403021006060f120e0304080102030f010503060103051e030f0a11010e0607050702130e0d08090f06040c140406030602130f050a08031603140d060815090303060d06060905 81
    0x6654582d2903502a40c801e401361800326481e8401942103034010b01c140c3c0002080f0b80362081490b4003a0a9040c03280780004030210754810f421200c545503034010341c01000a41e40c00810001405500c00700180540401c5020308421751640d201d10342c1d64014000124000c0450042c40074900c9800c004a4101800314140d4684591249102402c0d01c00f8070a00d0522075420001542da00010100c0c49502c11055901e07001e00305200ca07000e10035002d18912170314003170590300c002450390404200002417070b80145945040151600785441402e00302e0750402088c0c903038440c3c0300b4400042c03a50916075044d07803a00341203d4441e03416240003c1c05086158005014a8400980c0f0500800d00d00ea03410259030b8040d583c01c403102d650724141f082410312131044d02c0c0709400600c42800250905076003a20042d0103890414108680b4000c04803190b40034400103241d240d524581044000c000b8404400361016004d0780b0700c01840d0681c503860f100d03c401050940f007100000000420400b0b56130100c0043c01c2080820042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 627449379 1250 627448129 627448139
    0x1204050909161403100b0a06031d120403140718180209040c1409040507060f020307061416081e070c080d02030624040e0a0f020c0a110301091109040813 67
    0x2a60f04140860b90007400761400078080b072030060140d882010740140091202030300c2c0c80d001314000d1408100111010b00320940c10041c54104226055031202030480460f039403481c6144c40707081030426113044d0003544c00c440010441014200b01d001214000c1360750209001c1440f41100b0035121205030025441815482408140801c00804400f521601c0c031613051100c120b1400c20840d04003c85e03001308194011030090181c3e078843c0d10740c3d007000151401100c0c146910759440c10103617812031103081e4050244204010440306103004c02d05040c1940e0406210606214555000c03100381d030010005900c0d01da00104032028454444005140d030081d404588508004041c00c0181d80156141481803500c1c0082d68030f100c040c045a140e00f0806841000e160078602000000c111000078001603071a47e80e0340c280780c0001114002081803061100180c101e00103e40341201e0010040f00040c0d0290385800030060010f503201444170801c0104840741d07207070f41c2e0301c51400036031610800019a82c2c0c0249500c0001b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 627450629 1250 627449379 627449399
    0x250b031b070b0702073303060b0d14010e061f02030c010c03150506090d11130c030e1b100309060209030a1a0901050f01060315030204051e09120405090916 68
    0xf0045420340d0030354543c070741e0712802084402c4900c454000d089603568040c010761070500008402c00341d0317030b400c0109034180d840310461417603000740b285140807a40780c06c504d02e04243d42603400303409041c0031f0b00401c48909140c1d0100304400c5081c2c0c400c843d070200b00440018414001c0041d142c1d0204104001e010940307001c5001000352445001c4902c2e15208100e001c542c9241840545601140180c560701341480103850b80740108010041c2c451304802c0c41c4566a900107180d018520a20000780c80c00b08004204501d0300d864001d101100c0103c0e00d4508400213010780d00c0c840c41c0100407020f0328000c51a01d0640c2450303002440340186c69540b51007240502003c000d824402c441503040070a01c1652603a60302140b29003a03c20848040d2402c0c00d4907001441190b01981c04804a03034860b00c884102151641d0101e000c541041e1891100c0c84030140c1542d0b4680f10904a0603801045000070b000703c1099941c0c07102650084d4001d00e071003241c0d01c0c400601d00100c2040100d80720300015040d20031840d95210140307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 627451879 1250 627450629 627450631
    0x705160c050312041d0c0a051b1501060e091b070204021c1407020d090306090819020129090a1e14040201080a0e0601030323031503250b031b070b 64
    0x2440e0320a04a20007507517941482a10342c440c01003282803500d003060b1104101c03030b550f00249021030304101d08402c440e03e5517000c111a03844100544040700e250b505000c0301500c510f0561001c0f5220303007462820404c0242d0301603208920b505100c6041a05c07402544001000b0307010b0b02c0c0c55480e4070b00b0245034041c1404615000982114100c1000207003d49900104a0b02c03002d481100134085040c01c90100006801c03076010118007400b4240650420309104035044205140079840030041c1e4444a2850385494240f0401c140c14001c921440c480e000160701156860034000c00d1945100d5840b40003c0030703003014255410068a103083c0801240b4460341c03606040e9501981c00f0b0740021030100000340039080900c1010f200c04501c1c0003e2041703030f00e503a8080baa41d060030060f50b41801e09021003600e0000c0d102c0b000e14000c02ca6640c20300344100206050502d4035696071395891542004804540781122584815030564984000301c907900d03074444080c1143c00310040e2000740c001200050420a1010b525025 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 627453129 1250 627451879 627451889
    0x130803220602180603101a0d0c0309021005040503281205251104050c090316050310050c04090b0f0a09050a152714090f0d03050705160c05031204 64
    0xb12000942c43d00b80025400102c1c4c1e03003210948004424001550960b44546081e078901160500d840c0d901c50188090b0340e89090410007003070b21f40d120a4118a8140340c010b0785017040d80351950915107001d0029035586044654595018288015505241d11070682c0419907038104c0ea05035500201001d00400a510268020010a001c29048000721020078001000035400451400744000144c00f0000103020141010340054030803c0203c45a440038800d0a81008061401642d154646401e142c00c2032440410614580d04c0d100800602580b070009590030740b61075a000241c0365075020041030100b038444c0405d603405420554002010360441d041544908082c41c014411a441c42030340485000c0c1c240070700900070000d041012040d045412482900c4000f481000c41d108800c602100072000d004e0300c40001940200c0042040f4500822150415080500c0c0c01c1050b450600710082c12401080c038100c5581503100001005d2000c40551000642030007001da83c00040c0c50355941145a0041c450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 627454379 1250 627453129 627453157
    0xa080d060510200a0b09210c2a06070c06120c0f05091801080616090608160302070b0c03060102250603110403060906091a130803220602 60
    0x124080c00d0030103640a2010250b00c40d0340700d508031025488034103590580741c42010f200c0c541441c404180c1745880140180d00103009014100000c02e405030000c45401d80c000c0880c10108a010482180002c06c40d07424a40d8140842010810030b04503034580b4421241aa823141000c0307143c034144552420510700301c0d1241e8071070400d01e0b500103607480151903120518801003888103d203503900038047c03c02800f0300c4100500450340840031b14680c1207030400a81101e40300b6806141000f41c41c915003403805840c03040300d082680c0300f50310340040145801001001c281d82c0c8544400540425030084e0140c91080d0341c484184c00d043c1c0b401d80c500c00780d540c0049580d0b038014071403c0680d54840a66040000c3c04400076800006010b047c450107070060842c00c600420418420000040441c90034410028000d1103114089032883d807904055052440003030240c0d2040c01c1840501500d4000012404015a400302c4417544030b685207024900e81040c140e000c042810200d5480300c1c10021139a009180310552415 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 627455629 1250 627454379 627454391
    0x9010207081524280b070c060f140307140702280f06050d0e07030f0b010626070f050c01060605070b2809060209040f02090f060316051b0a080d 63
    0x2000c0f05850b031900b4501c0750020350001c0c0f50076100155000600000c081c1010f61200c2540d00c07080544141d015280942d014400d9103400e026803580080c030348900c20301c5894103841c1a903240700d05048922003c1d02082c00c0c0324036040c4114406800c00145c4124a800a000e000340365401011260180b0344d00e401c45c2405e1a08860110342c580c0c05601c080c00784c684643e41e542c2040480510030b401820041414040d0f482401c8000001540c40f0440f01d4900f031240000880651500740080c101030b10302c101c840346001c40c0000c0b9042d40a0080c8400f40c1c4490303d0300d04131414101205042d40c0784d22961000c4c0d041d0354200310340070402607045030041002c6449030074450180c1c0d07100c000d00e104182c070344921801100301c00d140e1300c000004103400500c0c28600914006151000d01d01c000b40c1142c0580100d0111150017107041011858000408008100e054404918500d851141c855100c1c440f89600c109004000c02c1040b00c04400b821001c001003214000c580c2da03903409040036016500080013000309242810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 627456879 1250 627455629 627455671
    0xf050105030619052e06030b04090206310b07110604030c03120504091d0c030f030d0905100222090c0806091e280207080f090102070815 60
    0x499922440e0f40e14240c00c0442d440100c07040c003915010b02804070300c160001c181e080e1104030303000f50b90030801d0450b8814001403414902a040d030b2100c0703454621451508041401507150002251080300340904610314014038411a4212100710400441a01d00b6a10002c01c044d2003a000601c0d0780e60150a601115484075420003d1b217100328040103152840c242000c00c00507046154030840803404d4207146090036158011001244c05001105420001c1d043c1c9580107510140040401f0070b030190040c10390b1180c00b0b40d07443d50320310a40c00c0c41695243c0e5400c24806121040c4401129015180020341d40c865581c02601d01a440d070340182c1241c0c545e110750005041c0c01794030a814501440b0784481d08160345000411110384001010800600d05d15a0541c032400401c4070a1845124101c0c070710f40d05050f94171148411940c40500c1101e2061040000c140828103034400d8038401201d5803070241c0d454000701c004034141451540062124031910701000f501c401a184014411181c450390710036115446 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 627458129 1250 627456879 627456883
    0xe0a050a0302160f05030c01030c110a03030b150c120f0c24090d08070f030b18010e0a0b01020318030f0a0b0615120f06030f0321060607023304090f05010503 69
    0x6220301c0e54180d11240c1d4424140d40a5000f031f038a2080c80d41007044160f01041d00d058140f5332000c00843c0040d41d90045490b251410800c402d00b072000c075900140c10700d40769001b000c0d81c40c203003c5d00c2031000140100744d081442c002c010450700240c40b1344080d01c03c200b40c0b40c03200c810044840c0b0420386180c11003100040600c400051f03030f03a02007076003075462346c0558943e1300050703a19149400000c3e04154036200c0c602c01e81d81728003690360b2781d40640c7c1c00c0340c42140d03141c4004424107440c040d01c43d005080c144201c4802903a400015039407000380070b40400700d4804809000a140003d201701802e280e00814040205000c8240070507849202c06a44150740c2c02c40312642c80905105804010706e1412183e800708110010340511154000000350440721110f104001d03c0c0d107036030028007048100c810f0200414112890010302c45030081001e588071030600c810b540c00500a0040c514962100d01380c1c0081c400004143c0620740c24010545000c2c00395116201e201d1b98001d4600941050261800c2c2000080e0034100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 627459379 1250 627458129 627458159
    0x2106030b0907240e1912050c040501050d151b080103050115030c091806021803010b030109030e0919020414010305091b040902011101020f041707080304090e0a050a030216 75
    0x49000841c3c241a0700400c4d030b0003900034040070381c02502c9540d0314200c030a1407001440250880110b000c08040b107030302c0c202d450101050314a03801a400e11004201e152100410a2001c0d98011800c65070380c801541448000d001d01412104903400d031050403440e0300e40040d6414140c0b40241d00070300034403c0c1420300784440c49080c8001440d42100c5507040000e0415070380281e440312200001ca0001c991661100404c4c1d80114001aa011002d0682c00c0740fa441e0912450418410550003400190941d441c05801880c1c44c5044600860700c0800162071072692006c003600780c010009045480d60784500304614003034240958a07012900c0d003000700300e030320000080c104025600707084090080030704541444090900400101c1c148040001c2e4061021406c3c005449040c030070032070080d103940c503208003c8007014580300210010f821003501400700c2e000c080211403d0301c0c40c0d290701064282404d407180d45426020741020b0311902910002d90304240c1d000c1140040c0031818100700711381c1900c0b0351000c60b0b2000c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 627460629 1250 627459379 627459419
    0x160314040308091e0a0b040618230303041703030105010305070e092d0c07020301050c070b0c0307091e08071a040e07090b07060605040c03020a020d2106030b0907 71
    0xb001c1c8007809041c038001101c610201c2e1000c40060204042da00030412250b1745421408120001050601c0711907400a1800f002a44d130310a04030280b0701c1c01010380301c4104001d8651804d005a140706030707070030b132400c200b12402000b454550310342e40303803444140985980083c02028002414070012a241c54440d40341886c41081c000d0074100a0745440014580b003401c48040c09104110311030355509c0d141c01d8211024415640380a80c641d0711081d510415003110f40c018115030307180405009030b40c0805e01030b0601c2c03980a0340d44001075980352201101507540d09450360010b2003d401c5030010350300c0e25420b0142441111812230803a10001d450301445030910582a942c40006041400100004e00a0a000d03542000302814200417081e01c901e032030341d80b80d40100415100756454100800c40ba08041c0706120078102c851800f10304152050380002d454110406040e820005c400542024501580010040e060020742041240941ea1b00d4243c0018000301c45520050180c0400081c200381ca001402c165a1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 627461879 1250 627460629 627460643
    0x1201030b130201080609040c26010c0201060e1911040803090f040e15040c15230702010c0b151e09090708251505070204052401140f1603140403 63
    0x4e601c1c17100707008904100410951781500f4001000806a208401086020300700c030176055170401851103214250b40c00d503c1c020086a02d072140c2006841c0104d0000f503000410020070802204207200b02001810b101c5540c0c2c0b1001c01c00040010396050000010110f400c0140c513020340c909410b1040108440303d0722014842d5030440b41484103054860303403660794414440d039079402c46240c950000e40c001803c84510b51000c41c242c0507655901c0c0c0c1d00e500f0035000341c0344e00d0340080d4a010210350002308060700790305005240c000580003040c1c0440082ca0310702c11055024002e0321214519076288050603101070321345801110f10b6000701d007400300c020405000380c0e0164070082c40384550000c0c42d80c1d09641f1041800c10344440e40ca06c0800c21440001a08220061316900c56480d1b00301401000212070b4080e04c407091a0b00c428001c1600402240201e520303408003420414103590f240c1010380b00603c070f8401c0e5120030000015806049001500e14528024025510020b02c1d0410140d00343c010700c541c0c0001303030540c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 627463129 1250 627461879 627461881
    0x290a0e040603050616080c0309070b0a030920040605010905031b19091a0f0f04050a02090901240212180d0b0a05010e0928030509061201030b13020108 66
    0x1140901060024010090000580240d60740c4516040c0103068a0140b262010101e1406106030b0000300390760031000c210416403540c20310080c1140d403100301d407181d07469042e004102a00554001ea00c01c02c04581c201030030840d040301c56002c0790020310b0808031851207545030650100319544100010b006842d4064020245100c04000c5081580b846500103940503546107800e0358081c40003170200c0d000b44003000c0080745e1a131003080c560110514a15085024600c00c0940c2c003c66561181000a100d6058a00107030395100d01d0a010040d20400420300d4004009100001d60b90380b110007600e5502c0103c4120401441240400700d0300e1314665640c103104040140b10051a886400e844202d00243c0141440050102551013244e040c20455000c1d0351641d6410040052040b0388440313a5206980c4006082e0411402c0c1d0301461503d1401c04500000c40840f44450806004408071407616400500031a140d860302004460503c1d03090108035010840540812803203007401442243d2550305071504252 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 627464379 1250 627463129 627463147
    0x170f060406090203030f04080c010210051e04050102041e14042c0304030209250905010f1202040f03050d2307060f09080a0201091b0602030f07080705070e0129 70
    0x240500b964280c1c0c0c14002000717840350403550040180010044000038041d101e20810019042003030700c00c1f11300e403454108020400b111000032003100c2c80c0c92402a0080194131141441c600a004a4000080d0400c013640d09003900020a0840f42c1190400c2804a0382c904402c402e0105030340302c01d0301007145a0780c0e580075140b080c1d00316003150804821207000c503810250341e0740020701c3c5000c05882c22a000c0c0c0390790510ba00c0310a4060030340000751650b414000d40c5580791200080840d09400003c00800070207015618410640d038040714010500c4d40d45081000d51207042c800d885200408502003c03030802c22265442d92a203611079508040301c400142d003010310584509001d411628a010f00e01074be1541c0aa002a8060000d44150700c1158000107400200d8900b250048000007003a401410900c030081107901d07030000444062120342031401e61209402d00d80000107004034000201180038104010031a0800c0c00b81c140d048920704001c8800d2088041020001015207485c400f03600c1d40300b0013001e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 627465629 1250 627464379 627464381
    0x150906090204060203042616030b13020105090f0f21070602011107060c03021b0115090b060433030f0515100311070609200604063f0501170f060406 65
    0x1078a00d030300180081e92145000c0c01f007070074880303032409407452940c09140c1481031100c00c100565100b0814400600401c6044d0001b0702075020751500742e88180f100c80c00e084819243c7c0720000505010240c83d01501a94182d0b41469206a03110407003030f40d00c02c0e078a00280c0c281c0b050150700381c80614100c4091134120640c80d820003030b0000ca001c043c1856020080d000c0410303d149140602d4403c03081c0001218034400c040007808840640c44540400d04145c49000a5501c0700d044400b241c071003052400c040000010310303070b919201020144180752a1030440124094250700030700c03004500000c040100356508501c1c0d440f0050961102900004c0d0380c0010000740d80660b000e5540d21b00320034062810030b1803e948100c259145448101e0340e03054503610441d90f9042e00a200c500726071084034058105410500000c2c00e1005200b18000d10030b4800d401a0155440c8041c0841e992040488443c040301400410b40060b04080c071403002c0400208400d00d004d0300002c600c5549950900d005800184c8860712010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 627466879 1250 627465629 627465659
    0x3040209042a050a120809060702011b0303020405090f13110f130b040506090f042402030406090201022b11010f05010609140402030f04021009080115090609020406020304 75
    0x4a02e900c400740302a1002c0400e8400d01c03601c00340851501c805a00303041c18440c081c60203034040400025294000300024800301d040d2046500700f81c54540d190502400101d4404e40d032070b40300c1e5a801110181e40c0092550540041c0152101501c804c801620b5000c4500c0c0b0601c02190882042e10000c505000011a0b06499000e541390040045001025260014600350207810f502da420940d01d005844c25800c0034000ca035409403040300c1c0544540703400340145400d080b000b04020f00c20704506904107400b00d030040c6000708404d15040111348a01e0300e40307405402400d015406902500c04c4ca511407140780c0207850003004401031506000104100d980c1c00341c4640c01c07079440c4400107540350018158401c0e0b20388a81c2c0e000b0b069995034211400d14002882e000580380c2400b682c0070314010020040d01d040c98036103094000380e05071502c450640010100b1034009010303401c0b4030240d508103152100c400031000358510a417a0f0740e11040001a550300c8584c4101d104601c240c0002d80c006000402000210409034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 627468129 1250 627466879 627466883
    0xb19060804050c010c030c110a0b0c0d0801050307122603040b040605150f360601080907030b01050904030c020d050714030f0a030c050a0b09030703091401020a080c1e0a1b03080304020904 82
    0x507420103622b0fa540001140c000b1319200b0003951040d5040701e40326a0207808540180426406441d526040440083c14180c43e0780001e007900305802440c0040309030035080d120307042d021a1400d640f64101440c00c60703a03401c001d030b8082d00c185042074040b44841030002c5940040301c100418040a0f908103806020080e2003620030008120311034281c20244014440144403901403042e0692018504480007404040014110507210f6100d55014400200e00120284c1526000c54014035280d40c1c40c07074201d40c08106460001d41040c1d04c509108100702001501006551000d45203464400d45982803556a100c4100f141e455a4040c94900012a00403100c0c035114a02034801d580064005495a490700302c0183da80144a074400a00c0809061307000b00a50301078403604296850032080c5500003561040b8809029201035800504011a40c00400960903122200b1000700a0029003005c41034980c0200c3c0000d40343c1078030009046e044102542e40003401d80b80d00c4540c86045844507000d101e00d0100003002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 627469379 1250 627468129 627468139
    0x309330e130b041812030f0b030f0105090606040b030c040504061d0c01080a060b030f0c090409032c130c0e090429060d060b19060804050c010c030c11 66
    0x500501500e0700701c00c1d41030790451000d0201d05080c0c0c64081c4401c8039440342c012018103440c0c0c03825500181034404400c403403410501c2c0200e000141d01800c000200580c0c8801941442020440c000e08441904180d00c0b9800a00c207540c00e65481c1014002943e4000b80c2156240c0c0101c0d420041d94640b551049030010300510740014440260080505209188090740303109a011980341034456a014110540c04507000710306001e01e600e01000d403507541c0400392000c4800060030307000900c400007010a840f03900ca401001449047e0f640d080191905420708042040480c07441120038081003403409030302c5a2000034000d40990b6000e0402c1c20020000c683c003180c20807160a000c03c42c02e0f03a4858a007801607004815810b48803100100e883e0030140071303000918066040f9000c004030f0f03036141e60f03031003102c25081000400c4686145000541e400300782018822003a10355070002ca0100d502480750342c42207101d441200d882484034001542c000e01e800d00014000782c003102d0040002a40750031458031124010301 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 627470629 1250 627469379 627469397
    0x114060405060c071a040819030917152802090916140a03020408100603112202030115090608060a050f1f03051006031401051207080304030807030933 66
    0x404015516880450081700f0380e01141c140702514003402110f9548004102070321040c07600751380180120459125615240162010904003c1d8007803100c02d551040c2c04103101e20a1070407003130760148074810300901420444211800405089548212210b080004040c50900d83d10b10170501c2c42400070f0f070000000c01244400c1030318035020f0800503001c3c521103030320003585440c14020694603150b2001c11401e24503040110420101d9042049818404016606142d00003854102c3c0d40700d29080c49c2d4002d0110f8400400011101005283c0f41110b00303140d51107000840c0d550300304a07070340001524102d506c003440301010421071805c1103807106c1c68200a015280c8400040240c02c41600005900c0d20219850b1000c000f10590002a950040d00d003900301008002c1031001d080c1c54940c4140612401440c00107030611030081d0400160004040c52800c5a0b178468491038103942a41180c1001c0300810503d400115401e0300c04007058a0391542400304038862075200390210840c624810405041c440c2e804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 627471879 1250 627470629 627470639
    0x106030c050f04261002040312210b0102011404050705030d020708061501030b04091208010803071502031f060207051306060203070236090d051c091e14060114060405060c07 76
    0x211805c400612212801030f1501e255050034810a8488116201041494400420918410a0300b47e40720351188000241a02c030900050f4011301019070b04050301c90a000402c41040f40018240050720010350035644d10300c0700c6d1801a6136034240c900a105141d00000b0024810083c19041991810814035020070314904030400310301210028074054407010000800d100117150411141401004400000d61400142c2d03265000c1070400070400340301641e0008003187c0010314944401c40f04141c0601c184044035940c40e00696030b903d00d44101e500800c0904002d00d48035034244030304001c8030382e0b40c0c000d5450b1020300c0e42000854004c14072102410324001c1c041c402155110308803001e45148582020425061203d4190700e0041054801e80030030908109084031115400070794850b100d0070200100340c40456161a0407180040c041e542c082860b54901d0303405004084603c0c05800c4444404e40748943d890362440d403010031801c082c1076040181080300b0001424900010003424104d002900c406d01d80310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 627473129 1250 627471879 627471883
    0x807021503071715090c3a0b0d050304260d0c030c0201120606021609060b09151c020d0506030a050d120605042c0601061d010519080106030c050f0426 66
    0xc0d40d410320071200100300080c001c8822086202d0559030040c0255070010342000c200700108450080261441c8c4070094218240c07100c100803011075600109403030310f0f5500c545000d050003e141a00042d185910303110700320803510224046000c0c1302e1603586c070900da100a8500f079a41001c4800b0480c100b0041070f2010700398190034481c00000d01413070340c094607106070268903181c2000c0d01d541040912626250702000903e04a80485292a0701510395001d26505809902090300850307200c01840020000500d0f003000596000381039400518004000945401e028159107071140c46005015501403554842c8103405011a409000f030001d0020441c142c469001c642522074030182d900507440c03100000144d209412090003180f481c0d0304024042ca604d0540e009042440000c0369207144082d0941101260344030b9400c0311400b00703c00100214422180b8001440d022003449101c000a00e02903150760b81501c140102c650501401b00ba245c2000c0c142805104407000003250f00803010130808959400d4042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 627474379 1250 627473129 627473131
    0x9010810140603280b030c061207030c1e0e2803030e030c120a120f0207150509040504032001060501020c0907031d0616210504060f09080702150307171509 68
    0x85131004241821000305061603c00300713210320343c881d000501445801411140c0320540c840ea50b0301d0003040568a190040e03c920521013480381140042d05411894140c0143c129520040c040d9448278a500122500080c40070124252544510ba500e170300f080420721a24055811680040175540908900800103600b110301003c03910340c030b4008101d41000e11260304503042000f100b07420f0003885a88542e000940b5030781d240c0031303038080b040c800d843c510000b40c880d50641d94840d401510800c00b03400c29003000390416201d49203509245090031700700c508000040c060721084803410303002080001c004004002d44040c00030700c01c108066552210301400540c0d240006980f0b220180a8081800d0041c00748040c0d612209404041c0403402c626119901c05000034803040d1110120001840d8843e464008054040041420442400c254040e420f11410b00c0090141920840351130886494a150381138541c081250104013007501600400e00802128459680c0081c588021a10a1003c08005000104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 627475629 1250 627474379 627474451
    0x7031d1806120c091602030d0f09060606020c0121110a080a0b01020c1302180402030c0a02061b03040213060b0708030108010b03070308190903050706020309010810140603 75
    0x80041c80440d0400344510141c0c0e0001c40050008003d003000404c039851009444003400100c0d0346078000d803061003881540c40328203801400b44407480c4000b10000145c80c1e0a00c0c02d4400b14500400004d00500001d502d09650300103071916141040c888140610034050401031002494640116800c040b1800009100b07040e080e494071015420912400400c0300d2040780009d066610583d62020700f640c1e100310b640e50340c0c1c0402c503015075a6800d94458507020b40400b800c00c0d4000e8004024468a480810054141642540d00b102c51513926a40c1856144d283d42c001d01034032100030404907016040900000305800908080801e0702c13656041c640711658070501083c0d444440c0800188804a02800340345031001c070441c01490002e045071591030051050340380c401100101071126168040c010400440103541182c107480180e60f0750302c8003a40300d0340000170311800030380380e20001606101c68000c00d900342c0c0c040c08000c490100c07010041c0704496001501070198a01040c000c504084044880403d0940f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 627476879 1250 627475629 627475669
    0x7080a0201090c0b0406080f04080c06071e0302040e0c0c150406020403110105030f0606090f03070b03041a090c0d060212100602010501080a050a0f0c03050f011a040b030307031d 78
    0x20954100319403a06169008041c6034002004100100c1f64094400382c0c101d80714412241c650380391881c00a402e0301c56144400998080c1400f00000150030404a2040c0400002010004104d00c1402c5040b8455070094ac040007886d00c0201c2c299415006c050041c042a5000b103d8100318030115020380600f0854007243c5032500002d040c010041034580ba01e054810030708015042d0b0809800848400b200241501e00816000c44c0c550459900c070380515001500107016583c4c540d4644800703210641c0111000e481d1049801e40c0c40d010780e0f10a4507102d10032007080c000751007400c00740c0c0101f00c640d030b0b0058002c5c2c48464081c0503448030a521445141c3c02500010150b0a0340c510344503001c1e09454051f40001c0c202e4020b2040c50000c1340010691920785980030306508802d100f81d1501c8c008100e21600003400702c8c407c1d444450000e0805500c80e19551070a2601d0500c00200d00f000c10099400b0041200d40542041c014980080c0c05141200440600c1032107010100680c0c001041190644d150411016 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 627478129 1250 627476879 627476891
    0x60c09010c0c09060801180b04060e120f0d18020a0303030507050415020d0914010509120703060920191e0305010e0c0108011a0712020a060f090318030b060409020607080a0201 77
    0x5e10007440383c90140c545c0e1269440300d403d00c80e21480351181b0010405003006807150220002c07000148030343e2080f030003481c00664661070b00b01004815a00900400c07582e0a2400c08000d1141c100c035100c0328440e5500601040d80320341542e030114046e00f4060050380601909100c042000d4040c43e110403000529079004014140d00030100407c0c01511358400c40603140406941d44880e41d01004072030f081e01094480300d070072003c048038444c6403840c1503101401561801312080704005d02c880c10140b00c90007807415082008840820051002000d05056010303590b030031000c015511000158581c002d480010041246940c1d89609003552021110360040e500440080d0b020b41da0050b10a07809030a0541c10f12300c0b0f042aa0109003d6407207000806800c0128490a05825502c00c100310840281c0c031180911040114a08850141c0701100045000c1420000440043d407407144c001022660000040c00b8207841e2207090000a2000718420303030f040344017001282d01040e220801404805600c1c1c1c00015a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 627479379 1250 627478129 627478139
    0x1090b070c060c0806100c0201050c190c08240403030e06070305010f120507120839060402030615030a14030d050c04120201030507030b0d03030501090e030c060c09010c0c0906 77
    0x440301d9a40b2400d0a0148910038021749494604140001c400c1600740840800c0c1e80b0f00040c0c4d070500445d4072102c0701c2e2060001c450144035030f507800722503072600c03e03145801040c0c2c0341c01802e9164031240000201081400e5010f6500c42400386145402a01904000907040304805180e030401908440c5040401e489070010046d00d40750230b81e0b6200401c81110201000d0b040c540d9290380b40c8096106004402901c500b12005024051049a519850050401d840c621001503080001503800c3c0503400b400392100c0080101000200b803691189030300030090002696a80c1c40c5525440711040f1340c90301032140f81100000513102d498100003040025004544551328507840e101a110001d15a0399024010b001c200800c4402047c041600c59090801288698a0074004c0b0014000b240300700c0d92016010b840e50f82495007540c8164140d49005c1e1042c0029a03942c5909075072407048885911142e1322401c00030b00024298005031411400515005580100548650508154680019018542e50001046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 627480629 1250 627479379 627479381
    0xf02070615050102070308091e09100807060e060316110d020303010e06030d0527040612060c030501080a0f0813061115150f010c0813061407080f070501090b070c06 72
    0x100400c0b0902c0200703181810365a421a00b40902a20705d0f008200000d10419191215919030118007030250110143c0c0c41c100c00c9490200d50b4a22804006001c0d90340c0200701c941c4240003410b0340000140030145161540c0d480060514003800d801c00402800c005105000700c024040c8100c944075540c021612035042452003140c00b20003406541c0301e03a120030349514101d500101a03608154444000305030108242c0080c440c004c0d003e00405a00a141c504080b80184500c04d0b20500180280340c1000600e18004080d800c8601c20700030703c40c03598041c0c00c038100014100c3ea90b2443e02c602c01e01c0083d06003900c0d06403030100305086401c0344000c910045600c007107044c0200181c0b00d0b46032035103c01c410142081d11442548001740507942e400340381481c0c550740d03559000f400d40810301c07a8441010303a51200802001030410713455014120001d070f400107140300d90302140c005840d01c280e01708000614060303030400400e50f1a8004001191350b5500c1d94441008116018500c40c03041c14142c0b00c4140740032741494000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 627481879 1250 627480629 627480671
    0x60907050d110423100f1d0a090e0f0c0604121e060c1209110f01172517060d020a17062d15060d020d1d07081b040f020706 54
    0x501030500125125002e40c0d201d4006d40d4011072508007184400e140214030a4445044102281c1200c2201c0b03000441a40c83d6010a105207120340566880b0066414401d031100c201d5001554048028802030001128098046005c030f0702c9030800380243d003800d9003451045254048243c90030781e52032901c1c01401c4d0f08846080184481100104201140d03035540700d21101c1100c3e2124083c152400342056180d001e901c0400480002d04000a034074034001d0403c0c0100d814000d00d40d80600750000e41140c00071f010707010a01d004030440031420f890b66910414000081035481003641c0c04010311750000346104003c2c903945500744004003d403d0a1614007000c5240113280800642c016810b000b2030003450200c07517262a041508a01840004a203400024160f1f009603580540300e80d10020f1514070019842e803250016030300b21030609100f80320342441c1c107032110601c0c0b242182a800c440801c48520410807403000303520900500006410501425050407070300100c008541f216915000c40c00600300c444165 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 627483129 1250 627481879 627481949
    0xa020901022104030b040c120c1401050408060f06031c320924040e010e06030f070603020904060906090506041d0d11030d0c020303070314060907050d1104 68
    0x51000c044003072041c9820b40304500c0058017400150f00498200001c07010300d0002401300440d000a800700c142001da461710410705c151240300384854808401540200140c90895407000068041039440302001850b8110041c50f042d41402048640489256940a9000016441c1da0341c040002040604c060054081020b01001d80350500b80004450312044c08443c1c0d000400c5c1e030030100d071158140352410130b140c03050000e00c0d580c5e0010401149110003510680d0482d51400c0041d111604c4807000c0c1526000c0382900f070380c0c0a030400641030010310301a4000780400000508002500743e568030068045a5a135000285400e07151000c0c80518a454082c030780300c6040c5184a00500078207405920780c2c54816804040603c0340241d100c604400d03041c0300341c42ea50003106406210f48002060003c1d166170085a0000c0800d1400c0c41d0481c400e0100c040d02c52151401610f500c5c05034540500a44180e0040380c81842050344810001e81d2040d078547c00f40c070040c84180584c026540a81d890083c12094400394 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 627484379 1250 627483129 627483163
    0x11010204030c0b0c0703150b01090504050402030a240903030c030c110304230a03050c120d020a02060f071407140904022404030507120c06020607090303031e050a02090102 75
    0x10030300200d600c4602c000100d4a61003516580c511440e0189814000164000b400c00480c034401fa100410395074000c5e0b44150801d03658100ba007130300c40b42040b003204c13001d880181d0954041c0c0b81c2100015409003080d400b22402408040c200e40c0466032a5040c3c0768044802c03030000703442c0c0d040400c030716400d0b0051005181c980c1c2011002d11200c0b035500b9a80e4090341c4950054030848240901400e01c0080c4446010500504458002d42c0c582c1029a07990291000a42c05201741082e080000b800101d42812030b20511b5010f01203100040d000c10000ba0050030184503000010419040010681011003400480400140003034a203409051001c8104900200e80184036020812005076510301e0704001400c28240c1c0c401c1550440f190f80d400314010794000170444d114002d808600008584081c80925200703443c66004d140c0c8910b0300f01e880780700036a1144040365240d0f10600c0004d0094000da800c201c07140f400d40c0d450307540e000110f8094a00650ba036041c07859000400718207559050101811198000314 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 627485629 1250 627484379 627484387
    0x15021309052a030709080f060f0105061305040903050903060405150604020406120f0207120315090b031e010e0706050903060117030328092a1a031305030a02030a110102 74
    0x11075421401c1e040002002d401d00000041c001c1ca000b00011406801c0300c03412551481904415640e49400507a00c103800f0309200340c00000c4a150100071600065a21201c00070b0380e03031608041c8009840340c0741d400c8003440030a0058540c5074030100300700c900c242e0040c07000300b43e90300149150142a0390702410303c5003d54010001888a9500041c842d45c00700d100070300c00191584a880c3d008001c0c00760100090200600c03100340280030740d160f0400410406010240d00603180c0e01c980d114101d9455603500364240d0003540070701d408402440800e040c2c0084003000862865551900542005070380c1e001030022030004075603a83c56080400120b409403103071000d403040344514040444d60768000101110301c03e44411400c0700215401d6161000e400107140380a00c100b1109282c5a1052504080304031704405524407400c060000e9640114100c9882031a075043e030355009803900d0a1640000c050300c500d40d06620091002810801c020300500304541e010b16200d1054102c000e08031040d40000110300e1b80188 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 627486879 1250 627485629 627485671
    0x160e040605060d0c200304170a0602120f010522050402130219020c09014509120806010f1103040509010e071b0302120703030e0a0305040f1d0406091502130905 70
    0x104070f6050311034231561030440c1210f44c0b00c50351030100080030040a041c00030599a00b054032061f00c4034050b001e003070302c0b14a02d60b88801c10320002c4443c5801c18000b60021040404896a80d9842141c004e40060304004451a0310750164041ea03103e41070300350310182e0214000010035410700c0703a03111051040f1810070480d45081c4d0f00c0c0740c00002150030300752000b4107807903041240b10003000e501c2401c640e440501d80d034a481154a078402009a4481566108402c82007242903d1040802511915050311002d402c814841011901e18100308054003d40c03104110109a41da030300c4c0000c6000709003001552410746403004000346540781c1814180905204407620200081d0089031490f00c0d0403007200da45844041c0303814110050641000b80c00018024102c0314010705a000006005444004034052030300c1e60703a00c40c40c51034044181d4501040899240205001a07550382018200700e001d8031940320000c0c143c203283e00803a4841801b0070031110009400300303c103683e240034155102c3e92142004285415030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 627488129 1250 627486879 627486883
    0x90f0603180204020c0a0f111011070e060d1703060a050d0305120a14040c060f1404050d03020c0612010305060f0103031b2306011409160e040605060d0c20 68
    0x804024440c940114004400031004c001d9a0b5545410000ea80c0000d8564102446a4a0061000c500414a0270b40000d0000d014500790603100090381e008007206464802d01010007072014111542c015103100200000c1074281c00030110054071410065600e040010800546201a44c8214044c01c0320075410000f29401c401941d16001c0d4403014082c8030b81d1500c1d0040300500c00100103a50400a140a020910030341c100b02a081c0c0310340c0d894882600354000070035100030102c43e80380c4c82c2003882003000f031103982001d001c003910345c6200740100d9580c5e081c0d243c000383d4280c1003c6004000c624802004005200b0104045904240210200b19039541583c40092000407403581c81c8540d40002003c01c010000c2c442e444281c0c20502e81c0c103e4003a01c5842c04d280e505d5503401c0c81000300000c00c0041100c02e43c0f0b001c1c10440e020301550307550308404e44c5c40f0301001ea5408007051061640155a003200090f5520707a04001c1c030700084905c20025208034000d0015041c120450031224119290070442c0e6181440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 627489379 1250 627488129 627488171
    0x9020c0c010c051f0b0d06090303050a0612080702190608090c10050313111c061401050a171c1709071811040b0f03061008092d010606090f0603 63
    0xe6844c0f03083c8825083c01400080c082e1602155007000e9070381c6000c01804102c0e40f0040c0d0507072090b64188416240e03c0807513015100c81c1e0140c040000c09013031069000841d50002070051070b2001d084180881e4001800d9001c0d00000d40c003040c041004903003000040903090000e1081240103d8500c00154100301c002021404000c0041a603510170001081c10700603081481c0001203401004540030254806100c55290340b000c8048861a0a14480c0c03540b02401c1002d03141a10f6010303140f001098a010700b100c00400b06029200098040d0700240001e59640075841d104110b034a459071a4012060007514010381c0c4010302c0446580c0000c542032140c401c5c00315088104180c90326002c6400c090002000c08148604c1d8840f0302c00344d400213500d5801d40082c001840c4a00000c0360095000308960340c080e1a40c0c00215006080b0b6040000303040040c40c0300300c58000d01e100034269501c001103000150b20303084485582010340801e400040030040c0d114000c100c800500194903045c0040c00c200c4c0840c11751000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 627490629 1250 627489379 627489403
    0x9060810050402070305070501060b0a1205131205040e0408030708150d031d03010207260c03161707030309060f020a0c08090402070f060e010501170d0305070207050a09020c0c010c05 80
    0x41c0000c1c4d2038042c0f611031030540d00c00355008802005000d5440401e0000e0354044d05c080f030045000c2c01c4c034598400d41b0318800c0302d100d800c50184c1600c0d1003005568403120401d100040e00b0501a0030300000c45c9180c1c2c0301aa0a01c681c0c41031000700ea030b078104010083c0014900500d014918080004509441e8407030001220700664181070404003c5402d02c1000260909068599003540c80415207009111111450140780c1140d00d01540b1150016010500c4c503104402c45400700f60f000300000300166510003080d0f4106805400d212404038045d0350400c0b00c56001450541c002903d90284c501401268420242c022813816011440c11511030005000d19041900c00b4040340c0c0085a0382e0380c60744854044444c0d503984070140320040b041d10b1500000030001c1d403208400d01e40ca0b0030004210071120990400d000c0310484001c142c1902c2d00d8204a01030800200f69a0441c0900c14001480751121000c40300036009044000d42c450303206d81d520528003804200c40d04d04000c0954550000b01d2408607803010224 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 627491879 1250 627490629 627490631
    0x30219140108180d020304090b0105090a0303080a0b130b18010501092606090a050705060f030109020a03090b09070317120f071116090b090c030712090f05060106090608100504 77
    0xd5150401c94a64001000c992203580c02035404e079415a650100003441030f2503002000300030410030900115802d0048400c1c03541c00c07010004c02440400e00500d0400c3d44040d00b24408600701c1002804111800e10403001c002181d616040e1304841d80c5803610f03503818088214004103030551314100000f45107085038415040074000c965a200403582e011145010070648000844105040107201b00741d4600301700c84140e56500401c2d1f004500b900e0014221107016401d4642941143d08014914001b940300225a80503d40d80310b59201c00144a500c502d40700d005d0035806401c9440c40c1d424110201c101c41c03100e10119180c200407461500c1900a21540c110040390060344081d0340307244080d201d051400409403964402c9401200e810107060301ca04099604203142444441c4014040c031502d40b80c02d0b038046409c001c0038000905a9842104211000c140040c400b084500c1d4541702d10090141001090340c3c0f5402590040c0903607a04484007100405281c94800c51a2170120310070710510f1464010a8851 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 627493129 1250 627491879 627491881
    0x30b04200a1106010305070609150e210109080409140103080a0f021207080d0f1505040510030c0801020a020c03190f0c050612010f270b1503070306030219140108 71
    0x851103042c80e8441100960202d40d0076584a080080da21181072080c00b0000b008102c0100f001c50840001110546250300c80d0403080d142a410040b200918807102d20030748545072544440c0082c01d0060a00460040050030359503401d0514a1080d1000740c000202d042220300e00400c001104075046502e007085034600b0405112030283d0407401c109000e404904030703e2010480b04188400440104004030400000304180c08032030000703000751011851400d1801c0001e240801c4a404d1035080a9801780d081c020100d12180c5aa40e21800c4400682040315140e6000c1900c84030580c04110215041c0b00480c02081c607000d030200e01c00311060791f1001c0100010391200f441070400c080c41d41c900f0054100100f40a80764002018440030b042c509101e1101c040711044400141903855050b14000d01400d500c0e12161400c0307051040000c1c100c0405000c0d003280000144001b501e00c090043c501599070360b60003117000340c81c5004004201d0013241a40c04168007500301000900b4400c0d5000d03141600170f00b000304503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 627494379 1250 627493129 627493147
    0x302030c060c0a050319030b0a0e040f081c020d050604020f031b1603030203150619050f090619080a05131101020a0b01080106030b0a021e0c0a0203010c050703030b0420 74
    0x7400d1041c3d0b4010640d20021464082e01c1c030070414403e03100d81c2c5c0355804020305c0119500700071070030065205405205100300c020501003103415012500441c02804a1803900403150340a207140b0b648860303005803050380450380411415090050700e4005000710350035810440000d01307e80c450320020300446090540b40700350000000003502941c0c2c00c50b205c2b43ca001151394003420090040e40c402c0301d844510700307442c0320302007017916011040e140c0d2070701d6404d0341c0c40014209401c2605d2582c890610031000032020b02160261756501801000c1110b000d480c41c44241e002100007620a01c009007540311654101010440010040201c201205400166a4130402035650050341480c1020401030300070590700700003103072401054000c10304880c810b1206014075a00c009900b800c90081c040e88e102c900d149907042d10303000910f02c00544100e1503a0420b42e03030700c084603500003403c4644801d91007000c0390001c9404020b260f00340c8102003030b0300700603035080c0710741c01a1003144407001d40d4000c48a1303007051001c03882640d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 627495629 1250 627494379 627494383
    0x90f07171c030e0303070309050f150c0a17010b071205070305070b060d0c080105060117132405070806010905010521072a11011d090c0f1308010b0a0302030c060c 71
    0x5905600c0c074080c1ca42c5e90400c0c82c0024050b0a655034240c030071740f06941c11003041540c0007907480f5841072000c0002d03200da207803100f800001e60300c060005010030100400401d107809041340e07030034000d091052010f0780c0ca480b1490080780140d4541300d51018081d06100d0f042c04a1f42060484a002c0e5111f05000c000f80c2e0780500040000c001c3c5c10000c2c0a1100d003140102e0b0400d415400a8002d1400740c0396900c1031246540e096107000c1048549480e190300c25901600000c8042c80041030390541301c41810200c0c03003451000d01c03ca131002c6540e500041c4a26061050550300603090b90050982803900d14909114418000c22003c1e103c050355120407840d10000b196035200e01d00303030481ca45252100c0300070865800b60b0488030102d1901e09503456100c5607400c122660140088400c4184c400c003e460100407000e00300711000300300030316031640380c0820404607031480310b804010044181d1b4110700c6010349041044003401c4485910900740a40e14843c07007400541e40001e103411076981e040301d40e660340341000c0314568 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 627496879 1250 627495629 627495641
    0x3030c070c091506090f0b091e0d0501050406050c0301030b191e0b090a090c0603020c010902040c021609110f09030c1c0605060312040b0304020d0b090f07171c03 71
    0x701d0b09450200c0d0180c0b4070a01540303600458000c5c0d03548403001601c500c01d2586403001c030300c1040301c0151304002a02041c101a08003c807542540c0204980e41139205000c1406003480120840700da954800400c000c014441c8260303900009510b101a00315030640d540c114084601501a186600e080c0c00300c00400d131100e4114032104800c043c200044109048003080142c84049401c0c1d10855182d400200d101c0064070800e01c44540050034030b0354040c03400509500030b41c0b1231052485a5500c0704070b22800b58859000703a0140e10f2640c1d0062280c42405450307607401c484190042d000803820600305004002c9840c0c265114203e500c150903507120706900000e4a8044030454040e0041c1701004410b0401500854070000280200c5050050350780365010550ac0304001600315410103000e010903c12000088081c3d81d000384090101500318010b92158003c8a200b21400e030403d91101e0703d840d46068081c040c050080c0890940000300022030700302c0c113469018210501c40c0c40004001030040c1144070360052 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 627498129 1250 627496879 627496889
    0xb07081f0602070303140702150c21040303030e010506010e01031805070806010f120302150403170405010f0b060c0c151207201504030813140c090601080903030c070c 73
    0x12008541d84000c065203030b11881c803055000c00c880d0a149206514144100d031003480e07000f0040c0003d04600b5100503642d070050540b62005100b08000c607111a03010480d808520242c11045907121403541c9401010707240b2841c1464a03076414130b002c6c0305459800642c1040664424240416041c1e4014021020301642c4040030300346208100c0300048080700131400c0b41c1070302ea440e0340038070a0b81d48071800c80d020030b200e052008005030310a0f4405ca0981000010f07040d000380c820710b1300728036040c041594410300060941c5c003600c103a5550403400740c0d0035006201e001141d48050351450f0401855101641e1102c850540c407a00606e102c400720125a1503040172650842e032203082c0c031039190402d42001800d821a00d411040c041d01e20b40fa10340090740c400160440c181d0007060101c086035030b441e03500f2154240050041004500d05003040c00019460b800c1070b00c00030625100401d003480d01103003009408003001d0101418401280180484400301104581d03018441005080e5240103602d0150305140e029400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 627499379 1250 627498129 627498181
    0x90303090d0b0405060c0c060f0a1119090504060f17010b0d050c090105040911040e030d09051f020306090f061903080c070906050f0d080403060212041a01030b0708 72
    0x5107204004002c92068000c5001e0001c984d46540c031070501d00b2071071003804107060b815408080000d8241d0070300c48160380d0080c1c41e1035012a41b00b441406031022900050a0b500c254030314100314004241d030114418000300421682407105d2440c1411007410400d02c4e000c2d09580b0f000d0100201c282003425045a81799000241c0700300d0a0401c1820155158510501d40902c80c40d00d5100009061404e170140c20401c58210a103c401e0441110800008009071003040066010601040000d540e0501c21038011901400c00f4128001c4102c1355044d1080315000c40b034034103c0c41442489000c0e169010b80c02d60003010f0700700001481e02c9800001d02c0440d03200f01c40c514108030250021080080201c0a03200d11112070701103c03443d82c0c0320010101503500d01d02401c2e8100401d07410842072880d00855803038106019103442c0e441e080e00ea444600691f40280c00031869092844240410000c0507001401d0081d03a0b00304801440d411950b5a070322464016000b202000520008200b050070705007c81c513001406808 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 627500629 1250 627499379 627499399
    0x27061c240314030906040608070c08040b0a0305102d0e01120311070302010e0d060906020c06040201110105010f06120b1206060a06031b051c1e0507030903080a0209030309 75
    0x20361100c01045404101d61451031a42c82e41042e0b2000010b07542d0301040144910301302428100308650b0190018595010402a603071502c4c04a4043c1004002400110300c8030741d52022410005025030790701030840c08400e400301c1002c014400c1c81c0c0c0350200224070f04c3d60403544031221150701130003481c0c0b064219034001c551103400042c91245031441614600d100b0b84401c3d00f03401074504030316280c420b2840080e0124810f04810089494402c011041e00342c4624030014000ca015140c070000c98009207092100c075800b07901848199078001040311200e0404900900056040050245032003220344500001e2001d038510108140301550803000a13500302524044010109001840e07031540141e6640e07000303c80c046400310745e10380300b030061074108a0400300307121070140c00c4c140880e8194401100c03000c2260700c41c04590300441282c0910764002ca1000303015014000440b42a030308036a005401c50b420715103829000000130390000135459003c985140700603124000c1d44003082c00c51143c00726090340000b080c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 627501879 1250 627500629 627500681
    0x50a121b0f0e010914040209071202070503030126120a0804020105090402031e0114060412060b030f031306031404020d0203030c030a051801080105060f090406180227061c 75
    0x81e840c6030488080c41018171401c01c1c03101d00003250400603503001c0c2d0809410400a041c4900034501c4100388032903004018604000c54680900315003080c0c100180343d82e450303100c01c11940000241c0460000b01030000d800c000b40683d010803401d2190151020a0001c0400020706582c082ca00703075001c1400c041c0041d03507a031030b04070245244890080756203045449480d0001c1000094140c81b642c2c0044050642071a007030416809a00410b0440303022249544c90b003108010540b010302c83e0400d008024001943c81e2030034640440c441c2212600008201440c10300310043e540404d0184540042c1c068034003a221038110300100741944074590100a15100018411141d40d078040024041c400c2812070b0802024491401140c0c41c803003e10030aa4003900a121352115120860020304480310000c10008906030b4404408006800150004000d1039022030342007040c121180d009078100540a9004c2040250000000e03d580500725a8034485402c0540100b40c4c099150300003641e04000d07150440d0035640350 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 627503129 1250 627501879 627501899
    0x30e0a080c01030c0504080a0f0f210f0c03320a0509030709090803040b100305070b09040b0a03020913080909250503060618010c060903030b0a050a121b0f 68
    0x1460645000914060a148803584900b06540c01d1f2545c520107000180310343e450304501c0019008054a010540c0d0805100043c90a8410310006d10500c1c0d40382c03807000c040e03480600841c50115580f0148121000e48200184c0d1101c20a9062071007889202c0f400403c2400c011244030b8070311100745003a080025480c1d042078020018001d078010031001c83e40c50396255554003055510f83d4000800710751050010400140c2e0300541d569015220701200c0c5402c555a44078141303404500d62020b80d411700005084c030007500f0140200c003860075098842c40c00c2240b440d0b010441c881c40042c02e21502100f10000d0004000001d004c4801c0c4a100408000c82403d01405e0400e9894105a004401c4403100140e903048034054000d40f4404d000041605003043c1c0d401010022a0344100d120300e0400c0302c0b480f10100055030307034800c09540c180a5540080c030200c50b40c041c0214128940c0152344100300ca480708015803071141000085d210303800004421800d088070404140813481d03800004aa100070400401c1d18004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 627504379 1250 627503129 627503143
    0x2130e0c2107090e0d030509030c0303010f0603060e06031218280e07050405010f090e040b06090907141e1003092d020d0213020f19050a1704030e0a08 66
    0x1c90560b40a42e41c0c0c1c03040030045a080d80c00b820426007002c0d0204510f5030007940410b6200303803d4401d90b0701e40160342e07189604650098100c0d14911162440900c001c69141c03140c0409010700c2c1c060f040b41400c01b800003a0f680d1100c40040040a1000980f01080401a590180066030b010b01061400300008030441240e007100c481001c955070000030000758110121071114020402501c540345401e013081c0c011254030904000d100113000102d00005020342d4800075440c4540e01552030769500e4100801000a10a0090300c000c0181d400303030303005220310427020845204c8080111081e0201040318001c4400340d01c9000c0381a944110068001101c00d5056040039090b030303104543c61038401e00c15804807100740031b202d440c0c0d02e8084e10403951300c0014104244610302c04c0d40002d0443e03404c110001c6020060341d006401078450203070040707800c4030203048078020380348268540d00b01242433a400020050000c6824144045000701031400f080605005820708264010080c041099058070f40c0c00d00c59850135 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 627505629 1250 627504379 627504439
    0x15030a0c0f110c0f01120e01091e030c08070303060e01180606140d0e010b030703031205010501030c0e060310170705090109020a0c020607060b042a020705030627102702130e0c 77
    0x4407001c060b6003000c4040e4490340351a680754480100030b03192378640007456000701d1300c00c4051640e10710003c12699000e400290080607a205400e411150501010054031640d038001018400345141038161044001d0598002d151321a03c0082d11178549002207000d4800010000d8040c0140320000c014164025000284009108400e0085982e5440110111001c5480c6000000c00c41140501c2616104008540001c0e014001c00d480c40d86491403081c803940400840d485070b9108103001c1019003010501d42740100003080046041580743d601c007a01c1c8141e207090080c40b6080c002450401c00c0640d5102d811603800c054000c1041c050003c0c08800c0c01030104d902030132041c03002004044490f10000d00c100a60b80302074003a081e01c0e02c8a40300035601d0170080445103110781a00340010207032030301004059100801c0e24004500c61900f640c3c100403140c148140341c1d01c029085041c0e2005a01e82c0b07146140704099070000015081150180720703080400c6001302076400b2480301c2e652240043c1407410942190 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 627506879 1250 627505629 627505643
    0xf0212040b010f12030e030a17030106020f011107081e040e2203020a030f0c08070c0e0106090b0a0e0622050a12030e040b15030a0c0f110c0f01120e0109 67
    0x1980720188415030014134411020401410611800040e10948040060950107000c0f161282429030322200000c800d90504400d17400080010020190304001ca81a80940d90000f000942c1ca1000010b92500c0f541d1006400c10700000380c0c0e8800a4840c8101c0c00d071275030703403682e00c00c0d02c95171901c41c084034000003541d03041988003020605c1c00103007034105601c12b401ea41c150006e1500d050295016101560100032200a10089041c0c0b000800d0040005240b82c40c480e04c406000b51b82840da505003013503010f0300310004100c1d411000f4480144207104a841901403414110311704d0000400080d441e00c124216045104860f442c2031261040100b80741d0150742007140d01411140d200e000c40d02002d03041c510054001584401260214202030344079001044020380b500c4c4d09007c103e1181100da40c42668800c13140c594401c00061384a0b031000c2c030100303242200d00c0c04003da601038200f29542c0302004030b031003881680c5c2d00e1004035140e03001d16182038401c4110705042c030001c2d43c05600d4030300030412064141c44032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 627508129 1250 627506879 627506881
    0x90a050d020a061406091306060906080a05070807081f111803010b0301020f0706020306060721030e0c10030b0f0a06030e010b062104080c160611011401050d020102010f0212040b 78
    0x2440419146031180031702410046850b6a80c18007a05421407580041d0b9a00c4e5898402051052460184801a02010004220003d1b6529010307241400030350080c80702d85c100100c1031042c64004030340b0a00c105e0010100340403500c94521544001c01c2809105580e0b00303c001a045080c0c40b9290518405038011002004200815000d050070303031080184101c0700c08000c0281c0340c00101d2540c050f64202d4406811141086202d03505c3c150b400240000340d09030fa4401004c1d0100240c2d1500821034003060f080040c002d2483c071000420310744481541c080041c1038840d000c02c81a0348500c00030310103a00e0001c0c071104040d542c0e481c02800501d081d81842d2000c0d400c1520500e05800d0070402c44091207c41c00d079000d00032282030b4040c20030020144c01142c03014000c002081004108020424960b09940001040c10780b4101001d45400f6003040300d10305070790419003030000080400b444281150010345005403501c000f40b0040b4014400d0500b0000c1a0748007140440c418000080401c2c4610b101c1d00c136072692 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 627509379 1250 627508129 627508151
    0x30c05031318051005010219030309120c020a0b07020904020607140d1d030309063016031416030e0c030303010e0a0c110c010507060b1804110f18090a050d020a06 71
    0x130380d0f40107010b45400340e4402e80d183c0964400e407102103401d1034001d2030009114a0542d490103400c0e002c0c0d2035000c0c002614106240709510340041410014240c1244c00c1e0b140101c15400b2440120300100003030f100e0304010030544140042808060b14440c005001d039100c5002451003d445612100042e1500824802100744681800002c60311140c2e002030446040a21507100c00d420500c4a0b140848185285101109040110980d00c0e0107100c3ca80441c5800d00c0e00c00100808a0f41044140c3c0100070070b00d400e0040920300d00300c04d010324080514000c1001c501c4031690a140201510080343c00d0b01c000000022501c8118099038000e8411201c18070058500c1d0070201d03482c0c2c1d514540d104d1f0f02e81040780441d49030341c0a4002400d07114410311001c1040d00c0c103d80028081c0c141041002115003022041004200c0d4103603140501050845202480c250400302081051a95903003400315010903401007841c0e42010440c3c40d200d642d0240440b00d000c40034a00094aa4070110310440300a4102460a10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 627510629 1250 627509379 627509401
    0xf0f020c16081906020f0c030721050322030509031b18060618031c0c0204050a1a01030b12011508060601080403120f0608070b120a0c020a030c0503131805 68
    0x500300340c0102a4070740700b903516440001e60024a10744846d0408000f43d0022400038809040e109000d400784001080c40001d074100c0c41110244564100441001040a0462104510300a80d90158400040303240c241c0303015102c0b48103886601e80d01d8810f40485104820780958030444142056172941941d11011000e081400c2d410341c3d040e54404000c0c402610318001d108034801213440c004007200d404543c0d5a080004501902e085040054102e00004017542401d01945030003003d509400c0103489154a55003010307007500d982c0c650400d1b0304c1c0d001400e8030790b6034200d0714958901e440008024031030a011540035505400e10a13030046016039000240d4944c05034104500c2550180c46400b000540c0866582c02401051507100c11542c1d034440200d074035001001040083c0200e0302c261556401c00300110300c3e1504009141c0170140d803c2c02c00e88105280e0110302c0100d4540d050400172040e1980c0c1c0380c428154001c84900c88030915258000040d541070840048055641d42031080144e5118810851 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 627511879 1250 627510629 627510643
    0x171f05030f1e07031506031a041203110d0608240c030109050c07050703140c0f0307091e0f0903140307020a030f02010e01050c03040203070608090d030f0f020c1608 72
    0x440c15401a20038003401150155910000c10010b0041e100341d40d40341d42d03400320480100e102000255a881c0c80500030000c913524055648540d003020704141e45465aa0129580da000d03010314101341e190500892000315040507030324011035808050021980398408941d4840c103099003150348030490407044080040c0452614051f22002c0d103518a10ba00303042102d07025280c060410700138008200940300100d0000e104a0b4050b40c03103994a5071201e80103083c03061402c48484100351082e0070382c0009449030707900012040100d8070020310100360154281d900f5221801c032119a01d0103182480d40d81e0341e40100300d03070016000d90720a444a2281108103c00c0e0410342c04102c91b01001b5a00c019648030200f4060a0074806c12110b52001040b850582605d140c295182586da010403100c001c403d00c01146028040e1002a045d07920300f60714145001242c0907555900491440289660740c4840481c9070800c0d00840c5030504264015541c03501c01801d4159940f61031852501c51046108012442d841c001c07400d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 627513129 1250 627511879 627511903
    0x1a0a05090c12180105040302010506030d05040e01170f0a030c030206070c05031e090319020a060f082e030f031404120b0903070b0108030a260703020a171f0503 70
    0xc500740b401c52420a82d1094015001142c119468a0400354080742405580e01c1180700e580003007984d040040a041c80d01c0c04015061007403041c107200500c1141e40004000703044600c0451010014410b40d01c1542c02c1c1010f400d8440e2090140303d450f00c00703258020030a5510941700c6d608482007580c41c0030b400c80e10580441c05c01001d41c0c104001c00005c003a9100810202c00d2545200ca0341351101c032100003407420395000701c0c45c0c1c65244e600310341006524010a09000030149800d00104907200d0b0100213012400007044801030004070840340e189040c3c0c102c20b82c8001d0001c00c80e80c4200907200d0500d81407889401100700d00051003044981c0c02608048140c0c0c1c200d4030003420814060810b030b0303a03400c20340c180140721844600c070a000d034401140852602d903009028080c0074680c0c400071201c0040c800b410149500b10304000781d84200c140200074a02040e0b000045141c0107071244070224048450044c86034030901c0020010060010360b550700010181002d50900607038511640da030782410b407503c400d8154 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 627514379 1250 627513129 627513151
    0xd091212030f15090c030506090402060304030c050c04020a050d0e07030b0112030e13020405100c02150702040213060201020a02010f0e030403110307030501090501020304020f040e1c121a0a0509 85
    0xc0301003035400380d04800356803034240502044188400f502c2c2e0b602880d0b00d9000c0106030740c40c0d655100307060f50035101c1d4541141050311010054645600481d5191101800080030451190b940c0418008140a84044240000c0040d50b60344e0f01d040c00102207800403a010f850709483c00d08045070000d40024400c04499003c603540c8090307880d000360482d80c161880c10540501494074805255075541804803c12824449001601d035820642407142008200648505210640f0b0354000940da81039071103a101100002115542c410f00d10100b006406608602c4c0c1200c1d840341d0012900d030350190054900d182da0f55000300030642042d15584240c0340406080a01c44d0820001031000c1420700c800d60006c01c20260032111060341d66958039084a004490558150f580401404114500000720003d1080d0444052024198180720103480300100e0110711164241c4401c0c0c822164010005003015484a6a04016000168640000882004502d180328010402c001b0495242c5000000d00803892006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 627515629 1250 627514379 627514403
    0x50406060c0312020904060902040e270c0904170d0615021501090906020c0a03180e09030a0f0917071a0f0703180e0c1806181e030f0d0912 61
    0x5183e40003503110700e0382c0a41103034440401040501c4140020302c02400880c1000c3d00d00d00e0b0513412502d0300d10941d005070048091228107021404000200590100d004492151507070300e5510700591403141001e00b14600b900c020500c0b0180003240d510040407500c801c1940c03881c03960205022a10340202819036409102c034440103000c0a41c1035440f80c0d40c5544a0384005251840440d0703014034050f613003001100040d8101074224662107203001000000c0403002c0c904d04980c20521059610303030080d5140c400c00c10a03100c9052045a10801040004003a140000c20401c208904010b4480741e05009140107007509002c2c0d40110610343c411200e0400074592400d051003201e40e03048901d804a1078800424075608000460001c00308007556014261041e4403aa845400350318000c44071058000040c860703041440201e014804003030705254400021520043d0a001d52000140310703842c401600c076054459a00300004003400004c0801ca1b010f40340d19011000365507940d20350a5800c0c200c00080036041d5400c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 627516879 1250 627515629 627515657
    0x70e040e03071419051605040b090112030c0204151e030b060d0611030c0a030b031609110409020c0a02011205090d08370c051204080c1213050406060c03 67
    0x3c81410400d036248010740300b5010640101c2410a4040d41e4103684039000781144c24500a40b401c0f0410040800355000e00c03070ba581c20400584e920005209207c5004110031079001018450000c1c12061580140704001d645d00301310038500039202c02e00520344110119116404a8038203d522242142c0e4030403a441c0c00d075601c10060003025a10700d18100e0b00d0580303406c03004002800301c0019501c03940d410301c807403615031070003c10040a4504580050f40240c010002c40988031200c9107555060303600794000400c1d03180f508200c0398a507109552100304554400710b20304c0030491000c2090440315000340d032520000500e00c226102219025554001c5c1903005c070904030303a01c0e406919129407003024590781032030444515955940c1c800c030440c0011020709204d0320040620115104008804801e803038102d003801c0514418a5280102902c0071b00700c92004034140402000c01c00105150218010300140c8a802e41280c561100703800d801880c1c41103090520208a20788180c5585101e917416640b42c410502c854 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 627517985 1106 627516879 627516893
    0xa17040303090b420a080a02040e190b060d0f0b06010206070f14070503211501050901120506031903020f0105011215050a02070c090203070e040e0307 66
    0x1980b0950501c90103812411416640b2000c201421107003250081002c004c000c040d00d52182e081540800c0404002c1201205c00740b084e9070500c50403050002c06900c5000412450100310031a200d100c000c80c0070401c8554101701d015040440c9405c00313032914601c00b685004183c80e656a08014440c0c0e82d41e0400080c0d40c410b2003442c02c0b09613042070702d800800109254495902c043c0d404a580c806000c0203208a40c2d61b00e81e23500c8100002c41012001c10400347c412540c001c10400c2d03ea80e10a141c2d402181159a4650140e403903440e1a010078140c0340081002500b110f07054401e811100c0003a54084807402c1885000f81c0090504105048000707080d180160040e0366507032942c20042001902d00300d15801000c2c402480891240e035428850300080c081d080c40508030415900000800030807690046003c0e07505035503101c0040c1c0c541410b010684856040140e031980c804c200c001e01061304 = true := by decide +kernel

theorem cover : BRFrame.Cov 627338129 627517985 := by
  have h0 := BRFrame.cov_init 627338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 627338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 627338129 ≤ n) (h2 : n < 627517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
