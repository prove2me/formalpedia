-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1096
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:13:33.621633+00:00
-- url     : https://prove2.me/submissions/2f47e4f1-2a0f-4fe3-bd6f-f2f53a0cf46d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 196942446 ≤ n < 197122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 196943696 1250 196942446 196942457
    0xd03080615280507050d0305150307030f1407080d03050a0f0519050a140a0b042022151d010c030909020a020c0307080f1501081c03110a 60
    0xc0e03440e022450035030207010709a950746450180c50b48454450420b180908007039010228140419025208980c0c200d640b0a0a54001003000b034000350050074241d4001d800f10400017480c61540c02d00055210a03240c0289000c41c00300640c1c1e950504a060301c0c40152601d0007220000980702c881000010100c191075103002c80c140c50542d0390310b4100c480e643c201c0c5a8a0f41400180404418805205090611420004142542d0f403d0841000d03014000c51b41219076143d4003084400141640160021201101c06008480c0810440d0310701108008403501303480c40802ca45040055600d2a143e41c4560f80d01880b400035035110140a01d0131020090080400d090581c1c640078803140c141084240744090910b5404051503031001445010075004202c04164001410382189008000916084c84000e08641030107072a0104151200b00c02da50036200c602c1102115a030001416241340e041c0d415410051001c03250585020346444107180d83c0f2802e25a55141000c040c04450008209040c9192282c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 196944946 1250 196943696 196943701
    0x2d07050a030b040504080307030c0509120c0405071404170a08070807110a0614090f1c0507060309200a0905010f03050601080105060303040e040c0e0a06060f11070515090d0308 77
    0x607065a41c00098035126514000810000981160599402c030086141c001185da070b00e4001600c0f01d10031040850f6004040804071241c0d0fa00004424881d0102518103019035242c00c0000d80d2007502030301c805558918127202c144985022192061204c507400411110514403a488503100e6a002d640705075407860300002d42e00c050140c4007140d04e80c400070640707503008420701d4003500801c00041503100540d120b034000707404ca04595840c0780d03419051400500f844a04920207c0d43e10095807018000c481038021800c001170201d000e48151200f498001020f0200840303544090100d911a961145620036000100400c82100f80d10815000c1d00c0a100300c1e58485045081051400d44168445011a030401080110544001c81501c084450042e00400d4686035842c101c44107005070b401c048504809230b000c000202c402600143c0807145191100c09c400c4200300320882d02080260b0308018260312214040089050402050004000001465051039402000544017101021007600020040e806 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 196946196 1250 196944946 196944967
    0x303020f04170d110d03020d1d0c0a06080103080703120f05070e04060b070f1b0b0a030606110a05120a0504030203010213060f110604030f1412010e0604142d0705 71
    0x403c8140f50540c1040f446290500d605280d403140b02022013400c150b000300740305140148135009008032042c0c801050090581e2101a240d807458a02400341c45401440c40c00210079025003d050f041c0c83d040759900d4542003a42e101910782c421800410001d81d980e600203502540307510b200b441e0056039655a0b03400c400d8001001c10090f94100d400064440300c08000881c0050a015034203401280d000c100c0398264098140c020608003026072100103621000200d100146d0b42c9030340880e080c1c541035107614502c011803007622980c80c044050002c000350311010040d07054280560141111400c80d00e032161500d40c80b80d020034266045001d600f032456400e241d0034811300e5041030104181c2c0290740380603018450481c418503580d0001030006014040250b6038100308911a2034010000e03090000320070794560761007200382c00310102482081d1b000d905020100e402803031715000e2524000d0508041100079141c40041c900350500c200c48804c194006407401031003003801250003611039450780c5c80d095202d445484 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 196947446 1250 196946196 196946203
    0x1b06040b010f0e0402100e0612010e10060c0615050613030c090c0c110112050f060f0603070c0204050c04030f050708010b0d080a0302030a06081603030e090405070608040303020f0417 80
    0x20000111003682070b00a01001c04000c43c0035610540466143c4940b04880d0300c1641d0f80c40d4621419500050700084910310500303c0c20f40c0703e04950488900c1102366441020f000103030100f902a8100041d4503a0b0148080740c002c2d0024160a800103a07000da07403a6603000028503035440305601083d2500c480b501042807007110307141300d0002c0089a07000c0c80b0175182d000c0c000703010018a0300028000e4415413410841644500001c201880083c1c1c41041241030086004140800c11904988903100c00d440c0c14209040c0842940d0060899444664400b6030310b60800000d803200614150384000103100020100307070350a0855070058002e02c003a100744d84c1072620142c20350314112042d50251441072004800103030400d044890b5041c041c500141c4039120107850b04040c1609905c4001e440c8201280205000d4991007440200c0307110b42c6680c4080f03803114050004105040f02e000d8100d8000e403004010040c003500c250f6520070320030302e40103242400342440c000441d0095000b03406045c9103494900c4881c038080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 196948696 1250 196947446 196947449
    0x105011214011401050111010605030102041205010f060e0112050c10030c08010b03010b0706020a0201090c0f050a1d070507080708161218231c0b010b16080f1b06040b01 74
    0x100a001100b84103030f9950040c101886154104048140070180f00e81080d48024090400140255942c580e505406101c0043c002c405032841d52800c02d80c4030003403244d072241108503102c61000300c00c01c1e8600466041400f41ca01815503860240703920b156026038880030341d01c54600168400140d0185106802400c4400503001038841660410041c08180390704001e5427042c0303600410159451405c038400724007502c4000c1c80204144584200400c2d0f4810300c03240f0b1400c0e0760041d19802c0701c2e560b03a42a001e14004500014290741e48404e030220704010720030f800070502d00f0b02a000040c9410001e94500c4c005500c022a50460011503030802d00405c020030070b94041005292800915060000c0c0c00e031a8070108038403483d022024400070001040711032044040511100400740660201c0740710400e88a442000811204481070000101702d01c9103400603601504840c46d240c600c0e000044c0d50326001e56026120800c0103410500400c2900c090030000d40c1400c0d242000602031500302481d214801d44410b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 196949946 1250 196948696 196948733
    0x6050a091209210f05030a1e0e010e0906060403021e030106090b0132070312060603230c07020901030807111f050f31120b0a0906060801050112 63
    0x440700200150345518103040c0f414401c00440341200542850b00d4014001d054a00405500020854140041c0c020010348801030301c02e8005a1303046400c1008592500c3c14000d40c07404283c000622002e81d0030b040f9007441c0d0140004d40788034542604d03034000910200c016150450b1070350004d1500281818280580c10050000080500021421400281034290300359103420702c02100030081008108008003241014040040041e5a41c04505004001348001119440502d0900d0800201d10748070b407154070510006100840d041020320403003070b640103102800c116102401440340e040541ea49484180c000c501c215102035440c0300518080b030041500d24003543c45004a00035085201c044000e112811883c9460072a075030711100d0b51402000e0180d041294450200c000c0c94041c030f01d46040c00013251186c6154500c49aa6903074050065100020400500b40c01b202c0010441000540d080040c02c2480360401061440d164144142128002d030300c40200443c8211400b418014000031007a1440e0a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 196951196 1250 196949946 196949957
    0xf190201060602010b0d0f060b090a150b1303140115140306150f0427030309020310110a140903011b031d0303010e0603240105010f0e030a0206090103060306050a0912 73
    0x10143c00041021450749006030495010504038410050709038840601140c9c0180160342c00c2c1820001d100040454bd2003155030040b0601d03001c10f81d0840482503d55030004024811b00d014296a507000859000c41c40007a901d42d210500358031b520100314034010252041c4151076405ca88010209447c5c01d00141a0750f210f070650340c0409040780c80340032400603900800c0c0d80114908900e40211051881076a001c6110b0b8034080c01c01004040d0300d600714940c4103000b14129184040760300316039011140200c551424204d000c0105e8411540950740c003041283c0880201c2d07040000f584e010909541c03034040c0c0000101440c25261804a401d4400c0b0440000c0c8903511410f61010340341c2c2c86a480c032040c0030350304502e42c010300001c3c1c0c40d0303408001c0e4030920314075000c3c40c031040701d041d03400c01040100038004c4901013180c1c5007082017002d00c80d0325100d80c40740d0018010301d07c2c940641c0a104940c2c0c80f010416041645a440200c0070401c5801032500980c29071100040040392410046800059400c40c43c08020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 196952446 1250 196951196 196951211
    0xa030c0e150a020a06110d060e0c04030f080c06070906080a09030912060902030a05070501020c060c1507021011091008010b120c0712020606010f030506060a03020304080f19020106060201 82
    0x11a05614088142a1502910750307940c03001d1401d070314040102d0b03c0142110b042c10b42000c00fa00440000e001447c64060050150546482e802042140101e841550f811024001000440c1c840740800340141d019904042c90410b48200441c01c080084401c00b01041d4050700802a013a44240c0a40d1700c5202c0d40e008201d510b9150b54020000c000341d1107a0110785071f0380c2d440c40c070a000c0d075644000080b070350080840b00190051b203421600c0d13806030303c282350250041c10003c60300c904200080710720200760b800c0500300c00242c000c0c10190010001d016002140306559850600701003030300c102c5030403007001090103441d03189680801107201c1c1e00c1c480c0c00e02004829401001809100015252a030381c106100b01e6280c0e80b05405121a8003c0c0117000d071004a040c074030000007640100341d8034040c0000703903980c408101054100390144e64040d60080d410400811040352154800c0e8091604240b00300e0707010b80b800e0302d8a0b0160301c2c682c05c640c44100e00d04101d50315000038a07409129840041c03031540002d21542 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 196953696 1250 196952446 196952449
    0x20a0e01181a0f0f070c150e090402010503070311180a050607051903020f0706050912070b09060a0e0d08120906150423040303060906060903080d0e12030c0a030c0e 72
    0x1d241040c0840d07001c0b400410b00322928880c110a071103009440110031a1159000d0808100c58980da00c82c13145513400303078188540d025228112010441c0006442c8102c5034071103500454095200500745410180e4810748140d40d04aa40c000f030940d100407800003240462110304101a02d01c503944034510601c010065040001c01c00310317403440f0248108854180b54011414180c1c20881018440c08141c050508040360140d08103001d0107030020207541a00031709294045540d0350b1200d80c040e6000c200010700c030480c01c43c9080ca00030a1002920b04d405400c001004001c6100600f1494003240d5441c404106900740c038190f40103840d80128030304028001803d086821003840c04190301624003e64449442e11942242c6424140d030518641042041526013410010300034080390052a58140c245900000c2c2c02d8418000e0405807900309000a1405030040f5812000384503141d80307206903004030605190914800380145100c1c2e43c81c4000705903510307100e00000f070486440000071005e2208400398038a16 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 196954946 1250 196953696 196953719
    0x906071103071e08040e07030624020703021009051206010503060f01060807120207050f070f05060a05030c0306030106120305180a182a0c020f090606070b0406020409020a0e0118 78
    0x4a42c1440c3c01111898600c2c00c1052241c03195070080507419450b4401d010381039505902c6041202c0b042d070130a40c61a070940d0f00d40c0345540d00080c9280d0050b406240240054605030301c20440090450030820146691070002c650641c1c005081c00303402d078002e10010030076414140900c1c0d52222207083d030014a0f40c10704a015280c004d029042c1c00420441c14010302d03440c16554101c032622900036007141d0101c070350303170140755030740c8485019035142403805a0380010107041c240d0544460f0402511010b0440c0c1d141d0030034509980000300440d5256489050004061782e0300c1d50000038007402035030ba20342e480074460340c8000030282900c10240102c241e08410440c2d000f104100c80044449640c010580b20030f4202d03500840e0811100c0d000c1c0142d02102198403154011400804032132023958145030304005a400c01050100445500d900050100061400601030360300701a44036102e040c005003400e03110840c92040746c200200146c013160002c0304010f01d6680000b0f01c0c0c4409144185a09110303410000706908 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 196956196 1250 196954946 196954973
    0x31204030c090c0210020309060402030c09090d0c0c030c080307060509030306010504050409050c03010e0a0c091407121e0506040b031c051b0313030c0e160c0201020c09090607110307 80
    0xc40300c0d034803154003c46610030300030f0304819501d6100954613403c0c80070301a6103625081d94120721910440ba05503400707003480a071462003509010060046c1c0c1009010598440003109000c03070701c0911150340480021010b900440c007403e20301e0019600d81c445803400504646002d015084030358014002c10000d42c0e4400119800d4078800d58000c40e0681c8549001c520b00380750b0061240c0e0550a120960b10380220005e0901e0a91b801611080c02580c0d80d009008111000d0f003401c0c2c2d202080d48400624010700600c000e48003062020800100c45400400c00000d000030350324600c0340382d40c80b40e040c00300620f458040c00035240000c070003a01c55600b5080d4001d03256508601007005011000c141a48400170040c0300044900c50b0405030307980d41045070b1100c4a560b140b4041100c03c9225140c0201e01c04902c40d0b039643c42040e01240c11242605041e406541c18090003008904502c26500d80e050651100c100c030a0080742044000e1085051083e4003809203000700079429900c0c0d005104030000300d2000082880d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 196957446 1250 196956196 196956209
    0x309100e070605300a0b060705061f03080d091a060906120c0d050114071e081801020a030c0f050a05030103080d091403030a060b07051b0a090606030506031204030c 72
    0x50355121311051040c0060183c9550201e00d002040313003000241100d204e0380c1d02c140c001c2481007140103420820044c90b8002e840000c0c0c0b49921207000188040560000010610104c4105001c06a40c940e9028415444003080840c12515810020200409942c5200301c80ba410301c2090034a10b01140070902800008110750b1040911505e005a00388050101100201c0003408091041c4d400313003486070280035482e61115845c0c0d080700c0040d10017403142095035040b000640460320248540c00b41115480405088080c0c02e41c0c4804142c01d804000348002e200100254030045604000060003811a4161101500c2804010000350b00403d40c090304072415683e1044609031220080403107880180642e42d0010b200d030000742400302c0301d000c00001441c82040780e1502407003002c3d1101d2241040e40901e01c0300604592104418000340a846000141e00750806461145c215942e02912015284c00e0350050380442c2e0354005100440c2020300c04001e50b4102d02409900e464a1750380d5070007800b81c0510960 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 196958696 1250 196957446 196957457
    0xc073011030d0f051806040b0d0617060f0106050702061303030c0308090c0a0902070507080d050c0115061707030b10170c130314071e09050a0504080306040c09030212030309100e0706 80
    0x117060580d01d040c1503402030012003264a803184496a400401812103000e804400c4400c80080902e032200002c81920070746800803090301a0f4641030060700c0e035400c0b02204903800ba00c18842c502d9280d03003850310b040c01140640d80b000311400c224200a4000d020160002603140c024005440c1c807512624000e104954180c500140d4074500e0f42880e50402d1302b103802c1070885000b100000801c20703500074080c2010401c90402007110510803490b1490706002403150784042200144907201b207018010849a01292900f800b043e14038400c000241e042480c19002c401180390703a107100c94003c02c801c10043c1c0c043c002c0070b181da00d400c600400c40e40703c4c50b1480c480240b810008200740d1102150904c00d81006040702c03071034080c000c00b20001d040d810840a005038003010f450000054034a50f00d0740a0307140502d07005590949140c030340005100241508074443c2c400d000322044c0020044e140c1c030f01e41c1514542401d018603203e050103001d20307050100103103400140078100440f0390ba860f040454101704581c540d0520 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 196959946 1250 196958696 196958737
    0x3020712170406030603150203061c060e01060321030908090d080f030903090f010513030210270e0105030604030f030c030b0607050609060c0c073011030d0f05 70
    0x118040005010300903207140c001140000310290941c000906a92003044030100740f2201c0001481240402c4658603813010100e000d9091000e036035154107120b1070060307601145918440d540e07030b425180d403a4000c40d00403803d4040c5030080001c078000c80010010320701d030600c101d42c000e890740078903402060542d51042c02e550940d0820442410103c808990740c18800580781d160140ca0030b602c980041c40028010400818888100c3d0302c141c0c220b441482c1c036603070000265030542c1c00784001c0101d0700c00c52340140000111100560440071880c002600241c40ca140d40d050709082c441101a141a80424025481402070100094000c44940d1210101d864001000410f807801140603007066010303070303410a80000e81581400b2000c00c54506c80c0b09140202c0e4515240c3d0030b00c02c3c10038441c4201d01d20142d00702c1401485428030101d020700c00b0100240c10780400b100310a0049c80c0c240b1140401303c40704500c0d1003500380035040c00d12445000d01c2d000c0c10b10399850354480b14040c04038420b03107988020300c3d000c4440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 196961196 1250 196959946 196959953
    0x40303020312070e0d08040923131502070f0c060e130c03110309030a2003040501030b0a0e0127020901051911010c020c03060a02070305090907030905010f022503020712 74
    0x4c00d00703080c24000e000d404503000c182040342040d4028003e032500c003402d0807003140300c62002d804041c0c9024941d280030900da0b0b80d403034940c8121028a02046581c1440c030350b411b018800d42c900240c141907014215603118100c1501d011040c808450748110240000740841c6480381d40c40c4500c14201003d2800c01049400c20042d00b14010b064a800c1035890b101e010084c049043c0001018281d014665284c40360183c035054403c0c01d03505034091100031258810402882194070a4101e586e200d41c000d41103c0c1400d440d044c8080d4040826002180c000c00c0e450742600d501412600301000a910358401186001c0311407000038401d00c1003410981c1d01c0c0a03024409800c0e1841920741c14070855141001704014030b11114000e40b200d415103e81842442007001161b8220380e07038402c88052035415103500b8a0201380c80c090017841c8800402407001c2c5651036242101044080c041c2c4200015201c1005070b680000c01070211160002103200f002c080f0304440342000003500015500150354401941c40425407440c0ba = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 196962446 1250 196961196 196961207
    0x62105150903070807080a03050601090e0a0e070b0a0f0914090423011e0b06090d030e01110307030c030914090612030705070f0e240607170a0c0c0b04030302031207 72
    0xf54001c0c09040001902d07001d00c0241c01c0130b000c0c0300c0d015130740910043e101d45004681c000d0a0f4010001242c242e9804520580e285070b21021b03010038107406460200c3d50310300c16a250303600703d04a907801041001c4903a90205601c1481b802c084e22000d000c00b103810079220041440e1441c0184002c01140041c1c410f11460044030954522007641c43c00284628030301007031458240d45045180040b1281060f94040940c942030003507960412000d40108941503258804803481e41010718118107000d00d020010184e46030034001046030728065190740303e083c01070b0700d0010701034a569401880b040311905214000d60b520b1210442d000a01150380c44080c00c0007204550851090101c001d00e1032290b0200003402040504990701201e0091f00190410381c1c94031900d40d0100b0400400c01c041d200f014248000034644040900001405003401031040410301029124a0b884a140003001c0341035500c40004000380e01c0322039000b4284480c3d0003410030b442c65a000c0d580c2e004108881064144400000d0a9076200c7c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 196963696 1250 196962446 196962457
    0x60714090d0f0803042301020703081f050303030709060906031a01180b0412020a12080a0804080405040504050102030f07030e070303051c052404020a0c030810080102030a062105150903 81
    0x2000d00d95a04261916940300a10407607200c02c2c00550401c2c0403a03406d018802d4810440d05a290740d03a03031340c0d110405d1141c1a60031503440c52000340d0803040841c1d1910100051072181810340c540f44501c509000000c0d05403c0c603640300504140c10031a650701c00749a003135505600d64a084c01e00c80c00d003030082d48400001d01c04a401444010340081800038856003503244044001d8029980c0428190711440d900c250704450050180001300100400c1d41c444d031090703401d958894003642e00c250034242c0790701c0064281c45081d141075480760b4000c420300800260010119810150781d040400a28400000e0382c5d072a0380c51440050705210020030300100c04181d043c80724612440000d0100f0103843e1a403140c841240f100301440031a4145540c107010b140c2014403c82d480d03000300da1100825841d060b6800c40c0c1403c4000d01c801035203522410700051680d002d0014500807a10100013140c041d040c1141400146500e203100300d00250340e81d07001000300b90040b1780302011841a9038505c03590740d03c40b040d892441c40f50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 196964946 1250 196963696 196963703
    0x20d060b1303020a0b0703090b0f09040f020901081807170c0a03060212070e06030f0901020c1005071101090b0114120303072102070c0b1c05090f060714090d0f 70
    0x10600c0780450075050140c00d8900c00c99020902c1911075802c00740c0b0707000e8814000c01103403001e41c050188000050141480c441c0194000f4034140c54000454141d582d6400d00340140c41d00800c9800a540e042080b07258083d80f085000740325000307580c00c440c2d5500d0f0700b4461a003112002617201484d038081030251048029002e0182a03006a503031500000030752140c0ca5200c4003281c200301186a0901c03031203c0d120400402040e0300c1c2140c5840520b00e804185c081d04d41e2456640c201311542a0690910801746400d481c014006054944440050803a50012403846180d924020581d800144034240283c195903c3c1303442c10104000c0b00020444002c003203606410140b10200403c01201d0b802070740e440d0f0081c2100001c40d01d088503042d162003a4041c40d54010001a02d0490601031100d0b01c2c2c01404c030144002c2c4002c0030035004028004212a429101c5e1181a006942d880100c10b0b0200806500040b01c1d240c4907202d4419140401a54041d10881034821014014041c080c4030800f4031440b81182c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 196966196 1250 196964946 196964969
    0x32d0309060a0e15180705010801080309131410030201140a1e0203070f0b0603070909030c0b1f09060e070e031209130606030c090609060c0623040503070c080607090504020d06 77
    0x41c105e25581701020981c00f800950311070701602007015440b9031492030480d204070001f2350500d0301c444204140019104124070074a070741c541d900e07014080503440d468003a0000748862000142540001071482140c030a4800c66080f04028890701654410311070f0714070410b500403011000301101c030100e0562040100c0a05000c00c0d000100042c000506501d42c0180c0084049500950745c503858002600c4450f18041c1c0071038055002140480c1c2582c41055224031040482c0021104a11140e80241c486400185000e42c0c0c0c0c40040c00038490502900d50448028200b4109142410780040d80d01c0354001811803080c4004100c4c0c1c2e02a031504224502641440e03942402000d40b80c0200400900c54100ca01c000100011000903044c1d02640001c0183d8031141d40b00e280d0300c4031130f072280ca001d040101e64002803100200079003280c241d8046801ea01961141001d10740d218241d0808404200c415007200500da00044140400d6a800c500d41200301e52003618050303103c5250201c01001014981d011910212 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 196967446 1250 196966196 196966201
    0x2070c12150c0c0b0114130c020d0305010509040503090d0807020901151701080c010c030c020d0503120a050c09040f0207020a0f150516031b05032d0309060a0e15 71
    0x304070141d0300e00038085400b040201c9074540300721540380c20280e000d44aa4060380c018030421000245065622202814803820020459810001c075010703441c00c1702c016000f0a54500503076030b040c09540c0c01804200c91600c8241007079207070b0a449126050380301d0701c10b040030100c0c40d08110592090710380d80c0741c004104000c0b96070340e0380c890340910700300343d80c07040005d40c80110041102c0308209119050300d070003000500c5039410540065075180c014603401e17428001c42003004001030751003c1411807428803e001940c0c4519010002400300304015102c204424101000c0040752115407090b5682190211004201042c000d110f1000030321135182c002e50400c800860101d40f10038440c039000f04840e5148101c5001d154441d604841c24054003a401550588050303403940403922403a060071040c1050f60081c040c0c0301321507840501c5c40d40460901083c1100c502090103e02d0384260340e410310050381c0c1030f6042c514039224039455240e08000701b2468103d1b5407102d81070b40040342046002d0450a01d20800e80700d90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 196968696 1250 196967446 196967453
    0x2031e0a05010504050a1404140f010207080406020c030706080c0a0c0b0711060c0a090302060903070b0a020f2a121f0207050c0f0a1205010b06041e050f1302070c12 72
    0x1040240241d5000c0c41c03c05c40442c00002840c0301e0050340040c25011190141c0f502d94a080da06d00815040310100d115226014162510a00c02003d00c03921401505a4032460400040d040000c05803489100307402818080000341d0700305e0301c00c40d400210144a0b40d43c0f40d140503800d0740d1480c0c0181e40a08a800c0f0b0030200003111360044917181c0c01c45122002c459041c0c1d40c000100c440c0d8800c0b034901c0000a40080c80420050030a4000380c01c0c5040005d040d200c450782c0703c1c1a030003005d41041e0001001a404203900c2415181c1c180b00e80034800303900002154904806201c0f101c0c00103208020305014800344100b80c844a44180304860104003104425401d0844160342400030b50886d510644076400383c41641c42c5549010602c26042540227003c00508601d00121004060302c1c07100d090b41e040d52510859a50f60b40d07003400074405000b1884e44503036184122501985c0c840f0a80d08100c1c00b0707001d045403800641d5100001d03050807280c8000c0c0580e07200700c240307010415214140e100354000c48440103d5000c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 196969946 1250 196968696 196968701
    0x31504200310051c030c021c0b01030c0617060f01092301030e030426011503030804030201140606030a0c0513060504051e060703030b0f0d053d02031e0a 67
    0x1946281442c0301819200e03020030181460f900c0107404a000301003e0f04000900401e01c0da0080c40c0020202e01d080d40c0464450191842100000c540001d4941c0051082003000c01c204009071425181503d0050307426a541c40e481c01014001070b11801d181000700c0d242d48c1c400c204000107005010324030300b0f402c5c1601209003808006140101c1c0070908014054948890000640c1c2c101ca902180050134440400040d8180301198060814a5500c50b20042c687c22084602c000080d84a680c690703c003880c00b03003402400c444000400307811440d040f2090090655440e0b0036207401c01030000001542c2e4031501400e440718030464032000d00404194400180064101e0040d0048450980e4110a441d50002c001c9040240b10010b240c2d02940a20000010038030039807081d0b055607030203080404d05c000b42e800021001e00322118120b075180d101c04140d0390700307102d0800070201071004c08121410085c0118001010301800880c10802e19034048000b610140300c0e82207444816030400c0c2d6042050400b245172901 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 196971196 1250 196969946 196969951
    0x615030a062a0c082d0403080d0e010207030801030209070327050d08090a060f09140c011101090c05040905010612030f090501050a27051c060b03120315042003 70
    0xd0040441c0ca10445590082c003903003d505030b01c100e041d85040082070341d1200421610700301c0602c0260042000c42c0c051007440092001d50700a0740302507206c011011705c4406480480801c858680d005010500c0041d800845184c10743e54101c8502d03040d035950740c03011801000780d002c501a5880e1101c12041000f180e00e14946031040c058003c1e14114910f00a05030740c8004207464a0311a64480078072880410150b41c8004c400a41a04000c40e03006510744610680b00450a601c26480c0c0018181000030768101c0040003010348800b0080c041c090300c54690301c81101d0f007842821b0207039031515030310401c026080d442103019040320707580840c1612079810001c10340592483c4110110b030000402040660142007950041a426940c402d603102034100c40044103e165071000ca03d000c0c0380e031008206940c859207995480200c03484040c00c8407a0034206036043d42c003210205c0d40a0380000c500c102d0394108203c1120340c01038403041103104201c10303440800d00400103030426510461820480b8100220741178020b50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 196972446 1250 196971196 196971251
    0x20c01060e1006170a0504060b10080f0a060609030b0606070c03030203040608010801140c090a0504050109020c100e060f1e01060f0f020d020d03111c060302030601170615030a06 78
    0x1c0345911240103480c07404a0100813151041e181e80095621042c9400055000d032050101096030603584020441c0001052000c00c0826902c1d0108180e10303154101c40e42d8041c88030002170012516080014041141c5070101500b591126400138605844030301c02c642c03800f503010072600403061b580e0400035100d400c58051000000c880c20000140514140148500c0c1042c8010802c3e054a43c02107100444e40b140150b603401c2040c5050005280d5a81e01c20385000f04030b155005603444103034890840c00c10010680c0c030006145801e810070f40723586000a00301d9015030b0200c228029521003c80350715a0311400d0020580003810300e030011856550040405e2020700c4280c50350b04101c0d00040c1c09903201c0390220321132001a4062685507910324480d4010400014851840340d01c0c110f903801041d42c0013004042a241101d446000800440c10304102c640d00504010030310180d95112444402e03100d50000d00881c440c828014020b00355542e0901ca4020850380c058000c000d840100e4049590541d51175100d00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 196973696 1250 196972446 196972471
    0xb04030506042306010506071b06050301060207050108090d23071b08060f0a110d0f02120c1312021215070f0c08030109022506060f0b0403080702010e04020c01060e 72
    0xc001a2034480f103241074014440c2e014006583c20700081c00120f4100c000262201550180c080c002d065118003150003404195a440b592503062034006031500a06a0055041101c84010442d2480011503040d038600c801d440c1601024000d4407101507805d841031807000780000f00049800400c03520ba00c88500344941104c00251942e503446030780713840324000c0b15180c160703504020003d2030030700d21980540c100340701079084981480c1c5405028021180382034424130900c0c0d030000d90704620711a041e034581e5002c641151400e280c002c01550348140c00794644504844c4d580300e1604002103581b42403141c085040514102c418444a070400d1081000e000d90b401c4000c65071010441c65814491030700c01c42c4264014500f80d1559180001c1100258810900001c0d00030600815010852290345141d600324091003000c05d903103003021107501602d840303640481c071003000030070040000511450a031050a034090814400c0c041c40240824041c3c0719081e481c1d5265480d207038001c5040c00b010f01440307011741c4008021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 196974946 1250 196973696 196973723
    0xb0313110a0305031c1b0206010f0b0c0a08130306050411091501020a08030901151d070807090306020702150309010603031707020304150c050d120f1e0c090b0403050604 74
    0x280721946100b4003000d012034008200340348110081140301c038888004400300151a11320100c0041e4005180300e00200160400d00040040341640c000d8080a048010400351500c5041e00a00ba507035142e0301401004c40360301080d5054480c00041280b0001c5401c00402e03c000d1425140c002800360450103807510404503580851410700025682448129040e00140309842c8280c50301007036034000402601e8590740358800c0c4255410340c1c80c2c40b2002409103880003620743c076060b4a1010501c1004000c141000103501c100801e07507034130551440480e40c11070300040c1d8030038442c00400d00c009500c0827000700114000007404440d40c1c056002500302c3c1c0c040d0b640c0c0301c2c07880440b0680c456008020745e100e80050340180b00c14030045030304281003004445d00d0f007000c1400c0c501d40d0f03031114181a4126213484c042844128074003c202c00c18014212841d651150810280c1c500c460074002c0248880c030052f80d03d6035242503407410345025032040d001610616110b00d454990b82d140070340e680c0c5d00450f41145c4102c1403190 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 196976196 1250 196974946 196974949
    0x20901031404080d0e070807080f060f0739030216050402070b01050f01020f0f0c0a152304050d060507020c18040305031302060d050106110a080d0b06040b031311 71
    0x80500540d80040e0f040e1820a82d0080d050213800c049402c0c0d00300d030003a40c80010707060b141044aa0010400c3d50b0151000ca400001d0300703030811400070001c0804902d510300f0041c0c0c80d517000300c046c2c8172030300c090071140c51000281c110720078800580240600e040c04220850303c14584c000500b10a0b10312010800000e194607901400b0590140b050010032401d1114014412807500012400d901d0300c040c81200c0604c041405c0080c9841e440000b01c031107a403c036a41c0c01415003030a0b0340c0345000d40b0b012a500b4100c114004401071969000c41940c40103162460080191003c1c403c0482d4010100103014100450a60402400500f015601c545c050700c11010350040342d003005501c1192502849142c03501ca0b40e21a00c1c166040d41c00200485072510541d444100182d03036a50281c02004440100010950704106025156000d0f0f040c02085c0ca9009612134000214040204e031041e042c801004101d50340360030b01007001d5019036040080800404000c01261260301c04018010707500404130100320442c03940 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 196977446 1250 196976196 196976231
    0xf09030e03060c0a080606070f082d0306011209030e181905010f03060b13050906071409032a030609030a02011a13050402010917070305013c020706050a02090103 71
    0x41e00310005c9100d100000d941031620724041d100d2240100c29240400490340d032600c0d003603032004010070340790072035030001080b140c41011a002c1112580c403101443d505042002810042d0701119990115450341d90340d804052142c96503000d420700241681e0b10341802d591055200110459030304a0850440111402c5041e203409418100c890701104030101038103648448010704400420603820007000686800c0800407846442c0c03003500401c011f06101e0502d0309008007038101000380100c111b0024040748486030b40c0400d070540003103000110912040e00300460300e0f81245071031b03154640c0f500170803041110aa102100400200c10785a0013000f000d1908180403080313520300c0701d80a801248808528003610815485150041d005040458030b982d6a000020101001100e042480d504089d0041040060900500341d00c81c00d01c0034008c1c030260785d6841d0316041c010f00104081c018920420011007081855048981140e0400340c24061441c040684402950050405a0000389810003001a10042c071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 196978696 1250 196977446 196977457
    0xe1b0301061401120e0313140102010b01050d0c09080307060615080403050403060506060c01060803041a18061c0911010f03020705210c01090c0302040b06040b0405060703030f09030e03060c 83
    0x1042d100d44034684100c01103030916002043da0000079611044080301900400151015401c032035450761413142044664104440c4440c000c9055a0600d900b15842d681c0100584403405807645001482480096007142c0e07081180d8800da46034000091003c0a100040d0064010341c1c0e10300e83ca01d07180d480004001c030384510040701c0142c000b0382c0c140001d0000590076001107070802c600819050500c9034a007009821541d65910500390750b40700040c2008000f0103030303842e08018100c00740418144020121075184002801000d44d104081c0000c0507494400c2c0c0010074402080c410764100880f05152600198400c903422007035021415028000c0c1550b4428000c40b940300c0d6000d4040c1500c01406050740102000e07a0741c034180210700510070b00882e071a09102da1403a050090380ca00f1070061070350050208560f10070741101d025042c100f01c188051268075003102e003203400945000e5640c18032400e0403002001d0944880c9103490801c4c40b40e50506174001c1b803105209a00310103840c19515808800300c4580300741c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 196979946 1250 196978696 196978709
    0x61b0c1b0f030f1124030a1b0c03080105010306030c12061107121403070e0d051c0302030105040501050d170a1e030209100305070215250809010c0309031b020d060e1b030106 76
    0x3510101c0382d056410101440d0021f40502012490407024200400c2c3c0200ca03110070740c00988258408814154010300090041c1030a0074100800c82c00c6890f140a0406103028407608030b16030302205801c00405500440c3c1d00c200c05d4007500d4a0301d4862400d004100c0d42c502d4220001451001d04103010304d1018100c901510164881820f030269801c2840703044000d615040c0c034540038941d2400c046180c0c84410154125161b500142ea03981058200802c445060b0011401030f4102c05400001940c900e50003215441c4082c952034540d01d1304142128105035240b0b5214030320803141854a41c403905a00603129407502204c0303402c10840e803458220101c6500312011030042e4041e903985010348104c085c50f039801c00c40310307c80c030f5488060004240d40d0700c0c030050a0220000d0a41410040c0c03180081c45096418001407030103005041d0503890003004031502103401920380c030141035004215521002460030303183c0d100034184a807500c0c050100c2d0715070710480c0710304101c040400d5000099240601c1003000b035802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 196981196 1250 196979946 196979989
    0x60103031d0f0901090c0c140a02031905030a1d04110703080703090b0c18090f0702060f0c0921060a02090114040803180625061b0c1b0f030f11 63
    0x3070400100090006c409092081c1310034071784804003042200351000a494400c900078803189800e0310500d490890315840e5074644a01c100417103c000360300441100c181148501d803ca0f82a5584d0106c110b1240c41518202e0b030280c5800d507800100361006010305100c078044c3c6c0707440c1001e581d00601901615a00c01d0b004100c0d0404000042035804800040e100882c4030314015202161201d01003450700d0000e0381c09841c00c01c1c80c0c3d020017044a07410010950b0082d007100000ca00750410101e200c501c0d0003910348541c0305280000d44100c0140c070748400310a12031002030880760170b4108401c00c40e009510000c50f01e800100008608109403004004850813640c0d03a80c000c51801040030351034005a68003103040e6a000c7c4d000c01c215000c5070841e2034100543d4040c5298102408007500d003942c12505948590105541d400c02c4800c4140c2c1c002c84d050200399085402d80031a00481c14004140b498141c0000c80150401c04010051041c60821042030510440500d07502c0b0000d102049902590040c8880b217040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 196982446 1250 196981196 196981199
    0x6010507030e130906090605040c0b0c0312180312010f050a0503033c0409140112030806012006090f0109241506030e0106050109180203040c08060103031d0f0901 71
    0x1041041410225001e4000141c070130f055684503030644c0c3e1000015600980c0300d000740400e0055000101006051060041d0710f41042001c0f00d43d12805003004981032064008001183c21944224507012040f03410300b942e594440302c0c200070f01032101c00c0c000d0a20b45000804045200c2c144200c10000303941d4010700850812002d4500180585840f8400300300006941d24443c51101344150300d44000c0d10300c680040d8640d401d00d048e00301224010250002c03224544401000f0001a007d094000300f501850490115514200140c40310801c0e044007001110407282010f045c14804962540580040016071f2907500b10800030350300b662498903020700021512401469801124030002d080c8003600340c0046580090101040b401051a0380070700e0120b51285141c0c1c202640078031580340540408d0070800d21040c105201660701441040308203101c3c99000001c035040c03004501d203450051001c00221400c541e124503005000c4018401c1e414010342180a1040840c504140303500e810031000741001c04147e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 196983696 1250 196982446 196982449
    0x60c02010506030313170f030a020706080c030f04020103020c12030a0b030606030304080304051002070e01060302040504052a090d0209130c0801050112030f0e04060603021b060903070305031f080d0806010507030e 93
    0x100d86c0e8262402e1080e080c1004440e003080c40135000050760754010345030b210300d0303c03a0242400f40700518980210381d0410421547c400300802e0300ea04290217190051300c07030241a601900c0c100000071511600b800c04820088403950036000584034070026819070301c070303512598141580c0c0d02603401000c40da42c000384400c1c4810b0810580340b181d4035400b4070403102d846070303660180ea051180c2a080000065000901800141424040e09400c181e41d0003d1082070481c1503008103903d900f00c0d4840e00c0a0b40000754865180da240014074290079002020092903080c40880c1d050940e00545040710031003043b440008654a062146504071104007403180c5c21100702d503070101c91451040c2284014401c007003000d07024580311407003944060580d98800580d14608840c1072101042e20301ca5400c01548240100f000801010050340c150b40c1c0e160404513142e4803010240b04044121180005004509200019500000281c0345e500003602e82c0362a811074550703200459081c03082900c003030f0102da100101b00885 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 196984946 1250 196983696 196983719
    0x60806072c040b010909020708030709060507020306061504080313090c170f0a060b190908010218040908071509120c020108040f0c05031002041508131403090409060c02010506030313 80
    0xb11405241210155884403080d0007248c20500c000e650000c0301108000109400100d05c1c4003400e07442c14510305188065000950703c1a009001901902c65015944d0507172a101d419079025150040c20f480e1500c207400c105120104641c400c0c10801c0e4241118283c4050240305500212154110340300c8181c0d4580b802c0a2000e2070103030004203903a541b40700010340004503002030b191400140d46180f0b01d2035042440100301000c00e030061107003648108030220b0f20030074040030f000c085a4103a80c082100c002c641410034075401403040c0034000b160100d05010401c03106a000d0b100091280980d41f02c6284070b8081120802c90441c0003e0116030020081070104484111031800c081c464004920b03459203910200381040724000103101c4141c0c01003000e110301002980001c003002d40761300e803802442c51b148a2401d015041900041c150300f00100f00221070702c0302402103d6026401070000d0219000524122004121104603100107528000110b000c5250210480e042c14404080c040400750414808406 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 196986196 1250 196984946 196984961
    0x50304111516034d100e01140c250210030209030715260723040506070b150405060108070f020703051005070f0206060109060503090c04060806072c04 66
    0x9229070713024144206011404e11070f0f808408091880c5020f0b42001005440710419040321803482d0044007440c02c211000030b000407402c5442ca074085445030303c00c000c1c14010305443d0400d01200d143c18007008108501c803401000c2c50508580b01c1080c0b1440303a440100c01d070300c1c9808000d41c4103080400d09500d851094001d0800d44800405840d1110fa403080c62902580c00c01351641d000c41c0355481c1520f080c0c0f4103c4480381c080080006094901d140840c4020025280e02400000d151003601c240704148041c0b8060317501034000608101d40c0e4490904002c6114641190b000d124000d03058859503850a180c000e207806207606031526032003601d4481068900d920340f00c0040741144600c840020102c0e9003007017409403e0650400c005482d081546c00107111210360071194003907600050601c40c1d6030740c4c40400c40d012a62a40780958903900d441103020b0420611001c869407082c1004000b182901011500d41d000c3d610341d48a0505503030f18016506100140c2105180c0716003280030f44a805400c2031707044a10b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 196987446 1250 196986196 196986203
    0xf0912030403122708011b03060e0103080c0f030c0115090b01081504090206070f050105011e050603180a06140106090f17030c03030a06050103051e07120e0706050304111516 76
    0x148180002d20000412001d5100b0301150703443d07c130015101000f1803451582401f0300e2809000302c0742080c0070540d02c00310622000307202502c00100004d8064040c01001c10240a00080d40e07543c20790542c4041c080c00182c0c1e0020006401c0c1400058a100c1c28826520048410385480402d540c030703100724088140c201c501d039036001501c41d801c41006940c1c7e4001803a200c2d100b9800b120b80c0b2941d50401030300b16075058000d07401e0848104420b82515070f042e24038034111003046400e02e69940d107241c840307101d110340c80a58850301e10035115010b0401000303410000c044804900341c3c1032580e0340c1c3c400480d40c8116510508030380e03884810341030258109110640a0400300001100c1c03911060003021071455204070b44101007140d07070b035400348099a414082c076500a180084808041e02000110390300d4040c018114109205000401119030b01c40d80d00203000c18130210003650038940d030b2410b024080e0340c400c507802c035416101113032640c2e05850581d1561000390a0440ea65040c0080614108942c1e42c8903082034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 196988696 1250 196987446 196987487
    0x3211d010f120c20010903090905070306122f06270901031505010801050403080f0604110d020a090f03230a06060909030201050703360204020f091203040312 69
    0x5502d801c91500035000b500400e83d507100008040c45240c000704545440c445503076a410420300b603001c258000d09001c240c600c1603400054945038200c040d0f0040106921101c180c46007924031030300f4004541e4081607603c0105a10140c5108200c0c1c10070907040404506981c0450207001440c0340c0450191040780004490400b407141d2864a00013450b0f081c0b09034412192003882c880344054030303c140d000301801001c11400074891780c1020354019240e81c2c401452045040d5143c00020b290b55503507041500c501c01c100e02959503d002d07402e00303140654412403036240480c0c0350030300c001003070914441844110717500301e4281c101910110030041020075000b008050340d0b1003800c009002050a41c49000000c12205000140c807030032900c0d0182c02d484000300160107040c50318404081040c204072040500040080b0b00398aa0080c42520012080c0c080102940051011a092130209001c0c1d00070b10f0201030845405004441003111155248650700000782100b0f543d55880d2170060180d400c516464a44c100384 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 196989946 1250 196988696 196988717
    0x1230111030d020c100614010806030a140f010c080c030112150606170606161401090b040602130807031203020906190305010311060909060d08090a03211d010f 70
    0x109241d42c220314100051a81d00165510010904215059180941c640103108880c544882003170b02c4500803494505010842000844a40d02803240c1881141d00c524403582100040e421550350b00d400b01c0c03c0c0c507101d6103010160701e20f0b00d0081e040300e8424024210298656824062040c0d030803042c601085030110a02c58401d4800701d111701a4a018002075a680c8101c2504540000072186000c1e1007140a864100407401e592002c1c40003c184a54015034007586c2821034509160040800960203018240d41c00c06000400010303800034061a05240d6020a000f40ca480c0ca0a4407502c0c42d110080401d400034081545c20380c02030700a0a90150700034615403c283c1d2001810342258003070f44450300000e554070018002c0048400c043c0c000480103130b80207424095604085115028007400341d070f11940e0b0f4551321604001d002c80441c2d0220310050400f03008030b5501d207884d50840581611800660401c43d00c9150b1061107010500300a541c1b08074030302c101e0404040103503400e4403495400c1e01007003000e080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 196991196 1250 196989946 196989977
    0x2160f02061207050919080a06090302030906070c0306060812071202072106050f07050a1101022802010e010207020d06090c050a0b0c0c0a050109031e052d0105012301 73
    0xb09548200074a860303807070351881444104000384468031001c003030001c00a0b205101c0203200181c104103207948181d000502c5115418281e00d98011f032045e50743d003d00001550000c01824041c3e900484c1d00ca50f00a0141644a448032910b5583c81903d03a001ca4400788881008a00c005184142d403a074179006840713041d603c0b1000010255044074a604d00704056070620710070804144115640018401e0360b01201f0305003080002c0080c40b40707041c40020000c015180066400f000e50403111450304401c0101e090100b40e900805104610144d108059441d00700e18291500301030007111078403580200096110000c0781c1d90a0300820359840191042d610143c1c0c045142c0d1650314070840940045061141c58940d540c095901c2e129084401d1800303000e00c1c000c10496a60801c0889050b20760201e00081c008036450100070004807040c01c041d081d8481c0c8068803450303201c00b444002c50002814661845644440009400e1b00c40a11a000070041c0564400f00c05284011012921000501d080e5418805420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 196992446 1250 196991196 196991227
    0x60904030513030f08030708070201110f0703031d010902130c080a0f090f05030301050a0609030c06110f0d0905010905010e0f15092805010f020616050903062802160f0206 75
    0x98101d1744000c0c00000d0001c0705401400c03840c1d02010034402804174541c030509a2a01c0d000e00b40c1c000c55804008240f010405000b6000390703174641150f0701800d116541d00d0961130b01802d4954000d80c0030b41a01d0551120b07503034840c0a0b01c0c0000c04c807a1100342c880e0316210f040500030315075402c0039002e00d0b0340c40049000085c00b06a10a40c6503000e003006540f00e50404003000050201980150103210300303904108000b4194032412801c9401e2400c00320100c2845010f103505207028412013403460702407400c458a15642192403070040d94000c2c0e0383c0700c10686c5c54400540311501d071702c2507140d8820400303200034603545007001c540032020104442e0f0a050860400c04030b10781c0c990b82d0fa505078940b1010705140c40c83d0f02d900c00021006080c2480e0000401128a1000e500c0f000d01401400090503006000c130040b6002e5411500507007400340031200036252600c15040d00600010801401005961148848407160300a88401058640340e0300461603640e034a407a2040320982c000c98000c601440b03198800e25945 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 196993696 1250 196992446 196992473
    0x112060f0c09050306010909150f1e0606020c0105041d04031206030f050c03030f030f100b0408060a050a060b0f1b0601060c1401150302060717030709030204060e06090403051303 78
    0x2074580c19002c0e07051108060a0460580042d1541c0349000c1640c00404d0501e00000b0000c3c51140001401280031040c0070b010b064042824003640912800f131000400c81d42d0702400441c1c0c955425a02103500300401118140303d280301c1c21044080c00790003007507121000c0803030a0b00180300b0304009500060720b251f10000c2c2d80c1c00f54000d07606100206d04200034050288905508002c00300d014500d8201503403510140350201825482c03100c280100007035500b899030340495000c4c0040304800e5031596511601c040d40da150031036044120782e0501000c100d00c04c909000d40f60554a00251042c00c060803018404195003200320149003051240c0c0e00901090b00901000f4007804069448200e0012076062103e030341d054010000c0b415a14040d102c03040100360f40440c80980380d044603450398030001e03400c2281c2614401140394501c1d0000005000d034280c1c001c600b22003181e00c292030500c20f6070385d01c45607201ca15108440040d04118840c00041c00a4410310090092a249000c0110031035100c1d299000b081591 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 196994946 1250 196993696 196993721
    0x20c0901091a04050f0420090c040305011404021513150207030221060c0702010507020315161403010b0a02100507030b0a0b090114180d05160f0e0112060f 68
    0x442400340c0c900410641c10b100d00703000c2a2814440d9003002007401540d03990060000e0410b44038050300f1403803c0109180c01900700c0d4002c104520300d0409402101466000d03100459103503191103ca00071103500a80464400c5400405030111a010780e44a074003941e001e805990030f042450240800d00c420703640200c00a400080c0d008103055030951051141c0c041e2000503003201401e91034645070300c00710000740907640b110640c501d690f2a05002e00c0140e80078020703140002c0d458000e428200010f03c03003c4e040548580f00d241000c03001a00b40307140c29510107002402058444008100610081d60420010035190f0801e204903400070040d52140800c541003070b1600000a40c031842e010318a840d240c1180c002400b450301f41c01d8940682280081d10900c0650540e0302402e07008903e07241208022881c2150090000e044408840c2480c84d043e92540a04102c108000f03000e2500842d1030f1103c440420107503801c400b180803d0340d0034940d045600c0c16209008807820703a1604011034000c001401851340d0000d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 196996196 1250 196994946 196994951
    0x110601090e06010f0f09020904020d0e0105090d05090a170a23010506010527120d0309140307030f180b120412051e0706020904020c030a030c0207050916020c090109 72
    0x805201d0a41440c4040e030096880840c4031505220b03a4400d20030741c20031640d02000060b514645c800c04a0064061480d21200c654507003064000c645006402007485014503030182c404881000710155950b0066481c0070341c00c001807030000e00c00c1d444000403108922280c40704940b11891503a072484000f103a225044404121114110580c18000f40565600b0800900306941030001e081010500400c0c0c0303203d544650215074034181d903652691a090011a00e2083c00d9030701346030070510b0290141c162060304543c00c0003810a80c244100d004000c0e104146d40c076940e00c5100010f018030031035580074412840e85040e441100009407003c41800202000b240b200000c48552803c1d0a0090000d5139507400c640520404000a00d12009200c0992482c422912010340d00e8400e942019002801070388a0150410300c0000c80d00c422960000184c001140a59030600c00d04203041030403611855940b00303264000881602144100402c14428455601d07140b0444070305040c8000010f1181000307030300c038809295 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 196997446 1250 196996196 196996211
    0x60207080c0109151a0d03080601030e01060f1d060918030903100c080907030804061412010e01030209180604030804020d0c0303050903070603020c061503120301230d03120203060111060109 83
    0x11250080c5c0c0e01c1d5aa641940564600b1000c0c0411868081414000c0402c43d070400001c13200e070f000b0303441000c900d007c040003041425142c1621669115080c0034089031070340000700b110401a03211303100921804028160242540301c40c42445074030342e0a0100070b0340e940401d1041042c192000c001800128202102c0491440e44029026010050252280d40150800705041c0007042e94203040741c0459016103402000401429400015802108000700d00c1000d10360000400442c0840f149041c0c0b80201c0b10b01006855041d02100d0400d4a104c9110860300500c0008001c00e0141e20740711b03401800985140e10007140d6035141481c10501d0380088001c600003080c0d0000c42c4c00c0c2008000040c251500b002c502d4044c4040800b40c1c1e400c4014031728540e01c058001e004041c1c3d1420b110300340c003c0c0102c20a298803940c540e02a011400c01c804100e152480900101ca41c051030b04180131841250148c032030420300080d070036540b0040e500040c20a41070000c03189181c09018000c00c046402890640000101c80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 196998696 1250 196997446 196997483
    0x806040f0b07020a0f150b09060d030e0604080114070e1210050a060308030907080f0c03120318030a0c170a0804030e0a05030d1107060c0203071e0906060509120316060207080c0109 79
    0x113464400047c0e00403041d0300100445600c0d94014440100c0c0c040c01c0002c50a000540003a82500c10384d00081ba16500b40340e8642c07240c1c008202c5042c02641c10381c460800c52000072007446444040c40c400009184c1c0311240d580c03581142a0b1000350000c18400010407440d4507600d40000c60340c41070b1001c100c0d91740164010003154800380300301e20141208202401c02c9007034101c00290744100000c1c01043c0410008040340103507100403019586064010b00340c03620307403526180240c5503000c00304003510303120140c5010300d0416914004980445900761544807040d100c1f601d044030481d0040c0055a000071030000082038968003000307201d1080d24030b0307038070f405400c00305d80400c505000542e400300702406502c49504005035804100502928140c102007017140050f148201c211402d5940074510880c50070901188880c0d100008210400042c0c1d400d804100340d50340030075900c0c42001480308a4408892107200040c3c1141c000b08070f102d000346881801e04480d901c901c0d0840f446000201e030111400340403c0f0b190b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 196999946 1250 196998696 196998701
    0x2010f0207111311120903090405070215100b040608130c08070519050108061e1804020405091501050607030e0303040603020912060c03070f021c0801060201060806040f0b07020a0f15 80
    0xc1c1c803403c0c08148100d40c41050340f18000c0c0a4030002c91405003558002654001c1d080007a9400301d04003c0040c415801c044c40080d4486980c000445014440034000452a00e042c0c28103104a42003105031611b010f14150f0100ca180202408000d10941b0045100c40070039046401400513020110183c61400c1ca08410070031418011805200314200c0c03901c042019a0f00491182c0e817040e01a0341803000c100640b0724072a0000c5204028640c03007400e110294038030101141289104900c00e0300e040103030380c407034440d000e40d1410030010620714a1030040c01071016040003c060440e01b0301c6410f0160b9508032180c00a41542c005802100000e640800c1806030340c90501d0140d41e105c00340001070051400c14890100700d503c8010a05414040794400e10340c415407080040c01554074080c2000c0d056600e50040c018086075080c4100e800560910001144202020400f40d000701d42c0400c2c0098040344076950009129001041941980204481030b40850701181c41144400c1c4030703450740c0d240d104080d1803001c01c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 197001196 1250 196999946 196999969
    0x15050405070c1505060301150503030a0305040201050f0a021b06090d030e030f0105090d17070503010302010503040206070609030804020a0801062405040e011d160e0d02040f14060a060203070803070e0102010f020711 94
    0x100c0c0c1d03444104200c0c3e40c40100c10cc0d1110340980c9030100d00b50b074403400140c0d082e10030000c6044824200140480c82c1560208900b401e040a422401e54402d011408000d001d008203809540c0c0301001e009411b0000780161544014800090290341880701501c00007401c640046502004640000840c00c0461b40c1c000380143d8a6100c1e0b556210490405e00707401401ca0005005c000d0620200001240030b40d0b5444c01641c14003a403280050042d01800d01e0300a003900350586040740190114580801d0b4800d060041c2415204410031518188040f5205000700c141d40382039010a10508001c08113a12518070081c901074003070612244400080071150500d03c810080c04801140780030303240e000c5400d5010061400e003071401c50b0340d01800c034070500026006100d10406030009a1810001c070151552455403184100b10844a101c2c0c411342e1900183c3c0c480c803411400070a9148208001905580a040700314204001880001500740c0d000204404980c0010000e8a42a45012090116140007030b0200f4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 197002446 1250 197001196 197001221
    0x702011523030a0b0f040204090f0f0303060b03190908040e0108060115020c06090103090302010605061b1006050616060603051e0f2a010302210f01080115050405070c1505060301 78
    0x10f40c1000354440b005080005010358080c1d041910208040d0354481d080b1421982e000007042c581a85035142404100b521240200c0220b41012000141070788440c055902c5060403074280040940144030304d00040008200403103004d4410700c000b0981140e485140e034080c000480041c80154145030060b0a090f0802c0101c5045501c00403080303070940c5500c01501c0280c4001e0134049030b490306600d8140e000d007100760801d6822076000300307425001e17440c01020f0300c500c9410071054404000c41002e000e01503840314000c442c0c01000802460841d003c1000a5400050055000080c0c194a030b41c0c500e41098001050070550110300304901340c8095051050011a503c850010010086014105101c1e00b0002c49800c2d030a2301c10500d5800564080e4040380c03003078050284001c42203c03810713000600c002002d880c0d400d007981d4020008110480144511169820030207a03040205140004201c00780c40010540f03410002c1c071b0782908000071007400b0021306295100c1070100c0d00c2d140c490305040c00c48a9a40405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 197003696 1250 197002446 197002453
    0x18030c0b0406080a2a020a060e010219031503030c080708070503030f371d10050702070e060f0109030b09010509010c02071a09010905060409020705160815070201152303 74
    0x40003482d140310104070101a406038405071764500310360603401e113805160301419241c14140c0d040c20300d00040d4010080000f4011081d40c20b0441c80400710102d80d031072942c191750412110b0b0b0610220b805598080d07540c0c1d10846503203103444100e555031103c5800880c002c4659510100600c8100c4200114a9a008602980e900300f451801d940302c00f2061004404451212400007030344582c07443c90b0700000803400210303090051a0f1408003180c0c3d07403518031a42c210304d0146482c0101e42418400f03d6403d08681d6000070580322138446004115511610f96400c03030600048400002c000b40d0400a0544185e491b10300000311460180e14450a607030800616008540010005000400410ba84000d0b04450b55861a44030054840103980c1c0705030581100da800070001c20002196072032a0003c10340d0a07c036400342c030354000d012403c4480a0025000e00e04454102c03950480704029401c200580c0903401e0f1001040d01154269401c02082c0030380c21005510720011003150b442c420440c02e8a40364142138004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 197004946 1250 197003696 197003711
    0x18060109050616020f031c050301030b0c13141f051e0a020a060b1504080d09091e0509010617010f061a030708090a06050f150406050105030718030c0b0406080a 70
    0x2005002001443c3c028440c0441c0040c1c00301a440401c858480b43d0200071900090303460540d0040c0450f00300b4401150700d0340314603000620740b00c0c0620a0715403c010601c06078020340e040c40c82c151200864040f2140e00400d92002c42942c4140c4214090446102500d445650b9101404d60b2426030800c0d01c660084403d0070000407451950006030112881c0d000540000c42d0440c143c00202010504046400700072000305010843e24008079110f843d83c140b9890340c48040d590740f0002c0d070580d4205003455540404144115808000e40e4026aa00440301000061500d89030075900808001004641e94243e54a240340d00c69912948107600103040382d0040b441c1c040410756100541407100070110410007841001040092008108008280754801c1050180b41b408600030300c01400101c80104110b130000c0814001400c20b032180c0c8040c0c45040c0d44451466440c10015034101d440441d40d5800100508000404a03000010702d0340501001e1424540e1f50f0315141c0005c1480d036010b88500c500c949001c56 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 197006196 1250 197004946 197004967
    0x1020a0b061905032e1406061812101103010e010306090f05060705120606070201120507050409090b100b0c0703020409060e161802040f090b060405180601090506 71
    0x40964000411038428107510810600c80714042d80b1540074603090320610919000c200703040100030b8054000d880502c8509102e4090310310665a000000c0003003000200302160250801e4001008000500307204114010b442d9004114400c0b030f00d6200d80050340041c0351040300d03242e0038043e444141d550072001c4c0741554100b040c0030800d220184401802555a400f02071708000300c05004004190304401a1482841c0c04607000d0942c0e44003000344125031400d400000c50300d2424000359a40540c0694500f600c05c41c401e80c44000a001c060070010a00200340300000e00b00c1880d0140070962880303651900100d0901000300030210345680c210403000041405501b040b40000101e00084a804032004207028a007030030800010705884056070014041c201c3d800070b0f80300309100d8450407100000d0211072200c1c041001e10089002d24006c3d80c0c031900407640304002c000d4140e00030310304101c4000d140d6440c1c955101d00244140c1c042c142d40c440d07000841c0d4200851503030052018002414143d5141345840a400c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 197007446 1250 197006196 197006213
    0x9031205040e06060d230105101706101107090e0f0705030a0303022d03060a0b0a05070308190501080f0708010c0c120903240e0c0108011203140f0406030b01020a 71
    0x20030a0b80200c0c408544140d1007980c41c1c00a01c1e0f1b40074a251036140c602010f241401079080c0c00d0243d9402000f80200c403050040c4209500803844042d0f0284042507142d882c01c004800f01d04440070390030400c07031200e9210110800d1040130010030b0500c0740024030341c6549400d0760600c4030101c035843c1c83d90000f281c1013001da00c0201c0da00742c2069052030010380c0d031038a0021201e0b001e00d9107408500c03140742190003c207100700140c0041d4010700c001c8448480c026911b0074942c4a6103c1c140214000420902c00a40064000c0c0e405a0b002001c20400c8045100a641c0d40c0d0101c4100341d100e811030707902c81113070500140010301401014050010090051300410200a410190301c203000410036465611140d804a2248200d9006903a109401d16a02e04450052441c1c000800051880b1203281c0140307044010400541d4000f040720603140e1443d01c0c0e00c0e200b051a01140c004802307505200804200744084140d01c17000b041814540c000c556100c6041900c010200d48000841d24199440800c01c1070110b400304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 197008696 1250 197007446 197007451
    0x60a0c050c100c170c07090c0206090a02130b04020403020310090b0907050105040b091f05030a0b060702090a0c12060905010311030619020c19050304050f180103020d1e0309031205040e 81
    0x241131140030201000d00c415a20400040400c80d0203080400b00d01c901c0a50401c044000e41a42112070f251141d00e05a07881b10720a4a00a5001c114081a4440316200380c10509080344010401410329a603a008241000c4001004072030036a40c4010042c100060701c54016040f1280c0c00003486018100341c00648148118014020781e41c0010410320b03902c2e0f85040e080092a101d09512850403000f10b40060315540054030030048050920300b4201450801500f903604085c1c0050ae0210541c6903080e0700e0000704040b4001d8010404602401410308a19005843c02001000c400260740d40c5141011841c59480807090761090708031409011510b040300300c1c1d900c81940c41001c0143c2e01d11940d4812450a0554180c050110a00701c00481c2484808400760007241c4080d58001c107841804010041890414000000324160400051000d0700b070001100b402c1d544a1203083d000449507103520802c401c1011011070000d10001c0d0144204841c41440640f040c01600702a400c0c217050544e00d14044800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 197009946 1250 197008696 197008703
    0x20601140d0f02060706060602010c0e03031e0708030f06010305010b0307021506030c031501090b100207031101031103010b07051006150e0a0b0c030a02010e03030402220b060a0c050c100c 82
    0x503601c960180075079030400901c11070303005010903900c1c0b0705403501001803e0a4800c40e40954a0090007419090084a944185080003406580740160f528a40003e41e0800c85a075290b40b05d0900c8500002840c010095015041c0e020300300155141040c00182580c00581081020402c28018050301d15000196084500035030300b1400c0c4169103000119140c099500340c00d552600c0b601c5a44c00c180f9850010f0f9034161006a2001e0007400007032424065103480003100c1c000142d101c103000704041450000408004e000503d40800c1403e00e000441290350400c1e0450b004c065800603103101040001c000700603001019082c28001e45241646542071040c128407580180030b00c08141082c3ca0351024048809040c0c3c40301d1b9551246440d542c0d0036907030303040012070b08055860300724a03028030030700081a02c0c0b040d40c1c01020759080c1807805407560850013107202c61301e00203901d5508040c2240d450f280a40a0501207554146501c0c4207414000d14250410300c0481c00340080d102007810b001d60000711104e00581 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 197011196 1250 197009946 197009959
    0x50c0f070f031e030c181d0c0409090b062106061c06020406081f03200103021c050a0f090f08030c130e070807021501031506051305061002060114 64
    0x1402c09859541c0d5030b403620126500d4100c05045482c0e0140d014800c80c0c44940d48800c00101041c200d001c840703c3d80c5c050301125644c07043c4058007040182d50851b906c100c1c4440ca040c10320303641d581160240d800b8184101d454900801c00c11005041175007515a204070030b034010030242c224070000c07180c450f00c000e0b10550250712074113551140303221821035642416078001070440d0f517940c0e11900109080402e0b10a00c0c1c5642560b503107030040242c400100b40c02c1c0d03034100c404020854100803a0064150f0043c001505047d002c2c06140d50805681c0020071501144100c0400c2070f140c001908021a08126401c01c0c905107040f414101285200c10b94030103e9600144083c0d403072f00c401c409140940030b201100002c00d8100400841d04401200c0824002d50264456451075140c07503205036106c0004480107420055003000420204100c1d0810810030010900e0010742c168039680482d040c9070310800545116610f58003402014240f1031058407410b0054806003019505003c1807403003090200d40864800d88 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 197012446 1250 197011196 197011223
    0xc0f020603100b030a090302011d030315012f0c03210306040603020603010303031b03020c210409020a030219020a02011b1502070f1104110703080a0209031e01050c0f07 74
    0x7800c00c40b41c40900949802d481d200d01c0c040001c04081c110b080c00840055003800e4a200d22a198000c041451407400c40103182585c3da040020045100780341050b034104401e40c003900e10a03400d00e49220220754005140a2a000503030141030b4139045111039420700a502152224505000c094100d6143d02c2900584a40d80c0d103850001a0240040b500b001c0d500c00000000001003640580c448882002e18106440c880100d10b102a8120300078004407022503000300241a006561080a0b9010181360b0405a410161508428000c03070300480d82180109600040a11854030340644581c00562544014208102d039070f03000a09044400404001c1d5001d40041d005c00c010a0800300610105143d40c11911015107003000122900c60002c151ba558109034376407103150400d4098001c0000c3c00e0b00b400e91405000d0340e0101c454590041180c1c0c5019800e20205003243e0b818000e503043c03a50b100c84540e50600d481090b982c03c4500141c8441c0e4803410800c6150b0080e481c220903640800d4021082e810b000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 197013696 1250 197012446 197012461
    0x60108100807030803190c05070b01050405100e07120c033801110a082b0e0d0e0a080f07030c090b0a050609061c0203010815130605060d080a08070f0c0f020603 70
    0x82091082541c6c2e80f81003100c821440c0740d00c00c010305201c601034120042e031640c0e0b40003400101d81050f034815072044076209051008441e0701024907001001c625118051061503c0c025048500c4070868000181d02c5500d200c405140d100e910210b00b0002000c550304e000c43d410440d500040300c2d000f401d4188040d040c0e849407044030902c0301c902c40b1900110002c1c0c0e20740c003016180d035031910328402403102008880c20422408141c4c0c0304802520071034500070078020281d01415100014001c1d0f41940c40865000702081c800021b001e8101c82640d040c0050184500b9480c20540f4050180c11450406181004243c20343c3e4400c50030741e044070000c1c1c036060b981e131200d50082800e521640900c0c5209400522042c0103200c1558002c50480300c401e400d45020140f18000130b0341c626010b84800314a1000c0c1c3c83c1100100f0911f901c0250058801420089803240d60764462a9a8110a4214010443c440200010b594121074030350a180e08a00e40305502c004940d0300d802000015140c041c0c000c1c0c50200000b0b40c40d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 197014946 1250 197013696 197013721
    0x601030c120906020a031d0c091302030115030b07020d21141305010c05070c0515040f0b07050d090501020a1202070503030c1b040507080a0b040f1103060108100807030803 75
    0x20800e81d1030180301021807400e109010317520050100d0002481c0410000a01007500c1282c00c140410b00c0203003181701442410024080c1e405800e50910440301082c1500581d000d124040704140012201c505042c59070030034031600000240b404d02550000300585c002076600140054101c485041200c0200980502aa0007000201846440081448140310310a020309090354140d901c500000c0c032000003006411074144c080c40c40010a1610880024409450520341d0408440505807030103051642e904805040c01c25070743c0c05040c102000007682400c1c4002031004000701201400c2c44103415140800003566081c60000203040340345221903141c0f007144280b21010042c036000b030460b5100e6104110b655100e03000c080040603400c481b8445101c003400d007401218481c400075144c0d900c3c01c0e035a40b8200c0d0083e040c005c0e15181e0155841107000d1041c0b80c50b02c00d548110134612321042d220325144e4005800c03071901902d0310101c410b51950030400464005656000c3d20f50144245071281c03a00d008041c81c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 197016196 1250 197014946 197014967
    0x12040602071203090c0605040f0504020702030a0b13170a080117070512070611060919060f11030411010305010b0f0d06050307060302070b070905030a06020c1608010b040b0312030601030c 82
    0x840b00c034071111002c9581600246000c80c01440d00415a6540c0c00007919907108178801c25010302e43d80f080c02c09c903d00d0b040c2d02500d821400601500c1800c82c6c103948171030603208111a4409084038182100c400d00449072200c040342c481c07400a252903c002010080c1c00700405104803080701c44c0d494198010303000180544002003070003403c1d01c0550046d81d0a50f644032041c9018001c0000e1021034a03030f01c40f03040080d00d580107043c5107003e460310300900c00050b0581c226a4000b9940941c449494000804440c8940300200c45c41c414040c0e181d09151414030b20010644028604060800005000c06140780c41221a00c3c0c8001090300d684c2c000398124071014100c1c03540200d0b4140192500060140c0d0140c0060201904c41c0425015607a0f4081c019142d840c0319004094142e8020580d500000380594020b00708000c406049075244d99841c10786104484c006d4205540c165140c1c070100505040c2400380c41c0c0340340002c80c00790a880050803001c500a00005040c1c50416807148050403180303026030310190 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 197017446 1250 197016196 197016203
    0xc0706060e010501021005060904081b1209040606030507021b21011a0a0803030a020a090b131a1806070305070203030d022d0307140c0f010f0b0f061204060207 70
    0x5060707681e80300552030356000d00c5841e000d03002ea080c100a2252462155038401e100c01012131869488a0300e420a1640211039081b0030141d105040c105111000c0103126241402c0c2c84046035a030002400740000c3d00c0c1030380d200d14241410041808509034001c070f40e40f0280c4501080780c440074980708000403141c0302a8a481c0305a054070845c5e01d107231618103411112100d05005081071440c074204042c000034a01500c03a0403000d4005102148442056030010300e0f19031464500010300da500c40010981640c0140c1c2c044180c0240700c0d10410120400034201040e95114085031400c00061040c00c03002e034000003505510503d40002e04508042c080c00030390304515000703403c4030b0315840a020344500a600c011442c16100e034601d003c800080034011400140b282c00e00d14040e045440c3c050040d9809800741c01044280a01440590400c80c0c04000039420551240008206030800000500803200c400943c40d000303180110020000342c032464212820002c0d20f505000d45a9034030700700701c8028010046d006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 197018696 1250 197017446 197017451
    0xf04021302070309300311010615020c01020f070602070b07020307090501030b15030d0e011b0b100609080102160b1009090b0402130c02280602120f13020306040602030c0706 76
    0x21801c0c5544101c02c44c054813403080c2894032400da40240c1840e0407200030040c020513410380e200390b00028411641c91040c2c3c54050004074029031108602d10b24941040b81c540c00607070258820a08541e070402000d041070740c400026145035814004c0094a80303066000b120142c01002510320110340302040314800404081c5002c220658407031030003d0260b40262947c4040c0d0311411100d20641c600407c0d07031081424180c031541448010000155440c640101c990042c10400c00088800714002010306803068800337020303500c0313994104040a040456541c0203942e00d0b07841030220018003000134204d16a0150006d81c045050b40d01d10903030b1080c04400d0303000380da580d40c1000042010070032a0f02405020718401c481d09100c8469240444080340c0c8880000001640080c40025603115041000c50f91079010210f00c1c0212106c94459a059910100e4051103800c880410400d2201c00311401319004684942d00c0034085580340c0004e07a6449024101400c404e0380080800c0584c000c0004070352032a9480340d0103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 197019946 1250 197018696 197018707
    0x1e03080a23090f010c110d0327120212030d020a030b0a0504050712020c010e0303040f050105070c081c020c10060302040605040608120d021b06010501140c060f04021302 74
    0x41100303080d5032444142040c4948080311002607407054880240c00a80540c01030750300c1030011a61100180810b44840006a0034005540c54000601e440300b8001d41362180c646039003d01040600e40b824680c0d0003103c40014003032040a10fa5100e03000790540407903808400c0400c6901260852240b454113030000b5100284c580c005582580001500d1001260b144400c1035a85e03082c042a201b00302d5100001408528144240743c00310344c05000c45010250001032044400842c151565100380c5003038408103840f203e42c4040103c2400f405a00c08007514142c2908445581c2d4135003540640b0030910103c03800710000184904040d4140c0c0e600780f60344021104d60610b17000c0b42900070811404140d00443c2460404202814240214800c0351440c40051003540714006140328590005108003082031b400b044094140d40c05000810360000204010f425030754540400901100c00032085814641000c1c4064180e10b82c01141a40d442540b0031490031096499100203910301e03142c4803022480c1440846c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 197021196 1250 197019946 197019967
    0x60f0a14030105010f0b0d0e03090a0f090f0c1d011b03050309060601030c050f0304060603020406030c170a02010816092c0606180607030e0406030b220209011e0308 72
    0x4280c185036106400800a5980312030310032072042c405000d07600c008001041f0031443c20708140c3c042c01c50107040d141620b0030002500001070041c003c1c3d80c0102d0b584402d100c011711050300c151141ca040441002401c101c10b240d421005044061081c000b03c98504072006403244c5c590007140641c01d00c02c05d009070f981c1d1580f40352030041c00940041e20301070303404d1043e0000035030030354003d04c02d142e040d803001e4852504115140c2e02840c0d140e400280126052502d400b000801a11940207101c0a54840d50750340740201c3c1460501c110410700100031107210340c413004403000541d030411405900904040c031140f1058503100000d031030f10b541e9236224109640303000348442c01007100308001401c0169440490481071311010301b00301e41c0b4050071040001d203150781c0107002e0f0545800300c01021264840c2c1480c0110780c2c6501c00080850302c480d4000d0701d01080d41020411002c21000d414065001c20140c080240b01d6943c002c00c000181c1402040140e0f08a094010f41c0c2c00b24040300c0000459001c0c3e8525034488d034252 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 197022446 1250 197021196 197021219
    0xf0304060815010903020f0409060f090c063c030912020618031e0a020f16150512070e04020d050114090c040303050d050601030e0d081816030b060f0a 66
    0x442c201d40c9031055032a01d807442e40c415510301c01220b800805444c5081044d000308030040101e0300007103c80c0e6591f01c8000071718021500070090003500410381e18404038580800509802c00301c401d4502c10854500425001d000241c11180b101c41c0c2503444850003960700e0509900601c1c0c040c4014141204159900038000e40c005448c9201e0041040d0f84d06031800140041a41c0740074140c03880100c5440c0455101c20154442d0161904041c036104892100c46000040c605101614041e410000300c0c4600a0001002225a81c0c41002c0c0e00e14040d8a03010b0300c40140d040d252009030540c020011032a20342042d99580750103489100000780001c00c0b0650f500da0514140c0361440d410b442c003e04d04480080d074203004100558040ba509601d920745400020190340004100c001c0005040c1944c580541c030703c10408000c1c0c181c8100094642c030000303040c491100c241608440007810401d5105100c0031105c040d86102c003208581e409400e10105491301000103002040701120b0a40140d0390010008030a181c52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 197023696 1250 197022446 197022451
    0x40503060415150308030a1808030702010501090605010c0206160503091905040c050304050a060c0c06020d0e16050d0303020f12040b072d0806010207031b050a08010507020a0308090f03040608 84
    0x80b00c003000242d402040fa0311030003016200103005103d0074000122162481d0300001b1004000e006260174810300350b596124030343c000796540300050795030340018000d520091141d000502000d0034a41070420065000503100e114000890803039680c0d000101c020041b081007a900c0c0c4000081205940c034603013035a40504c001481c03003038500c914100030f03184440c6402042200d000e1504030000e043d4507031054076038002800070407400f0000c0080c5d40800201090052000d041004105000810492240c0048525001d245444807003282175450040085a40d1880c104110982c1414096220789283c0c007100110f00442703200e4034194800f8000c1100304600a21240c2c420782c4540c458940c4000c2211400700080300b6482582480900c5d9031001012900508c1019404801403048800f00f40c1c4907541c0120401407202e100300f10301002c030810b001038680b001e81d40024002001c002c024034640350100a54a9510b01000f9042c00605004036110303c20502095441101c0c02084a94555903a40002c160740004c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 197024946 1250 197023696 197023733
    0x50a170a1e050105010c080c03120c030603150f0a0f0209060711010f0507080301031103010b040e28080906071b080c131a1c050a0506070206090d12110405030604 71
    0x2103807422800001a02c50181614810ba448550484950b95030a60030b600002c0b00c142c082c0b1050104070780f49198560450f104d039030343d0031165881b81021014180790414406402143c0c0003c4400c101d044d4400c00784599004581600c08100c610099521100a2003280000e6401000000381e0328180f0240741404041e440003030381c4452421185550448040c01040c1c001028440304000400201e558105100d0746a40c0080001400d0300011000a0480e81451304007159500548420444941501920b01070000c014010503200000c5c1d0342c80b0f8800d44608002c041c40344502192030002d101c0d40e0055582ca81101c50360540c0c1d051b4580600a656514484d50310784207004400b5507a0b41c2e5403c1e4002e408280142140c41c0031000c803c3c05c00c1202d82a00d000000900c6541a00d80704045101000502e1609004402904503801c0640b40207040050042c041d20056009181c00041d21f41d009a40c0d103c1c2d4402e2100000b10790781070701c00d40c020504c26a4021503161290b01e00b0700051100f510080d59407981c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 197026196 1250 197024946 197024981
    0xb1201080c0919020a120f0606030b0f0109090507020f030a020303100506040308120406020c0d05071e0c030807020d0c08030d0f0e07030b220813061e050a170a 70
    0xa608002c01a202121862001203100b0076262858209401034043c40015040c0128420080352006045802c0c0702d280364000c42d11100c0802c021501032261044580045d2442211000c0d04e030006040340c1094402d44042e2540c0f0740024010a109000c4640303144001d50651759914a1200025500d03041030380c03200341752901d9440004440c501042240c2c1240d0380400464100b034950652444601e000510136030700d1540800242c020b00c0d0f8103005103c0b036806540c40d1152110704e142020520040715884050903070300128200300c04140710781c201c2c000701d903440b9a0140d076a12891003c0348540380c10b0403005100700b503007034400b04501e80007002611202c1510501082a0310b100c0151a054132100942c20b00c80c1d0f04581010700103d010310010b541c1c094a00108250341d4003100480700201180c3c15020b813804080402da2809500c2125080c80c01807043e40380000300d1039100d04280d41c18460441005040c1700f00040c500007154020b81c290f0034040b600d8448013485140044105001d0008008001c21945 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 197027446 1250 197026196 197026213
    0x501090f030810120b1512030406120e0303190f0c0f18030305090d05070e100608010f0b041421100608010e030d110f03041a06030a0302061f0b120108 66
    0x1220628000440d4018920000c0c458001d89800507170300c8000d01415641c020700540841d098849145644445a071038005594a9107000c030003e00d4005c04042d0b0134a030302e0921416200d42c3d80c2c00000c1c1c5c2d8100c10785d4031304103001b0704a18036084000d014a00041c5030761420091402e040c2500702040c441c09600d41d44800061150303000f00c1e9140034171035000003004601c0600442602e4280051500d51485c8290100d0b0f13040c80d1507900d4684080421140c8980401d290001400b00984c0452500d0050408440c0d42d8215810700707916000c203004d40e01522540881e041e68640050361034200a800410020301c03420100c080c0d4059680d240d44030b10349000c03846405c06e800055000014410101150b5405024505000c44225000007803d01c0400401c211a418411100040c4450f402540203a210b82d45130b090481d02201150702c0d200004150b01e1180d0060003840380400d0700030801075481006c0303030038040d041100081c01501548860300503081da40c4021540031050100f00300101d0680748400103c42031b08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 197028696 1250 197027446 197027461
    0x60f150c050607030b010908070906061b080706020f070209180d0e010e0904080c0709021e0a050304020d0507080304090207020306060d050703201c02041505180406090501090f0308 79
    0x160048a001002a4050b0740003651062003075016a6001005246ca100525601c1d4041c502e800d1040c2c1140080d1903503542c0400440c0d030001c0382500c645592244808201449881d40040c0f0300405402408051b00026521803160b8003400300c441856004140740c0c01e03030a0541c1c054420265214400a07540706100c2c80c00318180c000c0c00200d02509050f96880342c01c425000500400c080064011130301020700748050100c00c8001e001c0980500540d1200580700c84800b035410803407017031124502611100401003014010307800340403a6805034065517140d90840242c40e0261601117123034010b0b54070b13010101e00851152850b07001071681074000c500300c9250791030300000c00510711a0003000034201d41c00000100001007407140304440900011514101c0407404101013040894250300044450000307194810440c0303024880d001c00b8402a000d07040b00c0c01d05150129a101901e01c1090800c01207441c0005e0070001c3c3c1c4c0d00a020213580c080000c0c868605d16107003881d4000340300c8408030003144c0d43c0000914032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 197029946 1250 197028696 197028707
    0x1b0a1e03020309191103011404030810150809100e0304050909060609040b09030705120a03050f221e110907030e0a0f14060f1503010e0d031e060f15 65
    0xf01140c0010b003511200c411030005003981c2d80d01c4115888200f4850341c103280da030300388151180140d040100810f24585458018840c00d4000d210440d04243c500050110000513160049403909909021003980c60302801d580c0b40490a0040c031006505104007084010b0001c0064800c650059a40302002e0312154a02c03034070703900700b185c1c256046926880020f0110300c0c0524041d130030244031419a450200a03841c1c1c0341c280f818040b603401e0504400070321030310301c42c0d410310400e940102080618500c13410030944003004099400c1c01c03587c140d18102c00c4082070000d81459002103c0d407101e500e4481a11504e0229030425030742d542c0c103100381b080340001644a4001d000d2401d041c039844000d40b083d80c660742d44040c2440086035080c1d90701f50100c203403038409401c1000028010a000c00c5404840d19156450000c600d4400c0d104600a07410001651421030000072032041201090a010800250400184607007207440e404010040341400303000144089400c20400586040414021101d031206000382e030b2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 197031196 1250 197029946 197029951
    0x160819051905040e0f100f0605030103110306040530040e0a0e06070c02012f0609010e070305030d0c030b030a1401051308120c0d0903020312060102061e1b0a1e030203 73
    0x2d0681d04c40c00150f00c004404211a0b8072120680348500c005072121302120303210440f50404d2000c00c00000050052000c401d405515807036084004207014685680ca0a4446401c0201180403032a040314031082d031454298807034101ca08043c500c546844d600c8a103c3c05590090310f1031001d5a25002c0702d03c80c01c5d4008142288030b45416101c6184001d085e034011101050310014400c4121b64042824990145c61250203070b031416040003c0c40981405c000e00c908644003c00c40110070f030f0101400700300164000c81503c6ea01440c0000c00680d001508034141e01070182104490340c54020749655070100074000d911100e41b0404007008100654903c0404c1c0c41c1560f104002030682a0f0501c81c0505550514203200d9203c880440524141a084c02c2c0000503111a04801c4001d80c001140d0540a4026441541e502001c02d1000f410207080c0381c1a290307910403400004130702441c000c000241810316001010310100341850852a079444501c00d0041c49000a049000503480c00c0340c049000c4ca6100c2d009690 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 197032446 1250 197031196 197031209
    0x30c14150118090507060c0816110f030106080c060d06080106030807033b0d0b180606060307080c0c0106030503030703060612050c1606090602030c092416081905190504 74
    0x42483e0401c08240c2c7d44010b00401111700080c10052442625448400c00c40024800c03030004025030441d20400111945c0041580d002c0c0e031510000b0095224002201c2c024180e040ea07015903503641c0650480c0180045800608940d8286034001040040001c001d2141c02d00903950fa041d20400a00c0218880104e1a080744840d00861524006050400d0098000c0040103003407522500007695103a801d003c080b07806600d8480c03c0d032150500c070b8030140900b942c4074000f1076002d803461908a9000d4140364000c6c1960307000220100e80e504100e0000d504c288003840c0c00c0b034101ea40740e181040004028080c1401190002500021170311400251802940c0c081e42010300703094100310201e00005003d91000c40185c48041d2600400408601c030741c401503001e5a0500c440716070300c0c5800c0e024044071000d0f240e085401e00c0c1450f60b060701d4448142c4144c956000b20204102e042c002c1e5810f003040785019151151108050b020f07110110b0340d811600403c080030850141e06062000d817002030340c041c0103520844 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 197033696 1250 197032446 197032453
    0xe03010e0c0102461a0703270605090304030609110f010305060f100306050603040c08011401120605070e040c020106060e0609010801090b0301181506090216030c141501180905 77
    0x7001600c41040e5142103500c50404c42e410310341e126225000d021408894401c441d09001003480384859144c0200c04000303d60507a0302e035441020140318071b03083c54000005010325540310003040040805204a40083d03170000000c2c4078100c1c440c1800c004103881c94420310700c1208208061311881d4041c4c01824400c0e1402000c280c404201c0800384105904050880b104050b55503c1c04940340e80c13074802940c002d41c055201c444071141802031301421240e1040c5442d17800d424000040100910504100c14807070750040c0003045d280c40300c081c1910004603400d005988942820301708800c29605600550803202d00e941c811800e1740c0070109004041c03050b941098002003101005000307400039070b00040103a190140000076024100188800340303c0a40008a4911460440c8000780d01400d001c0d40c006041c50582c11840d1000441d50300554200d107241c000c0c00e200d80744007920305002010441c0061071074080c003a600e455032100038483c090b885c2401980540b810350801c1c60030301d448502c107085050394010700a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 197034946 1250 197033696 197033773
    0x30c18040b180402040f11030a0c020616110a0b0103030c02090711030f03060d02060c0604111009050111070905090d033e0403080f030105031b0a050409030e03010e0c0102 75
    0x90040c90b401c000d00c20b0780c1058484c80069490030180c80350381c00e0b401c60154641c1e26818528008025a41e040005004561000080c0315211081d042240c41c1c151b00b17800c211401d282111103d03814881030900140c11140d11000000038075070058085040c0340e108407024080c981d584d050580d03200d0420902c0500940c02032200e41026071142d001590480002032001210780e800d640060b0048c0d0200c849401c0f5038012074140001c009030b1200c203181d510780844038541030041c4ea2600404c210f01c0e5120325810409a5008410040401d00c081d40180060500c02d00040c41d00e0310147d0b660718040300300b1000081c5049502c80c000d10b8900b2903002051001034604403032804008604900c0b5001c1c854070b203e1000700300b00000000303031050018010080c0e401400b80c0c0b0396140c07200301810040103452a0040091030f01200c00c50b0b40d2042d01c3d02e415628100c40019403120542811102081c68000d030a4041d0300e41003440c1d5040b4000584280c126109034201c0703100c0010841c801c45081ca1400d80028807504400c070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 197036196 1250 197034946 197034979
    0x110a0e07140c0703110102060f060108070311090a03061505031605040203061206100608010e04050a030305190f0b210a0206070f0f0606061808120d060506030c18040b 73
    0x80e8003074141507074400603081038144910682030035415403048440c803e206040c03040c00e50f0144481980140061010311283c507001001900da100014003c07020140c0d180c11541d02c3c05c54180694281100c05482c150f005501e0b032800000624040c03018140c2460120310000c2c82e4503001a03150341001041c0d1500f545076240800b840040c2d00003620141c0e0080903180303081d820000030403500307108241a00481c40050300c1c002010f098020107800130100d1180c50810080891400074203aa403403030b0b25280016a654580741d08400d4903504400380c08685081100108070400c00750426070595004640d40d01102da90341c00d034008100b811507103110940d001340c8100c02c05403515602a140250207070030000107000c825561381e1034103030b803010044030650741c0e607074041c00120741c010816203260b0803840912031001e00307004a040ea10401c24080d0b062001c030000788034003082e6254110303100400004e04111344074245007141c031004c1d030840003000d2a00005607151050525042c0900c0200700340140c0419021400c50b01d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 197037446 1250 197036196 197036207
    0x405150604031205090d03120501090209010f0818100f060509100303050c0a020d1b090b030a2303030403020d0311090901120201200a02040e160e040501061809110a0e07 74
    0x1010303c041c01000c2c01661030ba03440b00d009151200340b0a82d41d8400605007070210300112541030b04540d070a2072041c84080e8080c2d0f003100004208122a01340912285d80d40904e40c5800040c0c600a16058043d00c0803643c0c0008840d0444024841ca2003c00e020035034542041c421032003000c40b031400c2141e071410f0082021034003840080180d00d040300103466240c5196004652030407007409044600825920403001e940c1c14482c50303c0003404803814144040c40020000039611700401a02030500d40d406542c0d040100311100103a43d2500451041d40d40700d140600f0080e403140c102e005c02c0700c003290074005c1c00b1391462095002c6a443c03150040050350340340d0801c0404601440c540a08a051000c03a5503010311a4501600101e0758001840040c0442c543c2441444240c42c03000c1c50480302d0b0b92003001080c4113403c400c07045409031000754641000c1c0c2c3c2d0b035a0429034017501e40c90b0b01020220281d1a1001000000d9030007044510b40606a8481e601c0e41000034020460114410a0740c0c82c0317100390201f1086480344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 197038696 1250 197037446 197037473
    0x41e090c0503180705060301060e031b0f0f010e030f01050702160302010f0305090c03120c0c091303030b0102100e0705100f09060e03120c0102041e030804050f04022502040515060403 80
    0xf0790072200000c1d100c6010074181c0e0300a0f08006e01107460b188030001580380800c50183d507000d02000300c0015400b0000170600c000a0420540d00c61400d044034005140d100704501c200c007541c02000c441c000b41c1600d44042c020a020349100005014a600001206128007035641c11254107030355139080b40030300460440003054064180c554500605800000b5694100980700c0642018800159100007440180c1e261850381d0000c10b000d06420801c00525188140d0340b400403507018200400c2c24802d0310300407401d041c50500080c0d1264940051107501e5540041c0e9401501c0c1c0a488042c0042c1e9401401d5a00c101070400c00000151044428050588100d169003400705000e42111040c0301d0300341002d031142d0040300031104a60f41c04501046031400070000501c60300b003090701e5141a0750864991100d40e20450041501840c00c0d409130b1a001e03190359044600c411901c4c141ea41101c0c054601c600b882c05203d680c140c6c811400c08011030011010b00020310b50b03982c0000c1c01d0910301891075a40300c1c0701c085507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 197039946 1250 197038696 197038741
    0x6040b070c0c080a0302071e0b0f070807020d1212090b0424020d1a01030b03122505030304111912050106090c3f02090f0402041e090c0503 61
    0xb442400070704040104102800c8a200f80c01030a0040c5c1441a01c00000c2e05c845400c9044e017250f03010400030103081c0c104031210030300c69040c6281e0303c3c4100d003400c600c2c40c86a80c20094120b019512800c080c444c0d00883e444050b401951142d00c603007015074002d005e90303a407040301903c50075021000c50001a052034003031290b04900d0040e03400c208583c07040501203803c50100400c10644840d00b0400c1400c4074882140d1645090030104180303900800481e554500300a94440c0820b0009003802c460200c001180413101c0300d6485c8482c251605190260700ea0300292022a82d4a9004201501c0e07031901043d040c51041202c00c070414054a13080400580040706070040da0079550310000401c2c0c000d458065207800d410942c4450070495010341d80010b05000c51071901c143c44071040385102031a00501c1e00f0548151901760056200c520f0800040c90195043c2d2251f0b510600c00900021048410b00501802070010b0100c400c540d03548001117000d03142030086050015208100048900300407207000d07003050f0324 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 197041196 1250 197039946 197039963
    0x20a020301110703230714031606020703032f28020a020a080102070308131b0608010f14060405091e130c140306190b041107060e06040b070c 62
    0x1158000c28211034203001c40404190000030b000d420325800094500301c1d03502c1d011050760172900b4003c0000c094068011700508140b2881e05001602400b0829901c01d0401c0d654003190071001460040003d40c8401000c40c0408d09049200f036031003e074800500c20f16285190440100d014202c10b514040d8013182c20008410401640003040d0900c1000d40300160b64980c009140305407240c01000311014040e44481000d13801044a0f0001a6221441030741018104c8101e00110220b440c015907035595080d8011540d1040d044001819136105101d58100c07100c04100e0001d032500c6028007a2000300e070f0034200e60003001c104810801400c01c1a01d00e540300d070320300e0440138007070075488043c04400e030080d0f079100000169071901030140500341c400f002c000c01d0310010414101c080d60300401e8450320001c22a15041d101c102d2034081e07502c000e40111102ea40001e03c20010044140034062550b040210151340c898642140550921000516240030b40e80001e95110a65610f0404884801c607659081310f00b0030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 197042446 1250 197041196 197041213
    0x501090b0d111210050406050604050c2511090f100503030903060609040807021309110621270604050d08010303140c07090216030e0108060a091d16090b030c0913020102 74
    0x15505c030b000d000b14890341010501d03041c0346003004240c5a0107440003518000c1080356550148074140021006134161f014110140410f0402c02c400c4000c01c1c2401d40c012014104000f012030450301c41c0b6105130800d5061881658440f000d050381c030700401506a40603401a8040fa103203280114440303a006200d0795a80e4504003041d40401e500d103200e03102404003203031945030b0b0004100220543c801190700640f10756080c07002c01d2901c000708410400080182e840d100001c68003103c10043c104814102c04910444908101c012560b51220200c409803400d009409030303900b90621502000b41200d4155a50180c40c862945446800f80c1c030410070301c00c89201d80800060607040500180410800404509004090034140501600c10802e0158100700ca0705041010607900d540c01f2200351072901c0c50001c0d01003001e0b1a4481e00c0d8000e111015013501c00c11943e200b8250401400c08182d4410420500079000c4420a00d0790b50403440d505c099011054030700180031104034101c0107201328014030458071082d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 197043696 1250 197042446 197042473
    0x4020c030703050706060506190e01020f19031403040b220209040606060e0a030b07030b06070b012706080a031202191e020f030a0807021e010501090b0d1112 69
    0x5501040e02180401c3e0080391400034480c15100d60801030500b6030f030103482c00141c0007915003220038044080040c04113142e0151501c0e44200b191a10340c580540803102c28004400f0003030200035080c8070440004032803003145104a500b203001c0e20300440d80800b1a0303519844801d81c0e8282581960006521030110100090150795044007082c0030b28000e61001482c1070510b24000e140c083e2000d05140580820790041000402d40c01049034095900d00e00042e0202036807000505502c203500b00900f5100c200b10000c1880d1000e140d81012069400744801a030910540c129000d0350003521500b0b0190b0410036000c40442e000341c4a4014140132840014501340f8810f42c402c81c118900d100c1e4100040000341075000880c6004100507003220180001c0080c020000011030342c2e4481c01c6041001c01030031102141c1014000c215070054010215440800d03491070a14607070003000248110820907007444450704032410007014640515400909000d00c400300310341401404446205c049174107201d1845810b03206e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 197044946 1250 197043696 197043703
    0xa052b02060d1b0908030a23090915090f15011b05030a030b040f06050901121406090a050106240807050c070b0c06010803130e070201020910020610080c0d03050904020c 74
    0x202640d01030443c41c05682c10091950303c06400c40a01c2e0751040080c80341c0d20b904802e01038031801c5048148441d83c10b085218080902032045101d0b0080c10a40034401c648542c400b00c1050300d903080c3c4a460701e44da14819004030f01d50041e6000006803001c0c004001041d4440e0b901e102c00031007a600100c01850507940d40c3c41c40c5501c904038083c00039603a541109607030319040c0174400e4030340901038091068504000004644090600c0391f03a500e0b10021000c5410420b0500e01d0b064203124010075203006140c00c1d2807040c0c940c1c0b8011000c07100b5510344000440e80a80e4100e40383c44c0041158024060722a081030181d40c6100e01402d504240001888a00700542041250002901e003010303c20362100030100c18189440340c180c02120098206010030740700000230f0346120040710281c209003203140e1036444060b40240f083d003810540108580d918030051a4000408501480c85036002c0054265190803254548001030080d690102e070100700080481d01ca440685544031000704014548051460300030701d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 197046196 1250 197044946 197044961
    0x62003070c0b010e0114041808040b042903010509070c02150d39050d020315031005070e060703090503070326040303120e0109060504060b0a052b02060d 67
    0xd002441c45420840c60b00401401031481d140d0120443d414200700c0d03459003810841d014082e039502d40081c2a000c4d030305441c0d41c540b1500448019910381c0c4800c2d80032220b900600500300000140441d904001c081d448002c0e044802c50040d00d030440c0d080504116244102031b20031784c10030080032101000b6903101c0030840c0d0981c40104980707a50f110b050b2482400c0d580043c941c6004006076038425580c46001c09507000380204d800007110307041501100c090710b542c0101c0200e0103c4901c04810490480b01d90511030000447c2281141c4030036000d0501d210517604200d0320600001c2d4800c040200504004000c1d0003064400d060003011340c0e40300d4020038500046030f84162800310118211040c00014102182e40140000a4840c079003421510040d00d0304100c2c0c000c8009403540c407500e001040c84298446000e07103501000074031070360400b81480d10107491994030261003015140e00005291904842103d1190703803002d43c080300c1c1407081d082301c0409402400186e8109104001c6000c090f00d09115458 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 197047446 1250 197046196 197046211
    0xa1d0a09230c09040b03030405030606010c0f050609100f0b100302090f1201050402040e0a03050702060a1704051f06030f110f130f060512031e0c031303050d08060d062003 75
    0x3d454058001c100401d888520103154001c0e04100405d2103103403004156a07610140c2801c1122011503540b505060a904004c8054514003c81c414001c034aa0b01149180d00c0200a400078809801c041d00c1c804c041302e4040001d603034454403c0d880ca0075031034061317005810040c4004140401624803840400c540090070189900c607030b55100c040108520b17003441340040f180d055000600082020f80c0d800b40151082d403001034840c00c0046505001c1500c2a14614454800342da0041113506203880d1055480c10780c1030418400b8a1003800c3c104104d0b40c64401c40302200c2d0001c00440400026455490305040350520481d008900c00700c0f00c144503200c07030038042610003014a0001d2014030b5582c49401b1074a807a0495881100d80e44420049507000205440b1100100703400716034250070301c0074000402d200d031984d400e1140c0000700d440014034201261b840100c0e030088069500c0c61100000858400034200e038503e520005003c0b8000c0401c14560002d02c0e02d0160010f901191072070b6800d0000c06400440303611 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 197048696 1250 197047446 197047471
    0xc070801050105090a05090d0c0c0f080f0d03020c0706030f0e121209030708030708131401090302070504110406180506030f070e010c0506011e030c0b0a1d0a0923 71
    0x1040f0a0804401c1554007010348602040681000c1800b41c2d02c43d040b540250041181401e80c43e0144118070301c0c54030050805000c80540c150b5120310079a21407041000c01007450040315152503d00b40a4021100014003c60140c081d541c1010b00940c0109109801c6400c460f55038855080580d008000c2c0002c90000030041c00d072504051419038082040c0105650415002807003000005185c4c081079903004525410b0600c000d5447c980b8101e10b16074200320141142e88909410a5009019481302072110301035401e40342c0c40747c0c0750000d02040e1002c000301009000c6003008200895881a00c10300320581807200d4000b05c0d00d5889000408507002070312011100101c50043c0501e03e5003020300240708103000e09041c5005800c0c0d849903501d9440500c02c040742c070001984040c4114941d40d00600184d03611804400340d0b00d4482c000c98246401c55101c01001c0b4280300c890b2404c54030710000c9801828401044081d510f0308200c8403201030300101d60440c1d91405240758200c1e000960510f4584149002c04c0302 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 197049946 1250 197048696 197048699
    0x2040e010f06020706020303010909020f090a1e09080301090504031704110907020a024c140c060c0904090f030e1504080304150203070b040c0501020c042a050c0708010501 75
    0x41e015401503030380b01105550281008000e41a00442038074119441e030b01d00080d0200c0301e40081510f40f60042045c07503220820004000c4c160a03680d000652524001003400d010300b00e4034501e00c01701d80c401c072000f504035402400100b01c40912a08459401032085c60301c080c01010003d0340c50381c040020b80d0100c13940520300003586601c1c00e1100206510842034401450a09600d80205a00100102c00980c2d0701c0080c0e40c800520803c008032880d240244040c102684e103500c1c00340c15540400384910340c40001c140c0b90340b06402500601c103485403c0700c1c500103000c40f621000b004040c036034440448240c0043d1034000c00300210301030540d28030655003e41c64482e2240070020400900350300c5500041001700c1f0611081c4141c020000c1603605850030b501d0484001c4040701c1c401c0e80b0f0b60250540040004a90b48200b0040180c90300c04c2204584082e002c0f210034001000402c410f841c03000c0c00e044078600000c8000e03407001c040584101d129507c0e0f401d00c9071420802011440c01c0260940201c9000d0303446600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 197051196 1250 197049946 197049959
    0xa03091e050a171524030c030718050f01030506072601030807050105012c06061e070605010e04080a0e010905030106090605090c0f0a08150901030c090b010f091701020d02040e01 78
    0x140c0742c4d0f0040c442c0303100c8803500e444010050342c1424210a0031880003040c40909690b1001c005005032050000c013207460f020790329400051031b1240702050700380c04c5040070040396100325022a40c5050b00d5000c405460b9a6540c0c0d2000c4402e4034290714a41d44010b04805416118040500030f68040c6002d0501300b6524401ca0604600359107060b84050303180c00700b030080084000000100d0039025030028819a009841d4000050168082e0510105d18001011060001a801000188007a9210b0203007482a6a0b8520030135042c02e0007110054a90f24041000e6100341d4030454281d680601c1c141030074440d40740c8880100b42145d400350000c2580642d950b800380036030314201990340c1d440134184910b6803503c9014580c40c2c40f680a0000d81d0414080e03004003003400c0340030014802801400282051026603580e08080c0840e4a0310322903c2c41640c0307490420305c0994814070b15114040c103640c0f034824055141c1107100c2c464644203a03010713215550a100884024140780001d00007030103030540454041d4104007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 197052446 1250 197051196 197051203
    0x3040b04031b05030904091a0a02070201080702010b130209061207020313050603040c090c1b03031b0c0b0f270703020109050108010608070c1103030c011d0a03091e050a17 75
    0x32400c0b29101c003100d0710000264000203d6010100944011034500c0c0985030107004142d040203419a5810524200031a1840301c5e4090428039000340d89101040e1661502070303007200c050081640d00580c4020050000040703c0c0c00a000c0d03528043e00142c50705c150303940250b50014054441000503080000c41d00c0900c2402181381e006810103c40840c9181007030307600c82e40c0b5040144554031030251506241500c807400303070440003003054105482182c070000c94a001001007280700c403000844404800c2a070034592007a02d0fa4a0240c2c0e2040300242070392a04410301080140040040c200a142c2c0900302c003482c1146400540558040c00003400090306510000d00034100641049040001003801040580d509c4002c03103810014038204002e0603941420050310b1b40340e0780428180c06200c001800184031105522100861801c60201601c4200146050b03489800122018000420084c014010050607001c00e0040f0490840b04030403090f6078802080354021143d01464042c2140c16160719002d1091 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 197053696 1250 197052446 197052467
    0x8010501050a050315060d05030301031208161706150d0f050a0506010207230a062f0322030b0702060411040510030f0c09050c090a08210d09060203040b0403 69
    0x80700c2c04030045007000c02003030303559000035a100a81d005050116159480d802080300c1c43d01e40203800c2d699650307100e090091001c0150f001e880700040b00d8070001581080c2e00604841e1942c00b03540c60065a44031a1036025205502419859000c0c410342c0b6181e083c0c4c410400100210310003180082081c03600583d1140450f84001c1c90712038890309200400c40c09aa020600c1010b0b1800c1d00b104010090340c2c5c032000c00d117104003030784807541041d4600d038003140c4d65822401c0300d001c5075142082440590f50a9800d940c2402c1042c07404005d65005010b0350185a0700c04091034840104106501c038984d580b030301c1d600061841600c8c01c1c0c0250308580140300520070884211151128191820301482c02c00d6810030610340458840074042c1207162100c04104208808244000c0c01d0355030003840282051140940c5035030044124174480c2038405000105c0c007801181d9104680c111a1200d00c0000448840b034010b60b0081c01941d4040782d0320305c0390000080242c4061401b4034000c4e0640c030070500d40380c034002d848502413 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 197054946 1250 197053696 197053699
    0x207080f0d051605010912030605040c020a03021c050906070b01030b01061b02061b07031202160e06060a050403150203181504030e010903060509062502030a05090a0b0a090801050105 80
    0xc89074006469042800c031080d0b8603842c08100e5440c0c0b0030707081007401041000380040007010341e44000c0b030513540d240c0c0068040e180308036030811410301004006e0341e0f2441c80c998000c0241c0c01030240c002e0300401c01e4091221020742810110328160b80f0b000003c515601100040b03d1030740c034a000500034000b600e61841e014000e81c3c01c00038034403886100c5030310300c40300366150003845824005100c00350001c40e5544441d0074141c040884448076200e2508500588819030424010301c01c80107448000c2101488850407200003030028070b059180e040600c0400d60207041e9030700501804100000c002075090781e07034201d05007004400603203e0030244109104040d000280c0c00c0d4661000c000c2000030400038100c1c5401541c9030074413801e00b034031500050b50504006c3e0b1000d8091840e01b1f040000500d00810060312030152041c020b0070504140858285e01c9041c0c000040c01a031062108842c0c4600560080c684080001c0c0303c00b900342c1da40d0000c1c021950021010380000360000c507042000c80002d00130903014150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 197056196 1250 197054946 197054953
    0x130507030608150a321009050f06031002070f0b0402010c0c0305030a0f09050102032b0606051e0403030912030507140a030e06032a090d03051201050a05092403030a0207080f 76
    0x81414404410300c00c45c51a50141070300580c00700f40b0102c0d16004280060080307802c14001031410300c030303035003052801140e01c20f009004980404000320000c2c804ca4415980c4401032038141303404c0d600d8211940784002c00c200c1c103101011500401107104400c1d030f10300440c4a60005c60765020402002403403049035407218014010400c130280166030b00801035503070030041c280079100029841600c000d11000d000002080b41490941c01040c0c1aa20400410321201a80254007181c1c40b4002c5620086c4210b2001070000383c0395100a03c85840721480e2a50910700a2812504080c1d454072142d51b003002c6548400f000341e000c003020508041d04000e210390100c108548170741c1185000580520b02c140519803c00d5581603031600e0901401c408001d135081280040c202c078081e00358510f0301424503400291a4440b00e0040d0000142c5494250700d00010b41c0e80150410789940c8514007504044801e52000b078480c00044c24000295840401c06007070030820941c002c048079032800d203607203007403007070b4014100620740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 197057446 1250 197056196 197056241
    0xd05120a0e0910091e11130506070c030b0a020d061706100f060c1a01030302061906060207060c0809031203010518090a1b08060114090106050306130507030608150a 72
    0x501c80001c3c0031102d01d001c01058020350400351a41d140d00d060780305e1a8651030002c1003040300300000007519500c5001c41d40790508a45410800403a4014007100400340442c510080c40041ca90180303850301725080f03201c0542802c0c840f0b1500c0040c1c5200e80c1001e00300c00c5660300c8500c05c141080050a4100300025041418941802c9045040d00300d2401040144940c0e054079030100075000c0881c0440d0512003a41280d80e507180d1400a4943d60103445441c080028209042550f01c0035104039000c541c450f03002800d480d4a440b4040d5410250381105980d4800309010f80d898648060045e031100c00500c55455540358144010800c0c41c041401c00804000510410014600d03c0044c420642941250380d40013013030142d0b1158016480c2d1034010441c11300519000042480d0410b41e00360b0101c5040f941e010f4a60f89801088909000880f60b56510100c85d00c0507406c607001582c4500e400441614000c15401e848482251808207030420074040e49032040c0410149201d00c2c8a210280003003aa401d00034070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 197058696 1250 197057446 197057461
    0x10906080f070e0d0b1e07021f0c050409090309030201350a061508090d05070b19020903030703020a0c21080309010f0e1b041112060d05120a0e09 64
    0x601c1c00a15002c1031101041c0c10b6050395a900ca1602240c50340a251444e0071324140c4000031801130301d0407803408005101404920000d0007c907507094168501c4032400012124015901c0c09091400d0380842803040c01c00005c10b01e2881c0e40500c481d051b0090321030b800390902d54800100000b01c965075415814030105090b00520f0345144d1401c0c809425440c02080700e0301d5402a83c03000745103d5214441c0744540440c002e02050f00080400e1103034040e0f1041e5600b0340c44c414800c1e46c4500c40c5042c000d1076030441d040069103815140721080720b081a60700005041214400109185500400065000d613000c610540e0030800b010400001410080e450006030280302000800c0049a0003802405802c0210000f94a000d003513001041a1403100d109000540524100640300c0d90000c221b000c08000400c05d14105041c140146251000b041181c01d1400880350f03040810020082c21190b44133003c104281c000c690204840c428120111480319510490404040c0003d41520f0541d0b015065075000c1004a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 197059946 1250 197058696 197058721
    0x10e01090b1e0d1409070510050306041e02031f1a1902010e01180311010615030c0507020a06030608160b090418021305010f0603090210031509020f0901090608 70
    0x24185a0480d003240b0849003094011140690014984102d25100805582001410445000b0005003040d5800320fa107074001d1001c15068580c101011881c10404078580d41040c1d480000e034034901040014100c5411001d0f20240e034000e642803140403aa411048800c45181c98041004086034442c003090b003100004659100d000b59920008000a0030101e5200726000707402007a0400d003500020001c0101004581c107615071004015000200300c1e4007203100c24801445501d00b40c42d58248510100700208004402400b440000802088010301c580001031f01c0310003500001e00810385000c1010340c14901581d03c1d1802505040d40e0140c2d841d40200401e0f4541000c4814028007503030081000001c8006d82c103107450b03030103174025041400a1150725121419a02c1036051b00c0c414003210724075507a02c040c22000e550b4940e202941c000881300300c6a90f00780c040d50200d51504031100c808500ca03503645024400b2030308021850551124009074620181da480b8000c4000381902e801c10020038148076080420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 197061196 1250 197059946 197059957
    0x3050a020d030228110a060204061103211e01090501060315060801031502190e010e010c0b2d0106030f140f0610020c150c011a1813140c010e01090b 65
    0xc050018042c40c8813a03501c02c44910000990100c100c5240c0300715864228020341c007c0c4115070000f59140501c2078040d00c00b0040f41d030181c042a42c00b103980c2c0000090380d105480041d00c01040c08030070070564112503a03c2d60707095008000c25880080c0540c5805409010b03510203440702c21075500075400c14069540c1082005055076000244140042501480b00c4c00074414020361542094082502490640c2e01561380207240c80c003a42c550060400a40056507a4245030000a0098180400003a44008101c2010303c41000000703054202d03410403a182c990105080e0040d000103a11540c5103546480e05000310700955694a40e60341452800b040600d01c800d001a104a10031010301d1160f4006038400c02498100c400d004010039121044851107a6850380071541e411955424075201a40003a005624000901030180c1140c030340800d0021107075500600100030320060000140b600340400e8410a495811901600082489084007000900111600780c0000d040000c44982404824000020303140b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 197062446 1250 197061196 197061247
    0x160f090209030703151d03031311061b06071d010c080711091306060905090a03050a1b03030203040b1305120d0207140705120c090411030c03070303050a020d0302 71
    0x40e110007201000a007050500c1e8006410304034119000c43c940384150b4030100d0007825a0801d051101080000c03d41c40b03005c01c4036161543c00c200191743c004a0314050b01e8821034040102030b6071510b860b001c0000074040344c7c984010b056074401401c01c08880e4110101481a1201e10400c000d01031640000070010789040b00d000b05440c401240c0802005100c001c000700241005100d8815842c0044800450340301c000c1055403907a00708800045c0c2c0c0c000a101d4940074000940141020710708a4605a032141d0050704550100608403149003a40e910690882c0006403003076130051707130b603080a040211181d2030143c81e0619100740b941c03440000810001c0e2600451070350400351900c1d080c5450b00c40e0300034000da240180c040164a030884d41820404500941503c0d003c5902c00e03902258a940d03a40d07a031002d04034190b04003003080c003c035000c18400640301c0c48000000301201c4000304c540010034208441c6510480204001081c8060010b405000d025505200780ca01182064041d1044246840180c01c0c0300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 197063696 1250 197062446 197062451
    0x306030a150f0501080d09060c0b0f1902040b0304140c010f0f0221070b09031215060d0f0507230d11040b0a120b010306080a0209091009050a05160f09 66
    0x41d14a000280c020398007288042900308015a07541c2482525030880244401c0050f450300400f0403801e00070441c072a00c4680103c03000b5955651025034540081026204210141c5c01513082c031005ea1084c00288044c10014801940b00e0500d80f4100a08452085480001c1c0d0403554040041da40d1189901544120030700e050701110300c200b80140d00f0120005440725088400340d02079075501889200500ca41c6100d0005c0039034030341d500714000d500ca000300f0030003500c40c443c40000b140042141080450072158000d0002d03180030b8503001024101c400c003942102040c0e4517a41080b00361904866012550024003520303005a410401c19103160f88180701c1d02c1c2142aa4030484212015103102c01e03200581694190580d60b40101d0f14083c103003809076005414030500b40140c1751b41e154406e000321350480d100e2030000c0c8800ba40076402c1240c1e0500042c05110144036a00e45030b0040c03191030043d004481c2c051005014900c0e0b460a01c68140784484110202500c000ca000b003101c460015510380c1200d2480600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 197064946 1250 197063696 197063723
    0xc091a10030603031403072f0a0b040b0c030115030b031515040b010e0303090d1a0906040b07030209150901030f02041205070909020108060d050304080607050315151c060305030403050609060702030306030a 90
    0x3c3c4d03043c0201901071280922038041840b080ac072000500da8040c034052010007085588200d0000441c0c03009005001050b0001d10b080c103441c41c000d800c246034042004050382c1041e089107e8007580414111070070410000b1032038601000b0f013081c0c0304560518600707203087d0301100340d01408079603240f040c01030540c0202c00040e10441030100c400ca82c1d02d20080c00e1007099a180c2841144599074140980c0c064441040c40004903100c0d0380a4400c0381c0500d080501001b580b4802c4021588240d00102107c505060f2201034465010006100600103030020380542d222195460a00a00d040c0680e0042d0300010701c4c0c02ea00d800942c2e00004a150b02400499a860b004030280c5445402c3d40202d80c090f140602c540030512840d9900103028621a43e2551800d44195480740200000c038540c00b44d8416000780c0802c0707084040a43c0d414140c03c000003c11011900740c1e540c0d07503500c0ca03561169006962581260050110f6000c06102040d0403448130310003142142400400280c48900c49500180381482c803112 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 197066196 1250 197064946 197065007
    0x4060c1107140d060f090302070e011809050f070b0a09091103010326070b040303051e011505070c0308041a040f0902030a1d0d020c01020a0c091a1003060303140307 72
    0x10707103c5040d54480000d1165600a0410340e002e803402c0b07a002c4001d03001e9120007003480c42c121000c0d103040b61580d090340400035410381300d20300003040c001b001550300d800760701c50032044c03003404000500041912000c441c2e41e80800c110020001c40032030b0084500103003803031400c0b03290381080000d4906407034000600e44165030f0b02c109030083e81544114402510035001ca000400d0100c91241a8461030180e2014001c9541e100902a04030004800040001c020b4600504c8040c018400c880000500c5085c414681300d010b440d20014080d181c0d004584216001605000c4400c1142141242c4010302e41719600b41030400d1200f10609580c0c0c054a0500da0b0b01000041c100102508402c1032150030501800d9403015041c040ca4442a40524080c05842601d103841115440011a203841d507030044124000581043d981c0c0000d00090800450482540011800300790f4884c001d098050a2540740055000d2131407a000c0c2051201c0800001c0b40181402080030864200f6813500408807101d1315046011583e18 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 197067446 1250 197066196 197066209
    0x60f021201030305030a0c14070f241b02011e020306010e0a380a0815040203070801060201050901090b0f1f080a1109010311060f0c1504060c110714 65
    0x100034480c845010000418190008020740c05800c0454040c0111080c061044e503005181500d030550700c140070401900852120481c41001034403808080c411001e03030203108080c03c08a503494070b0085554425113800c0c42c002d07449030b101207403445c002400440390003c202103040c0350032009031040d2a00000019003982c03281524100300400140290074081c2c83e00c181e00030100a04071544160ba481c038060008048407110300b1420148081c600320b107880740b50070040729014005081c80b009800b81e210300700c1044e0703a0f50028512403100c0e41d0780d11550350b140010082c2510009400c410890345045074070000301da4608002988012095040503168580e5aa20f06d4003001d46446400c040d003c05d10081a105004030f00051918080d01900c04044e58601c00c125040030280720040ca0451a4000e545090170000c0180c01c00c141440440b0303040040d002103041c1000c03504002c00ca001c00b001e004100401c0303950300c01d50110741c0c154034107400b0103000029015a40c152500540c4403065102210428540c0c031710 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 197068696 1250 197067446 197067457
    0x303120e07090204093c06030203010e010b0907050406090303030b0d3e0a05040504051507020c0a06020d0806040506061b03070b010503060405070504020304020a030b090708121303060f02 82
    0x1012100c0959442c07400e50020b40082c0550407107241040207005111190f1000000c016840201884101c030150080410500e48501445001500d403000080580d40038410820b0043c0808008140b484800e407c004803444010400000d10409000503c42da981c007040752401d6070f078142400503d001c1200d0004014000140c0010004600303c100441c3d60310610003c0c2031a050040d140c0003583d05507c011000e100c0c186500540c0010041d142000540b60640009400a004030152a14502007018400c0c0c080002c4071140c01503485103030301840380d041c00c0c03103458024035051000d800341228054005081440140ca00e5110f00c0d10350b130105100f661000c0498080c494204200d1001d05110310711a616034001c2d5406440c4c00e40003030000255800c0100d4401d1207564080042c00300d0074201f00400000703403c003030810f03600300c0760344600440040c2400440f0f03405030b0b001d900105a9076140056891070b008800c44044c0320100c042c40b212010b040c5440594054070ba01040100e05040e0b244544002400340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 197069946 1250 197068696 197068721
    0x20606010f0c1506081011181518030613051507050408011a090106091a0a05070c0801140a0b01091a0c032a030304080d050613060b09010201050f10030312 68
    0x300107145583c50319a070700107030440c0c2d00201641c0104000d000154221442141082074020b0304101c41c244123014a03840745115400102202d4034224503070303013008850700504030091060580e989800113070b02e0104241644400110f140074900c0d1800d5403800d0319001c001c0c031111100e5070041d0120381d00c030b4007030710a5a015004034802000f14440b182c4004031050900e003491800341c051a000030413502d1241400030180c03204140b4219652510b070f4065045903000111903c2049014400da1000540101c07400000303010240c00490b1480f0468184a01c0c0000581400b44051801844100590700080c40f0012101030985d566070902050044051a2141850f944142e00002030903000d40703012050b502585103103410031020070003200d07218556284019a00903090032800d100103400105a50081548084060300c0700320003c500f00300c2502a516070f6003244644035030105501c035a95a09200d020781c80004c50500402d94180b03e507880d41e001100d408007038104001e0000741002c0c01950f070400e400c84040e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 197071196 1250 197069946 197069963
    0x60a03240603080c010204030224030712020f040603050118270f06020403120801080f0c0f06120f011802031504110c0d02060412030b0112020a0327060e0d020606010f0c 74
    0x81e2441118007d6209000883c45070a2003c90704032419420f0300180b00302003030400420315544038041e042e18000308810b44407010580800c00d00b01200c0c0f002016200034442924081a20350400907041400c1c62000b0390084407615000c0300c6442c144034103134000003c42035000f0407024900542480f0010401100019102c94000140042000341c00400d0725050308480e5100c2d422a603c400049445020031401c8010300d80c40981c2c0c203c0a8600207000450b41c0200a2800c0c0c034120006803102d00062048070b1b01a42014654010080015200d0b20214424500c81c01140b65152030051122122990401e00740156903036445030b024084124211421080d2032400c0320720007108144c1c0256210340031503045076818507510b250f50341c0034043e02030504451416180c0f007980d020800d00d00342c002d400034131079401015214203001a004404201c0e0f04800508800c082c1e1180c5c0729400c102007500d44005140d461070703208040300710075941e01103140350300580246002c0c6601c01002d070044407204d014040c042c04086 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 197072446 1250 197071196 197071207
    0xa02090a1805030a0807020f060a0c1205090105011a0913150f030803071704111002100606020102030411010203090904030e0d080307030209030c0a120201111501031208060a0324060308 81
    0x40004040c110250969a0b560b0440d07942c10070803600c6402c891015234155212101081c40018190000324017403185140082d1039403820340320032042e50410348003407401c2e03507481c0d005200400e1480d048002a5104072040703072400201a003ca00c070003034a5460702c0030455a030b8140c52003900d42400600018107a000f10401915200e082880480d8020758420000c0f5640310040000550601032080c41241c02c4140740507015070340d90622402203c107001e00003c500a180c0081c0380c0c2000e5101d42d0b40985110390005031a494107103042032120744200319103810b40d802030100720401e5035014a4207502c03903454940b88181003203540100d0558940340d2002442110080104804580d0580c040c2000401c11000c840d00105000c0a201c0102003078060014490410300003403003d54083d5801000c3c20f0055011150043d6504020a2600301d003038004403070b1082900a103a42e055130000b52107410100c201d0301211040e2840e59009440d90364001540100410100030300c405511300d92041004540220341039680780c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 197073696 1250 197072446 197072453
    0xa120f060306110301060306090506060a050c0111190e0901030b01051509060d02090f04090b01120f0506010f080708030f07031b020904060501050a140d03050705070b07030c140307050a02090a18 85
    0x20303002401b688000900d410b00c00a40b078245802018000d0601030b0200e441e080342d0101c100d032541d20014049070559280e4031001036079002c20703004005070700c1d080e15031114200d12010300a2030045c041944622500b40c0d10010302c04200100782650441e042214000e03100908000000214007410010660040300802da90b100799441c0e4000340411001100c034100401000b2082204950301144040d00c0000c0d0640140031140e004030720a0501c500a29402c0386891035036680b6407500300c090f08420f040707020b0640704000d840802c0001e10050b1103010042c0d800d04103050094803003400307202000307401c0010040840700300079500b40107120741a802401c690000e16250400c00d0241000f03205032400b83e180010000388940043c0c0100e5180900201485403031036554800312100d0b045500140c609000380040051414110001002414442c0d152a103802e109400d0560052201140212054100b001142e0001e1008905d00c207410354100c0304a640341d10b801d81c52a008284511070b20072400c08a42140050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 197074946 1250 197073696 197073731
    0x2d0b0d0b2205071d070f02060619030f060b0f0a03030e060703030204031a090709090305040e1e090a0b060904081215031f0b06070b010b0a030f0504080c01060b0a120f060306 76
    0x310750581d88590994845c4042203c19580070b0303000303e0061308404082541440c000c14a103e8407a0040c21a01981d81c0740e0300c650000303d0101c8130407181e40d61b0343e0304c030148070342052080000b12407000c0792501c1040c5d2840d180980403480d00815180305440000b1048105400795046d68041c60700241e05815200c4a001c46e4072071448252000101c6208000001445400a00490113a9503050781d9090409150001d03000103c940503142e001c450303c0300911999140c0045822612805030200101151102c600700074400c0103025003014040c80560382080040b039a410100c5403001d6156074a40d0080c1d450480780501304080101c074a43c10300801e80d4500060700941e501c0e030200c010840081050004200c1000101c0c40342d130300000d0140700d80c42c00401480003150080c040f00d541c203040118040c203039152290200c5074120b5048600c01390111300d540071102d00344510310241ca005d080062500c0700c43d410103440c84205100001403c3e89603102c01c41050400d4114100035640501c041c001d003801c2a03c2c8400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 197076196 1250 197074946 197074979
    0x2130b1608070b07021c020c1201020d050f0703060f0e0f04050f0708150a0212011a07060207061b08070503160e1201061505090a182d0b0d0b220507 65
    0x5200b001618000c14020711449003c0c1b06203a0000c040e400d048406221100d40880c02c0c2d500103542c00d119902142039039016052051540208240312850588000f9007114500d4110f490a0081030905001503e01000d0058000c403018030182040e5895142503441d0441c1c4245e0a400e50040c66000511402d00107100044142412180351040d0303514503e50040340920300d0707115043c0300c00314010008a590300700e1201150070301000983c40c08040b0384448090340c0c4207140803107080e0341e12131501d04141d4031954151101d64952030705814074200000d00410700d00015182503401d510070344101140c01c0c000c681e40c00340c550b4098054040044550b07011030080415105070b1481d0f102c0400600e603a00e00c103800721600828005d01001c2c41509240101102c83e048414031810660342d01141000c2503025a08000070010b440803962014582d0070340070042da000e64041c5030240c94150011400074240003040c030703844104440303280d10142d03030401c0d4001e500c819484041c10034041d4440203c1d6401059008a1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 197077446 1250 197076196 197076211
    0xd020c03011805060c0a0207030507150e0409031d04020c061e010503060906011208040b0c010603110f0604181103070207050307270c03060b04062102130b1608070b 72
    0x405001c2680c035030903404070080b00610300d810110019400303041c0700d0064000f0b43c030075104940c1e05580340d541e2249845d500c0d41001141102442c0c0c0c600e0030f503a00410035010f4400075602404030020030368025000401c1c00e01743d2020f0f41000204003005880f1641030350aa034079003000712101c40c10910181041c181c0301c55018005030074818004601400e002410702c4c000d042c0369000345440ea01c5d009060100b5191003004680010040000040140c1401d0103000342c80d5109000080d00d40c6113140c0121115518100280038065182e8000d045540b100240c0b01101e05010200c0e0260134030072403403001003a100510f10003075540030090141240d8000b944100765102230303080310f0407140c032000260107880900e280c9880c103c0000d6800c080d2081c0a030410341130f501c2c0c1803c001c14003e8640404c0702c26908280c01500005d90402420301026141814801c00110300c00c004610384151031420340c0c03030700440c0d010f440340054000515646082140f0103170380d802c0742c03c0801e154540d440c070328111400b440c040e20200c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 197078696 1250 197077446 197077451
    0xc060b0402130302091b18010201060f03081903060602120c010603020301020301030c080c0a0b0a1b05060c0d060b030405151902070f060b010f05091c0f03090501020d03090812180d020c0301 83
    0x46d07a03418030b802d13640241e41c682806e140c24003d051104884424083c0300c0d241c115500d84c140094260903000710310300514458030b00c003a1500901c110300030200140d82100340070107040c000108011a008036000000150b00e45d0344981d5a440c0c06005405842103a000941561001000200380200d045048042c0c40004080d625060001c10800200701442e000b000c02860b8100425520f0074010300d070320160303400d03d8040214011426114542884001c903410130442100007441d00d40003007140301e0702019115200616007541041c0d15030564a0300341c0382039001c030b4054075008501d007101200312800781700d001800c055503501c20070b10700031481104410302150910309182c03c5014a6003e1005400c14009540e80c1130304021051080025104070080b00703ca1054214452002140382001440d103030340d010303841e001140761070034000a1500c0080d442c0385081601e0904070100058000d000c842c1c4242040c00180b183e81c882e0442c41174142c41003041801988154500b00d02d64035000b240170600060224001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 197079946 1250 197078696 197078701
    0x170c030d031b0c0f020301060e180a1203020f0d0c05190c0b27030c01060f0f060903030503100503030c0c1507051e0a2009250c060b040213030209 64
    0x9030300381c955031038000920511100002c00842c0c0301d0044039401901542045500b4103c0c0d4002c42c0c211907603500291215043d180c104082802008241e102a0340c840005102d00611501c42c00c03032038202c8a00740400c064000580841c044d8104080d901c600a24040030001082881d0000e82240d210410000c4060749060b12501c0301405444503480d29500002449060782c3c603c40d40c100e1546000c2600210183e08420407014000d041003e0880c0c1ea07028400085c0442c100380383c0a03000300e6260301891803803000b010140709466112500e0412682d050034565120703290b0a00c500401c040340c0e00300d0740c1c052201080c1030100c1040014040240c4800341c40c8a620190403500f000b0700c2d8032411401510940c00251807000b089203440c41c1c0b20003001c514042e03a400499540e1039501400c40840400b04031104003280400501c1e240c284103401c00c0b040d18030b9000103603400c11041c000026414a000900c000701c0030b42c2d000d1118a0b0407003031700c24000400440d6075415210403006041054001a03000740f000400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 197081196 1250 197079946 197079973
    0x110f042c1c0f1202042d05030118030e030705120102030a0e03030912090f090c0403060b0103140f04021f050406080c070b040b040311060a0e0c01030606091202030106170c03 76
    0x1086441140b0340e100c0081d90061407080d26a145502c4072000d40c0c503070030400014581c030001c0288401071036604904c04035080300062000300000640055110ba45811142c2d84502100343d64030301050343c9402e010390041c886000090070005580d2200750003d00100c001c0c00d4040041d4002c40c45a554404100408000480210b5a900045441101d10340c005205107006880c2c440240c900c10600401c000b50301d58144000c100912000d0313811421000010405000b080180c1c029051280800e1804000a003c801030520220402900311000e00b00080080380542d01d508100000074071455003202485540030f20700524645c0140b0500b000900403d0110f4a410020b800f1250b40d103400405048050f121601c800c0803040000e00101d0901c038044581c1e5403515070900c003a40c425070148400181c00302c00061080e0034030200400f141c8c1014a48a03052090a0700f001241d0140c5e0f5100f44510b44192449c40442c0c018499900040300e00b0f1381c0c101d10100140d50004100610200c01d9003584c000301c41100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 197082446 1250 197081196 197081233
    0x12020301050f07020304050613050415031401020a05090603090f010903021c0e090705030903160302010504061103131101030e0f010c180f0b210f04031b110f042c 71
    0x41c1c0f40c4006800c100030804c914a8140080c00d2038410f16120007428541e101d001034122180b1803000e94a11100410420904c520039055440400700e20009520701011140000d207684290080248514070100216840f610700304460601c0b403810340300030403201c040d504010b5510034001020009202d0704444035201c0e07910420094807aa80d025040070161f803610007041c0c030ba0380c000900c00440ca100c00d11440d00c00080c0c0f104129400e034003d800015860820342012025a001c0d8080c0150005c000c2051007180c207011010091070a42080c0561003040b981c600480c042c2100b500e0080c10340c03144480d0300c40e071307403c040d48aa0004d40342e541300c0319129103040c4820380c1c443e040384c03040b19001c9041e003204020646011004080740318001d007407141004002500e030008000b081e980c50b081181000c0801c802c1580141e806040300004070748080039a1030036a1400540c80741081c11600410701804240800d417226008000c0300e20700c0e60014940d041d9400140d00c006008103a00508030702c10220144210308441 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 197083696 1250 197082446 197082451
    0x30603050f0c01020a150929010510020309040c14040b122d040809060c100e0f07090906020f0c0a061415010e0d12020102040504060905070903031d090112020301050f 73
    0x44e00540780f050303003030384444490740c0300f0030b105801e0707151030304030580000c1e4200151200400e203220a103080d07200c511013000300c074040c142c00c99401005040d01c01c9407c1c680000079900c40e100e041710082201441c00320112a5030203004100c643c0e05101241c0484c2c42d00a0001a08030580391400720003140d1784820710b61420051070b03042d062011000c0002e207005500c2240515500a000e092820b00d810840d8000c9541d65000c8150701d2716907082401481e01d103503034500400d40e0004a0000421010b00b0003003041d5281c03006440b501c00b40c2e5540321018020003031690117451512403003019480d21200900000b035203400710b021044546518120509010943e4140f1250140003207100c2c401076010142e005543d65030f0601e05032980081610280700c0050402101100b10f01c3c4603600258499144c4414013003900c0d03558010805050421041000140e446146082283e4040c80c221103c0400c9440c6040c0341081c00c52501c0d0810041000401c0d40c4400c0700b82201c5040c401e900030009651601d10890500031b09 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 197084946 1250 197083696 197083699
    0x90114090916030816020d060504140c06030c1810020c030d03021207050d0e07090b010f020a050c06070f06110406080606070308150307241404120201030911040c030603050f0c 77
    0xb2041403020a034007201402100c844000c034001c480100da000600011164031003140d0080d10742041004100800e0401d56410070160018480b00e00d0784030024902c1d0000070003551043c00301141125180d00d883c03c51000342980a0903040e107000d40a2402908d40801c01a07040c0030b0300c01c00403601a01c0c0c0c440e00c200c41c0000c00c040241d0200781c581d40030403100c99000003a1051507a4840e1119154500d00b03104c14002400c1c00e00d000203051380742e84009400c41c1c0401100f03005642003a400d50000c2200800d0034100080b007150b040c0d5440320585400c06100c005d1200140015140c1550b151080b81040c1c024015203c040d01c0704945175450b04200a402c2c443c00313000800080030740d8042460200480c003100705182005007916030030b80c5c80c0c43d02d08280703415007100240700440002826120a030031150131000301108103003803841c09080ca4141402c50244007002410155610000020710200140c00021008003c105201e200c11842d00180900110701042d80d5a004c0d045210101c54000140c10000110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 197086196 1250 197084946 197084983
    0x801080703171c1a01020c0603060f0a1502010c120b0607030e0406180519050105031504060204030b0702030d1a0a030204110417160f05010905060304030306050901140909 75
    0x8580e100d15030a000c6607644041d0490903c6a00341c00c0f1044000c400c00ca01045400242840c0e001480303860f091180c01d0349a0664001499607102c07616020100d0394008802d5984140d0441d555003c9030340400b50303510020201d8900b040880601c2d5042d0400d410942042d51800c410500314100201258600154aa4803510412040c0300107401003d80450601c0c0091002480542d903030f1621842c20700c0205a04109541c881c10042820040350f0f58227480d00e910441000a58103090110b0b41c1c070b01510032881d5207208140d0004c2d08000c042d40444024552050720030880307040c6000003a640c0c1d000304401c0b46040d402d1010400820211107840300442e18020200b41c3c20610351740070301c0300414000ea9a5008007100304400705401030160098212100703914000c215046480800504884082d000b07a51001d00c0d40c1401c21803603900100074400ea403401c481e110b03980d89482c0740c29002046260b00082d000962240005046000b1000300c02000d00140c401c4840c995408060b151200c280f00c525408410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 197087446 1250 197086196 197086199
    0x120907050d0b07120c0201020a1d030316170409050106020d020a0503160317010b030708090d0203070201080a02130b0d1104120f02060d06090207170304031707020a0c09060e0708010807 81
    0x320341c80b03035540c0c00c11014141907150b002d60703146a00c20344520300719201c0582c0d00082e03812109a48849414203940d500c0c1d4001d84e507010b4180c0000d03164415000360400d803501040c2c801050150b004d804c600d50b0481000d16942e1681d0314004140a07000906c103050141c020780320250307a400d00100d20380b42c03800e5104014520301480c142d10f07101c2031000d221007902082020184403407150064040c85001c0c00d0140079160322071800c440010311080004041440582081c0e900d89585500081030b01c2c1c0c4254242003014940d0b82da2440c85000780116416410585084d05000a4002da903074010188650301d03960a010800c0d01ca42c6210701803203540725002c100f2600303480303440c0840d44200c003407084148000d001500c0d004020341c00380280d4119030481990079900003001000c00c01d42c21507000341c078098218058118070305034802501d40024250030100c000cac085400142c82c1c40c030a100b00c5840a902011120440f13454200b154000c044a000c0c075034041c4590408a00c200d40140c84c454100d072800801071844a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 197088696 1250 197087446 197087453
    0x1905071d0601030f1a1e030304080606040518070905060409060c08091c0206160311030903030105040b1813050115090f05010603050c031602010204150c030f0e130914060c120907050d 80
    0x4521b4124002c0d0002000440301c00d03030b580900080c4010800d0310000d14050401c403040004441d0041c001e810054100c1034403202c007000c00300b24442182c41a8400050a542e058041400b42401040040160389080060a14030f5088640316018139808000caa4984031034198824415402d290030001503486040000c5094002c4640407080a0480c40d012503140700e103503800f00e800d8106440b10852500040014819070500e031162411804003140c1c90304d84103c00020071000c880003d0a1045c0c0303021081444814003009410904840b14030b80c5069076501e6582c0108801031150201841c411420300b00000344081c802d005082c000c4031500c02c0540b41d072b1644401200728004000030503040d55000d00c0f00207086250300320041c140981c00d4681e800e4407159441c0041c02c2210ba003260b4424070044003c5410162220040340540070311310f0b1000130f0070100c54140031401000001050109101c0c2004220140e440d50000d0801d8100c040201c81c003d40360f10741103d8940000d4054a5000ba030982cac80007020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 197089946 1250 197088696 197088709
    0x60e1009020d0f090c1805190902010c12020d08060901061b050a0c0b040603240b090402190e030d0305090c060315090109051b07051905071d0601030f1a 67
    0x104003429030024243e074504012105492144800f6100140042c030100042c00408000e8103017800c00600410292606600c0c4c010f402a284034050b0045940d280d0440840e40540c0d0916420b03500420700081000c201d0000a42c2c0e402008100350020350b40c4004035030799017000c1001c00e05030750541e20ba4100c5001b2503143c0640061004a054409110340c44c801d10110f1103840030207004d881d0401c801b41da00c0c1d04080000d0145c4516060704600ca0151610200c43e0034090401041542c0468403550350f503c0c0c2d40c60018019024000c068103004210303940040b00d081e0400445200ca0320140e059601c912280d00003a000c035003040312015255002040c040244c0d107400780045504c0b0381510280c2c00c8001c092004a242403030240c2200200d244d0361014030507002c2841407048444541015240d01c1c200c0c0a41e43d403074803000c0710000c0d0250400624100c0003000424080140034001101c054900c141340007684500401e01078507030502083c90710302da0380352400c002d0040744003100640d10700d0700b1403600c2e81051201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 197091196 1250 197089946 197089957
    0xf030712090e07020a031103131e08030d020408010c020708030f03040c030807030e011e090e09071503060f061b1425051008042301150e0a060e100902 66
    0x1c2014800c0c0116a04051036103403401551242d0050001048070f250240810700c2810060207260701c01e00c00755200c40c0c5003c0301d0340d00b59041250748004010042d000090000c00c1c54001c101c0768000491907440d1410558042c104462600c00280620840044c3c20707038a80807940030300601d030781080000c0420707210381070010740e00144102c0d0075414165503a1241041c58124840850002d0301201c0903400765a80040d111015006000c1912910082e42c000580702c0310852284a202030701603000106410024010700c001003417041e610f0300c0d031061580e0740107005200c00d02807806400342c100b101003000c42c85901c0915481c01d03441c0105200751a10b440310351100c880b203407007101b40748594240c0c81074072041d2580e00744980e4050f03e41d10180900300030800041150f5044505c01f0800d9031010403010801040d00c41c0f100802d510b40b40748000c9007a4500a004d0b044c0e0f00320b0b0303110410041c4800030f00003840c030100c14440d00244c401003181325291100e48001203030955001c12a842000800e2110704030940c000d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 197092446 1250 197091196 197091233
    0x301230c190503130210050a031b0f080402030a0606030b1006030606050d02360307140114130302060a21050903180604090e031b0604050601060c020f0405090615030f0307 75
    0x242d04d10b205900149040f070b049000500022004901045001d1305070207118041c400c2600b07000d05821400200034074466143c2c0c1100100701d41c00000c5810741d1002d0040b0303010103030824401c1c0592500c0e4145000d04000c01e85080d8000c0310159400220148a0300c5210150342c0766950f020b2514482d500b4440c003a40210000c0c41060b501d200210190415000603200c0482210036110340c800b216600301410b001040e404014001110624500a682d04c9020505a40c3c3c107841e60300c0d100e222001d03408640e041d41d504000e4100100250320401a5007060342c11200c18070f468ac100880f45070540803a01654030035140c030f4090b58001e000002018178014644800100c1c00307041581016030350920001550400c5d620b480350f41c1c10005010750107a114030725840e000b500200041109080640e00c0641e103200c144200810421a6000c2ca011956144250445d6100003030003070256081244001d0745589058802c4040d0415815161a240c00d004c60039581306c400d0000910709140b01a21500381c901748120105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 197093696 1250 197092446 197092471
    0x10f0605031e090d090b040e010b1c0c0c0605060d0510020f0c070f1d010f0e040f0204020d0e0f0a03140c0703080a0207030b060405010305030315040b0301230c190503 73
    0x450303015442c07a500903c2070b0324000050440810301c00740504260325941213030007850400c200c140807241501c0c01881c111003a810505903160118483e4880d0311034030b02d10786034115003000c85030740c04540d00c0b40340c1c0081c007030050004004c182c8480e0208002c24142c040010b0540d0081610440c1140303150b13003e0f2130314031031409419161402c1d00f21180e08044040d0400a20326824940500c9a00c006855580030b928084c85806255410428804c1c01500d551181d007180e201c402c800202007102480521000c00d9020300195150352a185114020b0035030300904501b0307845584030b800740e10000002c503822500d40513140d88080b030284807180f42c2c075680401d540442902c95a00008002031b103400041c13510800d10307400341c140c081c25407030310400d550405016288074509000040c4081000441101d030402485042503800140139030125014140d0852a140c0c5940b030201d05288140d862000d045c000c00b0741e28000b02d010340e52504942018003d6841e14000d0035900e156401c00c40e4010301c001d40c0c0040225049 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 197094946 1250 197093696 197093731
    0x3040b04120324080d0207060804110102010b060a080906060108010b070201050c0a0b13061505010906030e01090c08070302031c080f040521120907060e01030c120203040c1a03010f060503 82
    0x10b01080c90f81401204141a0703184041141010501081c802e000c0305102400006250200c024020030010b000075000d1045280d0540380c682c003d40c886400d60700c0c05040740d40c40c1d103403465000d801c0440c1140c1d10040c41c000c0000145c404d40c4602d0a007810790712407400050402c95950011541c0e600104505880e40c4104c80102c1e02055010356118410309120f070f90b110081c0402d1414000303035040d90401c00f0392400725034014422a070b0040e00c034500341c624516000a001c4c45000e03085000d000800e0002d8280c0403100c0010403081e030089602d000f0b490080c2c048400f540318505000012040c1006030b807002685400206203000c0b0441d03002034026005004841c0000d01c0504810042c50b00144064142c0c600004e11010000c80d80300001e500c001c91030003406505241000181001c0b140810160400d503951014118081c00307040c1c12810494015000c44d1030b440c1c245080d0030a81c4450041e6103245400174020b01202e03248004031b03810303100505500203119181c043c0666150704040c013180801c0b10300104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 197096196 1250 197094946 197094971
    0x30a1d010501120c150e010822051c020a020d02061b03030f0601170402030709050606040324110f040504180803091b040603051203100806090109110603040b041203 72
    0x54075028001141540018424500c0d04801802e11a8001e01440d180c10710302c0303458150085020310318900c007070030801000e0f41c0d1044002130520308001c0051742d00e864004080b0070300100090381f141d24030f0092306a510b940507401050781d5a00350344400a5008a440003ca8014204a00906486408480601409207518141d103003580c208541c4039000c0b0000104218156a0106030041360400c8401c40b600e060a050b00400c0d2034140f54000d201c003480d1941d021490079243c04c070444009603040030520000141118604007401a00c412840041e400d01410f02c0c88100c015048468182030100014a060b1070001480301401000041408a501c0230409a0104822200a51044e2000d10140140c0228045015051610300b158680a946880c50500020303000280f942100c0b100e0100d40ba40b00d559410701d0f24049001500310030114081c0d1820302044806c150005194203225046210b0318509901c107002c40744c0000c90780600107860a030042000701700030340b5482414911518004c900d8070420302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 197097446 1250 197096196 197096201
    0x702040e0f0a4d0f0a08060a0b0f0a0e0403020712120305090303101e03050a030f0e0f0604051e04050702031b031303081c0f0b12010e03030a1d01 64
    0x51007035401d01000a800500f030011052090a0004682484240485a00f0312100c04101480001402e40d011040c058400d58503a18031850440c401800d6a24580c1c50307012158481505450240b05a402e003076461072145040e5910f810420400b81c20b051410349005c03659210280042d20079030941c007514601054401c80304407020820342c000d1907400c0010240c404010101c500040110450750810300234050460180d07400441103078680700940d070800749042e83c0c0c001c8205c00c0d9400103105224030790b2901c00b0940c009041c0800d11905440303107541c1c0c41d80e030028400c003041843c00055000d00c0800c418005407420341452071400680c001c41c442c2c0c40185202143c21074070250380351009684013044140e546580d0321740b1304004500b10000b66040c00b0014007001c16280303050000800c4d105000c81c0a0449030505500c881101250a005101e0b404001c242e0784014a4031802d014010300b007001600e0780e089814019400400c0e0510004c500d96581c401101004049542d041c0c1d08136507510341c081441e81000d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 197098696 1250 197097446 197097463
    0x13210e0901090914010501060503060607030512090f0f0606031f09060e100b0609090a0b060f0403061406030f0619060e0103060506010905031204050409032a060c0e03030702040e0f 79
    0x1200020709030f0388030300384140207207540c00103800e0583c1880014005a6808000d40b5003010702601c21513140d50541c0f030155950301440507501ca004031a50100030303605200150000103181e6100560b400c494000445607140d1004494403030301940000505540800300d0030802c01e0140b1120000a131303034807140da1010700b0303264200c0885080b54001c2c450301c881e00400c0d1140c40c0442100300c40241c648141e040c04150412801800280c100c0d50355208428151110f0046407061000a40720741e40d280d4503882d00350001d1031000c0c0140d582c00c0013036001501d1411b000850501a2041100501590f07951402400e0f007034502121140903543c0340c46000480340c0c3c107400114041c51080e40003261501d0a074000500c04241c9070711891081e40403c01242c0100305c3c00301202e050f20010340d00400d01c200c0c541029242c044204003554019000071140114844002c0c802e444160b02c5000240a40d4041d81c00841d0291160320701c0d181d141c5c00404c8a0001854164841001c07000740c042a102200c85005a240c141500b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 197099946 1250 197098696 197098709
    0xf040e06071815170403020106050a08160b07030203031302150a020f010c020a021c0204110c010b090604061d0406060e0c0c21160c030203030301060c050613210e0901 73
    0x4880e07584884024000d01d00050145000c84054518080d003006100f0f240e1003084c41528010079000c9410b05100b90401c4014200107045000441da850314500c0c0d07070312850f8801d0003a200d0403940118000c00010100c0d291540c040d0300841c103544604511104142034000101d03031110400c02040001e01300c1001800d128100368001c0c104c1241400d00f06c42c25941d030f070481641150003900428005075141444100b0f110310342200e0250707906ca030b440402c005005902094018400200e01c81c1c085240540207001c04007401d8601c1441500c406051100341c511501031559180b02003d2130125110400b0f01241c6e11038091f44000c10002d503514559441c6501c00d0350000b000240000700705c120030741c042010000410400b5060b01c03104a51340c0f0311250a015410301522014140c002c1d5905010004103c14081c58005040d26078a5945250181c0010a41c08084030070340200f500080a000e40000009403043e041400c0842e0106d0001082d00c0140e00c46a65a05000c4c04d40100c401c1074585030303012400303002c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 197101196 1250 197099946 197099957
    0x604080409022b0b090f042a050a0902040303020d080103150209010e190602150403090611010e07080717120a030b01050c0604080319020c0c010e030703062f0f090f040e0607 76
    0x111300610007030100c01000d00408040c62401c0c000000d0748100c16850441607101003005440190b203043c0181c2586500461b0b10500f00d6001003101e188075401070085034441c1d02100c0b0150b00d00c040643c0d868100f4072000d0302d10b40d1204510011002c00c8e40050401400524100384414141c2d400a400c481c00009402001c03410540107018250b010040351000151094140201d0314062b5030007400d0b001240506000c000614508507600c643c00d4103c405c41d450409c3c01e075182c1a13240c2d034a2a50f1015284200c2c84802d82420450b5804540840c4411203d00070b05805403070f164120006801402c01648050b040103001c002c05007068805204442c080d610507040647d0301e042440307a0244d0390803401c2c81c000c045031041040504808000900440d003503002c0c02d000201c100c020b00003038105901c640c4003a00391420028005081440ca40d504030424500303440d9004000c02c0035455103c2401000002c144030102008500c02c0340c0f80001c03807684070b03801c0200041461182030482074104071090b1030348404030340c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 197102446 1250 197101196 197101211
    0x20901031a01050306091b131b03050c091e060702030f010c14090f0d0204020409020f190806090c0702030a0f0501090b070f02070303121506020a030f020604080409022b 74
    0x4030070240c40c0e401440100e00525107820000301845d1a90000e424213910700c105e408060115455541e80d1007421008007108022418050350000d20f405550104580000c0c40c00c0c000a600d000150b080c0d03819030901900a210640d800c10142441000350040144c0c40302051092800680d003c00002d130040d90341c440085040582104041d0010046c01e44222208070188105c0d1000d03100c2d0307030f4540091041200d1420480c589070020500a209070340281c07002d14000a1190b0405075500e0003001003c0c65002c00040d035402181c1d0417610720006803400b643c8103082001040f4502c0510001d09520390004080d40c458140903540e15054030209030f011901651200b9200b0284090400c140d0340c801053b0034100081503862000035125401400020207020440c1c0c0f41d29000001d075440241010345081501c6207151301c035000a55a2642c400088000580d903a040d45c0c50240b0104d481030040703900c20542400c1500300404c1e280070350003072014104d2441c03801000c10440e00300390b04c4030301d020311000d80e0028412 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 197103696 1250 197102446 197102483
    0x110c03070c0b04050d23060a0c020c030105070e09071e031a0f030706050c01060e0903040807080102120105060c0f0106060e03010c0219020402090d0c060810150906140702090103 78
    0x1c50103520480154109000c1003140e611503051880c00c3c9035100849a00d0f242c202e4040304544e8a0502c082c501c10b1040c6001c0225100060b402000b04070f10a4007110144c601c0401018240c075400c83c1c2c5030300000c01e45c180080050404090040c0c001610703042229400b001050610000d01c01002d6806c0000d0b141c80030f600d040004e80e41b200522250694072080244c2d2040042a40c0ba0398a120394000c20000150002c9038034029032241010386010501280e26040c151403899880d00580a40040d03030041c410300140140c0140308130345050340001d41030313200e40c1e18000812810f0f03001090002414054100c40c8451080280f040601810f11034542c0c80814440c6010b050031942c1600d01038065510104070501c045080c0d900b000091981114090b946060b07031408904c0c50740c0042001411070303821400c04903019030019119031092200b0301d52240010354500364030406850140605000c84c1c4005020b02c14140304100341c250041400d02201c0c5400701650200d00d0484090740182ea801141d0701c10b0b400301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 197104946 1250 197103696 197103713
    0x61d13171204150b100f0503060d0501050f01050103050c04080c010c03050d0e0d09120302060105130b130f0f110921190204050604020f0301090c0207090f1406010f0f030b04110c0307 80
    0x1110405e680c10308017401c5840001e080d002c0480d03000024080080f0005005070b460380d01501140782e114000744500d050000c10703c022140d0a00030280440c0c10640001c01342d42d25030f4151421510302a0081c060110004d006403a6030204903816420800e08103d8082e81c103403140580c0780d440400d000100580c0d121050000c01088136504120031111000d4000f40c0481d900040b95410350300e040318020524100e01aa0700300608080d484190803c2925501415007031280d481280f5250b05594240152807410005404682c0304540304041d06005009105c2142070991034040d890740f030408032422130750417400928600f4021408803503101039041e444c041181082e001b0184c1000041c2c82c01c0d03040104001c00c1c801d031400140100070005656270148181140300300602d500824252608001618000d5090750107010301100e510001d80c80302c0045805540300d8040341815a40d16680e091007800418404c40181c04100d507541c2d401602c0354264950401800014074a0b03210210046a9820301407415049 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 197106196 1250 197104946 197104961
    0xb24040608030417100c020d140403020d030513170a02120c03060103031d1008011d040201080a0b010917030c210405100c060609061d1317120415 64
    0x2450802008100c400800403d4034160342c485000da10401c80203080907490300620f000114441402c00321044034961f00401d40d00c0d41c83d880f55641030f18101880c00103804601c00c0f8031000f50005416051710021034810030262010320840c0c01d00302c82160780e0300f8103122401003e16489441d03810130111001107180c214030b12031141e03c403840a0f0141000000009442d4241484094107100c03c0646001c10341049801d03210300128001c140080704d003032402c1d005040303440074021020106101040c200111300003180703851140754141d440c111182e0310807045001034801e00408505100b4100004640d091144403428444c5002200031519000740149071848c0070360443c9100244e00da200f04458078840b001d4215415680705641d030b4402e0049517038040b80c08001c2d03140040e0981d0702d064008039440105400120031078958034103007030b64003000e001011802c84041d0303141d81046c040300c00e040700002c0407100718508498035070301d446003002d080850700b03100c0500c00c03a01142c240540c0140700661103924800c0741d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 197107446 1250 197106196 197106199
    0x13201002061e130c0602010209010e0d020a03060f110c0c0126040308100b0a090f0603060e0609040204090f15150e150f030a030804020f06091e06070b24 67
    0x145801d24042c44060002e5401444041600220010f0601040e03a900201003d40c0900c000c51400e030f603548007d000350000c01041e0b0000b1404540c2614524006104406064000b401c98a03200d00d5681da510081c0303080e103a81480b041d01c405402c01d14403501c84c05090464000c001412590200c1e900040009441c0107075600c00307003c0b211703a142c030283c800b40205034010b903d803c10a001d92126000c0150030710040e4010741d868400002e07020805584603019108641c1d4082c481840c454039060305074107803002800b40795140c24403180040c01601e004ca4416030003500140c00096143c4c000d4a643c0841c801078a1305480b0009000c480c0c0d4945001e5102d10000e09241083c030a03210b60600a40c1e5903101c4018000400a0010000c090b20b40c0c1d6a0710850100010010119200c4100d03e01e0302504404c0d045406903c1254040d0300e1501c1070170702100f1582c500c14020310f00501ca071a01c8100c4440c0051741881c09400034030501c0303c2c000140d030303440c481070164201c0c091071882d042071880400d0098400c0c01059 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 197108696 1250 197107446 197107453
    0x1101090c18181403040e011404050108010b01020c0d0c080703081c051e0601030b0a0f03110d02010e01080403050d0f14131e020613060810080d050904020313201002 72
    0xc803031524214a04440380c3c803500d10300d11070700382c1000301c3d1035030245030003ca0481d5600c40000602501d000070f800c510746010f46084c0410f070b0740d03905503e007251411101c143c0944c0104420440d149403041d002e006203840b800255001c15180d035015850444160021142c07200001b1b0ba804800080501c20169919525001d11041c079000b50715413020320b9500000c01030601c059001c196580c0c02034101031805e4201411488016503181404240c00245100c203645c4100701200007509820500110803000d901a1100c403c046888001141d42c01c0005100781e003004020700145920a001e4022102c2d0040c0c0401c02144405081c07085d4900b003e0060100c5a03094040701541c7d0010b0241d0005507a00b00e400381900552003110b00200340c01c0d200d41807849150f08000c66002c1080d58201b40381c14002ca05140084101944405015a8038200740c029039000c40c10900c141f450b1032409800540e84000f40141140c9042c01c04d940f500c1902488603108408a40c104c8201e00090070038402c4101d030b610070740c07008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 197109946 1250 197108696 197108711
    0x2150601120216050a080d0b0f100f12020a020a06050703051b090d0605040b010f06020303100312050912070e0601031406040504061116020a0605281101090c18 70
    0x1c0d1040c01c609402030562034000c00d400298612075425038081580180c185c071360300050743c981121503502103402400d0092500058000c1030801c510202c000450140014030608281c4000f82c581140c03884405041101030041c903c415086030001c0d0500f01010740060040708c07442e19100c829584000c080c00201403400f010416091a01d038580842308918a031010340e107620311400726400125020003c1c091a0138581032000b0003041c551981d04031241c070f0343c060252a8035400200d8a0748019140b00c01d80102c00103050012502e9010000e0300300c01a0b0510038a003104c56000728680f40f4000282c4442a082403008001d491448555150300190034a010032440e080b00c108a0000c5001410042c05a41d030b50002408001e81644079000a01051002036214184030501d0f005035840400c0c00c9000d0308040200082c054012030907102d220503604c00f00d480c00720702c8034581c607043c4940200d082e04000c40e4420042c5510020710461840340d014ac00140f1110741810310251020b02c21007485115540341486 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 197111196 1250 197109946 197109949
    0x8040b0604150312171510021c0815060403050d0302090f130e0106140112020c01180c03031e09051210050702030d0b120307150b0915011d0901140a030b0702010c021506 74
    0x6c001100d440c21911101c1d1810446000c91502c0981240c0444102c00f10300c65000058103d0fa0152150310035a601958018802c0f043c0030681c0603e101c000d01540c40300424000450090700a0402c1342070190a04000c0001d0100040203003640001a81d400f5554550b2181081000e003d103174003404c4454080549145041c000800781d010340c440b400103c50303000c00d094030341d00b10039000069002c0d040235030b000c0d8000460406403501031540c030003100410388102101c14481d581305054042c0e1100d03504d926060710310340300a101a00d07004284446007400783c03c080c0c204502d5140b1465004004e1035005640740c441d4030350018119110040e44900c207924100c00079080c1e80c800402ca0b2a43c990020700380c0c0ca00c24500502d04060200710346615400120b0508119400003255503c80740c41c40c00360380345150f802006590301070700c040b078185490b00302c0c80d0000103220b5003c8144003a4400c030000f500c0d10f85420340c1c071340391000300b40000d8644c0d10050f5168498032401c5a8100007d14503000035804403006820000c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 197112446 1250 197111196 197111221
    0x90d030e12070c090203090c131415030a150c09050d080a050c0307050a0602030a05010608100b0319020d0c0905060c0c0904020f03010e01240608040b060415031217 72
    0x22914070031040c005034070400c006091031414002c2c0b04a21041d5200e044c031081803030b190001d42000f503000d9a0b1032082101e503846980641c0034840200101c0c4a499143c001c03a520b0b001000300c40d9550103106800b0300d80001007400460010701117991100165120a1050040410119078001c42c49910b54010b4000800d6031001190381840c501d00b003141c1d45043d000c90f00c0b410350207050400392050050b0743e400d10034003209400851168050000820a50382c03188e609580b000e60581d1078544400c0440c4050110708008030003140c0200c03400b180108241842402082a81c2c40303a02242c01560300c4401400c08280c000b541100034003800c4034124184120380c10459900c0f04a81007803441403100401081c01e42d11452083d191800740034000703100c2600c8001400b4003070407550b18881030322521450b000d4000303000a40b42d04160b5040d540c5000f10f0742c640d0b454008907140c000d0011940300b42e44225202ca181030601c03406004510034401000d40700465580a0700b0b60040d01d0081100d00f0051040220303812120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 197113696 1250 197112446 197112463
    0x60f061003140f0907080307080706061203050d0f020f070c090b04050405210708070302150901180f0614250503040201090303050c100c090315020705030405130b03030a08090d030e 79
    0x548400b40c1d04d10b00b0503480c0000c50381c8101c442e804005001c40501082034020704a00d070150741c080c4442907072042130410501c072525000e80058400d01030400441025040901c0c03401c9411030150400300480440ca440d5845000103c41242e0410420052890280103e690990341120100858909501c0300ea80b1111807074207001403990300c00302810000d40c0600a540401e600492029120080b600e000b0b955034400d203100d140d11038140000640c5448050080101e4280440c080312901c0e1496545d03a010b65040740811170716180c9070314030415080c55446440384a10b0f440550382d401c00041c6090700c55801c0ca80e481d40c40030420100208070150740c0054040c1c0880c1d138540341c010340d03943c05844098142164408402541230402d680201031030380c005904001d481c084c8040303001080720460000f040f8850000001c00580090100f04080e1404030502c0c03481c2c0404280c089a11340c00c1e640007030304551007140d010010030000010300558007410854090341c3d50032411f003088000026110b1a6071110318 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 197114946 1250 197113696 197113711
    0xc01020c0708070308070212071a12060a1811041e060f0302030c090f1309030806030d09081020030a14090105190e0106090e0319090e0604020703090305060f06100314 73
    0x150040d140d00b88c20032101000b024802d503030104100c04004a143c882e0f02000701c64800340c3c280f8001c41c0f928031307016002c0c0007101c3c0c5131a0603291401d11011180c1c0900a0381101070000c110178000024140c40714055205200903112000c0d00c8a800c090b000341c003110409000804040c414402c00c480d03466180126003d091080b034440402904a070300003648040c1140e01d044440741418024001c03d50092501d60040c00b040f030070380e820383c842c3c0c50342101d240810f48203405040d48401c40032600c0001581c007100c2c1d2500803540c015805680c04868080c2e541c41521113038400c9907540040401c0903450b1003107039003000d0400000d00080c1460180400215940140c03c012070303507100e9000da10004254000002017290600921220721225501522034000e00107251030701845025915150b440740744610151410311f0b0a0000d41e484039011320009402c0060103c0600046040100100750304000c2d95105a4640488416610700f074014003603007100c403030000002d150070200700c100342500075400107600030b10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 197116196 1250 197114946 197114959
    0x705120c03040e0c09130b0406091401090e0712150606091d060f0307030b010302030d030513170f0f07020a0e010f06030509010b09070c0c0e040201090308030a0e030c01020c07080703080702 83
    0x4032031360a0b410f18403410321035507440000d400c41d00e44040751a030000e41c5040303011501000340b2640c9408d40d005039203800001202001042c801030003211115400008003180315030441303507001e455070a082e0011030890000e441c00d4490500c1c1075442026401590094a07452900c0d2034080d242c103843c00f014040040c8600ca04054420004009440d8003014280d40c0ea0010101d0700c00b00d0340d071300703243c1d01c0550203003c207900901400c00c0c440c101a009004940c01050f1814240c0d862110a03116040e440c03c04520798060b402041114007250050700c1c0107801074400ba070008a50300c5080d072042003410f03401c0d50701202502c903041004202140c100000041220310078240820141d4810a10a004100031000e85600030401230501c02c8466020304a80145481a01400d051741e8684071a048602d400711002030001d010003000707000041c0e1040185810140b100e601040c644203599800d81150824030141c18569408030f03014400c6074040202e1001001f62401811281c1e05540b5424820312034440081d00660 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 197117446 1250 197116196 197116201
    0xf05070b0405100e24040e010e130f0f0812090f06010f26070b0304021206190e0a12020c0109090608060c090105160b010f090b030619110409020705120c03040e 70
    0x450741e032001c02220540c801985442d46038241902c4694025016018047d0050000414485001d010702c078012003204040d580084050358801c440007d2171a000c036101500d1841c0940080d40e0320700a403900d0b8900803081d018616291680c01e00e04001c07030b086100e0b030b0b41c81038004028810040280c0c909540311600140c40034070b044500a00074020403205a0010700c030700d41000031002e0004015500480c800c940b05031400c1c11001d103d13981d41c0019602842c500003c1d198568410410754005800b80d640b21058614414441c0c6400c142042200400d401580005611201c0b56a10254403c068100701c04108420340c10820341680d1124003c0c49180e001030005000c204c1030780518140c9441c0e90700000003000c100d802c0e140181401c81d01317225210f025011b4804c0441c548086000b80d401c1854003800909140e6500700e0244141030000420f0221030390b444c0307400702c900d50440c4003c1024215404003d680e0702c0300ba2601d149442c9a001d00b803186604140300d034500e1150301200700d80455405079134809864 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 197118696 1250 197117446 197117449
    0x10030e0307020904060203010806010b0a050a0f12020a02010501080c04090302151e01140f010c0201050909060402090a08011b1b0305030915091e06070912060b0d0f05070b0405100e 79
    0x511030750402940c0803c01030200800c00490360000c6060380c5482080c0d880302e9a0b200104001ca0082600e600003140042c0590700d0054032803501c500802400d40340607180c5c01041e101c180102d038080360306240140d440d88010701c440c107400c00040c02011820358081019060700d03100291200d40c0c500d20701054403040c5c0080303405603111485ea0049041e143c0c0515000c1d5035144140301d13100c94001801401a040c044443e110b642c0a9040c450350301c3d406840d0725241a21070700810186101c010030855000b42e00340b044440b29190800752802814080000046480709010007102581c1001c41070f45c1000f03d080c046071000c22102d000c40c00c10a505042068485d224902140d050030002145582c103c6292400c000c210500026011041711300c21810006101281201a4a45000302da0b01d40114158010820a07a4031026540c022a40103002c00120007041800080100c4811001900c40000c03101a500a00400303102c42d0000340407081c1c03003038601803400b404520b210703081865003414013484c0c4950f81c645 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 197119946 1250 197118696 197118703
    0x140f09040b10020d09080a230a0602030c070b060d0804060c06090f0c051e0108150103020c0604030801030b0a0203040506040807050c0a03140d0810170709050a0c080708040210030e 79
    0x80030700141144441104040d0003941ca145112200002810f820b100080c10107001c44e8100c00a5006200400d1a18600640b404203001050b02084984298001d800218800d440590f01410743d0031030039903440100c0d003402c03a1031010140070240704108403121240007910031000c9804441c505e0070704c0301400b00b95090900040804070006810000b030340306850100000408040c0590700101c500b013140b816110001000c1c4104140d11a02094209012a5842d0214044403680700414074000d4a45410b00c2115424103205940071404540010018800c005001303a13001d40c014244201107080d40303015110b4035a50070010b0400350001c0c000041150034000244100a803001d40a0400f40005940386841e0038000e01c103603d0714038117005030842000030341d12500740d145c0181c03096001400060b0500040203001c80b4112900203040c410903e00084401301b5000b160311070b20241400181640c2c49003030240404070024054001c000c803c5041000503580c0e00c25000b92800e0602d00010061854000c8518 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 197121196 1250 197119946 197119961
    0x7110a030c180f0b0a05010e0307080724020303040506073e0717030f0a170103060606030605060307080f100b0c03030117030403120f030b04090501020316140f0904 72
    0xd4018054046000d04100040070002c4001074020051280d80765142d20855411405190380003900b22002c200641c8540c1001400080040c10350310b00c103075181c10b03071407500d2410b0380300050a104004600400c1200700c002810302003007500195103985415564152140001401c140600c80c003000010500d01c1c2c9c0000d0302c0501c42038110303141a649100d0040c0040268481e503050f41c54410b503800402d009080340741060b58108000011420301b180c960181d00d441d00802c40484c200300608030300b1000c4034000791107280218041d0fa400207400b424610b00a09036030039504a07901464040040c0710415074405401c0f40e04c803030300c0511800140c0782c0d50b8000c00200b42c641d1003201030707440200e540300319540c1c00320040d070407280080003006028040811b040e07224043c2d4400600f985d88060b00c0c20b4041c5003d500396a25807100ca20340003680342a424005403c850141c98240e405a6002c020402d1204074400706252152860410890041b640501038030320784145107001807446004108072030300e41c0385d0360000345 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 197122302 1106 197121196 197121203
    0xc07110a05100e062107140f030604090303110a050d06051e09041a0a0c1101060b09011101060905040602091003021c050c12090610050a080307110a03 66
    0x2e07035140c0c4220302c15402100130080d612004000310038005000c1410000c00041d1b04012170000d001020b0742048042064040003001c07041240c920076070340d1154040b5400300b8510301d03a02d4220042e108a004c41a42d08202080c24840f0f181c209016048465801400300b18003a030300c0080000840e09803d2400b2500d51008404440d030078002c1c20700d40d0050103043d5002e403006039a80e003941030241c111506a500c0342d49080c24605103604c000c80d01d01000c4e801000307110306818220a0300c8184034101246040c0080350b5030004ae540030a400040081003507010030800d41c642414204086e51240c040707107214501d148800594030b40240f080e542c0c180b502c1c0e03000e826860721010404008120103091800340300c0d000e001c0e43d008202d91a00103841268403034003404640c1032686c030500d142042504510b1080540000c00e0180309000403e549a580c1c001c003603440940003000c00b26207204816040503 = true := by decide +kernel

theorem cover : BRFrame.Cov 196942446 197122302 := by
  have h0 := BRFrame.cov_init 196942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 196942446 ≤ n) (h2 : n < 197122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
