-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3303
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:15:58.097974+00:00
-- url     : https://prove2.me/submissions/f996e68b-1c4c-4c5b-a6a4-b352be609f3c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 593884892 ≤ n < 594064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 593886142 1250 593884892 593884897
    0x20402072301050411040b100c030504080321091c140403060614030f010213420e06030c0d02031308041401020c0d0f0201050d02360102070f090906020d02 68
    0x6a03401c00420140f50a050508805c40b419142602642c06d110414100756140d03c0400b0300e0320302d04e0038800084403032030504407002d0082d500000000e1000044182083c08251a00341001c03030368040130886982c90341c011b10b854a24016944003504a40c99018400e03601803c1603000304400031604c1401c169a83d2903030b5090300e0701e40e400a04001001846581d550034180300780881c5003585d1009500c1c0000c40358030707054203203028130075007190310704014981880070081036401e04000c00601d4441000d40b0010080c201010b04c084404010880c425000d1200c0d08018040e02d00c00c0003e140a1801c1c04415415100a940010310b213403400c1400920540c0040d005001800c050071035002c0401121040a001904c3c0c1400f9010317182c404d20499042100080160059031203580e0b081c6030250320b640015242c0b00c0a80103085100b04824100c00c060041d900c800e8052590f620f805004199442450304016a1500264001c0116916034910240501b90894006040703a81c4914001884e1242d010911000ca8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 593887392 1250 593886142 593886203
    0x2001020f0c100b0603150f1f0f11060105010806130507020303060a0f03151e1e1103090601060518060f0c06090d08130f15092d02040207 60
    0x301008a81844105000c0001c92503070418090100403420600b40090301502004001000303900b842260310708981c4522101040e5604058618403400321692a040d090000741d401d0500040c40855610400b144035625000d400130b44000505443e0742800011a40000010a0290403119143c4121101d0100e031240c14030440a80d4003850702c07418110100064104150f001010f40c0c0c284c16824800b040500c655202c06280e8042c0016030707c015408005103000b010a01c3d82c2c107484c50013200c01d042d1040da40c40d034040003031400000c010000d60f0b082c0c2d41246020607145003000d503100c0c000502c651030049008106011140a461442082076000640143e0004c0302c0314101c0d070b0b00428002803060041021540003483d5402a0404012030000200b61520041007802001d0600e400b107814400c140b00410740d69038010030b11380c11040c2e0741c1d51000080d095500c41255101090803800e002d0020a08803202e00d5004000c03600d41e8541c2a400f008080e4000d820299510401c411701c60ba600f0050641e5030400c2c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 593888642 1250 593887392 593887417
    0x21804031e090509070915170105040b190609090b1f121509060513020c0d0813020a0603021b1605011202043512030a0f060806090115080d020d200102 66
    0x3c06e810140401c0207102d0007000740042c400c9601107a1540c102d42c900301c1b410b40360241d03000200d1400c044c00240d078004100c0c02243c8050756440f40419196808840b07030080d42e03030080060104414540c1809540c481918007031618541e0544144003182c81801000880a42c203403002c42d10406a01004580c81543d034490b0290307c0d52804208142c3c1001000708444105542c021400c0994003034800d45c45010f244079200c10043c0300c000044e07180018451404506030007900008800d502c0d542d0250096000202c00d00041c0449007160074400310024106500d00d608800c1c000400c1e00d00301c0156514060034004e400341e950244404541003443d54400016082c8031941007814900f6603081040d90301c0452860103198020100d03a2461181460490b50040d035866000104034491141c0d0700b0003060300c0e0f00b00d60340500860303050201c520b00c1504a400c0840f400b8041c2810b01d03075100350b5160303580142103400300503070032101c06002aa8010340d019441190389141400c20b83c0c05844c47c0d5801c903072105151480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 593889892 1250 593888642 593888657
    0x306010f0c021e122e090501050f04110a0b160305070f08190e090105151201140a0f0e130c03120309030905040504150b01030f06030c03021804031e09050907 69
    0x4040c540040302c8621149a800900780920410001030102d800d0010200d103802c4c040212150390317110a901c084461a00040200030380e0518000c041420780c1c054900740c9007076010b691040f50500c6c01280540450b00c15a201c14907100640c0d03108040d11541303520660a000c014410103000c10b00407007858140c240b0030700c1d080c1d42ea151042140e400011400041108221a281c1d0b405003d0321010141d5041d9042104c0c1d0551040b890104074103184150782d01c1c901100c0101d400002c401d030f00c8005600741c42d00100e6a481086031540e801ca90195480d102c0e2103030301010358011030180420000c0025400e8002c0302e114020986940740c007026130240243c081e001030b1b900d07024a4107156101000d00c0203414100c400384031504064131091000001d40100c68400c680d540c0c03000060782c2c001e81c4190500c00d00c214050008550b01d0030410045080d0344002d0b40aa0442e500c5100c00409031008148120313455215114009104074402418040010510b07040c4080c82c2c1010809660f020701c0b41e4032420560390380c850b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 593891142 1250 593889892 593889949
    0x80708040e0717010303080a0e19200105070803101d060301050a060521010e10020c0d020303040201090b03070e04050a09111020030d06060203030a0507050306060306010f0c02 77
    0x1440000804a42c20031012035084100410603524042c1143d805207000c0e44203480743c10303012004100007180d25084d8030480009501e4a01140400300b44a4010b60700b81c5424001110161032100c2110082c90009208003c50340009204078040c503007080f03108020a0003192540c4031403d4a114140b039580d000120b0500704501841d090084a51204450406120381c61415010515a4003902c0b5034240d100a42c5c002c81403a1107095102128044040044a01c519821002d49000354415920000c940c011105054151030001040701e000c0e55060351000750300b901d480b032244413a80018200700b0402c00c4511140c40c25030b850780035440c0950303d070070300025181c0214500801c000d04e000403400e0180c40700615861000307822002125441c01040507600503031400c1d13102c060462003807400180801340703040001b0075819400809944a00f2041c80c080006444180058549010455a03160711003410000182ca03035226003804401c00e0030b80d05007a0060200c583c0082d00c4254a5150044030942c6461500d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 593892392 1250 593891142 593891159
    0x41d030f070b130f0201030507030f0501140405090708060105130f05010b030109050f24360708011404020703020c150c010c170609100308040801051b09031c0c08070804 74
    0xc540180b000403404907044100e13035a004003030303c40d0007000c0e040c50b503204c0004030041d01a0b0001291107607e03400070400c07583c669040c608024800000c8901452824001444c0ca00c030001d0004182c600e020000c1980780cac40d0500700140d0301040c44e004040d01d0346400e80e031408078003d80182400303840003041460312907041422010072103800800c0081d001c070000302031004147d0402489914070480301640c030184605000807903961f1b92003609018079580302000103045205140103602503410303085244c140903140d6000c1100e250200307000e00182078501e0500100503141c198000c0c050640f0a0044c0c40001090f100028082410350060b4a00308400048905180c4020b128a440440d40742c02c0100543c6840d103007844901500402c07540c0900347c0c28020450040c1c911903110700560f40500095a41c42d01e840e5440d02070304c0d0540d000c0360f00c0c030311091581c1e407e1420117080e50b85492014000f04140d501c0c01c50040039002c80003000707400380092070907002c0c00310b00403000526041c5c0c0500d5459035141d02d0074904 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 593893642 1250 593892392 593892413
    0xa0515120108070918030806011412091005061509040903120c020706020d090b18030c0303221208032a070501021e031b0307020102090a06031508030c0c041d030f07 72
    0x4c0402c240c0568604500080c0c101c04808c0c3c020000707181000303801041d12a41030543c0b0818850258040050303003002840f07030000501140610f0582c00500c81030b280d44c401d1085501c030308940d45200c1b8006001072010350030a64030071540c090107840c240f05a103101c001c050b01155100b0a0101c01a04a080103000b1650108490944032141e45800c2c85407524050302000390b4051254282005414600380e1105540c0c10418041000002070940b95950601c60204410740110604003c41285504c07000604250090804030410303000414070380396a8132104030800c03035009000c0e94a411030040144d460303256400006041d0240c418400160b8440c407100010f15050280d18412128003410420000d1110380d41c1c3c008408544140300d01c1d61241c0710554184c0c0640102c418103600580301e690005921a0f068001000c0144c042c11110085038490359219240e1041e10b081c466980d06c010f00c0075100c5d040c90b51000c4054000d0300c84031a00b05c2c42912420342503510440701d4003034100000c1400024450301101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 593894892 1250 593893642 593893661
    0x1a030405010c1b111906090e0604050103170309010608030307090305010b0a12140c091e13081b0c100f0f030207021804060f050906090f06060a05151201080709 70
    0x1410030341c091142c000c2d912501c150640c002c2c2a051031400f00007291325041100c20359003000d10b070340048082c0c845c0b40c021f00c449428072446c1140610b2001080050829101d500d044e250002c041c1803c00004c0b5442501d580d002900300c1d1007540d80c0d104006040c1100303002940c0034803000c1c0d9030100c0c0640781d03083c290700f540c1401c0c41180c80340307040d22030800c4640e940745030b104a0507074062002d0b040c240e800b0510508000240701c5045d04107624604008111500d205003803e000049400c00b400358540a40b680b007428200d40c0700505030b000c10032601108207501142003a42d50080002c503400c48034101c0c04a026422556038800c04182c8030645072010175082003070300649481a02e41103040040703903000038000c0c2c070b00da6018020881f10305d40494180304903500482907008003200c090206080c036821071641e40701c0445104943d802481b041e603103007003404130b2080d01440d030040c40c1d80384660070034003000945200502d000e5083d00d0b080046c582c100704201800c1d8024200b4202401215250043d068103803221001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 593896142 1250 593894892 593894897
    0x31c0b01090e090a120909020a030212091902150d0f050a0e0d0804030e0d140a110f09061e130605180106020d0c29060f0d02060d0207020a1a030405010c 67
    0x1d04011100000141581c012030b00034450320f245c04c880c002c054809042540240b2019400010000410707078068006194101140d00f941a155031805501a02c40c842c440094028991071000ca0000d454880e448203406804000c8003403414845020060403140e100c008401c129450b030007003028030340c810304c50384000050a2024003011100e504000702000c100400003030034401002e44c6100291541c00c20000303aa80e10803092108045030000b4641d0781c0780d83c05022500c0642c222004041828000c1920101500107024800d0a03204d250802c0300c1d6111031130802e09029002c242041c2c0c2c030344d21000c0d4110030b0840030400051031070801b020301c0f400000a52400c0e00540700000100502c3d9800144054406030700e00c0e1003c944000c52400000d03101c10700882d800350a480713502c1503e03607265804040b4001d05c0c0c2125544203165400c0d0074448803001204020703600000500c51440c084a00350002e15045100400525190341c40780810ba05190f220b1404003030310f0402008200c10002c00344101d404811160 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 593897392 1250 593896142 593896169
    0x110a05060909162a0507060504083f070605060103051302010c030c06050115080907031208070905090a0506040b0301270201050c010f0c09140102120705031c0b0109 72
    0xb040c1d8041e00680110440f00407088040f12a6100d904141241c41250142c451301240e95070000d4044040350400f40d840740070b111000100c03540940122411242e6100243c68032180ca980d0110441e4000042c0310603102d40101d1244440080491102c800e000c9031000940f10715550601c030b001c9501c01001c0ca8181407038030052048089030100d5800d8003c1d82442c061025401e01d00d01152812603d1b00300034000c906160010410341000b2950708416081ca0b9915007941e6118065195155810302c0080c11707205040b0345140d0801d2082c21080d0380100141024013030b0799034030782c0450030081d01160210861907550080c0721170340c40e103400f072604209405c0f002407003103503801e000250040c500380c0344103503070441c0002003c03045900440503101d40c0200b60700200010f03140c20f00c50704050544100023200041001201081c6a420b00c0003038807180c801a40140301c500c1003a65544410b6020780402d0b03441d480180566000d22418440540b81c580e044c04001c10450750020002d4040c50f0503411114418405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 593898642 1250 593897392 593897407
    0x60f051206040e0307212303180a0c0f03030914030c040c1214040b01120305030a0903090509040507061407020306061e120d020d21110412110a0506 65
    0x54400d207500014122000030300c2c00c0204280500e14410803000034009007040d4405400c1c80c00802d1074580c800455204d684d00e80c14170000c030800c030304010300380040c0314801403000c030710301da50380c4545c006510503a4412190001c07000e80710b00d050700f0704503849180840e641803014030401d6400101200101400d2016000481d219400a0388550308000714500a82e514044a0480f9100703d030992060110100b042216400000d0800f04090007103d003941d40414010000501c240f5244801803419003560b10141552543e079060005007581e40425010000c070481c0200d030b10381c3d40300d805901880c8114006c003000c91504c0320241820103130314404004040c007880424003686000ca40c55900260454205004200b844c9082d8a00c1300c621810640007a01c1608890300c0d18400105104004855000c840c900c2e044d81707000302d0703022240d02e000b03404902e004620b41c8610462a0441e030000d0042c03008060602e0b403240c0c803442584081803c02d0700e4a040140140f0394a040c400d2030701000d00003c0d19003500e4041c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 593899892 1250 593898642 593898667
    0xc0f0f1d0c0912060f15100e0613061806021908030a11120421090b03070201090605090d091a0703050706020d02070807020306062224060306060f05 65
    0xc0d28144101102000000074101c01e115011903026002c0144040e2828502240d02d80c1d68041c11580c2c40c0110300c3e5080031035800b415071500504d512000420542030742441e94021a141c0d4003004400d50400c0c405e002c42c210f000038401c00d41000c0c00e07499036078411003010b1229a520188461f03100805540141416200303411079912401e0100b500110714a40c0c0351180d07004d107001001c07204101c101e694800300d0090003000f06070305d80b58056409984480802000785903401201112040308801091084a04001042c10b80029603032104940c000055581030948650042d40d034100e544a03082e03000081300c00030040e0080a08000f41400000c4e9214031100141c50340c809105544001e828000c01040d40c1d400c202d45a0110303480e10300d41200941d10740700d00340740c8001140c2089008a100340a0381001a900c0d00b007081c00021181c090b60903840000f1045544440181244010042a803c21105d130300082c82c2c4c1c4504060040c01c0071703540007030303098506038004040700c040391020310400508005d81c0082d450b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 593901142 1250 593899892 593899919
    0x4030f080402062a0706090f091e11120103030e2e05030c0f341104020c03130f030506090714010f05090d0c090f141801060b070c0f0f 59
    0x484e104050010702140a4000c072034040080032202c1d461181c1040801d485900c084520b0498520201800d8401d45400c1840300303440405d084014105180598000704101c00d8204184c080080d400c11854800004100075800409801c03c3d40030072040b0520b1000d0f4240a4000d41086950003044802d072440326030a070022910b180c00c181c04100011010452840f0050212001c48540900680c0d03110b101502d902185031407a8040245074480c42e55110b00201d4041450b0402548481447c02c1003094404010080d000407818029600c000d002074440607482040100203014840d03030710440c45296152640c90304038000d10b050910382008104010b80654000d80016044090030301c0c0e100c9204210040359240a04200164032081d42840d40c014000b40354496070507508d14140034460f082c00b0487c000d003641c0c0007144e40d1180072141c00008103c10348003181000c4000300500085095644d5143c1d004240c0c1202c0341c00d4a07201e2003d00100408140000c00300000c01c00d021907280198501180800001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 593902392 1250 593901142 593901157
    0x30d09081b070501140901020a0204110f0c0c100203090a060813120302030412030c0912020319081312030503060d110a080313090908160c03050a0b04030f08040206 72
    0xa48a254200030014440152030385008011061a0300c8000c1d25149591245a0300c10280461402444401c24480f28812581200010380040c010603443c0e074244002000170207250410500240001d4440f50540001007440940140040c05d00142070310800c00c81c032001e500c12405550041110400035141c3d65036900442d0020b00f0301c000e1603550010f0704891031042500003800107140042c002c4819030541e0155008501460200d126941d150f8001c0e81150f548081c1c0a0200d0411103003003296080e21a1499405880901925002c0da2400c1c1c06c08a600601102116030803804102000c10000ca0100c100080100c0107501c0441383e440d0b1006440703484094215030140000842c14411b0040302c41c001c804244020b05291056540c030307100e4585a13040400408144522100f001408c0b0700240511903070a90000d800030f26020100c030f01544030390148e0504440e0b000e00e12000101040b8180b0000300c0040c000d100314103003403800f4913005010780642e420394030074020281c06000c05611103000740c4005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 593903642 1250 593902392 593902417
    0x1508060705030910050a093e010203090a0801051b030c030106080901090f12030c1d0d030212160618050c120c0604090606090b07030c0b100513050103050d0201020c03 73
    0x50782c0f511008a42058070003d1030072203881c00c0001b40f09000d502544500c000c6800780d426800e480e0510568007e41e180300303c02c0100e06581085424550342900c0011200807001401143d00e032803555008544941d00d5a4003d4005035510401c0025000d402d1004450020b840e4001c0c41c034510b030100c01c450749404180100c004000c50031000070710841095120380f2403240c10800b070b41721031101481c02c458101c50310b0404500090a00942c0f41849001351900f4109a6110314440241c0c01e005092003216007036840f00381d0442c0300d844007428604503101d0090041c10f40c0011460300c211250b09003001544c0d070301d03d91414403011040c1400003013140030480209a20040b16155100d44d1048003003841d000c40c10941561001000400080b01200c5521450032501c080d01e83c030b100d075550307450145864015044080e0204204015903400510310035050341d84501a0492009107640b11404036081c00d040b01c40141d101d40d9910018018400200003035100240c0070f00c02985082410b0b00308076144e01844051200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 593904892 1250 593903642 593903647
    0x9102a0311100f0b040b030c13090b01060302040609050a0506090405042909190201020607050a0302040b0705030d060e0c16050c060a1808060402060a1b060e0a02041508060705 77
    0x4051041034400320300901502280e110440d50a04507000f4040d00c00030030100c40c5050124030302400c040c000c10702e1041004002e0301e80403c14030103220740c11022602c50070f10650b441062000080011022a0103000c4a075401030b01c2e5801c1c100080d15105c40e0360046403140300c03407000400650351482c04480e0035003000e40700403485407514641408107940c1d514695100c1d40c0c842d9200405464155003140c400e002d8032003107851504841490043c2c00203040303c00b80c01070708100001070b1840c0c02076008086600291030014507060765010303124156000b0f220f08995079080054821110000b80c02418054141d00c041c0e05014105518024441d1081c00480911b100340000d02006120b002d1059446003030001e010940d4031400507034002d101070780f60032004d400300c0c81e0720030003040310f8400142c0203214a2b03001e8801031914405032002d83c0c01c020701e2030300d01801c18902c084c0d000c00500140035070b05411002704010300300f2401510400041d10710103c0d030404000743e01c0c1000c11401e003001802c01c0d0040d00c2401c2259 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 593906142 1250 593904892 593904977
    0x30a020610091505041a0402040603020703080a18121218030f020708030d0915090c03020a0801020903060f131a070f0309020a031b0308040f1a0a020c09100e0a020910 73
    0xc2c00100085507c140b0204001400d0b58158000b007400d10b1090b031703901c103845c3d40358000407003141c0310b03003c2c142541003600f0051400690001001d01402101e8200310682c5801c2d90400420f03500014012000300314001100401c1541102402d440c511070703800504003160400d10650360f0b900440450044a50301d0344403540c28444001c2c45c41201c6040d00005001011203070409144900192208034010780c0c607804d00290040301031007a00c580a0004000c1d000d9611154280020020060004100c2d620030360300000004450004600010540d1204500c0c1450103910180c03803a2000c02007541858244004440141d4078541c504054a03031000c6980d80078202c5c0382d400c41c000c442503040144445800600456400c0242210a04076071240c0c1c056000c00390000305020140c0240c4a104025074030200d881c403000e10b0400002c0ba40560502001d035221941c41d4901070440100b5500c04880c11780c00a00e00b0600e040c021301d0b00b000c42507103003000040610703083c80c000158001c3c40c000c040c0c0c0707440440281 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 593907392 1250 593906142 593906171
    0x604020f0f04110f04030309171b0a09050a1a040c1e090b070c1503140411010516031205060907120506060d0f0507030515032a03030a02061009150504 66
    0x441c440f0208010f42034032061402e1200c90250b2041c0000d4020800440001606030015248105808140c0024020900b51601601585021007828641c0808048000315400ca010300c00d0300e108072403155003c02c001300c0e4030030780c1c07614000c0d003440f4140200c2c01e18001082154200c002154002070000100034249001c0c041161100b05981103038003800d100142100510050b00c07034000998031101c042c445c807080c10072001d404071100b00d50444041c0f040d91000a001c10800d440c50100301d003060402d28500714011f0300012002231080011400300d04c1d00d29404a00076414810160b00078010354010003030b41401d0340042c1410303805070405400306480e00002072031500c981058951a0720710410912500005c01d940d6000340108a030400006841c10000070245c04c1e080540264084014003c1d240303107a02c8407079150041c8201065103840c103007144601d000c142c40801c000e05280709254003030202c41c28150828824440b50350710144902e130809050010010343c0c0d5030040100d41044600140041c2e484480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 593908642 1250 593907392 593907401
    0xc090b071110050406170f130203070306020f0d14010e1f03080706050103060e06040c0b07060b06040e040b011212030e0a02030f01050a0b0109231201020310170604020f0f04 76
    0x85801582c0360b1080540c06821001400683d041610b40b000075042020813003008401c211104131800448001240111101d04107140d0728500207170a07a10030030388a86480301a41c0c007504400700b450b58005030305942840301e44524130200c460540085983e515000700c0008400d0060402c0c0f07010210005914103000c9080880c0008540c4051140e407501c0541c28490000c2c00c0c01d2000703880d200ccc20003491038034807600420158030940d404481c262420382004004c5460350851441203403501c1e030325062100c41d03903070b990050401068040c980c6983c07440d180c540b00f0183c45069000c29054402c4019080008650034441c100d01c280e9442c00280381c586290b40c031441d245103550301942501a403003001441b1034064100d9441054818000d0001400325001100c00302c05a00c40c8004411b4120883d0076141d41c7c6055508840f0f0006000e03181600008001508903803084e510402012004030042110070108090010030341d2226001d4185031400d6008184040106803c0600c43c4034030b526600e1403651203900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 593909892 1250 593908642 593908673
    0xa03080c12070e0a08010915050c0c0f010903140406050909060d0b04030f020606030a08040b0c0c120703030e0d11240403031805031f0911040c030f0b040c090b07 71
    0x5860081d820b01c480043d203800b9000c2240c0740140c4042c400825401414064a0304c4164000c080441070950408081c0042c400980000c51a003c00c0045400421080042d40e0704484002c00000e40c0504503c0e002c3c0244420051507010380005101c02c01110f9003210517a03051f0a000e80d607800c0e199980800045164066080040c02c5c0d05001c010b1000b819884064262003d825408548050720390204240ea1404100d030001c141050810090015000b0600940140000001265012903103000016080c600610a112456100600130014941d2280c240e4042ca0001c0d121115030300e0701c60701c484003800790602c1c0d000e0089800c041e805280039080140d030011200541d5210380c172151a850010030517108101410b11140e00300302d01240070720700460020903aa403545800d80e5860740c1d207106c000251495a5064031000c2d10a52000c0807901c0f2400340343d2440c1c0c074590300061403601050b1041c0c11aa03e82800c503008602d485006c0441e15000b541d25016100c54460003511014135207085a0302c84043c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 593911142 1250 593909892 593909917
    0x903020c060d05040606170c0f0a0e07020307030905010c020609060307021015090b0909070e1503060106030605011d09130c03021507051009030219061b05030601030e0a050a03080c 79
    0x30b60038281851a50003240518444d06090000b66607032080041a0742d01c0217000c00e542c3d0007801956040e86804520000300c00c0c0003500c0311010396500d5078004450482280d805016800c0041c88000300769111b04035070040d290908000301076030a2500400c4690003024a01c501641d000404078104d50f0003048040041e03940072109101c03a613401c54881d1114245071050385007003414040703100781500d8001500c621500c001e07401031000394030b003010301508240e000e4005032034554034001000094409002c894003800441c0c601041041c0742c440010010f44006140000414074001040b2a1b540c46c410320316000f20b01d15020385450302d03e070300700b82c100452284d0000f5404992048241681c1c400c503000307400268020002d4400c0074500c0c032000700580c1c0300f41c0c50003001600050f0b14960302c2c6a82e920502c442d00c2c052030300054120708600c5c3c919032a880c400c18000c04244003100b00f0005607410300601803401c50443c0500004c4902c0d64035941d8810400310000c0c14410214001240b801803141036a03004001d02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 593912392 1250 593911142 593911147
    0x20d080c060c041e03020922060c030c2d0e01020c03011a100c050718020c010507030e190c0504020d0908040b0d0b06040b0a03091b030503130806190903020c06 70
    0x1080c0700d600da10034800d0210051403101459510780c04c180304002143c1e00500b1b45d581c1e41c2d0702c208408940021a00b400f01100c0d09820024000c03504603c5400e0310f1249503240018a100f0700040a015055070224001e580925039034200300e505224000b84284a8190034901e07400d07504000183c0c10300a64204542d010341c600040040350703901c0032000c0801240c0a5034059260004224120382d0030060f032601034902d40c010081044101e04001107200244a0030b0001400c2081408045003554400d4030182d0000f41c5680600c5588201070000441584001d603d0b607840c02c0840d41e038440034003820300c1528451540400c1840315000590000b031203540c1c1c0034410541d038680391100100a50080202c01d80d40703620340140301d0301c2401c2650441d8140c0f18402885400c1c1142d10208801411356042c0840c0c0e0b00e14014401001042115004005544036030007a54880700b0545c942d0611004e00d60043c80e10358410820301c80748260803c0030204078a00c130180840e48140c40d0606a10b8042c15240154001800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 593913642 1250 593912392 593912401
    0xa17010605040302090f04080703030e0f1f0605030705011403040201030f060b091206060a051908011104141c110d0507080304051f090509040f0804090c030b041407030f060b030a0234020d080c06 85
    0xc000c5001034054031010030170fe01c5489a090543d10303183c0d40940e6020a01031081c008078a5050b0010f158080c0c070500d0041580c1e000446135006990907a8491075031130b8000700c1c1c14105450400e860000400388900180214a00503000070700c0003603e4800d00f4025103c1c50000d04d03c0e00f641d508120081c080200080c4640740842c00f003549140d2091144030700604101c4040b000d645001c01d00c0c00220381c1d8002004440c030509480c0c4e214050f00700c00060b9884120501781d6000603109000c0c1100801c0820055a00c0300d24000c00d11984c01c0544002d0315104680c407070000c1d10315401204500c1626000e941c1d4114607503071407034102c040300c6101d00040c1c01e45001090004408405030407645041519036028821902d410040c0419100500100c4104003121400600c1c4640309501401250180c1007000c00d026603200c4000c12150300969002001c0c58000440c1d03d800c9a000e40000103050103aa07041030150500411070300740c0c0e221428000d205050260707460080c44544000d5a10701c01c02c82301035520714101f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 593914892 1250 593913642 593913673
    0x32c0112020c12070827010c061a030111130902280210020304060b0f01030e070618030c0b0702011404060207060c020109270e12030c0a17010605040302090f04080703030e0f 76
    0x406c01d151001000030f2040703c810403408071002624940c06848406a602071640d8000207010104103d55400070500c5c0080f2580d9001d00480f440c01c0024150702d035540d8040b5600701c101c4030094201100e418010040c0060b61000f50300e40c031441224800c02c0903100c1071072940c100c3c2851010840c0c03002040c000700c280001c0c000740e0b5003e108140070440e904075040d0780b24030055013540e03141425a038132500014410070965004005408004400500403000c0036126074542140e00f01c01e40001100d1030303021541c5001c558024004280d4100005412400c0c40d00e8480002d640700e105015075001c011030a00f04078116401114250040c1c1141e00c18040c5013844c84040361503000e01009039032541410110a445410b4000c5107507403805001750500303880d5075078000046620b584590000000c02242d405815904252022094080c0040791744482c0d80d1407550042010741c110143c841e400c009000d20074003000446400403a0246541800c000c03801c1041070f03500300d042c4015003101c58054011a498490181ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 593916142 1250 593914892 593914897
    0xa020301050306060d030c02010c0c05130b040b0f03031909030b09061f050f0909100501080618031201091d010c020307060f11030601050c0712032c0112020c120708 72
    0x941c180e08075451076444a0030000d0480400c1d00140100300e01010340310240d4400c04200000728013a00401c944943d550010900400c40b00f03603102d2100d5070707480c0d18200500d0a80a06400350108030740100d48080f040c0c0c0000c0c1c50307114420b01075102e0004002c50a44140c01440d00078011038005c4450402c0b4a070140e405612407104584446c00704100c41110480c103078460b04c10900391540580201c1010a0350b1083c40203150340070b4000a6584901007050740e000009006560181884502074109401c00300741d5180301d06c3c0d000d020110150014010304078400170701c024050441c0c40141010940b80d800704011040040f030070142c0700080d402c100350250071980020081c481c840c459481049030f6206400c400041310071340c3c45d441903142000c0000c900e941d031080c4083e04040c80d6540594200507590f03007032104028500b903002c401140c0c121588840030240b64141100101a0140690b241c2e024800000c00802a502c0806044c40e4042070034501b68004103e0300304801204400700e40e0301c0115042820311074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 593917392 1250 593916142 593916149
    0xa02010b0d060b01230d0e010e100e15041203090f05101505031b2e09030b0108030c06071b02030a080d0e0307050c060d0b1908070504091a100b030a020301 68
    0x45d0304500b40040c411205903501001c40da2646428102003c0c030907004090700c1508010544c9648418031000c8a80c01400908503103008003400068010180342ea4505003180c041a83c1081ca80d01000c000206160405400c03076000c480c42c2c001451107551404500c1100c40c0c4502034124418070300e050028031050350141500f160030301155005503569404045d030324880101400b800c0d041340548400c403414050308224190380f84c64425450341d4611070b01544000c050400200004d005801c080040c04030785030031316000d00801d01c01b8624121519580715610035015040c40300f040018043c0c034040108800002c2e070300903030041c113032800a031850502801c940c001b00c030181d1030b50385484c84813217080e00008201d54106504c00047d02c020320300700f402c2010350b4015428440340039890340e0200c41c1941d41d054040d0104c4501061280c05181042c504501d45100354200364000d0f49442854008101201444004080b03074902070941e96803440641110101030f903010400800d00403040c0020243c003900514140c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 593918642 1250 593917392 593917397
    0xb0433170334150b1c02090a0207051c0e04020405030a11031c0201021c1b0c050c040f0c08091b06030a06080601060210050f0f040f0302010b031902010306080a050303010b0a02010b0d060b01 83
    0x20004140400c0801003901c00d00c08030713105d070744a08440181021600e05601802040300181030000d503460315810130300e11900c0c9500954200300001101e9070447e18584860f10181e600b18106800c110100e6911100d074040901034124100881045580411296031003214008440c620641055006030103504082680700308500c0d4107020305542c0c151403085940d01c0c005139001003080c00100c101643e07050308404003603c0901628070040d240b61034901500031400360900000400c043c0034140103002850191898159820480c03e000110042c1d000c1c01c0040c0108a510a50340c0d22003103182c1e001031141c0c2c0c0c440400b6020b260f0002030200e40202c1c00c4048969140b406000550740c0c2030146c500c08204179408801c001a84011038082004640c1381c0300c0061007030000154614988000914048100c41e04001c0a1804000300c4215641401100b005000620040404105036961681ca90005003c0c90f07030144404a0044403581c400d411100c840c0c8009025003c01c0030355801e01d00041d02c60054410301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 593919892 1250 593918642 593918651
    0x4051516121b0c170a0e1302040801180317060109090c020102090d141b030703030c03050d06170d0201020c0a031b0b09160b030702100b043317033415 66
    0x103624140d60210381741d400c2d440c0d54184169406500704003039010340c12121078580b60f0a03c0003145000091207400540e84184568505c6240d243c0740041403d0a60340000180200020501c82a40d8100e9001343c1503802c022004a030840c0006000c81c02030003034119080d4030052500c0c8110900c68284001e1140d00102e400703a41c817043e0802040c00c80300e40c034501500c0d0160b100d200104007091140c001e2805980c400d141c85841c11141640000a840032600091050002c0d16140e100100042006448040355400298109040a0007080e20740141243c003400740a00c1500514011110940800744654407907600786180c180751324595a07c603400b469210302074503200000300300c2c0eaa02c00241e07403042290f5401082072600b26103021016003085489190400c1e142e6064a91060b0880b1307078941003c080320352901d104c0b110617600400341c01071075114402541580004100c1d8001c04003c44116110301408541200c1c14100288050070a800020054000c14000d2004100d0b100c00300710185251010b0510 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 593921142 1250 593919892 593919923
    0x302070818100216061412070914040c020a02090402060906040b22120f1b06020102181804081c0c05180108090a060e0313030b04051516121b0c 63
    0x980e43d12030840c80d0a900130400f5000c010301031140702c64030428444440c00c1410308030800d000c004803010035518600071512405051200c2c52440f003020300c0381c4204440520103810b20b400c01035103428148001a021760800000242951180c0d41112112040030300f140d983c445d5260800075280d0041401903110003804c244000300c590528501d04203403242c480355485000119a1100c511030a00c0c4002c44d481d80b00d01000c03944205078485030341c0c0101300c190000340e034810740d100540b11030222181c100c52140c2170317005481d000c0042c64840703c0c0e03001e03a002030300a50301c1801100284111104440c15050142007007148074510350b004014003e030340d002c050804000701200005480c10a0100e50400c5030707901200b007c801141c4242c00a29190b80004140c3e4a441718050000c1103004c12038005555500c0307400244410080100144501e01c4007000041c19582001e11030344118040388116441080b84010051040d1401a842a81e80007061008009014012003000d4040240701209a608030010101074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 593922392 1250 593921142 593921147
    0x9090f0501060f03091406090f07080f37080912010c141b060106020703170702010f0c080d050a0501081902030304050907020708070602010209090603010c0804060c030207081810 78
    0x560580e0780603218200d6180042d081100189171843c1d040e243c0340e0070341c0240343c41102c0c14801c69015051140150212078005400c0c60f26119403036111450075484640651140100403901181082000c064109040c00d0b4600c0c4900e110240c4c02409415500c1d5010801000b454200500890b2402d46074848015080c071041422283c105081e000072400c084004071202c6001b40003030850f05680b4120307014820008000615100c000d030003081c0035a101410901c140011542611580e694074070b482440c180320390707000802d041040227507030b000c0c032581c840003a042000c3c14090b580186c8252400f048280340948101d00600340c05c0c411400240030700c0b0240c400000d8080b115404081c1c024000b140b802e4136000510802c2000104030908500030308502041c00f40302440348000a007040d500141c1c88400c4001000010b0001400d140c0c4241e142841c085a015040780c0350542c0030350800d0001a110300c1c0b580065029202d0bc3c40b000f4085400040e20102c034060701d0306003019072441518205241a202a401d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 593923642 1250 593922392 593922401
    0xc0306101e030501151a090d02010302160606151e020703060518010504050c0f0301060b030103020f030c0306070e030c090f162312100e1303030b0d03021b060406120209060f03040309090f 82
    0x226032300a81c3c1403c0c80030165010340c0041445032070b21110300c1302040303081d100c2c14102d80841d0403aa40200010707400801d020340c80080311802100d40c0c00c9603039014000007070103582c44546100040c40719480340e00007440301554511240c2c0500f4440c009108501d401c0c64030726161b82400c04658854042c94090790494281449003e05884004003110310303503406d41e0200000d00382040c40300d5915107d0708006c0d07007044d00c00f445114028502619070f85502c0c200002054200300381e662003140181540f000304010458014002a0441041444460307146039a48085480c280500c0308040c1c1040e0644800400038410030080190b10b09007e520310040e10b54560100d003602c8948a62003000412101160b031010686a030300781b1844c4a4100003500318484400301d0440214960140d0160300f2001502d2183d199810564010000032100a403074241000d41c050b04001003210203900f6154045a0700d05203440d41d20031a4003043d0307007c0b1038948914013031400400e00c3c40240190030819041401d10700002d02c1c1c2e80034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 593924892 1250 593923642 593923657
    0x50d020607031503140a020303120a0e0102030f060103090f0206031006020c09011d0a061a190e091501020307060509010c11070f05010804031b05030c0c0306101e030501151a 76
    0x400e444d2071900c03031420300c40318060516941d02400c24548010780d0204003c2c00314081c0c0b181c4804c8c5600d001070b1840105d03450b1840500c00c2e0b034010010040c40e048031010389a8012424240010440d40c5401c290410140020000390003002c00828001c400f044050003604503040e0343c1c01c80d884d1607070034000c0c42491442841101c40041c4900d9081c41039450b20702000e039100704141d00020b0304960b50201030850301010555402c030960300280030300c0c1c0b0f00058424050f14080c01c0c04c3c000b003c04400c0010403103e0b00c0050103400014110343c0c40d83c9507603100348201d4100c03580102080c48141000c200d501c0c001d0003566110740115011a10041c104007021411204661403107880b807101614040055440c0c7e9002801101000130034030f000d003e0700f84001701c07000f4903502a00c021519040e101182910b00f00200240b030b4406d80c821410070020601a641c01c0042c0d903001025412400c07000c100c5111002280d0b04010102d50030b05102d81100d0b5400c0403044102c50241c00b40c00d8042c1c22031030341c1d203440344602d11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 593926142 1250 593924892 593924921
    0x309040f090c05041d070306020d0c0c03091820040f1215050c0403050102070501090605071107051e0907020a0b07050a080a05060114070b01180b0319080403020d050d02060703 77
    0x7004201c203181550244134000d41005e4078100843c049120705042c60002d42048403455404034400c400740360244210039810600d41480c020031030494801620310019446044c03410120034070070250480c10350300700300440030907800c02c03605e0100300407406c000940060040c010b041540712000a42180c4038030303403c3d100c44d400c81aa100420000303641000035000c024410801c40000f0072001001135824030080070182c2c0260300029084895103040015590094040d404009a410342e2208100010800000320784040b501c428802ea00614400c104484840003d076016581d6070400c99019000716800d0140e0f44140c0e0808959554014180c5490081c1c1c9100e80009440340009101c050841e4403a40d0000d805051110200100041080d482d40c013070a0101c824020b504010401c03100c81c24501d2100d541a508240203205048012075035a12801d0400c10002c400e1521400a00c004542210050764000d4070051850b4003e00b4515500c040d00e801401c014400e400000d401c030b500c030b489220540c08206 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 593927392 1250 593926142 593926163
    0x8180307120806220203070e0618091005090903180103110703030507090305030307210c02031911010603030503160801050a0b090102010204080304060e030f071208160b04050309040f09 81
    0x80c282111072102c0240301c0f5410182d1010002c0c44581d490084070032407442c02001580d245001070000b0202c4800c00394140c0940c60034046400c1c000e01000700c04c0c0545400340c404480c07039594400340c101500d6540e80829004104d945c01d2082600011008151500d041d00c800740c400a668001107003144c0e80703100c0d06d0141900500510740001d10039005150000340c2840d144400741d881c1d840705400d65200303a4030b0002044914825003d02078000c11281100b40340c4040030881c9100c00b4a0207920b034070503003007103e800c114506035009845018104010b20707104260000c00403151240f81c040d03c1540183ca444200c044440ca0032400188a08103041c165075014044c42030b0240703404c0844055400203170045d81955028040400c00d10020406000105025541c8210200360003081c90b0402e809410041415003040c4014001a600d03941c5440c0c0495014100b03079500c1e580d100242d1140c0084400007040d0b40199001e1005000c0c000020340321a06040310100702401c0c6013100c40040b2000d07810010400c0304103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 593928642 1250 593927392 593927423
    0x1240b0f030c0909100914060604060e010c050304080d0e0906030a12031e051605070317060103060e04110901050307080c0f0d021011122a0c04060608180307 69
    0xa24007850b0888082100282000071200004a505104407921440c415176450100809070140c00744c1c26000c440c00407904100e04052011505520560040300b092040301488803038203034400d001000300c05401ca4107403034490341c0720348070319445030000001c9900240f907221034107809143c009040341c06928014010300c80040c9956840c03440008081c40c400525130382e00e81c2800b080040d5410b074443d0301da803072030002461318051028161a1141c144a41e08204041c424100000e40041400c9450b11200844001341d0307550350012009081c9940140604420b20810300c03080002078862842d501100310b034000c04980c0ca07001030542d500e0682c071448420350b000c1000900e40b41854801340071020f20190032107141b40b500340c000c68241694078007103400040d4680c2c440341902d82d0510541c03490311009800c031884c0c400e01d104540d00e4807c1d00500c80300c46500d0181034148c0d1a40c01c10018a0503000a00103000c003a56900300039110250850740807840702d540e03d000154130300c030100844418681c0031032442502e201 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 593929892 1250 593928642 593928667
    0x20d0e06090108060103060f0b090901090209010207090b19080f010b01020d090b031e0106020f12041505090a1e03150203010302210c1c03110703230312070201240b 72
    0x30080e0404c4e050594500340896121b0300340070100003030407070a0341031691b410210b41841803507103059001d1b24590f441800480072aa80c0425004100c5000c0302001c40c84284140004094440340122164424840280042e400d0008560056922840002085021035150059803031f030645199000c009070a8141c144491452000079540010700d07114400d003d072080f0100a111a4020b8004802590018003a411586010024500314850056440b8141032500300150040111440f5480c1480b10100c1c07064856203031118814010034801c501505804013100c0500c9541781580015603403232041c0c0c6d07044007881046000300c17812280e010704607840800803d220030700c04800440c41d006550003404841d2400e0342c5c0b92a202c0c2442c081c80c00e00424403030060714000d07204114170310501d007854020312400c2021910a00c402d811100d80c820803031717802d07198400183c1e0039441071402d104110805142030106c4194154400100c103151150000030105110540300002400c611424410220030411840c0120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 593931142 1250 593929892 593929907
    0x10051816180e0a0609050105191104090b032401050f0103091e020303071a06010306080a02130e152706010b160201121e05010906030b130201020f06010e07020d0e060901 74
    0x201c1c8419186a101d584c0e4584069a4020348240c45581d181c03802d111800b02000c40804030b0780310340c100c1003100c40203140303800c0c41c40c0c051403142e140c45076941c0b61721468646090124504c0981401d49123034108900705804440c4000a02a070b501404030450703810180d50080c401d11080e103401800e0044106d003d0040d03580d510489803008c07a014081400803000003204400f26660803141c22281c03600914042e80010112182607000c040c440c0e001462444c05a12803003080d141a0f0110300340814802c843d039121034901008031447c40501d00150307040080415803100c8402001c4a064109100c45082199181d03507080300b0300411012201c01c200e0001560041c46041e4440c2e813040c1447c444640194030a031003280c58000004144a0743c4400c2903075a4110740c416203014001c0e41c8010819203045480b00b00300000001c141140c900410700e912015a80200a1300904814040c112640341d03841d00300d031010b0b0b0b003000d480f00c2c000746c071950003007507500790041155043c00e1001811507030a2100c07070390045031400e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 593932392 1250 593931142 593931161
    0x20a030227070e03010c090b090f0a05131d0721060615020a0210051903020c0102070b070c0302010e0a08070615050a06020706020c1801050d051005181618 68
    0x104400075803103480389070a00449204074241c0d190201c0c02c0c5050014142925200c00c9400c0401c100048103100028505080e10039441c402d0700d107030030311900300004184007440d150800c0368042003504002490380074a03049260030701d64003007100d12030501c140c55596a0321024014040500c0c0c0460380c4501d21052304100007000e84c001d9501003455036992548a844140c80d81070140140c018041c006d0a60070b200761070200305410fa1a0003480c0030030b45c5400551a0b04111075500400da000140b200108100750196031440303802003000101e82c2403507040505001101d0b503046000d5400c041350401d030258081a25035446801403287c2c3e14000295540000400b087c0090340d1b1040892403010980340c449821100260001e500100750140c03c0510192600440d6030203d48502400c00d14101440c0c0345c0840721741192000d0ba80096024040d16250303042510404282c0c0ea070310302d0842009038090b4502100120628240217a1b040c02c03104c001210810151805410800b40780d0b80e14010303101d4101da0000c10070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 593933642 1250 593932392 593932429
    0xf09010b06070614090d140702041b0201020a110c0901030b07180608180606031009050a08160212030a020c0f180c03041103030a020a06091118090606030a020a0302 72
    0x1510000180300394009150507988290307500901c51071107601500d4181c01a0b4031780003e0410b20304600d4000e1800c0b00e0503202000448000c01c5480071511180c01403a8600301c01041401d00c024241c000070700031b403c031a5036140000e2900c42a03030400400412070948910001d0501902a8210303100d40c1c2c0001e00c0035100c40c1c20045000d00d1115200101c0400c00c003d0b000316a01c5c00014205000c0000e0b00a10041c5028042e420980501901355070018808580c0f00f01540041141030f072600b401800c0210007075000d0706104000850030f0306039175290101c0501c0391080311030504181d041c0902540d2400b52405030005030f0300c05040f0a440c1c2c03420a145003110071000342040c09070200d205002c10011401d44034244038800101c03c2c40208a00904208850503041c2c000b1410301d50840740003941c440c0080c2d00500b03019a5106100301780444071600c1150320b00043c0503498150b20000a2140005003150002c60320700580010030b030a890300ac200e114200c0d80003400901c2e000e0454080056415914410002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 593934892 1250 593933642 593933651
    0x105010c1a040507050306061e1005070c27020309060f040507080d12050604090203030406050705031603020a020112022d0d1b0e100c2013020903120702090f0901 71
    0x401c089508514855442000544141c074580400e01d0724140e00070b04001d01c150b85280c26002c140f0a59010218176400868550703960042050041c0e90a100b50100506050343d00e610120380d20003038140f0b4840b25440000c3c0004500c2009003180220f000c10303580e800302a009038011418040307400c110960441d00480030340e600d60b82d561528078600049020420003140a50140031031100641c49030551100f020741c1d0600809249500080d103e214a024001c248000415071000f40a8100240c03011104a205420500f0b18103043c041d5139944155000c0b40010076840b400b4105405034000d41c2c2100c0d6002c2ea40d030044020402009904004100c4070b6107003810309122011400c0064090518980303203807142d0b811100c0d00c2d600002c180c01198000e49000d8002c0c03880ca01906c0c1d510003101078240d500601f408200001207059030b05e04401c01c110151780650028800c4042e1f0034954001c041641080b0126401615503601c012464001c2880113580030643c40009803a00350155611075000c0d00000c000035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 593936142 1250 593934892 593934923
    0x40e160801051b132d0b07030806090a0902150d0c020705100e041b0905180106050a0e011806020f0c010c0c09180803010905010f0506090d02010e011209080a0201061d0105010c 77
    0x155241c0045c419404800c1c05003003189520828080b050020744100200d0030f142802c20744010f07180c001c0241007140501c0e40d4000182180c1e8156202000789035006000c000901e9250300155100e030060301030442c5007440c01508071425400002c654044a101070460084802c1005094031000c40e21440580c1050700c8101e604a0307400c0000d0342c05004030f00340c1c41d22000f42c0d0814041c4510b0841c00141050b00709108001482283e41100075a1060241841d01c0340051140d030004071081004d802415900d130090000110300640c02240121045402070101c0d120b002d1004011500743c0c0581740c0250150359290030500c0800030175007000358808140e400c1c0340c039040050b03030b81c00c10581d100742e00034158140e483c0014408403240440c110001c02c002c07140c16003458404000a510381250200003818015400d41d001100d901901e40f002c6c810f40c20700e80400a03480c0c2070402c01c07002d501880c0024015440c10314041503210082d02c41041c0c3c90100790400006070701b800010f441000c40d8220984000c0701c81e25594 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 593937392 1250 593936142 593936159
    0x60117160806041703010609090f14090105070f0c1a0916060c020f06031e0712020a0201050a181214130b0c210f0304020d02040e160801051b13 63
    0x403005000340390003800c25107024107000480d00c074100800f00300b1328010070042101d40c0d441070102050701c1d00130200040200050904a00a0454164000c0b03900955010004607040651100344540040c0e01d41e00745004142e042107543c0004000c009010f44000300760040801c2001003110350040414044810601c10015880304040c4039500c034000140031303c0d00138011402c1102103484000070a039001411410500140842ca509000451712141d08100010b61303818400c030481440903030300b06000c540d1841c21020081c0648022200d4500c861304240040f1a0303c418580c841c080103401c023100020b094000b8004941d01c850f41004031540030810310a000b0450f0508004100514031806966522038001c503820341003081280110154080d201c180c810701e400444203c5001c02c0c0c00d202c00540c5ca0b0740394400290340811001001e5041880d10941500000c00000c049030f41241d1014174442c1c465460040030b082e202c044545482255095407241110402d500160501118007181d44071083e4441d85103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 593938642 1250 593937392 593937433
    0xc060b0603091b062206031104050a03080d0b09100e0907060c03270f0603140106050d0e160b030f0a0905190f020405070504090612050307081b0a0b01050f010c0302060117 75
    0x1550402c4940c1d0410800c0300e415102300d03809110403210450030716140500054282c9991310000e80340803c00511007840e511141e102010030b042c010442206410656080c070344038507141c02441c118028107000710b45000c4001540b042265030380c2e9528641c0c40d5003650103c2d104030f80f15a01a61301c080350a02400c41c603401d1500040a400240a003c2c601d503e072010040a854004080384200050230005010b166804021681c445010b58404144d00340c0042a4510f082c02543c10381581940341000030a0100c00c07000191b000e9882034802d040c464840e40c0340f14044400311000185551300043c07070414003007140a14030181c9800344c00d442c2181a007079004201507420894003400042d00004051240d00100e10034080603001c00000300c7d80d01012a61001e54a1264000140c40c240005c260814030794000c403001100142410141c400c0c000c500d08c2c0150b40c0250a008442c0300d010003107100d02c895481a000c0c0001c0d0f6825500512041c0d181240d130386001e200040342c0c0809070082680500e003002480c0e81 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 593939892 1250 593938642 593938687
    0x180f060e01030501030f020f150f0909010e0405070902130503030313110109060503060f0402040b0d1b090b0d1a0a03030e04060e0603030712020c030a031d0405070210050604020d0c0c060b0603091b06 87
    0x2b1091390381e00900b0100103a443c0160048015178900e0301c00c0c040466000034500c801d40721180e00041e03807040700c0d1099032603004050b480154144000001c0110390900c0908290049214202c0064890144401929040c0c40b6020343c0f07000550510008640d442c201d0610000300078042c00051030a61246c21150079039000c105005d0301a5101c1a820020714030341d80b010310f005056490a58081414482c1001c00b07481078041801d02c141d100c00341030459a10410160051080c000c01d0540c80e2584e92501410041110031024827407460510009454902c80080a00c01c41005010394505292580d440c036240c44034000b00e0f021031080c881d51200d161002c009059206000b030326528000140000c0d050302e00c448403444d69014034104070030300c03201d11303000210a00070070030f40180441c140c1d41d02d03008a8000e02807030746842c80c154200706030025a50703004028810114040ca505200c203100c1d503030520607103110580d06c0301e043e680114501950070550101c20300030000002c140c40d180141c501140f824013400c082 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 593941142 1250 593939892 593939917
    0x18440d09140d0206270f0601080703050d0f09050d170f12180a0b151503070201050907180207020604090f0c1b0b060d03180f060e01030501030f020f15 66
    0x1118600d071040401825500190520090825103007440444000c04030f000244664910344004190455005012201500f1800c2c0102da6156039161034265a400c4103200a854901801d04061051032041954000c980c0c49600c410140311702d0101806081d81c07a04506032103c034082ea078020a4144980020f00c00740184010658843d03240d0b0036000c541d8080502404104e1101a16800048501103141c0820039000300a003500742d640c1103445400c000c0c0c40e01c0b40550019204900101c564281d80203140a8410380c0c0c02080b0340e50f40d03150115540e4171903019030018031241c5981d1414040044c1c0040c2206440a04041e0500d60780f40403100030b98081e240040e09803511110b0100701c40740e0059034003101515142c5030041d0441e241e11908555035018000500840340640205d040c50302514459074011000c4c0880c0882c01c2d0b842c0b000c104604014014200001ca0803004880a5846400f5882c140d0750030192610070324034a5070030080011400c3c100a80c0011410b031204484107202c40140045000c1e04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 593942392 1250 593941142 593941163
    0x1141b1c020c0d09050a090203090f010c05031e0601091401200a02030c1905010c0303110703020606030d11030306060705070e0a0501050916171918440d09 68
    0xc084650928844143e040108007043d0820006a994042040c003101e1440314016500d89a07910b0450030b0000c01100303074485600704200240f2490b4010000c41c81440d107002c2000e007141048211000b400c00541c1ca25002902e0128244200c030b55260750100034001c141419807800c542c3e82c43d010340d170800000d21000c00e50804d50340d01096060130301031024121400c0741c40c0d18480000800c5c0a0b0710711400e000d82810031034415400c508241c000d60058100b14048c5ca29143c44460501d0021750b212422120300b4024082c2d800310010560142220040b07000f01403010b58110fa6a0505008003900801c4040d40c80d48a220000640412441109402180c00000200b010340c1054140010f0810150003205c507091074000b481079aa902405002c00f00d10051001030607900c41041912100402e031440d541f5043c0392001c01c0140740030b01454409164400d00b03980030029840e600d9000b059034280800c00c5008821348401c0c540c290442d02c1e03100c5030311032812901d051103080148401225421403089030300e41ca24 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 593943642 1250 593942392 593942407
    0x60f01050c2505211903020d080a09061404030324060c08070b0f010602010b0f0906040f0b03030d0b010e090f071103130605090f220b0307030203030a020d1101141b1c02 74
    0x144119101e0001d171100d03030b85030098a942e00950314072103d200c107410809120702065400300c45030000d0500031f40185007440202030b110759081c1d00720f8050758120003181ca8400c00f20f00c025a11000014512644441c070201c05282c00001c0e5144049198111494081040070f900011703500d4040500030b40c801c50b21001290b0500c00003908480f01c3c0d0344118840e200f810400c040c250794000b54194003003015907011908079540e098034400b0342103a003c002d50600001c5407511511406a200c41e0502d0360036a02c4440b108011070600210000039594040082a0f00002442c082d01840c43c24143d04d400c142208d1030514080381c442c02080c41c50b04071400058000681d110035180200c03002207084801c40d00c194031115840540d6a450756100c1180402a490724210301044d80c06000c00d01c0250303009000d40340e0b10951440c0081d199159040320310f01142143d0b00c2180020030520036400300c00341400450000d600e0301c00c0c1c401a220004080004d55000400c01210b2a20311001c0120704105500d1000d03895450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 593944892 1250 593943642 593943709
    0x21b010c0906021617030d0e1b0d0c030605070513030b060f18060f030f060a021b0a080307050322050d02070b0c060105060a0302070c030308060f01050c2505 69
    0x10690103401150300807030394610403040700c481300301c100e8a010705580c00e4800440c003810b040d4003c0c070450080b01d03454003070703855803040340420100140342d00512000c2c42d904005e000c1005454403c803001c7c000702e003495810300004056502254000c2c14500384182040c40031032103603215241030303001100c21483e544180040c50030030441520580404070703424070081040c1500564401c13002080e151107105404071502c032700c3d1802c0c0004094400f45406454562424010903000303503001c18107907000080400700c00c2202a001099a00c88694015a081d00d541caa0320012610340d000a04040503950410385020741d29002c41c001d000d1500d20900c0500340d00c080e50b0780081d003405560b42c024501200f0070440c815074082e0100d001c07030640e20103d51054031507007420402c038000d0042c02c1005040541c0040d01009141d005008940708480848492010000d054011a0f8900451103003100c0d40d4008030b0940e1000b0421085041d001c6010fa401d8540030fa510350002d01c060341410490012070011a81e0008041e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 593946142 1250 593944892 593944907
    0x308090a0f0f0609052b0c0b070c0f05030307020a120c0b03010326031006141308100b0f01120e010f180203010f1104030308090c04060f05011806080604090204021b010c 74
    0xc5c0850b00f801b011910203490344d001041c0003200d4002d003c6c0d540ca0070020854000203900c058280703095a00e84400141c602080513407014014040701c03800c0e40a00180c5890008111042650f0140c1442000c0f85000303130410107088034003030807500c4400840c404985411004043c5000703501461134490fa9110000c9001001203c2c07030581d054410b0100208050840340780204412500e2600d4030320940301c110030182d41c1a0103006441242d21030440800a8588170019a905814900141c00c010008414080260808030404018003040c009d840e1548081a103620411001030400c001041c4059041d50201c1161610301c00d83c000030000c034000c0d00960509209100720100510002c008503518018045c000d401940310040402c5a040300081c1407000c01d002e101c3e032040d000380090121079164010403240880d41d000d2180080c1078030401030341c00c80b18002d00c242190600c0d11010195118801400301420b030501040e87c205400300000100304011295003044259402d00010300203042500080ca800c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 593947392 1250 593946142 593946149
    0xd081e100b0a050f0a0207050111010c020d050c010b03100c0e090114041e0c020d080c12370615020321070c1e05010606180308090a0f0f0609 62
    0x10815101044030000150314000103440c40d1244858964080700c01c21200361081d81254480503201241c2002e0701900051040107031042600d4000201c5c0038032000500322186101214010381c050b29000c060300e4081c00c0101104a4090000b040c2c2c00ca103880820704d480c94200c109216960754502150000350320604800a41c90219241e005951410544070240e00720001501d1086503610310758002000401c40070075468041340e070180036050601d80c000e5207800010f8210000b046500002a1031400315408403400b91000c11503003117017031b00d814141c039015000d14154001079400461107801c6460060200d0120042d44c01c401086203420850040904a0034103400c401307552040c4841c1e607010401d0700d04401e40250070485a41155146001102d000700003d002a0884250081c95000c1241d818a1180d000740114003d21034a5076451013210101c20000b0301c550413403003480c41030000440b145c0003488401d00040040c1d00c01a203840708426102181c1c1c1c1320b1000004124420003075640c0101048008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 593948642 1250 593947392 593947441
    0x5090315160207120219050a0b03010302033d020d020d0203041b0503060403050c032703060f090712060e01020a090911030709030b0702010617010b0f030f0a1e050d08 73
    0x400c2c548035113070340c01c404184e10080c481c130070308504a540c114110418400a040050040111540e0340c000070804da4401e000682c024002c0688100d4011a4941600006040324016000c41d0b072040381c2c031981c00c00040c0601c0c03040c5c5808101c9201c1e0025540040c084c45441400f0050380c0c0e04107450460907074150b4601002e112980ca000800641d40c004c202e2075841030b01401c00c10399071810311a41a04603c6403e130080d01c9506d000840081c01200d807040100030400c180c2c01c845003515261000a081e0204540e00c64081d8480318050040c5420100030101180c443d0b03102086003608001c0480c2a43c221a19590010310400410000d110844c010021444841d90880d461820510002400e014403400050101032804012a406074400d40c0300b10b0041000c0f100881c1034400c0d07640341c140a40800c0c481644201d08030f24100900b0700e400f05d809403107080481b0040407401e0315581d48500500d0f0403040003143c1030b000c460a0700451024402c1d100004245d0703036510414034000b540354805040004001d0780 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 593949892 1250 593948642 593948653
    0x40209030c270f09071208070503030a0501090e06150d05030706060308070b16050406050a11010903080a061409040b18030a02060f091902060f0405060c0d080108060405100c050903151602 82
    0x5401c5000c03031171005580350aa5030742400d044034103100149104841c80105075102c000108108800d4560106040e240e10030b50510142c004406150b544200c15500d419104075554a26000780c50010099055503106d0000e40382801140c1d1a501e044840651090b07600c0000010460700b081203600c440ca0380a400c5040d911011600304a00034010b02560080700c0600100161000d405401000c0c42c2120011540003404513801c1468000c0142d101980c4102e041c500344200031642d107411607051410703400040d04490031035445898007048200c001e0080c15a80e1125032000c41c0c0a9024002440c0300d00b101d8008081600302919400d0700000000c10703c3d0601c4c1c11203404200c50b403582209000285804441154a805400343d0301c0c8142d10444c0d200c19800b810004a0340d402d070801141803451499103844407a100d03030747c0d00140b90301c68804550041050300042283c491983d2582d0080e40030304842e107845400c01c6406008a4038005c419a8a840c18004400070084544200a00b9484404d0144041c2a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 593951142 1250 593949892 593949901
    0x220f03021204062106031b150f0e0d0807050708150f06011b08040909210c0b04060f02040b0d1a010e0d11060c120703081b09040209030c270f 62
    0x1001d1640b804000c00b40c240450804c1c841484294200c01c0103150001140001c10b200f1020340d14480c0e0441c80713140720b14031002e0540300c5114050260340a2501c1c440e213403052050b482c0c208101e1316031000081210038500c03d002041c00f04100300b00340805850f80c84010a145084204100b6078014000e21405200c2c0d014000c000e09644d010075441c851181103041008180364900c0d00c0d5216001d1a045103813818070305001d100038001c904000c001c0c1c41103222840d040c01080c1c00c2040345c414100d107801034204282900410001200c0b54011000070452a4006003016190005983c0d664488101c00340380e6900c402c900008000701060001d0f0140d000d00740280c070744101401281c482c04440b400a001038150380d09864803515454100c41c0034007080c5040c0e4094410b0200395000725040071006a000580410001c1c14400002d00c207520310756812075409081c602c10720f04000295101d032030500e4050140d800034408a0315940ba913014500c1003031031803200e181880720080c80c02c41c6000703101c4003c030409c0c1c44c18007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 593952392 1250 593951142 593951147
    0x601030c0b16030804030c060c020a1505070c02011d04060e1f032102120c150a0b010903062408100c170609071806120c020c03070e220f0302120406 65
    0x3240120743c90305042c111070355079081c160307000c8411080c09420141007060b01a161940410107114042c03280d0641c1d580040820742100440b00101e03014800b280c5a848850b015600550440c0d580505641c1c490001c42c0f242230104099909a6002002104100c03041c4100c2414030000c20207003850b0118418540345c9562201038454900100303480d01e1403201d126110341e61b4030a21070741c4c001e050ba52a5041c3d5a403207020001c0d1b582c60b83c4101010300480340300301040c12905140610b0070500300507500c84000500759241c80004211854510305841c4844080b000540108001c003002402c07403030041c3c0040700d40e081001d01502c42c080c01c0c0384204001c95003c0020b08c2018500e85400503403e81d0b032002107555042e0140c902c8c0700c01d4285038005501d2800d002030070380d034490700c0d00207c0a602d40301030000e441c1020b8160303901c0d00300c00c039030540c1a088220b05105000c0314078880d541c44000030489180e1104d2205035100c0c1c490400e4010345920f0700d082d0360102415010024500c410115840c0701e8542403600100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 593953642 1250 593952392 593952427
    0x60c030207050a060b0a09060b0c061e01091116050a020405130818042c07050a03030f2d050c0c0609090106080c0702101701080102040b0909090a140601030c0b 70
    0x30304c21035072452070b0041c540350010306034081d02e00032404028142d04d800007042150403006255415106520024079040034413902100c401d040b00b0401d028590801042e103003e0068040190030421003405040740308800d480c80ca12049001b0406081c1c101c109005200543e000205034a05001c00c3e4141800010408001c4031250785113504450940645400020081c01ca082042d000d640d40180b80200581c88440b42c402d80c0101101c200c900c2d81d80d880703003032051071100c601c4040c000c070701c4001c0d05591040c0030f00d04c0c10305101c10044003440740703c440020a2100c800b00364001c000003140450042861042000301144182040700c41034100050310700041c0b240c2205006440401818901003800c158550301900c0e40c250b0300412258000007400341c010300201501415550360803000000040450b0184215002d0f501c0b80c1650754504500e0206125040b003000c0c00d01c4559204c1c1041a0010607501810200d5454a40b0003034072032540b441c2000c01c1c0300c1d041070308000d2040308200411801204810340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 593954892 1250 593953642 593953663
    0x1e1106070e0d030c06060b04030813150c0b041106040902040911030105150a090e13061d06070318060e060105011404080706030b01260106031a030c0d0c03170304060c03020705 77
    0x80505590400f445e00303002500e510b500c0041c03000d4010601200308000c51b009002c2c403625062804020350794420007400711800320000303940804c0101a0807000320302c8072503465611038000c407203c8a501c0d6810001c02c02d194481e0380103d001d168045814048a01c2a000702d103061540e003c60613085506100000e103002e0b0040c0f803080401040000c0d18129a801200c5600040030714500c00c7c03000786400304201884101004d82241d546240c0307081d8042c1c14000b48903c005803061030000307015a60f603e8400380e00401d030610030001c0d5150b284208100240b40c2c0e0081959401d800c602400d41c41d4074190000d0045142010b44d034050003070030b0105009160f0006001403c943d16440d01003044403070f040050780c0030b2103203504046a00c0b00111401a900c0031001013107048400703544e01003207002c0a40e041d400ba00821004000d40c543c000a07240e460714030300440720a05450055007220103141c5d0700d40d15034010800b441d10090301103e0110402c4207002c01e82c07092580d0a080c0c2d040951a08100341d03621911546003a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 593956142 1250 593954892 593954897
    0x30b090f06061c110d05010e15060a0504031b030b0702190825030e010f030908040512010e030307020d0e0901150f050c03270406050d030509011e1106070e0d03 70
    0x550b1210301103d1503403801c0d039078006501000406185800000a64440080c4848240c281030000500000320301c041845003031101c0031076400402c84010040241e014410f103c080007014000400411000c4c60200b05d240da039085c0d100503241c911316200b814814010407110664002c4400c540c01c000402440c414069400850240d4501d40d0886181d48000e1481040403000d0501420a08240c2c000800344200c00098a500b980031050f8202141620300d05175005103032001c2071004103d141003101030f6200030030a060011423100035140714a86550030440386000103074415480111050340182e5200791402d000c0d40c010318117604040351125141c5600640008201c1840b200e111841d20600544040c5034552080c0e9540b43c940000f91b041e40043c01035041c403400043c06561440d850310344114021142c01411212400e105900e080d10326810070340456040c01041d07052502800c4070610300616518084d00d80c8074070401003002203464403000601c644140511403070203200540d00c011000391000d9261 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 593957392 1250 593956142 593956147
    0x1903120e10081e070f030609021e130b03160e100504140a0b13052b12050702030d0309030e031b06130e010b030610020c1302030603012307030b090f0606 67
    0x851803a0f010202000041551503500013030103001c503400550016060070f185e40901c485c40d11001d40004030311400f12030408500c04010503400000d007540c0030b03001100e141010580580d036906005907072036100300c50410861910b01098034981d50000c4070100e02880a4500381000702e440640a003440c420341c0206034200034400d07401100c5680d0402440080c14100e4545515081c0260b038084141c4040e000d058030652410504a0301c419901880d0320380c0b9000c510f11400e501140c2c1e201c403c0b0b40c1240340542c0f01013080801015015072020003c1c100e0713111003507400281d104010b04004044510540041d80f00c2e800102150400d03404801070400e2640084a07083d81c0d80080418000b00224981d0010210700c0000c00001f5008040402451090300c042c1c4000c4007254000303000301d84855404503801c0c0e0001c000e07403100801180c282d001d59400a07019000181c444e01d80700d0162a0341054449280c000305400042040856247c01400e210180541c0d80340c04a0910510800841300e0060800d030050001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 593958642 1250 593957392 593957401
    0x1404021606050106090b1608160f0f03030b0402030f0408090f04050108252d050319060b030d080a020d02040e010e0f071106070c02010207051903120e1008 68
    0x455044551945410420410302401460310101600c0b0034483d90340030a5100300d00042c0000d80d2800c85a6140070010820721014a079504c880c110381040c8645145101d491a01c80e00046009043d03907002406840c0d001001c080c9480c000f000d81c2d51940f8414003581c018028400d01844003203401c0e801a43c01200d2035241e00c10300003c1601204001c5d800342c0e001d410080000354005c00410005004050569000c206080da24403140103e82746115030145100400c0c03112015441c8085014419404070b00e98a413029034400000b490105000f50705012000f066a00078104003281c42040d440d4030094001e40000311203102c01420b50340006210007003071500080d1507040211a03504880160034400440d1045503150641f44041c40000c03920816984c42035400306032040c0c0501c10034101030302c10b200246039a030b03207542c01114a200307040c400b01c0c194810600d000c9842d589000058401c0e80300f0021504c54030b46541007000444025521150920400e00c6600d855600d07076100c0f481c801c0780c0c1410948001d80300d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 593959892 1250 593958642 593958649
    0xc07030f0c081e0c010b06070f17040312080f070f0212180306010602100e03120c0903010609050106020a050c040c050901180b0d090b0a06080304151701031a0f1014 72
    0xda403000c10780300307903100e40040c070342c100e00c002501d03030b41407808000c001b00707440e810a100083c41042405407584440c184214000354050130501810b8071107041c12030410750340382e440c4142148031282c05008125400204140302c0d800c0680903030301003110b1401c40c209030b03881e40c0c01a4840040040101c40320400244c41c41c907801c102031281c45d10f00006000c13121150380d1054025111700a8901c0e0403d50f500301022540c0c140301c000706075034040c10181c6004030341c1c0c0c4504151a09a0b40104003060300740d5210200000c2aa00621882d802002075401502c0d500301c0c240b5001d4244a10040041d03c568074007c121100b069008042d96030303115082c241050300720850070003030344001e40f15032109454500001d540752520f4040e80004028500c03032007182d103068440c0c0c10940140c46803030081c02c91030344c0140000c00110048a03200344048016080807508801e498030103080e45582600266006080c0d01c01d048035041070860307000c1c8d10600c090306103105400c16001c100c0c542e031303164802c1800010740710f0384200710f541c2c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 593961142 1250 593959892 593959897
    0x905060d020d02070c1508070e0a0905090c0d05070515040e15011202160b0109021207260f06010f0212071104110a03060504050702070602030f07110a0303020a05060c07030f0c08 78
    0x745c000c07a508101c1903840e0f0051464a4207603901030700050120b0007082c00703540030700c850404042000b407182e05800d003070058810003098020041c0080d48940d804070659915220b280d540120b0255000d040010708102c107201012110809072480c50303100300010072041090b183d10580102028031003103c05001000103c85840202040840d00ba01c0010401040d00c0007508400145101d41001e40d402d81c0d807001c1c42c004078051200701c002550140030000d400944148510f191089140e20941d42c00b01202c0d071682c00e402c000b101c4003440100003005028036980c0090244610060900c01490100341804030051039020302c101c01021640381100c01a000d51b0f0b140c00900040d855829020b448164501c4000c016102d5441018000c034034010105442610204800b401d446894004528205008130719103001e5008400680356003050003540541580c500c0c0c2e0101c0258040d9004004014242c100641000000f500d0541c0010081200380d001940024100e02001c2141c20700348030306590382c2080142407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 593962392 1250 593961142 593961157
    0xf132103080103200a0f080c060c1009020a170609120a09140102010f0c0c0c06051321020405090307031d211501080f0f070302060f0c0304030609060209010f0905060d020d02 76
    0x2220100301080c21103600c81b03800f0844950204031940b00490f00244516489841030110513904811704520090360300c0d8003c2504c2920140030000b106a48002d0300c44511000c25152031540c00107000e1110580c4200904850b000b0a10285440d200d02808003902c0070300309100302505d0001d039040e28903242e8000e5206038080101c144041c0302c189400d0364014010381325950304898202c411480462083c0c403d000381d80c0d158500e2040c06529900300000d54911240b8040f8103c018152103040380c005860718007074240600c514800850311006980380c0907141d04010200a8060344401400b50703445d654801c3e8460142c10b00e50844440202d00c80b40d03403402c04420b0203d1103044c01e03220000044690000410b0b0f04214200c03400d136a0001c859440d407070f880e107207648000380d03103c4400d114040328044c502009000c0321b0f80c800700f100c1c035003960390b07480405490792804251a0254041028051540c10100a0714441c1942c030700200b000e0308204c006905802440301e0201000d03808038401803584400c1e412240366 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 593963642 1250 593962392 593962399
    0xb0a142214130231020c1c03020307140306010c08070311120a0f091211030a0b1e0a1b0e041103010f03050c010c080d020f0f13210308010320 62
    0x9502d4500c0181c59800c0352100224095401007040255018050b83c400c43c880115285a18000060010300c03000394006094002c400c0c00f50241c8501c0d000313001d691140d03066060744c9000d0f0f101c1c903181802500c2c88040b044248a1210204200712060381c2c029034020b4219481580181c0751075460404685004800921444600c2801d00c00c0d031142c003414002c2d20b908025641e42030403200a0a404481548061142081600001800c4c1001600c4a8610a0500405002c40742103801c151122085480d050b03908001e00e446101a0f48851065a8015580442641014405041c420103840300740440d8040c410f081100c0e212a900e080d40e107640050104440082c0c040d500c03540c6550580170241e0072032100312014030070412003252550160380194000fa401500d8103090469021419000c0d510207001c1d10304000c800c01842c1030f080015800751000c0100d43c007400c8410340c1820703001152003840c1c40c0d11032524044091102d0010358403004070b43c1505d5000100f800c900c02c04440c0381083c40d90400000c0d91 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 593964892 1250 593963642 593963681
    0x80f0f070b04061d030a2f0d03020a140f0702090907080d0206060406050415030305070305190c0501060e0c160f0807051005070513031b15030b0a1422 66
    0x14402680c0103002e11003138050500ca0340c00110102c0c260380c1d1203003d59007800f01d07040300070042508000111820300b41d2002c920724044d605540840c2418003010800d540d021a901060095403158444400c1ca01023440c1e44680b481e140300c00e41081c415014041009110740c010000041c110740040c0b1000d0010800541200d03070a5452000c0a034031395101b120154011440c1c490001400d00d40742c026203060320894190942080e0035506c045070f040d0301c185015401d00c00c00700081d41110fa40d800b51900c1c2d400705130343c0313140030701505240241c203441c1139074013110506500d10f003801600b500c40303400c46c1c62040c11481004043d042c0351810b0340711042d00c18006000040045900c0050250100c0d1000b104000700004121564854800766900d0003206004d8100c3c1b43c40703880900000c0e0220041c1210190b1007810070034103503551403d0a800c00300700d2030304c00c002a454621688039400c000c207041e07000d0944e80c1403041400764002c021076500e0b5118445a200740240044054103403c056000c6001400708003100d50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 593966142 1250 593964892 593964901
    0x1060813200325031e020609011101021905070203060a1406011d0a1706090102030705030402010804030c151e060305100522080a110c01081b0909010806071803080f0f070b 75
    0x8482084510041e2921007000c039143c00c481e074050b45c4003010554002d02d003074103000014004494a030a24400c8041542d408c00c02010340d5803022000d0342c20908990341342030350b441561051505221000d424520003509000da07030b0a2a0100d4075040e81d0051007803900b030780c1005664070400d1504208102294000b15103620104400c410207200c4a03403200f000c4221006070325450360f554200e11045802c0f0740064002d002050056200b400e4498105000b49420120a125078444200c02d41c601c00d0414a0540c3d907000703882c051000c0b0401c0d000e4216201c202009000d1070764403a03030340f50744400c01500341da69a124000b030182c1c00190442148000c4050211461103072030701d440c0f903041e800a03002c24041402c40000c2e035004100041c0300714408070103a46500250f02e40d2106000e2004030441d4803141ca61042c4124100e0381c8540e03890b03038002c145030b03802000c0d039041401000c1c1c070120480400f03144288e043d44052012aa0310b1088403020240ba1007425034407508200700c05610701030f40c00010b00c4030380d0210070f00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 593967392 1250 593966142 593966203
    0x120224010303020118050a0b0a0605060a030c0908150105042d02120c0703051602011211071e080304083007030f0608070302010c060f14010608132003 66
    0x1203068900c0b82c1c0003040075119241100c0803001c80798000404942c800c90342c220000d11082c147d00c0d000a42d809005ca011601c480001c0c410707810800407000001d036030b0121542540d40c03042c24240101070f9003000c2c102c044001c01d051850f5040500441e4051174482408084929080c50a40100c14640440b0070140c0004001003000e98030003c00010049141c001041001c0228000c4a013181d80c1034981600d000c5003501d6208841141c1007050f0b0621071542a804a24485400f90a041000c0c80240959640d00d919124501c983e0741034603c0021883d00048000084d800c0040325005a0000006510f6620740000007580d0720a0380b1402c032401c035100e421000c2da00000140f541c01082b00391028003080846491a40444040344110380290f4001e400c200b016501070011a80342d58000d182c041f580008080c0e4075016501d0b05100052107080b00c000410100f50b21140154004805001598240140340c03116907124504007420108103c200054489941d420005846a40100e503051460980c0203c0c20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 593968642 1250 593967392 593967463
    0xc01080c16150608060f06120f060c040e0a02030c0307050c0a15020307020129040b01090504050405150f10060f021005040809041104050607060c051216120203070c1202 74
    0x82440c2500f0f00e8004104094049a0136200c0d0514141c0d071035a039585ca0040114901c2c0b00d5000c1c50080c00b498001c0b440ca01d07002e01a40d0311031160001c21503903079440c0004940d02404000c0144010603c14028807884154010403250021031514201d5282c00b00d4060305400c18210000050140300001c0a04000d4042a00074601c1034035540c000700f00d080140d986280261001c6202c1520318461510034200c2c0745442c4d44000000f040c18506030b9007440d161310105e0105d5000ba5819280c0368824809044c4001490924660010b001c41c4051036504007080348078036440f580d006131030071b01c14180c02142c0058801c00010100124506041c072980c00c082c01d00040310307444071142c140114105061341000024030000c0341c040760b0014007024a4001107071121070041c04000301c200700f004020010400180c0c03d8441a038010501c007100304241e402d060101038484401503904c01280c500500c100701c240c076080540d030f1806640010700050a00ad9140d000c90034504c11480411032034120010400c24406080345 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 593969892 1250 593968642 593968673
    0x228031b02010b0102060c0a050408030d0b0a0815040605040f0b040b040c060c05031209070f06020102031f210201030f0f050f070831020d050a021905030c01080c16 72
    0x2040156024003040480c02d07500140e52039400740c3c1c0480d0102d030790350182030003c0204485d00e280c030600301601c1d11030309400e42c1c2c010705d2044000c40d100c4c0e0b543d0300c091810190100060150b10300508800d8500c10501c2c1001000800c060f01e415514000242404008026028503540c03000324100ba5141c07030310700060200402da41c1500d50100d0400b0100d61503008045400181d07400100440c20301c1a01d200e0701c0040c4000034614180c41c0200440064407170a840e80c81c1028102035000540c807031410303400001d4a10403640020002409109080048001015207402d84440040d0200114041400180c000e0010600c5030120186420030728082003410b907100c1c0340140020b5130360301075944402204131400740003075a440000590b03070038150100361228103d070461500c26400341802200650002140160051010ba520303800c181ca4000461030000e004104103c0100d1003006580d0a100120350355070f0b11000303001c2c1400903103800b0540b00b041c500d059560151032400c0302a0035141c0c51a10009611500d070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 593971142 1250 593969892 593969921
    0x12010603090c0b0c0316060b0312030a0506010c030c030c02210708070503060402310606030c1e0905130603060c050406021203040506040b2823040b0604022803 70
    0x2001050f0100780c602190405007840004500700b60200a03c1c110740841e032881210016601e00d50741d0403684003407260135a00c048600d801900c0b498090411419a2001401c003410400d10200480010390842c07815500ca940514112600f55164404119030001e40181e0465040c170704081d80740c0c2000009003140036030310340b0380940c1c040c1ea03607500505a696509503070095000d410315181d80100084c00c001510a4040c60500002c1c100080f281d000031035085800000000341c607184540d0710603030085e1030081840c005100c2042540761100c001414400b00b070003580d100f00d00d03541d1900d110082e0307a04048059508003004200040c940c00c0c000d011988540b00340c102501403c0c2c0ba401803d5030203010b4074446d6420001400c0141c2ea103079583e810002c1c0040c444501c81c0258500700711089116403510581a0200e6070020304651000e8640c1c05403111032460381041144401040002850309892641144081d540981c42d040303504000000401d601012420208100140f40802945500002c000d1070458 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 593972392 1250 593971142 593971163
    0x24030f0106080c060f0301050d15020f2703100b03011d0c0901051206010302060a1106090f070911090906041416170105101d04180501151503020d021201060309 70
    0x40c0504c1400c0c001d070100c00f02c44039801d000410090808201c680441072165200403140d20105400d0012038001e250800c1000f100030680314903030000b0080e00300c0000d0f1a46c00040c05003c2e440002940d80c0074206000000e5030301e413080722680351425000f0489481485601c8035980b0054482d01c0d40c5c600000ea02d0394468504440005101e05041142101c01b0000c200074000c0d5030f0961f020b109280e0b0000d50301108000e01c000350398548900c28441c20380a6604080980b08030b44800c401e0a00c0c100c46604100c00151038549000b1250703e0805c00c8480400c13003135840103c10f0703581c1c0000400a00f4100f212281e01010039080206800c0000a48100040103894000c031110005000e12159402405001d80100c500c83c28020541e016003403524008a50601030500c620080011805035403500c00d05a14a42403040440c0810000b03002d403011984180e141c40040d00e2600605416464986030b0003020325a0010f200c541e900c890ba01164011581c0c1c1440754036950755514010000d003421003068541d1042d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 593973642 1250 593972392 593972413
    0xa0f0e0d080c120f0d0e0a0b0c1c020a020d11100509030c070f030b0a0f1d07050f10080711070801060b0405040f0501030b190b04180201080a060e24030f010608 70
    0xc03800d480d4280c4811843e58141048084500000d00c00402021b0051255003100d8000900008146100c1c91f0040d0f444e540360202c0c0e980c4c25500340070a21300b071080c02d03005000c08201d01394001510981c81d0594540740d00039114240b01c685c14601002c40c0d103d01141858104100c40c0c20000042402c40d442070100c07200030b41d071244064010291400014204c40c0100c011401d0790000c0d4008012000e0071040001c2c045580c0103604d00c2c801da281200320016000b0302c83c204070a10380444c00c241158000c0d03e113500e275220070006c02090450000c000100f1b010524a10380b00c0c1210401507078002d0801c15008001c0581c82e4008082103801134070500d1300c02e9080c502c40c0c042c00a03650003124102c1e41c0c490326101c3c0315250701e03d04455200d034590b01d0300f481c640d0350308444000b5510f90107400011981c400034042d00e40070f80e00006040401c0200200c2e801420300381c0c00c01000f4180011a07034000901081005884100c581e5180c49000303044140354188034094054090b010190710060881d150b550448005802 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 593974892 1250 593973642 593973673
    0xa080f070f0f031506020606040b041401051c050d081816050f010e0406120309051002120702010e040e0606040614011407030e03030f04050301050109050405030a0f0e0d080c 76
    0x141215140005001c2900c1d41042030300460900051020b58200400c50701d000080005140002d50311600c010307405102800103504061040c00403004055400307020320200d001c007808284e441886002d00a844420000e0700d2940396400e0f8440213a8044292a81d440080400825805064030250018001003610307064040c800100766000c0003140300050303040c0345040d08100204082c0d00c0703054140002c00010a00340d640c1c81c402d03a4046e100c44102d500d030501c000e040041c0f55403c2a04540e002d0404071000c0048aa0000750814124a40c0e03203034195166543c1c4012588102c0c07114019802074149240d4035a4803a01040c0944140401e4804200135640c846070703405251004204180851026030203d010000d200c0010301210f8080e08058896080202c046032031030740415003034488040701140034090b900d400e024040c01861208414012824541c07105078581c03007802d14220910810045174100c0034018688150501070041c441100c1a0460a20982e5648440d099070709600030420784901100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 593976142 1250 593974892 593974921
    0x30306091a09070509040f0f060b0a09120305070602030127200c0f03120a0b0303070209181c0c06150b03040209090304050405040f02180105130c03090204020309030a08 74
    0x915101404414541c1c0c1060001000002e001c20302001070400040c140d90310b45006c2c001c4003e800701700004580d00a49244000c540f8160410f1917156800c00c81020b40c968001480400d960b0042d401c1642c3d0304042c070381a6014821140020314441c008400042c030300e058150301005455100c3e04080399540e08000303004c01c881c005d044051211001c40c40704510690b01c83d000c0c3c8000d01c0002d0031240d80c0d03070040610070f02e15004080d0203013220041c88200705004d2401d00900d14041020f40c02903050003542d50008202c0400100b0403e0045401c5501511940082004038440d000d48103021050340a0050300606420340f000d0306a910364108050103a4034845005200116180525503a055071195402c0051004014041012911007400085130f01d903500e11516018510650b0098103580840c41401950f40303d0301d03070035000007540340700421440d1a144101d11038404180000600c2c07915406080e801001c1d41c103400303504030f440802040b442140010083c0140d6001351908400c076512860408200d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 593977392 1250 593976142 593976161
    0xc15030c0c080f0708091309032607030f0b04110301051509030606040b0d0b0c090a06030b0d03030c05070f1514010b0702060a031404030f08070905180403020717030703030609 77
    0xc904120f04845014a18007030104144140360403840e00c0000f04c009481480794041c1501603d5890f1500b10402da040444039101034500681c1a80741c4510f14820140c134200200084181a02d40e490040b44151a6015821102c3c1c0140100a0031800401c1c4024a80007400b03054000d00c000505004244458010f031182100010010200c43c1d0311082800080c0c080f082c20290000c5900c1d40040000340e100104620500c4014103994540325600104030a1401c1030303200700d041c149403848407281610f03041c00c2050702d16003500f004591200c1d0201c04440d5441500009003500d00751000340e40070030414801164a290803a1030522000d088184010301c040401c1c41030700280001084810300504049010340762102103400c00069000400380e6809107140c0454048001840030704c0150101c5820583d69901700c200c600d0019146401d060100709891700003016060032010ba80c0008082601c00c2100c040a012404003051354822100602903a80d084084120080303410001c000c0707000e08641c491440f29 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 593978642 1250 593977392 593977403
    0x150801061d0303030c0d09080414030d09050904110a0b1303110102060c07030806030c04021206030708010509030f1b030c07030b06030a030c02040209010e061606140609010e07020a0c15030c0c 84
    0x45880d00c58005200e90b1014240c6c0d80100d0700c03080720102060040700031b00010815000000c2031005c00c481014202881c43d40c43e401804142d400c00d0007183c0b076501c11958465403101c4800d000c2d03c800782c00210321803100d0b4000002c5080001c0c0704030800d03405003500c07400c503803290031051016051840160380ba2901210000718000b024411000401e01c5102d940303820640140946032414034800c00b140036070b40040c3c4200c407081c10440074410307035081c1002000004c00d2842c0c000c10682c28101001502c92041905800412202149006a408903103107c0c07503419041c0000c0320b0703442d48202100b5858150701e20040d1510940c0800103027041c100401c041c44107644c15500d80d0b60508090382004000e4024611503030410800f58041c88032910342d24020300c1c0d00300364022140c51099041c81d10ed0169140c2d00f0031036800204d807406102c402c0e11044451415500b50382c6034018a41d4865a08034a060410640500122400a800901c908070340c2070600f6400f000e5942071010819000040d2540e10408200070030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 593979892 1250 593978642 593978647
    0x70f140705090f0103171c0513110d0c090209010509090906071101020c062d07050415050412030c020d0b0f16020c0a060f090314030409231609150801061d0303 70
    0x345841000241f00854038900d082c1f59030700140e541802250407c8600c4c4940002140c1d4110034170009920804080c10120740a030b58800c2d10780d03a4002d02c045184079002180e9000f0414941d56802502a6202c681c80900850604d00d4801c42d115078440040e1a01c0c0b0104d02c2d8464609101c0e0018000c80700001024001011301c0d40b118a0014a403100b039406031348068014044404440064500e03142c0100071541d00e05841e98104488080c00589001c0601c0511200704406c02407080b041c03e51002060301420407030002072443c00420180c0d01c0703144000381042c1601e020440348440c0900854001c000e041d14400e0381403084402070b41c0c1d91210864996202040c044200011482a581040d8100e818a04041c1603540c0e540c600400c0c14241c0c054001e50b800100d001d21010341c407441003c0f40040b01344c01001e1050500510321780f2550014144184010710341a4001c042d41c01503908800900081075600302c83c032401800103000d61004e000b5100054004d520310100c910345075000096481000340950b1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 593981142 1250 593979892 593979923
    0x3030c08090a1706040c08012702030a0c060309060c0c0206030f040503090a030303090b070f05030c0c07180209241b120c030705060a06030b060105070f140705090f0103 74
    0x40e16040280039a0b030190360504042402c4a188003c2e101c080e000000408581c1400e01d442110301146030031002d69a89843c0440c04120216221030005c425040702d105a11030450010a04081c007050000d098031501d900000f501035490751140f24002d0241408001c218068041154014020a0065441001070000c50b200d10508290309420501c10401c49203010803a4021803c0c9a401d5401035002c680c0d1074182000f40460311071003940c091603030f140c94001c44610110241139400041d040841d1801c000c81d02116213882044000003900d41c113400c1c2c1100300c0d0580a030030080d40c000e1410b24044ea551120706c1c2a408841c01c10008160004200301c1d0030000101d5500444402c118045001ca2107111054000c0c0c002c80d500410000c1d1080018607641d05050a20354a0304c0405008041445d240080400102d0040314a89421000920b4104c1c0d548001382001c600c0c4a5083d0360103071580b40700d1240c8420400000412800f255400e03141d614003a541ca18000c81d540d50244005071a00c12160200c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 593982392 1250 593981142 593981153
    0x106030b01180f050709080f0606030706050c07030203060c0c0f0706020d0507020103060510080405150709050103230c09100311040302040504150f0212010b0c1527030a1803030c 78
    0x401150350b140b00007003031902071030904151501610b200001c41c01000c414010358000344040343c0305401c0540102118201040803c0d500c044a220342420440d01040125081600703012403801107030001e0403101c690510441c6c040340c6500000380141c29100d100440044040045807490403903142c1e40180605201440044e14507500000003281055555500450680c2d518040313449040c02c0c40d030b81c204091a041c5092441d1074200070840c04070501041c03c2102090b4021401d0060300ca0a10700480c1020305440c00d010750f812454031a602c003407e5001041040d070310340f02c00f0308a4410200d5002c0c020705120131054049400302e034101032070401c0c10803050001d0b040032341045030840d105580b03020482e040031454004403001c40040c6810590000707800300704600110002405020000107103072401c01c1c1d40304481d640e0044000c200c8030201050000030b0001d0f980101c040c08448842d001a040e40d201c01c0c0450b9129440000c8803c0482c80e094010141c10714048000801c1d00d60640361030b03510384540c0d16031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 593983642 1250 593982392 593982419
    0x30a1a190504050a021c0b0108130f031d03010c020115050a1233020a0e0a1d0709080a1506060e2b0c0305061b0a020705121e03030a0506030106030b01 66
    0x20b005a139808000e03501092208400c102c1d50000b120034001000c0120300d0005081d01001341024a0048030140307010007190b141135100ca0019418203044e520354402da14482003528132450010703410f520703220500b800c0d42c1e019005602105410740e620098661186c0402503018118024107a00d0700e2107400ca02d001070348502080044030400f0080c04440b804011200540e00c0c0300340104125142c010074400c001d0380e0020715103103413020211084400f007030801c0d090006210140702c2298510030582f0100303c5203030050381110041c10409040d503111a0482c107001104c0060109004540c42c68194006103082c443c620070a0354040040407400d56020701c1403403403d95034100c90181d031615001c2c1c0200c00000c200c40c07200700081d8403c03409003855141049041d0600760b2200700c0313003500100401280310400da000c541d080a0384c404803900380305025030481c0c8520304808580c5a500501c0c16070706820344003800001840c420444a030b41805140d4425080c03600781e400c6844014042c2e09040014402030305800e51 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 593984892 1250 593983642 593983651
    0xa060915020f270f0d03110d05040e0a020c070b070519060501030506071d150d1401150f140f0d111c1413030c08030a1a19050405 57
    0xd455403194518200d00040341e014156418400303000084914030340700200c00032400c0b11840d0800c501445240d070040703604441d041c41001d20491804525a0405d030150190318180d440820403100980e01840000c0c05a42c070a000e010550415240004c1c1c0c884440d000301d0b040f0020680103403a0462500e440030400340c00019084070240a080c21003010b80101809603d0300d01d002c0d000214003540b641c04c001e8201403002d08131504014108420b807900e20350181044048817815503000181c0e9035134125603d140d006422980401e541401d5013102420310124119042c1c031a945845000d88601000985641d4140c004210200754cc0515408140d513954010340401c21000b00c50320302c1c00710b409490b001104c4d8420704800a5000124000084141c10142c0b1288104000000c01401c424000d180c84003d1004001d595102000a00e07042014802c0c08034079520b513808800705840c0d0816008410151404904000e203049045007818003e19042400e4804100103583c0c0700d42d003a0911040c000500700091 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 593986142 1250 593984892 593984903
    0x61006180b0f0406030f02181509060d060f0509040c030b06130c12060b0913020c010e0a0c0302240d050402010e0d06021201090603080a0c0203100501030506041202030307020a0609 79
    0xc03400190224034400070b1800c0003044035001e94903400d10030080d045610071001c45082910601990710081542c2c00f49200c004400c852101040c01c410584102520500341402e8100001045e8103a0712450f640000043e1043d6010790801203403284203010965070102ca010713042024003201080452003c00401e03420000c040c0c54801c5000d000d880401c1610141d03101540000c040d41c0e03a002c5130840314400d4201415402d40203601c3c2c40900000120741d80d01c0e040e10704010360b60015510000800075032044004500481c1500c0c18240720f81054204280e81d0b1005030b00800340004600e2210341918614000204020859800c0c2070b11440b0540c018500200103c0c1400752010290b0038036500d43c640012040e108050140c0c0c1d03419141c010380100d48040c9d00840c0c5103404d00d88107000141640c3c0a540d00380405103049a0300794010300019140802c00c00002140700c2c0b13800004024800b0105800384100d004504401018460f034034102d80d41d101c00c49414005800c00180c0d00b00056140e0003000c1c402c1d0180303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 593987392 1250 593986142 593986187
    0x12010c0503040605060d170d1116060b0604120c061106160c141b040b040b030a0215071209030201020c0907021e070308132c0402011b0b0c090111061006 67
    0x87d03462101145000101e00b81c03211011440da001c80308940100340440002d524401e007000340b840e8407002c40841501e401000c01342c032030010440a403140030907034000b0407d50301c8801000c20345080c111a854114042c00000a2081000003c03e180c00507880d4002d8076a1555550000e83c1840100c41200c801101103460001d02e407451070141100300150819110841e1202c4203001b1424100021521000280c0d80294200600b460544e80d01003001c000203501035450260140c8200c01a920a10030b28030000e10042500414813600f590101310320098a100303800310b402802c14442048015042280c030200143d200c500081041e0000c084070803844c0a40000300c851060700ea581700c1403190440343d01d20701d050300c130080208100301c0d000845016030680900107070701075165070b00010f80006d03000700080d0500c0702da00308071040c070044110b200d04055040507040f01c4a0503c0305070442642d110300c000e01d00041c05896400f450700804030300503001c1c0c4110040c2419030381c034040302580c1800f858520245810803d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 593988642 1250 593987392 593987419
    0x5150d080d0504030e0f12070303050a051c0504021e09061012020c0c09060d03020303070311040504050906042d11180103140601060509010c0611130303090512010c050304060506 78
    0x5400b4103030156103e500c4000780b0002000500c41520084103507144141a1401e20b2020000040f6021040e0f82d010315000f40d582129440c1901c0341c1c0300c1c6100380a080d640311814042040f585901082c041c510841d86107030b9140b24181c2c1d01361204400b13144203600007200300224509140c11b07041441b1170005030608030035043c1c002405030300300e80016400c1019600007605950302d52030443c4500d40d020f241242c40c64004011910020742da030000030b001a00b07140d56510680c644003c1c0c0800c1d10000c0400810030b01a51a003924000e031100401d45080b1095900c40c0c0005001013580c01d1440440c4004c0600c03280d003104241c8a0400e0100b2104440e90400404d8491342c8014055440f024040c40c029040c4a8907000b03034820180c51302030141d2190003048824002c100c416a48a010000c0d40b0340c00800108845180302c5110f951032050041c401d0030403104160000c00c040d0005024402c4400490f01d00e2240708150080e58240c0d00c546080c0310009200300002400200117900907030704420007030161400100c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 593989892 1250 593988642 593988667
    0xe090601050a0309051f150e09101a09010801020d0c050a0f08040204020708130806060d02091305010608061f05190e100815041416060c0503121303110105150d08 71
    0x1c1b050170201400d61200b403040c0722040e54840d405c000b007040782007021b014540016560b465032199056400d001e80c032103c0845111031001004118100d004000c01c4540d40c0d2166941d000b5800450240f2010b400c1010303602c1080d0088d0f003990030401c02030729000307183c1c070a041c0c04480d440d10051049922903800d0103c1000b00b80044041c0c10102c04202c0341e500d07070707a0800c0306061a0841c0246150b104103012000200143c80e0074201d190001c0b450a8101c6444880d4a0801d0142003241c002d0b00c1a0312804080010040003150b90114011440d44111a02d0340c540b4140311040e03020b0020300b000390f85d201004101203000385100035401007503039134410b182c41c3d1505c0310f26080c18400641201044403180901c018007240400074400e40045030010210001c4151500c6125190f5104c3c040501882d001048140b2606004031b034140944242960913500d41408684541e040c03003101034001403207850500a59400510409005030194450f180c6203981035410898450411101115008414002c0c10a00f08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 593991142 1250 593989892 593989933
    0x803070c06090f14040c0e12070f06050f0a110a0c08210304050a080901110a120906081014010c05030a08011a0f0f03070207080304060503070e090601050a030905 71
    0x62254080d100458074206005084074090703080509510780c03801e8104250040c00d0111074100f0300646011a00c1c2c42c0011058a880b4040880d00e034001c2c1c0d100c8005490003501180060a40b42d40a94101c8043c3e20341000300c5e2540505210600303248030030441441024080c0140c0c155080140c02101c101c10200c0c0d40e1088505d00301d03800044550b0103510541705007140c1ca8940414003c00b804c1c12421031a154950310b540e0002c1c080f000d07002c0c00002612030035a910980c0d40010104810703007203c80c00142c500d09981f0103003020018200242ca0030101041503403040009038081c0740010300c141202030500c00004d00407180103001905108001c0f150034006041031010b8a0000d00703c0d26101c100f0f40c500301c02070890026030012024050710400c0703081c1498102000740c0c1d42a218400303e29031690b440382026807404250b60000802440089000100180d0020046105580599900303018101c00000d00031503030016260b05010403401d100062031036109521541150b40210201d40c1c40b000403280240006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 593992392 1250 593991142 593991157
    0x3290112024303030b090a0216020f01180807050f0a030201140a050d050901020a230421020402070f0501150b0a2f0a05120301050604050d060f021303030f0e0109140a0803 75
    0x94a0701170880d02e520303040c601c2c5680090700800a52610119600032842180308410080c40340c0100714484007543d02c20401c080700c0c5140200c4980070981c0310202940c0c0c0f0119842014818106070b40c07051410704061384050110b9a0685640780341c4003411000d10010b400824080080120900c0400107404aa02407140039000719030005035900d03203801d40140160400030401d903416034401c1c01224800f1011081300c00721080d0f2198074190b03070305180d54519074192080700654018008602d0805000d610b0030000106480f030350080103800c00310391001124050310700c60306071400c0c0140000c8800c2402007110a540f09890424440c10040c0c0161030003180710a000c82e03514940c080e200308020001d00b00200f41c0b8100d0146010780c00e5605d400c2c00216103209a0140341c1c02001481c00344001c0014507048200d071035035040b100350340b951225280c1505041c01840160001208240503076032460140824040c024010ba4407201d030141010250440c0c80c08140c016030700710001c0400051148024800352484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 593993642 1250 593992392 593992397
    0x50c010f14060d031814030f121606090602040902270a0909020f040c2c06030a090201020f0615090601081314070509040606030b010806010602031903290112024303 72
    0xc1e2151b01c0281864030454600e041c249900c1000c09900e80320f03a1400750303814a08441d0740100b90041034a4418046d09001c040284254008600071610804035005485824248014920036000e03c0036081d8510407407008898004940c00c4050000d84110740000c1c1c140b90000d4120f03458260b0250100b012611049040c000050141e41c80d68000d0140680341d4185000d1185d11044024904001550740d02c000741c54004440c1d541c07107410b41164000d1015241c244221000d90311140380052401c0503201591b02c1081c41450340c080004c480c1c1d8060100c0500800000c0c2041e44200c1560781d40c607401740b0b0400c044248a00c101c410020b56aa209180188664032540d000b14a040c51031402e92403081040e00440066000f4000501480350300000f52501c0c0c40000c4250343c1014400c41d0160002c0840f0700030700c0d169403001d00c0b1051548815041402c2882c8080e03031401c1d036404400c000c0b40c0c200d015400284c3c00710464001e0301003d243c032003e691000e0907410a2480001c550200321440700c0d558001c8120003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 593994892 1250 593993642 593993669
    0x7050d09140a02010f03150b090d08040b07020315280609020f19030506010215041b03061e230907170d020613020904060228050c010f14060d0318 64
    0x11942d20004c0585c880c10300e818180018000643d99442c0c4030900c1c080c050013084082154503003692080040320349103810801407030ba1580c803404010307110740c01a08242d01070310511003001c420300040385801c2e201d04011121585201c900d04d40e14045154000c0140324036507101d0303c01241c030b21500d200803d03a10a500ca04255581da00b00c40c5480301c500c1b2070040c4014185050104a1030703903000b0403e0404400b1612008419950701d00e00800ca501c0d40000b000050202e5050102c204a0783e98001c19540c04101c1c401b8100500c070350000340550365404181c0c03001c00c01e20f1100c442d0290b840c07903050350098002c40a0f1800b8549400750341e100d001c1440c010a040782d00c02620228400d40500a25400403800d40c080e007014040c940216500c4003018100410780c2e6400a003050102c1085c1c100e1945104104420032110240694001c115800c00008112035502c0c040f0200800007061040c8050030010040242581c1c2e214010043e1242c5904002d50070711247c0209169106520440d0901600d0509107860 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 593996142 1250 593994892 593994913
    0xf150e0303030a0f1a15070f0b040309051201060602071715130b180a021e090708071403010f06080429010609060c0507030219081506010e0a0b0307050d0914 69
    0x1e042c4c4000d01c107140e114803002041e001d590740f10780d121181b01d640711000041d07940c03256181c540c06080d03403084040e0010b00b4901c2400100369200e0311071012103108807480340001c114144450708a480303910030b039005603200001c20006000c1d80841c40300282001030540b81c4c00040d044020760f1030305088034914440f001111401c41004030480c3c905070000001401c001300d04440b101215914030081c2c1001e441a0703289031074030700d08007040846400108005080048141804103029211620034ac3d00400480c0350301c24502584075842094a04a49081150b0400c0924101c070559a0b240d028005607107412000b041450070f020011908114464041c2400034190315020004206810980000381002081308100d004034030300140400a880d0120b6520403c1d15111444003190030b461b901009490103013051851407211301d0310300c440c401c480c2a00c03a225600d040000700541130100b40a00c1074000024400329035594420400381c004030300c41c003200054120140e101d140205100c20301010b41c40d4050000b00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 593997392 1250 593996142 593996171
    0x201090602030f030f0a0902031c0206070f08130809090c0405010f3f0e0f0706050304050303070e01030906020f0304170306030709050901090807140c09010f150e0303030a 75
    0x41026201030b504214000406091501c00500040201c0765070001141b21050958032009102d0360003800c0380c656910725400c09000d04070300000c0300f01602803840054190f6010340303c2e0780b9405002d1b6440104642e00d000d04028040445801520403c0d000c0c803030310002c0d8030340880c2140101042c1c1f0016031109d00d003a000403c4000c2e01d4000c00e0400540742d08c4440345060780c4000b140d1928184441194501c8440868004010f011140703084035820048040500040401d20070002903203d000e84a0320b0391030740c0050310984401d89000303196500c1080002d40103841182d4102518605140c046003d803131603100c24060341c1001d403c1d00e54084001041c0010416180c2050382c60840044034a800c601d000341c0065243c1584e440380034100341d21031001401ea21800e52109403002e41c2725485549600705810200d03c401030040203044c00344501c0080c103200d032400880a41c100d82c5c0d26450038420504000d007942000205952440901c0080040030362075540c14409544107614002d80060410741d6a2850b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 593998642 1250 593997392 593997407
    0x5060708040b0c13051e040c110106050301090f0210030608070e07080a06080d030b060715020309120c060417130305030c12180d030c0b0c0a12020a0903110118080a0201 74
    0x951280d60030410403241c0e2489900707110801c6910445103641c02c2495254000502c81b0034500f6140c0c842d24020042042a41110a42200100b200020010b49450300285801c0313a8500e20041c0c491403211500b40014074060300310f14044422491b000c50f0311039840403058075248143d001b04020705005420805400c1e4000189940f242803a2418003071549440b80c50f40d00c80e400f540180c4101f54503079010000684501c01100d08060784800032424102c0e03c202414000c2d0000c1e01c552180c2e02034000f58090404805064400845011010f0412911560b0b0703540c2c50620324a40c207001c031b11002e00003103250030030481d40e41005500030009142e59103aa116014100084050504190769050000806145403da86190405815281100e4a1780c0a007001c0d00c48c0c00090030010b2562842c402084a5480c02902030301041d006503c0b40c0203040641c8022409030f02815412000090341c000341000468014402d0007807840040c18008002648050070b000649215000072105602c024282c00c02c5580c40400c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 593999892 1250 593998642 593998651
    0x3032502040b190e0a022a0d02060c09040b0d02061201090e16031101021903050a0e0904150b010513120c05030601061b051227040e030912030705060708040b 69
    0x41d80609020a000c600d542040b83c1c0c0039610108082d100065001c0e1001c1c2d048030003916080e0070785c0025941070398805c0c805140700480d1034824020201c4d141d480718000200d0301c1c01017100300c2e41e80307040c0400c48050200800c0c01c494481e41c0661500b070742101684036000200171511400c18540190f40c10314206405445d05454801019408607030381680d64481d2502c00400c2d0399001d941401c0103c8030000403850250f104440300d081408a40c0e04508140c0c00400030250a48540c8448034440c03031520070403102000440303028201a0700750441c01d0070f0b0003541d4070698820340141005030401001119120350302c40b0030381007501440544d05a0f0340501c128001401d000300b0b8200d006002d60340c1001e4000300110008503e400581030380f103c03040208181403040410b00e075107410340a130300d41c40011592074000c0c0c1c0c0344080d0600c034207240c00036400c581081c1c042d801e550319080c0e008614141011085c0145002c8480d08071015000601034000003510611009020b04520390303440b800d40c2010304149503e50806032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 594001142 1250 593999892 593999899
    0x503060f0609011d0406030506090604051605010f2105010f0302090c07020d020111030904020304080306010f0c080a050a03020c070b0a0f2a031e020706020f011a060903032502040b 79
    0x1003881c01a80e400164110216400c1c00710402001301000030401421054200911a010b60410032909260005140d0b201d140204211941e00510307015085044129000d03950000e40015449540980246116050700100022203440144844c4142040715402e0300700e620341e908485020025460000780580d009403200c00100d2601c0c00941c00207104c0e25680e84000d040c4010701c10715010380c070401c1c01500c0045038081d1040d176680c0780c20b00c0c01e50003d610440e900e034041a004101280c003d03100303400d030000c5264400c02152502c0c0c00200180c8240c4c01044035001015000c102c0c400720048103003c08002800c10200082d2101e91002c1d001c0c1100d40400c858131300300448a03442c0c0c102e14903501034010202400000802d82c1d600c150408848003c9010241c0501054201492014560008014044508541c20744c3e0341411400040d9098403488000d00200310701c00c12120341d5900d0850000c0c401100c00070101c87c80c120560400c00c20411a520403c061506407170f010005506040c000d40e1040b0000301c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 594002392 1250 594001142 594001147
    0x9230d1113021c0504080d1404030809030a02070306181b09050117210c06090d1101090b01230a030b0a1103010e04030809030c01090b0901060801151806030b04030503060f06 76
    0xc070f0b0032000b8600403100401e4690700c4202150503c030030780701164070084142c02d00f4008094104009030110009490440010f103005000468103080401680c1c44069140d002e062075038a19203507040500001e0282000d42020000340b0b0000503d001c00701c002e14015000500340d1540b403c8030002c2122816804100a11506607403070040d040049841044c174408000039181002c50078800c404a8007071152001101d100d84420300104402c001040d101c003070031541c3c980111b2804442c1a500f81e43e00240001c054001e02001849401c10481c08400030f0240d03820b441404c007a1010005a0392441580705039070007082072042c03041a04440c01603d80d0a807444214038915450024400000711004202504100703106000c40c3d12a40305004030fa030b50441034402800020243c0c00c014260010544000d4000d601e04000010a040103000f01c0c160303284940c2c00004401e00c1c6c4418440c0002509164040d200c1d40c506000c00000c0c07090103124001c6009039a401c1d00c0340f900300d0030700c0054030801702d090b4400c0c0f005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 594003642 1250 594002392 594002407
    0x140a020105270a0b150402030a1b02012c191202011802010e1905060d021b0622061b050405010e010c0b2a0f03040c140109230d111302 59
    0x20a483c00316400300311021103640308080c41034411a000c034055032190001081c4482d070f42c201d800840e40c2900e06a20b140002c1c2c03407480c043e401c0700c1011040c100284050005000f0f0071009152040c05801c18405985810381c0500d04441c18100d541c404641012105680e80c000c0d0748c1c2441205503443e220402c500d2500b540b500060040d11074071103004c0c810240d6401681000d800200c40304014103000e8089500c8d0043d40d0142c0700a508455400e0681c0e005502d260740c0b074040300044c0303580903c0d500e40c980283c070000e0001002c401d45481c0c1e402c0c1c4020742c40702e8012140316072198520410320069030340c154071542004001403d000c1102071850400c138540302d417032001c107280030384040d009122418900c4e14041c00e280210803101d500d06a001c0c1400010510b4501c0000c0b00c0002c500c502d10034181c0503105511080e049840560311001c0d1400240141024010b88100c007000d60740c10454420b50390550810840000c00707250660008547c0c004800b10300b85800e081045441c03400e08400242035082035103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 594004892 1250 594003642 594003721
    0x6181a01120302072d060e01030f02030f0a09021903061506031a090a09050303040507030209060a0e06040b0103020c190606081b1c020a0b03010e0709030302060402010807140a020105 80
    0xf07016040c0d1800c000c1d17007401280190703000700381070003d0783e1710b04040341c5555214068414040d002080d808207040621340e40c20301026208580c4600c048417a501c030b00c0c0d201c440d460300041400d0704049030480d20f44103d040c0b00310907451901000314890580441c84104800814a40700d0080c0e101105160030524155203500124510001c0b04605441e419010380d07461040700301805905d1400342a82c0400000d120902230f0100f9074000b0f4900039104046540c0310b250174401603c015108036066071404102091701840d0513040540403000500d00981132031540101d01e8100300e6a1000e00a0b50145030001e401002a0340c002c2c030004140315005442940501d81070100d0b03440e0800c842c54401c00481003841c4c1c030b0101c051146441070350060f103492201901d840362503c469100f0b00590340c042c2030351000905900e10401040c010703a94164050801601c0310740c01901c4080d4003900d0041072042c5003d810310300000110180c0708280c940d03800070601c0d0901540e02284801c1144214250a610000902c0d0740903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 594006142 1250 594004892 594004903
    0x7050409080304063821061b04150c060c030203090d080c12070206040312110d0209130e03090a05100f050c0c030703031d010e150706181a01120302 65
    0x1a002400805c1c8052a0105080f030581e0750364054004403c80d280003564250312242c2c1450320f20003591840b07900800d60b690208a0b40d4252400c2c1075a5205800240ca003c000740240316006c620703204aa410541c44200701109955484054400140313402c11050510910b401030070010300550404524604003100c5254641880500d03110910544801203421095013100702c51640580d040c600346181803000300291200c00588081d000030382210211554091580701e1090350000190b074132441c04810180c90006900400c400591102c410006503051402d1070003000c4480800c10055590703005801e040003d02204d23030708241c3c000c8600b440d600c2000f80c2c00241d224014681400d15036292001081e13100d103000c40c05040e41e40c15000350200041056045000700305458011303070f211322600b90181d004440b03400e0045c1e0010342c0300c10350006140c000c3c001080104141e43c010035010031703e14810301e0b2031102c041c1c0143e1308540400b01c0d0f03a0006040b0502d0034001d0f014000c455400000e8201f1134800039580c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 594007392 1250 594006142 594006151
    0x30610060f050f3c041202030a12203712260c0703050c0a1209030c0b121815040f050106050307270b030d12060b0702032a0d14070504090803 62
    0x401c6c010b1400b405565082003020000c070760041550fa84405801e5000700b45d00000b40b45a4100ca03103640003855841c10202c0c0d042c0664881c000340355070000b002c1041da0000469503804484087e29000c40c5404106241600c8811b0004c5845850741d0001c40800100407032101d00481000f01a0803090203144a074a50403a003c07950503140c0b081d1520711091406080c03480e0700000030b01c0d0010242144c100309420441080489009140c074000c5c00c0c0d5240d000000c0e5200341807030764032045001c42c0050b081d0300c0c106035840c1401c81500115010302e500b0102110032400245d5060311044c0d0b5603807144040050034000c901c041d11083d0058540c182c6020a201501103c0b441e080351807100036a60880d1440c1194042025000001d046030110300d010007014000145200695849505001012418850440454983e030754094000c0800004414102d9203c041340154000700c442021040c079101d596a00e001d9001c6030041181c8000000c2c2040c04c81d140c407840b5480a4000e41c10000741d00003080846c000c2d654072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 594008642 1250 594007392 594007409
    0x10914040506060f0c0606090a05040b070f02010e0d020a1511071106070606090f0b090108120d020409090305040602070e010617070306030512070c05030610060f050f3c04 75
    0x540c1c942e400001e0150040f41200c81200304041007a40044900140c0d00d40a110241c3e04181c031078a5581141040d6202180c020341528508404039418a00c9400c00402504444c400019420000c1698a042c01100840c0c0c8005034000d4003040c060140c01c082003410a42e034035508100904503051a04254054081c1c09081c19401c0b081e1480d10f5200c880882d03203d503910034400c104080d19841c0e89001000c9845050050911b404210b6440d402c0161026040e225900300808080b0104255100194001c1e0070b03a8603459000e002c00201e030900c500800710090b00c25150140c42e28200342000b03140038800e0b4021403c0f05400401000740a82000304500d065003481e0386240550b480b540240d01030409075200400300d01c10851502401001c180103405280d1040c0d020107001e42d566020165a20420340386001914502c910410006010302c540784200110350600c03508000325158100d5050300302d5150141030340c080e60080c001c0c0c62a80401d240d07040c0d00030158101c40c401110840303a500d000e64040e4056 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 594009892 1250 594008642 594008651
    0x15020f03030709030c2321010507030c080a0c0e0d0c050d11100f120209010c0b0a050105030d030e03030612342106050702011e0603051e0c01080411100e03060601091404 74
    0x100002e80b40c1c01d995403824600020b12140c1002c2c2b400400038002d0401c00c01c0065004e030081010700419001d0526040c90a0f0340303c0d055900d030309040201c3d19a4101c3c0488d00c05c0201d550003c1d144d00d07030780c0c0801d0340301d4040e080003100d070b06241c4140b00032002d5078500030040204152050700443e40122150501180340c03580141c0f41c036810300050340c070440a218082d00e40d0104008000111f50540c118034140c034020b0701514590403403120180c043e20406840320425800500000d0043c0c2401546040c044804404070341c0000c8640f1901e201c48207440000944000c119010101040552010040204101402c140300706c040a10516452070300c034880100050344034004074080d18400d4210f1408418806900c82c003030580014200c008003000d01c401ca8940c0543c680d0001c5264007500915038045200f006840f061000d08011562498014030455803030241c686103290a07150307240042a000b80a8503080c4407250300038209840c1c00c1c801404941044401c0c90b0602400c046041c141803d0b040949003c0f4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 594011142 1250 594009892 594009919
    0x80904020403150501080c0102010212060f180903030601020c0d0203030306010c030315170c0a060c0b060402070807050d031407020717010b15030f0703060302060415020f03030709030c23 82
    0x10064440d07540b0140034030709101c02030702d0600d9013580924100c454a03c203e410159421005a0907806640926801080020002000c0381030207240c20140c101c0080601190881c05649150883e5080d20801b480e58804030030000103503010006156007404c225031030030020400703500207582d170300c401040517040203110381d038680030903010350440003004602c426080b81050701d80c2d40901244e0030400c08110300340f08407406842a8202140042c2c165541950b8041c54180540c840f03142600c0c01a05080e0456802c10041002c02c2c40c850290038030342d106a001c0c3c0303a03000014000605039030015204001c480865800c0c490001c0e00051200c085a519203011606c071088a00a50300411500e0780076500040d09102c403118003440350000790b10489100da0b02d55100d44070394130210304598603030000940000c4100400d2204050320307004081199035900c1112034045010003001d0464000782e0303907200071811a10080c0208054043c0c544060207081000c2a030000c1410380c0c030014442c80c069000e00481036502100c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 594012392 1250 594011142 594011149
    0x32a030b040206540604030f0302030f0d14090f1e160602031317120304020d0f080301051c11040e0709060311010305150d020f120a0606060314070c0809 67
    0x41c20a4010005100c400718200340740000700d4100141380910000084a1426000d0744440ca1016a400901124181030460351606a5a0b1006200740c0035480140102144202a5401000142e0044202141c02c400c0820389680c46440a01010f03c90f4100300d07640d6144c2e000c001a85002c0f000070341803058070400319140103820507610590702e80400180320000b10361550004000c0000402d41c0e0314020702c0547c1d400e07a445c2d488007888029580c0d41c1140000700120309071000610f401c1400203084990045107580d5031039041055038800c94503803002000420003460001d8030b4139040b0b04988041c8036a000180da50b501103264064006200c2c690340e90307040415100401c820400341050742000c0200680342d00380207403102c0808840c3c0c1c0c002410100001c0c1000301140e000c1e2818840038085c081824242d03402c11810310f03041003100d6000180140c188010351401c101980c0c000340103410000d455400e280b00181035403001d030031425030411580c00307208541e648420641c1038103801502c00d80d01c035005031000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 594013642 1250 594012392 594012427
    0x2091005130909141905070e1e19060911030a111b0f0601050604060c030e0619030b180c0301060525060b031c05042607032a030b040206 60
    0x5854a54900030f0007000300996620503a090741e860100715914040604c40c14003000c040c4280080c1140c1001c042000303450840d01c00d454000000c0c0f80f0440c80003205044d0304144100440e6200c00c9a9070301500e802c2254030038031800e8003070200f8040901070b82031441d0812410307100180c0481500e56540ca065494800188103a0b415022400030321b41d00300300010089075603138040303482e94056401004000200d034034182003200c0c100c58464075801c40802140c2c505070f480e00d516406030394201c00c0070070428000e8108080c2c1c02543c1502c0740ca00040c1c1c44822010701680c41081c021354505c0f031010340c1c00d01920703443d05405e80341150310600d000c41d602c500101c000300e81c0e4029018082070502021044c8410403009420a40245c0342c1034040320001e02019407100c4201d5410310072440405e20400c81070100d4a05061408041202c80d02c0541c02d0030500f012062425255a00c01d8880e208015000c0105101c51017126010b04210f800d04160542544c591441e45000504001d114200001f00401031344a228070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 594014892 1250 594013642 594013649
    0x230d03050307030e06070e0d14062d011202042a0921030915030605130c0f030504230c03030d0c02072426010f14090405072702030a020703120209100513 67
    0x10358099040100b0410144034010034bd00100c40c0e14084645206540748040d18121042030403408030024594080c80b0050109010071508400d04021041860440c1134003014902020b542c2c0c0106207140610194108080c2e03544481468010410030020039801002c03901600c510201d5910060003500055000713105552000b500400111090042540c907079008032100000d03038540714514844610201c00b12a130440300113001d64610040f000f443e03401c0f0202a04106040c1c011904030070340322000649142c2003940030001c02e580364820051003a40c1440205e0042c41e4001c100c3d40f403c000c1c18050a1800030040100c010030040d4030503420502000c9969011042a8043c403010302d5844074452108101140107514074240d20204400c4103041000100344516000b40190112508001501c00076407401018481100c0005400b1010400c2030310046d4080c603010000142d60b55628580540565610480310620603c180112a05a180c40401c0c0082e00c0c11407804c5903988090b8111802000759981 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 594016142 1250 594014892 594014933
    0x90b040308030c0417010b0909060f040b090c0d0803150909031c0f02070b0f012c091609240303020c150d020c030301032307230d03050307030e06070e0d 67
    0x814003209019440785801030400c8d00c2c009040e43e1015201541c42e54184c42c89200b090f01800000c0100e4514a14075801015072810703607400d090080d000030300a91840f001581d44032000002d2002c0200c40c1310b900ca18000e401d0720b2050f80340c900b80d60604d80ba801351256910040000c51000b611102c00740d840b0020b08090704408649035903650074000030070007044601d030b020200c4540004c20940070200d4854803400e8050001d401401800e60450703042c10700034081001c1d61003500d14004403001c2c00c40b4828046c0034610000a40b00340710300c01ea500c45058000d0f040d69403000c02c100500110391301041400c1c80000c00e45900c09402502074202d040c91184c1000110340d14800f01e01400381c004084010b42c1224022001c0c5007401f4288052503d03080000c4c150303031800c0d40c0007800400c20300e65049181490850180f0000864a01382004950f100c0500d40f02200040c80000070048556014480d480810044000928880c588190041e01c14640c4aaa00e4420300110f1844020803400384004070500c400341 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 594017392 1250 594016142 594016169
    0x1203151203090603020f0a18050d05100515010e0409050a02040f1e110901120f0207120f081012020d060c0906170903030601050d0216031806090b040308030c04 70
    0x1482402803040388098200c00258540500080c40b512038001da40d40051024200d51902c0500d0740d050b102c03d810904424101c151021000550755034410945140e07c0c0600d010302092409020031504031b8000401c000206050001c025030540d1713001c461501a2107055400140c84540ca0805c1480c0c010a100004e50050824410341401c10542d046003400032038007041c4201d820440c240c98410b4034000708513101080c0044c4600881c80d845212400f20600409a00003641d00c04c410403501640d00412042d2204d405107246039660360740c048104a4610035629115825050043c903611031400188105108046001222415980d5030b100c3c3c83c455941c0418100702205004401a260440510689e1b01142904803440700d40c0d0340400f1075038810070500c40503501c1e5a541400545480c5c000d006c401e040310b5400c0c044010040342108002c003105019440740c9203180c080605c90480035886400c03d01c02c00c080302808000404511054400f070320350010000c1c1d1680d031104d030105502e004503808190100d642 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 594018642 1250 594017392 594017399
    0x51209031905040810020313050f060f0601030e0607140c030318160806270102070f06050c0c030304061109032b0809030a030b01030608030a0306050a1202030a120315 73
    0x8010a1404141012400070409003242603500e40614440e100554000148504881196034021a4000350f00c2000703102c1c55015440c1ca0b4a018030f03059030101198410310a001d1500140700c45c850f030201c2d0900c1d09102805040708003070345841c0003070321910522112070103a203800f04402d010384180d1f01c00102100d44a00e4443c0a0079010010039405514034010b98201e0001070b802d42d6841d80558580a00030042034a4140c4844036032030201c4050800034402d0800a0300d9031b1802e00050290750700860401e198407038141000c904442010f8a00c01c5e514104110301c1074906400b00549a0040d0003000000c0c8802040800c800c4034400c0e0b440907627150141c10200c08190340121106111401d049040c01040c41c003004043d14404003c0e2503510980e402407040c01106442604801c88180c0c042c034000c14155130b0f171180585103402810307510380800d072111070502407800d00a004074014030800b02949031030281c035008a07464041d07106c005040040281d07880041103010340c001800800d0300300400e02c8134564 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 594019892 1250 594018642 594018661
    0x10c022107030204060801022d0706020c0f06060a051e04020403080a0815040501120b06010201090605091e070f0308070c0b0403140f1609020d110a05130b07210512 72
    0x1075a01040380306030715000e4040b507818814804e4405280d10038903480c40c1da41200c0485500e0309010000c5003014042000301100017171890000d445144005002003c502101403421810100018017140c060b9180c7c0b00e0410a56440c069003002da6104141d90441c9001c0340030101c1c0180c4500e40000d0140c03030380041c20000050780510038921039056022003812800c640300c10442554004e10802e80b408802003120300200d4003450010790003010500000070b002d0351039035460081e650f0448400c0c215070003002c42240c00040910203140c13070003041000342840c076080545403080344645010280407403034082031000c1004140741488029106159665469503a030789001c04140994440e041454018044200c040500000348912401514541c0045003400c2c448103000a401c4401d0420081ba25901150b220030401c1008140480007960380304d5843c00229692140001241c0c410803040d14204001c03000303c0d00c0b841107281c05000d40400204440b820f180215142e0040341c16541c0c15210800501c201c196 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 594021142 1250 594019892 594019903
    0xa0207080d0c0201091208030103030806040f060923101e270b0d120e04090b0c030601090815010b07111c110a0b0315031f0504110409030e010c0221 65
    0x18405d82e03030030860903142c0803c290703a0025200c000b01840000e00042c00040d0040c110194440d8001d4400903018a0005095082c0e0311280c0c0100e2500b41d9842c0744d000d1090222a803010015241c50030407200b0b0030114018815605d81c0d200d42c819241d00340030b2011140c6005178104c80141900019102d071f030b80d50007440c001842c80038014401e49900d0a132407a54141481d104000d2103c0e00410000080b5108600655054035074038503880d44650303607800381c800003038402501900418404090a840c2d25101380050400c0405411444181d40020419184090320310801c0d410758100c0b01704d943c0c81300103a182c0401c0c100340d0151819881030013054040312942422143c1e02000c0e00648105d41d144c0090010700c6028000ea00940540c0041000000d00d45a003441c2ca40070364141c060112181c880301d04840c440c0c0703e19a808554031890f150418002841618994800b0191040710304001040c22980c014000d0385000e000c03c0e05105068039a4002c1d50707503850700514002d503a100014620040c030344200b85c561 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 594022392 1250 594021142 594021167
    0x140d0c090504060617100f14090702010e0a0f020d150930030b06090a0e091c05030402090a0f0203090c03070b0708090d0c0504150305012307050a0207080d 68
    0x4a06403000100c0745054060301d0103d03a81c54a03030100920104107183c0002200828030070300c40b0328501000402d4030a8414100003050040110150020010100081d1000c003401040c11681010043c00712100007050090042da0f1201c02c1c200941b0fa41c1c40850000f080c4010f010b07001c46d0a01500c0510340e0455008022a00e1158418240c1240f485c0c02d05200f03000f0300f074010601c0210100e43d0319109030180c0c0c8581c0c1c103c0d800400d1f243c2003104000001c1c000300050741196504881003c00e1107031035001003052500c10a40e100e03034a030b030300c50814000034014000204081c1c4108100c0303020503c0e42c189503120380000c0035240710071b56413443c0c6401d420b40c0e40c00c0e480210078001d10501c10b002031074005000981c0c40c2c840c1d01c800014540500c040420030301c910000020b503556010380710001040d585506c201e07035202030040000440e051843c00c100b0b0031035813024007c02c44102c2c03a012807002200b1602e26580d0200b6142400c60300c8040c900000c034138004541d004a0001e11030442c10b42c01c19500400c403500308 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 594023642 1250 594022392 594022397
    0xa2d09050315102c01031119030215032707060f1103030c0f0d05150406170607030e07050303120a0606180e0604111804241401140d0c 59
    0x326a4100c5005034414044880c80041e0a141406108180d0311914582c81500740b1100c0030071301c00c85a840c5041c00b003030a0b0300881d0a0060f044042c0e000d802d11031551100e101448034040c0c003c6255801049a8504100410240000c0040080c4840c5124808108000310b121851402e101e26494025961202c9000e04004a000203111040300e500c51484220250f00340c1c2d01071030450b21503030540ca0b0543c100d00800b036081002031000d901102028400e06209003980700c900c6841a264a0031b000444d00da50700207180300d8510f0540c4828803080001d08036002016890006541540100845e0400348141c003c44c0c0e150200244514000d400c1e4007000f402106011020480713555102070549501088201c010340c42104c00d0020031450000c214103035800207020b84040350248216207140007590000c00040310a0090051081341030034244124022200c03146902c92460145051400e10310602d80b145d031081015001000c09542d00c24500c500f031010106c240700e82c65000c0c03104203034050500418140300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 594024892 1250 594023642 594023653
    0x803042006211308182103070b061302071104050f060109090e120d091101020601140d0f0501050906040506100e040308250210110408030a2d090503 65
    0x20145031040071614804519540403400400c0354140e03501481004003950f080050201c0000003083c0a24000c01481890aa5090320103101c0e80400000524075100080d01c0300c9070a80107040443c0010480f40a281c21203080704590751918009421402c1110520584900104084041040c03001048103800011103042c801036031010303082c0c04002e00446003603000400d004410000004c075680221031140c0f4a1041e01d0308000742183c07807410340e807111020600941d543c20070501840242e42a01d000e4450074405810254509400d406401114440b00b501c1901c1c8070b90080c1c104240e103005000155488002885949042c69000d901c41c44115002d8403a03008440c00101c1c203121441070721080d901440e1180384680c03540c0d201290205d000a001000c801d46c41426880000102c000340300805540d07070b00811a08038002890030650f201468001c80010050009104191003c01501d40c41c0180380b5040b00940000031511000725640c00390f0051a000090090131200d41c081180340c20383d803095080741e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 594026142 1250 594024892 594024953
    0x120e090a050606040308030705070f0809011d060406050c160308120f070804030813050604050715080402060706020c0a140d030515102609031201080304030c06080c07080304 76
    0x426240111141540f00404000070300000d898031b00510303040405407401508010b02940d4030a90601a03407c29181c10f03801046103121036070320050401e45a00444c82101c1c0c120a43c0b404030b80f0783c2c01540540340038090086103442800700301300003603880c1243c03104d22000d880ba40c0b030030424010740c0850780f0802000300030000121401c54225850307010f0341d502d45d00d0b00300039a980d4404940c80540509081319140c0c075171100340b010030300c00c00c26940100d0280c000350101500e4030100d1030815262035030240c14803003d2070401c00580c0d5980b040d90040d50b0420009a5111110981681856800d4400030401d410042d10110403060005011400c10540d850400154441c00501e0055240c070041141d48a10030380240103c90b4450b40f0102009021035038140d24004140c40f0329114440c0032a05600568008505040840305130301c3c48900410041c0007030741c50541035441c1c00106100c0780c06000709110580011540c196040e80c115411150443c50b01e68403428185400f000d0a10380c034100102000702005031700c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 594027392 1250 594026142 594026161
    0x402120303040302030306010c020f030a12031518050405120d0c02160b0d0b030f010c0503091618050606040306180501060f080717010b0604060f110a0b0705030a0603120e09 76
    0x80380610f8041c2c00075400c540c1c941004550b0386501d80c100301d8211480002a000e562420060a00d00c103100c2d100310300a4030035a880040403603401d88a00032018130090f10030411115507a91014000700b4020020956903207904016181419219005200580001e0710407450101a484000946e6040d401c2c0e900040084840c0c2c80320500601510010a20030800010010310580c80b04040c50009811340d454100324945603821650b40341500800300300000304200c00d80d00c040c4604950754684c40240c40d681e5003400742042c81c0c42c042d0f8401d140819030b10300100d0060f9880c4e02c183d500642c0c0c410030501c0001c03002d100e05803d41403001c408407070541c00c003100405e980070081020030a41d030015000f0b21420b440e01c1e80e08001505c0c0f459038132206550b11140302c250760302c80500031b00140030291103580440c3c22142006080d07402343d130031070b90184c0c1103541c811000805101e03403550002c00e6860110748944074031031b01400800a5510003840106000444454650802c42180c002c81c3d0031620941642e8030500302 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 594028642 1250 594027392 594027397
    0x602160c1d010e180c27010b2b0b060a09090e0c060904150504060f0e0a09080a210606031506021902090414060f0609131709041e0504021203 62
    0x81c0340f03420700000c001442c55003400e110b6000440b200002c480140c1401c03400300c2c546591400c1c0025006582143c5c503181000c0c55445140140000041c0514040c1145400e29100a00c001720f1020b4414506a000e405210341d0031a4001e043c004240b180d4629441e400949a04400d2241400085c1444e0110080b1900814403440094000c3c0c4000e103032030016810880241206030404000f84008840821580c03202d2040c600607200c03c190202005061513640303052028020001001d481c1490344402c001072a04007524140d80b45800c20a141441e114145549c0c1c51401d4021014185040c02c000340c49907041c1c2150050203001068410b242303880707403400ca80328000920780d05101e0402e03010324801418440398456120b80030740040c16500383c18038095030404005440174a9120f41c0001403004d10b1511004c1b05420220f2985555016910360ba249121680581c07448030b060480402c0c0b0400e80e40b516046108600000c115220030701034945d185038020070f000c0c0e8041c1e01034507400c00c041c0e1260000004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 594029892 1250 594028642 594028649
    0x50106080a14060a17010f050115020f0a030e0d0f021008071d090f0a0b0303070b040302010501052e110123070201020a12180804092301061b0602160c1d01 68
    0x15400340c5d09001006505082007003034998150b40c1e6880300b11403650240b044038003a001030305880098942c2260300901e0840f4180786420103400180c41c81c000260406e40e041c2d000f03581547c0c00460fa5a090418886180301090043d400034414140d04442c158045521441032070182c40d0303e18410220f042001044c000c40004d680c21001c4c00c4040b404c0e05490076015035001c901c03000080303072900c80c00c000310b0b081d5044a00c0407600301940d102888100341d0280540c5000d884c0541c0e5181c600d0f0003c0f0701000311011800b0b21b20300c1c2640032042d841d142c130f0b1103128001801c101e541d00034804200d18600b554100c400f825007403401c21005c0008600814418022124410003954031144a9821180f000300104843c60240c1c00d2032000c81c1c010300004080f500604000c0c4102500090f2005170000c0710f082c42c00d801840700848074488001400708a8000155101000e0360007000c1d401d0307d045141c0240248155280340380b80c4a0a00054410000034161f2582558240268008402c0210800c048000020f02 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 594031142 1250 594029892 594029899
    0x3030c0703030207140d051908100e07020703020405090a0b13020307030b190603080301080c0102010902090c09121b01110706021b060d050106090503010c080112030e030f01050106080a1406 83
    0x6001181c0b1907000f8080160051804480c0700e05000082454030301140c00d504041040414030341c05d45031000300001c910f030415003080049440e20302c07007110240300940146e821040e124030100704006d00c2040706001035580500708000a04040303404543e100c3d102e01c02110b03039541ea54002051911001c0a00d003203168060f000780080c03030a40d6181220b12500804060884054419050600513a07000c0c000085000c0d000159483d41014021b07801c14401380d05440c15607042c8420540140c8079180c050380c0c08445201c9164550203c1c00020340841e00224505809106d401c580020b4102008055443d000c803d80301c1e000c000e04e880300c043c0d03242d011794801c400142c2c0104401c00b2040c4892103601c1f44150b0000d11003483c1225145005040300c40a0300100b0010701b1017030042c00036040034440d184491384cc0d410b00e0b86039585860700320010000b5420b0014100501400a03441d0b42e2001c0100c1c2e0302c40608200240643d42e12028000c0c070412040321b08680c0715040407550b004107400703e9030351070003a58042c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 594032392 1250 594031142 594031147
    0x20102180f0a03060c0c0f03050304020a05060c12031306061403060105120a06090809100206150301020f0418020405060307030b0420090f0303040503070303020705150c060103121206091d03030c 85
    0x15294080185881401c800501601b08000c0b0005201c036407596010700e1007611170729100d007054010300101e0792013078015a0045d5000c000c0d541544d400083e100b0f650050a0910f95a203550300030518003c003520101c01441c2e103080072404580d28010210986c110001542100e03550386c1d039002042109461500400080d40102c0607403400b10781d081d0000c03045580100c600618107503c580100d010007829840200050308031509020052800c2e0020503502071044009508201042000030300510030303441580d61001c0a8181d49001200d02d406540003084020503551300c80c50641e102501508545916500c200d1400500c0100030301e90444810604480f800710508107040801800902d9991280c0789a2622060000181545d41008018080e500c203a024094144c41d00e01440310003100c8002e078080b00b030340507c001e045405000401c0350442e41c21000c030f10129100360750243d60100c0781d0000402d82d22f0500c140441d41e09025040344485804601c111031103503000b0b200c2d031500c0c3d0005403140000050308 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 594033642 1250 594032392 594032399
    0x3110708032a0429030a2a0912050708030403050607020f070b0d050612070b0a0e0a05180a0f050106080610110c06090f0618210c010f030b10020102180f0a 68
    0x70b9164400d95035560000c4d55000c40d00c80e00d507000310380c00455031246100d80711403e000700710005102004103411046044d8102c40b190403400350948149004101c0085141640d200501074100801001443c218040d070303039170710b4807410200e8039044100e549401600c20a1841010103800003400e20448a80c10407450900d50072000341000b0381b002400703690f0300245031074132140011020300144000745030410515950740c0100038090172a203180101c0313078400c006d0704008100c00e88801101d4045c000b1440102401a40d074000500018603d0309041c5e01c41030310380800131076510b030404400c0d0700400d0229004400103450340000c80d10080300303104480c0f09800c003120181040c00d0081c09043c030407100800c0d804055003140042030440e044070721942c8401051a03004030759810140e4107a480c203402007100d00b00c107031500140e00327070b0300c1d82d170408040c2c10000c0740c2c264503400601c2a0301884103d48001c0880181010400001740030307410407400d01c5c5844100803a90301d02864400d501c0b6060f000b02a00c6042106e24 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 594034892 1250 594033642 594033659
    0x80706050c060411040912050d060b0f09010e0616030f0809030a23211f0e06011d0405040327051f0207030c030803010e0f071b0303110708032a04 64
    0x24004e0195082521515220001050446041d643c800d00c0d40d40c043d11a070866480c0d03000d50320240e020050401c810040d8160194140c02203d995541c01e003408686010101c01182452050021207a0041076050f440c1e02059404203103034111920070f036120a003940316100b0954503842000e14142c042031081d40d100e82050805070305030135040d02c01e0b0103860600258500201d040c41e0349109000d12003801100700040d96002035014a0071800c020120180380307003804500580d0801c05400c0c24140a200101e001110110f0004d018070b41d42d01400901407800c09240c003820711400c03c0030b4200403902800c00700c1ca06100d240c8030041100c0004141c4000c154405181895003400b140a1004600440e0320110104e04a11400d100442c8150045950b0750314001600700100300282c02e520b20200c010013803041180d03205002034030071995060070f007003035507001d00d41034004121ba801c0d9031040401c01b003100ba0910000c0d0025511400410800e1a9150032a411500c290031602000e00c0aa140c10320052004c070a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 594036142 1250 594034892 594034913
    0xc030f1807080706030524100305100302060d0c110115030206070f05030c030d0b0402030105060a0503060f030f010c02190507060f030b0a0f03060c0206270c09040309080706050c0604 80
    0x18400c8058601e1581c503645030a0404400343c000801080d200c40038400d0f84c00d40c404910318010b01c0c183c420043c0d1902c02000400f0040404448400c16031580c0114250750030012042c2c0046034010012665070007802100340203052603582c081d021600000500a00b45d0040c0101051880e6036482c00002608642c02c00031300303030400c80c015a1000882006000000c00400c01481c5041d080001107172900825506002607030a0b65248500840c014001003100b0384401043c0c509140c0b807820560340326a181c1011806404844650301c0c1e0510400300319803151302065100140c0c0410640c240c1b8800818110821050000244010103991104800f0000548692070b50003c0c003e452401040f9604101d000816080301d603049407a0548004600b0000c0240d02d21030502c001d8400e0024055514040c840a2000030550142516402180800c042074400500040200c01c01c01090f4200c60705150500615800340741c002e10150b8880c070317040440d00d14015419036440981420041000741e4842c3d46503141e06 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 594037392 1250 594036142 594036181
    0x18060302280b07050c090f0105150f030105060a0302070b01090b1206040804050f122e0b130b0d0615090e030c0c0d0f0b0412080c040503100e16090906050c030f 70
    0x2c1c020200a44240d55902890387e0050800b54030421007941031a04009d8041c00480c180300c55100c042290780041111441501d0455004540207915468410020f802030300c00c031203008014091800020650301c40a5200b03100000c01910348084680603200280d60321001560040d200480a0001304941d180110a0242001e0042c015901135450710130300d00e25007d082d0f5285a10741d20540c025109042402031201d0341007198000501810004401007601d01d0310700500310391960785602c81c4080980b01c18503010b4945501040400c00144c1064100c80608600e00440c3c0003e402c0078045a48920300206030b40b0110222000343c90180d0910b41045100e8060403012141d145204951801180062a80da4030460050703494040200611400524079407005143c07512602007841700b44040d03100000c2c0c40440710210302000800f860210700300c91a10592120a200714085000c0100d800e000c2da402104030988a080c0500c21901c5100c4e0140f07039800308030340c00081d4148100000b080020361405e0240030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 594038642 1250 594037392 594037403
    0x1e03080a031803050405090705180d051e100f150e06150a050309011508120304050f0d0518060a08041b051207141002070612020418060302280b07 64
    0x14010b81e03081c1d020010103040198003080004c10304001b0703420700c00c40840d8080d6043c41c12519208480c1d10380050004500c0040d40944c110303503040c108000042225011413240d4403c00c001e02e1495115281d0741d091400d050310403050901b42100c00040082c05044040c8804c0d0814a04060624144c0e03020103500401580e485803a60380010300c07404000c00205240091541c604e5542c0ca4511219400e440001c101c0c40c0c0040c480010070401041c000c910812075200b20941c40ba525152401c0c02407802401c4014400303d409200381c280280c07904140144a01d0101c0c42919040704805000c00407540a40d007804000300e00a81c002500240b25a41d00000c080c3d10706138440d0100391035102103451201a14601c030f01a5004800034030051841602d00c1002d07400c1114101071f001010000203486801620485091180c80742c4601c882d50030a0b015600a06540780c020747c00d130340c10ba070043c1c0042c040e1444180d015014881004d42800180c185560341c0600c000300d195003092031b0680c031001c00d070f018030000d440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 594039892 1250 594038642 594038651
    0x30f1d0709360804150816090b0901090f0803070b01091118040f0f0b0f0a0b0f03040f050a030f1e17070504050909060612060f010303030c09050603100e011e03080a03 73
    0x15907010040e002030b0074145d0000490201e001e01c041c0130b03250041c042640b80c080c5044000310307403a4800b20810984445060703d03610303030a2040050718002015040000c947e842920003250f6410008042e1a0030b6000f0905481542d80c2c0322104811516682c11124000000b00314a5030b114601072048201c108000c1c00001740d004a9500034801c0f20030320080c640785151500f800344500d1408440802600344105c0d140454249025429006413207018904095200f0200000d0284950701d00c802400d00d0300f1009403021103090340f50050007440c15240c010041000c6141124a00b0002a1416947d207030039100e8101d50790b4901c0e0601c0e40740b20000d003624100101080f0109103503c07101040350003111400300600450901c00100030a43d01d11101d845042c3d40030404201e0080319a441c2241166054200001c002d40400c50840d100c0304280c00254001d40c0000500c1100508500a1030442d4800000d401d02641c0b1440c140d85100f940c034501c105600300200c010300206010000a000d400036900b070018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 594041142 1250 594039892 594040001
    0x601060f111504050c040c08180c03060906090d0e10080411060403030504081b1815040c05030f090303070c230a12030b0402040e0115030f1d0709 64
    0x78070b0850140940240c1200d1101800300b0070900300400205210125814014000007980080c070011009115607100b2610711306c1c110140703006020070356603a940601616007501d4101d950990742c0c00c00781c0d81b000c107521864980e031011510510700100f50340001400001c507070b0401a000c03500484080e005540c00c1084c011301d400c580c0d803204018402181700c4d0f2140c41e1240d181030381071400c040084001034030400042150303031007982e50a4810541b2070101400d01045490340003814018015080002c1d402528094110300c0c2250050f01451080300c1c507200c100055695143c0c1a81c8901080c0c5000000c40d002551101c0020580120304000f00c01c10140441c000307103180d05191416041860a5461140d00c00c64101c17215898010134114900030f0f41c040d8a880c2c0b406581017030f207100510a407100c000ea000c00d03200d000c600c2600440051f040d106003d00c2103404104401a10300c580040701e01c201c1c03244800c0020405800c1c024491100910300f0400c0c04040079690440095104100c59044c00c1d040c0030014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 594042392 1250 594041142 594041177
    0x5070906140a09060602070b070c1a030412020a02130914070303080f0f06010905040207081303060b1201050405030304032607030b130e0706051804050a0207060c050a020601060f 78
    0xc034001c241c026035400301c0040c0c5209020003190b4a0b004400d03800d003815820300200e5000500314040350400100c2c10354803220340c18617140c10344031034008c86030305a4007100d541954540ca0b0055401907000d482c8442101c94046d1303003079964403880e1000035040046024040c3c10211142d102445050081c40d0050f140e1003554451418283e8940003200400d00c1c020071b00c000e1036420414180d20028008488016041c01000640b0b48202441303001d208540001e004020000c58000f0342c5c1c03441105440c0d10200680b20b1620f60090400842003c0c000d54450400400f0350300305004080c050754001d000b0b5482c3d921036460441d1142c000442d0004e00003010394107021a1454410300714400d410320b5a0016040800f61b040101c2c2e61541c2c1401c80b030940c02d1501303074698242c000c0741e60801c44010b0309006a9403201c410040d40c41c8000d0100640d80709113000d0402035400d212b42c00a0030154462101041700101c0900f0070b891500546480e040143e10140050100d14040e5001e503804070f280341082c0816a9140300003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 594043642 1250 594042392 594042401
    0x711030d05011d0108061e100509041a06030c0904020d0c080f0d030501050a0815190e03070c0b040e010b1c05130201020706091a090a0e012303010209060f07050709 72
    0x2810400c2c40c00040c0d0304084112000140588841c60140a5038181f20361807510f5103007507120300c9500c1c2e410003002c0303440d402e0035240c8040100005424100d05180904204080c0c806400c0c4d814000a1070200280c0b1520300030401206c00c0c0c00042100066443da0340a025811030400c0d801c0fa07031050001d00100ea196010004645d9041104000344070f800000d00d001803d030382040e40301c0e90003102d500000b44032030030000c80c0b034103100c500740070b5103003030325036a0303801200104403060b101ea09403501d03101041500c03e002000509400c0e025034805420369503100492000c0e842540302d81896032072114014460603034071074000e1840d4030410444030b802c081c4003400541111801d480b0068401d000410729002c40d40c0501407480105518240160054a022400b0030b071040c02c800300035158500000c0d588030359554584808003030705810700c02c0c0c1029a1030701901c00d0f4213010100700d4420b9042d2490350301030b186814000c44440c3c8202602041c03c4c5040c3d0003680307003190040300b01100c59014000c1d01040307010fa107108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 594044892 1250 594043642 594043649
    0x50d02040914100f06140306031e01020c06063a0b01330e15040810060501091403030f030406090506090c0f030f0a0b04030909020d060512010c080711030d0501 70
    0x81d841d42c64244031585021422540d4802e0320440500360701000303540d030045030780c50602007861348599990366902c000078107000c5c55528070400804032036824611030505601801d27800c10000e04403101a1a00c1c0d04010800520303c000e00704030707010b601c0c13444800080c00200440031200c02c100521008401d54030800c800c0300036001701540e421030140c3e9032150a201d048070b06a400e03103070021000c02001078200501d030620b0002c030b06024011101401c40c4644107017046900424a0318183d50048000301240d0010b05120312650f4001400c44001107881501c010039100c004000400a614100100e00b514a20b50001813050b1600c2d82c0c1d400410b00829020b2000e01c0c071401410700508810b540c040704000311000700c0b203a014001c0e40040f043c0e0415600024020b0840c0c4e41101211100f50740b14501100c4ea4060354016000b05400171a802c810100c907904040280d0b0300480d03040114a514160650880351f0901856001070300c1000032486035400b400e02c0070300054075002568079001a50f031400d802e840d400c1e030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 594046142 1250 594044892 594044921
    0xf0e0109090516060f1d01080f0903090d0602030a060806160e060f070b1b12040b2203020f100504200102010f060f030b060a032310050103030c120816050d020409 71
    0x295150140c0d1122412490641b003040d5540c1001c150f50000300117810050900b00d208694001107400e40c0e0007007003510420710004151912105151401d030000c1c0d0030507105580b42905100e00407443ca000031401c03500c142c45540c0030100006000008035086020070030066000542042000112450764004000301401840450168140780041d806010150002c0100c81c040c240043ca02000d0208080d68200340c220b4007003003240d03c0780000a400c1000c8102082c1c20a84080c0d6144201900170400104003042401643c6500391144d0080082c0c4030112801840b4802804003000060350802c044144d0780d9042c400090b42c81d03030611115080f0340c8107411100e0082c0c2a4001001085034103880c0d00d1380540e040e903c8501e41407440c0d03108dd429643c0c43c1c0080d20340c08414000110412420003407141c00c6c4240090600c0700396580d090240c0a2210040c0503600315000300345150850f13005000407070141541c1041140c44070701c0d050080700c958210810320150a41c0801c00014a0020360242040304030303000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 594047392 1250 594046142 594046157
    0x170702010c020f030903030906250c030309121109131b090b06040602030f18060f0c0d080403080114011101020c06070f1407080306190603020901090f0e010909051606 73
    0x810000e841d00d56082d0f040040c1c0c0d4002c20410f40707140c03404015a08081001d80e2010b441e50b404044800000b41c10005000c00d0800d084030761010b00c1082c0d035101d41142d0194031001c0304252114003040305c0488200b000380001448820340150707402c00308120340d03002804031882d408038482035071038007640700c0e6002070720207218a512010f12a4400f070344102084054200e07000c43c5400c1c03030003002940300e026841207011885000300b9000c1c2444261901082010f80080449581d078035160002d4030150032000ea40700d07a40c8280d58094100d00d0041d400c0d42c2c0100c0e016180c034103d41c0c2c0f17816401d07940815034421890402481e025059102d007400d0018040c03201861000d00003c0c5015076000f080f0100400c030260400c03c844251120085500c0201c40d20f103a08124400da403a03956a0110301b002c01d044100c21400d0030f140c140080c40c140c0c10384c090035074240c0c2642c1c2c0b0210180e40701a00d082008203800340340f64000c072040c01045264102e0380201c2080c0c0c031500a8620300340500c0c42c4031082c2403807a400b400200300e50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 594048642 1250 594047392 594047411
    0x1504080d05091806060f070615090e0606040e0a0f060b030f120406050a051c050f010f05031005070c02120607030501060f020c0127120203010b03012a17070201 70
    0x34852001054264074045040000d03030400a9000c54078035a202481e25566804909941c440034100c8036260820a2880c1d0f48244501d882401042d40d80035100b51400c00703420225000c105800341441c0c482c440da00130901038403120f080000814942242222910688034803000040c0008090601c2c03501a890003c0c100000302d06145c1001d91400c01019907400c820001404c071481b810a83c0c0c1907031818940035032a010303550750070b5529202d101e8020303446004e00c00d00c1c0c42c5000b280d900708622038081d00880b81d8480e6a0740a4984500190740682c03581500008440310701003210354001c60b030160051410881d800c0c01038002c954800c0603030300c07860165001201006065501030003100e006110600d0030b0070700c1c1a140800203441d41c101854243c100302e1200103081ca80c400440403441c025001c014140090303a6500b0703085000405199089000354204505482189410720910000301c044c50020030341c0080364090070300080d0300032030440c00b840304003040210741d0100d180d016071207034034140c00010300ea405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 594049892 1250 594048642 594048659
    0x1918020a05060a08040f0201140304110a050102030a020a02060d0b090403051b03072a0b0f0a2601170a150c08090c01120c21060513050103080313020f1504 68
    0x315410180c00740404000b149841640300403000c0d4403d0f00410502d400440b03d10040301c07078580880d0401c040b048084244800c1c0310507403500406003c011aa00b00202381d440d03005a07100e002d00400c40c03001d40c201003184005418850020100080b81720380c0040c0050100c000035040110907203060f00040c03008a141c0040340e000040c1c02c1001c1501070011410071009554060302509840030766007500c040c4040301031045c1d44040c80700b400350401c0c00845d603c41c81d02d0802180c242c1c2000c0f6069001070090011041034079800c080900c9035200c11003203510184c1c00d048094805030030480d09040c20348580500360010aa4054401c004800c03c80e00c042483d05c05094001d1081c2c40262242c2400c1d0044550241241c0c0c104490030307041480d400004c556208011030640c1c116291040032a540b070b01443c040921002c09034468410340340c007200e09100080010f80c0e001c0454000340401040040c040000c41c012819507500b1200c0584024008540400200d001ca00c01e400c004016213414000400c0a001008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 594051142 1250 594049892 594049909
    0x9040f0c02030c0d0c05030f092707020c12030a050304140d0203072d031b0b1e0c0315040b0a050301020a17010b07050a060b0d0b0c12060108090d08191802 68
    0x2c04c9140c59041c1002540fa19501d0b44030303000e902c1100f03850000d1840d006444074540f4110303440c00c0080c40f000481d501e100d03c0000d8001240c04d400180102454002d41c2c0c0ba10803509280461b58000460518400710400d07a42984040d0040e200542c040c0c80414043d101013054401c5148140c1c0a1500c1c1c4641c4d1034269510a200c45a4401c18841107a86484411100045403142a0980740070402ca8185e02c90500380201e1101300949200c1e910070800c403043d840070142000c2c0008508009000da603900920851300d000c15100c510400e280b0112640845c5095048400c40c0003000b401920003583e07030b4001a08990200c0180c1010449240c2d585000f00c1501400c2c0b03004140d403e1026113010001d9480036255007101e040100648d81e10036045c0501c0d00c0e90b6264092056208100888a040902c080c0f034140e003024104200030402c890010380b295100d4101c040c0113040c0c54004181003684c0b12015a0944401480b5a5580c00800e10f104280030700b0703008030b0f080d000214028040c98040750043c8074498 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 594052392 1250 594051142 594051163
    0x403021e011a060a1b031b030306050f03061b0304050304180504060f2c071508040b06030706140a020f030f0d0b09060d02120c061b011d030a0509040f0c02030c 70
    0x66809010315070f150303608a400754820309000a100040300086141c01d0303d07d003522402c004058034124448508158055110200750341003221989004a00340f004c140c0c2c0d81000f01d6103079144c501d007410062503042c05500991b0700580701c0d8095908298407a42d82654260340364007100020ba441c3c1c0c05103c2840800d1203284c48000f1243c070103206814199503a04a25403c1228044006250411f8402e01c3c540900c01040500300c1820010040f0140050050800e40151000d843ca4410200454150b02d0006910012074040c1d8540843d8a0320b82800341307510b90000c140c400107501440c0702071808643c051000f44040c10100001544030440e10101000300e03590110814003c083e900705200e910b940300c14210640075411500c49030840444050541400801442030740c000b18049440c03940c400d07c01000d02d10f54142500204012010048101a2406003615100161304104403011103144244020204042c000d0804039600040c88150011105407041610058002041c240142d40c01400300c11242c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 594053642 1250 594052392 594052399
    0x30709050108090f0705060a030f2301080303060a03140307021f020f010b0a1401020f0d050322020d0803070201060b04030b070215011406090d0204051801050a091a0403021e011a 78
    0x1c4c12402d00360a5580c512401a14422003001c02d05c1482140b01c3d4102c80074950100e0003c0c403401d882c3d0f070300342604245262032061215944034000f0030404130000039030f8440c820041046061510310b4680c00200010880101643e00081017520b025071100c040c0e00700d291040e2001d0400b0580d00550007400c0c0788941c50740e01413a90401103241803640d56035202c0000e550340b900071100340720038010060703103480700101c2c2c01d42c0b842c020300c040f40600c00d80120180d40302e5003c0240c0c0c510305010005091904000090000394008001c00798800803c11032809107901804a00000903025220040318100c0d410550044507544545010495443c0e07060099001060f032005a01c101541407039a2014645401500540910380103d4241e803955030728102c03000600d4000d4010485400d0900754010400c02c044000ca0003582040301154a0500c02d109804206401c803c000403032100d520703600400c0d4040500241d046104050b130603260344a5548680c0c2c0d00c6884140006406240c000b03050031a13a689840380d522 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 594054892 1250 594053642 594053653
    0x1707021f0e0c1207031e05010b0103020405010c0f0602040b0705030702040c030c08130305090a170610051e1201150303030c0801030b0106050c070321080a060f05120c040203070905010809 82
    0x241ca050020742c240d4000d20071100c4608002000d41000e141c404d03190f01c082c2540307503605021091084400c000c0020507001d20028482045c8400c01981030f0300c218401c00c1d0000d0750344c51840000c50782001035451410310958015140c5a650724420a21350040f1754169415000042c82c4401c502e070610403014000120300f02441402c444040250481100905028035061403007418402c00d84034008442c248200105883c51150b1a0803441c1d60070366204a00e2000e511801c0042104541080650400c558005209003026803c2078034800074006020580354000d900050604402c010a0180c00840740d0b2100c06810706c10301d1400e005098a00e03140f070701c00034809004011b0020598440c0c0c0541507500c00d0520f50381d03545844113102e123000541d40c40900716001c0130000d151400005e10030804d808410381e4901015441d0107400d03504550301e901c2200e04010000c1d80810a0307003454100030228801d41800c0d107000e10080310208080e40d100b2180c20b000136040302c01c02c0c0155030700641800c0d00304900000822 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 594056142 1250 594054892 594054911
    0x30f010c0e03061b0a1e091d01080c1216090e1005070206040b04051905100b0616060e03040b03040b0123010e0f060403060f051b0f04090203071707021f 67
    0x4441264101c03045009020014044c0c5000e070144101203206d4044040c0b08605a42040d0b00034020200e074059888140d50681c018148600d0b012142c5069603039a1010f40f81098204003000951108451400003d00400c3c5a968400c28139140440c01455440404100302034003216883c00c0c5002c420004800302d00d03003c148881c8031b13800140720341d06c80c0c0d00042000d620b803958100300b49001506954a03240040c0b4108031000c2003070224030152a001c410310207000f030f07010355001c00045000f50b1801100d0b01c80c407201c030400410a160012103014451809803494a03441d4800c611141c3d00407a025120821803c004005c040710304240e100b120708003c0c62900080c406040020500c410080195118041c41e207021045613442400703c034011580301d24100070b00003800343c0c8100030b807004942c6107a03101d090141c00039007404c2d1070080b11291a420fa0107203251a003031220040c001e40001c3c1c03040701000070103801d2200140035030b08064007800c860b40007130608003200e5155802c2050040380e174080c090b05244525 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 594057392 1250 594056142 594056161
    0xf060804050304050d0c0e040f060b040e03030a0504110909030c070e0c030412050f07050c0306010e040804030303020d1b0c11060c1005041103012306180a0c0e030f010c0e0306 77
    0x140d080d18402c403a05d44880d18103040003540c0030b04a812050b41e913844202800200000e0400086802d88944018442e5060810410040f0340030340001102c5504200002140c48070103a00859100307106186441d83c003a0f640703001c1a1401012541b0326100c1d0700c0081c8185e08184100f026000906c5014815001480e014114007200d000c0039000801d46450140c115110b0707809502981ea51011061080e03484000d141049a5241640d00b0000d0181c0205000400d44800000c0101c0c40360b070b0401c800529041c51b41d90114025406007038240720b010703515401e528148050740c41d074072008200b503074448920480030b0511108402500400e00d204072010400d070b12156001003070101c40102280d0b00020146d94505140819400900c8901d501d03520701003180d424035040300040401c3c0806004c0740c403020313614a000e0100500c0c002c84880c3c4007051a0300040c182942c0c6802c04120103246240040c501c0018002003458141c01404804559450707071f07003291189921a180c078181e03c03008c034014500303400c000840b1f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 594058642 1250 594057392 594057397
    0x30501050f071e09030503030c0d0509030406020c1338040b13090204090602040e04050d050c03041a1905040501141204020411040f08010c030f050403270b040905010f0608040503 78
    0x201c44460002c4150000f1a0b40034010290045400c0030944e50340345050310f102034050380080000038a45203850082403101a000040e9001d80300344e60000c04500001008002d00b01401c3c0c109101c190340c680345045d9528440e051040e614416040310400380212102030a100c101600030070303d0240e4a000c44c20b2209551342d0601c0c110654061100088104c040d00119000d403003800c1014001070700005001551044148105200d18000d00540c3eaa200411108503445d00c101200044640d01c20302060080c04a840c0452040c1e0045910381071034070310306140c1c4480c61521020640040f07074000c00c0800003960002c1d43e189480c5003590a442ca03218100048125400002e400030703005075901c0e110204102110021a000b419002c43c0d01030b0456030303c44641d4080d242e1500d94000007803d15203a107095200314040d0b54007c5a050302d4494000300e2000718440b10401021120082c800c2c1201c00041c860100c81c02840540010342d00840d01d0343c14900d209120075950361000040018590800c8041030003c001d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 594059892 1250 594058642 594058667
    0xc04350f0a060e010f0614040501120c050f0604090f0f060803070510020a0203071b061d100305040215040611160e0f0601050f0d1d010e120c10090c030501050f07 71
    0x240000d01168203c20700d80145804c01080030400e24003200403680c4050b007007020072030920841e02030260380c0c0c80348000c44048200d400c0003007010b00c1d01d000c184000e14001880104a55000c1c205e5400d0595540c4007500343c075611405100110b45d5030006001c42030050240c4c0e009041d000f0002c524094103580d4940e07071014844600010181d000c106085000d01c01d004903182036130000d50300e0008400c11001c1100c510b03503d10400000c690358040002c2285110100e40900c800c2c002c108584002d00c7c00d03030031f40161900420882e400b8840518450600740803501810181074240e0710403a0715480114054500100c400c8010140240c1d9203040080110140383e4a900020041d003002d03035501c0d01030042e20f06005034555101520000f00e00340100c0c40301075210b148100f142d10001c9040d03000307851400e4225250000001926000a00c03032103000044640200045151030302220056140400403034200c2e000e1050403a0540d0001d54100b084c4102400b13502d400503141243c140302c90501e41c0000d4100c511a03074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 594061142 1250 594059892 594059903
    0x90d120e010902150309060708150d11040f0905070515031b0c03070317070905100f0c0807050a12020105090c0d05030717190903080706050c04350f0a 66
    0x1030044103801820340146034160703805851101102e0020f0b0a581903500103c900840c0f84c17048000081038140308968140c01181d401d60706604c89000c0c00140103000f140080305843d011300f444034150507929984281c0310703c040c040200151200719450242d013807041681c0300310704c81c02060086d090032403007550440790089001c419040700050321013407220b2140520000c5070624080072a40b80c0c203140d04000f01c1d003d50501e4001d401210b50b80c0220070360790704816019858102400c01e00d01480300c1e00030f0203944403070002400d00c0100c41c8080d0707031281141d6120b00001ca405030030502d800300401060b510403010310b8020780002c0c802460001c10681c0e440c0c020b503600078491007010b0025014444140110303421241c03c008201507644071907280b1001640142c0d5645441180b160488000c140b1030488401a80d9100003041d1401c01140c8078040a80800340410860550411001800c0e030390704084803034141410700400c4a9612100c4402184c030034401248203680d009064000c2c080080425041440c0b40e001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 594062392 1250 594061142 594061151
    0x60606031f0305010e06011d2701020702040207060b010f0908060c1602030616080901020a0813210804060b0906091303030e01060b091306050d1410180b090d12 70
    0x115240d0311144036030002d0f02551801c117548515903000304161f4165030079510880141000d40c00e00000580044600b080b524200f84003600803042e04014400320142c50f14005801d22669800240c100d80c0074032411582e25585d40c1c0b9011403940c100c4070001c119119030910410036481c080081d510b480e80208201c58050300016258440003400b03018490454020701102c84918042c110380105c0d40e000071000001c1080391001803113400d0140200c503568481540c03000740c29240c1040d02071819514003012901907007011142c0030409003503810f04107901c00c969918062030400d410700c40300300c8022130070260040c407229040005988600d5546500551001c104074509030b0781d4202240140242c3c90303004134550074110700140580c800310150040c0c5108803000860320080121541c2194128824240c100c0740c62a1a840030510000258891301341d2030054440a02201d00c0342e00846030b0740340030a400e00c001d1003607000a110356100c2403a032000b10000100550040004042d2441e4000e0040502e519201c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 594063642 1250 594062392 594062431
    0x4081005090d111905010209040b0f0a170307060207030918020f160c03080d0e160807030209041b17100509190609060c030507230703030522030504080c0306060603 72
    0x400c01d015003d541c1130350007014401146400707400303584054400f604c03581c00c24107a94141d24040109150070000207000c80d0700b9614041d180103928945a81062890009000ca500420104d000404001e0b01c42d548001034a42811511542e10403910002034250380b040c0641c1c5040741c3c83d1022148818010f284402e0700007114503002c0c01d021020742000b000c0f0f600102c0c1005d608261a04040d0461401405403a2041800350341d00403009071500c80c28106500811003040503050007003007903411030b02a4113000102024022205a040c1c4203070720940101c40840050b201c1c0e07082c01d000d01d01c10505020414031040c204040c10656945c043c048140102840b00e007036008008070356100e1219994044418000050603044c00307030082008036008808030f400a100d41c1c0484a109994192103264503118605000ca0358070b040f0000e001c0285041510140c075124002041e8520610360603440c802c0d85e8895659003017103452803e198080d0b040c58043d0780880140601580c2e4402501d50040010042c20300c0c2c0d050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 594064748 1106 594063642 594063677
    0x41a030f07110a0606080a110102060f070f020102070203061f080a0c090f1d070501020706030216060e1203070c1110021f0605100504081005090d 64
    0x400c640040c080360301a14611044280400486100403403130381d101000c40f08075401a038102d5100703804c13038010009102030740010100c0038070103803100741041e1a0381010b180c070240444e0103101405114501e80da100350b0580f907070706400170100c40c1181014228125281440980310307681d0524181c01140c00d180004554a135268080b61140000c0e291208801c000d201d40382c0003d4441ea1203041c016038256400803001c41d00086040a0041c451414001903d4020a40e000d00e05050040c014140341003c0500301c2c1e0245500074002142d14161044032070b0909060502116000001109006107260b101c3c400c4900a8401c24403800c20000782000c0244004a00007a140180d1000040b0307860801c2400d42c5144a1030450000f050b1207032104001361440201c0c06a103c0011000710b0308100308e40381000310700f0034035460050402c040e0a00300203603922a66062403010a12080094a1b00c20f40e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 593884892 594064748 := by
  have h0 := BRFrame.cov_init 593884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 593884892 ≤ n) (h2 : n < 594064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
